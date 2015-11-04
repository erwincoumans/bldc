/*
	Copyright 2015 Benjamin Vedder	benjamin@vedder.se

	This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * mcpwm_foc.c
 *
 *  Created on: 10 okt 2015
 *      Author: benjamin
 */

#include "mcpwm_foc.h"
#include "mc_interface.h"
#include "ch.h"
#include "hal.h"
#include "stm32f4xx_conf.h"
#include "digital_filter.h"
#include "utils.h"
#include "ledpwm.h"
#include "hw.h"
#include "terminal.h"
#include "encoder.h"
#include "commands.h"
#include <math.h>

// Private types
typedef struct {
	volatile bool updated;
	volatile uint32_t top;
	volatile uint32_t duty1;
	volatile uint32_t duty2;
	volatile uint32_t duty3;
	volatile uint32_t val_sample;
	volatile uint32_t curr1_sample;
	volatile uint32_t curr2_sample;
} mc_timer_struct;

// Private variables
static volatile mc_configuration *conf;
static volatile mc_state state;
static volatile mc_control_mode control_mode;
static volatile int curr0_sum;
static volatile int curr1_sum;
static volatile int curr_start_samples;
static volatile int curr0_offset;
static volatile int curr1_offset;
static volatile float voltage_state_d;
static volatile float voltage_state_q;
static volatile float phase_now;
static volatile bool phase_override;
static volatile float phase_now_override;
static volatile float current_in;
static volatile float current_in_filtered;
static volatile float current;
static volatile float current_filtered;
static volatile float id_set;
static volatile float iq_set;
static volatile bool dccal_done;
static volatile mc_timer_struct timer_struct;
static volatile bool output_on;
static volatile float pos_pid_set_pos;

// Private functions
static void do_dc_cal(void);
static void control_current(float targetId, float targetIq, float Ia, float Ib,
		float phase, volatile float* IbusEst, volatile float* Id,
		volatile float* Iq, volatile float *vstate_d, volatile float *vstate_q,
		float dt);
static void svm(float alpha, float beta, volatile uint32_t PWMHalfPeriod,
		volatile uint32_t* tAout, volatile uint32_t* tBout,
		volatile uint32_t* tCout);
static void run_pid_control_pos(float dt);
static void get_timer_settings(mc_timer_struct *settings);
static void set_next_timer_settings(mc_timer_struct *settings);
static void update_timer_attempt(void);
static void stop_pwm_hw(void);
static void start_pwm_hw(void);

// Threads
static THD_WORKING_AREA(timer_thread_wa, 2048);
static THD_FUNCTION(timer_thread, arg);

// Constants
#define ONE_BY_SQRT3			(0.57735026919f)
#define TWO_BY_SQRT3			(2.0f * 0.57735026919f)
#define SQRT3_BY_2				(0.86602540378f)

void mcpwm_foc_init(volatile mc_configuration *configuration) {
	// Hardcoded FOC parameters
	// TODO: Remove this and move to conf_general. Implement in BLDC Tool.
	configuration->foc_current_kp = 0.05;
	configuration->foc_current_ki = 60.0;
	configuration->foc_f_sw = 20000;
	configuration->foc_encoder_inverted = false;
	configuration->foc_encoder_offset = 3.1;

	configuration->p_pid_kp = 0.01;
	configuration->p_pid_ki = 0.0;
	configuration->p_pid_kd = 0.0006;

	configuration->l_current_max = 30.0;
	configuration->l_current_min = -30.0;
	configuration->l_in_current_max = 5.0;
	configuration->l_in_current_min = -5.0;

	utils_sys_lock_cnt();

	TIM_TimeBaseInitTypeDef  TIM_TimeBaseStructure;
	TIM_OCInitTypeDef  TIM_OCInitStructure;
	TIM_BDTRInitTypeDef TIM_BDTRInitStructure;

	conf = configuration;

	// Initialize variables
	conf = configuration;
	state = MC_STATE_OFF;
	control_mode = CONTROL_MODE_NONE;
	dccal_done = false;
	voltage_state_d = 0.0;
	voltage_state_q = 0.0;
	phase_now = 0.0;
	phase_override = false;
	phase_now_override = 0.0;
	current_in = 0.0;
	current_in_filtered = 0.0;
	current = 0.0;
	current_filtered = 0.0;
	id_set = 0.0;
	iq_set = 0.0;
	output_on = false;
	pos_pid_set_pos = 0.0;

	TIM_DeInit(TIM1);
	TIM_DeInit(TIM8);
	TIM1->CNT = 0;
	TIM8->CNT = 0;

	// TIM1 clock enable
	RCC_APB2PeriphClockCmd(RCC_APB2Periph_TIM1, ENABLE);

	// Time Base configuration
	TIM_TimeBaseStructure.TIM_Prescaler = 0;
	TIM_TimeBaseStructure.TIM_CounterMode = TIM_CounterMode_CenterAligned2; // compare flag when upcounting
	TIM_TimeBaseStructure.TIM_Period = SYSTEM_CORE_CLOCK / (int)conf->foc_f_sw;
	TIM_TimeBaseStructure.TIM_ClockDivision = 0;
	TIM_TimeBaseStructure.TIM_RepetitionCounter = 1; // Only generate update event on underflow

	TIM_TimeBaseInit(TIM1, &TIM_TimeBaseStructure);

	// Channel 1, 2 and 3 Configuration in PWM mode
	TIM_OCInitStructure.TIM_OCMode = TIM_OCMode_PWM1;
	TIM_OCInitStructure.TIM_OutputState = TIM_OutputState_Enable;
	TIM_OCInitStructure.TIM_OutputNState = TIM_OutputState_Enable;
	TIM_OCInitStructure.TIM_Pulse = TIM1->ARR / 2;
	TIM_OCInitStructure.TIM_OCPolarity = TIM_OCPolarity_High;
	TIM_OCInitStructure.TIM_OCNPolarity = TIM_OCNPolarity_High;
	TIM_OCInitStructure.TIM_OCIdleState = TIM_OCIdleState_Set;
	TIM_OCInitStructure.TIM_OCNIdleState = TIM_OCNIdleState_Set;

	TIM_OC1Init(TIM1, &TIM_OCInitStructure);
	TIM_OC2Init(TIM1, &TIM_OCInitStructure);
	TIM_OC3Init(TIM1, &TIM_OCInitStructure);
	TIM_OC4Init(TIM1, &TIM_OCInitStructure);

	TIM_OC1PreloadConfig(TIM1, TIM_OCPreload_Enable);
	TIM_OC2PreloadConfig(TIM1, TIM_OCPreload_Enable);
	TIM_OC3PreloadConfig(TIM1, TIM_OCPreload_Enable);
	TIM_OC4PreloadConfig(TIM1, TIM_OCPreload_Enable);

	// Automatic Output enable, Break, dead time and lock configuration
	TIM_BDTRInitStructure.TIM_OSSRState = TIM_OSSRState_Enable;
	TIM_BDTRInitStructure.TIM_OSSIState = TIM_OSSRState_Enable;
	TIM_BDTRInitStructure.TIM_LOCKLevel = TIM_LOCKLevel_OFF;
	TIM_BDTRInitStructure.TIM_DeadTime = MCPWM_DEAD_TIME_CYCLES;
	TIM_BDTRInitStructure.TIM_Break = TIM_Break_Disable;
	TIM_BDTRInitStructure.TIM_BreakPolarity = TIM_BreakPolarity_High;
	TIM_BDTRInitStructure.TIM_AutomaticOutput = TIM_AutomaticOutput_Disable;

	TIM_BDTRConfig(TIM1, &TIM_BDTRInitStructure);
	TIM_CCPreloadControl(TIM1, ENABLE);
	TIM_ARRPreloadConfig(TIM1, ENABLE);

	/*
	 * ADC!
	 */
	ADC_CommonInitTypeDef ADC_CommonInitStructure;
	DMA_InitTypeDef DMA_InitStructure;
	ADC_InitTypeDef ADC_InitStructure;

	// Clock
	RCC_AHB1PeriphClockCmd(RCC_AHB1Periph_DMA2 | RCC_AHB1Periph_GPIOA | RCC_AHB1Periph_GPIOC, ENABLE);
	RCC_APB2PeriphClockCmd(RCC_APB2Periph_ADC1 | RCC_APB2Periph_ADC2 | RCC_APB2Periph_ADC3, ENABLE);

	dmaStreamAllocate(STM32_DMA_STREAM(STM32_DMA_STREAM_ID(2, 4)),
			3,
			(stm32_dmaisr_t)mcpwm_foc_adc_int_handler,
			(void *)0);

	// DMA for the ADC
	DMA_InitStructure.DMA_Channel = DMA_Channel_0;
	DMA_InitStructure.DMA_Memory0BaseAddr = (uint32_t)&ADC_Value;
	DMA_InitStructure.DMA_PeripheralBaseAddr = (uint32_t)&ADC->CDR;
	DMA_InitStructure.DMA_DIR = DMA_DIR_PeripheralToMemory;
	DMA_InitStructure.DMA_BufferSize = HW_ADC_CHANNELS;
	DMA_InitStructure.DMA_PeripheralInc = DMA_PeripheralInc_Disable;
	DMA_InitStructure.DMA_MemoryInc = DMA_MemoryInc_Enable;
	DMA_InitStructure.DMA_PeripheralDataSize = DMA_PeripheralDataSize_HalfWord;
	DMA_InitStructure.DMA_MemoryDataSize = DMA_MemoryDataSize_HalfWord;
	DMA_InitStructure.DMA_Mode = DMA_Mode_Circular;
	DMA_InitStructure.DMA_Priority = DMA_Priority_High;
	DMA_InitStructure.DMA_FIFOMode = DMA_FIFOMode_Disable;
	DMA_InitStructure.DMA_FIFOThreshold = DMA_FIFOThreshold_1QuarterFull;
	DMA_InitStructure.DMA_MemoryBurst = DMA_MemoryBurst_Single;
	DMA_InitStructure.DMA_PeripheralBurst = DMA_PeripheralBurst_Single;
	DMA_Init(DMA2_Stream4, &DMA_InitStructure);

	// DMA2_Stream0 enable
	DMA_Cmd(DMA2_Stream4, ENABLE);

	// Enable transfer complete interrupt
	DMA_ITConfig(DMA2_Stream4, DMA_IT_TC, ENABLE);

	// ADC Common Init
	// Note that the ADC is running at 42MHz, which is higher than the
	// specified 36MHz in the data sheet, but it works.
	ADC_CommonInitStructure.ADC_Mode = ADC_TripleMode_RegSimult;
	ADC_CommonInitStructure.ADC_Prescaler = ADC_Prescaler_Div2;
	ADC_CommonInitStructure.ADC_DMAAccessMode = ADC_DMAAccessMode_1;
	ADC_CommonInitStructure.ADC_TwoSamplingDelay = ADC_TwoSamplingDelay_5Cycles;
	ADC_CommonInit(&ADC_CommonInitStructure);

	// Channel-specific settings
	ADC_InitStructure.ADC_Resolution = ADC_Resolution_12b;
	ADC_InitStructure.ADC_ScanConvMode = ENABLE;
	ADC_InitStructure.ADC_ContinuousConvMode = DISABLE;
	ADC_InitStructure.ADC_ExternalTrigConvEdge = ADC_ExternalTrigConvEdge_Falling;
	ADC_InitStructure.ADC_ExternalTrigConv = ADC_ExternalTrigConv_T8_CC1;
	ADC_InitStructure.ADC_DataAlign = ADC_DataAlign_Right;
	ADC_InitStructure.ADC_NbrOfConversion = HW_ADC_NBR_CONV;

	ADC_Init(ADC1, &ADC_InitStructure);
	ADC_InitStructure.ADC_ExternalTrigConvEdge = ADC_ExternalTrigConvEdge_None;
	ADC_InitStructure.ADC_ExternalTrigConv = 0;
	ADC_Init(ADC2, &ADC_InitStructure);
	ADC_Init(ADC3, &ADC_InitStructure);

	// Enable Vrefint channel
	ADC_TempSensorVrefintCmd(ENABLE);

	// Enable DMA request after last transfer (Multi-ADC mode)
	ADC_MultiModeDMARequestAfterLastTransferCmd(ENABLE);

	// Injected channels for current measurement at end of cycle
	ADC_ExternalTrigInjectedConvConfig(ADC1, ADC_ExternalTrigInjecConv_T1_CC4);
	ADC_ExternalTrigInjectedConvConfig(ADC2, ADC_ExternalTrigInjecConv_T8_CC2);
	ADC_ExternalTrigInjectedConvEdgeConfig(ADC1, ADC_ExternalTrigInjecConvEdge_Falling);
	ADC_ExternalTrigInjectedConvEdgeConfig(ADC2, ADC_ExternalTrigInjecConvEdge_Falling);
	ADC_InjectedSequencerLengthConfig(ADC1, 2);
	ADC_InjectedSequencerLengthConfig(ADC2, 2);

	hw_setup_adc_channels();

	// Interrupt
	ADC_ITConfig(ADC1, ADC_IT_JEOC, ENABLE);
	nvicEnableVector(ADC_IRQn, 6);

	// Enable ADC1
	ADC_Cmd(ADC1, ENABLE);

	// Enable ADC2
	ADC_Cmd(ADC2, ENABLE);

	// Enable ADC3
	ADC_Cmd(ADC3, ENABLE);

	// ------------- Timer8 for ADC sampling ------------- //
	// Time Base configuration
	RCC_APB2PeriphClockCmd(RCC_APB2Periph_TIM8, ENABLE);

	TIM_TimeBaseStructure.TIM_Prescaler = 0;
	TIM_TimeBaseStructure.TIM_CounterMode = TIM_CounterMode_CenterAligned2;
	TIM_TimeBaseStructure.TIM_Period = SYSTEM_CORE_CLOCK / (int)conf->foc_f_sw;
	TIM_TimeBaseStructure.TIM_ClockDivision = 0;
	TIM_TimeBaseStructure.TIM_RepetitionCounter = 0;
	TIM_TimeBaseInit(TIM8, &TIM_TimeBaseStructure);

	TIM_OCInitStructure.TIM_OCMode = TIM_OCMode_PWM1;
	TIM_OCInitStructure.TIM_OutputState = TIM_OutputState_Enable;
	TIM_OCInitStructure.TIM_Pulse = 500;
	TIM_OCInitStructure.TIM_OCPolarity = TIM_OCPolarity_High;
	TIM_OCInitStructure.TIM_OCNPolarity = TIM_OCNPolarity_High;
	TIM_OCInitStructure.TIM_OCIdleState = TIM_OCIdleState_Set;
	TIM_OCInitStructure.TIM_OCNIdleState = TIM_OCNIdleState_Set;
	TIM_OC1Init(TIM8, &TIM_OCInitStructure);
	TIM_OC1PreloadConfig(TIM8, TIM_OCPreload_Enable);
	TIM_OC2Init(TIM8, &TIM_OCInitStructure);
	TIM_OC2PreloadConfig(TIM8, TIM_OCPreload_Enable);

	TIM_ARRPreloadConfig(TIM8, ENABLE);
	TIM_CCPreloadControl(TIM8, ENABLE);

	// PWM outputs have to be enabled in order to trigger ADC on CCx
	TIM_CtrlPWMOutputs(TIM8, ENABLE);

	// TIM1 Master and TIM8 slave
	TIM_SelectOutputTrigger(TIM1, TIM_TRGOSource_Update);
	TIM_SelectMasterSlaveMode(TIM1, TIM_MasterSlaveMode_Enable);
	TIM_SelectInputTrigger(TIM8, TIM_TS_ITR0);
	TIM_SelectSlaveMode(TIM8, TIM_SlaveMode_Reset);

	// Enable TIM1 and TIM8
	TIM_Cmd(TIM1, ENABLE);
	TIM_Cmd(TIM8, ENABLE);

	// Main Output Enable
	TIM_CtrlPWMOutputs(TIM1, ENABLE);

	// ADC sampling locations
	stop_pwm_hw();
	mc_timer_struct timer_tmp;
	timer_tmp.top = TIM1->ARR;
	timer_tmp.duty1 = 0;
	timer_tmp.duty2 = 0;
	timer_tmp.duty3 = 0;

	// Sample intervals. For now they are fixed with voltage samples in the center of V7
	// and current samples in the center of V0
	timer_tmp.curr1_sample = timer_tmp.top - 2;
	timer_tmp.curr2_sample = timer_tmp.top - 2;
	timer_tmp.val_sample = 5;

	set_next_timer_settings(&timer_tmp);

	utils_sys_unlock_cnt();

	// Calibrate current offset
	ENABLE_GATE();
	DCCAL_OFF();
	do_dc_cal();

	// Start threads
	chThdCreateStatic(timer_thread_wa, sizeof(timer_thread_wa), NORMALPRIO, timer_thread, NULL);

	// WWDG configuration
	RCC_APB1PeriphClockCmd(RCC_APB1Periph_WWDG, ENABLE);
	WWDG_SetPrescaler(WWDG_Prescaler_1);
	WWDG_SetWindowValue(255);
	WWDG_Enable(100);
}

void mcpwm_foc_set_configuration(volatile mc_configuration *configuration) {
	conf = configuration;
}

mc_state mcpwm_foc_get_state(void) {
	return state;
}

bool mcpwm_foc_is_dccal_done(void) {
	return dccal_done;
}

/**
 * Switch off all FETs.
 */
void mcpwm_foc_stop_pwm(void) {
	state = MC_STATE_OFF;
	stop_pwm_hw();
}

/**
 * Use duty cycle control. Absolute values less than MCPWM_MIN_DUTY_CYCLE will
 * stop the motor.
 *
 * @param dutyCycle
 * The duty cycle to use.
 */
void mcpwm_foc_set_duty(float dutyCycle) {
	(void)dutyCycle;
}

/**
 * Use duty cycle control. Absolute values less than MCPWM_MIN_DUTY_CYCLE will
 * stop the motor.
 *
 * WARNING: This function does not use ramping. A too large step with a large motor
 * can destroy hardware.
 *
 * @param dutyCycle
 * The duty cycle to use.
 */
void mcpwm_foc_set_duty_noramp(float dutyCycle) {
	(void)dutyCycle;
}

/**
 * Use PID rpm control. Note that this value has to be multiplied by half of
 * the number of motor poles.
 *
 * @param rpm
 * The electrical RPM goal value to use.
 */
void mcpwm_foc_set_pid_speed(float rpm) {
	(void)rpm;
}

/**
 * Use PID position control. Note that this only works when encoder support
 * is enabled.
 *
 * @param pos
 * The desired position of the motor in degrees.
 */
void mcpwm_foc_set_pid_pos(float pos) {
	control_mode = CONTROL_MODE_POS;
	pos_pid_set_pos = pos;

	if (state != MC_STATE_RUNNING) {
		state = MC_STATE_RUNNING;
	}
}

/**
 * Use current control and specify a goal current to use. The sign determines
 * the direction of the torque. Absolute values less than
 * conf->cc_min_current will release the motor.
 *
 * @param current
 * The current to use.
 */
void mcpwm_foc_set_current(float current) {
	if (fabsf(current) < conf->cc_min_current) {
		control_mode = CONTROL_MODE_NONE;
		state = MC_STATE_OFF;
		stop_pwm_hw();
		return;
	}

	utils_truncate_number(&current, conf->lo_current_min, conf->lo_current_max);

	control_mode = CONTROL_MODE_CURRENT;
	id_set = current;

	if (state != MC_STATE_RUNNING) {
		state = MC_STATE_RUNNING;
	}
}

/**
 * Brake the motor with a desired current. Absolute values less than
 * conf->cc_min_current will release the motor.
 *
 * @param current
 * The current to use. Positive and negative values give the same effect.
 */
void mcpwm_foc_set_brake_current(float current) {
	(void)current;

	// TODO!
	if (!phase_override) {
		mcpwm_foc_set_current(0.0);
	}
}

float mcpwm_foc_get_duty_cycle_set(void) {
	return 0;
}

float mcpwm_foc_get_duty_cycle_now(void) {
	// TODO: Is there a simpler way?
	const float Vbus = GET_INPUT_VOLTAGE();
	float mod_d = voltage_state_d / ((2.0 / 3.0) * Vbus);
	float mod_q = voltage_state_q / ((2.0 / 3.0) * Vbus);
	return SIGN(voltage_state_d) * sqrtf(mod_d * mod_d + mod_q * mod_q) / SQRT3_BY_2;
}

/**
 * Get the current switching frequency.
 *
 * @return
 * The switching frequency in Hz.
 */
float mcpwm_foc_get_switching_frequency_now(void) {
	return conf->foc_f_sw;
}

/**
 * Calculate the current RPM of the motor. This is a signed value and the sign
 * depends on the direction the motor is rotating in. Note that this value has
 * to be divided by half the number of motor poles.
 *
 * @return
 * The RPM value.
 */
float mcpwm_foc_get_rpm(void) {
	return 0;
}

/**
 * Get the motor current. The sign of this value will
 * represent whether the motor is drawing (positive) or generating
 * (negative) current.
 *
 * @return
 * The motor current.
 */
float mcpwm_foc_get_tot_current(void) {
	return current;
}

/**
 * Get the FIR-filtered motor current. The sign of this value will
 * represent whether the motor is drawing (positive) or generating
 * (negative) current.
 *
 * @return
 * The filtered motor current.
 */
float mcpwm_foc_get_tot_current_filtered(void) {
	return current_filtered;
}

/**
 * Get the motor current. The sign of this value represents the direction
 * in which the motor generates torque.
 *
 * @return
 * The motor current.
 */
float mcpwm_foc_get_tot_current_directional(void) {
	return 0;
}

/**
 * Get the filtered motor current. The sign of this value represents the
 * direction in which the motor generates torque.
 *
 * @return
 * The filtered motor current.
 */
float mcpwm_foc_get_tot_current_directional_filtered(void) {
	return 0;
}

/**
 * Get the input current to the motor controller.
 *
 * @return
 * The input current.
 */
float mcpwm_foc_get_tot_current_in(void) {
	return current_in;
}

/**
 * Get the FIR-filtered input current to the motor controller.
 *
 * @return
 * The filtered input current.
 */
float mcpwm_foc_get_tot_current_in_filtered(void) {
	return current_in_filtered;
}

/**
 * Measure encoder offset and direction.
 *
 * @param current
 * The locking open loop current for the motor.
 *
 * @param offset
 * The detected offset.
 *
 * @param direction
 * The detected direction.
 */
void mcpwm_foc_encoder_detect(float current, float *offset, bool *inverted) {
	id_set = current;
	phase_override = true;
	state = MC_STATE_RUNNING;

	// TODO: Detect if direction is inverted
	*inverted = false;

	// Find index
	while(!encoder_index_found()) {
		for (float i = 0.0;i < 2.0 * M_PI;i += (2.0 * M_PI) / 500.0) {
			phase_now_override = i;
			chThdSleepMilliseconds(1);
		}
	}

	// Rotate a bit more
	for (float i = 0.0;i < 2.0 * M_PI;i += (2.0 * M_PI) / 500.0) {
		phase_now_override = i;
		chThdSleepMilliseconds(1);
	}

	float encoder_samp = 0.0;

	// Forwards
	for (float i = 0.0;i < 2.0 * M_PI;i += (2.0 * M_PI) / 500.0) {
		phase_now_override = i;
		chThdSleepMilliseconds(1);
		encoder_samp += phase_now;
	}

	// Reverse
	for (float i = 2.0 * M_PI;i > 0.0;i -= (2.0 * M_PI) / 500.0) {
		phase_now_override = i;
		chThdSleepMilliseconds(1);
		encoder_samp += phase_now;
	}

	id_set = 0.0;
	phase_override = false;
	state = MC_STATE_OFF;
	stop_pwm_hw();

	*offset = encoder_samp / 1000.0;
}

void mcpwm_foc_adc_inj_int_handler(void) {
	int curr0 = ADC_GetInjectedConversionValue(ADC1, ADC_InjectedChannel_1);
	int curr1 = ADC_GetInjectedConversionValue(ADC2, ADC_InjectedChannel_1);

	curr0_sum += curr0;
	curr1_sum += curr1;
	curr_start_samples++;

	curr0 -= curr0_offset;
	curr1 -= curr1_offset;

	ADC_curr_norm_value[0] = curr0;
	ADC_curr_norm_value[1] = curr1;
	ADC_curr_norm_value[2] = -(ADC_curr_norm_value[0] + ADC_curr_norm_value[1]);

	float ia = -ADC_curr_norm_value[0] * (V_REG / 4095.0) / (CURRENT_SHUNT_RES * CURRENT_AMP_GAIN);
	float ib = -ADC_curr_norm_value[2] * (V_REG / 4095.0) / (CURRENT_SHUNT_RES * CURRENT_AMP_GAIN);

	float phase_tmp = encoder_read_deg();
	phase_tmp *= ECNODER_MOTOR_RATIO;
	if (!phase_override) {
		phase_tmp -= conf->foc_encoder_offset;
	}
	utils_norm_angle((float*)&phase_tmp);
	if (conf->foc_encoder_inverted) {
		phase_tmp = 360.0 - phase_tmp;
	}
	phase_now = phase_tmp * (M_PI / 180.0);

	float phase = phase_override ? phase_now_override : phase_now;

	if (state == MC_STATE_RUNNING) {
		float id, iq;
		const float dt = 1.0 / (conf->foc_f_sw / 2.0);

		// Apply current limits
		// TODO: Have another look at this since it only is implemented on the
		// direct axis now.
		const float Vbus = GET_INPUT_VOLTAGE();
		float mod_d = voltage_state_d / ((2.0 / 3.0) * Vbus);
		float id_set_tmp = id_set;
		utils_truncate_number(&id_set_tmp, conf->lo_current_min, conf->lo_current_max);
		if (mod_d > 0.0) {
			utils_truncate_number(&id_set_tmp, conf->lo_in_current_min / mod_d, conf->lo_in_current_max / mod_d);
		} else {
			utils_truncate_number(&id_set_tmp, conf->lo_in_current_max / mod_d, conf->lo_in_current_min / mod_d);
		}
		id_set = id_set_tmp;

		control_current(id_set, iq_set, ia, ib, phase, &current_in,
				&id, &iq, &voltage_state_d, &voltage_state_q, dt);
		current_in_filtered = current_in;
		current = id;
		current_filtered = current;
		run_pid_control_pos(dt);
	} else {
		current_in = 0.0;
		current_in_filtered = 0.0;
		current = 0.0;
		current_filtered = 0.0;

		// Track back emf
		float Va = ADC_VOLTS(ADC_IND_SENS1) * ((VIN_R1 + VIN_R2) / VIN_R2);
		float Vb = ADC_VOLTS(ADC_IND_SENS2) * ((VIN_R1 + VIN_R2) / VIN_R2);
		float Vc = ADC_VOLTS(ADC_IND_SENS3) * ((VIN_R1 + VIN_R2) / VIN_R2);

		// Clarke transform
		float Valpha = (2.0f / 3.0f) * Va - (1.0f / 3.0f) * Vb - (1.0f / 3.0f) * Vc;
		float Vbeta = ONE_BY_SQRT3 * Vb - ONE_BY_SQRT3 * Vc;

		// Park transform
		float c,s;
		// TODO Make fast sin/cos implementation or use arm_math
		sincosf(phase_now, &s, &c);
		voltage_state_d = -(c * Valpha + s * Vbeta);
		voltage_state_q = -(c * Vbeta  - s * Valpha);
	}
}

void mcpwm_foc_adc_int_handler(void *p, uint32_t flags) {
	(void)p;
	(void)flags;

	// Attempt to update the timer.
	update_timer_attempt();

	// Reset the watchdog
	WWDG_SetCounter(100);

	// Code...

	mc_interface_mc_timer_isr();
}

// Private functions

static THD_FUNCTION(timer_thread, arg) {
	(void)arg;

	chRegSetThreadName("mcpwm_foc timer");
	mcpwm_foc_encoder_detect(10.0, (float*)&conf->foc_encoder_offset, (bool*)&conf->foc_encoder_inverted);

	for(;;) {
		chThdSleepMilliseconds(100);
//		commands_printf("Vd: %.2f", (double)voltage_state_d);
//		commands_printf("Vq: %.2f", (double)voltage_state_q);
	}

}

static void do_dc_cal(void) {
	DCCAL_ON();
	while(IS_DRV_FAULT()){};
	chThdSleepMilliseconds(1000);
	curr0_sum = 0;
	curr1_sum = 0;
	curr_start_samples = 0;
	while(curr_start_samples < 4000) {};
	curr0_offset = curr0_sum / curr_start_samples;
	curr1_offset = curr1_sum / curr_start_samples;
	DCCAL_OFF();
	dccal_done = true;
}

static void control_current(float targetId, float targetIq, float Ia, float Ib,
		float phase, volatile float* IbusEst, volatile float* Id,
		volatile float* Iq, volatile float *vstate_d, volatile float *vstate_q,
		float dt) {

	mc_timer_struct timer_settings;
	get_timer_settings(&timer_settings);

	const float Ialpha = Ia;
	const float Ibeta = ONE_BY_SQRT3 * Ia + TWO_BY_SQRT3 * Ib;
	const float Vbus = GET_INPUT_VOLTAGE();

	float c,s;
	// TODO Make fast sin/cos implementation or use arm_math
	sincosf(phase, &s, &c);

	*Id = c * Ialpha + s * Ibeta;
	*Iq = c * Ibeta  - s * Ialpha;

	float Ierr_d = targetId - *Id;
	float Ierr_q = targetIq - *Iq;

	float Vd = *vstate_d + Ierr_d * conf->foc_current_kp;
	float Vq = *vstate_q + Ierr_q * conf->foc_current_kp;
	*vstate_d += Ierr_d * (conf->foc_current_ki * dt);
	*vstate_q += Ierr_q * (conf->foc_current_ki * dt);

	float mod_d = Vd / ((2.0 / 3.0) * Vbus);
	float mod_q = Vq / ((2.0 / 3.0) * Vbus);

	// Windup protection and saturation
	utils_saturate_vector_2d(&mod_d, &mod_q, SQRT3_BY_2 * conf->l_max_duty);
	utils_saturate_vector_2d((float*)vstate_d, (float*)vstate_q,
			(2.0 / 3.0) * conf->l_max_duty * SQRT3_BY_2 * Vbus);

	*IbusEst = mod_d * *Id + mod_q * *Iq;

	float Valpha = c * mod_d - s * mod_q;
	float Vbeta  = c * mod_q + s * mod_d;

	svm(Valpha, Vbeta, timer_settings.top, &timer_settings.duty1,
			&timer_settings.duty2, &timer_settings.duty3);

	set_next_timer_settings(&timer_settings);

	if (!output_on) {
		start_pwm_hw();
	}
}

// Magnitude must not be larger than sqrt(3)/2, or 0.866
static void svm(float alpha, float beta, volatile uint32_t PWMHalfPeriod,
		volatile uint32_t* tAout, volatile uint32_t* tBout,
		volatile uint32_t* tCout) {
	uint32_t Sextant;

	if (beta >= 0.0f) {
		if (alpha >= 0.0f) {
			//quadrant I
			if (ONE_BY_SQRT3 * beta > alpha)
				Sextant = 2;
			else
				Sextant = 1;
		} else {
			//quadrant II
			if (-ONE_BY_SQRT3 * beta > alpha)
				Sextant = 3;
			else
				Sextant = 2;
		}
	} else {
		if (alpha >= 0.0f) {
			//quadrant IV
			if (-ONE_BY_SQRT3 * beta > alpha)
				Sextant = 5;
			else
				Sextant = 6;
		} else {
			//quadrant III
			if (ONE_BY_SQRT3 * beta > alpha)
				Sextant = 4;
			else
				Sextant = 5;
		}
	}

	// PWM timings
	uint32_t tA, tB, tC;

	switch (Sextant) {

	// sextant 1-2
	case 1: {
		// Vector on-times
		uint32_t t1 = (alpha - ONE_BY_SQRT3 * beta) * PWMHalfPeriod;
		uint32_t t2 = (TWO_BY_SQRT3 * beta) * PWMHalfPeriod;

		// PWM timings
		tA = (PWMHalfPeriod - t1 - t2) / 2;
		tB = tA + t1;
		tC = tB + t2;

		break;
	}

		// sextant 2-3
	case 2: {
		// Vector on-times
		uint32_t t2 = (alpha + ONE_BY_SQRT3 * beta) * PWMHalfPeriod;
		uint32_t t3 = (-alpha + ONE_BY_SQRT3 * beta) * PWMHalfPeriod;

		// PWM timings
		tB = (PWMHalfPeriod - t2 - t3) / 2;
		tA = tB + t3;
		tC = tA + t2;

		break;
	}

		// sextant 3-4
	case 3: {
		// Vector on-times
		uint32_t t3 = (TWO_BY_SQRT3 * beta) * PWMHalfPeriod;
		uint32_t t4 = (-alpha - ONE_BY_SQRT3 * beta) * PWMHalfPeriod;

		// PWM timings
		tB = (PWMHalfPeriod - t3 - t4) / 2;
		tC = tB + t3;
		tA = tC + t4;

		break;
	}

		// sextant 4-5
	case 4: {
		// Vector on-times
		uint32_t t4 = (-alpha + ONE_BY_SQRT3 * beta) * PWMHalfPeriod;
		uint32_t t5 = (-TWO_BY_SQRT3 * beta) * PWMHalfPeriod;

		// PWM timings
		tC = (PWMHalfPeriod - t4 - t5) / 2;
		tB = tC + t5;
		tA = tB + t4;

		break;
	}

		// sextant 5-6
	case 5: {
		// Vector on-times
		uint32_t t5 = (-alpha - ONE_BY_SQRT3 * beta) * PWMHalfPeriod;
		uint32_t t6 = (alpha - ONE_BY_SQRT3 * beta) * PWMHalfPeriod;

		// PWM timings
		tC = (PWMHalfPeriod - t5 - t6) / 2;
		tA = tC + t5;
		tB = tA + t6;

		break;
	}

		// sextant 6-1
	case 6: {
		// Vector on-times
		uint32_t t6 = (-TWO_BY_SQRT3 * beta) * PWMHalfPeriod;
		uint32_t t1 = (alpha + ONE_BY_SQRT3 * beta) * PWMHalfPeriod;

		// PWM timings
		tA = (PWMHalfPeriod - t6 - t1) / 2;
		tC = tA + t1;
		tB = tC + t6;

		break;
	}
	}

	*tAout = tA;
	*tBout = tB;
	*tCout = tC;
}

static void run_pid_control_pos(float dt) {
	static float i_term = 0;
	static float prev_error = 0;
	float p_term;
	float d_term;

	// PID is off. Return.
	if (control_mode != CONTROL_MODE_POS) {
		i_term = 0;
		prev_error = 0;
		return;
	}

	// Compute error
	float angle = conf->foc_encoder_inverted ? encoder_read_deg() : 360.0 - encoder_read_deg();
	float error = utils_angle_difference(angle, pos_pid_set_pos);

	// Compute parameters
	p_term = error * conf->p_pid_kp;
	i_term += error * (conf->p_pid_ki * dt);
	d_term = (error - prev_error) * (conf->p_pid_kd / dt);

	// I-term wind-up protection
	utils_truncate_number(&i_term, -1.0, 1.0);

	// Store previous error
	prev_error = error;

	// Calculate output
	float output = p_term + i_term + d_term;
	utils_truncate_number(&output, -1.0, 1.0);

	id_set = output * conf->lo_current_max;
}

static void get_timer_settings(mc_timer_struct *settings) {
	utils_sys_lock_cnt();
	*settings = timer_struct;
	utils_sys_unlock_cnt();
}

static void set_next_timer_settings(mc_timer_struct *settings) {
	utils_sys_lock_cnt();
	timer_struct = *settings;
	timer_struct.updated = false;
	utils_sys_unlock_cnt();

	update_timer_attempt();
}

/**
 * Try to apply the new timer settings. This is really not an elegant solution, but for now it is
 * the best I can come up with.
 */
static void update_timer_attempt(void) {
	utils_sys_lock_cnt();

	// Set the next timer settings if an update is far enough away
	// TODO: Maybe check if an update is far away
	if (!timer_struct.updated) {
		// Disable preload register updates
		TIM1->CR1 |= TIM_CR1_UDIS;
		TIM8->CR1 |= TIM_CR1_UDIS;

		// Set the new configuration
		TIM1->ARR = timer_struct.top;
		TIM8->ARR = timer_struct.top;
		TIM1->CCR1 = timer_struct.duty1;
		TIM1->CCR2 = timer_struct.duty2;
		TIM1->CCR3 = timer_struct.duty3;
		TIM8->CCR1 = timer_struct.val_sample;
		TIM1->CCR4 = timer_struct.curr1_sample;
		TIM8->CCR2 = timer_struct.curr2_sample;

		// Enables preload register updates
		TIM1->CR1 &= ~TIM_CR1_UDIS;
		TIM8->CR1 &= ~TIM_CR1_UDIS;
		timer_struct.updated = true;
	}

	utils_sys_unlock_cnt();
}

static void stop_pwm_hw(void) {
	TIM_SelectOCxM(TIM1, TIM_Channel_1, TIM_ForcedAction_InActive);
	TIM_CCxCmd(TIM1, TIM_Channel_1, TIM_CCx_Enable);
	TIM_CCxNCmd(TIM1, TIM_Channel_1, TIM_CCxN_Disable);

	TIM_SelectOCxM(TIM1, TIM_Channel_2, TIM_ForcedAction_InActive);
	TIM_CCxCmd(TIM1, TIM_Channel_2, TIM_CCx_Enable);
	TIM_CCxNCmd(TIM1, TIM_Channel_2, TIM_CCxN_Disable);

	TIM_SelectOCxM(TIM1, TIM_Channel_3, TIM_ForcedAction_InActive);
	TIM_CCxCmd(TIM1, TIM_Channel_3, TIM_CCx_Enable);
	TIM_CCxNCmd(TIM1, TIM_Channel_3, TIM_CCxN_Disable);

	TIM_GenerateEvent(TIM1, TIM_EventSource_COM);

	output_on = false;
}

static void start_pwm_hw(void) {
	TIM_SelectOCxM(TIM1, TIM_Channel_1, TIM_OCMode_PWM1);
	TIM_CCxCmd(TIM1, TIM_Channel_1, TIM_CCx_Enable);
	TIM_CCxNCmd(TIM1, TIM_Channel_1, TIM_CCxN_Enable);

	TIM_SelectOCxM(TIM1, TIM_Channel_2, TIM_OCMode_PWM1);
	TIM_CCxCmd(TIM1, TIM_Channel_2, TIM_CCx_Enable);
	TIM_CCxNCmd(TIM1, TIM_Channel_2, TIM_CCxN_Enable);

	TIM_SelectOCxM(TIM1, TIM_Channel_3, TIM_OCMode_PWM1);
	TIM_CCxCmd(TIM1, TIM_Channel_3, TIM_CCx_Enable);
	TIM_CCxNCmd(TIM1, TIM_Channel_3, TIM_CCxN_Enable);

	TIM_GenerateEvent(TIM1, TIM_EventSource_COM);

	output_on = true;
}
