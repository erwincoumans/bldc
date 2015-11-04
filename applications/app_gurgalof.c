/*
	Copyright 2012-2014 Benjamin Vedder	benjamin@vedder.se

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
 * app_gurgalof.c
 *
 *  Created on: 18 apr 2014
 *      Author: benjamin
 */

#include "app.h"
#ifdef USE_APP_GURGALOF

#include "ch.h"
#include "hal.h"
#include "stm32f4xx_conf.h"
#include "servo_dec.h"
#include "mc_interface.h"
#include "hw.h"
#include "timeout.h"

// Threads
static THD_FUNCTION(gurgalof_thread, arg);
static THD_WORKING_AREA(gurgalof_thread_wa, 1024);

void app_gurgalof_init(void) {
	chThdCreateStatic(gurgalof_thread_wa, sizeof(gurgalof_thread_wa), NORMALPRIO, gurgalof_thread, NULL);
}

static THD_FUNCTION(gurgalof_thread, arg) {
	(void)arg;

	chRegSetThreadName("APP_GURGALOF");

	for(;;) {
#define MIN_PWR	0.2
		float pwr = (float)ADC_Value[ADC_IND_EXT];
		pwr /= 4095.0;
		pwr /= (1.0 - MIN_PWR);
		pwr -= MIN_PWR;

		if (pwr < 0.0) {
			mc_interface_set_current(0.0);
		} else {
			mc_interface_set_duty(pwr);
//			mc_interface_set_current(pwr * mc_interface_get_configuration()->l_current_max);
		}

		timeout_reset();
		chThdSleepMilliseconds(10);
	}
}

#endif
