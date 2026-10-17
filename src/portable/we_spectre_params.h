#ifndef WE_SPECTRE_PARAMS_H
#define WE_SPECTRE_PARAMS_H

/* Protocol settings. These control branch training, not CPU cache geometry. */
#define WE_TRAIN_CALLS 30
#define WE_TRAIN_PERIOD 6
#define WE_TRAIN_DELAY_SPINS 100
#define WE_MAX_TRIES 999

#if WE_TRAIN_CALLS % WE_TRAIN_PERIOD != 0
#error WE_TRAIN_CALLS must contain complete training periods
#endif

#endif
