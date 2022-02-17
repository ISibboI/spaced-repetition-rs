//! A library implementing a spaced repetition algorithm.

#![warn(missing_docs)]

use chrono::{DateTime, Duration, TimeZone, Utc};
use serde::{Deserialize, Serialize};

#[cfg(test)]
mod tests;

/// The repetition state of a learnable item.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum RepetitionState {
    /// The item has made it through the initial learning phase and will now be repeated at larger intervals.
    Reviewing {
        /// The ease factor of the word.
        /// It influences how fast the intervals between repetitions get larger.
        ease_factor: f64,
        /// The time of the last repetition.
        last_repetition: DateTime<Utc>,
        /// The time of the next repetition.
        next_repetition: DateTime<Utc>,
    },

    /// The item is in the initial learning phase where it is repeated in shorter intervals.
    Learning {
        /// The count of easy repetition results.
        /// [RepetitionResult::Easy] increments this by one, and [RepetitionResult::Hard] and [RepetitionResult::Again] decrement this by one.
        easy_count: i16,
        /// The current stage of the item within the learning phase.
        stage: u16,
        /// The time of the next repetition.
        next_repetition: DateTime<Utc>,
    },
}

impl RepetitionState {
    /// Construct a new repetition state in learning stage 0, with its first repetition being at the given `datetime`.
    pub fn new<TZ: TimeZone>(datetime: DateTime<TZ>) -> Self {
        Self::Learning {
            easy_count: 0,
            stage: 0,
            next_repetition: datetime.with_timezone(&Utc),
        }
    }

    /// Update the repetition state after an item was repeated by the user.
    /// The time of the repetition was `datetime`, and the result of the repetition was `result`.
    /// The configuration of the algorithm is given as `configuration`.
    pub fn update<TZ: TimeZone>(
        self,
        datetime: DateTime<TZ>,
        result: RepetitionResult,
        configuration: &Configuration,
    ) -> Result<Self, Error> {
        let datetime = datetime.with_timezone(&Utc);
        match self {
            RepetitionState::Reviewing { .. } => {
                todo!()
            }
            RepetitionState::Learning {
                easy_count, stage, ..
            } => {
                match result {
                    // If the user chooses again during learning, the word starts from the beginning.
                    RepetitionResult::Again => {
                        if let Some(delay_seconds) = configuration
                            .learning_phase_stage_delay_seconds
                            .first()
                            .cloned()
                        {
                            Ok(Self::Learning {
                                stage: 0,
                                easy_count: easy_count.checked_sub(1).ok_or(Error::Overflow)?,
                                next_repetition: datetime + Duration::seconds(delay_seconds.into()),
                            })
                        } else {
                            Err(Error::ConfigurationMissesLearningStage)
                        }
                    }
                    RepetitionResult::Hard => {
                        if let Some(delay_seconds) = configuration
                            .learning_phase_stage_delay_seconds
                            .get(usize::from(stage.max(1) - 1)) // Cannot overflow because it is at least one.
                            .cloned()
                        {
                            Ok(Self::Learning {
                                stage,
                                easy_count: easy_count.checked_sub(1).ok_or(Error::Overflow)?,
                                next_repetition: datetime
                                    .checked_add_signed(Duration::seconds(delay_seconds.into()))
                                    .ok_or(Error::Overflow)?,
                            })
                        } else {
                            Err(Error::ConfigurationMissesLearningStage)
                        }
                    }
                    RepetitionResult::Normal => {
                        if let Some(delay_seconds) = configuration
                            .learning_phase_stage_delay_seconds
                            .get(usize::from(stage))
                            .cloned()
                        {
                            Ok(Self::Learning {
                                stage: stage.checked_add(1).ok_or(Error::Overflow)?,
                                easy_count,
                                next_repetition: datetime
                                    .checked_add_signed(Duration::seconds(delay_seconds.into()))
                                    .ok_or(Error::Overflow)?,
                            })
                        } else {
                            let (delay_seconds, ease_factor) = configuration
                                .reviewing_phase_initial_delay_seconds_and_ease_factor(
                                    easy_count,
                                )?;
                            Ok(Self::Reviewing {
                                ease_factor,
                                last_repetition: datetime,
                                next_repetition: datetime
                                    .checked_add_signed(Duration::seconds(delay_seconds.into()))
                                    .ok_or(Error::Overflow)?,
                            })
                        }
                    }
                    RepetitionResult::Easy => {
                        if usize::from(stage)
                            >= configuration.learning_phase_stage_delay_seconds.len()
                            || (configuration.learning_phase_easy_may_skip_last_stage
                                && usize::from(
                                    stage
                                        .checked_add(configuration.learning_phase_easy_skip_stages)
                                        .ok_or(Error::Overflow)?,
                                ) >= configuration.learning_phase_stage_delay_seconds.len())
                        {
                            let (delay_seconds, ease_factor) = configuration
                                .reviewing_phase_initial_delay_seconds_and_ease_factor(
                                    easy_count,
                                )?;
                            Ok(Self::Reviewing {
                                ease_factor,
                                last_repetition: datetime,
                                next_repetition: datetime
                                    .checked_add_signed(Duration::seconds(delay_seconds.into()))
                                    .ok_or(Error::Overflow)?,
                            })
                        } else {
                            let stage = (stage + configuration.learning_phase_easy_skip_stages)
                                .min(
                                    u16::try_from(
                                        configuration.learning_phase_stage_delay_seconds.len(),
                                    )
                                    .map_err(|_| Error::Overflow)?
                                    .checked_sub(1)
                                    .ok_or(Error::ConfigurationMissesLearningStage)?,
                                );
                            let delay_seconds = configuration
                                .learning_phase_stage_delay_seconds
                                .get(usize::from(stage))
                                .cloned()
                                .unwrap();
                            Ok(Self::Learning {
                                stage: stage.checked_add(1).ok_or(Error::Overflow)?,
                                easy_count: easy_count.checked_add(1).ok_or(Error::Overflow)?,
                                next_repetition: datetime
                                    .checked_add_signed(Duration::seconds(delay_seconds.into()))
                                    .ok_or(Error::Overflow)?,
                            })
                        }
                    }
                }
            }
        }
    }
}

/// The configuration of the algorithm.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Configuration {
    /// The delays between repetitions in the initial learning phase.
    /// These are given as seconds.
    ///
    /// **Warning:** This vector must contain at least one value.
    ///
    /// **Example:**
    /// Setting learning_stages to `[10, 60]` causes the item to be repeated 10 seconds after the initial repetition, and another 60 seconds after that.
    pub learning_phase_stage_delay_seconds: Vec<u16>,

    /// The amount of stages skipped if the user chooses easy in the learning phase.
    /// A value of zero resembles the behaviour of a normal result.
    pub learning_phase_easy_skip_stages: u16,

    /// If true, if the user chooses easy in the learning phase and this would skip past the last stage, the item directly enters the reviewing phase.
    /// If false, then the item will always enter the last stage, and only after successfully repeating again the item may enter the reviewing phase.
    pub learning_phase_easy_may_skip_last_stage: bool,

    /// The initial delay in the reviewing phase in seconds.
    pub reviewing_phase_initial_delay_seconds: u32,

    /// The initial ease factor used in the reviewing phase.
    pub reviewing_phase_initial_ease_factor: f64,

    /// The minimum ease factor used in the reviewing phase.
    pub reviewing_phase_min_ease_factor: f64,

    /// The maximum ease factor used in the reviewing phase.
    pub reviewing_phase_max_ease_factor: f64,

    /// The maximum number of easy results from the learning phase to be applied to the initial ease factor when entering the reviewing phase.
    pub reviewing_phase_initial_ease_max_easy_count: u16,

    /// The maximum number of hard results from the learning phase to be applied to the initial ease factor when entering the reviewing phase.
    pub reviewing_phase_initial_ease_max_hard_count: u16,

    /// The factor applied to the ease factor on an easy result.
    pub reviewing_phase_ease_factor_easy_update: f64,

    /// The factor applied to the ease factor on a hard result.
    pub reviewing_phase_ease_factor_hard_update: f64,
}

impl Configuration {
    fn reviewing_phase_initial_ease_factor(&self, easy_count: i16) -> Result<f64, Error> {
        if self.reviewing_phase_initial_ease_factor < 1.0 {
            return Err(Error::ReviewingPhaseInitialEaseFactorLowerThanOne);
        }

        if easy_count == 0 {
            Ok(self.reviewing_phase_initial_ease_factor)
        } else if easy_count > 0 {
            let easy_count = easy_count.min(
                self.reviewing_phase_initial_ease_max_easy_count
                    .try_into()
                    .map_err(|_| Error::Overflow)?,
            );
            if self.reviewing_phase_ease_factor_easy_update < 1.0 {
                return Err(Error::ReviewingPhaseEaseFactorEasyUpdateLowerThanOne);
            }
            Ok((self.reviewing_phase_initial_ease_factor
                * self
                    .reviewing_phase_ease_factor_easy_update
                    .powi(easy_count.into()))
            .min(self.reviewing_phase_max_ease_factor))
        } else
        /* easy_count < 0 */
        {
            let hard_count = easy_count.checked_mul(-1).ok_or(Error::Overflow)?.min(
                self.reviewing_phase_initial_ease_max_hard_count
                    .try_into()
                    .map_err(|_| Error::Overflow)?,
            );
            if self.reviewing_phase_ease_factor_hard_update > 1.0 {
                return Err(Error::ReviewingPhaseEaseFactorHardUpdateGreaterThanOne);
            }
            Ok((self.reviewing_phase_initial_ease_factor
                * self
                    .reviewing_phase_ease_factor_hard_update
                    .powi(hard_count.into()))
            .max(self.reviewing_phase_min_ease_factor))
        }
    }

    fn reviewing_phase_initial_delay_seconds_and_ease_factor(
        &self,
        easy_count: i16,
    ) -> Result<(u32, f64), Error> {
        let initial_ease_factor = self.reviewing_phase_initial_ease_factor(easy_count)?;
        let ease_ratio = initial_ease_factor / self.reviewing_phase_initial_ease_factor;
        let initial_delay_seconds =
            (f64::from(self.reviewing_phase_initial_delay_seconds) * ease_ratio).round();

        // Subtract one because I am not totally sure how accurately u32 -> f64 conversion works.
        if initial_delay_seconds >= (u32::MAX - 1) as f64 {
            Err(Error::Overflow)
        } else {
            Ok((initial_delay_seconds as u32, initial_ease_factor))
        }
    }
}

/// The result of a repetition as specified by the user.
#[derive(Clone, Copy, Debug, Serialize, Deserialize, Eq, PartialEq)]
pub enum RepetitionResult {
    /// The user was not able to repeat the item.
    Again,
    /// The user was able to repeat the item, but found it especially hard.
    Hard,
    /// The user was able to repeat the item, with average difficulty.
    Normal,
    /// The user was able to repeat the item, and found it especially easy.
    Easy,
}

/// The error type used by this crate.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Error {
    /// The configuration has no or not enough stages in the learning phase.
    /// The stages in the learning phase are defined by [Configuration::learning_phase_stage_delay_seconds].
    ConfigurationMissesLearningStage,

    /// The value of [Configuration::reviewing_phase_ease_factor_easy_update] is lower than one.
    ReviewingPhaseEaseFactorEasyUpdateLowerThanOne,

    /// The value of [Configuration::reviewing_phase_ease_factor_hard_update] is greater than one.
    ReviewingPhaseEaseFactorHardUpdateGreaterThanOne,

    /// The value of [Configuration::reviewing_phase_initial_ease_factor] is lower than one.
    ReviewingPhaseInitialEaseFactorLowerThanOne,

    /// An overflow occurred.
    Overflow,
}
