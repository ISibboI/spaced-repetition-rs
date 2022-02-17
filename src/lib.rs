use crate::hacks::DurationInMilliseconds;
use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};

/// Some crates are missing important features
mod hacks;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum RepetitionState {
    Reviewing {
        ease_factor: f64,
        current_interval: DurationInMilliseconds,
        next_review: DateTime<Utc>,
    },

    Learning {
        stage: u8,
        next_review: DateTime<Utc>,
    },
}
