use chrono::Duration;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Serialize, Deserialize)]
pub struct DurationInMilliseconds {
    duration: i64,
}

impl From<Duration> for DurationInMilliseconds {
    fn from(duration: Duration) -> Self {
        Self {
            duration: duration.num_milliseconds(),
        }
    }
}

impl From<DurationInMilliseconds> for Duration {
    fn from(duration: DurationInMilliseconds) -> Self {
        Self::milliseconds(duration.duration)
    }
}
