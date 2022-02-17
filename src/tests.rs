use crate::{Configuration, Error, RepetitionResult, RepetitionState};
use chrono::{DateTime, Duration, NaiveDate, NaiveDateTime, NaiveTime, Utc};
use std::mem;

fn create_test_configuration() -> Configuration {
    Configuration {
        learning_phase_stage_delay_seconds: vec![10, 10, 20, 60],
        learning_phase_easy_skip_stages: 1,
        learning_phase_easy_may_skip_last_stage: false,
        reviewing_phase_initial_delay_seconds: 600,
        reviewing_phase_initial_ease_factor: 2.5,
        reviewing_phase_min_ease_factor: 1.3,
        reviewing_phase_max_ease_factor: 5.0,
        reviewing_phase_initial_ease_max_easy_count: 1,
        reviewing_phase_initial_ease_max_hard_count: 1,
        reviewing_phase_ease_factor_easy_update: 1.15,
        reviewing_phase_ease_factor_hard_update: 1.0 / 1.15,
    }
}

fn datetime(seconds: i64) -> DateTime<Utc> {
    DateTime::<Utc>::from_utc(
        NaiveDateTime::new(
            NaiveDate::from_ymd(2000, 1, 1),
            NaiveTime::from_hms(1, 0, 0),
        ),
        Utc,
    ) + Duration::seconds(seconds)
}

fn new() -> RepetitionState {
    RepetitionState::new(datetime(0))
}

fn update(
    state: &mut RepetitionState,
    seconds: i64,
    result: RepetitionResult,
    configuration: &Configuration,
) -> Result<(), Error> {
    let mut tmp_state = new();
    mem::swap(&mut tmp_state, state);
    *state = tmp_state.update(datetime(seconds), result, configuration)?;
    Ok(())
}

fn update_unwrap(
    repetition_state: &mut RepetitionState,
    seconds: i64,
    result: RepetitionResult,
    configuration: &Configuration,
) {
    update(repetition_state, seconds, result, configuration).unwrap();
}

fn assert_learning(state: &RepetitionState, easy_count: i16, stage: u16, next_repetition_seconds: i64) {
    match state {
        RepetitionState::Reviewing { .. } => panic!(),

        RepetitionState::Learning {
            easy_count: easy_count_is,
            stage: stage_is,
            next_repetition: next_repetition_is,
        } => {
            assert_eq!(*easy_count_is, easy_count);
            assert_eq!(*stage_is, stage);
            assert_eq!(*next_repetition_is, datetime(next_repetition_seconds));
        }
    }
}

fn assert_reviewing(state: &RepetitionState, ease_factor: f64, last_repetition_seconds: i64, next_repetition_seconds: i64) {
    match state {
        RepetitionState::Reviewing { ease_factor: ease_factor_is, last_repetition: last_repetition_is, next_repetition: next_repetition_is } => {
            assert!((ease_factor - *ease_factor_is).abs() < 1e-4);
            assert_eq!(*last_repetition_is, datetime(last_repetition_seconds));
            assert_eq!(*next_repetition_is, datetime(next_repetition_seconds));
        }
        RepetitionState::Learning { .. } => panic!(),    }
}

#[test]
fn test_learning_phase_normal() {
    let configuration = create_test_configuration();
    let mut state = new();

    update_unwrap(&mut state, 2, RepetitionResult::Normal, &configuration);
    assert_learning(&state, 0, 1, 12);

    update_unwrap(&mut state, 14, RepetitionResult::Normal, &configuration);
    assert_learning(&state, 0, 2, 24);

    update_unwrap(&mut state, 24, RepetitionResult::Normal, &configuration);
    assert_learning(&state, 0, 3, 44);

    update_unwrap(&mut state, 60, RepetitionResult::Normal, &configuration);
    assert_learning(&state, 0, 4, 120);

    update_unwrap(&mut state, 121, RepetitionResult::Normal, &configuration);
    assert_reviewing(&state, 2.5, 121, 721);
}