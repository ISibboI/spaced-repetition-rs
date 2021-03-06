use crate::{Configuration, Error, Jitter, RepetitionResult, RepetitionState};
use chrono::{DateTime, Duration, NaiveDate, NaiveDateTime, NaiveTime, Utc};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha12Rng;
use std::mem;

fn create_test_configuration() -> Configuration {
    Configuration {
        learning_phase_stage_delay_seconds: vec![10, 10, 20, 60],
        learning_phase_easy_skip_stages: 1,
        learning_phase_easy_may_skip_last_stage: false,
        learning_phase_delay_jitter: Jitter::None,
        reviewing_phase_initial_delay_seconds: 600,
        reviewing_phase_initial_ease_factor: 2.5,
        reviewing_phase_min_ease_factor: 1.3,
        reviewing_phase_max_ease_factor: 5.0,
        reviewing_phase_initial_ease_max_easy_count: 1,
        reviewing_phase_initial_ease_max_hard_count: 1,
        reviewing_phase_ease_factor_easy_update: 1.15,
        reviewing_phase_ease_factor_hard_update: 1.0 / 1.15,
        reviewing_phase_ease_factor_again_update: 1.0 / 1.2,
        reviewing_phase_easy_one_time_interval_bonus: 1.5,
        reviewing_phase_hard_fixed_interval_factor: Some(1.2),
        reviewing_phase_delay_jitter: Jitter::None,
    }
}

fn base_datetime() -> DateTime<Utc> {
    DateTime::<Utc>::from_utc(
        NaiveDateTime::new(
            NaiveDate::from_ymd(2000, 1, 1),
            NaiveTime::from_hms(1, 0, 0),
        ),
        Utc,
    )
}

fn datetime(seconds: i64) -> DateTime<Utc> {
    base_datetime() + Duration::seconds(seconds)
}

fn seconds(datetime: &DateTime<Utc>) -> i64 {
    (*datetime - base_datetime()).num_seconds()
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

fn update_with_rng<RngType: Rng>(
    state: &mut RepetitionState,
    seconds: i64,
    result: RepetitionResult,
    configuration: &Configuration,
    rng: &mut RngType,
) -> Result<(), Error> {
    let mut tmp_state = new();
    mem::swap(&mut tmp_state, state);
    *state = tmp_state.update_with_rng(datetime(seconds), result, configuration, rng)?;
    Ok(())
}

fn update_with_rng_unwrap<RngType: Rng>(
    repetition_state: &mut RepetitionState,
    seconds: i64,
    result: RepetitionResult,
    configuration: &Configuration,
    rng: &mut RngType,
) {
    update_with_rng(repetition_state, seconds, result, configuration, rng).unwrap();
}

fn assert_learning(
    state: &RepetitionState,
    easy_count: i16,
    stage: u16,
    next_repetition_seconds: i64,
) {
    match state {
        RepetitionState::Reviewing { .. } => panic!(),

        RepetitionState::Learning {
            easy_count: easy_count_is,
            stage: stage_is,
            next_repetition: next_repetition_is,
        } => {
            assert_eq!(*easy_count_is, easy_count, "Wrong easy count");
            assert_eq!(*stage_is, stage, "Wrong stage");
            assert_eq!(
                *next_repetition_is,
                datetime(next_repetition_seconds),
                "Wrong next repetition"
            );
        }
    }
}

fn assert_reviewing(
    state: &RepetitionState,
    ease_factor: f64,
    last_repetition_seconds: i64,
    next_repetition_seconds: i64,
) {
    match state {
        RepetitionState::Reviewing {
            ease_factor: ease_factor_is,
            last_repetition: last_repetition_is,
            next_repetition: next_repetition_is,
        } => {
            assert!(
                (ease_factor - *ease_factor_is).abs() < 1e-4,
                "Wrong ease factor: should be {ease_factor}, but is {ease_factor_is}"
            );
            let last_repetition_is_seconds = seconds(last_repetition_is);
            assert_eq!(
                *last_repetition_is,
                datetime(last_repetition_seconds),
                "Wrong last repetition: should be {last_repetition_seconds}, but is {last_repetition_is_seconds}"
            );
            let next_repetition_is_seconds = seconds(next_repetition_is);
            assert_eq!(
                *next_repetition_is,
                datetime(next_repetition_seconds),
                "Wrong next repetition: should be {next_repetition_seconds}, but is {next_repetition_is_seconds}"
            );
        }
        RepetitionState::Learning { .. } => panic!(),
    }
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

#[test]
fn test_learning_phase_hard() {
    let configuration = create_test_configuration();
    let mut state = new();

    update_unwrap(&mut state, 2, RepetitionResult::Normal, &configuration);
    assert_learning(&state, 0, 1, 12);

    update_unwrap(&mut state, 14, RepetitionResult::Hard, &configuration);
    assert_learning(&state, -1, 1, 24);

    update_unwrap(&mut state, 25, RepetitionResult::Normal, &configuration);
    assert_learning(&state, -1, 2, 35);

    update_unwrap(&mut state, 34, RepetitionResult::Normal, &configuration);
    assert_learning(&state, -1, 3, 54);

    update_unwrap(&mut state, 60, RepetitionResult::Hard, &configuration);
    assert_learning(&state, -2, 3, 80);

    update_unwrap(&mut state, 121, RepetitionResult::Normal, &configuration);
    assert_learning(&state, -2, 4, 181);

    update_unwrap(&mut state, 190, RepetitionResult::Hard, &configuration);
    assert_learning(&state, -3, 4, 250);

    update_unwrap(&mut state, 256, RepetitionResult::Normal, &configuration);
    assert_reviewing(&state, 2.5 / 1.15, 256, 778);
}

#[test]
fn test_learning_phase_easy() {
    let configuration = create_test_configuration();
    let mut state = new();

    update_unwrap(&mut state, 2, RepetitionResult::Easy, &configuration);
    assert_learning(&state, 1, 2, 12);

    update_unwrap(&mut state, 13, RepetitionResult::Normal, &configuration);
    assert_learning(&state, 1, 3, 33);

    update_unwrap(&mut state, 36, RepetitionResult::Easy, &configuration);
    assert_learning(&state, 2, 4, 96);

    update_unwrap(&mut state, 100, RepetitionResult::Easy, &configuration);
    assert_reviewing(&state, 2.5 * 1.15, 100, 790);
}

#[test]
fn test_reviewing_phase() {
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

    update_unwrap(&mut state, 400, RepetitionResult::Normal, &configuration);
    assert_reviewing(&state, 2.5, 400, 1000);

    update_unwrap(&mut state, 1000, RepetitionResult::Normal, &configuration);
    assert_reviewing(&state, 2.5, 1000, 2500);

    update_unwrap(&mut state, 3000, RepetitionResult::Normal, &configuration);
    assert_reviewing(&state, 2.5, 3000, 8000);

    update_unwrap(&mut state, 9000, RepetitionResult::Easy, &configuration);
    assert_reviewing(&state, 2.5 * 1.15, 9000, 34875);

    update_unwrap(&mut state, 35000, RepetitionResult::Again, &configuration);
    assert_reviewing(&state, 2.5 * 1.15 / 1.2, 35000, 35575);

    update_unwrap(&mut state, 36000, RepetitionResult::Hard, &configuration);
    assert_reviewing(&state, 2.5 / 1.2, 36000, 37200);
}

#[test]
fn test_jitter() {
    let mut configuration = create_test_configuration();
    configuration.learning_phase_delay_jitter = Jitter::Gaussian {
        standard_deviation: 0.05,
    };
    configuration.reviewing_phase_delay_jitter = Jitter::Gaussian {
        standard_deviation: 0.05,
    };
    let mut state = new();
    // Use a fixed rng algorithm and seed to prevent this test from breaking in the future.
    let mut rng = ChaCha12Rng::seed_from_u64(0);

    update_with_rng_unwrap(
        &mut state,
        2,
        RepetitionResult::Normal,
        &configuration,
        &mut rng,
    );
    assert_learning(&state, 0, 1, 12);

    update_with_rng_unwrap(
        &mut state,
        14,
        RepetitionResult::Normal,
        &configuration,
        &mut rng,
    );
    assert_learning(&state, 0, 2, 24);

    update_with_rng_unwrap(
        &mut state,
        24,
        RepetitionResult::Normal,
        &configuration,
        &mut rng,
    );
    assert_learning(&state, 0, 3, 42);

    update_with_rng_unwrap(
        &mut state,
        60,
        RepetitionResult::Normal,
        &configuration,
        &mut rng,
    );
    assert_learning(&state, 0, 4, 120);

    update_with_rng_unwrap(
        &mut state,
        400,
        RepetitionResult::Normal,
        &configuration,
        &mut rng,
    );
    assert_reviewing(&state, 2.5, 400, 962);

    update_with_rng_unwrap(
        &mut state,
        1000,
        RepetitionResult::Normal,
        &configuration,
        &mut rng,
    );
    assert_reviewing(&state, 2.5, 1000, 2596);

    update_with_rng_unwrap(
        &mut state,
        3000,
        RepetitionResult::Normal,
        &configuration,
        &mut rng,
    );
    assert_reviewing(&state, 2.5, 3000, 7629);

    update_with_rng_unwrap(
        &mut state,
        9000,
        RepetitionResult::Easy,
        &configuration,
        &mut rng,
    );
    assert_reviewing(&state, 2.5 * 1.15, 9000, 35667);

    update_with_rng_unwrap(
        &mut state,
        35000,
        RepetitionResult::Again,
        &configuration,
        &mut rng,
    );
    assert_reviewing(&state, 2.5 * 1.15 / 1.2, 35000, 35592);

    update_with_rng_unwrap(
        &mut state,
        36000,
        RepetitionResult::Hard,
        &configuration,
        &mut rng,
    );
    assert_reviewing(&state, 2.5 / 1.2, 36000, 37304);
}

#[test]
fn test_early_repetitions() {
    let configuration = create_test_configuration();
    let mut state = new();

    update_unwrap(&mut state, 2, RepetitionResult::Normal, &configuration);
    assert_learning(&state, 0, 1, 12);

    update_unwrap(&mut state, 10, RepetitionResult::Normal, &configuration);
    assert_learning(&state, 0, 2, 20);

    update_unwrap(&mut state, 15, RepetitionResult::Normal, &configuration);
    assert_learning(&state, 0, 3, 35);

    update_unwrap(&mut state, 30, RepetitionResult::Normal, &configuration);
    assert_learning(&state, 0, 4, 90);

    update_unwrap(&mut state, 80, RepetitionResult::Normal, &configuration);
    assert_reviewing(&state, 2.5, 80, 680);

    update_unwrap(&mut state, 380, RepetitionResult::Normal, &configuration);
    assert_reviewing(&state, 2.5, 380, 1430);

    update_unwrap(&mut state, 1000, RepetitionResult::Normal, &configuration);
    assert_reviewing(&state, 2.5, 1000, 2980);

    update_unwrap(&mut state, 1990, RepetitionResult::Easy, &configuration);
    assert_reviewing(&state, 2.5 * 1.075, 1990, 7465);

    update_unwrap(&mut state, 5000, RepetitionResult::Again, &configuration);
    assert_reviewing(&state, 2.5 * 1.075 / 1.2, 5000, 5537);

    update_unwrap(&mut state, 5500, RepetitionResult::Hard, &configuration);
    assert_reviewing(&state, 2.5 * 1.075 / 1.2 / 1.15, 5500, 6100);
}
