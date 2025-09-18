use ark_serialize::*;
use std::os::unix;
use std::time::{SystemTime, UNIX_EPOCH};
use tokio::time::{Duration, Instant};
use tokio_stream::wrappers::IntervalStream;
use tokio_stream::{Stream, StreamExt};

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct Epoch(u64);

/// Round a tokio Instant up to the next multiple of `step` since midnight wall-clock time.
fn round_up_to_multiple(t: Instant, step: Duration) -> Instant {
    // Get wall-clock "now" and its monotonic Instant counterpart
    let sys_now = SystemTime::now();
    let inst_now = Instant::now();

    // Work out today's midnight in SystemTime
    let since_epoch = sys_now.duration_since(UNIX_EPOCH).unwrap();
    let midnight_epoch = since_epoch - Duration::from_secs(since_epoch.as_secs() % 86_400);

    // Convert that midnight into an Instant anchor
    let midnight_instant = inst_now - (since_epoch - midnight_epoch);

    // Now do the rounding relative to that anchor
    let elapsed = t.duration_since(midnight_instant);

    let n = (elapsed.as_nanos() + step.as_nanos() - 1) / step.as_nanos();
    midnight_instant + Duration::from_nanos((n * step.as_nanos()) as u64)
}

impl Epoch {
    const DURATION: Duration = Duration::from_secs(60 * 10);

    pub fn to_bytes(&self) -> [u8; 8] {
        self.0.to_le_bytes()
    }

    pub fn stream() -> impl Stream<Item = Epoch> {
        let now = Instant::now();
        let next_start: Instant = round_up_to_multiple(Instant::now(), Self::DURATION);

        let start = if next_start - now < Duration::from_secs(30) {
            // wait til next time
            next_start + Self::DURATION
        } else {
            next_start
        };

        let interval = tokio::time::interval_at(start, Self::DURATION);

        let unix_epoch = {
            let sys_now = SystemTime::now();
            let since_epoch = sys_now.duration_since(UNIX_EPOCH).unwrap();
            now - since_epoch
        };

        IntervalStream::new(interval).map(move |tick_instant| {
            let elapsed = tick_instant
                .checked_duration_since(unix_epoch)
                .unwrap_or_else(|| Duration::from_nanos(0));

            // Integer division in nanoseconds to avoid float rounding.
            let n = elapsed.as_nanos() / Self::DURATION.as_nanos();
            Epoch(n as u64)
        })
    }
}
