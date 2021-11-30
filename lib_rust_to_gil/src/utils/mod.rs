mod cgu_reuse;
mod log;

pub fn init() {
    log::init();
}

pub use cgu_reuse::{determine_cgu_reuse, reuse_workproduct_for_cgu};
pub mod fatal;
