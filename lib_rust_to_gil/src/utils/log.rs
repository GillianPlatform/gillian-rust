pub fn init() {
    env_logger::init_from_env(env_logger::Env::default().filter_or("RUST_LOG", "debug"))
}
