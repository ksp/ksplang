use std::{cmp, str::FromStr, sync::LazyLock};


#[derive(Debug, Clone, PartialEq)]
pub struct JitConfig {
    pub verbosity: u8,
    pub soften_limits: bool,
    pub start_interpret_limit: u32,
    pub start_instr_limit: u32,
    pub start_branch_limit: u32,
    pub adhoc_interpret_limit: u32,
    pub adhoc_branch_limit: u32,
    pub adhoc_instr_limit: u32,
    pub callcache_interpret_limit: u32,
    pub callcache_branch_limit: u32,
    pub callcache_instr_limit: u32,

    pub allow_pruning: bool,
    pub allow_uphoisting: bool,
    pub verify: u8, // 0 = off, 1 = first run, 2 = full
    pub error_as_deopt: bool,
    pub allow_osmibyte_backend: bool,
    pub trace_limit: u32,
    pub trace_trigger_count: u32,
    pub min_gain_const: u32,
    pub min_gain_mul: u32,

    pub shrinker_final_verbosity: u8,
}

impl JitConfig {
    #[inline]
    pub fn verbosity(&self) -> u8 {
        if cfg!(debug_assertions) {
            self.verbosity
        } else {
            cmp::min(16, self.verbosity)
        }
    }

    #[inline]
    pub fn should_log(&self, level: u8) -> bool {
        self.verbosity() >= level
    }
}
fn parse_env_opt<T>(key: &str) -> Option<T>
where
    T: FromStr + 'static, <T as FromStr>::Err: std::fmt::Display
{
    if let Ok(mut val) = std::env::var(key) {
        if std::any::TypeId::of::<T>() == std::any::TypeId::of::<bool>() {
            val = val.to_lowercase();
            if val == "1" || val == "yes" {
                val = "true".to_string();
            } else if val == "0" || val == "no" {
                val = "false".to_string();
            }
        }
        match val.parse::<T>() {
            Ok(v) => Some(v),
            Err(err) => if val == "" {
                None
            } else {
                panic!("Failed to parse env var {key} with value {val}: {err}");
            }
        }
    } else {
        None
    }
}

fn parse_env<T>(key: &str, default: T) -> T
where
    T: FromStr + 'static, <T as FromStr>::Err: std::fmt::Display
{
    parse_env_opt(key).unwrap_or(default)
}

fn create_config() -> JitConfig {
    let verbosity = parse_env("KSPLANGJIT_VERBOSITY", if cfg!(debug_assertions) { 10 } else { 1 });
    let c = JitConfig {
        verbosity,
        soften_limits: parse_env("KSPLANGJIT_SOFTEN_LIMITS", true),
        start_interpret_limit: parse_env("KSPLANGJIT_START_LIMIT", 50_000),
        start_branch_limit: parse_env("KSPLANGJIT_START_BRANCH_LIMIT", 1024),
        start_instr_limit: parse_env("KSPLANGJIT_START_INSTR_LIMIT", 3000),
        adhoc_interpret_limit: parse_env("KSPLANGJIT_ADHOC_INTERPRET_LIMIT", 5_000),
        adhoc_branch_limit: parse_env("KSPLANGJIT_ADHOC_BRANCH_LIMIT", 64),
        adhoc_instr_limit: parse_env("KSPLANGJIT_ADHOC_INSTR_LIMIT", 600),
        callcache_interpret_limit: parse_env("KSPLANGJIT_CALLCACHE_INTERPRET_LIMIT", 20_000),
        callcache_branch_limit: parse_env("KSPLANGJIT_CALLCACHE_BRANCH_LIMIT", 70),
        callcache_instr_limit: parse_env("KSPLANGJIT_CALLCACHE_INSTR_LIMIT", 200),

        allow_pruning: parse_env("KSPLANGJIT_PRUNING", true),
        allow_uphoisting: parse_env("KSPLANGJIT_ALLOW_UPHOISTING", true),
        error_as_deopt: parse_env("KSPLANGJIT_ERROR_AS_DEOPT", true),
        allow_osmibyte_backend: parse_env("KSPLANGJIT_ALLOW_OSMIBYTE_BACKEND", true),
        verify: parse_env("KSPLANGJIT_VERIFY", 1),
        trace_limit: parse_env("KSPLANGJIT_TRACE_LIMIT", 1000),
        trace_trigger_count: parse_env("KSPLANGJIT_TRIGGER_COUNT", 3),
        min_gain_const: parse_env("KSPLANGJIT_MIN_GAIN_CONST", 5),
        min_gain_mul: parse_env("KSPLANGJIT_MIN_GAIN_MUL", 2),

        shrinker_final_verbosity: parse_env("KSPLANGJIT_SHRINKER_FINAL_VERBOSITY", verbosity)
    };

    #[cfg(not(debug_assertions))] {
        if c.verbosity > 16 {
            panic!("Verbosity level above 16 is only available in debug builds: {}", c.verbosity);
        }
    }

    c

}

static CELL: LazyLock<JitConfig> = LazyLock::new(|| create_config());

pub fn get_config() -> &'static JitConfig {
    &CELL
}
