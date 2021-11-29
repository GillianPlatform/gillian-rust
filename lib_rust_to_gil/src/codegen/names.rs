use rustc_middle::mir::{BasicBlock, Local};

const BB_LABEL: &str = "bb";
const RET_VAR: &str = "ret";
const MIR_TEMP_PREFIX: &str = "mirtemp___";
const GIL_TEMP_PREFIX: &str = "giltemp___";
const GIL_UNUSED_VAR: &str = "gil____THROAWAY";
const UNDERSCORED_PREFIX: &str = "underscored___";
const GLOBAL_ENV_DECL: &str = "i__global_env";

pub fn bb_label(bb: &BasicBlock) -> String {
    format!("{}{}", BB_LABEL, bb.as_usize())
}

pub fn ret_var() -> String {
    String::from(RET_VAR)
}

pub fn temp_name_from_local(local: &Local) -> String {
    format!("{}{}", MIR_TEMP_PREFIX, local.as_usize())
}

pub fn gil_temp_from_id(id: usize) -> String {
    format!("{}{}", GIL_TEMP_PREFIX, id)
}

pub fn unused_var() -> String {
    String::from(GIL_UNUSED_VAR)
}

pub fn sanitize_name(name: String) -> String {
    if name.starts_with('_') {
        UNDERSCORED_PREFIX.to_string() + &name
    } else {
        name
    }
}

pub fn global_env_proc() -> String {
    String::from(GLOBAL_ENV_DECL)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bb_label_test() {
        let bb = BasicBlock::from(0usize);
        assert_eq!(bb_label(&bb), String::from("bb0"));
        let bb = BasicBlock::from(100usize);
        assert_eq!(bb_label(&bb), String::from("bb100"));
    }
}
