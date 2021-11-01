use rustc_middle::mir::{BasicBlock, Local};

const BB_LABEL: &str = "bb";
const RET_VAR: &str = "ret";
const MIR_TEMP_PREFIX: &str = "mirtemp___";
const GIL_TEMP_PREFIX: &str = "giltemp___";
const GIL_UNUSED_VAR: &str = "gil____THROAWAY";
const UNDERSCORED_PREFIX: &str = "underscored___";

pub fn bb_label(bb: &BasicBlock) -> String {
    format!("{}{}", BB_LABEL, bb.as_u32())
}

pub fn ret_var() -> String {
    String::from(RET_VAR)
}

pub fn temp_name_from_local(local: &Local) -> String {
    format!("{}{}", MIR_TEMP_PREFIX, local.as_u32())
}

pub fn gil_temp_from_id(id: u32) -> String {
    format!("{}{}", GIL_TEMP_PREFIX, id)
}

pub fn unused_var() -> String {
    String::from(GIL_UNUSED_VAR)
}

pub fn sanitize_name(name: String) -> String {
    if name.chars().next().unwrap() == '_' {
        UNDERSCORED_PREFIX.to_string() + &name
    } else {
        name
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bb_label_test() {
        let bb = BasicBlock::from(0u32);
        assert_eq!(bb_label(&bb), String::from("bb0"));
        let bb = BasicBlock::from(100u32);
        assert_eq!(bb_label(&bb), String::from("bb100"));
    }
}
