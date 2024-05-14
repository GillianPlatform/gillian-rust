use crate::prelude::*;

pub(crate) mod action_names {
    pub(crate) const NEW_LFT: &str = "new_lft";
    pub(crate) const KILL_LFT: &str = "kill_lft";
}

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    pub fn push_create_lifetime(&mut self, lft_name: String) {
        let temp = self.temp_var();
        self.push_cmd(Cmd::Action {
            variable: temp.clone(),
            action_name: action_names::NEW_LFT.to_string(),
            parameters: vec![],
        });
        self.push_cmd(Cmd::Assignment {
            variable: lft_name,
            assigned_expr: Expr::lnth(Expr::PVar(temp), 0),
        })
    }

    #[allow(dead_code)]
    pub fn push_kill_lifetime(&mut self, lft_name: String) {
        self.push_cmd(Cmd::Action {
            variable: names::unused_var(),
            action_name: action_names::KILL_LFT.to_string(),
            parameters: vec![Expr::PVar(lft_name)],
        });
    }
}
