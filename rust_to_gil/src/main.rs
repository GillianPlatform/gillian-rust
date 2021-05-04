#![feature(rustc_private)]
#![deny(rustc::internal)]
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_interface;
extern crate rustc_lint;
extern crate rustc_middle;
extern crate rustc_hir;
extern crate log;



use lib_rtg::config::{Config as RtgConfig, ExecMode};
use simple_logger::SimpleLogger;

use rustc_interface::interface::Compiler;
use rustc_interface::Queries;
use rustc_driver::Compilation;
use rustc_hir::def_id::LOCAL_CRATE;

#[derive(Debug)]
struct RTGCompilerCalls {
    gil_config: RtgConfig,
}

impl rustc_driver::Callbacks for RTGCompilerCalls {
    fn after_analysis<'tcx>(&mut self, compiler: &Compiler, queries: &'tcx Queries<'tcx>) -> Compilation {
        compiler.session().abort_if_errors();
        
        log::debug!("{:?}", self);
        
        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            let key = tcx.mir_keys(LOCAL_CRATE).iter().next().unwrap();
            log::debug!("{:?}", key);
            let mir_main = tcx.mir_built(rustc_middle::ty::WithOptConstParam::unknown(*key));
            log::debug!("{:?}", mir_main);
            
        });
        
        compiler.session().abort_if_errors();
        
        Compilation::Stop
    }
}

impl Default for RTGCompilerCalls {
    fn default() -> Self {
        Self {
            gil_config: RtgConfig {
                mode: ExecMode::Concrete
            }
        }
    }
}



fn main() {
    rustc_driver::install_ice_hook();
    SimpleLogger::new().init().unwrap();
    
    
    let args: Vec<_> = std::env::args().collect();
    let mut my_cb = RTGCompilerCalls::default();
    
    
    
    match rustc_driver::RunCompiler::new(&args, &mut my_cb).run() {
        Ok(_) => log::debug!("correct !"),
        Err(_) => log::debug!("incorrect !")
    };
}
