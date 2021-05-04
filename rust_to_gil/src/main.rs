#![feature(rustc_private)]
#![deny(rustc::internal)]
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_interface;
extern crate rustc_lint;
extern crate rustc_middle;
extern crate log;


use lib_rtg::config::{Config as RtgConfig, ExecMode};
use simple_logger::SimpleLogger;

use rustc_interface::interface::Compiler;
use rustc_interface::Queries;
use rustc_driver::Compilation;

struct RTGCompilerCalls {
    gil_config: RtgConfig,
}

impl rustc_driver::Callbacks for RTGCompilerCalls {
    fn after_analysis<'tcx>(&mut self, compiler: &Compiler, _queries: &'tcx Queries<'tcx>) -> Compilation {
        compiler.session().abort_if_errors();
        
        if let ExecMode::Concrete = self.gil_config.mode {
            println!("bite")
        }
        
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
    log::debug!("bite");
    
    
    let args: Vec<_> = std::env::args().collect();
    let mut my_cb = RTGCompilerCalls::default();
    
    
    
    match rustc_driver::RunCompiler::new(&args, &mut my_cb).run() {
        Ok(_) => log::debug!("correct !"),
        Err(_) => log::debug!("incorrect !")
    };
}
