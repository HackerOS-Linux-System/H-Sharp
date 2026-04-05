//! H# Math
pub const PI:f64=std::f64::consts::PI;
pub const E:f64=std::f64::consts::E;
pub fn abs(x:f64)->f64{x.abs()} pub fn sqrt(x:f64)->f64{x.sqrt()} pub fn pow(b:f64,e:f64)->f64{b.powf(e)}
pub fn floor(x:f64)->f64{x.floor()} pub fn ceil(x:f64)->f64{x.ceil()} pub fn round(x:f64)->f64{x.round()}
pub fn sin(x:f64)->f64{x.sin()} pub fn cos(x:f64)->f64{x.cos()} pub fn tan(x:f64)->f64{x.tan()}
pub fn log(x:f64)->f64{x.ln()} pub fn log10(x:f64)->f64{x.log10()}
pub fn min_f(a:f64,b:f64)->f64{a.min(b)} pub fn max_f(a:f64,b:f64)->f64{a.max(b)}
pub fn clamp(v:f64,lo:f64,hi:f64)->f64{v.clamp(lo,hi)}
