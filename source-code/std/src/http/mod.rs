//! H# HTTP client (no external deps)
use std::io::{Read,Write};
pub struct Response{pub status:u16,pub body:String}
impl Response{pub fn ok(&self)->bool{self.status>=200&&self.status<300}}
pub fn get(url:&str)->Result<Response,String>{
    let(host,path)=parse_url(url);
    let addr=format!("{}:80",host).parse::<std::net::SocketAddr>().map_err(|e|e.to_string())?;
    let mut s=std::net::TcpStream::connect_timeout(&addr,std::time::Duration::from_secs(10)).map_err(|e|e.to_string())?;
    write!(s,"GET {} HTTP/1.0\r\nHost: {}\r\nUser-Agent: H#/0.1\r\nConnection: close\r\n\r\n",path,host).map_err(|e|e.to_string())?;
    s.set_read_timeout(Some(std::time::Duration::from_secs(15))).ok();
    let mut r=String::new(); s.read_to_string(&mut r).map_err(|e|e.to_string())?;
    let(_, body)=r.split_once("\r\n\r\n").unwrap_or(("",&r));
    let status:u16=r.lines().next().and_then(|l|l.split_whitespace().nth(1)).and_then(|s|s.parse().ok()).unwrap_or(0);
    Ok(Response{status,body:body.to_string()})
}
fn parse_url(url:&str)->(String,String){
    let u=url.trim_start_matches("http://").trim_start_matches("https://");
    if let Some(i)=u.find('/'){(u[..i].to_string(),u[i..].to_string())}else{(u.to_string(),"/".to_string())}
}
fn parse_url_res(url:&str)->Result<(String,String),String>{Ok(parse_url(url))}
