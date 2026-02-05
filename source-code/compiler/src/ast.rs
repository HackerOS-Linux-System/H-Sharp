use serde::Deserialize;

#[derive(Debug, Deserialize)]
pub struct Program {
    pub declarations: Vec<Declaration>,
    pub main_body: Vec<Statement>,
}

#[derive(Debug, Deserialize)]
#[serde(tag = "node")]
pub enum Declaration {
    Function {
        name: String,
        params: Vec<Param>,
        #[serde(default)]
        return_type: String,
        body: Vec<Statement>,
    },
    Object {
        name: String,
        #[serde(default)]
        kind: String,
        #[serde(default)]
        members: Vec<Member>,
        #[serde(default)]
        variants: Vec<Variant>
    },
}

#[derive(Debug, Deserialize)]
pub struct Param {
    pub name: String,
    #[serde(rename = "type")]
    pub type_name: String,
}

#[derive(Debug, Deserialize)]
pub struct Member {
    pub name: String,
    #[serde(rename = "type")]
    pub type_name: String,
}

#[derive(Debug, Deserialize)]
pub struct Variant {
    pub tag: String,
    pub types: Vec<String>,
}

#[derive(Debug, Deserialize)]
#[serde(tag = "node")]
pub enum Statement {
    Log { format: String, args: Vec<String> },
    System { command: String, #[serde(default)] args: Vec<String> },
    Let { name: String, value: Expr },
    Call { target: String, args: Vec<Expr> },
    Return { value: Expr },
    If { condition: Expr, then: Vec<Statement>, #[serde(default)] r#else: Vec<Statement> },
    ArraySet { target: String, index: Expr, value: Expr },
}

#[derive(Debug, Deserialize)]
#[serde(tag = "node")]
pub enum Expr {
    Literal { #[serde(rename = "type")] type_name: String, value: serde_json::Value },
    Var { name: String },
    Call { target: String, args: Vec<Expr> },
    BinaryOp { op: String, left: Box<Expr>, right: Box<Expr> },
    ArrayGet { target: String, index: Box<Expr> },
}
