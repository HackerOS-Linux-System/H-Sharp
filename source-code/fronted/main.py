import sys
import json
import re
import argparse
from sly import Lexer, Parser

# --- Lexer ---
class HSharpLexer(Lexer):
    tokens = {
        FUNC, OBJECT, LOG, IMPORT, MEMORY_MODE, LINKAGE_MODE,
        IF, ELSE, LET, RETURN, NULL,
        ID, STRING, NUMBER,
        EQEQ, NEQ, GEQ, LEQ, GT, LT,
        EQ, COMMA, COLON, LBRACKET, RBRACKET, PIPE, LPAREN, RPAREN,
        PLUS, MINUS
    }
    ignore = ' \t'
    
    @_(r'\n+')
    def ignore_newline(self, t):
        self.lineno += len(t.value)

    ignore_comment = r'![^\n]*'

    # Keywords
    FUNC = r'func'
    OBJECT = r'object'
    LOG = r'log'
    IF = r'if'
    ELSE = r'else'
    LET = r'let'
    RETURN = r'return'
    NULL = r'NULL'

    # Special
    IMPORT = r'\#'
    MEMORY_MODE = r'---'
    LINKAGE_MODE = r'==='
    PIPE = r'\|'

    # Operators
    EQEQ = r'=='
    NEQ = r'!='
    GEQ = r'>='
    LEQ = r'<='
    GT = r'>'
    LT = r'<'
    EQ = r'='
    PLUS = r'\+'
    MINUS = r'-'

    ID = r'[a-zA-Z_][a-zA-Z0-9_]*'
    STRING = r'"[^"]*"'
    NUMBER = r'\d+'

    LBRACKET = r'\['
    RBRACKET = r'\]'
    LPAREN = r'\('
    RPAREN = r'\)'
    COMMA = r','
    COLON = r':'

    @_(r'!!')
    def MULTI_COMMENT_START(self, t):
        self.begin(MultiCommentLexer)

class MultiCommentLexer(Lexer):
    tokens = {}
    ignore = r'.*?'
    @_(r'!!')
    def MULTI_COMMENT_END(self, t):
        self.begin(HSharpLexer)

# --- Parser ---
class HSharpParser(Parser):
    tokens = HSharpLexer.tokens
    
    # Precedence rules to resolve Shift/Reduce conflicts
    precedence = (
        ('right', ELSE),           # Bind ELSE to the nearest IF
        ('left', EQEQ, NEQ, GT, LT, GEQ, LEQ),
        ('left', PLUS, MINUS),
    )

    def __init__(self):
        self.ast = {
            "node": "Program",
            "config": {"memory": "auto", "linkage": "auto"},
            "imports": [],
            "declarations": [],
            "main_body": [] 
        }

    @_('statements')
    def program(self, p):
        for stmt in p.statements:
            if stmt: 
                self.ast["main_body"].append(stmt)
        return self.ast

    @_('statement statements')
    def statements(self, p):
        return [p.statement] + p.statements

    @_('empty')
    def statements(self, p):
        return []

    @_('')
    def empty(self, p):
        return None

    # --- Statements ---

    @_('import_stmt', 'memory_mode_stmt', 'linkage_mode_stmt')
    def statement(self, p):
        return None 

    @_('func_def', 'object_def')
    def statement(self, p):
        return None 

    @_('log_stmt', 'system_exec_stmt', 'if_stmt', 'let_stmt', 'return_stmt', 'call_stmt', 'assign_stmt')
    def statement(self, p):
        return p[0]

    # --- Configurations ---

    @_('IMPORT LT ID COLON ID GT')
    def import_stmt(self, p):
        self.ast["imports"].append({"source": p.ID0, "lib": p.ID1})

    @_('MEMORY_MODE ID MEMORY_MODE')
    def memory_mode_stmt(self, p):
        self.ast["config"]["memory"] = p.ID.lower()

    @_('LINKAGE_MODE ID LINKAGE_MODE')
    def linkage_mode_stmt(self, p):
        self.ast["config"]["linkage"] = p.ID.lower()

    # --- Core Logic ---

    @_('LOG STRING')
    def log_stmt(self, p):
        text = p.STRING[1:-1]
        parts = []
        args = []
        last = 0
        for match in re.finditer(r'\{([a-zA-Z_][a-zA-Z0-9_]*)\}', text):
            parts.append(text[last:match.start()])
            args.append(match.group(1))
            parts.append("%s") 
            last = match.end()
        parts.append(text[last:])
        
        return {
            "node": "Log",
            "format": "".join(parts),
            "args": args
        }

    @_('GT STRING')
    def system_exec_stmt(self, p):
        cmd = p.STRING[1:-1]
        parts = []
        args = []
        last = 0
        for match in re.finditer(r'\{([a-zA-Z_][a-zA-Z0-9_]*)\}', cmd):
            parts.append(cmd[last:match.start()])
            args.append(match.group(1))
            parts.append("%s")
            last = match.end()
        parts.append(cmd[last:])

        if not args:
            return {"node": "System", "command": cmd, "args": []}
        else:
            return {"node": "System", "command": "".join(parts), "args": args}

    @_('FUNC ID params COLON type EQ LBRACKET statements RBRACKET')
    def func_def(self, p):
        func_node = {
            "node": "Function",
            "name": p.ID,
            "params": p.params,
            "return_type": self.map_type(p.type),
            "body": [s for s in p.statements if s]
        }
        self.ast["declarations"].append(func_node)

    @_('LPAREN paramlist RPAREN')
    def params(self, p):
        return p.paramlist

    @_('param COMMA paramlist')
    def paramlist(self, p):
        return [p.param] + p.paramlist

    @_('param')
    def paramlist(self, p):
        return [p.param]

    @_('empty')
    def paramlist(self, p):
        return []

    @_('ID COLON type')
    def param(self, p):
        return {"name": p.ID, "type": self.map_type(p.type)}

    # --- Objects ---
    
    @_('OBJECT ID EQ variants')
    def object_def(self, p):
        self.ast["declarations"].append({
            "node": "Object",
            "kind": "enum",
            "name": p.ID,
            "variants": p.variants
        })

    @_('OBJECT ID LBRACKET members RBRACKET')
    def object_def(self, p):
        self.ast["declarations"].append({
            "node": "Object",
            "kind": "struct",
            "name": p.ID,
            "members": p.members
        })

    @_('member members')
    def members(self, p):
        return [p.member] + p.members

    @_('empty')
    def members(self, p):
        return []

    # Removed SEMICOLON token requirement
    @_('ID COLON type')
    def member(self, p):
        return {"name": p.ID, "type": self.map_type(p.type)}

    @_('PIPE variant variants')
    def variants(self, p):
        return [p.variant] + p.variants

    @_('PIPE variant')
    def variants(self, p):
        return [p.variant]

    @_('ID LPAREN typelist RPAREN')
    def variant(self, p):
        return {"tag": p.ID, "types": p.typelist}

    @_('ID')
    def variant(self, p):
        return {"tag": p.ID, "types": []}

    @_('type COMMA typelist')
    def typelist(self, p):
        return [self.map_type(p.type)] + p.typelist

    @_('type')
    def typelist(self, p):
        return [self.map_type(p.type)]

    @_('empty')
    def typelist(self, p):
        return []

    # --- Control Flow ---

    @_('IF expr LBRACKET statements RBRACKET')
    def if_stmt(self, p):
         return {
            "node": "If",
            "condition": p.expr,
            "then": [s for s in p.statements if s],
            "else": []
        }

    @_('IF expr LBRACKET statements RBRACKET ELSE LBRACKET statements RBRACKET')
    def if_stmt(self, p):
        return {
            "node": "If",
            "condition": p.expr,
            "then": [s for s in p.statements0 if s],
            "else": [s for s in p.statements1 if s]
        }

    @_('IF expr LBRACKET statements RBRACKET ELSE if_stmt')
    def if_stmt(self, p):
        return {
            "node": "If",
            "condition": p.expr,
            "then": [s for s in p.statements if s],
            "else": [p.if_stmt]
        }

    @_('LET ID EQ expr')
    def let_stmt(self, p):
        return {
            "node": "Let",
            "name": p.ID,
            "value": p.expr
        }

    @_('ID LBRACKET expr RBRACKET EQ expr')
    def assign_stmt(self, p):
        return {
            "node": "ArraySet",
            "target": p.ID,
            "index": p.expr0,
            "value": p.expr1
        }
        
    @_('RETURN expr')
    def return_stmt(self, p):
        return {
            "node": "Return",
            "value": p.expr
        }

    @_('ID LPAREN args RPAREN')
    def call_stmt(self, p):
        return {
            "node": "Call",
            "target": p.ID,
            "args": p.args
        }

    # --- Expressions ---

    @_('expr EQEQ expr', 'expr NEQ expr', 'expr GT expr', 'expr LT expr', 'expr GEQ expr', 'expr LEQ expr', 
       'expr PLUS expr', 'expr MINUS expr')
    def expr(self, p):
        return {"node": "BinaryOp", "op": p[1], "left": p.expr0, "right": p.expr1}

    @_('ID LPAREN args RPAREN')
    def expr(self, p):
        return {"node": "Call", "target": p.ID, "args": p.args}

    @_('ID LBRACKET expr RBRACKET')
    def expr(self, p):
        return {"node": "ArrayGet", "target": p.ID, "index": p.expr}

    @_('STRING')
    def expr(self, p):
        return {"node": "Literal", "type": "str", "value": p.STRING[1:-1]}

    @_('NUMBER')
    def expr(self, p):
        return {"node": "Literal", "type": "i32", "value": int(p.NUMBER)}

    @_('ID')
    def expr(self, p):
        return {"node": "Var", "name": p.ID}

    @_('NULL')
    def expr(self, p):
        return {"node": "Literal", "type": "ptr", "value": 0}

    @_('expr COMMA args')
    def args(self, p):
        return [p.expr] + p.args

    @_('expr')
    def args(self, p):
        return [p.expr]

    @_('empty')
    def args(self, p):
        return []

    # --- Helpers ---

    @_('type LBRACKET RBRACKET')
    def type(self, p):
        return self.map_type(p.type) + "[]"

    @_('ID')
    def type(self, p):
        return p.ID

    def map_type(self, t):
        mapping = {'i32': 'i32', 'str': 'str', 'void': 'void'}
        return mapping.get(t, t)

    def error(self, p):
        if p:
            raise ValueError(f"Syntax error at '{p.value}' (line {p.lineno})")
        else:
            raise ValueError("EOF error")

if __name__ == '__main__':
    parser_arg = argparse.ArgumentParser(description="H-Sharp Frontend Compiler")
    parser_arg.add_argument("input", help="Input .hla file")
    parser_arg.add_argument("-o", "--output", help="Output .json file", default="program.json")
    args = parser_arg.parse_args()

    lexer = HSharpLexer()
    parser = HSharpParser()
    
    try:
        with open(args.input, 'r') as f:
            code = f.read()
    except FileNotFoundError:
        sys.stderr.write(f"Error: File '{args.input}' not found.\n")
        sys.exit(1)

    try:
        ast = parser.parse(lexer.tokenize(code))
        with open(args.output, 'w') as f:
            json.dump(ast, f, indent=2)
        # Keep silent for JSON output to pipe correctly if needed, or just standard logging
    except Exception as e:
        sys.stderr.write(f"Parse Error: {e}\n")
        sys.exit(1)
