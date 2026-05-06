//! Compiler for `mini`, the very-simple DSL on top of the zkvm asm.
//!
//! Each statement compiles to one or a few asm lines. No nested expressions:
//! every assignment has at most one operator on the right-hand side.
//!
//! Statements (one per line, semicolon-terminated):
//!   let x = 0;            - constant assignment
//!   let x = y;            - copy
//!   let x = read();
//!   x = y + z;
//!   x = y - z;
//!   x = y * z;
//!   x = mem[y];
//!   mem[y] = x;
//!   write(x);
//!   if x == 0 { ... }     - optional `else { ... }`
//!   while x != 0 { ... }
//!   halt;
//!
//! Output is asm text; pipe through `crate::asm::assemble`.

use std::collections::HashMap;

pub fn compile(src: &str) -> Result<String, String> {
    let mut p = Parser::new(src)?;
    let mut ctx = Ctx::new();
    while !p.is_eof() {
        compile_stmt(&mut p, &mut ctx)?;
    }
    Ok(ctx.asm)
}

struct Ctx {
    asm: String,
    vars: HashMap<String, u32>, // name -> register (1..=7)
    next_reg: u32,              // next free register, starts at 1
    next_label: u32,
}

impl Ctx {
    fn new() -> Self {
        Self { asm: String::new(), vars: HashMap::new(), next_reg: 1, next_label: 0 }
    }
}

impl Ctx {
    fn alloc_reg(&mut self, name: &str) -> Result<u32, String> {
        if let Some(&r) = self.vars.get(name) { return Ok(r); }
        if self.next_reg > 7 {
            return Err(format!("too many variables (max 7); '{}' would be the 8th", name));
        }
        let r = self.next_reg;
        self.next_reg += 1;
        self.vars.insert(name.to_string(), r);
        Ok(r)
    }
    fn lookup(&self, name: &str) -> Result<u32, String> {
        self.vars.get(name).copied().ok_or_else(|| format!("undefined variable '{}'", name))
    }
    fn fresh_label(&mut self, prefix: &str) -> String {
        let l = format!("_{}{}", prefix, self.next_label);
        self.next_label += 1;
        l
    }
}

// ── tokenizer / parser (just enough) ──────────────────────────────────

struct Parser {
    toks: Vec<Tok>,
    pos: usize,
}

#[derive(Debug, Clone, PartialEq)]
enum Tok {
    Word(String),
    Num(u64),
    Punct(char),
    EqEq,
    NotEq,
}

impl Parser {
    fn new(src: &str) -> Result<Self, String> {
        let mut toks = Vec::new();
        let mut chars = src.chars().peekable();
        while let Some(&c) = chars.peek() {
            if c.is_whitespace() { chars.next(); continue; }
            if c == '/' {
                let mut tmp = chars.clone();
                tmp.next();
                if tmp.peek() == Some(&'/') {
                    while let Some(&cc) = chars.peek() {
                        chars.next();
                        if cc == '\n' { break; }
                    }
                    continue;
                }
            }
            if c.is_ascii_alphabetic() || c == '_' {
                let mut s = String::new();
                while let Some(&cc) = chars.peek() {
                    if cc.is_ascii_alphanumeric() || cc == '_' {
                        s.push(cc); chars.next();
                    } else { break; }
                }
                toks.push(Tok::Word(s));
            } else if c.is_ascii_digit() {
                let mut s = String::new();
                while let Some(&cc) = chars.peek() {
                    if cc.is_ascii_digit() { s.push(cc); chars.next(); }
                    else { break; }
                }
                let n: u64 = s.parse().map_err(|_| format!("bad number '{}'", s))?;
                toks.push(Tok::Num(n));
            } else if c == '=' {
                chars.next();
                if chars.peek() == Some(&'=') {
                    chars.next();
                    toks.push(Tok::EqEq);
                } else {
                    toks.push(Tok::Punct('='));
                }
            } else if c == '!' {
                chars.next();
                if chars.peek() == Some(&'=') {
                    chars.next();
                    toks.push(Tok::NotEq);
                } else {
                    return Err("expected '=' after '!'".to_string());
                }
            } else if "+-*;,(){}[]".contains(c) {
                toks.push(Tok::Punct(c));
                chars.next();
            } else {
                return Err(format!("unexpected character '{}'", c));
            }
        }
        Ok(Self { toks, pos: 0 })
    }

    fn is_eof(&self) -> bool { self.pos >= self.toks.len() }
    fn peek(&self) -> Option<&Tok> { self.toks.get(self.pos) }
    fn bump(&mut self) -> Option<Tok> {
        let t = self.toks.get(self.pos).cloned();
        if t.is_some() { self.pos += 1; }
        t
    }
    fn expect_punct(&mut self, c: char) -> Result<(), String> {
        match self.bump() {
            Some(Tok::Punct(p)) if p == c => Ok(()),
            other => Err(format!("expected '{}', got {:?}", c, other)),
        }
    }
    fn eat_word(&mut self, w: &str) -> bool {
        if let Some(Tok::Word(s)) = self.peek() {
            if s == w { self.pos += 1; return true; }
        }
        false
    }
    fn eat_punct(&mut self, c: char) -> bool {
        if let Some(Tok::Punct(p)) = self.peek() {
            if *p == c { self.pos += 1; return true; }
        }
        false
    }
    fn parse_word(&mut self) -> Result<String, String> {
        match self.bump() {
            Some(Tok::Word(s)) => Ok(s),
            other => Err(format!("expected identifier, got {:?}", other)),
        }
    }
}

// ── statement compilation ─────────────────────────────────────────────

fn compile_stmt(p: &mut Parser, ctx: &mut Ctx) -> Result<(), String> {
    match p.peek() {
        Some(Tok::Word(w)) if w == "let" => { p.bump(); compile_let(p, ctx) }
        Some(Tok::Word(w)) if w == "write" => { p.bump(); compile_write(p, ctx) }
        Some(Tok::Word(w)) if w == "if" => { p.bump(); compile_if(p, ctx) }
        Some(Tok::Word(w)) if w == "while" => { p.bump(); compile_while(p, ctx) }
        Some(Tok::Word(w)) if w == "halt" => { p.bump(); p.expect_punct(';')?; ctx.asm.push_str("    HALT\n"); Ok(()) }
        Some(Tok::Word(w)) if w == "mem" => { p.bump(); compile_mem_store(p, ctx) }
        Some(Tok::Word(_)) => compile_assign(p, ctx),
        other => Err(format!("unexpected start of statement: {:?}", other)),
    }
}

fn compile_let(p: &mut Parser, ctx: &mut Ctx) -> Result<(), String> {
    let name = p.parse_word()?;
    p.expect_punct('=')?;
    let r = ctx.alloc_reg(&name)?;

    // Three forms: read(), constant number, identifier (copy).
    if p.eat_word("read") {
        p.expect_punct('(')?;
        p.expect_punct(')')?;
        p.expect_punct(';')?;
        ctx.asm.push_str(&format!("    READ r{}\n", r));
        return Ok(());
    }
    match p.bump() {
        Some(Tok::Num(n)) => {
            p.expect_punct(';')?;
            ctx.asm.push_str(&format!("    IMM r{}, {}\n", r, n));
        }
        Some(Tok::Word(src)) => {
            let rs = ctx.lookup(&src)?;
            // Two forms: copy (`let x = y;`) or op (`let x = y + z;`).
            if p.eat_punct(';') {
                ctx.asm.push_str(&format!("    MOV r{}, r{}\n", r, rs));
            } else {
                let op = match p.bump() {
                    Some(Tok::Punct('+')) => "ADD",
                    Some(Tok::Punct('-')) => "SUB",
                    Some(Tok::Punct('*')) => "MUL",
                    other => return Err(format!("expected ';', '+', '-' or '*', got {:?}", other)),
                };
                let z = p.parse_word()?;
                let rz = ctx.lookup(&z)?;
                p.expect_punct(';')?;
                ctx.asm.push_str(&format!("    {} r{}, r{}, r{}\n", op, r, rs, rz));
            }
        }
        other => return Err(format!("bad rhs after 'let': {:?}", other)),
    }
    Ok(())
}

fn compile_write(p: &mut Parser, ctx: &mut Ctx) -> Result<(), String> {
    p.expect_punct('(')?;
    let name = p.parse_word()?;
    let r = ctx.lookup(&name)?;
    p.expect_punct(')')?;
    p.expect_punct(';')?;
    ctx.asm.push_str(&format!("    WRITE r{}\n", r));
    Ok(())
}

fn compile_assign(p: &mut Parser, ctx: &mut Ctx) -> Result<(), String> {
    // <name> = ...
    let name = p.parse_word()?;
    let r = ctx.lookup(&name)?;
    p.expect_punct('=')?;

    // Two cases:
    //  - mem[y] form: x = mem[y];
    //  - operator form: x = y OP z;
    if p.eat_word("mem") {
        p.expect_punct('[')?;
        let y = p.parse_word()?;
        let ry = ctx.lookup(&y)?;
        p.expect_punct(']')?;
        p.expect_punct(';')?;
        ctx.asm.push_str(&format!("    LOAD r{}, r{}\n", r, ry));
        return Ok(());
    }

    // Otherwise expect "y OP z;" where OP is + - *.
    let y = p.parse_word()?;
    let ry = ctx.lookup(&y)?;
    let op = match p.bump() {
        Some(Tok::Punct('+')) => "ADD",
        Some(Tok::Punct('-')) => "SUB",
        Some(Tok::Punct('*')) => "MUL",
        other => return Err(format!("expected '+', '-' or '*', got {:?}", other)),
    };
    let z = p.parse_word()?;
    let rz = ctx.lookup(&z)?;
    p.expect_punct(';')?;
    ctx.asm.push_str(&format!("    {} r{}, r{}, r{}\n", op, r, ry, rz));
    Ok(())
}

fn compile_mem_store(p: &mut Parser, ctx: &mut Ctx) -> Result<(), String> {
    p.expect_punct('[')?;
    let y = p.parse_word()?;
    let ry = ctx.lookup(&y)?;
    p.expect_punct(']')?;
    p.expect_punct('=')?;
    let x = p.parse_word()?;
    let rx = ctx.lookup(&x)?;
    p.expect_punct(';')?;
    ctx.asm.push_str(&format!("    STORE r{}, r{}\n", ry, rx));
    Ok(())
}

fn compile_if(p: &mut Parser, ctx: &mut Ctx) -> Result<(), String> {
    let name = p.parse_word()?;
    let r = ctx.lookup(&name)?;
    let op = match p.bump() {
        Some(Tok::EqEq)  => true,   // == 0
        Some(Tok::NotEq) => false,  // != 0
        other => return Err(format!("expected '==' or '!=', got {:?}", other)),
    };
    match p.bump() {
        Some(Tok::Num(0)) => {}
        other => return Err(format!("only '== 0' or '!= 0' supported, got rhs {:?}", other)),
    }
    p.expect_punct('{')?;
    let l_else = ctx.fresh_label("else");
    let l_end = ctx.fresh_label("endif");
    if op {
        // if x == 0 { THEN } else { ELSE }
        // JZ x, then_l ; JMP else_l ; then_l: THEN ; JMP end ; else_l: ELSE ; end:
        // Cleaner: invert with two labels.
        // We'll emit: JZ x, then_l; JMP l_else; then_l: THEN; JMP l_end; l_else: ELSE; l_end:
        let l_then = ctx.fresh_label("then");
        ctx.asm.push_str(&format!("    JZ r{}, {}\n", r, l_then));
        ctx.asm.push_str(&format!("    JMP {}\n", l_else));
        ctx.asm.push_str(&format!("{}:\n", l_then));
        compile_block(p, ctx)?;
        ctx.asm.push_str(&format!("    JMP {}\n", l_end));
    } else {
        // if x != 0 { THEN } else { ELSE }
        // JZ x, l_else; THEN; JMP l_end; l_else: ELSE; l_end:
        ctx.asm.push_str(&format!("    JZ r{}, {}\n", r, l_else));
        compile_block(p, ctx)?;
        ctx.asm.push_str(&format!("    JMP {}\n", l_end));
    }
    ctx.asm.push_str(&format!("{}:\n", l_else));
    if p.eat_word("else") {
        p.expect_punct('{')?;
        compile_block(p, ctx)?;
    }
    ctx.asm.push_str(&format!("{}:\n", l_end));
    Ok(())
}

fn compile_while(p: &mut Parser, ctx: &mut Ctx) -> Result<(), String> {
    let name = p.parse_word()?;
    let r = ctx.lookup(&name)?;
    // We support while x != 0 { ... } and while x == 0 { ... }.
    let neq = match p.bump() {
        Some(Tok::NotEq) => true,
        Some(Tok::EqEq)  => false,
        other => return Err(format!("expected '!=' or '==', got {:?}", other)),
    };
    match p.bump() {
        Some(Tok::Num(0)) => {}
        other => return Err(format!("only ' != 0' or '== 0' supported, got {:?}", other)),
    }
    p.expect_punct('{')?;

    let l_top = ctx.fresh_label("loop");
    let l_end = ctx.fresh_label("endloop");
    if neq {
        // while x != 0 { body }: top: JZ x, end ; body ; JMP top ; end:
        ctx.asm.push_str(&format!("{}:\n", l_top));
        ctx.asm.push_str(&format!("    JZ r{}, {}\n", r, l_end));
        compile_block(p, ctx)?;
        ctx.asm.push_str(&format!("    JMP {}\n", l_top));
        ctx.asm.push_str(&format!("{}:\n", l_end));
    } else {
        // while x == 0: top: JZ x, body ; JMP end ; body: <body> ; JMP top ; end:
        let l_body = ctx.fresh_label("body");
        ctx.asm.push_str(&format!("{}:\n", l_top));
        ctx.asm.push_str(&format!("    JZ r{}, {}\n", r, l_body));
        ctx.asm.push_str(&format!("    JMP {}\n", l_end));
        ctx.asm.push_str(&format!("{}:\n", l_body));
        compile_block(p, ctx)?;
        ctx.asm.push_str(&format!("    JMP {}\n", l_top));
        ctx.asm.push_str(&format!("{}:\n", l_end));
    }
    Ok(())
}

fn compile_block(p: &mut Parser, ctx: &mut Ctx) -> Result<(), String> {
    while !p.eat_punct('}') {
        if p.is_eof() { return Err("unterminated block".into()); }
        compile_stmt(p, ctx)?;
    }
    Ok(())
}
