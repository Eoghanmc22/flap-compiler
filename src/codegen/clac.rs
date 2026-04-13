use core::fmt;
use std::{fmt::Display, iter, sync::Arc};

use clac_lang::types::FunctionRef;
use regex::Regex;

use crate::ast::Ident;

pub type ClacValue = i64;
pub type ClacValueUnsigned = u64;

#[derive(Default, Debug, Clone)]
pub struct ClacProgram(pub Vec<ClacToken>);

impl Display for ClacProgram {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut iter = self.0.iter().peekable();
        while let Some(token) = iter.next() {
            if matches!(iter.peek(), None | Some(ClacToken::NewLine))
                || matches!(token, ClacToken::NewLine | ClacToken::Comment(_))
            {
                write!(f, "{token}")?;
            } else {
                write!(f, "{token} ")?;
            }
        }

        Ok(())
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct MangledIdent(pub Arc<Ident>);

/// A Clac Source Code Token
#[derive(Debug, Clone)]
pub enum ClacToken {
    Number(ClacValue),
    Print,
    Quit,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
    Lt,
    Drop,
    Swap,
    Rot,
    If,
    Pick,
    Skip,
    StartDef {
        mangled_ident: MangledIdent,
    },
    EndDef,
    Call {
        mangled_ident: MangledIdent,
        stack_delta: ClacValue,
    },

    // Misc
    NewLine,
    Comment(String),
    Silent(Box<ClacToken>),

    // Clac++
    Syscall,
    Write8,
    WriteNative,
    Read8,
    ReadNative,
    WidthNative,
    DropRange {
        stack_delta: ClacValue,
    },
}

impl ClacToken {
    pub fn stack_delta(&self) -> ClacValue {
        match self {
            ClacToken::Number(_) => 1,
            ClacToken::Print => -1,
            ClacToken::Quit => 0,
            ClacToken::Add => -1,
            ClacToken::Sub => -1,
            ClacToken::Mul => -1,
            ClacToken::Div => -1,
            ClacToken::Mod => -1,
            ClacToken::Pow => -1,
            ClacToken::Lt => -1,
            ClacToken::Drop => -1,
            ClacToken::Swap => 0,
            ClacToken::Rot => 0,
            ClacToken::If => -1,
            ClacToken::Pick => 0,
            ClacToken::Skip => -1,
            ClacToken::StartDef { .. } => 0,
            ClacToken::EndDef => 0,
            ClacToken::Call { stack_delta, .. } => *stack_delta,
            ClacToken::NewLine => 0,
            ClacToken::Comment(_) => 0,
            ClacToken::Silent(_) => 0,
            ClacToken::Syscall => -6,
            ClacToken::Write8 => -2,
            ClacToken::WriteNative => -2,
            ClacToken::Read8 => 0,
            ClacToken::ReadNative => 0,
            ClacToken::WidthNative => 1,
            ClacToken::DropRange { stack_delta } => *stack_delta,
        }
    }

    pub fn canonicalize(&self) -> &ClacToken {
        match self {
            ClacToken::Silent(token) => token.canonicalize(),
            token => token,
        }
    }
}

impl Display for ClacToken {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ClacToken::Number(num) => write!(f, "{num}"),
            ClacToken::Print => write!(f, "print"),
            ClacToken::Quit => write!(f, "quit"),
            ClacToken::Add => write!(f, "+"),
            ClacToken::Sub => write!(f, "-"),
            ClacToken::Mul => write!(f, "*"),
            ClacToken::Div => write!(f, "/"),
            ClacToken::Mod => write!(f, "%"),
            ClacToken::Pow => write!(f, "**"),
            ClacToken::Lt => write!(f, "<"),
            ClacToken::Drop => write!(f, "drop"),
            ClacToken::Swap => write!(f, "swap"),
            ClacToken::Rot => write!(f, "rot"),
            ClacToken::If => write!(f, "if"),
            ClacToken::Pick => write!(f, "pick"),
            ClacToken::Skip => write!(f, "skip"),
            ClacToken::StartDef {
                mangled_ident: ident,
            } => write!(f, ": {}", ident.0),
            ClacToken::EndDef => write!(f, ";"),
            ClacToken::Call {
                mangled_ident: ident,
                ..
            } => write!(f, "{}", ident.0),
            ClacToken::NewLine => writeln!(f),
            ClacToken::Comment(text) => {
                let regex = Regex::new(r"(\s);(\s)").unwrap();

                writeln!(
                    f,
                    "{}",
                    regex.replace_all(&format!(": comment {} ;", text.trim()), r"$1\;$2")
                )
            }
            ClacToken::Silent(clac_token) => <ClacToken as Display>::fmt(clac_token, f),
            ClacToken::Syscall => write!(f, "syscall"),
            ClacToken::Write8 => write!(f, "write8"),
            ClacToken::WriteNative => write!(f, "write_native"),
            ClacToken::Read8 => write!(f, "read8"),
            ClacToken::ReadNative => write!(f, "read_native"),
            ClacToken::WidthNative => write!(f, "width_native"),
            ClacToken::DropRange { .. } => write!(f, "drop_range"),
        }
    }
}

impl PartialEq for ClacToken {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Number(l0), Self::Number(r0)) => l0 == r0,
            (
                Self::StartDef {
                    mangled_ident: l_mangled_ident,
                },
                Self::StartDef {
                    mangled_ident: r_mangled_ident,
                },
            ) => l_mangled_ident == r_mangled_ident,
            (
                Self::Call {
                    mangled_ident: l_mangled_ident,
                    stack_delta: l_stack_delta,
                },
                Self::Call {
                    mangled_ident: r_mangled_ident,
                    stack_delta: r_stack_delta,
                },
            ) => l_mangled_ident == r_mangled_ident && l_stack_delta == r_stack_delta,
            (Self::Comment(l0), Self::Comment(r0)) => l0 == r0,
            (Self::Silent(l0), r0) => &**l0 == r0,
            (l0, Self::Silent(r0)) => l0 == &**r0,
            _ => core::mem::discriminant(self) == core::mem::discriminant(other),
        }
    }
}

impl ClacToken {
    pub fn as_clac_lang(&self) -> impl Iterator<Item = clac_lang::types::Token> {
        use clac_lang::types::Token;

        fn call(s: &str) -> Token {
            Token::FunctionCall(FunctionRef::Unresolved(s.to_string()))
        }

        if let ClacToken::Silent(inner) = self {
            return inner.as_clac_lang();
        }

        iter::from_coroutine(
            #[coroutine]
            || {
                let token = match self {
                    ClacToken::Number(val) => Token::Literal(*val),
                    ClacToken::Print => Token::Print,
                    ClacToken::Quit => Token::Quit,
                    ClacToken::Add => call("+"),
                    ClacToken::Sub => call("-"),
                    ClacToken::Mul => call("*"),
                    ClacToken::Div => call("/"),
                    ClacToken::Mod => call("%"),
                    ClacToken::Pow => call("**"),
                    ClacToken::Lt => call("<"),
                    ClacToken::Drop => Token::Drop,
                    ClacToken::Swap => Token::Swap,
                    ClacToken::Rot => Token::Rot,
                    ClacToken::If => Token::If,
                    ClacToken::Pick => Token::Pick,
                    ClacToken::Skip => Token::Skip,
                    ClacToken::StartDef { mangled_ident } => {
                        yield Token::Colon;
                        yield call(&mangled_ident.0);
                        return;
                    }
                    ClacToken::EndDef => Token::Semicolon,
                    ClacToken::Call { mangled_ident, .. } => call(&mangled_ident.0),
                    ClacToken::NewLine => return,
                    ClacToken::Comment(_) => return,
                    ClacToken::Silent(_) => unreachable!(),

                    // clac++ extensions
                    ClacToken::Syscall => call("syscall"),
                    ClacToken::Write8 => call("write8"),
                    ClacToken::WriteNative => call("write_native"),
                    ClacToken::Read8 => call("read8"),
                    ClacToken::ReadNative => call("read_native"),
                    ClacToken::WidthNative => call("width_native"),
                    ClacToken::DropRange { .. } => call("drop_range"),
                };

                yield token;
            },
        )
    }
}
