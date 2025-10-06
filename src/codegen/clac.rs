use core::fmt;
use std::{fmt::Display, sync::Arc};

use crate::ast::Ident;

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

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct MangledIdent(pub Arc<Ident>);

/// A Clac Source Code Token
#[derive(Debug, Clone)]
pub enum ClacToken {
    Number(i32),
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
        stack_delta: i32,
    },

    // Misc
    NewLine,
    Comment(String),
    Silent(Box<ClacToken>),
}

impl ClacToken {
    pub fn stack_delta(&self) -> i32 {
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
                let ends_with_white_space = text
                    .chars()
                    .last()
                    .map(|it| it.is_whitespace())
                    .unwrap_or(false);

                if ends_with_white_space {
                    writeln!(f, ": comment {text};")
                } else {
                    writeln!(f, ": comment {text} ;")
                }
            }
            ClacToken::Silent(clac_token) => <ClacToken as Display>::fmt(clac_token, f),
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
