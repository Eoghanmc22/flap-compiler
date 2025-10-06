use crate::{
    ast::{FunctionAttribute, Type},
    codegen::{
        CodegenCtx, MaybeTailCall,
        clac::{ClacToken, MangledIdent},
        ir::{DataReference, FunctionSignature},
    },
};
use color_eyre::eyre::WrapErr;

pub fn register_mutation_builtins(ctx: &mut CodegenCtx) {
    register_drop_range(ctx);
}

fn register_drop_range(ctx: &mut CodegenCtx) {
    ctx.define_function(
        "drop_range",
        FunctionSignature {
            // start inclusive, end exclusive
            arguements: vec![(Type::Int, "start_depth"), (Type::Int, "end_depth")],
            return_type: Type::Void,
        },
        &[
            FunctionAttribute::NoMangle,
            FunctionAttribute::AllowUnderflow,
            FunctionAttribute::Naked,
        ]
        .into(),
        |ctx| {
            ctx.define_function(
                "drop_range_outer",
                FunctionSignature {
                    arguements: vec![(Type::Int, "start_depth"), (Type::Int, "end_depth")],
                    return_type: Type::Void,
                },
                &[
                    FunctionAttribute::NoMangle,
                    FunctionAttribute::AllowUnderflow,
                    FunctionAttribute::Naked,
                ]
                .into(),
                |ctx| {
                    ctx.define_function(
                        "drop_range_inner",
                        FunctionSignature {
                            arguements: vec![
                                (Type::Int, "start_depth"),
                                (Type::Int, "end_depth"),
                                (Type::Int, "number"),
                            ],
                            return_type: Type::Void,
                        },
                        &[
                            FunctionAttribute::NoMangle,
                            FunctionAttribute::AllowUnderflow,
                            FunctionAttribute::Naked,
                        ]
                        .into(),
                        |ctx| {
                            // start, end, num

                            // Load number
                            ctx.push_token(ClacToken::Number(1))?;
                            ctx.push_token(ClacToken::Pick)?;

                            // Load number
                            ctx.push_token(ClacToken::Number(2))?;
                            ctx.push_token(ClacToken::Pick)?;

                            // start, end, num, num, num

                            // if number != 0
                            ctx.push_token(ClacToken::If)?;
                            // start, end, num, num
                            // later used for mod
                            ctx.push_token(ClacToken::Number(2))?;
                            ctx.push_token(ClacToken::Number(12))?;
                            ctx.push_token(ClacToken::Skip)?;

                            // if number == 0
                            // start, end, num, num
                            ctx.push_token(ClacToken::Drop)?;
                            ctx.push_token(ClacToken::Drop)?;
                            ctx.push_token(ClacToken::Number(-1))?;
                            ctx.push_token(ClacToken::Add)?;
                            ctx.push_token(ClacToken::Swap)?;
                            ctx.push_token(ClacToken::Number(-1))?;
                            ctx.push_token(ClacToken::Add)?;
                            ctx.push_token(ClacToken::Swap)?;
                            // start-1, end-1
                            ctx.push_token(ClacToken::Call {
                                mangled_ident: MangledIdent("drop_range_outer".to_string().into()),
                                stack_delta: 0,
                            })?;
                            // Base case for reconstruction
                            ctx.push_token(ClacToken::Number(0))?;
                            ctx.push_token(ClacToken::Number(32))?;
                            ctx.push_token(ClacToken::Skip)?;

                            // if number != 0
                            // start_depth, end_depth, number, number, 2
                            {
                                // number % 2 = lsb(number) (can be 0, 1, -1)
                                ctx.push_token(ClacToken::Mod)?;

                                // number, number%2
                                ctx.push_token(ClacToken::Swap)?;

                                // number%2, number
                                ctx.push_token(ClacToken::Number(2))?;
                                ctx.push_token(ClacToken::Div)?;

                                // number%2, number/2
                                ctx.push_token(ClacToken::Swap)?;
                                // number/2, number%2

                                ctx.push_token(ClacToken::Number(1))?;
                                ctx.push_token(ClacToken::Pick)?;
                                // number/2, number%2, number%2

                                // if lsb(number) == 1 || -1
                                ctx.push_token(ClacToken::If)?;
                                ctx.push_token(ClacToken::Number(1))?;
                                ctx.push_token(ClacToken::Number(3))?;
                                ctx.push_token(ClacToken::Skip)?;

                                // if lsb(number) == 0
                                // number/2, number%2
                                ctx.push_token(ClacToken::Drop)?;
                                ctx.push_token(ClacToken::Number(12))?;
                                ctx.push_token(ClacToken::Skip)?;

                                // if lsb(number) == 1 || -1
                                // number/2, number%2, 1
                                ctx.push_token(ClacToken::Add)?;
                                // number/2, number%2+1

                                // if lsb(number) == 1
                                ctx.push_token(ClacToken::If)?;
                                // start_depth, end_depth, number/2
                                ctx.push_token(ClacToken::Call {
                                    mangled_ident: MangledIdent(
                                        "drop_range_inner".to_string().into(),
                                    ),
                                    stack_delta: 0,
                                })?;
                                ctx.push_token(ClacToken::Number(4))?;
                                ctx.push_token(ClacToken::Skip)?;

                                // if lsb(number) == -1
                                // start_depth, end_depth, number/2
                                ctx.push_token(ClacToken::Call {
                                    mangled_ident: MangledIdent(
                                        "drop_range_inner".to_string().into(),
                                    ),
                                    stack_delta: 0,
                                })?;
                                ctx.push_token(ClacToken::Number(-1))?;
                                ctx.push_token(ClacToken::Number(5))?;
                                ctx.push_token(ClacToken::Skip)?;

                                // if lsb(number) == 1
                                ctx.push_token(ClacToken::Number(1))?;
                                ctx.push_token(ClacToken::Number(2))?;
                                ctx.push_token(ClacToken::Skip)?;

                                // if lsb(number) == 0
                                // start_depth, end_depth, number/2
                                ctx.push_token(ClacToken::Call {
                                    mangled_ident: MangledIdent(
                                        "drop_range_inner".to_string().into(),
                                    ),
                                    stack_delta: 0,
                                })?;
                                ctx.push_token(ClacToken::Number(0))?;

                                // start_depth, end_depth, number/2, lsb(number)
                                ctx.push_token(ClacToken::Swap)?;
                                ctx.push_token(ClacToken::Number(2))?;
                                ctx.push_token(ClacToken::Mul)?;
                                ctx.push_token(ClacToken::Add)?;
                                // start_depth, end_depth, number
                            }

                            Ok(MaybeTailCall::Regular(DataReference::Tempoary(
                                ctx.allocate_tempoary(Type::Void),
                            )))
                        },
                    )
                    .wrap_err("Define builtin drop_range_inner")?;

                    // Load end_depth
                    ctx.push_token(ClacToken::Number(1))?;
                    ctx.push_token(ClacToken::Pick)?;

                    // if end_depth != 0
                    // bring forward the next number
                    ctx.push_token(ClacToken::If)?;
                    // Initial value for drop_range_inner `number`
                    ctx.push_token(ClacToken::Rot)?;
                    ctx.push_token(ClacToken::Number(2))?;
                    ctx.push_token(ClacToken::Skip)?;

                    // otherwise when end_depth == 0
                    // jump to end
                    ctx.push_token(ClacToken::Number(19))?;
                    ctx.push_token(ClacToken::Skip)?;

                    // start, end, number

                    // Load start_depth
                    ctx.push_token(ClacToken::Number(3))?;
                    ctx.push_token(ClacToken::Pick)?;

                    // start, end, number, start

                    // if start_depth != 0
                    ctx.push_token(ClacToken::If)?;
                    ctx.push_token(ClacToken::Call {
                        mangled_ident: MangledIdent("drop_range_inner".to_string().into()),
                        stack_delta: 0,
                    })?;
                    // start, end, number_reconstructed
                    ctx.push_token(ClacToken::Number(0))?;
                    ctx.push_token(ClacToken::Skip)?;

                    // start, end, number_to_drop or number_reconstructed

                    // Load end_depth
                    ctx.push_token(ClacToken::Number(2))?;
                    ctx.push_token(ClacToken::Pick)?;

                    // start, end, number_to_drop or number_reconstructed, end

                    // if end_depth != 0
                    ctx.push_token(ClacToken::If)?;
                    ctx.push_token(ClacToken::Drop)?;
                    ctx.push_token(ClacToken::Number(4))?;
                    ctx.push_token(ClacToken::Skip)?;

                    // if end_depth == 0
                    ctx.push_token(ClacToken::Rot)?;
                    ctx.push_token(ClacToken::Rot)?;
                    ctx.push_token(ClacToken::Number(3))?;
                    ctx.push_token(ClacToken::Skip)?;

                    // if end_depth != 0
                    // start, end
                    ctx.push_token(ClacToken::Number(-1))?;
                    ctx.push_token(ClacToken::Add)?;
                    ctx.push_token(ClacToken::Call {
                        mangled_ident: MangledIdent("drop_range_outer".to_string().into()),
                        stack_delta: 0,
                    })?;

                    Ok(MaybeTailCall::Regular(DataReference::Tempoary(
                        ctx.allocate_tempoary(Type::Void),
                    )))
                },
            )
            .wrap_err("Define builtin drop_range_outer")
            .unwrap();

            ctx.push_token(ClacToken::Call {
                mangled_ident: MangledIdent("drop_range_outer".to_string().into()),
                stack_delta: 0,
            })?;
            ctx.push_token(ClacToken::Drop)?;
            ctx.push_token(ClacToken::Drop)?;

            Ok(MaybeTailCall::Regular(DataReference::Tempoary(
                ctx.allocate_tempoary(Type::Void),
            )))
        },
    )
    .wrap_err("Define builtin drop_range")
    .unwrap();
}
