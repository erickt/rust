// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use ast::{MetaItem, Item, Expr, MutMutable, Inherited};
use codemap::Span;
use ext::base::ExtCtxt;
use ext::build::AstBuilder;
use ext::deriving::generic::*;
use parse::token::InternedString;

pub fn expand_deriving_hash(cx: &mut ExtCtxt,
                            span: Span,
                            mitem: @MetaItem,
                            item: @Item,
                            push: &|@Item|) {

    let allow_default_type_param_usage = cx.attribute(
        span,
        cx.meta_list(
            span,
            InternedString::new("allow"),
            ~[cx.meta_word(span, InternedString::new("default_type_param_usage"))]));

    let hash_trait_def = TraitDef {
        span: span,
        attributes: ~[allow_default_type_param_usage],
        path: Path::new_(~["std", "hash", "Hash"], None,
                         ~[~Literal(Path::new_local("__S"))], true),
        additional_bounds: ~[
            Literal(Path::new_(~["std", "hash", "StreamHash"], None,
                                 ~[~Literal(Path::new_local("__S"))], true)),
        ],
        generics: LifetimeBounds {
            lifetimes: ~[],
            bounds: ~[("__S", ~[Path::new(~["std", "hash", "StreamState"])])],
        },
        methods: ~[
            MethodDef {
                name: "hash",
                generics: LifetimeBounds::empty(),
                explicit_self: borrowed_explicit_self(),
                args: ~[Literal(Path::new_local("__S"))],
                ret_ty: Literal(Path::new(~["u64"])),
                inline: true,
                const_nonmatching: false,
                combine_substructure: hash_substructure
            }
        ]
    };

    let stream_hash_trait_def = TraitDef {
        span: span,
        attributes: ~[allow_default_type_param_usage],
        path: Path::new_(~["std", "hash", "StreamHash"], None,
                         ~[~Literal(Path::new_local("__S"))], true),
        additional_bounds: ~[],
        generics: LifetimeBounds {
            lifetimes: ~[],
            bounds: ~[("__S", ~[Path::new(~["std", "hash", "StreamState"])])],
        },
        methods: ~[
            MethodDef {
                name: "input",
                generics: LifetimeBounds::empty(),
                explicit_self: borrowed_explicit_self(),
                args: ~[Ptr(~Literal(Path::new_local("__S")),
                            Borrowed(None, MutMutable))],
                ret_ty: nil_ty(),
                inline: true,
                const_nonmatching: false,
                combine_substructure: stream_hash_substructure
            }
        ]
    };

    hash_trait_def.expand(cx, mitem, item, push);
    stream_hash_trait_def.expand(cx, mitem, item, push);
}

fn hash_substructure(cx: &mut ExtCtxt, span: Span, substr: &Substructure) -> @Expr {
    let self_expr = match substr.self_args {
        [self_expr] => self_expr,
        _ => cx.span_bug(span, "incorrect number of arguments in `deriving(Hash)`")
    };

    let state_expr = match substr.nonself_args {
        [state_expr] => state_expr,
        _ => cx.span_bug(span, "incorrect number of arguments in `deriving(Hash)`")
    };

    // use std::hash::StreamHash;
    let use_stream_hash_path = cx.path(span, ~[cx.ident_of("std"),
                                               cx.ident_of("hash"),
                                               cx.ident_of("StreamHash")]);

    let use_stream_hash = cx.view_use_simple(span, Inherited, use_stream_hash_path);

    // let mut state = state;
    let state_ident = cx.ident_of("state");
    let state_stmt = cx.stmt_let(span, true, state_ident, state_expr);
    let state_expr = cx.expr_ident(span, state_ident);

    // self.input(&mut state);
    let borrow_state_expr = cx.expr_mut_addr_of(span, state_expr);
    let input_ident = cx.ident_of("input");
    let input_expr = cx.expr_method_call(span, self_expr, input_ident, ~[borrow_state_expr]);
    let input_stmt = cx.stmt_expr(input_expr);

    // state.result()
    let result_ident = cx.ident_of("result");
    let result_expr = cx.expr_method_call(span, state_expr, result_ident, ~[]);

    let block = cx.block_all(span,
                             ~[use_stream_hash],
                             ~[state_stmt, input_stmt],
                             Some(result_expr));

    cx.expr_block(block)
}

fn stream_hash_substructure(cx: &mut ExtCtxt, trait_span: Span, substr: &Substructure) -> @Expr {
    let state_expr = match substr.nonself_args {
        [state_expr] => state_expr,
        _ => cx.span_bug(trait_span, "incorrect number of arguments in `deriving(StreamHash)`")
    };
    let hash_ident = substr.method_ident;
    let call_hash = |span, thing_expr| {
        let expr = cx.expr_method_call(span, thing_expr, hash_ident, ~[state_expr]);
        cx.stmt_expr(expr)
    };
    let mut stmts = ~[];

    let fields = match *substr.fields {
        Struct(ref fs) => fs,
        EnumMatching(index, variant, ref fs) => {
            // Determine the discriminant. We will feed this value to the byte
            // iteration function.
            let discriminant = match variant.node.disr_expr {
                Some(d) => d,
                None => cx.expr_uint(trait_span, index)
            };

            stmts.push(call_hash(trait_span, discriminant));

            fs
        }
        _ => cx.span_bug(trait_span, "impossible substructure in `deriving(StreamHash)`")
    };

    for &FieldInfo { self_, span, .. } in fields.iter() {
        stmts.push(call_hash(span, self_));
    }

    if stmts.len() == 0 {
        cx.span_bug(trait_span, "#[deriving(StreamHash)] needs at least one field");
    }

    cx.expr_block(cx.block(trait_span, stmts, None))
}
