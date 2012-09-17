/*

The compiler code necessary to implement the #[auto_serialize2]
extension.  The idea here is that type-defining items may be tagged
with #[auto_serialize2], which will cause us to generate a little
companion module with the same name as the item.

For example, a type like:

    type node_id = uint;

would generate two functions like:

    impl node_id: Serializable {
        fn serialize<S: Serializer>(s: S) {
            s.emit_uint(self)
        }

        static fn deserialize<D: Deserializer>(d: D) -> node_id {
            d.read_uint()
        }
    }

Other interesting scenarios are whe the item has type parameters or
references other non-built-in types.  A type definition like:

    type spanned<T> = {node: T, span: span};

would yield functions like:

    impl<T: Serializable> spanned<T>: Serializable {
        fn serialize<S: Serializer>(s: S) {
            do s.emit_rec {
                s.emit_rec_field("node", 0, self.node.serialize(s));
                s.emit_rec_field("span", 1, self.span.serialize(s));
            }
        }

        static fn deserialize<D: Deserializer>(d: D) -> spanned<T> {
            do d.read_rec {
                {
                    node: d.read_rec_field(~"node", 0, || deserialize(d)),
                    span: d.read_rec_field(~"span", 1, || deserialize(d)),
                }
            }
        }
    }

FIXME (#2810)--Hygiene. Search for "__" strings.  We also assume "std" is the
standard library.

Misc notes:
-----------

I use move mode arguments for ast nodes that will get inserted as is
into the tree.  This is intended to prevent us from inserting the same
node twice.

*/

use base::*;
use codemap::span;
use std::map;
use std::map::HashMap;

export expand;

// Transitional reexports so qquote can find the paths it is looking for
mod syntax {
    pub use ext;
    pub use parse;
}

type ser_tps_map = map::HashMap<ast::ident, fn@(@ast::expr) -> ~[@ast::stmt]>;
type deser_tps_map = map::HashMap<ast::ident, fn@() -> @ast::expr>;

/*
trait ext_ctxt_helpers {
    fn helper_path(base_path: @ast::path, helper_name: ~str) -> @ast::path;
    fn path(span: span, strs: ~[ast::ident]) -> @ast::path;
    fn path_tps(span: span, strs: ~[ast::ident],
                tps: ~[@ast::ty]) -> @ast::path;
    fn ty_path(span: span, strs: ~[ast::ident], tps: ~[@ast::ty]) -> @ast::ty;
    fn ty_fn(span: span,
             -input_tys: ~[@ast::ty],
             -output: @ast::ty) -> @ast::ty;
    fn ty_nil(span: span) -> @ast::ty;
    fn expr(span: span, node: ast::expr_) -> @ast::expr;
    fn var_ref(span: span, name: ast::ident) -> @ast::expr;
    fn blk(span: span, stmts: ~[@ast::stmt]) -> ast::blk;
    fn expr_blk(expr: @ast::expr) -> ast::blk;
    fn binder_pat(span: span, nm: ast::ident) -> @ast::pat;
    fn stmt(expr: @ast::expr) -> @ast::stmt;
    fn alt_stmt(arms: ~[ast::arm], span: span, -v: @ast::expr) -> @ast::stmt;
    fn lit_str(span: span, s: @~str) -> @ast::expr;
    fn lit_uint(span: span, i: uint) -> @ast::expr;
    fn lambda(blk: ast::blk) -> @ast::expr;
    fn clone_folder() -> fold::ast_fold;
    fn clone(v: @ast::expr) -> @ast::expr;
    fn clone_ty(v: @ast::ty) -> @ast::ty;
    fn clone_ty_param(v: ast::ty_param) -> ast::ty_param;
    fn at(span: span, expr: @ast::expr) -> @ast::expr;
}

impl ext_ctxt: ext_ctxt_helpers {
    fn helper_path(base_path: @ast::path,
                   helper_name: ~str) -> @ast::path {
        let head = vec::init(base_path.idents);
        let tail = vec::last(base_path.idents);
        self.path(base_path.span,
                  vec::append(head,
                              ~[self.parse_sess().interner.
                                intern(@(helper_name + ~"_" +
                                         *self.parse_sess().interner.get(
                                             tail)))]))
    }

    fn path(span: span, strs: ~[ast::ident]) -> @ast::path {
        @{span: span, global: false, idents: strs, rp: None, types: ~[]}
    }

    fn path_tps(span: span, strs: ~[ast::ident],
                tps: ~[@ast::ty]) -> @ast::path {
        @{span: span, global: false, idents: strs, rp: None, types: tps}
    }

    fn ty_path(span: span, strs: ~[ast::ident],
               tps: ~[@ast::ty]) -> @ast::ty {
        @{id: self.next_id(),
          node: ast::ty_path(self.path_tps(span, strs, tps), self.next_id()),
          span: span}
    }

    fn ty_fn(span: span,
             -input_tys: ~[@ast::ty],
             -output: @ast::ty) -> @ast::ty {
        let args = do vec::map(input_tys) |ty| {
            {mode: ast::expl(ast::by_ref),
             ty: ty,
             ident: parse::token::special_idents::invalid,
             id: self.next_id()}
        };

        @{id: self.next_id(),
          node: ast::ty_fn(ast::proto_block,
                           ast::impure_fn,
                           @~[],
                           {inputs: args,
                            output: output,
                            cf: ast::return_val}),
          span: span}
    }

    fn ty_nil(span: span) -> @ast::ty {
        @{id: self.next_id(), node: ast::ty_nil, span: span}
    }

    fn expr(span: span, node: ast::expr_) -> @ast::expr {
        @{id: self.next_id(), callee_id: self.next_id(),
          node: node, span: span}
    }

    fn var_ref(span: span, name: ast::ident) -> @ast::expr {
        self.expr(span, ast::expr_path(self.path(span, ~[name])))
    }

    fn blk(span: span, stmts: ~[@ast::stmt]) -> ast::blk {
        {node: {view_items: ~[],
                stmts: stmts,
                expr: None,
                id: self.next_id(),
                rules: ast::default_blk},
         span: span}
    }

    fn expr_blk(expr: @ast::expr) -> ast::blk {
        {node: {view_items: ~[],
                stmts: ~[],
                expr: Some(expr),
                id: self.next_id(),
                rules: ast::default_blk},
         span: expr.span}
    }

    fn binder_pat(span: span, nm: ast::ident) -> @ast::pat {
        let path = @{span: span, global: false, idents: ~[nm],
                     rp: None, types: ~[]};
        @{id: self.next_id(),
          node: ast::pat_ident(ast::bind_by_implicit_ref,
                               path,
                               None),
          span: span}
    }

    fn stmt(expr: @ast::expr) -> @ast::stmt {
        @{node: ast::stmt_semi(expr, self.next_id()),
          span: expr.span}
    }

    fn alt_stmt(arms: ~[ast::arm],
                span: span, -v: @ast::expr) -> @ast::stmt {
        self.stmt(
            self.expr(
                span,
                ast::expr_match(v, arms)))
    }

    fn lit_str(span: span, s: @~str) -> @ast::expr {
        self.expr(
            span,
            ast::expr_vstore(
                self.expr(
                    span,
                    ast::expr_lit(
                        @{node: ast::lit_str(s),
                          span: span})),
                ast::expr_vstore_uniq))
    }

    fn lit_uint(span: span, i: uint) -> @ast::expr {
        self.expr(
            span,
            ast::expr_lit(
                @{node: ast::lit_uint(i as u64, ast::ty_u),
                  span: span}))
    }

    fn lambda(blk: ast::blk) -> @ast::expr {
        let ext_cx = self;
        let blk_e = self.expr(blk.span, ast::expr_block(blk));
        #ast{ || $(blk_e) }
    }

    fn clone_folder() -> fold::ast_fold {
        fold::make_fold(@{
            new_id: |_id| self.next_id(),
            .. *fold::default_ast_fold()
        })
    }

    fn clone(v: @ast::expr) -> @ast::expr {
        let fld = self.clone_folder();
        fld.fold_expr(v)
    }

    fn clone_ty(v: @ast::ty) -> @ast::ty {
        let fld = self.clone_folder();
        fld.fold_ty(v)
    }

    fn clone_ty_param(v: ast::ty_param) -> ast::ty_param {
        let fld = self.clone_folder();
        fold::fold_ty_param(v, fld)
    }

    fn at(span: span, expr: @ast::expr) -> @ast::expr {
        fn repl_sp(old_span: span, repl_span: span, with_span: span) -> span {
            if old_span == repl_span {
                with_span
            } else {
                old_span
            }
        }

        let fld = fold::make_fold(@{
            new_span: |a| repl_sp(a, ast_util::dummy_sp(), span),
            .. *fold::default_ast_fold()
        });

        fld.fold_expr(expr)
    }
}
*/

fn expand(cx: ext_ctxt,
          span: span,
          _mitem: ast::meta_item,
          in_items: ~[@ast::item]) -> ~[@ast::item] {
    fn not_auto_serialize2(a: ast::attribute) -> bool {
        attr::get_attr_name(a) != ~"auto_serialize2"
    }

    fn filter_attrs(item: @ast::item) -> @ast::item {
        @{attrs: vec::filter(item.attrs, not_auto_serialize2),
          .. *item}
    }

    do vec::flat_map(in_items) |in_item| {
        match in_item.node {
            ast::item_ty(ty, tps) => {
                ~[filter_attrs(in_item), ty_impl(cx, ty, tps)]
            }
            _ => {
                cx.span_err(span, ~"#[auto_serialize] can only be \
                                   applied to type and enum \
                                   definitions");
                ~[in_item]
            }
        }
    }
}

fn ty_impl(cx: ext_ctxt, ty: @ast::ty, tps: ~[ast::ty_param]) -> @ast::item {

    // This is a new-style impl declaration.
    // XXX: clownshoes
    let ident = ast::token::special_idents::clownshoes_extensions;

    let path = @{
        span: ty.span,
        global: true,
        idents: ~[
            cx.ident_of(~"std"),
            cx.ident_of(~"serialization2"),
            cx.ident_of(~"Serializable"),
        ],
        rp: None,
        types: ~[]
    };

    let opt_trait = Some(@{
        path: path,
        ref_id: cx.next_id(),
        impl_id: cx.next_id(),
    });

    let methods = ~[
        mk_ser_method(cx, ty),
        mk_deser_method(cx, ty),
    ];

    @{ident: ident,
      attrs: ~[],
      id: cx.next_id(),
      node: ast::item_impl(tps, opt_trait, ty, methods),
      vis: ast::public,
      span: ty.span,
    }
}

fn mk_ser_method(cx: ext_ctxt, ty: @ast::ty) -> @ast::method {
    let ser_bound = cx.ty_path(
        ty.span,
        ~[
            cx.ident_of(~"std"),
            cx.ident_of(~"serialization2"),
            cx.ident_of(~"Serializer"),
        ],
        ~[]
    );

    let ser_tps = ~[{
        ident: cx.ident_of(~"S"),
        id: cx.next_id(),
        bounds: @~[ast::bound_trait(ser_bound)],
    }];

    let ser_inputs = ~[{
        mode: ast::expl(ast::by_ref),
        ty: cx.ty_path(ty.span, ~[cx.ident_of(~"S")], ~[]),
        ident: cx.ident_of(~"s"),
        id: cx.next_id(),
    }];

    let ser_output = @{
        id: cx.next_id(),
        node: ast::ty_nil,
        span: ty.span,
    };

    let ser_decl = {
        inputs: ser_inputs,
        output: ser_output,
        cf: ast::return_val,
    };

    let ser_blk = cx.blk(ty.span, ser_ty(cx, ty));

    @{
        ident: cx.ident_of(~"serialize"),
        attrs: ~[],
        tps: ser_tps,
        self_ty: {node: ast::sty_value, span: ty.span},
        purity: ast::impure_fn,
        decl: ser_decl,
        body: ser_blk,
        id: cx.next_id(),
        span: ty.span,
        self_id: cx.next_id(),
        vis: ast::public,
    }
}

fn ser_ty(cx: ext_ctxt, ty: @ast::ty) -> ~[@ast::stmt] {
    let ext_cx = cx; // required for #ast{}

    match ty.node {
        ast::ty_nil => ~[#ast[stmt]{ self.serialize(s) }],

        ast::ty_bot => {
            cx.span_err(ty.span, ~"Cannot serialize bottom type");
            ~[]
        },

        ast::ty_box(_) => ~[#ast[stmt]{ self.serialize(s) }],

        ast::ty_uniq(_) => ~[#ast[stmt]{ self.serialize(s) }],

        ast::ty_ptr(_) | ast::ty_rptr(*) => {
            cx.span_err(ty.span, ~"cannot serialize pointer types");
            ~[]
        },

        ast::ty_rec(fields) => {
            let stmts = do fields.mapi |idx, field| {
                let name = cx.lit_str(
                    field.span,
                    @cx.str_of(field.node.ident)
                );
                let idx = cx.lit_uint(field.span, idx);

                let expr_self = cx.expr(
                    ty.span,
                    ast::expr_path(
                        cx.path(ty.span, ~[cx.ident_of(~"self")])
                    )
                );

                let expr_name = cx.expr(
                    ty.span,
                    ast::expr_field(
                        expr_self,
                        field.node.ident,
                        ~[])
                );

                let expr_serialize = cx.expr(
                    ty.span,
                    ast::expr_field(expr_name, cx.ident_of(~"serialize"), ~[])
                );

                let expr_arg = cx.expr(
                    ty.span,
                    ast::expr_path(
                        cx.path(ty.span, ~[cx.ident_of(~"s")])
                    )
                );

                let expr = cx.expr(
                    ty.span,
                    ast::expr_call(expr_serialize, ~[expr_arg], false)
                );

                #ast[stmt]{ s.emit_rec_field($(name), $(idx), || $(expr))) }
            };

            let fields_lambda = cx.lambda(cx.blk(ty.span, stmts));

            ~[#ast[stmt]{ s.emit_rec($(fields_lambda)) }]
        },

        ast::ty_fn(*) => {
            cx.span_err(ty.span, ~"cannot serialize function types");
            ~[]
        },

        ast::ty_tup(tys) => ~[#ast[stmt]{ self.serialize(s) }],

        ast::ty_path(_path, _) => {
            ~[#ast[stmt]{ fail }]
        },

        ast::ty_mac(_) => {
            cx.span_err(ty.span, ~"cannot serialize macro types");
            ~[]
        },

        ast::ty_infer => {
            cx.span_err(ty.span, ~"cannot serialize inferred types");
            ~[]
        },

        ast::ty_vec(_) => ~[#ast[stmt]{ self.serialize(s) }],

        ast::ty_fixed_length(*) => {
            cx.span_unimpl(ty.span, ~"serialization for fixed length types");
        }
    }
}

fn mk_deser_method(cx: ext_ctxt, ty: @ast::ty) -> @ast::method {
    let deser_bound = cx.ty_path(
        ty.span,
        ~[
            cx.ident_of(~"std"),
            cx.ident_of(~"serialization2"),
            cx.ident_of(~"Deserializer"),
        ],
        ~[]
    );

    let deser_tps = ~[{
        ident: cx.ident_of(~"D"),
        id: cx.next_id(),
        bounds: @~[ast::bound_trait(deser_bound)],
    }];

    let deser_inputs = ~[{
        mode: ast::expl(ast::by_ref),
        ty: cx.ty_path(ty.span, ~[cx.ident_of(~"D")], ~[]),
        ident: cx.ident_of(~"d"),
        id: cx.next_id(),
    }];

    let deser_decl = {
        inputs: deser_inputs,
        output: ty,
        cf: ast::return_val,
    };

    let deser_blk = cx.expr_blk(deser_ty(cx, ty));

    @{
        ident: cx.ident_of(~"deserialize"),
        attrs: ~[],
        tps: deser_tps,
        self_ty: {node: ast::sty_static, span: ty.span},
        purity: ast::impure_fn,
        decl: deser_decl,
        body: deser_blk,
        id: cx.next_id(),
        span: ty.span,
        self_id: cx.next_id(),
        vis: ast::public,
    }
}

fn deser_ty(cx: ext_ctxt, ty: @ast::ty) -> @ast::expr {
    let ext_cx = cx; // required for #ast{}
    
    match ty.node {
        ast::ty_nil => #ast{ deserialize(d) },

        ast::ty_bot => #ast{ fail },

        ast::ty_box(_) => #ast{ @d.read_box(|| deserialize(d)) },

        ast::ty_uniq(_) => #ast{ ~d.read_uniq(|| deserialize(d)) },

        ast::ty_ptr(*) | ast::ty_rptr(*) => #ast{ fail },

        ast::ty_rec(fields) => {
            let fields = do fields.mapi |idx, field| {
                let name = cx.lit_str(
                    field.span,
                    @cx.str_of(field.node.ident)
                );
                let idx = cx.lit_uint(field.span, idx);
                let expr = #ast{
                     d.read_rec_field($(name), $(idx), || deserialize(d))
                };

                {
                    node: {
                        mutbl: field.node.mt.mutbl,
                        ident: field.node.ident,
                        expr: expr,
                    },
                    span: field.span,
                }
            };

            let fields_expr = cx.expr(ty.span, ast::expr_rec(fields, None));
            let fields_lambda = cx.lambda(cx.expr_blk(fields_expr));

            #ast{ d.read_rec($(fields_lambda)) }
        },

        ast::ty_fn(*) => #ast{ fail },

        ast::ty_tup(tys) => {
            /*
             Generate code like:

             do d.read_tup(3) {
                 (d.read_tup_elt(0, || deserialize(d)),
                  d.read_tup_elt(1, || deserialize(d)),
                  d.read_tup_elt(2, || deserialize(d)))
             }
             */

            let sz = cx.lit_uint(ty.span, tys.len());

            let arg_exprs = do tys.mapi |idx, _t| {
                let idx = cx.lit_uint(ty.span, idx);
                #ast{ d.read_tup_elt($(idx), || deserialize(d)) }
            };

            let expr = cx.expr(ty.span, ast::expr_tup(arg_exprs));
            let body = cx.lambda(cx.expr_blk(expr));

            #ast{ d.read_tup($(sz), $(body)) }
        },

        ast::ty_path(_path, _) => {
            // ...
            fail
        },

        ast::ty_mac(*) => #ast{ fail },

        ast::ty_infer => #ast{ fail },

        ast::ty_vec(_) => {
            #ast{
                do d.read_vec |len| {
                    do d.read_vec(len) |i| {
                        d.read_vec_elt(i, || deserialize(d))
                    }
                }
            }
        },

        ast::ty_fixed_length(*) => {
            cx.span_unimpl(
                ty.span,
                 ~"deserialization for fixed length types"
            );
        },
    }
}
