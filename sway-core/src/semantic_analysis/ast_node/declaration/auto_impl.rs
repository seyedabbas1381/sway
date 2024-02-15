use std::ops::Deref;

use crate::{
    decl_engine::{parsed_engine::ParsedDeclEngineInsert, DeclEngineGet},
    language::{
        parsed::{
            AmbiguousPathExpression, AmbiguousSuffix, AstNode, AstNodeContent, CodeBlock,
            Declaration, DelineatedPathExpression, Expression, ExpressionKind, FunctionDeclaration,
            FunctionDeclarationKind, FunctionParameter, ImplItem, ImplTrait, MatchBranch,
            MatchExpression, MethodApplicationExpression, MethodName, Scrutinee, StructExpression,
            StructExpressionField,
        },
        ty::{self, TyAstNode, TyDecl},
        CallPath, Literal, QualifiedCallPath,
    },
    semantic_analysis::{type_check_context::EnforceTypeArguments, TypeCheckContext},
    transform::AttributesMap,
    Engines, TraitConstraint, TypeArgs, TypeArgument, TypeBinding, TypeId, TypeInfo, TypeParameter,
};
use sway_error::handler::Handler;
use sway_types::{integer_bits::IntegerBits, BaseIdent, Ident, Span};

/// Contains all information needed to implement AbiEncode
pub struct AutoImplAbiEncodeContext<'a, 'b> {
    ctx: &'b mut TypeCheckContext<'a>,
    buffer_type_id: TypeId,
    buffer_reader_type_id: TypeId,
    abi_encode_call_path: CallPath,
    abi_decode_call_path: CallPath,
}

impl<'a, 'b> AutoImplAbiEncodeContext<'a, 'b> {
    /// This function fails if the context does not have access to the "core" module
    pub fn new(ctx: &'b mut TypeCheckContext<'a>) -> Option<Self> {
        let buffer_type_id =
            Self::resolve_type(ctx, CallPath::absolute(&["core", "codec", "Buffer"]))?;
        let buffer_reader_type_id =
            Self::resolve_type(ctx, CallPath::absolute(&["core", "codec", "BufferReader"]))?;
        Some(Self {
            ctx,
            buffer_type_id,
            buffer_reader_type_id,
            abi_encode_call_path: CallPath::absolute(&["core", "codec", "AbiEncode"]),
            abi_decode_call_path: CallPath::absolute(&["core", "codec", "AbiDecode"]),
        })
    }

    fn resolve_type(ctx: &mut TypeCheckContext<'_>, call_path: CallPath) -> Option<TypeId> {
        let handler = Handler::default();
        let buffer_type_id = ctx.engines.te().insert(
            ctx.engines,
            TypeInfo::Custom {
                qualified_call_path: QualifiedCallPath {
                    call_path,
                    qualified_path_root: None,
                },
                type_arguments: None,
                root_type_id: None,
            },
            None,
        );
        let buffer_type_id = ctx
            .resolve_type(
                &handler,
                buffer_type_id,
                &Span::dummy(),
                EnforceTypeArguments::No,
                None,
            )
            .ok()?;
        Some(buffer_type_id)
    }

    fn import_core_codec(&mut self) -> bool {
        // Check if the compilation context has acces to the
        // core library.
        let handler = Handler::default();
        let _ = self.ctx.star_import(
            &handler,
            &[
                Ident::new_no_span("core".into()),
                Ident::new_no_span("codec".into()),
            ],
            true,
        );

        !handler.has_errors()
    }

    fn auto_impl_abi_decode(
        &mut self,
        type_parameters: &[TypeParameter],
        suffix: BaseIdent,
        _unit_type_id: TypeId,
        engines: &Engines,
        contents: Vec<AstNode>,
    ) -> Option<TyAstNode> {
        let type_parameters =
            self.duplicate_type_parameters_with_extra_constraint(type_parameters, "AbiDecode");
        let (implementing_for_type_id, implementing_for) =
            self.build_implementing_for_with_type_parameters(suffix, &type_parameters);

        let fn_abi_decode_trait_item = FunctionDeclaration {
            purity: crate::language::Purity::Pure,
            attributes: AttributesMap::default(),
            name: Ident::new_no_span("abi_decode".into()),
            visibility: crate::language::Visibility::Public,
            body: CodeBlock {
                contents,
                whole_block_span: Span::dummy(),
            },
            parameters: vec![FunctionParameter {
                name: Ident::new_no_span("buffer".into()),
                is_reference: true,
                is_mutable: true,
                mutability_span: Span::dummy(),
                type_argument: TypeArgument {
                    type_id: self.buffer_reader_type_id,
                    initial_type_id: self.buffer_reader_type_id,
                    span: Span::dummy(),
                    call_path_tree: None,
                },
            }],
            span: Span::dummy(),
            return_type: TypeArgument {
                type_id: implementing_for_type_id,
                initial_type_id: implementing_for_type_id,
                span: Span::dummy(),
                call_path_tree: None,
            },
            type_parameters: vec![],
            where_clause: vec![],
            kind: FunctionDeclarationKind::Default,
        };

        let fn_abi_decode_trait_item = engines.pe().insert(fn_abi_decode_trait_item);
        let impl_abi_decode = ImplTrait {
            impl_type_parameters: type_parameters,
            trait_name: self.abi_decode_call_path.clone(),
            trait_type_arguments: vec![],
            implementing_for,
            items: vec![ImplItem::Fn(fn_abi_decode_trait_item)],
            block_span: Span::dummy(),
        };

        let impl_abi_decode = engines.pe().insert(impl_abi_decode);
        let impl_abi_decode = Declaration::ImplTrait(impl_abi_decode);

        let handler = Handler::default();
        let impl_abi_decode = TyAstNode::type_check(
            &handler,
            self.ctx.by_ref(),
            AstNode {
                content: AstNodeContent::Declaration(impl_abi_decode),
                span: Span::dummy(),
            },
        )
        .ok()?;

        assert!(!handler.has_errors(), "{:?}", handler);
        assert!(!handler.has_warnings(), "{:?}", handler);

        Some(impl_abi_decode)
    }

    fn build_implementing_for_with_type_parameters(
        &mut self,
        suffix: BaseIdent,
        type_parameters: &Vec<TypeParameter>,
    ) -> (TypeId, TypeArgument) {
        let qualified_call_path = QualifiedCallPath {
            call_path: CallPath {
                prefixes: vec![],
                suffix,
                is_absolute: false,
            },
            qualified_path_root: None,
        };

        let type_arguments = if type_parameters.is_empty() {
            None
        } else {
            Some(
                type_parameters
                    .iter()
                    .map(|x| {
                        let type_id = self.ctx.engines().te().insert(
                            self.ctx.engines(),
                            TypeInfo::Custom {
                                qualified_call_path: QualifiedCallPath {
                                    call_path: CallPath {
                                        prefixes: vec![],
                                        suffix: x.name_ident.clone(),
                                        is_absolute: false,
                                    },
                                    qualified_path_root: None,
                                },
                                type_arguments: None,
                                root_type_id: None,
                            },
                            None,
                        );

                        TypeArgument {
                            type_id,
                            initial_type_id: type_id,
                            span: Span::dummy(),
                            call_path_tree: None,
                        }
                    })
                    .collect(),
            )
        };

        let type_id = self.ctx.engines.te().insert(
            self.ctx.engines,
            TypeInfo::Custom {
                qualified_call_path,
                type_arguments,
                root_type_id: None,
            },
            None,
        );

        let implementing_for = TypeArgument {
            type_id,
            initial_type_id: type_id,
            span: Span::dummy(),
            call_path_tree: None,
        };

        (type_id, implementing_for)
    }

    // This duplicates the "decl" type parameters and adds an extra constraint, for example:
    //
    // ```
    // enum E<T> where T: SomeTrait {
    //
    // }
    // ```
    //
    // This will return `T: SomeTrait + ExtraConstraint`
    fn duplicate_type_parameters_with_extra_constraint(
        &mut self,
        type_parameters: &[TypeParameter],
        constraint_name: &str,
    ) -> Vec<TypeParameter> {
        type_parameters
            .iter()
            .map(|type_parameter| {
                let type_id = self.ctx.engines.te().insert(
                    self.ctx.engines(),
                    TypeInfo::Custom {
                        qualified_call_path: QualifiedCallPath {
                            call_path: CallPath {
                                prefixes: vec![],
                                suffix: Ident::new_no_span(
                                    type_parameter.name_ident.as_str().into(),
                                ),
                                is_absolute: false,
                            },
                            qualified_path_root: None,
                        },
                        type_arguments: None,
                        root_type_id: None,
                    },
                    None,
                );

                let mut trait_constraints: Vec<_> = type_parameter
                    .trait_constraints
                    .iter()
                    .map(|x| TraitConstraint {
                        trait_name: CallPath {
                            prefixes: vec![],
                            suffix: Ident::new_no_span(x.trait_name.suffix.as_str().into()),
                            is_absolute: false,
                        },
                        type_arguments: x
                            .type_arguments
                            .iter()
                            .map(|x| {
                                let name = match &*self.ctx.engines.te().get(x.type_id) {
                                    TypeInfo::Custom {
                                        qualified_call_path,
                                        ..
                                    } => Ident::new_no_span(
                                        qualified_call_path.call_path.suffix.as_str().into(),
                                    ),
                                    _ => todo!(),
                                };

                                let type_id = self.ctx.engines.te().insert(
                                    self.ctx.engines(),
                                    TypeInfo::Custom {
                                        qualified_call_path: QualifiedCallPath {
                                            call_path: CallPath {
                                                prefixes: vec![],
                                                suffix: name,
                                                is_absolute: false,
                                            },
                                            qualified_path_root: None,
                                        },
                                        type_arguments: None,
                                        root_type_id: None,
                                    },
                                    None,
                                );

                                TypeArgument {
                                    type_id,
                                    initial_type_id: type_id,
                                    span: Span::dummy(),
                                    call_path_tree: None,
                                }
                            })
                            .collect(),
                    })
                    .collect();

                trait_constraints.push(TraitConstraint {
                    trait_name: CallPath {
                        prefixes: vec![],
                        suffix: Ident::new_no_span(constraint_name.into()),
                        is_absolute: false,
                    },
                    type_arguments: vec![],
                });

                TypeParameter {
                    type_id,
                    initial_type_id: type_id,
                    name_ident: Ident::new_no_span(type_parameter.name_ident.as_str().into()),
                    trait_constraints,
                    trait_constraints_span: Span::dummy(),
                    is_from_parent: false,
                }
            })
            .collect()
    }

    fn auto_impl_abi_encode(
        &mut self,
        type_parameters: &[TypeParameter],
        suffix: BaseIdent,
        unit_type_id: TypeId,
        engines: &Engines,
        contents: Vec<AstNode>,
    ) -> Option<TyAstNode> {
        let type_parameters =
            self.duplicate_type_parameters_with_extra_constraint(type_parameters, "AbiEncode");
        let (implementing_for_type_id, implementing_for) =
            self.build_implementing_for_with_type_parameters(suffix, &type_parameters);
        let fn_trait_item = self.build_abi_encode_fn_trait_item(
            contents,
            implementing_for_type_id,
            unit_type_id,
            engines,
        );
        self.type_check_impl(type_parameters, implementing_for, fn_trait_item, engines)
    }

    fn type_check_impl(
        &mut self,
        type_parameters: Vec<TypeParameter>,
        implementing_for: TypeArgument,
        fn_abi_encode_trait_item: crate::decl_engine::parsed_id::ParsedDeclId<FunctionDeclaration>,
        engines: &Engines,
    ) -> Option<TyAstNode> {
        let impl_abi_encode_for_enum = ImplTrait {
            impl_type_parameters: type_parameters,
            trait_name: self.abi_encode_call_path.clone(),
            trait_type_arguments: vec![],
            implementing_for,
            items: vec![ImplItem::Fn(fn_abi_encode_trait_item)],
            block_span: Span::dummy(),
        };
        let impl_abi_encode_for_enum = engines.pe().insert(impl_abi_encode_for_enum);
        let impl_abi_encode_for_enum = Declaration::ImplTrait(impl_abi_encode_for_enum);
        let handler = Handler::default();
        let impl_abi_encode_for_enum = TyAstNode::type_check(
            &handler,
            self.ctx.by_ref(),
            AstNode {
                content: AstNodeContent::Declaration(impl_abi_encode_for_enum),
                span: Span::dummy(),
            },
        )
        .ok()?;
        assert!(!handler.has_errors());
        assert!(!handler.has_warnings());
        Some(impl_abi_encode_for_enum)
    }

    fn build_abi_encode_fn_trait_item(
        &mut self,
        contents: Vec<AstNode>,
        implementing_for_type_id: TypeId,
        unit_type_id: TypeId,
        engines: &Engines,
    ) -> crate::decl_engine::parsed_id::ParsedDeclId<FunctionDeclaration> {
        let fn_abi_encode_trait_item = FunctionDeclaration {
            purity: crate::language::Purity::Pure,
            attributes: AttributesMap::default(),
            name: Ident::new_no_span("abi_encode".into()),
            visibility: crate::language::Visibility::Public,
            body: CodeBlock {
                contents,
                whole_block_span: Span::dummy(),
            },
            parameters: vec![
                FunctionParameter {
                    name: Ident::new_no_span("self".into()),
                    is_reference: false,
                    is_mutable: false,
                    mutability_span: Span::dummy(),
                    type_argument: TypeArgument {
                        type_id: implementing_for_type_id,
                        initial_type_id: implementing_for_type_id,
                        span: Span::dummy(),
                        call_path_tree: None,
                    },
                },
                FunctionParameter {
                    name: Ident::new_no_span("buffer".into()),
                    is_reference: true,
                    is_mutable: true,
                    mutability_span: Span::dummy(),
                    type_argument: TypeArgument {
                        type_id: self.buffer_type_id,
                        initial_type_id: self.buffer_type_id,
                        span: Span::dummy(),
                        call_path_tree: None,
                    },
                },
            ],
            span: Span::dummy(),
            return_type: TypeArgument {
                type_id: unit_type_id,
                initial_type_id: unit_type_id,
                span: Span::dummy(),
                call_path_tree: None,
            },
            type_parameters: vec![],
            where_clause: vec![],
            kind: FunctionDeclarationKind::Default,
        };
        let fn_abi_encode_trait_item = engines.pe().insert(fn_abi_encode_trait_item);
        fn_abi_encode_trait_item
    }

    // Check if a struct can implement AbiEncode and AbiDecode
    fn can_auto_impl_struct(&mut self, decl: &TyDecl) -> (bool, bool) {
        // skip module "core"
        // Because of ordering, we cannot guarantee auto impl
        // for structs inside "core"
        if matches!(self.ctx.namespace.root().module.name.as_ref(), Some(x) if x.as_str() == "core")
        {
            return (false, false);
        }

        let Some(decl_ref) = decl.get_struct_decl_ref() else {
            return (false, false);
        };
        let struct_ref = self.ctx.engines().de().get(decl_ref.id());

        // Do not support types with generic constraints
        // because this generates a circular impl trait
        if struct_ref.type_parameters.iter().any(|x| {
            x.trait_constraints
                .iter()
                .any(|c| !c.type_arguments.is_empty())
        }) {
            return (false, false);
        }

        let all_fields_are_abi_encode = struct_ref.fields.iter().all(|field| {
            if let TypeInfo::UnknownGeneric { .. } =
                &*self.ctx.engines().te().get(field.type_argument.type_id)
            {
                return true;
            }

            self.ctx.check_type_impls_traits(
                field.type_argument.type_id,
                &[TraitConstraint {
                    trait_name: self.abi_encode_call_path.clone(),
                    type_arguments: vec![],
                }],
            )
        });

        let all_fields_are_abi_decode = struct_ref.fields.iter().all(|field| {
            if let TypeInfo::UnknownGeneric { .. } =
                &*self.ctx.engines().te().get(field.type_argument.type_id)
            {
                return true;
            }

            self.ctx.check_type_impls_traits(
                field.type_argument.type_id,
                &[TraitConstraint {
                    trait_name: self.abi_decode_call_path.clone(),
                    type_arguments: vec![],
                }],
            )
        });

        (all_fields_are_abi_encode, all_fields_are_abi_decode)
    }

    // Auto implements AbiEncode and AbiDecode for structs and returns their `AstNode`s.
    fn auto_impl_struct(
        &mut self,
        engines: &Engines,
        decl: &TyDecl,
    ) -> (Option<TyAstNode>, Option<TyAstNode>) {
        let (impl_encode, impl_decode) = self.can_auto_impl_struct(decl);

        if !impl_encode && !impl_decode {
            return (None, None);
        }

        let implementing_for_decl_ref = decl.get_struct_decl_ref().unwrap();

        let unit_type_id =
            self.ctx
                .engines
                .te()
                .insert(self.ctx.engines, TypeInfo::Tuple(vec![]), None);

        let struct_decl = self.ctx.engines().de().get(implementing_for_decl_ref.id());

        if !self.import_core_codec() {
            return (None, None);
        }

        let abi_encode_contents = struct_decl
            .fields
            .iter()
            .map(|x| {
                AstNode::call_method(
                    Ident::new_no_span("abi_encode".into()),
                    vec![
                        Expression::subfield(
                            Expression::ambiguous_variable_expression(Ident::new_no_span(
                                "self".into(),
                            )),
                            x.name.clone(),
                        ),
                        Expression::ambiguous_variable_expression(Ident::new_no_span(
                            "buffer".into(),
                        )),
                    ],
                )
            })
            .collect();

        let abi_decode_contents = vec![AstNode::return_node(Expression {
            kind: ExpressionKind::Struct(Box::new(StructExpression {
                call_path_binding: TypeBinding {
                    inner: CallPath {
                        prefixes: vec![],
                        suffix: Ident::new_no_span("Self".into()),
                        is_absolute: false,
                    },
                    type_arguments: TypeArgs::Regular(vec![]),
                    span: Span::dummy(),
                },
                fields: struct_decl
                    .fields
                    .iter()
                    .map(|x| StructExpressionField {
                        name: x.name.clone(),
                        value: Self::call_abi_decode(engines, x.type_argument.type_id),
                    })
                    .collect(),
            })),
            span: Span::dummy(),
        })];

        (
            impl_encode
                .then(|| {
                    self.auto_impl_abi_encode(
                        &struct_decl.type_parameters,
                        struct_decl.call_path.suffix.clone(),
                        unit_type_id,
                        engines,
                        abi_encode_contents,
                    )
                })
                .flatten(),
            impl_decode
                .then(|| {
                    self.auto_impl_abi_decode(
                        &struct_decl.type_parameters,
                        struct_decl.call_path.suffix.clone(),
                        unit_type_id,
                        engines,
                        abi_decode_contents,
                    )
                })
                .flatten(),
        )
    }

    /// Verify if am enum has all variants that can be implement AbiEncode and AbiDecode.
    fn can_auto_impl_enum(&mut self, decl: &ty::TyDecl) -> (bool, bool) {
        let handler = Handler::default();
        let Ok(enum_decl) = decl
            .to_enum_ref(&handler, self.ctx.engines())
            .map(|enum_ref| self.ctx.engines().de().get(enum_ref.id()))
        else {
            return (false, false);
        };

        let all_variants_are_abi_encode = enum_decl.variants.iter().all(|variant| {
            // If the variant is the generic argument of the enum, we are ok
            // because we will constraint it later
            if self
                .ctx
                .engines()
                .te()
                .get(variant.type_argument.type_id)
                .is_unknown_generic()
            {
                return true;
            }

            self.ctx.check_type_impls_traits(
                variant.type_argument.type_id,
                &[TraitConstraint {
                    trait_name: self.abi_encode_call_path.clone(),
                    type_arguments: vec![],
                }],
            )
        });

        let all_variants_are_abi_decode = enum_decl.variants.iter().all(|variant| {
            // If the variant is the generic argument of the enum, we are ok
            // because we will constraint it later
            if self
                .ctx
                .engines()
                .te()
                .get(variant.type_argument.type_id)
                .is_unknown_generic()
            {
                return true;
            }

            self.ctx.check_type_impls_traits(
                variant.type_argument.type_id,
                &[TraitConstraint {
                    trait_name: self.abi_decode_call_path.clone(),
                    type_arguments: vec![],
                }],
            )
        });

        (all_variants_are_abi_encode, all_variants_are_abi_decode)
    }

    fn call_abi_decode(engines: &Engines, type_id: TypeId) -> Expression {
        let ty = engines.te().get(type_id);
        let name = Ident::new_no_span("".into());
        Expression::call_associated_function(
            (TypeInfo::clone(ty.deref()), name),
            Ident::new_no_span("abi_decode".into()),
            vec![Expression::ambiguous_variable_expression(
                Ident::new_no_span("buffer".into()),
            )],
        )
    }

    fn call_abi_decode_with_type_info(ty: TypeInfo, name: BaseIdent) -> Expression {
        Expression::call_associated_function(
            (ty, name),
            Ident::new_no_span("abi_decode".into()),
            vec![Expression::ambiguous_variable_expression(
                Ident::new_no_span("buffer".into()),
            )],
        )
    }

    // Auto implements AbiEncode and AbiDecode for enums and returns their `AstNode`
    fn auto_impl_enum(
        &mut self,
        engines: &Engines,
        decl: &TyDecl,
    ) -> (Option<TyAstNode>, Option<TyAstNode>) {
        let (impl_encode, impl_decode) = self.can_auto_impl_enum(decl);
        if !impl_encode && !impl_decode {
            return (None, None);
        }

        let unit_type_id =
            self.ctx
                .engines
                .te()
                .insert(self.ctx.engines, TypeInfo::Tuple(vec![]), None);

        let enum_decl_ref = decl.get_enum_decl_ref().unwrap();
        let enum_decl = self.ctx.engines().de().get(enum_decl_ref.id());

        if !self.import_core_codec() {
            return (None, None);
        }

        let abi_encode_contents = vec![
            AstNode {
                content: AstNodeContent::Expression(
                    Expression {
                        kind: ExpressionKind::Match(
                            MatchExpression {
                                value: Box::new(Expression {
                                    kind: ExpressionKind::AmbiguousVariableExpression (
                                        Ident::new_no_span("self".into())
                                    ),
                                    span: Span::dummy()
                                }),
                                branches: enum_decl.variants.iter()
                                    .enumerate()
                                    .map(|(i, x)| {
                                        let variant_type = self.ctx.engines().te().get(x.type_argument.type_id);
                                        MatchBranch {
                                            scrutinee: Scrutinee::EnumScrutinee {
                                                call_path: CallPath {
                                                    prefixes: vec![
                                                        Ident::new_no_span("Self".into())
                                                    ],
                                                    suffix: Ident::new_no_span(
                                                        x.name.as_str().into()
                                                    ),
                                                    is_absolute: false
                                                },
                                                value: Box::new(if variant_type.is_unit() {
                                                    Scrutinee::CatchAll {
                                                        span: Span::dummy()
                                                    }
                                                } else {
                                                    Scrutinee::Variable {
                                                        name: Ident::new_no_span("x".into()),
                                                        span: Span::dummy()
                                                    }
                                                }),
                                                span: Span::dummy(),
                                            },
                                            result: Expression {
                                                kind: ExpressionKind::CodeBlock(
                                                    CodeBlock {
                                                        contents: {
                                                            let mut contents = vec![];

                                                            // discriminant
                                                            contents.push(
                                                                AstNode {
                                                                    content: AstNodeContent::Expression(
                                                                        Expression {
                                                                            kind: ExpressionKind::MethodApplication(
                                                                                Box::new(MethodApplicationExpression {
                                                                                    method_name_binding: TypeBinding {
                                                                                        inner: MethodName::FromModule {
                                                                                            method_name: Ident::new_no_span("abi_encode".into())
                                                                                        },
                                                                                        type_arguments: TypeArgs::Regular(vec![]),
                                                                                        span: Span::dummy()
                                                                                    },
                                                                                    arguments: vec![
                                                                                        Expression {
                                                                                            kind: ExpressionKind::Literal(
                                                                                                crate::language::Literal::U64(
                                                                                                    i as u64
                                                                                                )
                                                                                            ),
                                                                                            span: Span::dummy()
                                                                                        },
                                                                                        Expression {
                                                                                            kind: ExpressionKind::AmbiguousVariableExpression(
                                                                                                Ident::new_no_span("buffer".into())
                                                                                            ),
                                                                                            span: Span::dummy()
                                                                                        }
                                                                                    ],
                                                                                    contract_call_params: vec![],
                                                                                })
                                                                            ),
                                                                            span: Span::dummy()
                                                                        }
                                                                    ),
                                                                    span: Span::dummy()
                                                            });

                                                            // variant data
                                                            if !variant_type.is_unit() {
                                                                contents.push(
                                                                    AstNode {
                                                                        content: AstNodeContent::Expression(
                                                                            Expression {
                                                                                kind: ExpressionKind::MethodApplication(
                                                                                    Box::new(MethodApplicationExpression {
                                                                                        method_name_binding: TypeBinding {
                                                                                            inner: MethodName::FromModule {
                                                                                                method_name: Ident::new_no_span("abi_encode".into())
                                                                                            },
                                                                                            type_arguments: TypeArgs::Regular(vec![]),
                                                                                            span: Span::dummy()
                                                                                        },
                                                                                        arguments: vec![
                                                                                            Expression {
                                                                                                kind: ExpressionKind::AmbiguousVariableExpression (
                                                                                                    Ident::new_no_span("x".into())
                                                                                                ),
                                                                                                span: Span::dummy()
                                                                                            },
                                                                                            Expression {
                                                                                                kind: ExpressionKind::AmbiguousVariableExpression(
                                                                                                    Ident::new_no_span("buffer".into())
                                                                                                ),
                                                                                                span: Span::dummy()
                                                                                            }
                                                                                        ],
                                                                                        contract_call_params: vec![],
                                                                                    })
                                                                                ),
                                                                                span: Span::dummy()
                                                                            }
                                                                        ),
                                                                        span: Span::dummy()
                                                                    }
                                                                );
                                                            }

                                                            contents
                                                        },
                                                        whole_block_span: Span::dummy()
                                                    }
                                                ),
                                                span: Span::dummy()
                                            },
                                            span: Span::dummy()
                                        }
                                    }).collect()
                            }
                        ),
                        span: Span::dummy()
                    }
                ),
                span: Span::dummy()
            }
        ];

        let decode_result = Ident::new_no_span("variant".into());
        let abi_decode_contents = vec![
            AstNode::variable_declaration(
                engines,
                decode_result.clone(),
                Self::call_abi_decode_with_type_info(
                    TypeInfo::UnsignedInteger(IntegerBits::SixtyFour),
                    Ident::new_no_span("u64".into()),
                ),
                false,
            ),
            AstNode::return_node(Expression::match_branch(
                Expression::ambiguous_variable_expression(decode_result),
                enum_decl
                    .variants
                    .iter()
                    .enumerate()
                    .map(|(idx, variant)| {
                        MatchBranch::literal(
                            Literal::U64(idx as u64),
                            if engines.te().get(variant.type_argument.type_id).is_unit() {
                                Expression {
                                    kind: ExpressionKind::DelineatedPath(Box::new(
                                        DelineatedPathExpression {
                                            call_path_binding: TypeBinding {
                                                inner: QualifiedCallPath {
                                                    call_path: CallPath {
                                                        prefixes: vec![Ident::new_no_span(
                                                            "Self".into(),
                                                        )],
                                                        suffix: variant.name.clone(),
                                                        is_absolute: false,
                                                    },
                                                    qualified_path_root: None,
                                                },
                                                type_arguments: TypeArgs::Regular(vec![]),
                                                span: Span::dummy(),
                                            },
                                            args: None,
                                        },
                                    )),
                                    span: Span::dummy(),
                                }
                            } else {
                                Expression {
                                    kind: ExpressionKind::AmbiguousPathExpression(Box::new(
                                        AmbiguousPathExpression {
                                            qualified_path_root: None,
                                            call_path_binding: TypeBinding {
                                                inner: CallPath {
                                                    prefixes: vec![],
                                                    suffix: AmbiguousSuffix {
                                                        before: Some(TypeBinding {
                                                            inner: Ident::new_no_span(
                                                                "Self".into(),
                                                            ),
                                                            type_arguments: TypeArgs::Regular(
                                                                vec![],
                                                            ),
                                                            span: Span::dummy(),
                                                        }),
                                                        suffix: variant.name.clone(),
                                                    },
                                                    is_absolute: false,
                                                },
                                                type_arguments: TypeArgs::Regular(vec![]),
                                                span: Span::dummy(),
                                            },
                                            args: vec![Self::call_abi_decode(
                                                engines,
                                                variant.type_argument.type_id,
                                            )],
                                        },
                                    )),
                                    span: Span::dummy(),
                                }
                            },
                        )
                    })
                    .chain([MatchBranch::catch_all(Expression::revert_u64(0))])
                    .collect(),
            )),
        ];

        (
            impl_encode
                .then(|| {
                    self.auto_impl_abi_encode(
                        &enum_decl.type_parameters,
                        enum_decl.call_path.suffix.clone(),
                        unit_type_id,
                        engines,
                        abi_encode_contents,
                    )
                })
                .flatten(),
            impl_decode
                .then(|| {
                    self.auto_impl_abi_decode(
                        &enum_decl.type_parameters,
                        enum_decl.call_path.suffix.clone(),
                        unit_type_id,
                        engines,
                        abi_decode_contents,
                    )
                })
                .flatten(),
        )
    }

    pub fn generate(
        &mut self,
        engines: &Engines,
        decl: &ty::TyDecl,
    ) -> (Option<TyAstNode>, Option<TyAstNode>) {
        match decl {
            TyDecl::StructDecl(_) => self.auto_impl_struct(engines, decl),
            TyDecl::EnumDecl(_) => self.auto_impl_enum(engines, decl),
            _ => (None, None),
        }
    }
}
