use crate::{
    decl_engine::{parsed_engine::ParsedDeclEngineInsert, DeclEngineGet},
    language::{
        parsed::{
            AstNode, AstNodeContent, CodeBlock, Declaration, Expression, ExpressionKind,
            FunctionApplicationExpression, FunctionDeclarationKind, IfExpression,
            IntrinsicFunctionExpression, MethodApplicationExpression, MethodName, ParseProgram,
            TreeType, TupleIndexExpression, VariableDeclaration,
        },
        ty::{self, TyAstNode, TyFunctionDecl, TyModule, TyProgram},
        CallPath, Literal, Purity,
    },
    metadata::MetadataManager,
    semantic_analysis::{
        namespace::{self, Namespace},
        TypeCheckContext,
    },
    transform::AttributesMap,
    BuildConfig, Engines, TypeArgs, TypeArgument, TypeBinding, TypeId, TypeInfo,
};
use sway_ast::Intrinsic;
use sway_error::handler::{ErrorEmitted, Handler};
use sway_ir::{Context, Module};
use sway_types::{BaseIdent, Ident, Span, Spanned};

use super::{
    TypeCheckAnalysis, TypeCheckAnalysisContext, TypeCheckFinalization,
    TypeCheckFinalizationContext,
};

fn call_encode(_engines: &Engines, arg: Expression) -> Expression {
    Expression {
        kind: ExpressionKind::FunctionApplication(Box::new(FunctionApplicationExpression {
            call_path_binding: TypeBinding {
                inner: CallPath {
                    prefixes: vec![],
                    suffix: Ident::new_no_span("encode".into()),
                    is_absolute: false,
                },
                type_arguments: TypeArgs::Regular(vec![]),
                span: Span::dummy(),
            },
            arguments: vec![arg],
        })),
        span: Span::dummy(),
    }
}

fn call_decode_first_param(engines: &Engines) -> Expression {
    let string_slice_type_id = engines.te().insert(engines, TypeInfo::StringSlice, None);
    Expression {
        kind: ExpressionKind::FunctionApplication(Box::new(FunctionApplicationExpression {
            call_path_binding: TypeBinding {
                inner: CallPath {
                    prefixes: vec![],
                    suffix: Ident::new_no_span("decode_first_param".into()),
                    is_absolute: false,
                },
                type_arguments: TypeArgs::Regular(vec![TypeArgument {
                    type_id: string_slice_type_id,
                    initial_type_id: string_slice_type_id,
                    span: Span::dummy(),
                    call_path_tree: None,
                }]),
                span: Span::dummy(),
            },
            arguments: vec![],
        })),
        span: Span::dummy(),
    }
}

fn call_decode_second_param(_engines: &Engines, args_type: TypeArgument) -> Expression {
    Expression {
        kind: ExpressionKind::FunctionApplication(Box::new(FunctionApplicationExpression {
            call_path_binding: TypeBinding {
                inner: CallPath {
                    prefixes: vec![],
                    suffix: Ident::new_no_span("decode_second_param".into()),
                    is_absolute: false,
                },
                type_arguments: TypeArgs::Regular(vec![args_type]),
                span: Span::dummy(),
            },
            arguments: vec![],
        })),
        span: Span::dummy(),
    }
}

fn call_eq(_engines: &Engines, l: Expression, r: Expression) -> Expression {
    Expression {
        kind: ExpressionKind::MethodApplication(Box::new(MethodApplicationExpression {
            method_name_binding: TypeBinding {
                inner: MethodName::FromModule {
                    method_name: Ident::new_no_span("eq".to_string()),
                },
                type_arguments: TypeArgs::Regular(vec![]),
                span: Span::dummy(),
            },
            contract_call_params: vec![],
            arguments: vec![l, r],
        })),
        span: Span::dummy(),
    }
}

fn call_fn(expr: Expression, name: &str) -> Expression {
    Expression {
        kind: ExpressionKind::MethodApplication(Box::new(MethodApplicationExpression {
            method_name_binding: TypeBinding {
                inner: MethodName::FromModule {
                    method_name: Ident::new_no_span(name.to_string()),
                },
                type_arguments: TypeArgs::Regular(vec![]),
                span: Span::dummy(),
            },
            contract_call_params: vec![],
            arguments: vec![expr],
        })),
        span: Span::dummy(),
    }
}

fn arguments_type(engines: &Engines, decl: &TyFunctionDecl) -> Option<TypeArgument> {
    if decl.parameters.is_empty() {
        return None;
    }

    // if decl.parameters.len() == 1 {
    //     return Some(decl.parameters[0].type_argument.clone());
    // }

    let types = decl
        .parameters
        .iter()
        .map(|p| {
            let arg_t = engines.te().get(p.type_argument.type_id);
            let arg_t = match &*arg_t {
                TypeInfo::Unknown => todo!(),
                TypeInfo::UnknownGeneric { .. } => todo!(),
                TypeInfo::Placeholder(_) => todo!(),
                TypeInfo::TypeParam(_) => todo!(),
                TypeInfo::StringSlice => todo!(),
                TypeInfo::StringArray(_) => todo!(),
                TypeInfo::UnsignedInteger(v) => TypeInfo::UnsignedInteger(*v),
                TypeInfo::Enum(_) => todo!(),
                TypeInfo::Struct(s) => TypeInfo::Struct(s.clone()),
                TypeInfo::Boolean => todo!(),
                TypeInfo::Tuple(_) => todo!(),
                TypeInfo::ContractCaller { .. } => todo!(),
                TypeInfo::Custom { .. } => todo!(),
                TypeInfo::B256 => TypeInfo::B256,
                TypeInfo::Numeric => todo!(),
                TypeInfo::Contract => todo!(),
                TypeInfo::ErrorRecovery(_) => todo!(),
                TypeInfo::Array(_, _) => todo!(),
                TypeInfo::Storage { .. } => todo!(),
                TypeInfo::RawUntypedPtr => todo!(),
                TypeInfo::RawUntypedSlice => todo!(),
                TypeInfo::Ptr(_) => todo!(),
                TypeInfo::Slice(_) => todo!(),
                TypeInfo::Alias { .. } => todo!(),
                TypeInfo::TraitType { .. } => todo!(),
                TypeInfo::Ref(_) => todo!(),
            };
            let tid = engines.te().insert(engines, arg_t, None);
            TypeArgument {
                type_id: tid,
                initial_type_id: tid,
                span: Span::dummy(),
                call_path_tree: None,
            }
        })
        .collect();
    let type_id = engines.te().insert(engines, TypeInfo::Tuple(types), None);
    Some(TypeArgument {
        type_id,
        initial_type_id: type_id,
        span: Span::dummy(),
        call_path_tree: None,
    })
}

fn arguments_as_expressions(name: BaseIdent, decl: &TyFunctionDecl) -> Vec<Expression> {
    decl.parameters
        .iter()
        .enumerate()
        .map(|(idx, _)| Expression {
            kind: ExpressionKind::TupleIndex(TupleIndexExpression {
                prefix: Box::new(Expression {
                    kind: ExpressionKind::AmbiguousVariableExpression(name.clone()),
                    span: Span::dummy(),
                }),
                index: idx,
                index_span: Span::dummy(),
            }),
            span: Span::dummy(),
        })
        .collect()
}

fn gen_entry_fn(
    ctx: &mut TypeCheckContext,
    root: &mut TyModule,
    purity: Purity,
    contents: Vec<AstNode>,
    unit_type_id: TypeId,
) -> Result<(), ErrorEmitted> {
    let entry_fn_decl = crate::language::parsed::function::FunctionDeclaration {
        purity,
        attributes: AttributesMap::default(),
        name: Ident::new_no_span("__entry".to_string()),
        visibility: crate::language::Visibility::Public,
        body: CodeBlock {
            contents,
            whole_block_span: Span::dummy(),
        },
        parameters: vec![],
        span: Span::dummy(),
        return_type: TypeArgument {
            type_id: unit_type_id,
            initial_type_id: unit_type_id,
            span: Span::dummy(),
            call_path_tree: None,
        },
        type_parameters: vec![],
        where_clause: vec![],
        kind: FunctionDeclarationKind::Entry,
    };
    let entry_fn_decl = ctx.engines.pe().insert(entry_fn_decl);

    let handler = Handler::default();
    root.all_nodes.push(TyAstNode::type_check(
        &handler,
        ctx.by_ref(),
        AstNode {
            content: AstNodeContent::Declaration(Declaration::FunctionDeclaration(entry_fn_decl)),
            span: Span::dummy(),
        },
    )?);

    assert!(!handler.has_errors(), "{:?}", handler);
    assert!(!handler.has_warnings(), "{:?}", handler);

    Ok(())
}

impl TyProgram {
    /// Type-check the given parsed program to produce a typed program.
    ///
    /// The given `initial_namespace` acts as an initial state for each module within this program.
    /// It should contain a submodule for each library package dependency.
    pub fn type_check(
        handler: &Handler,
        engines: &Engines,
        parsed: &ParseProgram,
        initial_namespace: namespace::Module,
        package_name: &str,
        build_config: Option<&BuildConfig>,
    ) -> Result<Self, ErrorEmitted> {
        let mut namespace = Namespace::init_root(initial_namespace);
        let mut ctx = TypeCheckContext::from_root(&mut namespace, engines)
            .with_kind(parsed.kind)
            .with_experimental_flags(build_config.map(|x| x.experimental));

        let ParseProgram { root, kind } = parsed;

        // Analyze the dependency order for the submodules.
        let modules_dep_graph = ty::TyModule::analyze(handler, root)?;
        let module_eval_order: Vec<sway_types::BaseIdent> =
            modules_dep_graph.compute_order(handler)?;

        let mut root = ty::TyModule::type_check(handler, ctx.by_ref(), root, module_eval_order)?;

        if ctx.experimental.new_encoding {
            let main_decl = root
                .all_nodes
                .iter_mut()
                .find_map(|x| match &mut x.content {
                    ty::TyAstNodeContent::Declaration(ty::TyDecl::FunctionDecl(decl)) => {
                        (decl.name.as_str() == "main").then(|| engines.de().get(&decl.decl_id))
                    }
                    _ => None,
                });

            let unit_type_id = engines.te().insert(engines, TypeInfo::Tuple(vec![]), None);
            let string_slice_type_id = engines.te().insert(engines, TypeInfo::StringSlice, None);

            match &parsed.kind {
                TreeType::Predicate => {}
                TreeType::Script => {
                    let main_decl = main_decl.unwrap();
                    let result_name = Ident::new_no_span("result".into());

                    let mut contents = vec![];
                    let arguments = AstNode::push_decode_script_data_as_fn_args(
                        engines,
                        &mut contents,
                        result_name.clone(),
                        &main_decl,
                    );
                    AstNode::push_encode_and_return(
                        engines,
                        &mut contents,
                        result_name,
                        Expression::call_function_with_suffix(
                            Ident::new_no_span("main".into()),
                            arguments,
                        ),
                    );

                    gen_entry_fn(&mut ctx, &mut root, Purity::Pure, contents, unit_type_id)?;
                }
                TreeType::Contract => {
                    // let main_decl = main_decl.unwrap();
                    let var_decl = ctx.engines.pe().insert(VariableDeclaration {
                        name: Ident::new_no_span("method_name".to_string()),
                        type_ascription: TypeArgument {
                            type_id: string_slice_type_id,
                            initial_type_id: string_slice_type_id,
                            span: Span::dummy(),
                            call_path_tree: None,
                        },
                        body: call_decode_first_param(engines),
                        is_mutable: false,
                    });
                    let mut contents = vec![AstNode {
                        content: AstNodeContent::Declaration(Declaration::VariableDeclaration(
                            var_decl,
                        )),
                        span: Span::dummy(),
                    }];

                    let method_name_var_ref = Expression {
                        kind: ExpressionKind::Variable(Ident::new_no_span(
                            "method_name".to_string(),
                        )),
                        span: Span::dummy(),
                    };

                    fn import_core_ops(ctx: &mut TypeCheckContext<'_>) -> bool {
                        // Check if the compilation context has acces to the
                        // core library.
                        let handler = Handler::default();
                        let _ = ctx.star_import(
                            &handler,
                            &[
                                Ident::new_no_span("core".into()),
                                Ident::new_no_span("ops".into()),
                            ],
                            true,
                        );

                        !handler.has_errors()
                    }

                    assert!(import_core_ops(&mut ctx));

                    let all_entries: Vec<_> = root
                        .submodules_recursive()
                        .flat_map(|(_, submod)| submod.module.contract_fns(engines))
                        .chain(root.contract_fns(engines))
                        .collect();
                    for r in all_entries {
                        let decl = engines.de().get(r.id());
                        let args_type = arguments_type(engines, &decl);
                        //let result_type = decl.return_type.clone();
                        let args_tuple_name = Ident::new_no_span("args".to_string());
                        let result_name = Ident::new_no_span("result".to_string());

                        let slice = engines
                            .te()
                            .insert(engines, TypeInfo::RawUntypedSlice, None);
                        let slice = TypeArgument {
                            type_id: slice,
                            initial_type_id: slice,
                            span: Span::dummy(),
                            call_path_tree: None,
                        };

                        contents.push(AstNode {
                        content: AstNodeContent::Expression(Expression {
                            kind: ExpressionKind::If(IfExpression {
                                // call eq
                                condition: Box::new(call_eq(
                                    engines,
                                    method_name_var_ref.clone(),
                                    Expression {
                                        kind: ExpressionKind::Literal(Literal::String(
                                            decl.name.span(),
                                        )),
                                        span: Span::dummy(),
                                    },
                                )),
                                then: Box::new(
                                    Expression::code_block({
                                        let mut nodes = vec![];
                                        let arguments = if let Some(args_type) = args_type {
                                            // decode parameters
                                            nodes.push(AstNode::typed_variable_declaration(
                                                engines,
                                                args_tuple_name.clone(),
                                                args_type.clone(),
                                                call_decode_second_param(engines, args_type),
                                                false
                                            ));
                                            arguments_as_expressions(args_tuple_name.clone(), &decl)
                                        } else {
                                            vec![]
                                        };

                                        // call the contract method
                                        nodes.push(AstNode::typed_variable_declaration(
                                            engines,
                                            result_name.clone(),
                                            slice,
                                            call_encode(engines, Expression {
                                                kind: ExpressionKind::FunctionApplication(
                                                    Box::new(
                                                        FunctionApplicationExpression {
                                                            call_path_binding: TypeBinding {
                                                                inner: CallPath {
                                                                    prefixes: vec![],
                                                                    suffix: Ident::new_no_span(format!("__contract_entry_{}", decl.call_path.suffix.clone())),
                                                                    is_absolute: false
                                                                },
                                                                type_arguments: TypeArgs::Regular(vec![]),
                                                                span: Span::dummy(),
                                                            },
                                                            arguments
                                                        }
                                                    )
                                                ),
                                                span: Span::dummy(),
                                            }),
                                            false
                                        ));

                                        // return the encoded contract result
                                        nodes.push(AstNode {
                                            content: AstNodeContent::Expression(Expression {
                                                kind: ExpressionKind::IntrinsicFunction(IntrinsicFunctionExpression {
                                                    name: Ident::new_no_span("__contract_ret".to_string()), 
                                                    kind_binding: TypeBinding {
                                                        inner: Intrinsic::ContractRet,
                                                        type_arguments: TypeArgs::Regular(vec![]),
                                                        span: Span::dummy()
                                                    },
                                                    arguments: vec![
                                                        call_fn(Expression {
                                                            kind: ExpressionKind::AmbiguousVariableExpression(result_name.clone()),
                                                            span: Span::dummy()
                                                        }, "ptr"),
                                                        call_fn(Expression {
                                                            kind: ExpressionKind::AmbiguousVariableExpression(result_name.clone()),
                                                            span: Span::dummy()
                                                        }, "number_of_bytes"),
                                                    ]
                                                }),
                                                span: Span::dummy(),
                                            }),
                                            span: Span::dummy()
                                        });

                                        nodes
                                    })
                                ),
                                r#else: None,
                            }),
                            span: Span::dummy(),
                        }),
                        span: Span::dummy(),
                    });
                    }

                    gen_entry_fn(
                        &mut ctx,
                        &mut root,
                        Purity::ReadsWrites,
                        contents,
                        unit_type_id,
                    )?;
                }
                TreeType::Library => {}
            }
        }

        let (kind, declarations, configurables) =
            Self::validate_root(handler, engines, &root, *kind, package_name)?;

        let program = TyProgram {
            kind,
            root,
            declarations,
            configurables,
            storage_slots: vec![],
            logged_types: vec![],
            messages_types: vec![],
        };

        Ok(program)
    }

    pub(crate) fn get_typed_program_with_initialized_storage_slots(
        self,
        handler: &Handler,
        engines: &Engines,
        context: &mut Context,
        md_mgr: &mut MetadataManager,
        module: Module,
    ) -> Result<Self, ErrorEmitted> {
        let decl_engine = engines.de();
        match &self.kind {
            ty::TyProgramKind::Contract { .. } => {
                let storage_decl = self
                    .declarations
                    .iter()
                    .find(|decl| matches!(decl, ty::TyDecl::StorageDecl { .. }));

                // Expecting at most a single storage declaration
                match storage_decl {
                    Some(ty::TyDecl::StorageDecl(ty::StorageDecl {
                        decl_id,
                        decl_span: _,
                        ..
                    })) => {
                        let decl = decl_engine.get_storage(decl_id);
                        let mut storage_slots = decl.get_initialized_storage_slots(
                            handler, engines, context, md_mgr, module,
                        )?;
                        // Sort the slots to standardize the output. Not strictly required by the
                        // spec.
                        storage_slots.sort();
                        Ok(Self {
                            storage_slots,
                            ..self
                        })
                    }
                    _ => Ok(Self {
                        storage_slots: vec![],
                        ..self
                    }),
                }
            }
            _ => Ok(Self {
                storage_slots: vec![],
                ..self
            }),
        }
    }
}

impl TypeCheckAnalysis for TyProgram {
    fn type_check_analyze(
        &self,
        handler: &Handler,
        ctx: &mut TypeCheckAnalysisContext,
    ) -> Result<(), ErrorEmitted> {
        for node in self.root.all_nodes.iter() {
            node.type_check_analyze(handler, ctx)?;
        }
        Ok(())
    }
}

impl TypeCheckFinalization for TyProgram {
    fn type_check_finalize(
        &mut self,
        handler: &Handler,
        ctx: &mut TypeCheckFinalizationContext,
    ) -> Result<(), ErrorEmitted> {
        handler.scope(|handler| {
            for node in self.root.all_nodes.iter_mut() {
                let _ = node.type_check_finalize(handler, ctx);
            }
            Ok(())
        })
    }
}
