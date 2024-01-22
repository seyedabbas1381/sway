use crate::{
    language::{
        parsed::{
            AsmExpression, AsmRegisterDeclaration, AstNode, AstNodeContent, CodeBlock, Declaration,
            Expression, ExpressionKind, FunctionApplicationExpression, FunctionDeclaration,
            IfExpression, IntrinsicFunctionExpression, MatchBranch, MatchExpression, ParseProgram,
            Scrutinee, VariableDeclaration, MethodApplicationExpression, MethodName, SubfieldExpression, TupleIndexExpression,
        },
        ty::{self, TyAstNode, TyDecl, TyFunctionDecl, TyProgram},
        AsmOp, AsmRegister, CallPath, Literal, Purity,
    },
    metadata::MetadataManager,
    semantic_analysis::{
        namespace::{self, Namespace},
        TypeCheckContext,
    },
    transform::AttributesMap,
    BuildConfig, Engines, TypeArgs, TypeArgument, TypeBinding, TypeInfo, decl_engine::{self, DeclEngineGet},
};
use sway_ast::Intrinsic;
use sway_error::handler::{ErrorEmitted, Handler};
use sway_ir::{Context, Module};
use sway_types::{integer_bits::IntegerBits, Ident, Span, Spanned, BaseIdent};

use super::{
    TypeCheckAnalysis, TypeCheckAnalysisContext, TypeCheckFinalization,
    TypeCheckFinalizationContext,
};

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
        let ctx = TypeCheckContext::from_root(&mut namespace, engines)
            .with_kind(parsed.kind.clone())
            .with_experimental_flags(build_config.map(|x| x.experimental));

        let ParseProgram { root, kind } = parsed;

        // Analyze the dependency order for the submodules.
        let modules_dep_graph = ty::TyModule::analyze(handler, root)?;
        let module_eval_order: Vec<sway_types::BaseIdent> = modules_dep_graph.compute_order(handler)?;

        let mut root = ty::TyModule::type_check(handler, ctx.by_ref(), root, module_eval_order)?;

        if matches!(&parsed.kind, crate::language::parsed::TreeType::Contract) {
            fn call_decode_first_param(engines: &Engines) -> Expression {
                let string_slice_type_id =
                    engines.te().insert(engines, TypeInfo::StringSlice, None);
                Expression {
                    kind: ExpressionKind::FunctionApplication(Box::new(
                        FunctionApplicationExpression {
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
                        },
                    )),
                    span: Span::dummy(),
                }
            }

            fn call_decode_second_param(engines: &Engines, args_type: TypeArgument) -> Expression {
                Expression {
                    kind: ExpressionKind::FunctionApplication(Box::new(
                        FunctionApplicationExpression {
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
                        },
                    )),
                    span: Span::dummy(),
                }
            }

            fn call_eq(engines: &Engines, l: Expression, r: Expression) -> Expression {
                let string_slice_type_id = engines.te().insert(engines, TypeInfo::Boolean, None);
                Expression {
                    kind: ExpressionKind::MethodApplication(
                        Box::new(
                            MethodApplicationExpression {
                                method_name_binding: TypeBinding { 
                                    inner: MethodName::FromModule { 
                                        method_name: Ident::new_no_span("eq".to_string())
                                    }, 
                                    type_arguments: TypeArgs::Regular(vec![]), 
                                    span: Span::dummy()
                                },
                                contract_call_params: vec![],
                                arguments: vec![l, r]
                            }
                        )
                    ),
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

                let types = decl.parameters.iter().map(|p| {
                    let arg_t = engines.te().get(p.type_argument.type_id);
                    let arg_t = match &*arg_t {
                        TypeInfo::Unknown => todo!(),
                        TypeInfo::UnknownGeneric { name, trait_constraints } => todo!(),
                        TypeInfo::Placeholder(_) => todo!(),
                        TypeInfo::TypeParam(_) => todo!(),
                        TypeInfo::StringSlice => todo!(),
                        TypeInfo::StringArray(_) => todo!(),
                        TypeInfo::UnsignedInteger(v) => TypeInfo::UnsignedInteger(*v),
                        TypeInfo::Enum(_) => todo!(),
                        TypeInfo::Struct(s) => TypeInfo::Struct(s.clone()),
                        TypeInfo::Boolean => todo!(),
                        TypeInfo::Tuple(_) => todo!(),
                        TypeInfo::ContractCaller { abi_name, address } => todo!(),
                        TypeInfo::Custom { qualified_call_path, type_arguments, root_type_id } => todo!(),
                        TypeInfo::B256 => TypeInfo::B256,
                        TypeInfo::Numeric => todo!(),
                        TypeInfo::Contract => todo!(),
                        TypeInfo::ErrorRecovery(_) => todo!(),
                        TypeInfo::Array(_, _) => todo!(),
                        TypeInfo::Storage { fields } => todo!(),
                        TypeInfo::RawUntypedPtr => todo!(),
                        TypeInfo::RawUntypedSlice => todo!(),
                        TypeInfo::Ptr(_) => todo!(),
                        TypeInfo::Slice(_) => todo!(),
                        TypeInfo::Alias { name, ty } => todo!(),
                        TypeInfo::TraitType { name, trait_type_id } => todo!(),
                        TypeInfo::Ref(_) => todo!(),
                    };
                    let tid = engines.te().insert(engines, arg_t, None);
                    TypeArgument {
                        type_id: tid,
                        initial_type_id: tid,
                        span: Span::dummy(),
                        call_path_tree: None,
                    }
                }).collect();
                let type_id = engines.te().insert(engines, TypeInfo::Tuple(types), None);
                Some(TypeArgument { 
                    type_id: type_id.clone(), 
                    initial_type_id: type_id, 
                    span: Span::dummy(), 
                    call_path_tree: None
                })
            }

            fn arguments_as_expressions(name: BaseIdent, decl: &TyFunctionDecl) -> Vec<Expression> {
                decl.parameters.iter().enumerate().map(|(idx, p)| {
                    Expression {
                        kind: ExpressionKind::TupleIndex(TupleIndexExpression {
                            prefix: Box::new(Expression {
                                kind: ExpressionKind::AmbiguousVariableExpression(name.clone()),
                                span: Span::dummy(),
                            }),
                            index: idx,
                            index_span: Span::dummy(),
                        }),
                        span: Span::dummy(),
                    }
                }).collect()
            }

            let unit_type_id = engines.te().insert(engines, TypeInfo::Tuple(vec![]), None);
            let string_slice_type_id = engines.te().insert(engines, TypeInfo::StringSlice, None);

            let mut contents = vec![AstNode {
                content: AstNodeContent::Declaration(Declaration::VariableDeclaration(
                    VariableDeclaration {
                        name: Ident::new_no_span("method_name".to_string()),
                        type_ascription: TypeArgument {
                            type_id: string_slice_type_id,
                            initial_type_id: string_slice_type_id,
                            span: Span::dummy(),
                            call_path_tree: None,
                        },
                        body: call_decode_first_param(engines),
                        is_mutable: false,
                    },
                )),
                span: Span::dummy(),
            }];

            let method_name_var_ref = Expression {
                kind: ExpressionKind::Variable(Ident::new_no_span("method_name".to_string())),
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
                .flat_map(|(_, submod)| {
                    submod.module.contract_fns(engines)
                })
                .chain(root.contract_fns(engines))
                .collect();
            for r in all_entries {
                let decl = engines.de().get(r.id());
                let args_type = arguments_type(engines, &decl);
                let args_tuple_name = Ident::new_no_span("args".to_string());

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
                                    match args_type {
                                        Some(args_type) => {
                                            // decode parameters
                                            nodes.push(AstNode {
                                                content: AstNodeContent::Declaration(
                                                    Declaration::VariableDeclaration(VariableDeclaration { 
                                                        name: args_tuple_name.clone(), 
                                                        type_ascription: args_type.clone(), 
                                                        body: call_decode_second_param(engines, args_type), 
                                                        is_mutable: false
                                                    })
                                                ),
                                                span: Span::dummy()
                                            });
                                            // call the contract method
                                            nodes.push(AstNode {
                                                content: AstNodeContent::Expression(Expression {
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
                                                                    arguments: arguments_as_expressions(args_tuple_name.clone(), &decl)
                                                                }
                                                            )
                                                        ),
                                                        span: Span::dummy(),
                                                }),
                                                span: Span::dummy()
                                            });
                                        },
                                        None => {
                                             // call the contract method
                                             nodes.push(AstNode {
                                                content: AstNodeContent::Expression(Expression {
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
                                                                    arguments: vec![]
                                                                }
                                                            )
                                                        ),
                                                        span: Span::dummy(),
                                                }),
                                                span: Span::dummy()
                                            });
                                        },
                                    }

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

            let entry_fn_decl = crate::language::parsed::function::FunctionDeclaration {
                purity: Purity::ReadsWrites,
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
            };

            root.all_nodes.push(TyAstNode::type_check(
                handler,
                ctx,
                AstNode {
                    content: AstNodeContent::Declaration(Declaration::FunctionDeclaration(entry_fn_decl)),
                    span: Span::dummy(),
                },
            )?);
        }

        let (kind, declarations, configurables) =
            Self::validate_root(handler, engines, &root, kind.clone(), package_name)?;

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
