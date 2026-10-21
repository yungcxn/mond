# Trees

Every tree has a root kind, written `ast.Kind`. Kinds work as types (`ast.Identifier x`), as patterns (`ast.BinaryAdd(l, r)`), in tests (`e oftype ast.IfThen`), and as constructors (`ast.IntegerValue("7")`). Children are reached by position or by the field names below. List kinds take any number of children; text kinds take one `[]u8`.

Build a list node from a `[]ast` by spreading it into a quote: `quote { @..stmts; }`, `quote: f(@..args)`, `quote: [@..xs]`.

Most metaprogramming doesn't need this table: quotes, quote patterns and [views](metaprogramming.md#views) cover declarations, parameters, fields and cases. Use it to match or build expressions node by node.

## Shapes of declarations

| code | tree |
|---|---|
| `x = v` | `Assignment(assignee, assigned)` |
| `T x = v` | `AssignmentTyped(def_var: VariableDefinition(type, identifier), assigned)` |
| `fun f = (..) -> R: b` | `AssignmentTyped` whose type is `TypeFunction` and whose value is a `FunctionDefinition` |
| `mut` / `stc` / `pub` .. | a `Modifier*` around the declaration (views like `name` see through it) |
| `*(fields)` | `TypeDefinition`; its fields are the children of its `param_tuple` |
| `if c: a else: b` | `IfElse(if_then: IfThen(cond, then))` with the else part as the second child |

```mond
stcfun kind_of = (ast e) -> u32: ret match e {
    ast.Assignment => 1,
    ast.AssignmentTyped => 2,
    ast.ModifierMutable => 3,
    _ => 0,
};
stc u32 K1 = kind_of(quote: x = 1);          #= K1 1
stc u32 K2 = kind_of(quote: u32 x = 1);      #= K2 2
stc u32 K3 = kind_of(quote: mut u32 x = 1);  #= K3 3
stcfun rhs_text = (ast e) -> []u8: ret e.rhs.src;
stc []u8 R = rhs_text(quote: a + b * c);     #= R "b * c"
stcfun cond_text = (ast e) -> []u8: ret match e { ast.IfElse(ast.IfThen(c, _), _) => c.src, _ => "" };
stc []u8 C = cond_text(quote: if ready: 1 else: 2);   #= C "ready"
stcfun is_fun = (ast e) -> bool: ret match e {
    ast.AssignmentTyped(ast.VariableDefinition(ast.TypeFunction, _), ast.FunctionDefinition) => true,
    _ => false,
};
stc bool F = is_fun(quote: fun f = () -> u32: ret 1);   #= F true
```

## All kinds

The last column is the name `mond -b` prints in its tree dump.

| kind | written | children | dump name |
|---|---|---|---|
| `CodeBlock` | `{ a; b; }` | list | block |
| `FunctionDefinition` | `(params) -> R: body` | fun_header, unit | def_fun |
| `FunctionDeclaration` | `(params) -> R` (no body) | fun_header | def_fun_declaration |
| `FunctionDefinitionHeader` | `(params)` | param_tuple | partial__fun_def_header |
| `FunctionDefinitionHeaderReturning` | `(params) -> R` | param_tuple, return_type | partial__fun_def_header_ret |
| `FunctionDefinitionParameterTuple` | parameter list | list | partial__fun_def_param_tuple |
| `FunctionDefinitionParameter` | `T` | type | partial__fun_def_param |
| `FunctionDefinitionParameterNamed` | `T x` | param, identifier | partial__fun_def_param_named |
| `FunctionDefinitionParameterDefaulted` | `T x = d` | param, default_value | partial__fun_def_param_default |
| `FunctionDefinitionParameterWhere` | `T x where c` | param, where_predicate | partial__fun_def_param_where |
| `FunctionDefinitionParameterStaticWhere` | `T x stcwhere c` | param, where_predicate | partial__fun_def_param_stcwhere |
| `FunctionDefinitionParameterWhereElse` | `T x where c else v` | param, where_else_value | partial__fun_def_param_where_else |
| `Capture` | `(e)` | subnode | capture |
| `Array` | `[a, b]` | list | array |
| `ArrayEmpty` | `[]` | – | array_empty |
| `TypeOf` | `typeof e` | subnode | typeof |
| `SizeOf` | `sizeof e` | subnode | sizeof |
| `AlignOf` | `alignof e` | subnode | alignof |
| `LengthOf` | `lenof e` | subnode | lenof |
| `TagOf` | `tagof e` | subnode | tagof |
| `TypeArray` | `[N]T` | length, type | type_array |
| `TypeArrayUnlengthed` | `[]T` | type | type_array_unlengthed |
| `NegateNumerical` | `-e` | subnode | neg_num |
| `NegateLogical` | `!e` | subnode | neg_logic |
| `IncrementPrefix` | `++e` | subnode | inc_prefix |
| `DecrementPrefix` | `--e` | subnode | dec_prefix |
| `GenUpperboundIncl` | `..=b` | subnode | gen_upperbound_incl |
| `GenUpperboundExcl` | `..<b` | subnode | gen_upperbound_excl |
| `None` | nothing (an empty slot) | – | none |
| `Do` | `do e` | subnode | do |
| `Deinit` | `deinit e` | subnode | deinit |
| `Continue` | `cont` | – | cont |
| `Break` | `brk` | – | brk |
| `Return` | `ret e` | subnode | ret |
| `ReturnVoid` | `ret` | – | ret_void |
| `IfThen` | `if c: a` | cond, then | if_then |
| `IfElse` | `if c: a else: b` (the `else` part is the 2nd child) | if_then | if_else |
| `StaticIfThen` | `stcif c: a` | cond, then | stcif_then |
| `StaticIfElse` | `stcif c: a else: b` (the `else` part is the 2nd child) | if_then | stcif_else |
| `While` | `while c: s` | cond, body | while |
| `WhileWithRepeatStmt` | `while c, step: s` | repeated | while_with_repeat_stmt |
| `StaticWhile` | `stcwhile c: s` | cond, body | stcwhile |
| `StaticWhileWithRepeatStmt` | `stcwhile c, step: s` | repeated | stcwhile_with_repeat_stmt |
| `ForSeq` | `for xs: s` | seq, body | for_seq |
| `ForVarInSeq` | `for x in xs: s` | for_seq, variable | for_var_in_seq |
| `StaticForSeq` | `stcfor xs: s` | seq, body | stcfor_seq |
| `StaticForVarInSeq` | `stcfor x in xs: s` | for_seq, variable | stcfor_var_in_seq |
| `Loop` | `loop s` | body | loop |
| `LoopWithRepeatStmt` | `loop pre: s` | repeated, body | loop_with_repeat_stmt |
| `StaticLoop` | `stcloop s` | body | stcloop |
| `StaticLoopWithRepeatStmt` | `stcloop pre: s` | repeated, body | stcloop_with_repeat_stmt |
| `Match` | `match e { .. }` | matched, match_body | match |
| `StaticMatch` | `stcmatch e { .. }` | matched, match_body | stcmatch |
| `MatchBody` | the arms | list | partial__match_body |
| `MatchCase` | `p => body` | pattern, body | partial__match_case |
| `MatchCasePatternOr` | `p1 | p2` | list | partial__match_case_pattern_or |
| `MatchCasePatternTypeCast` | `T x` (pattern) | type, casted_var | partial__match_case_pattern_typecast |
| `TypePointerMutable` | `*T` | subnode | type_ptrmut |
| `TypePointer` | `&T` | subnode | type_ptr |
| `TypeUnsignedInteger8` | `u8` | – | type_u8 |
| `TypeUnsignedInteger16` | `u16` | – | type_u16 |
| `TypeUnsignedInteger32` | `u32` | – | type_u32 |
| `TypeUnsignedInteger64` | `u64` | – | type_u64 |
| `TypeSignedInteger8` | `i8` | – | type_i8 |
| `TypeSignedInteger16` | `i16` | – | type_i16 |
| `TypeSignedInteger32` | `i32` | – | type_i32 |
| `TypeSignedInteger64` | `i64` | – | type_i64 |
| `TypeFloat16` | `f16` | – | type_f16 |
| `TypeFloat32` | `f32` | – | type_f32 |
| `TypeFloat64` | `f64` | – | type_f64 |
| `TypeBool` | `bool` | – | type_bool |
| `TypeAst` | `ast` | – | type_ast |
| `TypeType` | `type` | – | type_type |
| `TypeTrait` | `trait` | – | type_trait |
| `TypeVariant` | `variant` | – | type_variant |
| `TypeUnit` | `()` | – | type_unit |
| `TypeInlinedFunction` | `inlfun` | – | type_inlfun |
| `TypeFunction` | `fun` | – | type_fun |
| `TypeStaticFunction` | `stcfun` | – | type_stcfun |
| `TypeDefinition` | `*(fields)` | param_tuple | def_type |
| `TypeDefinitionPacked` | `**(fields)` | param_tuple | def_type_packed |
| `TypeDefinitionWithAssertedSize` | `.. assertsize N` | def_type, assertsize | def_type_assertsize |
| `TypeDefinitionWithTrait` | `*(..) implof T !{..}` | def_type, def_trait | def_type_implof |
| `VariantDefinition` | `+(cases)` | param_tuple | def_variant |
| `VariantDefinitionPacked` | `++(cases)` | param_tuple | def_variant_packed |
| `VariantDefinitionWithTag` | `.. tagtype T` | def_variant, tagtype | def_variant_tagtype |
| `VariantDefinitionWithAssertedSize` | `.. assertsize N` | def_variant, assertsize | def_variant_assertsize |
| `VariantDefinitionWithTrait` | `+(..) implof T !{..}` | def_variant, def_trait | def_variant_implof |
| `TraitDefinition` | `!{ members }` | body | def_trait |
| `TraitDefinitionWithImplementations` | `implof S !{ .. }` | implof_tuple, body | def_trait_implof |
| `TypeDefinitionParameterTuple` | field list | list | partial__type_def_param_tuple |
| `TypeDefinitionParameter` | `T` | type | partial__type_def_param |
| `TypeDefinitionParameterMutable` | `mut T ..` | param | partial__type_def_param_mut |
| `TypeDefinitionParameterNamed` | `T x` | param, identifier | partial__type_def_param_named |
| `TypeDefinitionParameterDefaulted` | `T x = d` | param, default_value | partial__type_def_param_default |
| `TypeDefinitionParameterWhere` | `T x where c` | param, where_predicate | partial__type_def_param_where |
| `TypeDefinitionParameterWhereElse` | `T x where c else v` | param, where_else_value | partial__type_def_param_where_else |
| `VariantDefinitionParameterTuple` | case list | list | partial__variant_def_param_tuple |
| `VariantDefinitionParameter` | `Case` | name | partial__variant_def_param |
| `VariantDefinitionParameterTyped` | `Case(fields)` | param, def_type | partial__variant_def_param_typed |
| `VariantDefinitionParameterTagged` | `Case = tag` | param, tag_value | partial__variant_def_param_tagged |
| `TraitDefinitionImplementationTuple` | `implof A, B` | list | partial__trait_def_implof_tuple |
| `TraitDefinitionBody` | `!{ .. }` members | list | partial__trait_def_body |
| `UnifyVariants` | `A || B` | left_type, right_type | unify_variants |
| `UnifyVariantsPacked` | `A ||| B` | left_type, right_type | unify_variants_packed |
| `With` | `e with (f = v)` | value, fun_call_param_tuple | with |
| `FunctionCall` | `f(args)` | callable, fun_param_tuple | fun_call |
| `BuiltinCall` | `crash x`, `asm x`, `syscall (..)`, `fresh x` | callable, fun_param_tuple | builtin_call |
| `FunctionCallParameterTuple` | argument list | list | partial__fun_call_param_tuple |
| `FunctionCallAssignedParameter` | `name = v` (argument) | identifier, value | partial__fun_call_assigned_param |
| `ArrayIndexing` | `a[i]` | indexable, index | array_index |
| `MemberAccess` | `a.m` | parent, member | member |
| `Dereference` | `p.*` | subnode | dereference |
| `AddressOf` | `x.&` | subnode | address_of |
| `IncrementPostfix` | `e++` | subnode | inc_postfix |
| `DecrementPostfix` | `e--` | subnode | dec_postfix |
| `GenerateLowerBound` | `a..` | subnode | gen_lowerbound |
| `GenerateInclusive` | `a..=b` | lower, upper | gen_incl |
| `GenerateExclusive` | `a..<b` | lower, upper | gen_excl |
| `OfType` | `e oftype T` | value, type | oftype |
| `As` | `e as T` | value, type | as |
| `AsBits` | `e asbits T` | value, type | asbits |
| `LabelArrow` | `e <- x` | value, label | labelarrow |
| `SelfTagArrow` | `e ?<- x` | value, label | selftag_arrow |
| `Destructure` | `a, b` (after `<-`) | list | partial__destructure |
| `SelfTagUnwrap` | `e??` | value | selftag_unwrap |
| `SelfTagUnwrapWithFallback` | `e ?? f` | value, fallback | selftag_unwrap_fallback |
| `Defer` | `defer s` | defered | defer |
| `InlinedDeferDeinit` | `e defer deinit` | subnode | inlined_defer_deinit |
| `BinaryLogicalOr` | `or` | lhs, rhs | binary_logic_or |
| `BinaryLogicalXor` | `xor` | lhs, rhs | binary_logic_xor |
| `BinaryLogicalAnd` | `and` `&&` | lhs, rhs | binary_logic_and |
| `BinaryNumericalOr` | `\|` | lhs, rhs | binary_num_or |
| `BinaryNumericalXor` | `^` | lhs, rhs | binary_num_xor |
| `BinaryNumericalAnd` | `&` | lhs, rhs | binary_num_and |
| `BinaryEquals` | `==` | lhs, rhs | binary_eq |
| `BinaryNotEquals` | `!=` | lhs, rhs | binary_neq |
| `BinaryLess` | `<` | lhs, rhs | binary_less |
| `BinaryGreater` | `>` | lhs, rhs | binary_greater |
| `BinaryLessOrEqual` | `<=` | lhs, rhs | binary_less_eq |
| `BinaryGreaterOrEqual` | `>=` | lhs, rhs | binary_greater_eq |
| `BinaryAdd` | `+` | lhs, rhs | binary_add |
| `BinarySubtract` | `-` | lhs, rhs | binary_sub |
| `BinaryMultiply` | `*` | lhs, rhs | binary_mul |
| `BinaryDivide` | `/` | lhs, rhs | binary_div |
| `BinaryModulus` | `%` | lhs, rhs | binary_mod |
| `BinaryShiftLeft` | `<<` | lhs, rhs | binary_shift_left |
| `BinaryShiftRight` | `>>` | lhs, rhs | binary_shift_right |
| `IdentifierSelf` | `self` | – | identifier_self |
| `Identifier` | `name` | text | identifier |
| `StringValue` | `"text"` | text | string |
| `IntegerValue` | `42` | text | int |
| `FloatingPointValue` | `2.5` | text | float |
| `CharacterValue` | `'c'` | text | char |
| `BooleanTrue` | `true` | – | boolean_true |
| `BooleanFalse` | `false` | – | boolean_false |
| `Quote` | `quote: e` | body | quote |
| `Unquote` | `@x` | subnode | unquote |
| `UnquoteList` | `@..xs` | subnode | unquote_list |
| `Paste` | `name_@(x)` | prefix, hole | paste |
| `Splice` | `<e>` | subnode | splice |
| `Reflect` | `refl x` | subnode | refl |
| `Include` | `include "f"` | subnode | include |
| `IncludeRaw` | `includeraw "f"` | subnode | include_raw |
| `VariableDefinition` | `T x` (declared name) | type, identifier | def_var |
| `Assignment` | `x = v` | assignee, assigned | assign |
| `AssignmentTyped` | `T x = v` | def_var, assigned | assign_typed |
| `ModifierPublic` | `pub ..` | subnode | mod_pub |
| `ModifierMutable` | `mut ..` | subnode | mod_mut |
| `ModifierStatic` | `stc ..` | subnode | mod_stc |
| `AssignmentAdd` | `+=` | lhs, rhs | assign_add |
| `AssignmentSubtract` | `-=` | lhs, rhs | assign_sub |
| `AssignmentMultiply` | `*=` | lhs, rhs | assign_mul |
| `AssignmentDivide` | `/=` | lhs, rhs | assign_div |
| `AssignmentModulus` | `%=` | lhs, rhs | assign_mod |
| `MultipleAssignedValues` | `1, 2` (values of `a, b = 1, 2`) | list | partial__assign_multival |
