/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Proof-value dependency guard

`#guard_depends_on source, identity` fails unless the elaborated value of
`source` transitively references `identity`.  Only declaration values are
followed: types are deliberately ignored so that mentioning an identity in
an interface does not count as using its proof.  The traversal opens theorem
and opaque-definition wrappers stored in the environment, making indirect
uses mechanically visible without relying on reducibility.
-/
import Lean.Elab.Command
import Lean.Util.FoldConsts

namespace Fermat.Conservation.GuardDependsOn

open Lean Elab Command

/-- The environment value carried by declarations whose implementations can
be audited.  Axioms, constructors, recursors, and quotient primitives have
no implementation value to traverse. -/
private def declarationValue? : ConstantInfo → Option Expr
  | .defnInfo info => some info.value
  | .thmInfo info => some info.value
  | .opaqueInfo info => some info.value
  | _ => none

/-- Whether the value of `declaration` transitively references `identity`.
The visited set both bounds the traversal and handles shared wrapper graphs. -/
private partial def valueDependsOn
    (env : Environment) (identity declaration : Name) :
    StateM NameSet Bool := do
  if declaration == identity then
    return true
  let visited ← get
  if visited.contains declaration then
    return false
  modify fun visited => visited.insert declaration
  let some value := (env.find? declaration).bind declarationValue?
    | return false
  value.getUsedConstants.anyM (valueDependsOn env identity)

/--
`#guard_depends_on source, identity` checks that `identity` occurs in the
transitive declaration-value dependency graph of `source`.

The source's type and all dependency types are intentionally excluded.  A
successful guard therefore records a proof-term dependency, including one
hidden behind theorem or opaque-definition wrappers, rather than a merely
decorative occurrence in a declaration signature.
-/
elab "#guard_depends_on " source:ident ", " identity:ident : command => do
  let sourceName ←
    liftCoreM <| realizeGlobalConstNoOverloadWithInfo source
  let identityName ←
    liftCoreM <| realizeGlobalConstNoOverloadWithInfo identity
  let env ← getEnv
  let some sourceValue := (env.find? sourceName).bind declarationValue?
    | throwError
        "cannot audit {sourceName}: the declaration has no implementation value"
  let depends := Id.run <|
    (sourceValue.getUsedConstants.anyM
      (valueDependsOn env identityName)).run' {}
  unless depends do
    throwError
      "no transitive value-dependency path from {sourceName} to {identityName}; declaration types are intentionally ignored"

/--
`#guard_not_depends_on source, identity` is the negative proof-value guard.
It succeeds exactly when the implementation of `source` has no transitive
reference to `identity`; declaration types remain intentionally ignored.

This is useful when a new proof shares infrastructure with an older route
but must not close by invoking the older endpoint itself.
-/
elab "#guard_not_depends_on " source:ident ", " identity:ident : command => do
  let sourceName ←
    liftCoreM <| realizeGlobalConstNoOverloadWithInfo source
  let identityName ←
    liftCoreM <| realizeGlobalConstNoOverloadWithInfo identity
  let env ← getEnv
  let some sourceValue := (env.find? sourceName).bind declarationValue?
    | throwError
        "cannot audit {sourceName}: the declaration has no implementation value"
  let depends := Id.run <|
    (sourceValue.getUsedConstants.anyM
      (valueDependsOn env identityName)).run' {}
  if depends then
    throwError
      "unexpected transitive value-dependency path from {sourceName} to {identityName}; declaration types are intentionally ignored"

/-- The equivalence constructors which could package a middle object as a
product.  The no-splitting audit intentionally treats every one of these as
forbidden when `Prod` occurs in the same public declaration type. -/
private def equivalenceTypeNames : Array Name :=
  #[Name.mkSimple "Equiv", Name.mkSimple "MulEquiv",
    Name.mkSimple "AddEquiv", Name.mkSimple "LinearEquiv"]

/--
`#audit_no_product_equiv_types_prefix Namespace` fails when a declaration
under `Namespace` has a type mentioning both a product and an equivalence.

This is the type-level companion to `#guard_depends_on`: it audits consumed
interfaces rather than proof values.  The power-root cone uses it to make the
no-Selmer-splitting rule mechanical.  Its deliberately conservative scope is
appropriate there: the public exact-sequence API has no legitimate reason to
return or accept any equivalence with a product.
-/
elab "#audit_no_product_equiv_types_prefix " p:ident : command => do
  let env ← getEnv
  let auditedPrefix := p.getId
  let declarations :=
    env.constants.toList
      |>.filter fun entry => auditedPrefix.isPrefixOf entry.1
  for (declaration, info) in declarations do
    let used := info.type.getUsedConstants
    let mentionsProduct := used.contains ``Prod
    let mentionsEquivalence := equivalenceTypeNames.any used.contains
    if mentionsProduct && mentionsEquivalence then
      throwError
        "{declaration} exposes or consumes an equivalence with a product; the audited exact-sequence cone must retain its unsplit middle"

end Fermat.Conservation.GuardDependsOn
