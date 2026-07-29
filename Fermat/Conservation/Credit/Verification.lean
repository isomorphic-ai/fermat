/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Executable audit for the route-neutral credit ladder

This non-imported leaf audits every public C1--C3 theorem and checks that no
forbidden endpoint, generic-irregular, or ladder declaration enters the
credit cone.
-/
import Fermat.Conservation.Credit.Vacuum
import Fermat.Conservation.Credit.Capacity
import Fermat.Conservation.Credit.Repayment

/-! ## C1: generated vacuum and two-sided semilattice -/

/--
info: 'Fermat.Conservation.Credit.mem_generated' does not depend on any axioms
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.mem_generated

/--
info: 'Fermat.Conservation.Credit.mem_merge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.mem_merge

/--
info: 'Fermat.Conservation.Credit.merge_self' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.merge_self

/--
info: 'Fermat.Conservation.Credit.merge_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.merge_comm

/--
info: 'Fermat.Conservation.Credit.merge_assoc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.merge_assoc

/--
info: 'Fermat.Conservation.Credit.merge_bot_left' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.merge_bot_left

/--
info: 'Fermat.Conservation.Credit.merge_bot_right' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.merge_bot_right

/--
info: 'Fermat.Conservation.Credit.generated_union' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.generated_union

/--
info: 'Fermat.Conservation.Credit.opposite_apply' depends on axioms: [Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.opposite_apply

/--
info: 'Fermat.Conservation.Credit.opposite_opposite' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.opposite_opposite

/--
info: 'Fermat.Conservation.Credit.opposite_merge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.opposite_merge

/--
info: 'Fermat.Conservation.Credit.reverseRoute_reverseRoute' depends on axioms: [Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.reverseRoute_reverseRoute

/--
info: 'Fermat.Conservation.Credit.opposite_generated' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.opposite_generated

/--
info: 'Fermat.Conservation.Credit.generated_eq_bot_of_no_generator' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.generated_eq_bot_of_no_generator

/--
info: 'Fermat.Conservation.Credit.kummer_credit_vacuum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.kummer_credit_vacuum

/-! ## C2: one cycle, generated edge family, and capacity index -/

/--
info: 'Fermat.Conservation.Credit.Cycle.point_zero' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Cycle.point_zero

/--
info: 'Fermat.Conservation.Credit.Cycle.point_succ' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Cycle.point_succ

/--
info: 'Fermat.Conservation.Credit.Cycle.point_closes' does not depend on any axioms
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Cycle.point_closes

/--
info: 'Fermat.Conservation.Credit.Cycle.edge_mem_generatedSubledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Cycle.edge_mem_generatedSubledger

/--
info: 'Fermat.Conservation.Credit.Cycle.capacityIndex_eq_relIndex' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Cycle.capacityIndex_eq_relIndex

/--
info: 'Fermat.Conservation.Credit.Cycle.transfer_self' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Cycle.transfer_self

/--
info: 'Fermat.Conservation.Credit.Cycle.transfer_opposite' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Cycle.transfer_opposite

/--
info: 'Fermat.Conservation.Credit.Cycle.CapacityData.capacity_eq_relIndex' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Cycle.CapacityData.capacity_eq_relIndex

/--
info: 'Fermat.Conservation.Credit.Cycle.CapacityData.capacity_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Cycle.CapacityData.capacity_pos

/--
info: 'Fermat.Conservation.Credit.Cycle.CapacityCertificate.sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Cycle.CapacityCertificate.sound

/--
info: 'Fermat.Conservation.Credit.Cycle.IndexCertificate.sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Cycle.IndexCertificate.sound

/--
info: 'Fermat.Conservation.Credit.Cycle.iterate_mul_left' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Cycle.iterate_mul_left

/--
info: 'Fermat.Conservation.Credit.Cycle.ofMul_point' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Cycle.ofMul_point

/-! ## C3: Vandiver repayment on the generated edge family -/

/--
info: 'Fermat.Conservation.Credit.Repayment.realUnits_odd_pow_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Repayment.realUnits_odd_pow_injective

/--
info: 'Fermat.Conservation.Credit.Repayment.repay_of_deep_generated_cycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Repayment.repay_of_deep_generated_cycle

/-! ## Exhaustive forbidden-prefix guards -/

open Lean Elab Command

/-- Fail if the imported environment contains any declaration below a
forbidden namespace or module prefix. -/
elab "#guard_no_decl_prefix " p:ident : command => do
  let env ← getEnv
  let forbiddenPrefix := p.getId
  let offenders :=
    env.constants.toList.filter fun entry =>
      forbiddenPrefix.isPrefixOf entry.1
  unless offenders.isEmpty do
    throwError
      "declarations with forbidden prefix {forbiddenPrefix}: {offenders.map Prod.fst}"

#guard_no_decl_prefix Fermat.FiftyNine.GenericProof
#guard_no_decl_prefix Fermat.FiftyNine.FirstCase
#guard_no_decl_prefix Fermat.FiftyNine.GenericSecondCase
#guard_no_decl_prefix Fermat.FiftyNine.Folding
#guard_no_decl_prefix Fermat.FiftyNine.GenericChannels
#guard_no_decl_prefix Fermat.FiftyNine.GenericLemmaTwo
#guard_no_decl_prefix Fermat.GenericIrregular
#guard_no_decl_prefix Fermat.Irregular
#guard_no_decl_prefix Fermat.Ladder

/-! The forbidden repository transport is a declaration, not a namespace. -/

/--
error: Unknown identifier `Fermat.HoldsAt.mono_of_dvd`
-/
#guard_msgs in
#check Fermat.HoldsAt.mono_of_dvd
