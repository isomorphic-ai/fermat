/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Executable audit for the route-neutral credit ladder

This non-imported leaf audits the public C1--C3 and W1--W3 surfaces and
checks that no forbidden endpoint, generic-irregular, or ladder declaration
or module enters the credit cone.
-/
import Fermat.Conservation.Credit.Vacuum
import Fermat.Conservation.Credit.Capacity
import Fermat.Conservation.Credit.Repayment
import Fermat.Conservation.Credit.Flow
import Fermat.Conservation.Credit.CompletedFlow
import Fermat.Conservation.Credit.Bernoulli
import Fermat.Conservation.Credit.Gauge
import Fermat.Conservation.Credit.HighFlow
import Fermat.Conservation.Credit.Forcing

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

/-! ## W1--W2: generated flow and gauge diagonalization -/

open Lean Elab Command

/-- Fail if any declaration below a prefix uses an axiom beyond Lean's
standard extensionality, choice, and quotient-soundness boundary.  The
prefix form keeps this audit exhaustive when a generated API gains another
public theorem. -/
elab "#guard_standard_axioms_prefix " p:ident : command => do
  let env ← getEnv
  let auditedPrefix := p.getId
  let allowed : Array Name :=
    #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations :=
    env.constants.toList
      |>.map Prod.fst
      |>.filter auditedPrefix.isPrefixOf
  for declaration in declarations do
    let axioms ← Lean.collectAxioms declaration
    let unexpected := axioms.filter fun ax =>
      !allowed.contains ax
    unless unexpected.isEmpty do
      throwError
        "{declaration} depends on nonstandard axioms: {unexpected}"

#guard_standard_axioms_prefix Fermat.Conservation.Credit.Flow
#guard_standard_axioms_prefix Fermat.Conservation.Credit.Gauge
#guard_standard_axioms_prefix Fermat.Conservation.Credit.Bernoulli

/--
info: 'Fermat.Conservation.Credit.Gauge.GaugeData.orbitGenerator_pow_rank_add_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Gauge.GaugeData.orbitGenerator_pow_rank_add_one

/--
info: 'Fermat.Conservation.Credit.Gauge.GaugeData.cycle_rank' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Gauge.GaugeData.cycle_rank

/--
info: 'Fermat.Conservation.Credit.Gauge.GaugeData.cycle_point' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Gauge.GaugeData.cycle_point

/--
info: 'Fermat.Conservation.Credit.Gauge.GaugeData.realCycleOrder_odd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Gauge.GaugeData.realCycleOrder_odd

/--
info: 'Fermat.Conservation.Credit.Gauge.GaugeData.prime_mod_four_eq_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Gauge.GaugeData.prime_mod_four_eq_three

/--
info: 'Fermat.Conservation.Credit.Gauge.GaugeData.orbitNode_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Gauge.GaugeData.orbitNode_injective

/--
info: 'Fermat.Conservation.Credit.Gauge.GaugeData.orbitGenerator_square_pow_succ_ne_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Gauge.GaugeData.orbitGenerator_square_pow_succ_ne_one

/--
info: 'Fermat.Conservation.Credit.Gauge.GaugeData.rowScale_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Gauge.GaugeData.rowScale_ne_zero

/--
info: 'Fermat.Conservation.Credit.Gauge.GaugeData.columnScale_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Gauge.GaugeData.columnScale_ne_zero

/--
info: 'Fermat.Conservation.Credit.Gauge.GaugeData.characterMatrix_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Gauge.GaugeData.characterMatrix_apply

/--
info: 'Fermat.Conservation.Credit.Gauge.GaugeData.characterMatrix_eq_high_edge_difference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Gauge.GaugeData.characterMatrix_eq_high_edge_difference

/--
info: 'Fermat.Conservation.Credit.Gauge.GaugeData.characterMatrix_det_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Gauge.GaugeData.characterMatrix_det_ne_zero

/--
info: 'Fermat.Conservation.Credit.Gauge.GaugeData.raw_eq_zero_of_character_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Gauge.GaugeData.raw_eq_zero_of_character_eq_zero

/--
info: 'Fermat.Conservation.Credit.Gauge.GaugeData.characterCoordinates_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Gauge.GaugeData.characterCoordinates_injective

/-! ## W1 completed flow, exact lift, and generic W3 forcing -/

/--
info: 'Fermat.Conservation.Credit.Flow.completedLogFlow_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Flow.completedLogFlow_mul

/--
info: 'Fermat.Conservation.Credit.Flow.dworkParameterPowerBasis_coeff_sub_mem_primeIdeal_sq_of_mem_parameterIdeal_two_mul_prime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Flow.dworkParameterPowerBasis_coeff_sub_mem_primeIdeal_sq_of_mem_parameterIdeal_two_mul_prime

/--
info: 'Fermat.Conservation.Credit.Flow.dworkCompleteCyclotomicEquiv_completedLog' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Flow.dworkCompleteCyclotomicEquiv_completedLog

/--
info: 'Fermat.Conservation.Credit.Bernoulli.exceptional_bernoulli_numerator_not_dvd_cube_of_faulhaber' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Bernoulli.exceptional_bernoulli_numerator_not_dvd_cube_of_faulhaber

/--
info: 'Fermat.Conservation.Credit.Flow.intCast_teichNodeValue' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Flow.intCast_teichNodeValue

/--
info: 'Fermat.Conservation.Credit.Flow.gaugeGeneratorOrbit_exponentFlow_eq_exactHighEdgeCoefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Flow.gaugeGeneratorOrbit_exponentFlow_eq_exactHighEdgeCoefficient

/--
info: 'Fermat.Conservation.Credit.Flow.intCast_exactHighEdgeCoefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Flow.intCast_exactHighEdgeCoefficient

/--
info: 'Fermat.Conservation.Credit.Flow.exponent_dvd_of_highFlowVanishes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Flow.exponent_dvd_of_highFlowVanishes

/--
info: 'Fermat.Conservation.Credit.Flow.deepExponentForcing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Flow.deepExponentForcing

/-! ## Exhaustive forbidden-prefix guards -/

/-- Fail if the imported environment contains any declaration below a
forbidden namespace prefix. -/
elab "#guard_no_decl_prefix " p:ident : command => do
  let env ← getEnv
  let forbiddenPrefix := p.getId
  let offenders :=
    env.constants.toList.filter fun entry =>
      forbiddenPrefix.isPrefixOf entry.1
  unless offenders.isEmpty do
    throwError
      "declarations with forbidden prefix {forbiddenPrefix}: {offenders.map Prod.fst}"

/-- Fail if the transitive import graph contains a module below a forbidden
prefix.  Declaration checks alone cannot detect modules which declare into
a shorter namespace. -/
elab "#guard_no_module_prefix " p:ident : command => do
  let env ← getEnv
  let forbiddenPrefix := p.getId
  let offenders :=
    env.header.moduleNames.filter forbiddenPrefix.isPrefixOf
  unless offenders.isEmpty do
    throwError
      "modules with forbidden prefix {forbiddenPrefix}: {offenders}"

/-- Fail if one exact module occurs in the transitive import graph.  This is
used when a permitted sibling module shares its name prefix. -/
elab "#guard_no_module " p:ident : command => do
  let env ← getEnv
  let forbiddenModule := p.getId
  if env.header.moduleNames.contains forbiddenModule then
    throwError "forbidden module {forbiddenModule} is imported"

#guard_no_decl_prefix Fermat.FiftyNine
#guard_no_decl_prefix Fermat.FiftyNine.GenericProof
#guard_no_decl_prefix Fermat.FiftyNine.FirstCase
#guard_no_decl_prefix Fermat.FiftyNine.GenericSecondCase
#guard_no_decl_prefix Fermat.FiftyNine.Folding
#guard_no_decl_prefix Fermat.FiftyNine.GenericChannels
#guard_no_decl_prefix Fermat.FiftyNine.GenericLemmaTwo
#guard_no_decl_prefix Fermat.GenericIrregular
#guard_no_decl_prefix Fermat.Irregular
#guard_no_decl_prefix Fermat.KummerIso
#guard_no_decl_prefix Fermat.Ladder

#guard_no_module_prefix Fermat.FiftyNine
#guard_no_module_prefix Fermat.GenericIrregular
#guard_no_module_prefix Fermat.Irregular
#guard_no_module_prefix Fermat.KummerIso
#guard_no_module_prefix Fermat.Ladder
#guard_no_module Fermat.Statement

/-! ## Mechanical selected-prime source-literal gate -/

/-- Scan every generic credit Lean source and reject the campaign's selected
prime literal.  Its two digits are assembled as characters so the guard
does not create the occurrence it is designed to reject. -/
elab "#guard_no_selected_prime_literal" : command => do
  let currentPath := System.FilePath.mk (← getFileName)
  let some sourceDirectory := currentPath.parent
    | throwError "cannot locate the generic credit source directory"
  let entries ← liftIO <| System.FilePath.readDir sourceDirectory
  let selectedPrimeLiteral := String.ofList ['5', '9']
  let mut offenders : Array String := #[]
  for entry in entries do
    if entry.path.extension == some "lean" then
      let source ← liftIO <| IO.FS.readFile entry.path
      for (line, index) in source.splitOn "\n" |>.zipIdx do
        if (line.splitOn selectedPrimeLiteral).length > 1 then
          offenders := offenders.push
            s!"{entry.path}:{index + 1}"
  unless offenders.isEmpty do
    throwError
      "selected-prime source literal occurs at {offenders}"

#guard_no_selected_prime_literal

/-! The forbidden repository transport is a declaration, not a namespace. -/

/--
error: Unknown identifier `Fermat.HoldsAt.mono_of_dvd`
-/
#guard_msgs in
#check Fermat.HoldsAt.mono_of_dvd
