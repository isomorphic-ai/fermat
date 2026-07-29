/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# N59 conservation structural verification

This non-imported executable audit leaf checks every theorem currently
exposed by the clean exponent-59 structural spine.  It also checks the
complete forbidden namespace prefixes, rather than relying only on
representative unused-name tests.

The final `Fermat.HoldsAt 59` theorem is not present here: `FINDINGS.md`
records the completed C2 certificate and bounded C4 bridge, together with
the exact remaining C3 character-forcing and stock-to-successor seams which
must close before that endpoint can be added honestly.
-/
import Fermat.FiftyNine.Conservation.Spine
import Fermat.FiftyNine.Conservation.CapacityCertificate
import Fermat.FiftyNine.Conservation.BoundedSinnott

/-! ## Generated N59 credit: tower, orbit, matrix, capacity, repayment -/

/--
info: 'Fermat.FiftyNine.Conservation.Credit.stockRank_eq_twentyEight' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.stockRank_eq_twentyEight

/--
info: 'Fermat.FiftyNine.Conservation.Credit.realCycleOrder_eq_twentyNine' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.realCycleOrder_eq_twentyNine

/--
info: 'Fermat.FiftyNine.Conservation.Credit.conductor_eq_fiftyNine' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.conductor_eq_fiftyNine

/--
info: 'Fermat.FiftyNine.Conservation.Credit.generationTower' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.generationTower

/--
info: 'Fermat.FiftyNine.Conservation.Credit.attestationPrime_eq_eightHundredTwentySeven' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.attestationPrime_eq_eightHundredTwentySeven

/--
info: 'Fermat.FiftyNine.Conservation.Credit.attestationPrime_isPrime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.attestationPrime_isPrime

/--
info: 'Fermat.FiftyNine.Conservation.Credit.attestationRoot_eq_sixHundredSeventyOne' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.attestationRoot_eq_sixHundredSeventyOne

/--
info: 'Fermat.FiftyNine.Conservation.Credit.attestationRoot_order' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.attestationRoot_order

/--
info: 'Fermat.FiftyNine.Conservation.Credit.exponentGenerator_val' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.exponentGenerator_val

/--
info: 'Fermat.FiftyNine.Conservation.Credit.exponentGenerator_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.exponentGenerator_order

/--
info: 'Fermat.FiftyNine.Conservation.Credit.exponentGenerator_pow_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.exponentGenerator_pow_order

/--
info: 'Fermat.FiftyNine.Conservation.Credit.exponentCycle_rank' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.exponentCycle_rank

/--
info: 'Fermat.FiftyNine.Conservation.Credit.exponentCycle_exactPeriod' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.exponentCycle_exactPeriod

/--
info: 'Fermat.FiftyNine.Conservation.Credit.exponentCycle_point' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.exponentCycle_point

/--
info: 'Fermat.FiftyNine.Conservation.Credit.generatedUnit_eq_orbit_ratio' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.generatedUnit_eq_orbit_ratio

/--
info: 'Fermat.FiftyNine.Conservation.Credit.generatedUnit_mem_subledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.generatedUnit_mem_subledger

/--
info: 'Fermat.FiftyNine.Conservation.Credit.fundingTransfer_opposite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.fundingTransfer_opposite

/--
info: 'Fermat.FiftyNine.Conservation.Credit.everyTransfer_isFunded' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.everyTransfer_isFunded

/--
info: 'Fermat.FiftyNine.Conservation.Credit.fundedGenerators_eq_univ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.fundedGenerators_eq_univ

/--
info: 'Fermat.FiftyNine.Conservation.Credit.receivableLedger_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.receivableLedger_apply

/--
info: 'Fermat.FiftyNine.Conservation.Credit.receivableLedger_opposite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.receivableLedger_opposite

/--
info: 'Fermat.FiftyNine.Conservation.Credit.ledger_cardinality' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.ledger_cardinality

/--
info: 'Fermat.FiftyNine.Conservation.Credit.capacityIndex_eq_relIndex' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.capacityIndex_eq_relIndex

/--
info: 'Fermat.FiftyNine.Conservation.Credit.repayment_of_capacity_and_coefficient_forcing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.repayment_of_capacity_and_coefficient_forcing

/-! ## Filled C2 and bounded C4 seams -/

/--
info: 'Fermat.FiftyNine.Conservation.CapacityCertificate.capacityCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.CapacityCertificate.capacityCertificate

/--
info: 'Fermat.FiftyNine.Conservation.Credit.boundedSinnottBridge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.boundedSinnottBridge

/-! ## Seven-stock receipt -/

/--
info: 'Fermat.FiftyNine.Conservation.stockSpineReceipt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.stockSpineReceipt

/-! ## Rank-28 gauge and ramified drain -/

/--
info: 'Fermat.FiftyNine.Conservation.charge_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.charge_mul

/--
info: 'Fermat.FiftyNine.Conservation.gauge_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.gauge_decomposition

/--
info: 'Fermat.FiftyNine.Conservation.charge_gauge_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.charge_gauge_invariant

/--
info: 'Fermat.FiftyNine.Conservation.charge_full_gauge_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.charge_full_gauge_invariant

/--
info: 'Fermat.FiftyNine.Conservation.unitRank_eq_twentyEight' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.unitRank_eq_twentyEight

/--
info: 'Fermat.FiftyNine.Conservation.rankTwentyEightGauge_regulator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.rankTwentyEightGauge_regulator

/--
info: 'Fermat.FiftyNine.Conservation.lambda_eq_neg_zeta_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.lambda_eq_neg_zeta_sub_one

/--
info: 'Fermat.FiftyNine.Conservation.lambda_charge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.lambda_charge

/--
info: 'Fermat.FiftyNine.Conservation.charge_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.charge_pow

/--
info: 'Fermat.FiftyNine.Conservation.drainCharge_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.drainCharge_eq

/--
info: 'Fermat.FiftyNine.Conservation.drainCharge_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.drainCharge_strictMono

/--
info: 'Fermat.FiftyNine.Conservation.drainCharge_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.drainCharge_step

/-! ## Shared conservation floor -/

/--
info: 'Fermat.Conservation.noInfinitePositiveChargeDrain' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.noInfinitePositiveChargeDrain

/--
info: 'Fermat.Conservation.impossible_of_strict_charge_drain' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.impossible_of_strict_charge_drain

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

/-! Representative declaration guards cover module boundaries whose source
file does not declare into a same-named namespace (notably `FirstCase`). -/

/--
error: Unknown identifier `Fermat.FiftyNine.GenericProof.holdsAt_fiftyNine_generic`
-/
#guard_msgs in
#check Fermat.FiftyNine.GenericProof.holdsAt_fiftyNine_generic

/--
error: Unknown identifier `Fermat.FiftyNine.firstCase_of_pairwise_coprime`
-/
#guard_msgs in
#check Fermat.FiftyNine.firstCase_of_pairwise_coprime

/--
error: Unknown identifier `Fermat.FiftyNine.GenericSecondCase.secondCaseExcluded_fiftyNine_generic`
-/
#guard_msgs in
#check Fermat.FiftyNine.GenericSecondCase.secondCaseExcluded_fiftyNine_generic

/--
error: Unknown identifier `Fermat.FiftyNine.Folding.safePrimeLadder`
-/
#guard_msgs in
#check Fermat.FiftyNine.Folding.safePrimeLadder

/--
error: Unknown identifier `Fermat.FiftyNine.GenericChannels.bernoulliCubeCondition_fiftyNine_generic`
-/
#guard_msgs in
#check Fermat.FiftyNine.GenericChannels.bernoulliCubeCondition_fiftyNine_generic

/--
error: Unknown identifier `Fermat.FiftyNine.GenericLemmaTwo.vandiverLemmaTwo_fiftyNine_generic`
-/
#guard_msgs in
#check Fermat.FiftyNine.GenericLemmaTwo.vandiverLemmaTwo_fiftyNine_generic

/-! The forbidden repository transport is a declaration rather than a
namespace, so it receives a direct unknown-constant guard. -/

/--
error: Unknown constant `Fermat.HoldsAt.mono_of_dvd`
-/
#guard_msgs in
#check Fermat.HoldsAt.mono_of_dvd

/-! Additional classical endpoints remain outside the cone as well. -/

/--
error: Unknown identifier `Fermat.FiftyNine.holdsAt_fiftyNine_conservation`
-/
#guard_msgs in
#check Fermat.FiftyNine.holdsAt_fiftyNine_conservation

/--
error: Unknown identifier `Fermat.FiftyNine.holdsAt_fiftyNine`
-/
#guard_msgs in
#check Fermat.FiftyNine.holdsAt_fiftyNine

/--
error: Unknown identifier `Fermat.KummerIso.ResidueRegressions.holdsAt_fiftyNine`
-/
#guard_msgs in
#check Fermat.KummerIso.ResidueRegressions.holdsAt_fiftyNine
