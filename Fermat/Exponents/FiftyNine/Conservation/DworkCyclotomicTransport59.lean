/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Cyclotomic covariance of the Dwork-to-local transport at 59

The completed Dwork ring, the pinned valued completion, and the concrete
Fermat-side lambda completion carry cyclotomic actions built by different
constructions.  This file proves that the existing transport maps intertwine
those actions.

The final theorem exposes the exact finite unit-level rewrite needed to turn
a genuine local conjugate of a transported Dwork principal unit back into a
Dwork conjugate.  It asserts no Artin--Hasse or Hilbert-symbol formula and no
nonvanishing statement.
-/
import Fermat.Exponents.FiftyNine.Conservation.DworkPrincipalUnitCandidates59
import Fermat.Experiments.Conservation.GuardDependsOn
import KummerCriterion.CyclotomicUnits.DworkParameter.Part18

open scoped NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.DworkCyclotomicTransport59

open KummerCriterion
open KummerCriterion.CyclotomicUnits.PadicLogSetup
open KummerCriterion.CyclotomicUnits.PadicLogSetup.DworkParameter
open KummerCriterion.CyclotomicUnits.PadicLogSetup.DworkParameter.Conjugation
open Fermat.Conservation.LocalKummerTransport
open Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59
open Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59
open Fermat.FiftyNine.Conservation.DworkPrincipalUnitCandidates59
open Fermat.FiftyNine.Conservation.LambdaCyclotomicCompletionAction59
open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.LocalIntegralTrace59
open Fermat.FiftyNine.Conservation.TwistedArtinHasse59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

/-! ## Dwork completion to valued integers -/

/-- The Dwork-to-valued-integer equivalence intertwines the two cyclotomic
actions.  Equality in the adic completion is checked at every finite
evaluation level. -/
theorem dworkValuedAlgEquiv59_cyclotomic
    (sigma : CyclotomicUnitDelta 59)
    (x : DworkCompleteIntegerRing 59 K) :
    dworkValuedAlgEquiv59 K
        (dworkCompleteCyclotomicEquiv (p := 59) K sigma x) =
      valuedIntegerCyclotomicEquiv (p := 59) K sigma
        (dworkValuedAlgEquiv59 K x) := by
  apply (AdicCompletion.ofAlgEquiv (lambdaIdeal 59 K)).injective
  change AdicCompletion.of (lambdaIdeal 59 K) (ValuedIntegerRing 59 K)
      ((AdicCompletion.ofAlgEquiv (lambdaIdeal 59 K)).symm
        (dworkCompleteCyclotomicEquiv (p := 59) K sigma x)) =
    AdicCompletion.of (lambdaIdeal 59 K) (ValuedIntegerRing 59 K)
      (valuedIntegerCyclotomicEquiv (p := 59) K sigma
        ((AdicCompletion.ofAlgEquiv (lambdaIdeal 59 K)).symm x))
  rw [AdicCompletion.of_ofAlgEquiv_symm]
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_dworkCompleteCyclotomicEquiv]
  rw [← AdicCompletion.mk_ofAlgEquiv_symm]
  rfl

/-- Restricting the valued-completion action to its integer ring commutes
definitionally with inclusion into the completion. -/
@[simp]
theorem valuedCompletionCyclotomicEquiv_valuedInteger
    (sigma : CyclotomicUnitDelta 59)
    (x : ValuedIntegerRing 59 K) :
    valuedCompletionCyclotomicEquiv (p := 59) K sigma
        (valuedIntegerToLambdaCompletion59 K x) =
      valuedIntegerToLambdaCompletion59 K
        (valuedIntegerCyclotomicEquiv (p := 59) K sigma x) := by
  rfl

/-! ## The pinned and concrete lambda completions -/

/-- The cast between the equal pinned and Fermat-side lambda places respects
the dense global-field embeddings. -/
@[simp]
theorem valuedCompletionEquivLambdaField59_algebraMap
    (x : K) :
    valuedCompletionEquivLambdaField59 K
        (algebraMap K (ValuedCompletion 59 K) x) =
      lambdaLocalization59 K x := by
  unfold valuedCompletionEquivLambdaField59
  have hplace := lambdaPlace59_eq_kummerCriterion K
  cases hplace
  rfl

/-- The cyclotomic action constructed in the pinned valued completion is
the same action as the independently constructed Fermat-side action after
casting between the equal lambda places. -/
theorem valuedCompletionEquivLambdaField59_cyclotomic
    (sigma : CyclotomicUnitDelta 59)
    (x : ValuedCompletion 59 K) :
    valuedCompletionEquivLambdaField59 K
        (valuedCompletionCyclotomicEquiv (p := 59) K sigma x) =
      cyclotomicLambdaCompletionRingEquiv59 K sigma
        (valuedCompletionEquivLambdaField59 K x) := by
  have hcast : Continuous (valuedCompletionEquivLambdaField59 K) := by
    unfold valuedCompletionEquivLambdaField59
    have hplace := lambdaPlace59_eq_kummerCriterion K
    cases hplace
    exact continuous_id
  have hfermat :
      Continuous (cyclotomicLambdaCompletionRingEquiv59 K sigma) := by
    exact UniformSpace.Completion.continuous_map
  apply UniformSpace.Completion.ext'
    (hcast.comp
      (continuous_valuedCompletionCyclotomicEquiv (p := 59) (K := K) sigma))
    (hfermat.comp hcast)
    (fun y => ?_) x
  change valuedCompletionEquivLambdaField59 K
      (valuedCompletionCyclotomicEquiv (p := 59) K sigma
        (algebraMap K (ValuedCompletion 59 K) y.ofVal)) =
    cyclotomicLambdaCompletionRingEquiv59 K sigma
      (valuedCompletionEquivLambdaField59 K
        (algebraMap K (ValuedCompletion 59 K) y.ofVal))
  rw [valuedCompletionCyclotomicEquiv_algebraMap]
  rw [valuedCompletionEquivLambdaField59_algebraMap]
  rw [valuedCompletionEquivLambdaField59_algebraMap]
  rw [cyclotomicLambdaCompletionRingEquiv59_lambdaLocalization]
  rfl

/-! ## End-to-end covariance -/

/-- The complete element-level Dwork-to-local transport intertwines the
cyclotomic actions. -/
theorem dworkToLambdaLocal59_cyclotomic
    (sigma : CyclotomicUnitDelta 59)
    (x : DworkCompleteIntegerRing 59 K) :
    valuedCompletionEquivLambdaField59 K
        (valuedIntegerToLambdaCompletion59 K
          (dworkValuedAlgEquiv59 K
            (dworkCompleteCyclotomicEquiv (p := 59) K sigma x))) =
      cyclotomicLambdaCompletionRingEquiv59 K sigma
        (valuedCompletionEquivLambdaField59 K
          (valuedIntegerToLambdaCompletion59 K
            (dworkValuedAlgEquiv59 K x))) := by
  rw [dworkValuedAlgEquiv59_cyclotomic]
  rw [← valuedCompletionCyclotomicEquiv_valuedInteger]
  rw [valuedCompletionEquivLambdaField59_cyclotomic]

/-- Unit-level spelling of the complete covariance theorem. -/
theorem dworkUnitToLambdaLocal59_cyclotomic
    (sigma : CyclotomicUnitDelta 59)
    (u : (DworkCompleteIntegerRing 59 K)ˣ) :
    unitMap (cyclotomicLambdaCompletionRingEquiv59 K sigma).toRingHom
        (Units.map (valuedCompletionEquivLambdaField59 K).toRingHom
          (Units.map (valuedIntegerToLambdaCompletion59 K).toMonoidHom
            (Units.map (dworkValuedAlgEquiv59 K).toRingHom u))) =
      Units.map (valuedCompletionEquivLambdaField59 K).toRingHom
        (Units.map (valuedIntegerToLambdaCompletion59 K).toMonoidHom
          (Units.map (dworkValuedAlgEquiv59 K).toRingHom
            (Units.map
              (dworkCompleteCyclotomicEquiv (p := 59) K sigma).toMonoidHom u))) := by
  apply Units.ext
  exact (dworkToLambdaLocal59_cyclotomic K sigma (u :
    DworkCompleteIntegerRing 59 K)).symm

/-- Every genuine local conjugate of the transported depth-indexed Dwork
principal unit is exactly the transport of its Dwork conjugate. -/
theorem dworkPrincipalUnitLocal59_cyclotomic
    (sigma : CyclotomicUnitDelta 59)
    (depth : ℕ) (hdepth : depth ≠ 0) :
    unitMap (cyclotomicLambdaCompletionRingEquiv59 K sigma).toRingHom
        (dworkPrincipalUnitLocal59 K depth hdepth) =
      Units.map (valuedCompletionEquivLambdaField59 K).toRingHom
        (Units.map (valuedIntegerToLambdaCompletion59 K).toMonoidHom
          (Units.map (dworkValuedAlgEquiv59 K).toRingHom
            (Units.map
              (dworkCompleteCyclotomicEquiv (p := 59) K sigma).toMonoidHom
              (dworkPrincipalUnitAtDepth59 K depth hdepth)))) := by
  unfold dworkPrincipalUnitLocal59 dworkPrincipalUnitPinnedLambda59
    dworkPrincipalUnitValuedInteger59
  exact dworkUnitToLambdaLocal59_cyclotomic K sigma
    (dworkPrincipalUnitAtDepth59 K depth hdepth)

/-! ## Kernel-trust and dependency audit -/

/--
info: 'Fermat.FiftyNine.Conservation.DworkCyclotomicTransport59.dworkValuedAlgEquiv59_cyclotomic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms dworkValuedAlgEquiv59_cyclotomic

/--
info: 'Fermat.FiftyNine.Conservation.DworkCyclotomicTransport59.valuedCompletionEquivLambdaField59_cyclotomic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms valuedCompletionEquivLambdaField59_cyclotomic

/--
info: 'Fermat.FiftyNine.Conservation.DworkCyclotomicTransport59.dworkPrincipalUnitLocal59_cyclotomic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms dworkPrincipalUnitLocal59_cyclotomic

/- The finite-evaluation proof must consume the existing Dwork action law. -/
#guard_depends_on
  dworkValuedAlgEquiv59_cyclotomic,
  evalₐ_dworkCompleteCyclotomicEquiv

/- Completion covariance is forced from the two dense-embedding laws. -/
#guard_depends_on
  valuedCompletionEquivLambdaField59_cyclotomic,
  valuedCompletionCyclotomicEquiv_algebraMap

#guard_depends_on
  valuedCompletionEquivLambdaField59_cyclotomic,
  cyclotomicLambdaCompletionRingEquiv59_lambdaLocalization

/- The principal-unit endpoint retains both nontrivial transport seams. -/
#guard_depends_on
  dworkPrincipalUnitLocal59_cyclotomic,
  dworkValuedAlgEquiv59_cyclotomic

#guard_depends_on
  dworkPrincipalUnitLocal59_cyclotomic,
  valuedCompletionEquivLambdaField59_cyclotomic

end Fermat.FiftyNine.Conservation.DworkCyclotomicTransport59
