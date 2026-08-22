/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The cyclotomic action on the wild 59-adic completion

This file extends the canonical cyclotomic action on the global field to the
actual completion at `lambda = (zeta_59 - 1)`.  The extension is forced by
uniqueness of the prime above `59`: cyclotomic automorphisms fix the lambda
place, hence preserve its valuation exactly.  The resulting valued-ring
automorphism is continuous in both directions and therefore lifts through
Mathlib's uniform-space completion functor.

No local action or continuity certificate is supplied by a caller.
-/
import Fermat.Exponents.FiftyNine.Conservation.CyclotomicSelmerAction59
import Fermat.Exponents.FiftyNine.Conservation.LocalCompletion59
import Mathlib.Topology.Algebra.UniformRing

open scoped NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.LambdaCyclotomicCompletionAction59

open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

/-! ## The unique wild place is fixed -/

/-- Every cyclotomic automorphism fixes the unique height-one place above
`59`, namely `lambda = (zeta_59 - 1)`. -/
theorem cyclotomicPlaceEquiv59_lambdaPlace59
    (sigma : GaloisIndex59) :
    cyclotomicPlaceEquiv59 K sigma (lambdaPlace59 K) =
      lambdaPlace59 K := by
  apply IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
  let moved := cyclotomicPlaceEquiv59 K sigma (lambdaPlace59 K)
  have hunder :
      moved.asIdeal.under ℤ = (lambdaIdeal59 K).under ℤ := by
    simpa [moved] using
      cyclotomicPlaceEquiv59_under_int K sigma (lambdaPlace59 K)
  letI : moved.asIdeal.LiesOver (Ideal.span {(59 : ℤ)}) :=
    ⟨(lambdaIdeal59_liesOver K).over.trans hunder.symm⟩
  change moved.asIdeal = lambdaIdeal59 K
  simpa [lambdaIdeal59] using
    (IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver'
      59 K (globalPrimitiveRoot59_isPrimitive K) moved.asIdeal)

/-! ## Exact valuation preservation -/

/-- The global cyclotomic field automorphism, exposed as a ring
equivalence for the completion functor. -/
noncomputable def cyclotomicFieldRingEquiv59
    (sigma : GaloisIndex59) : K ≃+* K :=
  (KummerCriterion.cyclotomicSigmaOfUnit
    (p := 59) K sigma).toRingEquiv

@[simp]
theorem cyclotomicFieldRingEquiv59_one :
    cyclotomicFieldRingEquiv59 K 1 = RingEquiv.refl K := by
  apply RingEquiv.ext
  intro x
  simp [cyclotomicFieldRingEquiv59,
    KummerCriterion.cyclotomicSigmaOfUnit_one]

/-- Multiplication of cyclotomic indices is composition in action order. -/
theorem cyclotomicFieldRingEquiv59_mul
    (sigma tau : GaloisIndex59) :
    cyclotomicFieldRingEquiv59 K (sigma * tau) =
      (cyclotomicFieldRingEquiv59 K tau).trans
        (cyclotomicFieldRingEquiv59 K sigma) := by
  apply RingEquiv.ext
  intro x
  simp [cyclotomicFieldRingEquiv59,
    KummerCriterion.cyclotomicSigmaOfUnit_mul]

/-- Because the lambda place is fixed, its full valuation (including zero)
is invariant under every cyclotomic field automorphism. -/
theorem lambdaValuation_cyclotomic59
    (sigma : GaloisIndex59) (x : K) :
    (lambdaPlace59 K).valuation K
        (cyclotomicFieldRingEquiv59 K sigma x) =
      (lambdaPlace59 K).valuation K x := by
  by_cases hx : x = 0
  · subst x
    simp [cyclotomicFieldRingEquiv59]
  · let ux : Kˣ := Units.mk0 x hx
    have hcov := valuationOfNeZero_cyclotomic59 K sigma
      (lambdaPlace59 K) ux
    rw [cyclotomicPlaceEquiv59_lambdaPlace59 K sigma⁻¹] at hcov
    have hcov' := congrArg
      (fun z : Multiplicative ℤ => (z : WithZero (Multiplicative ℤ))) hcov
    have haction :
        ((cyclotomicUnitEquiv59 K sigma ux : Kˣ) : K) =
          cyclotomicFieldRingEquiv59 K sigma x := by
      rfl
    simpa [haction, ux,
      IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq] using hcov'

/-! ## The valued pre-completion automorphism -/

/-- The ring carrying the lambda-adic topology before completion. -/
abbrev LambdaWithVal59 :=
  WithVal ((lambdaPlace59 K).valuation K)

/-- The cyclotomic field automorphism transported to the ring equipped with
the lambda valuation. -/
noncomputable def cyclotomicLambdaWithValRingEquiv59
    (sigma : GaloisIndex59) :
    LambdaWithVal59 K ≃+* LambdaWithVal59 K :=
  WithVal.congr
    ((lambdaPlace59 K).valuation K)
    ((lambdaPlace59 K).valuation K)
    (cyclotomicFieldRingEquiv59 K sigma)

@[simp]
theorem cyclotomicLambdaWithValRingEquiv59_one :
    cyclotomicLambdaWithValRingEquiv59 K 1 =
      RingEquiv.refl (LambdaWithVal59 K) := by
  rw [cyclotomicLambdaWithValRingEquiv59,
    cyclotomicFieldRingEquiv59_one]
  exact WithVal.congr_refl _

/-- The pre-completion equivalences inherit the cyclotomic composition
law exactly. -/
theorem cyclotomicLambdaWithValRingEquiv59_mul
    (sigma tau : GaloisIndex59) :
    cyclotomicLambdaWithValRingEquiv59 K (sigma * tau) =
      (cyclotomicLambdaWithValRingEquiv59 K tau).trans
        (cyclotomicLambdaWithValRingEquiv59 K sigma) := by
  rw [cyclotomicLambdaWithValRingEquiv59,
    cyclotomicFieldRingEquiv59_mul]
  exact WithVal.congr_trans _ _ _ _ _

/-- The pre-completion automorphism preserves the canonical valuation
exactly. -/
theorem cyclotomicLambdaWithValRingEquiv59_valuation
    (sigma : GaloisIndex59) (x : LambdaWithVal59 K) :
    Valued.v (cyclotomicLambdaWithValRingEquiv59 K sigma x) =
      Valued.v x := by
  change (lambdaPlace59 K).valuation K
      (cyclotomicFieldRingEquiv59 K sigma x.ofVal) =
    (lambdaPlace59 K).valuation K x.ofVal
  exact lambdaValuation_cyclotomic59 K sigma x.ofVal

/-- Valuation preservation sends every basic lambda-adic neighborhood to
itself, so the pre-completion automorphism is uniformly continuous. -/
theorem cyclotomicLambdaWithValRingEquiv59_uniformContinuous
    (sigma : GaloisIndex59) :
    UniformContinuous (cyclotomicLambdaWithValRingEquiv59 K sigma) := by
  refine uniformContinuous_of_continuousAt_zero _ ?_
  simp_rw [ContinuousAt, map_zero,
    (Valued.hasBasis_nhds_zero _ _).tendsto_iff
      (Valued.hasBasis_nhds_zero _ _),
    true_and, forall_const]
  intro gamma
  refine ⟨gamma, ?_⟩
  intro x hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  rw [Valuation.restrict_lt_iff_lt_embedding] at hx ⊢
  simpa only [cyclotomicLambdaWithValRingEquiv59_valuation] using hx

/-- Continuous spelling consumed by `Completion.mapRingEquiv`. -/
theorem cyclotomicLambdaWithValRingEquiv59_continuous
    (sigma : GaloisIndex59) :
    Continuous (cyclotomicLambdaWithValRingEquiv59 K sigma) :=
  (cyclotomicLambdaWithValRingEquiv59_uniformContinuous K sigma).continuous

/-- The inverse pre-completion automorphism preserves the same valuation.
This follows internally from preservation by the forward equivalence. -/
theorem cyclotomicLambdaWithValRingEquiv59_symm_valuation
    (sigma : GaloisIndex59) (x : LambdaWithVal59 K) :
    Valued.v ((cyclotomicLambdaWithValRingEquiv59 K sigma).symm x) =
      Valued.v x := by
  have h := cyclotomicLambdaWithValRingEquiv59_valuation K sigma
    ((cyclotomicLambdaWithValRingEquiv59 K sigma).symm x)
  simpa using h.symm

/-- The inverse also preserves every basic lambda-adic neighborhood. -/
theorem cyclotomicLambdaWithValRingEquiv59_symm_uniformContinuous
    (sigma : GaloisIndex59) :
    UniformContinuous (cyclotomicLambdaWithValRingEquiv59 K sigma).symm := by
  refine uniformContinuous_of_continuousAt_zero _ ?_
  simp_rw [ContinuousAt, map_zero,
    (Valued.hasBasis_nhds_zero _ _).tendsto_iff
      (Valued.hasBasis_nhds_zero _ _),
    true_and, forall_const]
  intro gamma
  refine ⟨gamma, ?_⟩
  intro x hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  rw [Valuation.restrict_lt_iff_lt_embedding] at hx ⊢
  simpa only [cyclotomicLambdaWithValRingEquiv59_symm_valuation] using hx

/-- Continuous inverse spelling consumed by `Completion.mapRingEquiv`. -/
theorem cyclotomicLambdaWithValRingEquiv59_symm_continuous
    (sigma : GaloisIndex59) :
    Continuous (cyclotomicLambdaWithValRingEquiv59 K sigma).symm :=
  (cyclotomicLambdaWithValRingEquiv59_symm_uniformContinuous K sigma).continuous

/-! ## The actual automorphism of the lambda-adic completion -/

/-- The genuine cyclotomic ring automorphism of the completed local field. -/
noncomputable def cyclotomicLambdaCompletionRingEquiv59
    (sigma : GaloisIndex59) :
    LambdaLocalField59 K ≃+* LambdaLocalField59 K :=
  UniformSpace.Completion.mapRingEquiv
    (cyclotomicLambdaWithValRingEquiv59 K sigma)
    (cyclotomicLambdaWithValRingEquiv59_continuous K sigma)
    (cyclotomicLambdaWithValRingEquiv59_symm_continuous K sigma)

/-- The completed automorphism really extends the original cyclotomic field
automorphism along the canonical localization map. -/
@[simp]
theorem cyclotomicLambdaCompletionRingEquiv59_lambdaLocalization
    (sigma : GaloisIndex59) (x : K) :
    cyclotomicLambdaCompletionRingEquiv59 K sigma
        (lambdaLocalization59 K x) =
      lambdaLocalization59 K (cyclotomicFieldRingEquiv59 K sigma x) := by
  change UniformSpace.Completion.map
      (cyclotomicLambdaWithValRingEquiv59 K sigma)
      (↑(WithVal.toVal ((lambdaPlace59 K).valuation K) x)) =
    ↑(WithVal.toVal ((lambdaPlace59 K).valuation K)
      (cyclotomicFieldRingEquiv59 K sigma x))
  rw [UniformSpace.Completion.map_coe
    (cyclotomicLambdaWithValRingEquiv59_uniformContinuous K sigma)]
  rfl

@[simp]
theorem cyclotomicLambdaCompletionRingEquiv59_one :
    cyclotomicLambdaCompletionRingEquiv59 K 1 =
      RingEquiv.refl (LambdaLocalField59 K) := by
  apply RingEquiv.ext
  intro x
  change UniformSpace.Completion.map
      (cyclotomicLambdaWithValRingEquiv59 K 1) x = x
  rw [cyclotomicLambdaWithValRingEquiv59_one]
  exact congrFun
    (UniformSpace.Completion.map_id
      (α := LambdaWithVal59 K)) x

/-- The completed automorphisms retain the cyclotomic composition law. -/
theorem cyclotomicLambdaCompletionRingEquiv59_mul_apply
    (sigma tau : GaloisIndex59) (x : LambdaLocalField59 K) :
    cyclotomicLambdaCompletionRingEquiv59 K (sigma * tau) x =
      cyclotomicLambdaCompletionRingEquiv59 K sigma
        (cyclotomicLambdaCompletionRingEquiv59 K tau x) := by
  change UniformSpace.Completion.map
      (cyclotomicLambdaWithValRingEquiv59 K (sigma * tau)) x =
    UniformSpace.Completion.map
      (cyclotomicLambdaWithValRingEquiv59 K sigma)
      (UniformSpace.Completion.map
        (cyclotomicLambdaWithValRingEquiv59 K tau) x)
  rw [cyclotomicLambdaWithValRingEquiv59_mul]
  have hcomp := congrFun
    (UniformSpace.Completion.map_comp
      (cyclotomicLambdaWithValRingEquiv59_uniformContinuous K sigma)
      (cyclotomicLambdaWithValRingEquiv59_uniformContinuous K tau)) x
  simpa [Function.comp_def] using hcomp.symm

theorem cyclotomicLambdaCompletionRingEquiv59_mul
    (sigma tau : GaloisIndex59) :
    cyclotomicLambdaCompletionRingEquiv59 K (sigma * tau) =
      (cyclotomicLambdaCompletionRingEquiv59 K tau).trans
        (cyclotomicLambdaCompletionRingEquiv59 K sigma) := by
  apply RingEquiv.ext
  exact cyclotomicLambdaCompletionRingEquiv59_mul_apply K sigma tau

/-! ## Kernel-trust audit -/

/--
info: 'Fermat.FiftyNine.Conservation.LambdaCyclotomicCompletionAction59.cyclotomicPlaceEquiv59_lambdaPlace59' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cyclotomicPlaceEquiv59_lambdaPlace59

/--
info: 'Fermat.FiftyNine.Conservation.LambdaCyclotomicCompletionAction59.cyclotomicLambdaWithValRingEquiv59_uniformContinuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cyclotomicLambdaWithValRingEquiv59_uniformContinuous

/--
info: 'Fermat.FiftyNine.Conservation.LambdaCyclotomicCompletionAction59.cyclotomicLambdaCompletionRingEquiv59_lambdaLocalization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cyclotomicLambdaCompletionRingEquiv59_lambdaLocalization

/--
info: 'Fermat.FiftyNine.Conservation.LambdaCyclotomicCompletionAction59.cyclotomicLambdaCompletionRingEquiv59_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cyclotomicLambdaCompletionRingEquiv59_mul

end Fermat.FiftyNine.Conservation.LambdaCyclotomicCompletionAction59
