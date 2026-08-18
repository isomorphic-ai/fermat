/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Cyclotomic naturality of global-unit Selmer lifts at 59

The cyclotomic action on the ring of integers preserves global units and
59th powers.  It therefore descends to the actual group of global units
modulo 59th powers.  This file proves that Mathlib's `fromUnitLift` map
intertwines that descended action with the genuine strict Selmer action.

Thus an equation-(8) coefficient unit remains the coefficient unit of the
transported Kummer class; no new representative or naturality certificate
is supplied.
-/
import Fermat.FiftyNine.Conservation.FermatStatePrimalUnitProjection59
import Mathlib.RepresentationTheory.Intertwining

open scoped MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Fermat.FiftyNine.Conservation.CyclotomicUnitSelmerNaturality59

open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

/-! ## The descended action on global units modulo 59th powers -/

/-- The cyclotomic ring automorphism, restricted to global units. -/
noncomputable def cyclotomicRingUnitMulEquiv59
    (sigma : GaloisIndex59) :
    (NumberField.RingOfIntegers K)ˣ ≃*
      (NumberField.RingOfIntegers K)ˣ :=
  Units.mapEquiv
    (KummerCriterion.cyclotomicRingOfIntegersEquiv
      (p := 59) K sigma).toMulEquiv

/-- Cyclotomic transport carries the subgroup of 59th powers onto itself. -/
theorem cyclotomicRingUnitMulEquiv59_powRange
    (sigma : GaloisIndex59) :
    Subgroup.map (cyclotomicRingUnitMulEquiv59 K sigma)
        (powMonoidHom 59 :
          (NumberField.RingOfIntegers K)ˣ →*
            (NumberField.RingOfIntegers K)ˣ).range =
      (powMonoidHom 59 :
        (NumberField.RingOfIntegers K)ˣ →*
          (NumberField.RingOfIntegers K)ˣ).range := by
  ext u
  constructor
  · rintro ⟨v, ⟨w, rfl⟩, rfl⟩
    exact ⟨cyclotomicRingUnitMulEquiv59 K sigma w, by simp⟩
  · rintro ⟨w, rfl⟩
    refine ⟨(cyclotomicRingUnitMulEquiv59 K sigma).symm w ^ 59,
      ⟨(cyclotomicRingUnitMulEquiv59 K sigma).symm w, rfl⟩, ?_⟩
    simp

/-- The induced multiplicative automorphism of global units modulo 59th
powers. -/
noncomputable def cyclotomicUnitModPMulEquiv59
    (sigma : GaloisIndex59) :
    ((NumberField.RingOfIntegers K)ˣ ⧸
      (powMonoidHom 59 :
        (NumberField.RingOfIntegers K)ˣ →*
          (NumberField.RingOfIntegers K)ˣ).range) ≃*
    ((NumberField.RingOfIntegers K)ˣ ⧸
      (powMonoidHom 59 :
        (NumberField.RingOfIntegers K)ˣ →*
          (NumberField.RingOfIntegers K)ˣ).range) :=
  QuotientGroup.congr _ _ (cyclotomicRingUnitMulEquiv59 K sigma)
    (cyclotomicRingUnitMulEquiv59_powRange K sigma)

/-- Computation of the quotient action on a represented global unit. -/
@[simp]
theorem cyclotomicUnitModPMulEquiv59_mk
    (sigma : GaloisIndex59)
    (u : (NumberField.RingOfIntegers K)ˣ) :
    cyclotomicUnitModPMulEquiv59 K sigma (QuotientGroup.mk u) =
      QuotientGroup.mk (cyclotomicRingUnitMulEquiv59 K sigma u) := by
  exact QuotientGroup.quotientMulEquivOfEq_mk
    (cyclotomicRingUnitMulEquiv59_powRange K sigma) _

/-- The same descended automorphism in the additive notation used by the
unit--Selmer exact sequence. -/
noncomputable def cyclotomicUnitModPAddEquiv59
    (sigma : GaloisIndex59) :
    UnitModP (NumberField.RingOfIntegers K) 59 ≃+
      UnitModP (NumberField.RingOfIntegers K) 59 :=
  (cyclotomicUnitModPMulEquiv59 K sigma).toAdditive

/-- The descended action at the identity is the identity. -/
@[simp]
theorem cyclotomicUnitModPAddEquiv59_one_apply
    (u : UnitModP (NumberField.RingOfIntegers K) 59) :
    cyclotomicUnitModPAddEquiv59 K 1 u = u := by
  obtain ⟨epsilon, hepsilon⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom 59 :
      (NumberField.RingOfIntegers K)ˣ →*
        (NumberField.RingOfIntegers K)ˣ).range (Additive.toMul u)
  have hu : u = Additive.ofMul (QuotientGroup.mk epsilon) := by
    apply Additive.toMul.injective
    exact hepsilon.symm
  rw [hu]
  apply Additive.toMul.injective
  change cyclotomicUnitModPMulEquiv59 K 1 (QuotientGroup.mk epsilon) =
    QuotientGroup.mk epsilon
  rw [cyclotomicUnitModPMulEquiv59_mk]
  apply congrArg QuotientGroup.mk
  apply Units.ext
  change KummerCriterion.cyclotomicRingOfIntegersEquiv
      (p := 59) K 1 (epsilon : NumberField.RingOfIntegers K) = epsilon
  exact KummerCriterion.cyclotomicRingOfIntegersEquiv_one_apply
    (p := 59) (K := K) epsilon

/-- Multiplication in the Galois index acts by composition, in the same
order as the strict Selmer representation. -/
theorem cyclotomicUnitModPAddEquiv59_mul_apply
    (sigma tau : GaloisIndex59)
    (u : UnitModP (NumberField.RingOfIntegers K) 59) :
    cyclotomicUnitModPAddEquiv59 K (sigma * tau) u =
      cyclotomicUnitModPAddEquiv59 K sigma
        (cyclotomicUnitModPAddEquiv59 K tau u) := by
  obtain ⟨epsilon, hepsilon⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom 59 :
      (NumberField.RingOfIntegers K)ˣ →*
        (NumberField.RingOfIntegers K)ˣ).range (Additive.toMul u)
  have hu : u = Additive.ofMul (QuotientGroup.mk epsilon) := by
    apply Additive.toMul.injective
    exact hepsilon.symm
  rw [hu]
  apply Additive.toMul.injective
  change cyclotomicUnitModPMulEquiv59 K (sigma * tau)
      (QuotientGroup.mk epsilon) =
    cyclotomicUnitModPMulEquiv59 K sigma
      (cyclotomicUnitModPMulEquiv59 K tau (QuotientGroup.mk epsilon))
  rw [cyclotomicUnitModPMulEquiv59_mk,
    cyclotomicUnitModPMulEquiv59_mk,
    cyclotomicUnitModPMulEquiv59_mk]
  apply congrArg QuotientGroup.mk
  apply Units.ext
  change KummerCriterion.cyclotomicRingOfIntegersEquiv
      (p := 59) K (sigma * tau)
        (epsilon : NumberField.RingOfIntegers K) =
    KummerCriterion.cyclotomicRingOfIntegersEquiv (p := 59) K sigma
      (KummerCriterion.cyclotomicRingOfIntegersEquiv (p := 59) K tau
        (epsilon : NumberField.RingOfIntegers K))
  exact KummerCriterion.cyclotomicRingOfIntegersEquiv_mul_apply
    (p := 59) (K := K) sigma tau epsilon

/-! ## The genuine representation on unit classes -/

omit [NumberField K] [IsCyclotomicExtension {59} ℚ K] in
/-- Global units modulo 59th powers are killed by 59. -/
theorem unitModP59_nsmul_eq_zero
    (u : UnitModP (NumberField.RingOfIntegers K) 59) :
    59 • u = 0 := by
  obtain ⟨epsilon, hepsilon⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom 59 :
      (NumberField.RingOfIntegers K)ˣ →*
        (NumberField.RingOfIntegers K)ˣ).range (Additive.toMul u)
  have hu : u = Additive.ofMul (QuotientGroup.mk epsilon) := by
    apply Additive.toMul.injective
    exact hepsilon.symm
  rw [hu]
  apply Additive.toMul.injective
  change ((QuotientGroup.mk epsilon :
      (NumberField.RingOfIntegers K)ˣ ⧸
        (powMonoidHom 59 :
          (NumberField.RingOfIntegers K)ˣ →*
            (NumberField.RingOfIntegers K)ˣ).range) ^ 59) = 1
  rw [← QuotientGroup.mk_pow]
  exact (QuotientGroup.eq_one_iff _).2 ⟨epsilon, rfl⟩

local instance instUnitModP59ModuleZMod :
    Module (ZMod 59) (UnitModP (NumberField.RingOfIntegers K) 59) :=
  AddCommGroup.zmodModule (unitModP59_nsmul_eq_zero K)

local instance instUnitModP59ModulePadicInt :
    Module (PadicInt 59) (UnitModP (NumberField.RingOfIntegers K) 59) :=
  Module.compHom _ PadicInt.toZMod

/-- One cyclotomic automorphism as an additive homomorphism of unit
classes. -/
noncomputable def cyclotomicUnitModPAddHom59
    (sigma : GaloisIndex59) :
    UnitModP (NumberField.RingOfIntegers K) 59 →+
      UnitModP (NumberField.RingOfIntegers K) 59 :=
  (cyclotomicUnitModPAddEquiv59 K sigma).toAddMonoidHom

/-- The descended unit-class action is linear over integral 59-adic
coefficients. -/
noncomputable def cyclotomicUnitModPLinearMap59
    (sigma : GaloisIndex59) :
    UnitModP (NumberField.RingOfIntegers K) 59 →ₗ[PadicInt 59]
      UnitModP (NumberField.RingOfIntegers K) 59 where
  toFun := cyclotomicUnitModPAddHom59 K sigma
  map_add' := map_add _
  map_smul' a u := by
    change cyclotomicUnitModPAddHom59 K sigma
        (PadicInt.toZMod a • u) =
      PadicInt.toZMod a • cyclotomicUnitModPAddHom59 K sigma u
    exact ZMod.map_smul (cyclotomicUnitModPAddHom59 K sigma)
      (PadicInt.toZMod a) u

/-- The genuine cyclotomic representation on global units modulo 59th
powers. -/
noncomputable def cyclotomicUnitModPRepresentation59 :
    Representation (PadicInt 59) GaloisIndex59
      (UnitModP (NumberField.RingOfIntegers K) 59) where
  toFun sigma := cyclotomicUnitModPLinearMap59 K sigma
  map_one' := by
    apply LinearMap.ext
    intro u
    exact cyclotomicUnitModPAddEquiv59_one_apply K u
  map_mul' sigma tau := by
    apply LinearMap.ext
    intro u
    exact cyclotomicUnitModPAddEquiv59_mul_apply K sigma tau u

/-! ## Naturality of the actual unit lift -/

/-- Embedding a transported ring unit into the field is the same as first
embedding it and then applying the cyclotomic field automorphism. -/
theorem cyclotomicRingUnitMulEquiv59_map_algebraMap
    (sigma : GaloisIndex59)
    (epsilon : (NumberField.RingOfIntegers K)ˣ) :
    Units.map (algebraMap (NumberField.RingOfIntegers K) K)
        (cyclotomicRingUnitMulEquiv59 K sigma epsilon) =
      cyclotomicUnitEquiv59 K sigma
        (Units.map (algebraMap (NumberField.RingOfIntegers K) K)
          epsilon) := by
  apply Units.ext
  change ((KummerCriterion.cyclotomicSigmaOfUnit
      (p := 59) K sigma •
        (epsilon : NumberField.RingOfIntegers K)) : K) =
    KummerCriterion.cyclotomicSigmaOfUnit (p := 59) K sigma
      ((epsilon : NumberField.RingOfIntegers K) : K)
  exact algebraMap.coe_smul'
    (KummerCriterion.cyclotomicSigmaOfUnit (p := 59) K sigma)
    (epsilon : NumberField.RingOfIntegers K) K

/-- Mathlib's genuine units-to-Selmer map commutes with each cyclotomic
automorphism.  The equality is on the actual strict Selmer subtype, not only
on its ambient Kummer quotient. -/
theorem unitInclusion_cyclotomicUnitModPAddEquiv59
    (sigma : GaloisIndex59)
    (u : UnitModP (NumberField.RingOfIntegers K) 59) :
    unitInclusion
        (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
        (cyclotomicUnitModPAddEquiv59 K sigma u) =
      cyclotomicStrictSelmerRepresentation59 K sigma
        (unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59) u) := by
  obtain ⟨epsilon, hepsilon⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom 59 :
      (NumberField.RingOfIntegers K)ˣ →*
        (NumberField.RingOfIntegers K)ˣ).range (Additive.toMul u)
  have hu : u = Additive.ofMul (QuotientGroup.mk epsilon) := by
    apply Additive.toMul.injective
    exact hepsilon.symm
  rw [hu]
  apply Additive.toMul.injective
  apply Subtype.ext
  change QuotientGroup.mk
      (Units.map (algebraMap (NumberField.RingOfIntegers K) K)
        (cyclotomicRingUnitMulEquiv59 K sigma epsilon)) =
    cyclotomicKummerHom59 K sigma
      (QuotientGroup.mk
        (Units.map (algebraMap (NumberField.RingOfIntegers K) K)
          epsilon))
  rw [cyclotomicRingUnitMulEquiv59_map_algebraMap]
  rfl

/-- Mathlib's unit inclusion, upgraded to a linear map over integral
59-adic coefficients. -/
noncomputable def unitInclusionLinearMap59 :
    UnitModP (NumberField.RingOfIntegers K) 59 →ₗ[PadicInt 59]
      SelmerCarrier (NumberField.RingOfIntegers K) K 59 where
  toFun := unitInclusion
    (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
  map_add' := map_add _
  map_smul' a u := by
    change unitInclusion
        (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
        (PadicInt.toZMod a • u) =
      PadicInt.toZMod a •
        unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59) u
    exact ZMod.map_smul
      (unitInclusion
        (R := NumberField.RingOfIntegers K) (K := K) (p := 59))
      (PadicInt.toZMod a) u

/-- The linear unit inclusion intertwines the genuine unit-class and strict
Selmer representations. -/
noncomputable def unitInclusionIntertwiner59 :
    Representation.IntertwiningMap
      (cyclotomicUnitModPRepresentation59 K)
      (cyclotomicStrictSelmerRepresentation59 K) :=
  (unitInclusionLinearMap59 K).intertwiningMap_of_isIntertwiningMap
    (cyclotomicUnitModPRepresentation59 K)
    (cyclotomicStrictSelmerRepresentation59 K) <| by
      intro sigma u
      exact unitInclusion_cyclotomicUnitModPAddEquiv59 K sigma u

/-- The character-idempotent action on actual global units modulo 59th
powers. -/
noncomputable def cyclotomicUnitProjector59
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (eta : Fermat.Conservation.InvolutiveBase.Character
      (PadicInt 59) GaloisIndex59) :
    UnitModP (NumberField.RingOfIntegers K) 59 →ₗ[PadicInt 59]
      UnitModP (NumberField.RingOfIntegers K) 59 :=
  (cyclotomicUnitModPRepresentation59 K).asAlgebraHom
    (Fermat.Conservation.InvolutiveBase.characterIdempotent eta)

/-- Strong projector naturality: including a projected global-unit class
is exactly the strict-Selmer character projection of its included class. -/
theorem unitInclusionLinearMap59_characterProjector
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (eta : Fermat.Conservation.InvolutiveBase.Character
      (PadicInt 59) GaloisIndex59)
    (u : UnitModP (NumberField.RingOfIntegers K) 59) :
    unitInclusionLinearMap59 K (cyclotomicUnitProjector59 K eta u) =
      (characterProjectorAt
        (cyclotomicStrictSelmerRepresentation59 K) eta
        (unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59) u)).1 := by
  change unitInclusionLinearMap59 K
      ((cyclotomicUnitModPRepresentation59 K).asAlgebraHom
        (Fermat.Conservation.InvolutiveBase.characterIdempotent eta) u) =
    (cyclotomicStrictSelmerRepresentation59 K).asAlgebraHom
      (Fermat.Conservation.InvolutiveBase.characterIdempotent eta)
      (unitInclusionLinearMap59 K u)
  let F :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      (cyclotomicUnitModPRepresentation59 K)
      (cyclotomicStrictSelmerRepresentation59 K))
      (unitInclusionIntertwiner59 K)
  exact F.map_smul
    (Fermat.Conservation.InvolutiveBase.characterIdempotent eta) u

/-! ## Equation-(8) coefficient units under the actual action -/

open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.FermatFactorSelmerSource59
open Fermat.FiftyNine.Conservation.FermatState
open Fermat.FiftyNine.Conservation.FermatStatePrimalUnitProjection59
open Fermat.FiftyNine.Conservation.FermatStateSelmerUnitLifts59
open Fermat.FiftyNine.Conservation.StateFactorPair

variable {L : Type} [Field L] [NumberField L]
  [IsCyclotomicExtension {59} ℚ L]
  {zeta : L} {hZeta : IsPrimitiveRoot zeta 59}
  {S : PrimitiveSecondCaseSolution} {hz : (59 : ℤ) ∣ S.z}

/-- Every cyclotomic transport of the concrete plus equation-(8)
coefficient unit is an explicit unit lift of the correspondingly transported
Fermat-factor Selmer source. -/
theorem exists_cyclotomicTransport_explicitUnitLift_fermatPlusStrictSelmer59
    (sigma : GaloisIndex59)
    (pair : StateLinkedIdealPair hZeta S hz) :
    ∃ (rho : NumberField.RingOfIntegers L)
        (epsilon : (NumberField.RingOfIntegers L)ˣ),
      pair.plusIdeal = Ideal.span {rho} ∧
      normalizedPlusFactor hZeta S hz = epsilon * rho ^ 59 ∧
      unitInclusion
          (R := NumberField.RingOfIntegers L) (K := L) (p := 59)
          (cyclotomicUnitModPAddEquiv59 L sigma
            (Additive.ofMul (QuotientGroup.mk epsilon))) =
        cyclotomicStrictSelmerRepresentation59 L sigma
          (fermatPlusStrictSelmer59 pair) := by
  obtain ⟨rho, epsilon, hideal, heq, hlift⟩ :=
    exists_explicitUnitLift_fermatPlusStrictSelmer59 pair
  refine ⟨rho, epsilon, hideal, heq, ?_⟩
  rw [unitInclusion_cyclotomicUnitModPAddEquiv59, hlift]

/-- The analogous arbitrary cyclotomic transport statement for the minus
equation-(8) coefficient unit. -/
theorem exists_cyclotomicTransport_explicitUnitLift_fermatMinusStrictSelmer59
    (sigma : GaloisIndex59)
    (pair : StateLinkedIdealPair hZeta S hz) :
    ∃ (rho : NumberField.RingOfIntegers L)
        (epsilon : (NumberField.RingOfIntegers L)ˣ),
      pair.minusIdeal = Ideal.span {rho} ∧
      normalizedMinusFactor hZeta S hz = epsilon * rho ^ 59 ∧
      unitInclusion
          (R := NumberField.RingOfIntegers L) (K := L) (p := 59)
          (cyclotomicUnitModPAddEquiv59 L sigma
            (Additive.ofMul (QuotientGroup.mk epsilon))) =
        cyclotomicStrictSelmerRepresentation59 L sigma
          (fermatMinusStrictSelmer59 pair) := by
  obtain ⟨rho, epsilon, hideal, heq, hlift⟩ :=
    exists_explicitUnitLift_fermatMinusStrictSelmer59 pair
  refine ⟨rho, epsilon, hideal, heq, ?_⟩
  rw [unitInclusion_cyclotomicUnitModPAddEquiv59, hlift]

/-- The concrete plus coefficient unit can be projected on the unit side;
its image is exactly the actual plus irregular Fermat mode. -/
theorem exists_explicitUnitProjector_fermatPlusPrimalMode59
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (pair : StateLinkedIdealPair hZeta S hz) :
    ∃ (rho : NumberField.RingOfIntegers L)
        (epsilon : (NumberField.RingOfIntegers L)ˣ),
      pair.plusIdeal = Ideal.span {rho} ∧
      normalizedPlusFactor hZeta S hz = epsilon * rho ^ 59 ∧
      unitInclusionLinearMap59 L
          (cyclotomicUnitProjector59 L irregularCharacter59
            (Additive.ofMul (QuotientGroup.mk epsilon))) =
        (fermatPlusPrimalMode59 pair).1 := by
  obtain ⟨rho, epsilon, hideal, heq, hprojection⟩ :=
    exists_explicitUnitProjection_fermatPlusPrimalMode59 pair
  refine ⟨rho, epsilon, hideal, heq, ?_⟩
  calc
    unitInclusionLinearMap59 L
        (cyclotomicUnitProjector59 L irregularCharacter59
          (Additive.ofMul (QuotientGroup.mk epsilon))) =
        (characterProjectorAt
          (cyclotomicStrictSelmerRepresentation59 L) irregularCharacter59
          (unitInclusion
            (R := NumberField.RingOfIntegers L) (K := L) (p := 59)
            (Additive.ofMul (QuotientGroup.mk epsilon)))).1 :=
      unitInclusionLinearMap59_characterProjector L irregularCharacter59 _
    _ = (fermatPlusPrimalMode59 pair).1 := congrArg Subtype.val hprojection

/-- The concrete minus coefficient unit projects on the unit side to the
actual minus irregular Fermat mode. -/
theorem exists_explicitUnitProjector_fermatMinusPrimalMode59
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (pair : StateLinkedIdealPair hZeta S hz) :
    ∃ (rho : NumberField.RingOfIntegers L)
        (epsilon : (NumberField.RingOfIntegers L)ˣ),
      pair.minusIdeal = Ideal.span {rho} ∧
      normalizedMinusFactor hZeta S hz = epsilon * rho ^ 59 ∧
      unitInclusionLinearMap59 L
          (cyclotomicUnitProjector59 L irregularCharacter59
            (Additive.ofMul (QuotientGroup.mk epsilon))) =
        (fermatMinusPrimalMode59 pair).1 := by
  obtain ⟨rho, epsilon, hideal, heq, hprojection⟩ :=
    exists_explicitUnitProjection_fermatMinusPrimalMode59 pair
  refine ⟨rho, epsilon, hideal, heq, ?_⟩
  calc
    unitInclusionLinearMap59 L
        (cyclotomicUnitProjector59 L irregularCharacter59
          (Additive.ofMul (QuotientGroup.mk epsilon))) =
        (characterProjectorAt
          (cyclotomicStrictSelmerRepresentation59 L) irregularCharacter59
          (unitInclusion
            (R := NumberField.RingOfIntegers L) (K := L) (p := 59)
            (Additive.ofMul (QuotientGroup.mk epsilon)))).1 :=
      unitInclusionLinearMap59_characterProjector L irregularCharacter59 _
    _ = (fermatMinusPrimalMode59 pair).1 := congrArg Subtype.val hprojection

end Fermat.FiftyNine.Conservation.CyclotomicUnitSelmerNaturality59
