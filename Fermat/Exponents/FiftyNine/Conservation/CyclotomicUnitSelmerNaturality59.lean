/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The 59-adapter for cyclotomic unit--Selmer naturality

This file specializes the prime-generic unit action, representation,
unit-inclusion intertwiner, and character-projector naturality at `p = 59`.
The only proof bodies retained here are the four equation-(8) state adapters.
-/
import Fermat.Experiments.Conservation.PrimeCyclotomicUnitSelmerNaturality
import Fermat.Exponents.FiftyNine.Conservation.FermatStatePrimalUnitProjection59

open scoped MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Fermat.FiftyNine.Conservation.CyclotomicUnitSelmerNaturality59

open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.PrimeCyclotomicUnitSelmerNaturality
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

/-! ## The prime-generic unit action specialized at 59 -/

/-- The cyclotomic ring automorphism, restricted to global units. -/
noncomputable abbrev cyclotomicRingUnitMulEquiv59
    (sigma : GaloisIndex59) : (𝓞 K)ˣ ≃* (𝓞 K)ˣ :=
  cyclotomicRingUnitMulEquiv 59 K sigma

/-- Cyclotomic transport carries the subgroup of 59th powers onto itself. -/
theorem cyclotomicRingUnitMulEquiv59_powRange
    (sigma : GaloisIndex59) :
    Subgroup.map (cyclotomicRingUnitMulEquiv59 K sigma)
        (powMonoidHom 59 : (𝓞 K)ˣ →* (𝓞 K)ˣ).range =
      (powMonoidHom 59 : (𝓞 K)ˣ →* (𝓞 K)ˣ).range :=
  cyclotomicRingUnitMulEquiv_powRange 59 K sigma

/-- The induced multiplicative automorphism of global units modulo 59th
powers. -/
noncomputable abbrev cyclotomicUnitModPMulEquiv59
    (sigma : GaloisIndex59) :
    ((𝓞 K)ˣ ⧸ (powMonoidHom 59 : (𝓞 K)ˣ →* (𝓞 K)ˣ).range) ≃*
      ((𝓞 K)ˣ ⧸ (powMonoidHom 59 : (𝓞 K)ˣ →* (𝓞 K)ˣ).range) :=
  cyclotomicUnitModPMulEquiv 59 K sigma

/-- Computation of the quotient action on a represented global unit. -/
@[simp]
theorem cyclotomicUnitModPMulEquiv59_mk
    (sigma : GaloisIndex59) (u : (𝓞 K)ˣ) :
    cyclotomicUnitModPMulEquiv59 K sigma (QuotientGroup.mk u) =
      QuotientGroup.mk (cyclotomicRingUnitMulEquiv59 K sigma u) :=
  cyclotomicUnitModPMulEquiv_mk 59 K sigma u

/-- The same descended automorphism in the additive notation used by the
unit--Selmer exact sequence. -/
noncomputable abbrev cyclotomicUnitModPAddEquiv59
    (sigma : GaloisIndex59) :
    UnitModP (𝓞 K) 59 ≃+ UnitModP (𝓞 K) 59 :=
  cyclotomicUnitModPAddEquiv 59 K sigma

/-- The descended action at the identity is the identity. -/
@[simp]
theorem cyclotomicUnitModPAddEquiv59_one_apply
    (u : UnitModP (𝓞 K) 59) :
    cyclotomicUnitModPAddEquiv59 K 1 u = u :=
  cyclotomicUnitModPAddEquiv_one_apply 59 K u

/-- Multiplication in the Galois index acts by composition, in the same
order as the strict Selmer representation. -/
theorem cyclotomicUnitModPAddEquiv59_mul_apply
    (sigma tau : GaloisIndex59)
    (u : UnitModP (𝓞 K) 59) :
    cyclotomicUnitModPAddEquiv59 K (sigma * tau) u =
      cyclotomicUnitModPAddEquiv59 K sigma
        (cyclotomicUnitModPAddEquiv59 K tau u) :=
  cyclotomicUnitModPAddEquiv_mul_apply 59 K sigma tau u

/-! ## The genuine representation on unit classes -/

omit [NumberField K] [IsCyclotomicExtension {59} ℚ K] in
/-- Global units modulo 59th powers are killed by 59. -/
theorem unitModP59_nsmul_eq_zero
    (u : UnitModP (𝓞 K) 59) : 59 • u = 0 :=
  unitModP_nsmul_eq_zero 59 K u

local instance instUnitModP59ModuleZMod :
    Module (ZMod 59) (UnitModP (𝓞 K) 59) :=
  instUnitModPModuleZMod 59 K

local instance instUnitModP59ModulePadicInt :
    Module (PadicInt 59) (UnitModP (𝓞 K) 59) :=
  instUnitModPModulePadicInt 59 K

/-- One cyclotomic automorphism as an additive homomorphism of unit
classes. -/
noncomputable abbrev cyclotomicUnitModPAddHom59
    (sigma : GaloisIndex59) :
    UnitModP (𝓞 K) 59 →+ UnitModP (𝓞 K) 59 :=
  cyclotomicUnitModPAddHom 59 K sigma

/-- The descended unit-class action is linear over integral 59-adic
coefficients. -/
noncomputable abbrev cyclotomicUnitModPLinearMap59
    (sigma : GaloisIndex59) :
    UnitModP (𝓞 K) 59 →ₗ[PadicInt 59] UnitModP (𝓞 K) 59 :=
  cyclotomicUnitModPLinearMap 59 K sigma

/-- The genuine cyclotomic representation on global units modulo 59th
powers. -/
noncomputable abbrev cyclotomicUnitModPRepresentation59 :
    Representation (PadicInt 59) GaloisIndex59
      (UnitModP (𝓞 K) 59) :=
  cyclotomicUnitModPRepresentation 59 K

/-! ## Naturality of the actual unit lift -/

/-- Embedding a transported ring unit into the field is the same as first
embedding it and then applying the cyclotomic field automorphism. -/
theorem cyclotomicRingUnitMulEquiv59_map_algebraMap
    (sigma : GaloisIndex59)
    (epsilon : (𝓞 K)ˣ) :
    Units.map (algebraMap (𝓞 K) K)
        (cyclotomicRingUnitMulEquiv59 K sigma epsilon) =
      cyclotomicUnitEquiv59 K sigma
        (Units.map (algebraMap (𝓞 K) K) epsilon) :=
  cyclotomicRingUnitMulEquiv_map_algebraMap 59 K sigma epsilon

/-- Mathlib's genuine units-to-Selmer map commutes with each cyclotomic
automorphism.  The equality is on the actual strict Selmer subtype, not only
on its ambient Kummer quotient. -/
theorem unitInclusion_cyclotomicUnitModPAddEquiv59
    (sigma : GaloisIndex59)
    (u : UnitModP (𝓞 K) 59) :
    unitInclusion (R := 𝓞 K) (K := K) (p := 59)
        (cyclotomicUnitModPAddEquiv59 K sigma u) =
      cyclotomicStrictSelmerRepresentation59 K sigma
        (unitInclusion (R := 𝓞 K) (K := K) (p := 59) u) :=
  unitInclusion_cyclotomicUnitModPAddEquiv 59 K sigma u

/-- Mathlib's unit inclusion, upgraded to a linear map over integral
59-adic coefficients. -/
noncomputable abbrev unitInclusionLinearMap59 :
    UnitModP (𝓞 K) 59 →ₗ[PadicInt 59] SelmerCarrier (𝓞 K) K 59 :=
  unitInclusionLinearMap 59 K

/-- The linear unit inclusion intertwines the genuine unit-class and strict
Selmer representations. -/
noncomputable abbrev unitInclusionIntertwiner59 :
    Representation.IntertwiningMap
      (cyclotomicUnitModPRepresentation59 K)
      (cyclotomicStrictSelmerRepresentation59 K) :=
  unitInclusionIntertwiner 59 K

/-- The character-idempotent action on actual global units modulo 59th
powers. -/
noncomputable abbrev cyclotomicUnitProjector59
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (eta : Fermat.Conservation.InvolutiveBase.Character
      (PadicInt 59) GaloisIndex59) :
    UnitModP (𝓞 K) 59 →ₗ[PadicInt 59] UnitModP (𝓞 K) 59 :=
  cyclotomicUnitProjector 59 K eta

/-- Strong projector naturality: including a projected global-unit class
is exactly the strict-Selmer character projection of its included class. -/
theorem unitInclusionLinearMap59_characterProjector
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (eta : Fermat.Conservation.InvolutiveBase.Character
      (PadicInt 59) GaloisIndex59)
    (u : UnitModP (𝓞 K) 59) :
    unitInclusionLinearMap59 K (cyclotomicUnitProjector59 K eta u) =
      (characterProjectorAt
        (cyclotomicStrictSelmerRepresentation59 K) eta
        (unitInclusion (R := 𝓞 K) (K := K) (p := 59) u)).1 :=
  unitInclusionLinearMap_characterProjector 59 K eta u

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
