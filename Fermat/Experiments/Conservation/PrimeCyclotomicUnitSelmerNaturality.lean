/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Prime-generic cyclotomic naturality of global-unit Selmer lifts

For a prime `p`, the canonical cyclotomic action on the ring of integers
preserves global units and `p`-th powers.  This file descends that action to
global units modulo `p`-th powers and proves that Mathlib's actual
`unitInclusion` map intertwines it with the canonical strict Selmer action.

The same intertwiner proves naturality for every character projector.  No
prime-specific state or character is selected here.
-/
import Fermat.Experiments.Conservation.CommonActionSelmerCore
import Fermat.Experiments.Conservation.PrimeCyclotomicSelmerAction
import Mathlib.RepresentationTheory.Intertwining

open scoped MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Fermat.Conservation.PrimeCyclotomicUnitSelmerNaturality

open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.PrimeCyclotomicSelmerAction

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]

local instance : Fact (0 < p) := ⟨(Fact.out : Nat.Prime p).pos⟩

/-! ## The descended action on global units modulo `p`-th powers -/

/-- The cyclotomic ring automorphism restricted to global units. -/
noncomputable def cyclotomicRingUnitMulEquiv
    (sigma : KummerCriterion.CyclotomicUnitDelta p) :
    (𝓞 K)ˣ ≃* (𝓞 K)ˣ :=
  Units.mapEquiv
    (KummerCriterion.cyclotomicRingOfIntegersEquiv
      (p := p) K sigma).toMulEquiv

/-- Cyclotomic transport carries the subgroup of `p`-th powers onto itself. -/
theorem cyclotomicRingUnitMulEquiv_powRange
    (sigma : KummerCriterion.CyclotomicUnitDelta p) :
    Subgroup.map (cyclotomicRingUnitMulEquiv p K sigma)
        (powMonoidHom p : (𝓞 K)ˣ →* (𝓞 K)ˣ).range =
      (powMonoidHom p : (𝓞 K)ˣ →* (𝓞 K)ˣ).range := by
  ext u
  constructor
  · rintro ⟨v, ⟨w, rfl⟩, rfl⟩
    exact ⟨cyclotomicRingUnitMulEquiv p K sigma w, by simp⟩
  · rintro ⟨w, rfl⟩
    refine ⟨(cyclotomicRingUnitMulEquiv p K sigma).symm w ^ p,
      ⟨(cyclotomicRingUnitMulEquiv p K sigma).symm w, rfl⟩, ?_⟩
    simp

/-- The induced multiplicative automorphism of global units modulo
`p`-th powers. -/
noncomputable def cyclotomicUnitModPMulEquiv
    (sigma : KummerCriterion.CyclotomicUnitDelta p) :
    ((𝓞 K)ˣ ⧸ (powMonoidHom p : (𝓞 K)ˣ →* (𝓞 K)ˣ).range) ≃*
      ((𝓞 K)ˣ ⧸ (powMonoidHom p : (𝓞 K)ˣ →* (𝓞 K)ˣ).range) :=
  QuotientGroup.congr _ _ (cyclotomicRingUnitMulEquiv p K sigma)
    (cyclotomicRingUnitMulEquiv_powRange p K sigma)

/-- Computation of the quotient action on a represented global unit. -/
@[simp]
theorem cyclotomicUnitModPMulEquiv_mk
    (sigma : KummerCriterion.CyclotomicUnitDelta p) (u : (𝓞 K)ˣ) :
    cyclotomicUnitModPMulEquiv p K sigma (QuotientGroup.mk u) =
      QuotientGroup.mk (cyclotomicRingUnitMulEquiv p K sigma u) := by
  exact QuotientGroup.quotientMulEquivOfEq_mk
    (cyclotomicRingUnitMulEquiv_powRange p K sigma) _

/-- The descended automorphism in the additive notation used by the
unit--Selmer exact sequence. -/
noncomputable def cyclotomicUnitModPAddEquiv
    (sigma : KummerCriterion.CyclotomicUnitDelta p) :
    UnitModP (𝓞 K) p ≃+ UnitModP (𝓞 K) p :=
  (cyclotomicUnitModPMulEquiv p K sigma).toAdditive

/-- The descended action at the identity is the identity. -/
@[simp]
theorem cyclotomicUnitModPAddEquiv_one_apply
    (u : UnitModP (𝓞 K) p) :
    cyclotomicUnitModPAddEquiv p K 1 u = u := by
  obtain ⟨epsilon, hepsilon⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom p : (𝓞 K)ˣ →* (𝓞 K)ˣ).range (Additive.toMul u)
  have hu : u = Additive.ofMul (QuotientGroup.mk epsilon) := by
    apply Additive.toMul.injective
    exact hepsilon.symm
  rw [hu]
  apply Additive.toMul.injective
  change cyclotomicUnitModPMulEquiv p K 1 (QuotientGroup.mk epsilon) =
    QuotientGroup.mk epsilon
  rw [cyclotomicUnitModPMulEquiv_mk]
  apply congrArg QuotientGroup.mk
  apply Units.ext
  change KummerCriterion.cyclotomicRingOfIntegersEquiv
      (p := p) K 1 (epsilon : 𝓞 K) = epsilon
  exact KummerCriterion.cyclotomicRingOfIntegersEquiv_one_apply
    (p := p) (K := K) epsilon

/-- Multiplication in the Galois index acts by composition, in the same
order as the strict Selmer representation. -/
theorem cyclotomicUnitModPAddEquiv_mul_apply
    (sigma tau : KummerCriterion.CyclotomicUnitDelta p)
    (u : UnitModP (𝓞 K) p) :
    cyclotomicUnitModPAddEquiv p K (sigma * tau) u =
      cyclotomicUnitModPAddEquiv p K sigma
        (cyclotomicUnitModPAddEquiv p K tau u) := by
  obtain ⟨epsilon, hepsilon⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom p : (𝓞 K)ˣ →* (𝓞 K)ˣ).range (Additive.toMul u)
  have hu : u = Additive.ofMul (QuotientGroup.mk epsilon) := by
    apply Additive.toMul.injective
    exact hepsilon.symm
  rw [hu]
  apply Additive.toMul.injective
  change cyclotomicUnitModPMulEquiv p K (sigma * tau)
      (QuotientGroup.mk epsilon) =
    cyclotomicUnitModPMulEquiv p K sigma
      (cyclotomicUnitModPMulEquiv p K tau (QuotientGroup.mk epsilon))
  rw [cyclotomicUnitModPMulEquiv_mk,
    cyclotomicUnitModPMulEquiv_mk,
    cyclotomicUnitModPMulEquiv_mk]
  apply congrArg QuotientGroup.mk
  apply Units.ext
  change KummerCriterion.cyclotomicRingOfIntegersEquiv
      (p := p) K (sigma * tau) (epsilon : 𝓞 K) =
    KummerCriterion.cyclotomicRingOfIntegersEquiv (p := p) K sigma
      (KummerCriterion.cyclotomicRingOfIntegersEquiv (p := p) K tau
        (epsilon : 𝓞 K))
  exact KummerCriterion.cyclotomicRingOfIntegersEquiv_mul_apply
    (p := p) (K := K) sigma tau epsilon

/-! ## The canonical representation on unit classes -/

omit [Fact p.Prime] [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- Global units modulo `p`-th powers are killed by `p`. -/
theorem unitModP_nsmul_eq_zero (u : UnitModP (𝓞 K) p) : p • u = 0 := by
  obtain ⟨epsilon, hepsilon⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom p : (𝓞 K)ˣ →* (𝓞 K)ˣ).range (Additive.toMul u)
  have hu : u = Additive.ofMul (QuotientGroup.mk epsilon) := by
    apply Additive.toMul.injective
    exact hepsilon.symm
  rw [hu]
  apply Additive.toMul.injective
  change ((QuotientGroup.mk epsilon :
      (𝓞 K)ˣ ⧸ (powMonoidHom p : (𝓞 K)ˣ →* (𝓞 K)ˣ).range) ^ p) = 1
  rw [← QuotientGroup.mk_pow]
  exact (QuotientGroup.eq_one_iff _).2 ⟨epsilon, rfl⟩

local instance instUnitModPModuleZMod :
    Module (ZMod p) (UnitModP (𝓞 K) p) :=
  AddCommGroup.zmodModule (n := p) (G := UnitModP (𝓞 K) p)
    (unitModP_nsmul_eq_zero p K)

local instance instUnitModPModulePadicInt :
    Module (PadicInt p) (UnitModP (𝓞 K) p) :=
  Module.compHom _ PadicInt.toZMod

/-- One cyclotomic automorphism as an additive homomorphism of unit classes. -/
noncomputable def cyclotomicUnitModPAddHom
    (sigma : KummerCriterion.CyclotomicUnitDelta p) :
    UnitModP (𝓞 K) p →+ UnitModP (𝓞 K) p :=
  (cyclotomicUnitModPAddEquiv p K sigma).toAddMonoidHom

/-- The descended unit-class action is linear over integral `p`-adic
coefficients. -/
noncomputable def cyclotomicUnitModPLinearMap
    (sigma : KummerCriterion.CyclotomicUnitDelta p) :
    UnitModP (𝓞 K) p →ₗ[PadicInt p] UnitModP (𝓞 K) p where
  toFun := cyclotomicUnitModPAddHom p K sigma
  map_add' := map_add _
  map_smul' a u := by
    change cyclotomicUnitModPAddHom p K sigma (PadicInt.toZMod a • u) =
      PadicInt.toZMod a • cyclotomicUnitModPAddHom p K sigma u
    exact ZMod.map_smul (cyclotomicUnitModPAddHom p K sigma)
      (PadicInt.toZMod a) u

/-- The canonical cyclotomic representation on global units modulo
`p`-th powers. -/
noncomputable def cyclotomicUnitModPRepresentation :
    Representation (PadicInt p) (KummerCriterion.CyclotomicUnitDelta p)
      (UnitModP (𝓞 K) p) where
  toFun sigma := cyclotomicUnitModPLinearMap p K sigma
  map_one' := by
    apply LinearMap.ext
    intro u
    exact cyclotomicUnitModPAddEquiv_one_apply p K u
  map_mul' sigma tau := by
    apply LinearMap.ext
    intro u
    exact cyclotomicUnitModPAddEquiv_mul_apply p K sigma tau u

/-! ## Naturality of the actual unit lift -/

/-- Embedding a transported ring unit into the field agrees with first
embedding it and then applying the cyclotomic field automorphism. -/
theorem cyclotomicRingUnitMulEquiv_map_algebraMap
    (sigma : KummerCriterion.CyclotomicUnitDelta p)
    (epsilon : (𝓞 K)ˣ) :
    Units.map (algebraMap (𝓞 K) K)
        (cyclotomicRingUnitMulEquiv p K sigma epsilon) =
      cyclotomicUnitEquiv p K sigma
        (Units.map (algebraMap (𝓞 K) K) epsilon) := by
  apply Units.ext
  change ((KummerCriterion.cyclotomicSigmaOfUnit
      (p := p) K sigma • (epsilon : 𝓞 K)) : K) =
    KummerCriterion.cyclotomicSigmaOfUnit (p := p) K sigma
      ((epsilon : 𝓞 K) : K)
  exact algebraMap.coe_smul'
    (KummerCriterion.cyclotomicSigmaOfUnit (p := p) K sigma)
    (epsilon : 𝓞 K) K

/-- Mathlib's actual units-to-Selmer map commutes with each cyclotomic
automorphism on the strict Selmer subtype. -/
theorem unitInclusion_cyclotomicUnitModPAddEquiv
    (sigma : KummerCriterion.CyclotomicUnitDelta p)
    (u : UnitModP (𝓞 K) p) :
    unitInclusion (R := 𝓞 K) (K := K) (p := p)
        (cyclotomicUnitModPAddEquiv p K sigma u) =
      cyclotomicStrictSelmerRepresentation p K sigma
        (unitInclusion (R := 𝓞 K) (K := K) (p := p) u) := by
  obtain ⟨epsilon, hepsilon⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom p : (𝓞 K)ˣ →* (𝓞 K)ˣ).range (Additive.toMul u)
  have hu : u = Additive.ofMul (QuotientGroup.mk epsilon) := by
    apply Additive.toMul.injective
    exact hepsilon.symm
  rw [hu]
  apply Additive.toMul.injective
  apply Subtype.ext
  change QuotientGroup.mk
      (Units.map (algebraMap (𝓞 K) K)
        (cyclotomicRingUnitMulEquiv p K sigma epsilon)) =
    cyclotomicKummerHom p K sigma
      (QuotientGroup.mk
        (Units.map (algebraMap (𝓞 K) K) epsilon))
  rw [cyclotomicRingUnitMulEquiv_map_algebraMap]
  rfl

/-- Mathlib's unit inclusion as a linear map over integral `p`-adic
coefficients. -/
noncomputable def unitInclusionLinearMap :
    UnitModP (𝓞 K) p →ₗ[PadicInt p] SelmerCarrier (𝓞 K) K p where
  toFun := unitInclusion (R := 𝓞 K) (K := K) (p := p)
  map_add' := map_add _
  map_smul' a u := by
    change unitInclusion (R := 𝓞 K) (K := K) (p := p)
        (PadicInt.toZMod a • u) =
      PadicInt.toZMod a •
        unitInclusion (R := 𝓞 K) (K := K) (p := p) u
    exact ZMod.map_smul
      (unitInclusion (R := 𝓞 K) (K := K) (p := p))
      (PadicInt.toZMod a) u

/-- The linear unit inclusion intertwines the canonical unit-class and
strict Selmer representations. -/
noncomputable def unitInclusionIntertwiner :
    Representation.IntertwiningMap
      (cyclotomicUnitModPRepresentation p K)
      (cyclotomicStrictSelmerRepresentation p K) :=
  (unitInclusionLinearMap p K).intertwiningMap_of_isIntertwiningMap
    (cyclotomicUnitModPRepresentation p K)
    (cyclotomicStrictSelmerRepresentation p K) <| by
      intro sigma u
      exact unitInclusion_cyclotomicUnitModPAddEquiv p K sigma u

/-! ## Arbitrary-character projector naturality -/

/-- The character-idempotent action on global units modulo `p`-th powers. -/
noncomputable def cyclotomicUnitProjector
    [Invertible
      (Fintype.card (KummerCriterion.CyclotomicUnitDelta p) : PadicInt p)]
    (eta : Fermat.Conservation.InvolutiveBase.Character
      (PadicInt p) (KummerCriterion.CyclotomicUnitDelta p)) :
    UnitModP (𝓞 K) p →ₗ[PadicInt p] UnitModP (𝓞 K) p :=
  (cyclotomicUnitModPRepresentation p K).asAlgebraHom
    (Fermat.Conservation.InvolutiveBase.characterIdempotent eta)

/-- Including a projected global-unit class is exactly the strict-Selmer
character projection of its included class. -/
theorem unitInclusionLinearMap_characterProjector
    [Invertible
      (Fintype.card (KummerCriterion.CyclotomicUnitDelta p) : PadicInt p)]
    (eta : Fermat.Conservation.InvolutiveBase.Character
      (PadicInt p) (KummerCriterion.CyclotomicUnitDelta p))
    (u : UnitModP (𝓞 K) p) :
    unitInclusionLinearMap p K (cyclotomicUnitProjector p K eta u) =
      (characterProjectorAt
        (cyclotomicStrictSelmerRepresentation p K) eta
        (unitInclusion (R := 𝓞 K) (K := K) (p := p) u)).1 := by
  change unitInclusionLinearMap p K
      ((cyclotomicUnitModPRepresentation p K).asAlgebraHom
        (Fermat.Conservation.InvolutiveBase.characterIdempotent eta) u) =
    (cyclotomicStrictSelmerRepresentation p K).asAlgebraHom
      (Fermat.Conservation.InvolutiveBase.characterIdempotent eta)
      (unitInclusionLinearMap p K u)
  let F :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      (cyclotomicUnitModPRepresentation p K)
      (cyclotomicStrictSelmerRepresentation p K))
      (unitInclusionIntertwiner p K)
  exact F.map_smul
    (Fermat.Conservation.InvolutiveBase.characterIdempotent eta) u

end Fermat.Conservation.PrimeCyclotomicUnitSelmerNaturality
