/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Comparing the two concrete Kummer characters at an arbitrary prime

For every prime `p`, the character obtained by restricting the absolute
Galois action to the concrete Kummer splitting field agrees exactly with
primitive-root coordinates of the chosen-root Kummer cocycle.  The comparison
tracks both noncomputable root choices and proves that no generator rotation
or sign correction occurs.
-/
import Fermat.Conservation.PrimeKummerCyclicQuotient
import Fermat.Conservation.ContinuousKummerOrientation

open Polynomial

noncomputable section

namespace Fermat.Conservation.PrimeKummerCharacterComparison

open Fermat.Conservation.PrimeKummerCyclicQuotient
open Fermat.Conservation.ContinuousKummerOrientation
open Fermat.Conservation.ContinuousKummerH1
open Fermat.Conservation.LocalKummerH1
open Fermat.Conservation.KummerOrientation

variable (p : ℕ) [Fact p.Prime]
local instance : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩

variable (F : Type) [Field F]
variable (zeta a : F)
variable (hzeta : IsPrimitiveRoot zeta p)
variable (ha : ∀ b : F, b ^ p ≠ a)

/-- The root selected by Mathlib inside the concrete splitting field, viewed
in the fixed algebraic closure. -/
def splittingRoot : AlgebraicClosure F := by
  letI : IsSplittingField F (kummerExtension p F a)
      (kummerPolynomial p F a) :=
    kummerExtension_isSplittingField p F a
  exact
    ((rootOfSplitsXPowSubC (n := p) (NeZero.pos p) a
        (kummerExtension p F a) : kummerExtension p F a) :
      AlgebraicClosure F)

/-- A radicand which is not a `p`-th power is nonzero. -/
theorem radicand_ne_zero (ha : ∀ b : F, b ^ p ≠ a) : a ≠ 0 := by
  intro h
  exact ha 0 (by simp [h, (Fact.out : Nat.Prime p).ne_zero])

/-- The splitting-field root really is a `p`-th root of the radicand. -/
theorem splittingRoot_pow :
    splittingRoot p F a ^ p = algebraMap F (AlgebraicClosure F) a := by
  letI : IsSplittingField F (kummerExtension p F a)
      (kummerPolynomial p F a) :=
    kummerExtension_isSplittingField p F a
  change
    (((rootOfSplitsXPowSubC (n := p) (NeZero.pos p) a
        (kummerExtension p F a) : kummerExtension p F a) :
      AlgebraicClosure F) ^ p) = _
  exact congrArg Subtype.val
    (rootOfSplitsXPowSubC_pow (n := p) a (kummerExtension p F a))

/-- The splitting-field root bundled as an algebraic-closure unit. -/
def splittingRootUnit : (AlgebraicClosure F)ˣ :=
  Units.mk0 (splittingRoot p F a) (by
    intro h
    have hp := splittingRoot_pow p F a
    rw [h, zero_pow (Fact.out : Nat.Prime p).ne_zero] at hp
    apply radicand_ne_zero p F a ha
    apply (algebraMap F (AlgebraicClosure F)).injective
    simpa using hp.symm)

/-- Unit-level form of `splittingRoot_pow`. -/
theorem splittingRootUnit_pow : splittingRootUnit p F a ha ^ p =
    Units.map (algebraMap F (AlgebraicClosure F)).toMonoidHom
      (Units.mk0 a (radicand_ne_zero p F a ha)) := by
  apply Units.ext
  exact splittingRoot_pow p F a

/-- The nonzero radicand bundled as a base-field unit. -/
def radicandUnit : Fˣ := Units.mk0 a (radicand_ne_zero p F a ha)

/-- The exponent assigned by the splitting-field character is exactly the
exponent by which the absolute Galois element acts on the selected root. -/
theorem restrictedGalois_acts_on_splittingRoot
    (g : AbsoluteGalois F) :
    g • splittingRoot p F a =
      algebraMap F (AlgebraicClosure F) zeta ^
          (kummerCharacter p F zeta a hzeta ha g).toAdd.val *
        splittingRoot p F a := by
  letI : IsSplittingField F (kummerExtension p F a)
      (kummerPolynomial p F a) :=
    kummerExtension_isSplittingField p F a
  letI : FiniteDimensional F (kummerExtension p F a) :=
    Polynomial.IsSplittingField.finiteDimensional
      (kummerExtension p F a) (kummerPolynomial p F a)
  letI : IsGalois F (kummerExtension p F a) :=
    isGalois_of_isSplittingField_X_pow_sub_C
      ⟨zeta, (mem_primitiveRoots (Fact.out : Nat.Prime p).pos).2 hzeta⟩
      (kummerPolynomial_irreducible p F a ha)
      (kummerExtension p F a)
  let m : ZMod p :=
    (kummerCharacter p F zeta a hzeta ha g).toAdd
  have hcoord :
      (kummerGalEquiv p F zeta a hzeta ha).symm
          (Multiplicative.ofAdd (m.val : ZMod p)) =
        AlgEquiv.restrictNormalHom (kummerExtension p F a) g := by
    apply (kummerGalEquiv p F zeta a hzeta ha).injective
    rw [(kummerGalEquiv p F zeta a hzeta ha).apply_symm_apply]
    change Multiplicative.ofAdd (m.val : ZMod p) =
      kummerCharacter p F zeta a hzeta ha g
    apply Multiplicative.toAdd.injective
    exact ZMod.natCast_zmod_val m
  have hroot := autEquivZmod_symm_apply_natCast
    (kummerPolynomial_irreducible p F a ha)
    (kummerExtension p F a)
    (rootOfSplitsXPowSubC_pow (n := p) a (kummerExtension p F a))
    hzeta m.val
  change
    (autEquivZmod (kummerPolynomial_irreducible p F a ha)
      (kummerExtension p F a) hzeta).symm
        (Multiplicative.ofAdd (m.val : ZMod p)) =
      AlgEquiv.restrictNormalHom (kummerExtension p F a) g at hcoord
  rw [hcoord] at hroot
  have hval := congrArg Subtype.val hroot
  change (show AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F from g)
      (splittingRoot p F a) = _
  simpa [m, splittingRoot, AlgEquiv.restrictNormalHom_apply,
    Algebra.smul_def, map_pow] using hval

/-- The `k`-th power of the chosen primitive root, bundled in `μ_p`. -/
def algebraicPowerRoot (k : ℕ) : KummerRoots p F :=
  ⟨(algebraicPrimitiveUnit p F zeta hzeta) ^ k, by
    rw [mem_rootsOfUnity, ← pow_mul, mul_comm, pow_mul,
      (algebraicPrimitiveUnit_isPrimitive p F zeta hzeta).pow_eq_one,
      one_pow]⟩

/-- Primitive-root coordinates read the displayed power with no sign or
generator change. -/
theorem coordinate_algebraicPowerRoot (k : ℕ) :
    coordinateContinuousLinearEquiv p F zeta hzeta
        (Additive.ofMul (algebraicPowerRoot p F zeta hzeta k)) =
      (k : ZMod p) := by
  change coordinateLinearEquiv p F zeta hzeta
      (Additive.ofMul (algebraicPowerRoot p F zeta hzeta k)) = _
  change coordinateAddEquiv p F zeta hzeta
      (Additive.ofMul (algebraicPowerRoot p F zeta hzeta k)) = _
  change
    (algebraicPrimitiveUnit_isPrimitive p F zeta hzeta).zmodEquivZPowers.symm
        ((MulEquiv.toAdditive (rootsEquivZPowers p F zeta hzeta))
          (Additive.ofMul (algebraicPowerRoot p F zeta hzeta k))) = _
  apply
    (algebraicPrimitiveUnit_isPrimitive p F zeta hzeta).zmodEquivZPowers.injective
  rw [AddEquiv.apply_symm_apply]
  rw [IsPrimitiveRoot.zmodEquivZPowers_apply_coe_nat]
  rfl

/-- Root-choice independence identifies the public chosen-root Kummer
cocycle pointwise with the splitting-field exponent. -/
theorem cocycleValue_eq_algebraicPowerRoot
    (g : AbsoluteGalois F) :
    cocycleValue p F (radicandUnit p F a ha) g =
      algebraicPowerRoot p F zeta hzeta
        (kummerCharacter p F zeta a hzeta ha g).toAdd.val := by
  apply Subtype.ext
  have hfix : ∀ η : KummerRoots p F, g • η = η := by
    intro η
    have h := absoluteGalois_smul_root_eq p F zeta hzeta g
      (Additive.ofMul η)
    exact congrArg Additive.toMul h
  have hcoc := cocycleValue_coe_eq_of_root p F
    (radicandUnit p F a ha) g (splittingRootUnit p F a ha)
    (splittingRootUnit_pow p F a ha) hfix
  have haction :
      g • splittingRootUnit p F a ha =
        (algebraicPrimitiveUnit p F zeta hzeta) ^
            (kummerCharacter p F zeta a hzeta ha g).toAdd.val *
          splittingRootUnit p F a ha := by
    apply Units.ext
    simpa [splittingRootUnit, algebraicPrimitiveUnit, primitiveUnit,
      map_pow] using
      restrictedGalois_acts_on_splittingRoot p F zeta a hzeta ha g
  calc
    (cocycleValue p F (radicandUnit p F a ha) g :
        (AlgebraicClosure F)ˣ) =
        g • splittingRootUnit p F a ha / splittingRootUnit p F a ha := hcoc
    _ = (algebraicPrimitiveUnit p F zeta hzeta) ^
          (kummerCharacter p F zeta a hzeta ha g).toAdd.val := by
            rw [haction]
            simp
    _ = (algebraicPowerRoot p F zeta hzeta
          (kummerCharacter p F zeta a hzeta ha g).toAdd.val :
        (AlgebraicClosure F)ˣ) := rfl


/-! ## Generic primitive-root coordinates -/

/-- Primitive-root coordinates of the roots-valued continuous Kummer cocycle. -/
def orientedKummerValue (u : Fˣ) : C(AbsoluteGalois F, ZMod p) where
  toFun g := coordinateContinuousLinearEquiv p F zeta hzeta
    (continuousCocycle p F u g)
  continuous_toFun :=
    (coordinateContinuousLinearEquiv p F zeta hzeta).continuous.comp
      (continuousCocycle p F u).continuous

/-- Over a field containing the selected primitive root, the oriented Kummer
cocycle is an additive character. -/
theorem orientedKummerValue_mul (u : Fˣ) (g h : AbsoluteGalois F) :
    orientedKummerValue p F zeta hzeta u (g * h) =
      orientedKummerValue p F zeta hzeta u g +
        orientedKummerValue p F zeta hzeta u h := by
  change coordinateContinuousLinearEquiv p F zeta hzeta
      (continuousCocycle p F u (g * h)) = _
  rw [continuousCocycle_crossed]
  rw [map_add]
  congr 1
  exact congrArg (coordinateContinuousLinearEquiv p F zeta hzeta)
    (absoluteGalois_smul_root_eq p F zeta hzeta g
      (continuousCocycle p F u h))

/-- The generic oriented Kummer cocycle as a continuous homomorphism to
`Multiplicative (ZMod p)`. -/
def orientedKummerCharacter (u : Fˣ) :
    AbsoluteGalois F →ₜ* Multiplicative (ZMod p) where
  toFun g := Multiplicative.ofAdd (orientedKummerValue p F zeta hzeta u g)
  map_one' := by
    change orientedKummerValue p F zeta hzeta u 1 = 0
    have h := orientedKummerValue_mul p F zeta hzeta u 1 1
    simp only [one_mul] at h
    apply add_left_cancel (a := orientedKummerValue p F zeta hzeta u 1)
    simpa using h.symm
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    simpa using orientedKummerValue_mul p F zeta hzeta u g h
  continuous_toFun := (orientedKummerValue p F zeta hzeta u).continuous

/-- Pointwise additive-coordinate equality between the two Kummer
characters. -/
theorem orientedKummerValue_eq_kummerCharacter_toAdd
    (g : AbsoluteGalois F) :
    orientedKummerValue p F zeta hzeta (radicandUnit p F a ha) g =
      (kummerCharacter p F zeta a hzeta ha g).toAdd := by
  change coordinateContinuousLinearEquiv p F zeta hzeta
      (Additive.ofMul
        (cocycleValue p F (radicandUnit p F a ha) g)) = _
  rw [cocycleValue_eq_algebraicPowerRoot p F zeta a hzeta ha g]
  rw [coordinate_algebraicPowerRoot p F zeta hzeta]
  exact ZMod.natCast_zmod_val _

/-- The restriction/`autEquivZmod` construction and the oriented genuine
Kummer cocycle are exactly the same continuous `C_p` character. -/
theorem kummerCharacter_eq_orientedKummerCharacter :
    kummerCharacter p F zeta a hzeta ha =
      orientedKummerCharacter p F zeta hzeta (radicandUnit p F a ha) := by
  ext g
  apply Multiplicative.toAdd.injective
  exact (orientedKummerValue_eq_kummerCharacter_toAdd
    p F zeta a hzeta ha g).symm


end Fermat.Conservation.PrimeKummerCharacterComparison
