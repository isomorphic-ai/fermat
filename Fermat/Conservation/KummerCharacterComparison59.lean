/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Comparing the two concrete Kummer characters at 59

`KummerCyclicQuotient59.kummerCharacter59` is defined by restricting the
absolute Galois action to the splitting field of `X ^ 59 - a` and applying
Mathlib's `autEquivZmod`.  `OrientedKummerRepresentative59` instead takes
primitive-root coordinates of the usual chosen-root Kummer cocycle.

This file proves that they are exactly the same continuous character.  No
generator rotation is necessary: both conventions assign `m` to the action

`g(root) = zeta ^ m * root`.

The proof also makes the independence from the two noncomputable root choices
explicit, via `LocalKummerH1.cocycleValue_coe_eq_of_root`.
-/
import Fermat.Conservation.KummerCyclicQuotient59
import Fermat.Conservation.OrientedKummerRepresentative59

open Polynomial

noncomputable section

namespace Fermat.Conservation.KummerCharacterComparison59

open Fermat.Conservation.KummerCyclicQuotient59
open Fermat.Conservation.OrientedKummerRepresentative59
open Fermat.Conservation.ContinuousCyclicQuotient59
open Fermat.Conservation.ContinuousKummerOrientation
open Fermat.Conservation.LocalKummerH1
open Fermat.Conservation.KummerOrientation

local instance : NeZero 59 := ⟨by decide⟩

variable (F : Type) [Field F]
variable (zeta a : F)
variable (hzeta : IsPrimitiveRoot zeta 59)
variable (ha : ∀ b : F, b ^ 59 ≠ a)

/-- The root selected by Mathlib inside the concrete splitting field, viewed
in the fixed algebraic closure. -/
def splittingRoot59 : AlgebraicClosure F := by
  letI : IsSplittingField F (kummerExtension59 F a)
      (kummerPolynomial59 F a) :=
    kummerExtension59_isSplittingField F a
  exact
    ((rootOfSplitsXPowSubC (n := 59) (NeZero.pos 59) a
        (kummerExtension59 F a) : kummerExtension59 F a) :
      AlgebraicClosure F)

/-- A radicand which is not a 59th power is nonzero. -/
theorem radicand_ne_zero (ha : ∀ b : F, b ^ 59 ≠ a) : a ≠ 0 := by
  intro h
  exact ha 0 (by simp [h])

/-- The splitting-field root really is a 59th root of the radicand. -/
theorem splittingRoot59_pow :
    splittingRoot59 F a ^ 59 = algebraMap F (AlgebraicClosure F) a := by
  letI : IsSplittingField F (kummerExtension59 F a)
      (kummerPolynomial59 F a) :=
    kummerExtension59_isSplittingField F a
  change
    (((rootOfSplitsXPowSubC (n := 59) (NeZero.pos 59) a
        (kummerExtension59 F a) : kummerExtension59 F a) :
      AlgebraicClosure F) ^ 59) = _
  exact congrArg Subtype.val
    (rootOfSplitsXPowSubC_pow (n := 59) a (kummerExtension59 F a))

/-- The splitting-field root bundled as an algebraic-closure unit. -/
def splittingRootUnit59 : (AlgebraicClosure F)ˣ :=
  Units.mk0 (splittingRoot59 F a) (by
    intro h
    have hp := splittingRoot59_pow F a
    rw [h, zero_pow (by decide : 59 ≠ 0)] at hp
    apply radicand_ne_zero F a ha
    apply (algebraMap F (AlgebraicClosure F)).injective
    simpa using hp.symm)

/-- Unit-level form of `splittingRoot59_pow`. -/
theorem splittingRootUnit59_pow : splittingRootUnit59 F a ha ^ 59 =
    Units.map (algebraMap F (AlgebraicClosure F)).toMonoidHom
      (Units.mk0 a (radicand_ne_zero F a ha)) := by
  apply Units.ext
  exact splittingRoot59_pow F a

/-- The nonzero radicand bundled as a base-field unit. -/
def radicandUnit59 : Fˣ := Units.mk0 a (radicand_ne_zero F a ha)

/-- The exponent assigned by the splitting-field character is exactly the
exponent by which the absolute Galois element acts on the selected root. -/
theorem restrictedGalois_acts_on_splittingRoot59
    (g : AbsoluteGalois F) :
    g • splittingRoot59 F a =
      algebraMap F (AlgebraicClosure F) zeta ^
          (kummerCharacter59 F zeta a hzeta ha g).toAdd.val *
        splittingRoot59 F a := by
  letI : IsSplittingField F (kummerExtension59 F a)
      (kummerPolynomial59 F a) :=
    kummerExtension59_isSplittingField F a
  letI : FiniteDimensional F (kummerExtension59 F a) :=
    Polynomial.IsSplittingField.finiteDimensional
      (kummerExtension59 F a) (kummerPolynomial59 F a)
  letI : IsGalois F (kummerExtension59 F a) :=
    isGalois_of_isSplittingField_X_pow_sub_C
      ⟨zeta, (mem_primitiveRoots (by decide : 0 < 59)).2 hzeta⟩
      (kummerPolynomial59_irreducible F a ha)
      (kummerExtension59 F a)
  let m : ZMod 59 :=
    (kummerCharacter59 F zeta a hzeta ha g).toAdd
  have hcoord :
      (kummerGalEquiv59 F zeta a hzeta ha).symm
          (Multiplicative.ofAdd (m.val : ZMod 59)) =
        AlgEquiv.restrictNormalHom (kummerExtension59 F a) g := by
    apply (kummerGalEquiv59 F zeta a hzeta ha).injective
    rw [(kummerGalEquiv59 F zeta a hzeta ha).apply_symm_apply]
    change Multiplicative.ofAdd (m.val : ZMod 59) =
      kummerCharacter59 F zeta a hzeta ha g
    apply Multiplicative.toAdd.injective
    exact ZMod.natCast_zmod_val m
  have hroot := autEquivZmod_symm_apply_natCast
    (kummerPolynomial59_irreducible F a ha)
    (kummerExtension59 F a)
    (rootOfSplitsXPowSubC_pow (n := 59) a (kummerExtension59 F a))
    hzeta m.val
  change
    (autEquivZmod (kummerPolynomial59_irreducible F a ha)
      (kummerExtension59 F a) hzeta).symm
        (Multiplicative.ofAdd (m.val : ZMod 59)) =
      AlgEquiv.restrictNormalHom (kummerExtension59 F a) g at hcoord
  rw [hcoord] at hroot
  have hval := congrArg Subtype.val hroot
  change (show AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F from g)
      (splittingRoot59 F a) = _
  simpa [m, splittingRoot59, AlgEquiv.restrictNormalHom_apply,
    Algebra.smul_def, map_pow] using hval

/-- The `k`-th power of the chosen primitive root, bundled in `μ_59`. -/
def algebraicPowerRoot59 (k : ℕ) : KummerRoots 59 F :=
  ⟨(algebraicPrimitiveUnit 59 F zeta hzeta) ^ k, by
    rw [mem_rootsOfUnity, ← pow_mul, mul_comm, pow_mul,
      (algebraicPrimitiveUnit_isPrimitive 59 F zeta hzeta).pow_eq_one,
      one_pow]⟩

/-- Primitive-root coordinates read the displayed power with no sign or
generator change. -/
theorem coordinate_algebraicPowerRoot59 (k : ℕ) :
    coordinateContinuousLinearEquiv 59 F zeta hzeta
        (Additive.ofMul (algebraicPowerRoot59 F zeta hzeta k)) =
      (k : ZMod 59) := by
  change coordinateLinearEquiv 59 F zeta hzeta
      (Additive.ofMul (algebraicPowerRoot59 F zeta hzeta k)) = _
  change coordinateAddEquiv 59 F zeta hzeta
      (Additive.ofMul (algebraicPowerRoot59 F zeta hzeta k)) = _
  change
    (algebraicPrimitiveUnit_isPrimitive 59 F zeta hzeta).zmodEquivZPowers.symm
        ((MulEquiv.toAdditive (rootsEquivZPowers 59 F zeta hzeta))
          (Additive.ofMul (algebraicPowerRoot59 F zeta hzeta k))) = _
  apply
    (algebraicPrimitiveUnit_isPrimitive 59 F zeta hzeta).zmodEquivZPowers.injective
  rw [AddEquiv.apply_symm_apply]
  rw [IsPrimitiveRoot.zmodEquivZPowers_apply_coe_nat]
  rfl

/-- Root-choice independence identifies the public chosen-root Kummer
cocycle pointwise with the splitting-field exponent. -/
theorem cocycleValue_eq_algebraicPowerRoot59
    (g : AbsoluteGalois F) :
    cocycleValue 59 F (radicandUnit59 F a ha) g =
      algebraicPowerRoot59 F zeta hzeta
        (kummerCharacter59 F zeta a hzeta ha g).toAdd.val := by
  apply Subtype.ext
  have hfix : ∀ η : KummerRoots 59 F, g • η = η := by
    intro η
    have h := absoluteGalois_smul_root_eq 59 F zeta hzeta g
      (Additive.ofMul η)
    exact congrArg Additive.toMul h
  have hcoc := cocycleValue_coe_eq_of_root 59 F
    (radicandUnit59 F a ha) g (splittingRootUnit59 F a ha)
    (splittingRootUnit59_pow F a ha) hfix
  have haction :
      g • splittingRootUnit59 F a ha =
        (algebraicPrimitiveUnit 59 F zeta hzeta) ^
            (kummerCharacter59 F zeta a hzeta ha g).toAdd.val *
          splittingRootUnit59 F a ha := by
    apply Units.ext
    simpa [splittingRootUnit59, algebraicPrimitiveUnit, primitiveUnit,
      map_pow] using
      restrictedGalois_acts_on_splittingRoot59 F zeta a hzeta ha g
  calc
    (cocycleValue 59 F (radicandUnit59 F a ha) g :
        (AlgebraicClosure F)ˣ) =
        g • splittingRootUnit59 F a ha / splittingRootUnit59 F a ha := hcoc
    _ = (algebraicPrimitiveUnit 59 F zeta hzeta) ^
          (kummerCharacter59 F zeta a hzeta ha g).toAdd.val := by
            rw [haction]
            simp
    _ = (algebraicPowerRoot59 F zeta hzeta
          (kummerCharacter59 F zeta a hzeta ha g).toAdd.val :
        (AlgebraicClosure F)ˣ) := rfl

/-- Pointwise additive-coordinate equality between the two Kummer
characters. -/
theorem orientedKummerValue_eq_kummerCharacter59_toAdd
    (g : AbsoluteGalois F) :
    orientedKummerValue F zeta hzeta (radicandUnit59 F a ha) g =
      (kummerCharacter59 F zeta a hzeta ha g).toAdd := by
  change coordinateContinuousLinearEquiv 59 F zeta hzeta
      (Additive.ofMul
        (cocycleValue 59 F (radicandUnit59 F a ha) g)) = _
  rw [cocycleValue_eq_algebraicPowerRoot59 F zeta a hzeta ha g]
  rw [coordinate_algebraicPowerRoot59 F zeta hzeta]
  exact ZMod.natCast_zmod_val _

/-- The restriction/`autEquivZmod` construction and the oriented genuine
Kummer cocycle are exactly the same continuous `C_59` character. -/
theorem kummerCharacter59_eq_orientedKummerCharacter :
    kummerCharacter59 F zeta a hzeta ha =
      orientedKummerCharacter F zeta hzeta (radicandUnit59 F a ha) := by
  ext g
  apply Multiplicative.toAdd.injective
  exact (orientedKummerValue_eq_kummerCharacter59_toAdd
    F zeta a hzeta ha g).symm

end Fermat.Conservation.KummerCharacterComparison59
