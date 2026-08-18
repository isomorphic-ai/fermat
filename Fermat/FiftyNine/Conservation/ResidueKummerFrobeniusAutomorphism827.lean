/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The residue Kummer Frobenius is an automorphism

The local Kummer--Frobenius comparison first bundled 827-power Frobenius as
an algebra endomorphism of `ZMod 827[T]/(T^59-u)`.  Here we construct its
inverse explicitly: the inverse sends the Kummer root to `u^(-14) * T`.

The construction uses only `827 - 1 = 14 * 59`, so the Frobenius multiplier
has 59th power one.  It upgrades the local reading to a genuine algebra
automorphism without asserting a global ray-class Artin map, reciprocity, or
faithfulness on the ideal class group.
-/
import Fermat.FiftyNine.Conservation.LocalKummerFrobeniusFactorization827

open Polynomial
open scoped nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation.ResidueKummerFrobeniusAutomorphism827

open Credit
open KummerFrobeniusRead827
open LocalKummerFrobeniusFactorization827

local instance : Fact (Nat.Prime Credit.attestationPrime) :=
  ⟨Credit.attestationPrime_isPrime⟩

/-- The scalar by which residue Frobenius moves the Kummer root is itself a
59th root of unity. -/
theorem residueFrobeniusMultiplier_pow_fiftyNine
    (u : (ZMod Credit.attestationPrime)ˣ) :
    (u ^ 14) ^ 59 = 1 := by
  have h := ZMod.units_pow_card_sub_one_eq_one Credit.attestationPrime u
  rw [← pow_mul]
  norm_num [Credit.attestationPrime] at h ⊢
  exact h

private theorem inverseScaledRoot_isRoot
    (u : (ZMod Credit.attestationPrime)ˣ) :
    (X ^ 59 - C (u : ZMod Credit.attestationPrime)).eval₂
        (Algebra.ofId (ZMod Credit.attestationPrime)
          (ResidueKummerAlgebra827 u))
        (algebraMap (ZMod Credit.attestationPrime)
            (ResidueKummerAlgebra827 u)
            (((u ^ 14)⁻¹ : (ZMod Credit.attestationPrime)ˣ) :
              ZMod Credit.attestationPrime) *
          residueKummerRoot827 u) = 0 := by
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  rw [mul_pow, residueKummerRoot827_pow_fiftyNine]
  have hcUnits : ((u ^ 14)⁻¹) ^ 59 =
      (1 : (ZMod Credit.attestationPrime)ˣ) := by
    rw [inv_pow, residueFrobeniusMultiplier_pow_fiftyNine, inv_one]
  have hc : ((((u ^ 14)⁻¹ : (ZMod Credit.attestationPrime)ˣ) :
      ZMod Credit.attestationPrime) ^ 59) = 1 := by
    simpa using congrArg
      (fun z : (ZMod Credit.attestationPrime)ˣ =>
        (z : ZMod Credit.attestationPrime)) hcUnits
  rw [← map_pow, hc, map_one, one_mul]
  change algebraMap (ZMod Credit.attestationPrime)
      (ResidueKummerAlgebra827 u) (u : ZMod Credit.attestationPrime) -
    algebraMap (ZMod Credit.attestationPrime)
      (ResidueKummerAlgebra827 u) (u : ZMod Credit.attestationPrime) = 0
  exact sub_self _

/-- The explicit inverse of residue Frobenius, defined by its action on the
universal Kummer root. -/
noncomputable def residueFrobeniusInverseAlgHom827
    (u : (ZMod Credit.attestationPrime)ˣ) :
    ResidueKummerAlgebra827 u →ₐ[ZMod Credit.attestationPrime]
      ResidueKummerAlgebra827 u :=
  AdjoinRoot.liftAlgHom
    (X ^ 59 - C (u : ZMod Credit.attestationPrime))
    (Algebra.ofId (ZMod Credit.attestationPrime)
      (ResidueKummerAlgebra827 u))
    (algebraMap (ZMod Credit.attestationPrime)
        (ResidueKummerAlgebra827 u)
        (((u ^ 14)⁻¹ : (ZMod Credit.attestationPrime)ˣ) :
          ZMod Credit.attestationPrime) *
      residueKummerRoot827 u)
    (inverseScaledRoot_isRoot u)

@[simp]
theorem residueFrobeniusInverseAlgHom827_root
    (u : (ZMod Credit.attestationPrime)ˣ) :
    residueFrobeniusInverseAlgHom827 u (residueKummerRoot827 u) =
      algebraMap (ZMod Credit.attestationPrime)
          (ResidueKummerAlgebra827 u)
          (((u ^ 14)⁻¹ : (ZMod Credit.attestationPrime)ˣ) :
            ZMod Credit.attestationPrime) *
        residueKummerRoot827 u := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

/-- Frobenius followed by its explicit inverse is the identity algebra map. -/
theorem residueFrobeniusAlgHom827_comp_inverse
    (u : (ZMod Credit.attestationPrime)ˣ) :
    (residueFrobeniusAlgHom827 u).comp
        (residueFrobeniusInverseAlgHom827 u) =
      AlgHom.id (ZMod Credit.attestationPrime)
        (ResidueKummerAlgebra827 u) := by
  apply AdjoinRoot.algHom_ext
  change residueFrobeniusAlgHom827 u
      (residueFrobeniusInverseAlgHom827 u (residueKummerRoot827 u)) =
    residueKummerRoot827 u
  rw [residueFrobeniusInverseAlgHom827_root, map_mul,
    residueFrobeniusAlgHom827_root]
  rw [(residueFrobeniusAlgHom827 u).commutes]
  change algebraMap (ZMod Credit.attestationPrime)
      (ResidueKummerAlgebra827 u)
        (((u ^ 14)⁻¹ : (ZMod Credit.attestationPrime)ˣ) :
          ZMod Credit.attestationPrime) *
      (algebraMap (ZMod Credit.attestationPrime)
          (ResidueKummerAlgebra827 u)
          ((u : ZMod Credit.attestationPrime) ^ 14) *
        residueKummerRoot827 u) = residueKummerRoot827 u
  rw [← mul_assoc, ← map_mul]
  simp

/-- The explicit inverse followed by Frobenius is the identity algebra map. -/
theorem residueFrobeniusInverseAlgHom827_comp
    (u : (ZMod Credit.attestationPrime)ˣ) :
    (residueFrobeniusInverseAlgHom827 u).comp
        (residueFrobeniusAlgHom827 u) =
      AlgHom.id (ZMod Credit.attestationPrime)
        (ResidueKummerAlgebra827 u) := by
  apply AdjoinRoot.algHom_ext
  change residueFrobeniusInverseAlgHom827 u
      (residueFrobeniusAlgHom827 u (residueKummerRoot827 u)) =
    residueKummerRoot827 u
  rw [residueFrobeniusAlgHom827_root, map_mul,
    residueFrobeniusInverseAlgHom827_root]
  rw [(residueFrobeniusInverseAlgHom827 u).commutes]
  rw [map_pow]
  change (algebraMap (ZMod Credit.attestationPrime)
      (ResidueKummerAlgebra827 u)
        (u : ZMod Credit.attestationPrime)) ^ 14 *
      (algebraMap (ZMod Credit.attestationPrime)
          (ResidueKummerAlgebra827 u)
          (((u ^ 14)⁻¹ : (ZMod Credit.attestationPrime)ˣ) :
            ZMod Credit.attestationPrime) *
        residueKummerRoot827 u) = residueKummerRoot827 u
  rw [← map_pow, ← mul_assoc, ← map_mul]
  simp

/-- Literal residue Frobenius on the universal Kummer algebra, now bundled
as an algebra automorphism. -/
noncomputable def residueKummerFrobeniusAlgEquiv827
    (u : (ZMod Credit.attestationPrime)ˣ) :
    ResidueKummerAlgebra827 u ≃ₐ[ZMod Credit.attestationPrime]
      ResidueKummerAlgebra827 u :=
  AlgEquiv.ofAlgHom
    (residueFrobeniusAlgHom827 u)
    (residueFrobeniusInverseAlgHom827 u)
    (residueFrobeniusAlgHom827_comp_inverse u)
    (residueFrobeniusInverseAlgHom827_comp u)

@[simp]
theorem residueKummerFrobeniusAlgEquiv827_apply
    (u : (ZMod Credit.attestationPrime)ˣ)
    (a : ResidueKummerAlgebra827 u) :
    residueKummerFrobeniusAlgEquiv827 u a =
      residueFrobeniusAlgHom827 u a :=
  rfl

@[simp]
theorem residueKummerFrobeniusAlgEquiv827_root
    (u : (ZMod Credit.attestationPrime)ˣ) :
    residueKummerFrobeniusAlgEquiv827 u (residueKummerRoot827 u) =
      algebraMap (ZMod Credit.attestationPrime)
          (ResidueKummerAlgebra827 u)
          ((u : ZMod Credit.attestationPrime) ^ 14) *
        residueKummerRoot827 u := by
  rw [residueKummerFrobeniusAlgEquiv827_apply,
    residueFrobeniusAlgHom827_root]

/-! ## Axiom audit -/

/--
info: 'Fermat.FiftyNine.Conservation.ResidueKummerFrobeniusAutomorphism827.residueFrobeniusMultiplier_pow_fiftyNine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms residueFrobeniusMultiplier_pow_fiftyNine

/--
info: 'Fermat.FiftyNine.Conservation.ResidueKummerFrobeniusAutomorphism827.residueFrobeniusAlgHom827_comp_inverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms residueFrobeniusAlgHom827_comp_inverse

/--
info: 'Fermat.FiftyNine.Conservation.ResidueKummerFrobeniusAutomorphism827.residueFrobeniusInverseAlgHom827_comp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms residueFrobeniusInverseAlgHom827_comp

/--
info: 'Fermat.FiftyNine.Conservation.ResidueKummerFrobeniusAutomorphism827.residueKummerFrobeniusAlgEquiv827_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms residueKummerFrobeniusAlgEquiv827_root

end Fermat.FiftyNine.Conservation.ResidueKummerFrobeniusAutomorphism827
