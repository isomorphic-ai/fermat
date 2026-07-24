import Fermat.Irregular.CircularUnitResidues
import Fermat.SixHundredSeven.FirstCase
import Fermat.SixHundredSeven.CircularUnitMatrix

/-!
# Structural finite-field provenance at exponent 607

At `20639 = 34 * 607 + 1`, the package fixes `14674 = 11^34`, an element
of exact order `607`. The normalized circular-unit symbols are quotients of
the inversion-invariant weight

`W(x) = (1 - x)^34 / x^17`.

This file contains the algebraic part of the entry reconstruction. The
finite phase and coordinate data are certified in separate one-dimensional
modules before the final entry theorem is assembled.
-/

namespace Fermat.SixHundredSeven.CircularUnitEntryCertificate

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitResidues
open Fermat.SixHundredSeven.CircularUnitCyclic
open Fermat.SixHundredSeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 607) :=
  ⟨Fermat.SixHundredSeven.prime_607⟩
local instance : Fact (Nat.Prime 20639) :=
  ⟨Fermat.SixHundredSeven.prime_20639⟩

/-- The package root `14674 = 11^34 mod 20639` has exact order `607`. -/
theorem root_order : orderOf (14674 : ZMod 20639) = 607 := by
  apply orderOf_eq_prime
  · decide
  · decide

/-- The package root is primitive of order `607`. -/
theorem root_isPrimitive : IsPrimitiveRoot (14674 : ZMod 20639) 607 :=
  IsPrimitiveRoot.iff_orderOf.mpr root_order

/-- The inversion-invariant weight whose quotients are the normalized
thirty-fourth-power residue symbols. -/
def weight (x : ZMod 20639) : ZMod 20639 :=
  (1 - x) ^ 34 / x ^ 17

/-- Raising a normalized circular unit to the symbol exponent is exactly a
quotient of two weights. -/
theorem normalized_pow_eq_weight_ratio (j i : Fin 302) :
    normalizedUnitValue (p := 607) (14674 : ZMod 20639) j i ^ 34 =
      weight
          (embeddingRoot (p := 607) (14674 : ZMod 20639) j ^ (i.val + 2)) /
        weight (embeddingRoot (p := 607) (14674 : ZMod 20639) j) := by
  let x : ZMod 20639 :=
    embeddingRoot (p := 607) (14674 : ZMod 20639) j
  let a : Nat := i.val + 2
  let e : Nat := canonicalNormalizationExponent (p := 607) a
  have hxprim : IsPrimitiveRoot x 607 := by
    exact embeddingRoot_isPrimitive (p := 607) (q := 20639) (by norm_num)
      root_isPrimitive j
  have hx0 : x ≠ 0 := hxprim.ne_zero (by norm_num)
  have hx1 : 1 - x ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (hxprim.ne_one (by norm_num)))
  have hnorm : 2 * e + a ≡ 1 [MOD 607] :=
    canonicalNormalizationExponent_modEq (p := 607) (by norm_num) a
  have hnorm17 : 17 * (2 * e + a) ≡ 17 * 1 [MOD 607] :=
    hnorm.mul_left 17
  have hexp : 34 * e + 17 * a ≡ 17 [MOD 607] := by
    convert hnorm17 using 1 <;> omega
  have hpow : x ^ (34 * e + 17 * a) = x ^ 17 :=
    pow_eq_pow_of_modEq hexp hxprim.pow_eq_one
  change (x ^ e * (1 - x ^ a) / (1 - x)) ^ 34 =
    weight (x ^ a) / weight x
  simp only [weight, mul_pow, div_pow]
  field_simp [hx0, hx1]
  have hpow' : x ^ (e * 34) * x ^ (a * 17) = x ^ 17 := by
    rw [← pow_add]
    simpa [Nat.mul_comm] using hpow
  calc
    _ = (x ^ (e * 34) * x ^ (a * 17)) * (1 - x ^ a) ^ 34 := by ring
    _ = x ^ 17 * (1 - x ^ a) ^ 34 := by rw [hpow']
    _ = _ := by ring

/-- Real Galois class `[303]·[3]^r`, represented modulo `607`. -/
def classExponent (r : Cyc) : Nat :=
  ((303 : ZMod 607) * (3 : ZMod 607) ^ r.val).val

/-- Casting the canonical representative recovers its defining residue
class. -/
theorem classExponent_cast (r : Cyc) :
    (classExponent r : ZMod 607) =
      (303 : ZMod 607) * (3 : ZMod 607) ^ r.val := by
  exact ZMod.natCast_zmod_val _

/-- The corresponding order-`607` root at the split prime. -/
def classRoot (r : Cyc) : ZMod 20639 :=
  (14674 : ZMod 20639) ^ classExponent r

/-- Squaring a power of `3` turns it into the corresponding power of `9`. -/
theorem three_pow_sq (n : ℕ) :
    (((3 : ZMod 607) ^ n) ^ 2) = (9 : ZMod 607) ^ n := by
  calc
    (((3 : ZMod 607) ^ n) ^ 2) =
        (3 : ZMod 607) ^ (n * 2) := (pow_mul _ n 2).symm
    _ = (3 : ZMod 607) ^ (2 * n) := by rw [Nat.mul_comm]
    _ = ((3 : ZMod 607) ^ 2) ^ n := pow_mul _ 2 n
    _ = (9 : ZMod 607) ^ n := by norm_num

/-- `9` has period dividing the real cycle length modulo `607`. -/
theorem nine_pow_cycleLength : (9 : ZMod 607) ^ 303 = 1 := by
  decide

/-- Addition of real cyclic coordinates multiplies the corresponding
class exponents after squaring. Squaring removes the harmless sign from
reduction modulo the real cycle length `303`. -/
theorem classExponent_add_sq (r s : Cyc) :
    ((classExponent (r + s) : ZMod 607) ^ 2) =
      ((classExponent r : ZMod 607) ^ 2) *
        (((3 : ZMod 607) ^ s.val) ^ 2) := by
  have hmod : (r + s).val ≡ r.val + s.val [MOD 303] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simp
  have hnine :
      (9 : ZMod 607) ^ (r + s).val =
        (9 : ZMod 607) ^ (r.val + s.val) :=
    pow_eq_pow_of_modEq hmod nine_pow_cycleLength
  rw [classExponent_cast, classExponent_cast, mul_pow, mul_pow,
    three_pow_sq, three_pow_sq, three_pow_sq, hnine, pow_add]
  ring

/-- Every represented class exponent is nonzero modulo `607`. -/
theorem classExponent_ne_zero (r : Cyc) : classExponent r ≠ 0 := by
  intro hzero
  have hcast : (classExponent r : ZMod 607) = 0 := by simp [hzero]
  rw [classExponent_cast] at hcast
  exact (mul_ne_zero (by decide) (pow_ne_zero _ (by decide))) hcast

/-- Canonical class exponents lie below the modulus. -/
theorem classExponent_lt (r : Cyc) : classExponent r < 607 :=
  ZMod.val_lt _

/-- No represented real class is the trivial `607`th root. -/
theorem classRoot_ne_one (r : Cyc) : classRoot r ≠ 1 := by
  intro hone
  have hdvd : 607 ∣ classExponent r :=
    (root_isPrimitive.pow_eq_one_iff_dvd _).mp hone
  have heq : classExponent r = 0 :=
    Nat.eq_zero_of_dvd_of_lt hdvd (classExponent_lt r)
  exact classExponent_ne_zero r heq

/-- Every represented real class is nonzero in the split field. -/
theorem classRoot_ne_zero (r : Cyc) : classRoot r ≠ 0 := by
  exact pow_ne_zero _ (root_isPrimitive.ne_zero (by norm_num))

/-- Equality of squared exponents identifies real root classes up to
inversion. -/
theorem classRoot_eq_pow_or_inv_of_sq
    (r : Cyc) (target : ℕ)
    (hsquare :
      ((classExponent r : ZMod 607) ^ 2) =
        ((target : ℕ) : ZMod 607) ^ 2) :
    classRoot r = (14674 : ZMod 20639) ^ target ∨
      classRoot r = ((14674 : ZMod 20639) ^ target)⁻¹ := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with hsame | hneg
  · have hmod : classExponent r ≡ target [MOD 607] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      exact hsame
    have hp :
        (14674 : ZMod 20639) ^ classExponent r =
          (14674 : ZMod 20639) ^ target :=
      pow_eq_pow_of_modEq hmod root_isPrimitive.pow_eq_one
    exact Or.inl (by simpa only [classRoot] using hp)
  · have hcast :
        ((classExponent r + target : ℕ) : ZMod 607) = 0 := by
      push_cast
      rw [hneg]
      simp
    have hmod : classExponent r + target ≡ 0 [MOD 607] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      exact hcast
    have hp :
        (14674 : ZMod 20639) ^ classExponent r *
            (14674 : ZMod 20639) ^ target = 1 := by
      rw [← pow_add]
      simpa using pow_eq_pow_of_modEq hmod root_isPrimitive.pow_eq_one
    have htarget0 : (14674 : ZMod 20639) ^ target ≠ 0 :=
      pow_ne_zero _ (root_isPrimitive.ne_zero (by norm_num))
    exact Or.inr (by
      simpa only [classRoot] using
        (mul_eq_one_iff_eq_inv₀ htarget0).mp hp)

/-- The weight is invariant under inversion, so it descends to real Galois
classes. -/
theorem weight_inv (x : ZMod 20639) (hx : x ≠ 0) :
    weight x⁻¹ = weight x := by
  simp only [weight, inv_pow]
  field_simp [hx]
  ring

/-- Phase relative to the omitted real class `[303]`. -/
def phaseValue (r : Cyc) : ZMod 20639 :=
  weight (classRoot r) / weight (classRoot 0)

theorem weight_classRoot_ne_zero (r : Cyc) : weight (classRoot r) ≠ 0 := by
  apply div_ne_zero
  · exact pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm (classRoot_ne_one r)))
  · exact pow_ne_zero _ (classRoot_ne_zero r)

theorem weight_ratio_eq_phase_ratio (r s : Cyc) :
    weight (classRoot (r + s)) / weight (classRoot r) =
      phaseValue (r + s) / phaseValue r := by
  simp only [phaseValue]
  field_simp [weight_classRoot_ne_zero]

/-- Subtraction in `ZMod 607` is division of powers of the primitive root. -/
theorem root_pow_sub_val (a b : ZMod 607) :
    (14674 : ZMod 20639) ^ (a - b).val =
      (14674 : ZMod 20639) ^ a.val /
        (14674 : ZMod 20639) ^ b.val := by
  have hmod : (a - b).val + b.val ≡ a.val [MOD 607] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simp
  have hpow := pow_eq_pow_of_modEq hmod root_isPrimitive.pow_eq_one
  have hroot0 : (14674 : ZMod 20639) ≠ 0 :=
    root_isPrimitive.ne_zero (by norm_num)
  field_simp [hroot0]
  simpa [pow_add] using hpow

end Fermat.SixHundredSeven.CircularUnitEntryCertificate
