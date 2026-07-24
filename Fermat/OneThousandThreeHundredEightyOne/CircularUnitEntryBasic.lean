import Fermat.Irregular.CircularUnitResidues
import Fermat.OneThousandThreeHundredEightyOne.FirstCase
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitMatrix

/-!
# Structural finite-field provenance at exponent 1381

At `38669 = 28 * 1381 + 1`, the source fixes `33927`, an element of
exact order `1381`. The normalized circular-unit symbols are quotients of
the inversion-invariant weight

`W(x) = (1 - x)^28 / x^14`.

This file contains the algebraic part of the entry reconstruction.  The
finite phase and coordinate data are certified in separate one-dimensional
modules before the final entry theorem is assembled.
-/

namespace Fermat.OneThousandThreeHundredEightyOne.CircularUnitEntryCertificate

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitResidues
open Fermat.OneThousandThreeHundredEightyOne.CircularUnitCyclic
open Fermat.OneThousandThreeHundredEightyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 1381) :=
  ⟨Fermat.OneThousandThreeHundredEightyOne.prime_1381⟩
local instance : Fact (Nat.Prime 38669) :=
  ⟨Fermat.OneThousandThreeHundredEightyOne.prime_38669⟩

/-- The package root `33927 = 2^28 mod 38669` has exact order `1381`. -/
theorem root_order : orderOf (33927 : ZMod 38669) = 1381 := by
  apply orderOf_eq_prime
  · decide
  · decide

/-- The package root is primitive of order `1381`. -/
theorem root_isPrimitive : IsPrimitiveRoot (33927 : ZMod 38669) 1381 :=
  IsPrimitiveRoot.iff_orderOf.mpr root_order

/-- The inversion-invariant weight whose quotients are the normalized
twenty-eighth-power residue symbols. -/
def weight (x : ZMod 38669) : ZMod 38669 :=
  (1 - x) ^ 28 / x ^ 14

/-- Raising a normalized circular unit to the symbol exponent is exactly a
quotient of two weights. -/
theorem normalized_pow_eq_weight_ratio (j i : Fin 689) :
    normalizedUnitValue (p := 1381) (33927 : ZMod 38669) j i ^ 28 =
      weight
          (embeddingRoot (p := 1381) (33927 : ZMod 38669) j ^ (i.val + 2)) /
        weight (embeddingRoot (p := 1381) (33927 : ZMod 38669) j) := by
  let x : ZMod 38669 :=
    embeddingRoot (p := 1381) (33927 : ZMod 38669) j
  let a : Nat := i.val + 2
  let e : Nat := canonicalNormalizationExponent (p := 1381) a
  have hxprim : IsPrimitiveRoot x 1381 := by
    exact embeddingRoot_isPrimitive (p := 1381) (q := 38669) (by norm_num)
      root_isPrimitive j
  have hx0 : x ≠ 0 := hxprim.ne_zero (by norm_num)
  have hx1 : 1 - x ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (hxprim.ne_one (by norm_num)))
  have hnorm : 2 * e + a ≡ 1 [MOD 1381] :=
    canonicalNormalizationExponent_modEq (p := 1381) (by norm_num) a
  have hnorm14 : 14 * (2 * e + a) ≡ 14 * 1 [MOD 1381] :=
    hnorm.mul_left 14
  have hexp : 28 * e + 14 * a ≡ 14 [MOD 1381] := by
    convert hnorm14 using 1 <;> omega
  have hpow : x ^ (28 * e + 14 * a) = x ^ 14 :=
    pow_eq_pow_of_modEq hexp hxprim.pow_eq_one
  change (x ^ e * (1 - x ^ a) / (1 - x)) ^ 28 =
    weight (x ^ a) / weight x
  simp only [weight, mul_pow, div_pow]
  field_simp [hx0, hx1]
  have hpow' : x ^ (e * 28) * x ^ (a * 14) = x ^ 14 := by
    rw [← pow_add]
    simpa [Nat.mul_comm] using hpow
  calc
    _ = (x ^ (e * 28) * x ^ (a * 14)) * (1 - x ^ a) ^ 28 := by ring
    _ = x ^ 14 * (1 - x ^ a) ^ 28 := by rw [hpow']
    _ = _ := by ring

/-- Real Galois class `[690]·[2]^r`, represented modulo `1381`. -/
def classExponent (r : Cyc) : Nat :=
  ((690 : ZMod 1381) * (2 : ZMod 1381) ^ r.val).val

/-- Casting the canonical representative recovers its defining residue
class. -/
theorem classExponent_cast (r : Cyc) :
    (classExponent r : ZMod 1381) =
      (690 : ZMod 1381) * (2 : ZMod 1381) ^ r.val := by
  exact ZMod.natCast_zmod_val _

/-- The corresponding order-`1381` root at the split prime. -/
def classRoot (r : Cyc) : ZMod 38669 :=
  (33927 : ZMod 38669) ^ classExponent r

/-- Squaring a power of `2` turns it into the corresponding power of `4`. -/
theorem two_pow_sq (n : ℕ) :
    (((2 : ZMod 1381) ^ n) ^ 2) = (4 : ZMod 1381) ^ n := by
  calc
    (((2 : ZMod 1381) ^ n) ^ 2) =
        (2 : ZMod 1381) ^ (n * 2) := (pow_mul _ n 2).symm
    _ = (2 : ZMod 1381) ^ (2 * n) := by rw [Nat.mul_comm]
    _ = ((2 : ZMod 1381) ^ 2) ^ n := pow_mul _ 2 n
    _ = (4 : ZMod 1381) ^ n := by norm_num

/-- `4` has period dividing the real cycle length modulo `1381`. -/
theorem four_pow_cycleLength : (4 : ZMod 1381) ^ 690 = 1 := by
  decide

/-- Addition of real cyclic coordinates multiplies the corresponding
class exponents after squaring.  Squaring removes the harmless sign from
reduction modulo the real cycle length `690`. -/
theorem classExponent_add_sq (r s : Cyc) :
    ((classExponent (r + s) : ZMod 1381) ^ 2) =
      ((classExponent r : ZMod 1381) ^ 2) *
        (((2 : ZMod 1381) ^ s.val) ^ 2) := by
  have hmod : (r + s).val ≡ r.val + s.val [MOD 690] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simp
  have hfour :
      (4 : ZMod 1381) ^ (r + s).val =
        (4 : ZMod 1381) ^ (r.val + s.val) :=
    pow_eq_pow_of_modEq hmod four_pow_cycleLength
  rw [classExponent_cast, classExponent_cast, mul_pow, mul_pow,
    two_pow_sq, two_pow_sq, two_pow_sq, hfour, pow_add]
  ring

/-- Every represented class exponent is nonzero modulo `1381`. -/
theorem classExponent_ne_zero (r : Cyc) : classExponent r ≠ 0 := by
  intro hzero
  have hcast : (classExponent r : ZMod 1381) = 0 := by simp [hzero]
  rw [classExponent_cast] at hcast
  exact (mul_ne_zero (by decide) (pow_ne_zero _ (by decide))) hcast

/-- Canonical class exponents lie below the modulus. -/
theorem classExponent_lt (r : Cyc) : classExponent r < 1381 :=
  ZMod.val_lt _

/-- No represented real class is the trivial `1381`-st root. -/
theorem classRoot_ne_one (r : Cyc) : classRoot r ≠ 1 := by
  intro hone
  have hdvd : 1381 ∣ classExponent r :=
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
      ((classExponent r : ZMod 1381) ^ 2) =
        ((target : ℕ) : ZMod 1381) ^ 2) :
    classRoot r = (33927 : ZMod 38669) ^ target ∨
      classRoot r = ((33927 : ZMod 38669) ^ target)⁻¹ := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with hsame | hneg
  · have hmod : classExponent r ≡ target [MOD 1381] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      exact hsame
    have hp :
        (33927 : ZMod 38669) ^ classExponent r =
          (33927 : ZMod 38669) ^ target :=
      pow_eq_pow_of_modEq hmod root_isPrimitive.pow_eq_one
    exact Or.inl (by simpa only [classRoot] using hp)
  · have hcast :
        ((classExponent r + target : ℕ) : ZMod 1381) = 0 := by
      push_cast
      rw [hneg]
      simp
    have hmod : classExponent r + target ≡ 0 [MOD 1381] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      exact hcast
    have hp :
        (33927 : ZMod 38669) ^ classExponent r *
            (33927 : ZMod 38669) ^ target = 1 := by
      rw [← pow_add]
      simpa using pow_eq_pow_of_modEq hmod root_isPrimitive.pow_eq_one
    have htarget0 : (33927 : ZMod 38669) ^ target ≠ 0 :=
      pow_ne_zero _ (root_isPrimitive.ne_zero (by norm_num))
    exact Or.inr (by
      simpa only [classRoot] using
        (mul_eq_one_iff_eq_inv₀ htarget0).mp hp)

/-- The weight is invariant under inversion, so it descends to real
Galois classes. -/
theorem weight_inv (x : ZMod 38669) (hx : x ≠ 0) :
    weight x⁻¹ = weight x := by
  simp only [weight, inv_pow]
  field_simp [hx]
  ring

/-- Phase relative to the omitted real class `[690]`. -/
def phaseValue (r : Cyc) : ZMod 38669 :=
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

/-- Subtraction in `ZMod 1381` is division of powers of the primitive
root. -/
theorem root_pow_sub_val (a b : ZMod 1381) :
    (33927 : ZMod 38669) ^ (a - b).val =
      (33927 : ZMod 38669) ^ a.val /
        (33927 : ZMod 38669) ^ b.val := by
  have hmod : (a - b).val + b.val ≡ a.val [MOD 1381] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simp
  have hpow := pow_eq_pow_of_modEq hmod root_isPrimitive.pow_eq_one
  have hroot0 : (33927 : ZMod 38669) ≠ 0 :=
    root_isPrimitive.ne_zero (by norm_num)
  field_simp [hroot0]
  simpa [pow_add] using hpow

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitEntryCertificate
