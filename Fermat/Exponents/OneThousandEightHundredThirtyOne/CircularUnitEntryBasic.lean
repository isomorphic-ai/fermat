import Fermat.Descent.Irregular.CircularUnitResidues
import Fermat.Exponents.OneThousandEightHundredThirtyOne.FirstCase
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitMatrix

/-!
# Structural finite-field provenance at exponent 1831

At `358877 = 196 * 1831 + 1`, the source fixes `266093`, an element of
exact order `1831`. The normalized circular-unit symbols are quotients of
the inversion-invariant weight

`W(x) = (1 - x)^196 / x^98`.

This file contains the algebraic part of the entry reconstruction.  The
finite phase and coordinate data are certified in separate one-dimensional
modules before the final entry theorem is assembled.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitEntryCertificate

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitResidues
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitCyclic
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 1831) :=
  ⟨Fermat.OneThousandEightHundredThirtyOne.prime_1831⟩
local instance : Fact (Nat.Prime 358877) :=
  ⟨Fermat.OneThousandEightHundredThirtyOne.prime_358877⟩

/-- The package root `266093 = 2^196 mod 358877` has exact order `1831`. -/
theorem root_order : orderOf (266093 : ZMod 358877) = 1831 := by
  apply orderOf_eq_prime
  · decide
  · decide

/-- The package root is primitive of order `1831`. -/
theorem root_isPrimitive : IsPrimitiveRoot (266093 : ZMod 358877) 1831 :=
  IsPrimitiveRoot.iff_orderOf.mpr root_order

/-- The inversion-invariant weight whose quotients are the normalized
one-hundred-ninety-sixth-power residue symbols. -/
def weight (x : ZMod 358877) : ZMod 358877 :=
  (1 - x) ^ 196 / x ^ 98

/-- Raising a normalized circular unit to the symbol exponent is exactly a
quotient of two weights. -/
theorem normalized_pow_eq_weight_ratio (j i : Fin 914) :
    normalizedUnitValue (p := 1831) (266093 : ZMod 358877) j i ^ 196 =
      weight
          (embeddingRoot (p := 1831) (266093 : ZMod 358877) j ^ (i.val + 2)) /
        weight (embeddingRoot (p := 1831) (266093 : ZMod 358877) j) := by
  let x : ZMod 358877 :=
    embeddingRoot (p := 1831) (266093 : ZMod 358877) j
  let a : Nat := i.val + 2
  let e : Nat := canonicalNormalizationExponent (p := 1831) a
  have hxprim : IsPrimitiveRoot x 1831 := by
    exact embeddingRoot_isPrimitive (p := 1831) (q := 358877) (by norm_num)
      root_isPrimitive j
  have hx0 : x ≠ 0 := hxprim.ne_zero (by norm_num)
  have hx1 : 1 - x ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (hxprim.ne_one (by norm_num)))
  have hnorm : 2 * e + a ≡ 1 [MOD 1831] :=
    canonicalNormalizationExponent_modEq (p := 1831) (by norm_num) a
  have hnorm98 : 98 * (2 * e + a) ≡ 98 * 1 [MOD 1831] :=
    hnorm.mul_left 98
  have hexp : 196 * e + 98 * a ≡ 98 [MOD 1831] := by
    convert hnorm98 using 1; omega
  have hpow : x ^ (196 * e + 98 * a) = x ^ 98 :=
    pow_eq_pow_of_modEq hexp hxprim.pow_eq_one
  change (x ^ e * (1 - x ^ a) / (1 - x)) ^ 196 =
    weight (x ^ a) / weight x
  simp only [weight, mul_pow, div_pow]
  field_simp [hx0, hx1]
  have hpow' : x ^ (e * 196) * x ^ (a * 98) = x ^ 98 := by
    rw [← pow_add]
    simpa [Nat.mul_comm] using hpow
  calc
    _ = (x ^ (e * 196) * x ^ (a * 98)) * (1 - x ^ a) ^ 196 := by ring
    _ = x ^ 98 * (1 - x ^ a) ^ 196 := by rw [hpow']
    _ = _ := by ring

/-- Real Galois class `[915]·[3]^r`, represented modulo `1831`. -/
def classExponent (r : Cyc) : Nat :=
  ((915 : ZMod 1831) * (3 : ZMod 1831) ^ r.val).val

/-- Casting the canonical representative recovers its defining residue
class. -/
theorem classExponent_cast (r : Cyc) :
    (classExponent r : ZMod 1831) =
      (915 : ZMod 1831) * (3 : ZMod 1831) ^ r.val := by
  exact ZMod.natCast_zmod_val _

/-- The corresponding order-`1831` root at the split prime. -/
def classRoot (r : Cyc) : ZMod 358877 :=
  (266093 : ZMod 358877) ^ classExponent r

/-- Squaring a power of `3` turns it into the corresponding power of `9`. -/
theorem three_pow_sq (n : ℕ) :
    (((3 : ZMod 1831) ^ n) ^ 2) = (9 : ZMod 1831) ^ n := by
  calc
    (((3 : ZMod 1831) ^ n) ^ 2) =
        (3 : ZMod 1831) ^ (n * 2) := (pow_mul _ n 2).symm
    _ = (3 : ZMod 1831) ^ (2 * n) := by rw [Nat.mul_comm]
    _ = ((3 : ZMod 1831) ^ 2) ^ n := pow_mul _ 2 n
    _ = (9 : ZMod 1831) ^ n := by norm_num

/-- `9` has period dividing the real cycle length modulo `1831`. -/
theorem nine_pow_cycleLength : (9 : ZMod 1831) ^ 915 = 1 := by
  decide

/-- Addition of real cyclic coordinates multiplies the corresponding
class exponents after squaring.  Squaring removes the harmless sign from
reduction modulo the real cycle length `915`. -/
theorem classExponent_add_sq (r s : Cyc) :
    ((classExponent (r + s) : ZMod 1831) ^ 2) =
      ((classExponent r : ZMod 1831) ^ 2) *
        (((3 : ZMod 1831) ^ s.val) ^ 2) := by
  have hmod : (r + s).val ≡ r.val + s.val [MOD 915] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simp
  have hnine :
      (9 : ZMod 1831) ^ (r + s).val =
        (9 : ZMod 1831) ^ (r.val + s.val) :=
    pow_eq_pow_of_modEq hmod nine_pow_cycleLength
  rw [classExponent_cast, classExponent_cast, mul_pow, mul_pow,
    three_pow_sq, three_pow_sq, three_pow_sq, hnine, pow_add]
  ring

/-- Every represented class exponent is nonzero modulo `1831`. -/
theorem classExponent_ne_zero (r : Cyc) : classExponent r ≠ 0 := by
  intro hzero
  have hcast : (classExponent r : ZMod 1831) = 0 := by simp [hzero]
  rw [classExponent_cast] at hcast
  exact (mul_ne_zero (by decide) (pow_ne_zero _ (by decide))) hcast

/-- Canonical class exponents lie below the modulus. -/
theorem classExponent_lt (r : Cyc) : classExponent r < 1831 :=
  ZMod.val_lt _

/-- No represented real class is the trivial `1831`-st root. -/
theorem classRoot_ne_one (r : Cyc) : classRoot r ≠ 1 := by
  intro hone
  have hdvd : 1831 ∣ classExponent r :=
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
      ((classExponent r : ZMod 1831) ^ 2) =
        ((target : ℕ) : ZMod 1831) ^ 2) :
    classRoot r = (266093 : ZMod 358877) ^ target ∨
      classRoot r = ((266093 : ZMod 358877) ^ target)⁻¹ := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with hsame | hneg
  · have hmod : classExponent r ≡ target [MOD 1831] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      exact hsame
    have hp :
        (266093 : ZMod 358877) ^ classExponent r =
          (266093 : ZMod 358877) ^ target :=
      pow_eq_pow_of_modEq hmod root_isPrimitive.pow_eq_one
    exact Or.inl (by simpa only [classRoot] using hp)
  · have hcast :
        ((classExponent r + target : ℕ) : ZMod 1831) = 0 := by
      push_cast
      rw [hneg]
      simp
    have hmod : classExponent r + target ≡ 0 [MOD 1831] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      exact hcast
    have hp :
        (266093 : ZMod 358877) ^ classExponent r *
            (266093 : ZMod 358877) ^ target = 1 := by
      rw [← pow_add]
      simpa using pow_eq_pow_of_modEq hmod root_isPrimitive.pow_eq_one
    have htarget0 : (266093 : ZMod 358877) ^ target ≠ 0 :=
      pow_ne_zero _ (root_isPrimitive.ne_zero (by norm_num))
    exact Or.inr (by
      simpa only [classRoot] using
        (mul_eq_one_iff_eq_inv₀ htarget0).mp hp)

/-- The weight is invariant under inversion, so it descends to real
Galois classes. -/
theorem weight_inv (x : ZMod 358877) (hx : x ≠ 0) :
    weight x⁻¹ = weight x := by
  simp only [weight, inv_pow]
  field_simp [hx]
  ring

/-- Phase relative to the omitted real class `[915]`. -/
def phaseValue (r : Cyc) : ZMod 358877 :=
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

/-- Subtraction in `ZMod 1831` is division of powers of the primitive
root. -/
theorem root_pow_sub_val (a b : ZMod 1831) :
    (266093 : ZMod 358877) ^ (a - b).val =
      (266093 : ZMod 358877) ^ a.val /
        (266093 : ZMod 358877) ^ b.val := by
  have hmod : (a - b).val + b.val ≡ a.val [MOD 1831] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simp
  have hpow := pow_eq_pow_of_modEq hmod root_isPrimitive.pow_eq_one
  have hroot0 : (266093 : ZMod 358877) ≠ 0 :=
    root_isPrimitive.ne_zero (by norm_num)
  field_simp [hroot0]
  simpa [pow_add] using hpow

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitEntryCertificate
