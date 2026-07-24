import Fermat.Irregular.CircularUnitResidues
import Fermat.FourHundredNinetyOne.FirstCase
import Fermat.FourHundredNinetyOne.CircularUnitMatrix

/-!
# Compressed finite-field provenance at exponent 491

At `983 = 2 * 491 + 1`, the package fixes `2`, an element of exact order
`491`.  Instead of checking 59,536 unrelated entries, this file proves the
structural identity

`normalizedUnitValue² = W(x^a) / W(x)`, where `W(x) = (1-x)²/x`,

checks the 245 cyclic phase values, and checks the two finite real-class
reindexings.  Invariance of `W` under inversion then reconstructs every
entry of the uploaded matrix.
-/

namespace Fermat.FourHundredNinetyOne.CircularUnitEntryCertificate

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitResidues
open Fermat.FourHundredNinetyOne.CircularUnitCyclic
open Fermat.FourHundredNinetyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 491) :=
  ⟨Fermat.FourHundredNinetyOne.prime_491⟩
local instance : Fact (Nat.Prime 983) :=
  ⟨Fermat.FourHundredNinetyOne.prime_983⟩

/-- The package root `2 mod 983` has exact order `491`. -/
theorem root_order : orderOf (2 : ZMod 983) = 491 := by
  apply orderOf_eq_prime
  · decide
  · decide

/-- The package root is primitive of order `491`. -/
theorem root_isPrimitive : IsPrimitiveRoot (2 : ZMod 983) 491 :=
  IsPrimitiveRoot.iff_orderOf.mpr root_order

/-- The inversion-invariant weight whose quotients are the normalized
quadratic residue symbols. -/
def weight (x : ZMod 983) : ZMod 983 :=
  (1 - x) ^ 2 / x

/-- Squaring a normalized circular unit is exactly a quotient of weights. -/
theorem normalized_pow_eq_weight_ratio (j i : Fin 244) :
    normalizedUnitValue (p := 491) (2 : ZMod 983) j i ^ 2 =
      weight (embeddingRoot (p := 491) (2 : ZMod 983) j ^ (i.val + 2)) /
        weight (embeddingRoot (p := 491) (2 : ZMod 983) j) := by
  let x : ZMod 983 := embeddingRoot (p := 491) (2 : ZMod 983) j
  let a : Nat := i.val + 2
  let e : Nat := canonicalNormalizationExponent (p := 491) a
  have hxprim : IsPrimitiveRoot x 491 := by
    exact embeddingRoot_isPrimitive (p := 491) (q := 983) (by norm_num)
      root_isPrimitive j
  have hx0 : x ≠ 0 := hxprim.ne_zero (by norm_num)
  have hx1 : 1 - x ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (hxprim.ne_one (by norm_num)))
  have hnorm : 2 * e + a ≡ 1 [MOD 491] :=
    canonicalNormalizationExponent_modEq (p := 491) (by norm_num) a
  have hpow : x ^ (2 * e + a) = x := by
    simpa using pow_eq_pow_of_modEq hnorm hxprim.pow_eq_one
  change (x ^ e * (1 - x ^ a) / (1 - x)) ^ 2 =
    weight (x ^ a) / weight x
  simp only [weight, mul_pow, div_pow]
  field_simp [hx0, hx1]
  have hpow' : x ^ (e * 2) * x ^ a = x := by
    rw [← pow_add]
    simpa [Nat.mul_comm] using hpow
  calc
    _ = (x ^ (e * 2) * x ^ a) * (1 - x ^ a) ^ 2 := by ring
    _ = x * (1 - x ^ a) ^ 2 := by rw [hpow']
    _ = _ := by ring

/-- Real Galois class `[245]·[2]^r`, represented modulo `491`. -/
def classExponent (r : Cyc) : Nat :=
  ((245 : ZMod 491) * (2 : ZMod 491) ^ r.val).val

/-- The corresponding order-`491` root at the split prime. -/
def classRoot (r : Cyc) : ZMod 983 :=
  (2 : ZMod 983) ^ classExponent r

/-- The weight is invariant under inversion, hence descends to real
Galois classes. -/
theorem weight_inv (x : ZMod 983) (hx : x ≠ 0) :
    weight x⁻¹ = weight x := by
  simp only [weight]
  field_simp [hx]
  ring

/-- Phase relative to the omitted real class `[245]`. -/
def phaseValue (r : Cyc) : ZMod 983 :=
  weight (classRoot r) / weight (classRoot 0)

/-- The 245 kernel-checked discrete logarithms of the relative phases. -/
theorem phase_value_certificate (r : Cyc) :
    phaseValue r = (2 : ZMod 983) ^ (symbolPhase r).val := by
  have hr : classRoot r ≠ 0 :=
    pow_ne_zero _ (root_isPrimitive.ne_zero (by norm_num))
  have hzero : classRoot 0 ≠ 0 :=
    pow_ne_zero _ (root_isPrimitive.ne_zero (by norm_num))
  have hzero1 : 1 - classRoot 0 ≠ 0 := by
    decide +kernel
  unfold phaseValue weight
  field_simp [hr, hzero, hzero1]
  decide +revert

/-- Every original row has its recorded real cyclic coordinate. -/
theorem row_root_relation (j : Fin 244) :
    classRoot (coord (rowPermutation j)) =
        embeddingRoot (p := 491) (2 : ZMod 983) j ∨
      classRoot (coord (rowPermutation j)) =
        (embeddingRoot (p := 491) (2 : ZMod 983) j)⁻¹ := by
  let x := embeddingRoot (p := 491) (2 : ZMod 983) j
  have hx : x ≠ 0 :=
    (embeddingRoot_isPrimitive (p := 491) (q := 983) (by norm_num)
      root_isPrimitive j).ne_zero (by norm_num)
  have h :
      classRoot (coord (rowPermutation j)) = x ∨
        classRoot (coord (rowPermutation j)) * x = 1 := by
    decide +revert
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr ((mul_eq_one_iff_eq_inv₀ hx).mp h)

/-- Multiplication by a unit coordinate adds the cyclic exponents, up to
the harmless real-class sign. -/
theorem product_root_relation (j i : Fin 244) :
    classRoot (coord (rowPermutation j) + coord (columnPermutation i)) =
        embeddingRoot (p := 491) (2 : ZMod 983) j ^ (i.val + 2) ∨
      classRoot (coord (rowPermutation j) + coord (columnPermutation i)) =
        (embeddingRoot (p := 491) (2 : ZMod 983) j ^ (i.val + 2))⁻¹ := by
  let x := embeddingRoot (p := 491) (2 : ZMod 983) j ^ (i.val + 2)
  have hx : x ≠ 0 :=
    pow_ne_zero _ ((embeddingRoot_isPrimitive (p := 491) (q := 983)
      (by norm_num) root_isPrimitive j).ne_zero (by norm_num))
  have h :
      classRoot (coord (rowPermutation j) + coord (columnPermutation i)) = x ∨
        classRoot (coord (rowPermutation j) + coord (columnPermutation i)) * x = 1 := by
    decide +revert
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr ((mul_eq_one_iff_eq_inv₀ hx).mp h)

theorem classRoot_ne_zero (r : Cyc) : classRoot r ≠ 0 := by
  exact pow_ne_zero _ (root_isPrimitive.ne_zero (by norm_num))

theorem classRoot_ne_one (r : Cyc) : classRoot r ≠ 1 := by
  decide +revert

theorem weight_classRoot_ne_zero (r : Cyc) : weight (classRoot r) ≠ 0 := by
  apply div_ne_zero
  · exact pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm (classRoot_ne_one r)))
  · exact classRoot_ne_zero r

theorem weight_ratio_eq_phase_ratio (r s : Cyc) :
    weight (classRoot (r + s)) / weight (classRoot r) =
      phaseValue (r + s) / phaseValue r := by
  simp only [phaseValue]
  field_simp [weight_classRoot_ne_zero]

/-- Subtraction in `ZMod 491` is division of powers of the primitive root. -/
theorem root_pow_sub_val (a b : ZMod 491) :
    (2 : ZMod 983) ^ (a - b).val =
      (2 : ZMod 983) ^ a.val / (2 : ZMod 983) ^ b.val := by
  have hmod : (a - b).val + b.val ≡ a.val [MOD 491] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simp
  have hpow := pow_eq_pow_of_modEq hmod root_isPrimitive.pow_eq_one
  have hroot0 : (2 : ZMod 983) ≠ 0 :=
    root_isPrimitive.ne_zero (by norm_num)
  field_simp [hroot0]
  simpa [pow_add] using hpow

/-- Every compressed entry is the discrete logarithm of the corresponding
quadratic residue symbol. -/
theorem matrix_entry_certificate (j i : Fin 244) :
    normalizedUnitValue (p := 491) (2 : ZMod 983) j i ^ 2 =
      (2 : ZMod 983) ^ (matrix j i).val := by
  let x : ZMod 983 := embeddingRoot (p := 491) (2 : ZMod 983) j
  let a : Nat := i.val + 2
  let r : Cyc := coord (rowPermutation j)
  let s : Cyc := coord (columnPermutation i)
  have hx0 : x ≠ 0 := by
    exact (embeddingRoot_isPrimitive (p := 491) (q := 983) (by norm_num)
      root_isPrimitive j).ne_zero (by norm_num)
  have hrowWeight : weight x = weight (classRoot r) := by
    rcases row_root_relation j with h | h
    · exact congrArg weight h.symm
    · calc
        weight x = weight x⁻¹ := (weight_inv x hx0).symm
        _ = weight (classRoot r) := congrArg weight h.symm
  have hprodWeight : weight (x ^ a) = weight (classRoot (r + s)) := by
    rcases product_root_relation j i with h | h
    · exact congrArg weight h.symm
    · calc
        weight (x ^ a) = weight (x ^ a)⁻¹ :=
          (weight_inv (x ^ a) (pow_ne_zero _ hx0)).symm
        _ = weight (classRoot (r + s)) := congrArg weight h.symm
  rw [normalized_pow_eq_weight_ratio]
  change weight (x ^ a) / weight x = _
  rw [hprodWeight, hrowWeight, weight_ratio_eq_phase_ratio,
    phase_value_certificate, phase_value_certificate]
  rw [← root_pow_sub_val]
  rfl

end Fermat.FourHundredNinetyOne.CircularUnitEntryCertificate
