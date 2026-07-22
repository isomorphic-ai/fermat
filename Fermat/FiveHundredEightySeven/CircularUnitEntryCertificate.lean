import Fermat.Irregular.CircularUnitResidues
import Fermat.FiveHundredEightySeven.FirstCase
import Fermat.FiveHundredEightySeven.CircularUnitMatrix

/-!
# Compressed finite-field provenance at exponent 587

At `8219 = 14 * 587 + 1`, the package fixes `8165 = 2^14`, an element of
exact order `587`.  A direct entry-by-entry check would repeat the same
finite-field calculation 85,264 times.  Instead this module proves the
structural identity

`normalizedUnitValue^14 = W(x^a) / W(x)`, where
`W(x) = (1-x)^14 / x^7`,

checks the 293 cyclic phase values, and checks only the finite real-class
reindexing.  Invariance of `W` under inversion then reconstructs every
matrix entry.
-/

namespace Fermat.FiveHundredEightySeven.CircularUnitEntryCertificate

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitResidues
open Fermat.FiveHundredEightySeven.CircularUnitCyclic
open Fermat.FiveHundredEightySeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 587) :=
  ⟨Fermat.FiveHundredEightySeven.prime_587⟩
local instance : Fact (Nat.Prime 8219) :=
  ⟨Fermat.FiveHundredEightySeven.prime_8219⟩

/-- The package root `8165 = 2^14 mod 8219` has exact order `587`. -/
theorem root_order : orderOf (8165 : ZMod 8219) = 587 := by
  apply orderOf_eq_prime
  · decide
  · decide

/-- The package root is primitive of order `587`. -/
theorem root_isPrimitive : IsPrimitiveRoot (8165 : ZMod 8219) 587 :=
  IsPrimitiveRoot.iff_orderOf.mpr root_order

/-- The inversion-invariant weight whose quotients are the normalized
fourteenth-power residue symbols. -/
def weight (x : ZMod 8219) : ZMod 8219 :=
  (1 - x) ^ 14 / x ^ 7

/-- Raising a normalized circular unit to the symbol exponent is exactly a
quotient of two weights. -/
theorem normalized_pow_eq_weight_ratio (j i : Fin 292) :
    normalizedUnitValue (p := 587) (8165 : ZMod 8219) j i ^ 14 =
      weight (embeddingRoot (p := 587) (8165 : ZMod 8219) j ^ (i.val + 2)) /
        weight (embeddingRoot (p := 587) (8165 : ZMod 8219) j) := by
  let x : ZMod 8219 := embeddingRoot (p := 587) (8165 : ZMod 8219) j
  let a : Nat := i.val + 2
  let e : Nat := canonicalNormalizationExponent (p := 587) a
  have hxprim : IsPrimitiveRoot x 587 := by
    exact embeddingRoot_isPrimitive (p := 587) (q := 8219) (by norm_num)
      root_isPrimitive j
  have hx0 : x ≠ 0 := hxprim.ne_zero (by norm_num)
  have hx1 : 1 - x ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (hxprim.ne_one (by norm_num)))
  have hnorm : 2 * e + a ≡ 1 [MOD 587] :=
    canonicalNormalizationExponent_modEq (p := 587) (by norm_num) a
  have hnorm7 : 7 * (2 * e + a) ≡ 7 * 1 [MOD 587] := hnorm.mul_left 7
  have hexp : 14 * e + 7 * a ≡ 7 [MOD 587] := by
    convert hnorm7 using 1 <;> omega
  have hpow : x ^ (14 * e + 7 * a) = x ^ 7 :=
    pow_eq_pow_of_modEq hexp hxprim.pow_eq_one
  change (x ^ e * (1 - x ^ a) / (1 - x)) ^ 14 =
    weight (x ^ a) / weight x
  simp only [weight, mul_pow, div_pow]
  field_simp [hx0, hx1]
  have hpow' : x ^ (e * 14) * x ^ (a * 7) = x ^ 7 := by
    rw [← pow_add]
    simpa [Nat.mul_comm] using hpow
  calc
    _ = (x ^ (e * 14) * x ^ (a * 7)) * (1 - x ^ a) ^ 14 := by ring
    _ = x ^ 7 * (1 - x ^ a) ^ 14 := by rw [hpow']
    _ = _ := by ring

/-- Real Galois class `[293]·[2]^r`, represented modulo `587`. -/
def classExponent (r : Cyc) : Nat :=
  ((293 : ZMod 587) * (2 : ZMod 587) ^ r.val).val

/-- The corresponding order-`587` root at the split prime. -/
def classRoot (r : Cyc) : ZMod 8219 :=
  (8165 : ZMod 8219) ^ classExponent r

/-- The weight is invariant under inversion, so it descends to real
Galois classes. -/
theorem weight_inv (x : ZMod 8219) (hx : x ≠ 0) :
    weight x⁻¹ = weight x := by
  simp only [weight, inv_pow]
  field_simp [hx]
  ring

/-- Phase relative to the omitted real class `[293]`. -/
def phaseValue (r : Cyc) : ZMod 8219 :=
  weight (classRoot r) / weight (classRoot 0)

/-- The 293 kernel-checked discrete logarithms of the relative phases. -/
theorem phase_value_certificate (r : Cyc) :
    phaseValue r = (8165 : ZMod 8219) ^ (symbolPhase r).val := by
  decide +revert

/-- Every original row has the recorded real cyclic coordinate. -/
theorem row_root_relation (j : Fin 292) :
    classRoot (coord (rowPermutation j)) =
        embeddingRoot (p := 587) (8165 : ZMod 8219) j ∨
      classRoot (coord (rowPermutation j)) =
        (embeddingRoot (p := 587) (8165 : ZMod 8219) j)⁻¹ := by
  decide +revert

/-- Multiplying an embedding coordinate by a unit coordinate gives the
sum of their cyclic exponents, up to the harmless real-class sign. -/
theorem product_root_relation (j i : Fin 292) :
    classRoot (coord (rowPermutation j) + coord (columnPermutation i)) =
        embeddingRoot (p := 587) (8165 : ZMod 8219) j ^ (i.val + 2) ∨
      classRoot (coord (rowPermutation j) + coord (columnPermutation i)) =
        (embeddingRoot (p := 587) (8165 : ZMod 8219) j ^ (i.val + 2))⁻¹ := by
  decide +revert

theorem classRoot_ne_zero (r : Cyc) : classRoot r ≠ 0 := by
  exact pow_ne_zero _ (root_isPrimitive.ne_zero (by norm_num))

theorem classRoot_ne_one (r : Cyc) : classRoot r ≠ 1 := by
  decide +revert

theorem weight_classRoot_ne_zero (r : Cyc) : weight (classRoot r) ≠ 0 := by
  apply div_ne_zero
  · exact pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm (classRoot_ne_one r)))
  · exact pow_ne_zero _ (classRoot_ne_zero r)

theorem weight_ratio_eq_phase_ratio (r s : Cyc) :
    weight (classRoot (r + s)) / weight (classRoot r) =
      phaseValue (r + s) / phaseValue r := by
  simp only [phaseValue]
  field_simp [weight_classRoot_ne_zero]

/-- Subtraction in `ZMod 587` is division of powers of the primitive root. -/
theorem root_pow_sub_val (a b : ZMod 587) :
    (8165 : ZMod 8219) ^ (a - b).val =
      (8165 : ZMod 8219) ^ a.val / (8165 : ZMod 8219) ^ b.val := by
  have hmod : (a - b).val + b.val ≡ a.val [MOD 587] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simp
  have hpow := pow_eq_pow_of_modEq hmod root_isPrimitive.pow_eq_one
  have hroot0 : (8165 : ZMod 8219) ≠ 0 :=
    root_isPrimitive.ne_zero (by norm_num)
  field_simp [hroot0]
  simpa [pow_add] using hpow

/-- Every compressed entry is the discrete logarithm of the corresponding
fourteenth-power residue symbol. -/
theorem matrix_entry_certificate (j i : Fin 292) :
    normalizedUnitValue (p := 587) (8165 : ZMod 8219) j i ^ 14 =
      (8165 : ZMod 8219) ^ (matrix j i).val := by
  let x : ZMod 8219 := embeddingRoot (p := 587) (8165 : ZMod 8219) j
  let a : Nat := i.val + 2
  let r : Cyc := coord (rowPermutation j)
  let s : Cyc := coord (columnPermutation i)
  have hx0 : x ≠ 0 := by
    exact (embeddingRoot_isPrimitive (p := 587) (q := 8219) (by norm_num)
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

end Fermat.FiveHundredEightySeven.CircularUnitEntryCertificate
