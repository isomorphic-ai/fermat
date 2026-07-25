import Fermat.Irregular.CircularUnitResidues
import Fermat.SixHundredNinetyOne.FirstCase
import Fermat.SixHundredNinetyOne.CircularUnitMatrix

/-!
# Compressed finite-field provenance at exponent 691

At `11057 = 16 * 691 + 1`, the package fixes `1820`, an element of
exact order `691`. A direct entry-by-entry check would repeat the same
finite-field calculation 118,336 times. Instead this module proves the
structural identity

`normalizedUnitValue^16 = W(x^a) / W(x)`, where
`W(x) = (1-x)^16 / x^8`,

checks the 345 cyclic phase values, and checks only the finite real-class
reindexing. Invariance of `W` under inversion then reconstructs every
matrix entry.
-/

namespace Fermat.SixHundredNinetyOne.CircularUnitEntryCertificate

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitResidues
open Fermat.SixHundredNinetyOne.CircularUnitCyclic
open Fermat.SixHundredNinetyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 691) :=
  ⟨Fermat.SixHundredNinetyOne.prime_691⟩
local instance : Fact (Nat.Prime 11057) :=
  ⟨Fermat.SixHundredNinetyOne.prime_11057⟩

/-- The package root `1820 = 3^16 mod 11057` has exact order `691`. -/
theorem root_order : orderOf (1820 : ZMod 11057) = 691 := by
  apply orderOf_eq_prime
  · decide
  · decide

/-- The package root is primitive of order `691`. -/
theorem root_isPrimitive : IsPrimitiveRoot (1820 : ZMod 11057) 691 :=
  IsPrimitiveRoot.iff_orderOf.mpr root_order

/-- The inversion-invariant weight whose quotients are the normalized
sixteenth-power residue symbols. -/
def weight (x : ZMod 11057) : ZMod 11057 :=
  (1 - x) ^ 16 / x ^ 8

/-- Raising a normalized circular unit to the symbol exponent is exactly a
quotient of two weights. -/
theorem normalized_pow_eq_weight_ratio (j i : Fin 344) :
    normalizedUnitValue (p := 691) (1820 : ZMod 11057) j i ^ 16 =
      weight (embeddingRoot (p := 691) (1820 : ZMod 11057) j ^ (i.val + 2)) /
        weight (embeddingRoot (p := 691) (1820 : ZMod 11057) j) := by
  let x : ZMod 11057 := embeddingRoot (p := 691) (1820 : ZMod 11057) j
  let a : Nat := i.val + 2
  let e : Nat := canonicalNormalizationExponent (p := 691) a
  have hxprim : IsPrimitiveRoot x 691 := by
    exact embeddingRoot_isPrimitive (p := 691) (q := 11057) (by norm_num)
      root_isPrimitive j
  have hx0 : x ≠ 0 := hxprim.ne_zero (by norm_num)
  have hx1 : 1 - x ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (hxprim.ne_one (by norm_num)))
  have hnorm : 2 * e + a ≡ 1 [MOD 691] :=
    canonicalNormalizationExponent_modEq (p := 691) (by norm_num) a
  have hnorm8 : 8 * (2 * e + a) ≡ 8 * 1 [MOD 691] := hnorm.mul_left 8
  have hexp : 16 * e + 8 * a ≡ 8 [MOD 691] := by
    convert hnorm8 using 1 <;> omega
  have hpow : x ^ (16 * e + 8 * a) = x ^ 8 :=
    pow_eq_pow_of_modEq hexp hxprim.pow_eq_one
  change (x ^ e * (1 - x ^ a) / (1 - x)) ^ 16 =
    weight (x ^ a) / weight x
  simp only [weight, mul_pow, div_pow]
  field_simp [hx0, hx1]
  have hpow' : x ^ (e * 16) * x ^ (a * 8) = x ^ 8 := by
    rw [← pow_add]
    simpa [Nat.mul_comm] using hpow
  calc
    _ = (x ^ (e * 16) * x ^ (a * 8)) * (1 - x ^ a) ^ 16 := by ring
    _ = x ^ 8 * (1 - x ^ a) ^ 16 := by rw [hpow']
    _ = _ := by ring

/-- Real Galois class `[345]·[3]^r`, represented modulo `691`. -/
def classExponent (r : Cyc) : Nat :=
  ((345 : ZMod 691) * (3 : ZMod 691) ^ r.val).val

/-- The corresponding order-`691` root at the split prime. -/
def classRoot (r : Cyc) : ZMod 11057 :=
  (1820 : ZMod 11057) ^ classExponent r

/-- The weight is invariant under inversion, so it descends to real
Galois classes. -/
theorem weight_inv (x : ZMod 11057) (hx : x ≠ 0) :
    weight x⁻¹ = weight x := by
  simp only [weight, inv_pow]
  field_simp [hx]
  ring

/-- Phase relative to the omitted real class `[345]`. -/
def phaseValue (r : Cyc) : ZMod 11057 :=
  weight (classRoot r) / weight (classRoot 0)

/-- The 345 kernel-checked discrete logarithms of the relative phases. -/
theorem phase_value_certificate (r : Cyc) :
    phaseValue r = (1820 : ZMod 11057) ^ (symbolPhase r).val := by
  have hr : classRoot r ≠ 0 :=
    pow_ne_zero _ (root_isPrimitive.ne_zero (by norm_num))
  have hzero : classRoot 0 ≠ 0 :=
    pow_ne_zero _ (root_isPrimitive.ne_zero (by norm_num))
  have hzero1 : 1 - classRoot 0 ≠ 0 := by
    decide +kernel
  unfold phaseValue weight
  field_simp [hr, hzero, hzero1]
  decide +revert

/-- Every original row has the recorded real cyclic coordinate. -/
theorem row_root_relation (j : Fin 344) :
    classRoot (coord (rowPermutation j)) =
        embeddingRoot (p := 691) (1820 : ZMod 11057) j ∨
      classRoot (coord (rowPermutation j)) =
        (embeddingRoot (p := 691) (1820 : ZMod 11057) j)⁻¹ := by
  let x := embeddingRoot (p := 691) (1820 : ZMod 11057) j
  have hx : x ≠ 0 :=
    (embeddingRoot_isPrimitive (p := 691) (q := 11057) (by norm_num)
      root_isPrimitive j).ne_zero (by norm_num)
  have h :
      classRoot (coord (rowPermutation j)) = x ∨
        classRoot (coord (rowPermutation j)) * x = 1 := by
    decide +revert
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr ((mul_eq_one_iff_eq_inv₀ hx).mp h)

/-- Multiplying an embedding coordinate by a unit coordinate gives the
sum of their cyclic exponents, up to the harmless real-class sign. -/
theorem product_root_relation (j i : Fin 344) :
    classRoot (coord (rowPermutation j) + coord (columnPermutation i)) =
        embeddingRoot (p := 691) (1820 : ZMod 11057) j ^ (i.val + 2) ∨
      classRoot (coord (rowPermutation j) + coord (columnPermutation i)) =
        (embeddingRoot (p := 691) (1820 : ZMod 11057) j ^ (i.val + 2))⁻¹ := by
  let x := embeddingRoot (p := 691) (1820 : ZMod 11057) j ^ (i.val + 2)
  have hx : x ≠ 0 :=
    pow_ne_zero _ ((embeddingRoot_isPrimitive (p := 691) (q := 11057)
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
  · exact pow_ne_zero _ (classRoot_ne_zero r)

theorem weight_ratio_eq_phase_ratio (r s : Cyc) :
    weight (classRoot (r + s)) / weight (classRoot r) =
      phaseValue (r + s) / phaseValue r := by
  simp only [phaseValue]
  field_simp [weight_classRoot_ne_zero]

/-- Subtraction in `ZMod 691` is division of powers of the primitive root. -/
theorem root_pow_sub_val (a b : ZMod 691) :
    (1820 : ZMod 11057) ^ (a - b).val =
      (1820 : ZMod 11057) ^ a.val / (1820 : ZMod 11057) ^ b.val := by
  have hmod : (a - b).val + b.val ≡ a.val [MOD 691] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simp
  have hpow := pow_eq_pow_of_modEq hmod root_isPrimitive.pow_eq_one
  have hroot0 : (1820 : ZMod 11057) ≠ 0 :=
    root_isPrimitive.ne_zero (by norm_num)
  field_simp [hroot0]
  simpa [pow_add] using hpow

/-- Every compressed entry is the discrete logarithm of the corresponding
sixteenth-power residue symbol. -/
theorem matrix_entry_certificate (j i : Fin 344) :
    normalizedUnitValue (p := 691) (1820 : ZMod 11057) j i ^ 16 =
      (1820 : ZMod 11057) ^ (matrix j i).val := by
  let x : ZMod 11057 := embeddingRoot (p := 691) (1820 : ZMod 11057) j
  let a : Nat := i.val + 2
  let r : Cyc := coord (rowPermutation j)
  let s : Cyc := coord (columnPermutation i)
  have hx0 : x ≠ 0 := by
    exact (embeddingRoot_isPrimitive (p := 691) (q := 11057) (by norm_num)
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

end Fermat.SixHundredNinetyOne.CircularUnitEntryCertificate
