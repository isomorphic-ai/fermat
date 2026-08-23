import Fermat.Certificates.CaseII_1.CircularUnitIrregularChannel1831AtQ18311
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitEntryCoordinates

/-!
# Circular-unit residue certificate for p = 1831 at q = 18311

The 915 checked phase values at the second split prime reconstruct every
source-order circular-unit residue entry. This supplies the genuine
`CircularUnitResidues.Certificate 1831 18311` consumed by the selective
saturation route; no nonsingularity claim is made.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitResidueCertificate1831AtQ18311

noncomputable section

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitResidues
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitCyclic
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitMatrix

namespace SharedCoordinates
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitEntryCertificate
abbrev classExponent :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitEntryCertificate.classExponent
abbrev classExponent_add_sq :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitEntryCertificate.classExponent_add_sq
abbrev row_exponent_square_certificate :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitEntryCertificate.row_exponent_square_certificate
abbrev column_exponent_square_certificate :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitEntryCertificate.column_exponent_square_certificate
end SharedCoordinates

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 1831) := ⟨by decide⟩
local instance : Fact (Nat.Prime 18311) :=
  ⟨by norm_num [Nat.prime_def]⟩

theorem prime_18311 : Nat.Prime 18311 := Fact.out

theorem root_order : orderOf (1024 : ZMod 18311) = 1831 := by
  apply orderOf_eq_prime
  · change (1024 : ZMod 18311) ^ 1831 = 1
    calc
      (1024 : ZMod 18311) ^ 1831 = ((2 : ZMod 18311) ^ 10) ^ 1831 := by
        norm_num
      _ = (2 : ZMod 18311) ^ (10 * 1831) := by rw [pow_mul]
      _ = (2 : ZMod 18311) ^ (18311 - 1) := by norm_num
      _ = 1 := ZMod.pow_card_sub_one_eq_one (by decide)
  · change (1024 : ZMod 18311) ≠ 1
    decide

theorem root_isPrimitive : IsPrimitiveRoot (1024 : ZMod 18311) 1831 :=
  IsPrimitiveRoot.iff_orderOf.mpr root_order

def weight (x : ZMod 18311) : ZMod 18311 :=
  (1 - x) ^ 10 / x ^ 5

theorem normalized_pow_eq_weight_ratio (j i : Fin 914) :
    normalizedUnitValue (p := 1831) (1024 : ZMod 18311) j i ^ 10 =
      weight
          (embeddingRoot (p := 1831) (1024 : ZMod 18311) j ^ (i.val + 2)) /
        weight (embeddingRoot (p := 1831) (1024 : ZMod 18311) j) := by
  let x : ZMod 18311 :=
    embeddingRoot (p := 1831) (1024 : ZMod 18311) j
  let a : Nat := i.val + 2
  let e : Nat := canonicalNormalizationExponent (p := 1831) a
  have hxprim : IsPrimitiveRoot x 1831 := by
    exact embeddingRoot_isPrimitive (p := 1831) (q := 18311) (by norm_num)
      root_isPrimitive j
  have hx0 : x ≠ 0 := hxprim.ne_zero (by norm_num)
  have hx1 : 1 - x ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (hxprim.ne_one (by norm_num)))
  have hnorm : 2 * e + a ≡ 1 [MOD 1831] :=
    canonicalNormalizationExponent_modEq (p := 1831) (by norm_num) a
  have hnorm5 : 5 * (2 * e + a) ≡ 5 * 1 [MOD 1831] :=
    hnorm.mul_left 5
  have hexp : 10 * e + 5 * a ≡ 5 [MOD 1831] := by
    convert hnorm5 using 1
    all_goals omega
  have hpow : x ^ (10 * e + 5 * a) = x ^ 5 :=
    pow_eq_pow_of_modEq hexp hxprim.pow_eq_one
  change (x ^ e * (1 - x ^ a) / (1 - x)) ^ 10 =
    weight (x ^ a) / weight x
  simp only [weight, mul_pow, div_pow]
  field_simp [hx0, hx1]
  have hpow' : x ^ (e * 10) * x ^ (a * 5) = x ^ 5 := by
    rw [← pow_add]
    simpa [Nat.mul_comm] using hpow
  calc
    _ = (x ^ (e * 10) * x ^ (a * 5)) * (1 - x ^ a) ^ 10 := by ring
    _ = x ^ 5 * (1 - x ^ a) ^ 10 := by rw [hpow']
    _ = _ := by ring

def classRoot (r : Cyc) : ZMod 18311 :=
  (1024 : ZMod 18311) ^ SharedCoordinates.classExponent r

theorem classRoot_ne_one (r : Cyc) : classRoot r ≠ 1 := by
  intro hone
  have hdvd : 1831 ∣ SharedCoordinates.classExponent r :=
    (root_isPrimitive.pow_eq_one_iff_dvd _).mp hone
  have heq : SharedCoordinates.classExponent r = 0 :=
    Nat.eq_zero_of_dvd_of_lt hdvd
      (Fermat.OneThousandEightHundredThirtyOne.CircularUnitEntryCertificate.classExponent_lt r)
  exact
    (Fermat.OneThousandEightHundredThirtyOne.CircularUnitEntryCertificate.classExponent_ne_zero r)
      heq

theorem classRoot_ne_zero (r : Cyc) : classRoot r ≠ 0 := by
  exact pow_ne_zero _ (root_isPrimitive.ne_zero (by norm_num))

theorem classRoot_eq_pow_or_inv_of_sq
    (r : Cyc) (target : ℕ)
    (hsquare :
      ((SharedCoordinates.classExponent r : ZMod 1831) ^ 2) =
        ((target : ℕ) : ZMod 1831) ^ 2) :
    classRoot r = (1024 : ZMod 18311) ^ target ∨
      classRoot r = ((1024 : ZMod 18311) ^ target)⁻¹ := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with hsame | hneg
  · have hmod : SharedCoordinates.classExponent r ≡ target [MOD 1831] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      exact hsame
    have hp :
        (1024 : ZMod 18311) ^ SharedCoordinates.classExponent r =
          (1024 : ZMod 18311) ^ target :=
      pow_eq_pow_of_modEq hmod root_isPrimitive.pow_eq_one
    exact Or.inl (by simpa only [classRoot] using hp)
  · have hcast :
        ((SharedCoordinates.classExponent r + target : ℕ) : ZMod 1831) = 0 := by
      push_cast
      rw [hneg]
      simp
    have hmod : SharedCoordinates.classExponent r + target ≡ 0 [MOD 1831] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      exact hcast
    have hp :
        (1024 : ZMod 18311) ^ SharedCoordinates.classExponent r *
            (1024 : ZMod 18311) ^ target = 1 := by
      rw [← pow_add]
      simpa using pow_eq_pow_of_modEq hmod root_isPrimitive.pow_eq_one
    have htarget0 : (1024 : ZMod 18311) ^ target ≠ 0 :=
      pow_ne_zero _ (root_isPrimitive.ne_zero (by norm_num))
    exact Or.inr (by
      simpa only [classRoot] using
        (mul_eq_one_iff_eq_inv₀ htarget0).mp hp)

theorem weight_inv (x : ZMod 18311) (hx : x ≠ 0) :
    weight x⁻¹ = weight x := by
  simp only [weight, inv_pow]
  field_simp [hx]
  ring

def phaseValue (r : Cyc) : ZMod 18311 :=
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

theorem root_pow_sub_val (a b : ZMod 1831) :
    (1024 : ZMod 18311) ^ (a - b).val =
      (1024 : ZMod 18311) ^ a.val /
        (1024 : ZMod 18311) ^ b.val := by
  have hmod : (a - b).val + b.val ≡ a.val [MOD 1831] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simp
  have hpow := pow_eq_pow_of_modEq hmod root_isPrimitive.pow_eq_one
  have hroot0 : (1024 : ZMod 18311) ≠ 0 :=
    root_isPrimitive.ne_zero (by norm_num)
  field_simp [hroot0]
  simpa [pow_add] using hpow

abbrev symbolPhase :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitIrregularChannel1831AtQ18311.symbolPhase

def matrix : Matrix (Fin 914) (Fin 914) (ZMod 1831) :=
  Matrix.reindex rowPermutation.symm columnPermutation.symm
    (differenceMatrix symbolPhase)

theorem row_root_relation (j : Fin 914) :
    classRoot (coord (rowPermutation j)) =
        embeddingRoot (p := 1831) (1024 : ZMod 18311) j ∨
      classRoot (coord (rowPermutation j)) =
        (embeddingRoot (p := 1831) (1024 : ZMod 18311) j)⁻¹ := by
  simpa only [embeddingRoot] using
    classRoot_eq_pow_or_inv_of_sq
      (coord (rowPermutation j)) (j.val + 1)
      (SharedCoordinates.row_exponent_square_certificate j)

theorem product_root_relation (j i : Fin 914) :
    classRoot (coord (rowPermutation j) + coord (columnPermutation i)) =
        embeddingRoot (p := 1831) (1024 : ZMod 18311) j ^ (i.val + 2) ∨
      classRoot (coord (rowPermutation j) + coord (columnPermutation i)) =
        (embeddingRoot (p := 1831) (1024 : ZMod 18311) j ^
          (i.val + 2))⁻¹ := by
  let r : Cyc := coord (rowPermutation j)
  let s : Cyc := coord (columnPermutation i)
  let target : ℕ := (j.val + 1) * (i.val + 2)
  have hsquare :
      ((SharedCoordinates.classExponent (r + s) : ZMod 1831) ^ 2) =
        ((target : ℕ) : ZMod 1831) ^ 2 := by
    dsimp only [target]
    rw [SharedCoordinates.classExponent_add_sq,
      SharedCoordinates.row_exponent_square_certificate,
      SharedCoordinates.column_exponent_square_certificate]
    push_cast
    ring
  simpa only [r, s, target, embeddingRoot, pow_mul] using
    classRoot_eq_pow_or_inv_of_sq (r + s) target hsquare

theorem phase_value_certificate (r : Cyc) :
    phaseValue r = (1024 : ZMod 18311) ^ (symbolPhase r).val := by
  have hr : classRoot r ≠ 0 := classRoot_ne_zero r
  have hzero : classRoot 0 ≠ 0 := classRoot_ne_zero 0
  have hzero1 : 1 - classRoot 0 ≠ 0 := by
    decide +kernel
  unfold phaseValue weight
  field_simp [hr, hzero, hzero1]
  decide +revert

theorem matrix_entry_certificate (j i : Fin 914) :
    normalizedUnitValue (p := 1831) (1024 : ZMod 18311) j i ^ 10 =
      (1024 : ZMod 18311) ^ (matrix j i).val := by
  let x : ZMod 18311 :=
    embeddingRoot (p := 1831) (1024 : ZMod 18311) j
  let a : Nat := i.val + 2
  let r : Cyc := coord (rowPermutation j)
  let s : Cyc := coord (columnPermutation i)
  have hx0 : x ≠ 0 := by
    exact (embeddingRoot_isPrimitive (p := 1831) (q := 18311)
      (by norm_num) root_isPrimitive j).ne_zero (by norm_num)
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

/-- Complete compressed q=18311 residue certificate. -/
def certificate :
    Fermat.Irregular.CircularUnitResidues.Certificate 1831 18311 where
  hp2 := by norm_num
  symbolExponent := 10
  q_sub_one := by norm_num
  root := 1024
  root_isPrimitive := root_isPrimitive
  matrix := matrix
  entry_certificate := matrix_entry_certificate

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitResidueCertificate1831AtQ18311
