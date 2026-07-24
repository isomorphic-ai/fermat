import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.Tactic

/-!
# The finite diagonal calculation in Vandiver's Lemma 2 at `67`

Vandiver indexes his independent real units by
`1 ≤ i ≤ (p - 3) / 2`.  At `p = 67` there are thirty-two units and
thirty-three terms in each character sum.

We use the Teichmüller lift `r = 1342` of the primitive root `2` modulo
`67`.  It satisfies `r ^ 66 = 1 (mod 67 ^ 2)`.  At derivative order
`2 * 67 * k`, the character sum occurring in Vandiver's formula (4) is

`sum_{j=0}^{32} r ^ (2 * j * (67 * k - n))`.

The finite theorems below certify that this sum vanishes modulo `67 ^ 2`
off the diagonal and equals `33` on the diagonal.  They also record the
positive-exponent form produced by Vandiver's integral diagonal units.

Unlike the numerical coincidence `18 * 76 = -1 (mod 37 ^ 2)` at exponent
`37`, the diagonal coefficient here is

`33 * 1342 = 3885 = -604 (mod 67 ^ 2)`.

Keeping that coefficient explicit is important: the exponent-`67`
formalization is an actual specialization of the historical calculation,
not a blind replacement of the numerals in the exponent-`37` proof.
-/

namespace Fermat.SixtySeven.VandiverDiagonalArithmetic

open Finset

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Vandiver's unit indices `1, ..., 32`, represented by `Fin 32`. -/
def sourceIndex (i : Fin 32) : ℕ := i.val + 1

/-- The Teichmüller lift of the primitive root `2` used at exponent `67`. -/
def teichmullerRoot67 : ℕ := 1342

/-- The common ratio exponent in a row-`k`, column-`n` character sum. -/
def characterRatioExponent67 (k n : Fin 32) : ℕ :=
  2 * (67 * sourceIndex k - sourceIndex n)

/-- The exponent in the row-`k`, column-`n` character sum. -/
def characterExponent67 (k n : Fin 32) (j : ℕ) : ℕ :=
  characterRatioExponent67 k n * j

/-- The common ratio of the geometric character sum. -/
def characterRatio67 (k n : Fin 32) : ZMod (67 ^ 2) :=
  (teichmullerRoot67 : ZMod (67 ^ 2)) ^
    characterRatioExponent67 k n

/-- The thirty-three-term character sum in Vandiver's formula (4). -/
def characterSum67 (k n : Fin 32) : ZMod (67 ^ 2) :=
  ∑ j ∈ range 33,
    characterRatio67 k n ^ j

/-- `1342` is a Teichmüller lift modulo `67²`. -/
theorem teichmullerRoot67_pow_card_sub_one :
    (teichmullerRoot67 : ZMod (67 ^ 2)) ^ 66 = 1 := by
  decide

/-- The chosen root remains primitive modulo `67`. -/
theorem teichmullerRoot67_isPrimitive :
    IsPrimitiveRoot (teichmullerRoot67 : ZMod 67) 66 := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun n hnlt hnpos ↦ ?_⟩
  have hn : n ∈ Ioo 0 66 := by simp [hnpos, hnlt]
  fin_cases hn <;> decide

/-- Every character-sum ratio has thirty-third power one. -/
theorem characterRatio67_pow_thirtyThree (k n : Fin 32) :
    characterRatio67 k n ^ 33 = 1 := by
  rw [characterRatio67, ← pow_mul]
  have hmultiple :
      characterRatioExponent67 k n * 33 =
        66 * (67 * sourceIndex k - sourceIndex n) := by
    simp only [characterRatioExponent67]
    omega
  rw [hmultiple, pow_mul, teichmullerRoot67_pow_card_sub_one, one_pow]

/-- Reduction of the character ratio from `ZMod (67²)` to `ZMod 67`. -/
theorem cast_characterRatio67 (k n : Fin 32) :
    ZMod.castHom (show 67 ∣ 67 ^ 2 by norm_num) (ZMod 67)
        (characterRatio67 k n) =
      (teichmullerRoot67 : ZMod 67) ^
        characterRatioExponent67 k n := by
  simp [characterRatio67]

/-- An off-diagonal character ratio is not one.  The proof is algebraic:
after reduction modulo `67`, primitivity of `2` turns equality to one into
the divisibility `66 ∣ 2(67k-n)`, and the source-index bounds force
`k = n`. -/
theorem characterRatio67_ne_one (k n : Fin 32) (hkn : k ≠ n) :
    characterRatio67 k n ≠ 1 := by
  intro h
  have hmap := congrArg
    (ZMod.castHom (show 67 ∣ 67 ^ 2 by norm_num) (ZMod 67)) h
  rw [cast_characterRatio67] at hmap
  simp only [map_one] at hmap
  have hdvd : 66 ∣ characterRatioExponent67 k n :=
    (teichmullerRoot67_isPrimitive.pow_eq_one_iff_dvd _).mp
      (by simpa [teichmullerRoot67] using hmap)
  obtain ⟨c, hc⟩ := hdvd
  apply hkn
  apply Fin.ext
  simp only [characterRatioExponent67, sourceIndex] at hc
  omega

/-- Off the diagonal, `ratio - 1` is a unit modulo `67²`.  It is nonzero
modulo `67`, hence coprime to the square modulus. -/
theorem characterRatio67_sub_one_isUnit
    (k n : Fin 32) (hkn : k ≠ n) :
    IsUnit (characterRatio67 k n - 1) := by
  have hunit :
      IsUnit (((characterRatio67 k n - 1).val : ℕ) :
        ZMod (67 ^ 2)) := by
    apply (ZMod.isUnit_iff_coprime
      (characterRatio67 k n - 1).val (67 ^ 2)).2
    apply Nat.Coprime.pow_right 2
    apply Nat.Coprime.symm
    apply ((by norm_num : Nat.Prime 67).coprime_iff_not_dvd).2
    intro hdvd
    have hzero :
        ((characterRatio67 k n - 1).val : ZMod 67) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 hdvd
    have hcast :
        ZMod.castHom (show 67 ∣ 67 ^ 2 by norm_num) (ZMod 67)
            (characterRatio67 k n - 1) =
          ((characterRatio67 k n - 1).val : ZMod 67) := by
      rw [ZMod.castHom_apply, ZMod.cast_eq_val]
    rw [← hcast, map_sub, cast_characterRatio67] at hzero
    simp only [map_one, sub_eq_zero] at hzero
    have hdvd' : 66 ∣ characterRatioExponent67 k n :=
      (teichmullerRoot67_isPrimitive.pow_eq_one_iff_dvd _).mp
        (by simpa [teichmullerRoot67] using hzero)
    obtain ⟨c, hc⟩ := hdvd'
    apply hkn
    apply Fin.ext
    simp only [characterRatioExponent67, sourceIndex] at hc
    omega
  simpa only [ZMod.natCast_zmod_val] using hunit

/-- Off-diagonal geometric character sums vanish. -/
theorem characterSum67_eq_zero_of_ne
    (k n : Fin 32) (hkn : k ≠ n) :
    characterSum67 k n = 0 := by
  apply (characterRatio67_sub_one_isUnit k n hkn).mul_right_cancel
  rw [zero_mul]
  change
    (∑ j ∈ range 33, characterRatio67 k n ^ j) *
      (characterRatio67 k n - 1) = 0
  rw [geom_sum_mul, characterRatio67_pow_thirtyThree]
  simp

/-- The complete finite diagonal character-sum calculation. -/
theorem characterSum67_eq (k n : Fin 32) :
    characterSum67 k n = if k = n then 33 else 0 := by
  by_cases h : k = n
  · subst n
    have hratio : characterRatio67 k k = 1 := by
      rw [characterRatio67]
      have hmultiple :
          characterRatioExponent67 k k =
            66 * (2 * sourceIndex k) := by
        simp only [characterRatioExponent67]
        have hk : sourceIndex k ≤ 67 * sourceIndex k := by
          simp [sourceIndex]
        omega
      rw [hmultiple, pow_mul, teichmullerRoot67_pow_card_sub_one, one_pow]
    simp [characterSum67, hratio]
  · rw [if_neg h]
    exact characterSum67_eq_zero_of_ne k n h

/-- Off-diagonal character sums vanish modulo `67²`. -/
theorem characterSum67_eq_zero {k n : Fin 32} (hkn : k ≠ n) :
    characterSum67 k n = 0 := by
  rw [characterSum67_eq, if_neg hkn]

/-- A diagonal character sum has the expected thirty-three terms. -/
theorem characterSum67_self (k : Fin 32) : characterSum67 k k = 33 := by
  rw [characterSum67_eq, if_pos rfl]

/-- Vandiver's positive exponent after multiplying the formal exponent
`r ^ (-2*n*j)` by `rho = r ^ (67²)`. -/
def positiveCharacterExponent67 (k n : Fin 32) (j : ℕ) : ℕ :=
  67 ^ 2 - 2 * sourceIndex n * j + 2 * 67 * sourceIndex k * j

/-- The same character sum in the positive-exponent presentation. -/
def positiveCharacterSum67 (k n : Fin 32) : ZMod (67 ^ 2) :=
  ∑ j ∈ range 33,
    (teichmullerRoot67 : ZMod (67 ^ 2)) ^
      positiveCharacterExponent67 k n j

/-- The positive-exponent sum is the original sum multiplied by
`rho = r^(67²)`. -/
theorem positiveCharacterSum67_eq_rho_mul (k n : Fin 32) :
    positiveCharacterSum67 k n =
      (teichmullerRoot67 : ZMod (67 ^ 2)) ^ (67 ^ 2) *
        characterSum67 k n := by
  rw [positiveCharacterSum67, characterSum67, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [characterRatio67, ← pow_mul, ← pow_add]
  congr 1
  have hj32 : j ≤ 32 := by
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hn32 : sourceIndex n ≤ 32 := by
    simp only [sourceIndex]
    omega
  have hnk : sourceIndex n ≤ 67 * sourceIndex k := by
    simp only [sourceIndex]
    omega
  have hsmall :
      2 * sourceIndex n * j ≤ 67 ^ 2 := by
    calc
      2 * sourceIndex n * j ≤ 2 * 32 * 32 := by gcongr
      _ ≤ 67 ^ 2 := by norm_num
  have hlarge :
      2 * sourceIndex n * j ≤
        2 * 67 * sourceIndex k * j := by
    have h := Nat.mul_le_mul_left 2 hnk
    have hjmul := Nat.mul_le_mul_right j h
    simpa only [mul_assoc] using hjmul
  have hchar :
      characterRatioExponent67 k n * j =
        2 * 67 * sourceIndex k * j - 2 * sourceIndex n * j := by
    rw [characterRatioExponent67, Nat.mul_sub_left_distrib, Nat.sub_mul]
    ring_nf
  rw [hchar]
  simp only [positiveCharacterExponent67]
  calc
    67 ^ 2 - 2 * sourceIndex n * j +
          2 * 67 * sourceIndex k * j =
        67 ^ 2 + (2 * 67 * sourceIndex k * j) -
          2 * sourceIndex n * j :=
      (Nat.sub_add_comm hsmall).symm
    _ = 67 ^ 2 +
        (2 * 67 * sourceIndex k * j - 2 * sourceIndex n * j) :=
      Nat.add_sub_assoc hlarge (67 ^ 2)

/-- Positive-exponent form of the diagonal calculation. -/
theorem positiveCharacterSum67_eq (k n : Fin 32) :
    positiveCharacterSum67 k n =
      if k = n then
        33 * (teichmullerRoot67 : ZMod (67 ^ 2)) ^ (67 ^ 2)
      else 0 := by
  rw [positiveCharacterSum67_eq_rho_mul, characterSum67_eq]
  split_ifs <;> ring

/-- Since `67² = 68 * 66 + 1`, `rho` reduces to the Teichmüller root. -/
theorem rho67_eq_root :
    (teichmullerRoot67 : ZMod (67 ^ 2)) ^ (67 ^ 2) =
      teichmullerRoot67 := by
  decide

/-- The exact diagonal residue is `3885`, equivalently `-604`, modulo
`67²`; all off-diagonal residues vanish. -/
theorem positiveCharacterSum67_eq_neg604_or_zero (k n : Fin 32) :
    positiveCharacterSum67 k n = if k = n then -604 else 0 := by
  rw [positiveCharacterSum67_eq, rho67_eq_root]
  split_ifs <;> decide

/-- Multiplication by Vandiver's outer factor `p - 1 = 66` leaves the
`67`-adic unit `-39864` on the diagonal and zero off it. -/
theorem relationCharacterFactor67_eq (k n : Fin 32) :
    (66 : ZMod (67 ^ 2)) * positiveCharacterSum67 k n =
      if k = n then -39864 else 0 := by
  rw [positiveCharacterSum67_eq_neg604_or_zero]
  split_ifs <;> ring

end Fermat.SixtySeven.VandiverDiagonalArithmetic
