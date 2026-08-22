import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.Tactic

/-!
# The finite diagonal calculation in Vandiver's Lemma II at 157

Vandiver indexes his independent real units by
`1 ≤ i ≤ (p - 3) / 2`.  At `p = 157` there are seventy-seven units and
seventy-eight terms in each character sum.

We use the small Teichmüller lift `r = 226` of the primitive root `69`
modulo `157`.  It satisfies `r ^ 156 = 1 (mod 157 ^ 2)`.  At derivative
order `2 * 157 * k`, the character sum in Vandiver's formula (4) is

`sum_{j=0}^{77} r ^ (2 * j * (157 * k - n))`.

The proof below is algebraic rather than a `77 × 77` case split.  Off the
diagonal, the summand ratio has order dividing `156`, is not one modulo
`157`, and hence differs from one by a unit modulo `157²`; cancellation in
the geometric-sum identity gives zero.  On the diagonal every summand is
one.

The positive-exponent presentation has diagonal residue
`78 * 226 = 17628 = -7021 (mod 157²)`.  This replaces the accidental
exponent-37 simplification to `-1`.
-/

namespace Fermat.OneHundredFiftySeven.VandiverDiagonalArithmetic

open Finset

set_option maxHeartbeats 0
set_option maxRecDepth 100000

local instance : Fact (Nat.Prime 157) := ⟨by norm_num⟩

/-- Vandiver's source indices `1, ..., 77`, represented by `Fin 77`. -/
def sourceIndex (i : Fin 77) : ℕ := i.val + 1

/-- The least positive Teichmüller lift used in this specialization. -/
def teichmullerRoot157 : ℕ := 226

/-- The exponent in the row-`k`, column-`n` character sum. -/
def characterExponent157 (k n : Fin 77) (j : ℕ) : ℕ :=
  2 * j * (157 * sourceIndex k - sourceIndex n)

/-- The seventy-eight-term character sum in Vandiver's formula (4). -/
def characterSum157 (k n : Fin 77) : ZMod (157 ^ 2) :=
  ∑ j ∈ range 78,
    (teichmullerRoot157 : ZMod (157 ^ 2)) ^
      characterExponent157 k n j

/-- `226` is a Teichmüller lift modulo `157²`. -/
theorem teichmullerRoot157_pow_card_sub_one :
    (teichmullerRoot157 : ZMod (157 ^ 2)) ^ 156 = 1 := by
  decide

/-- Its reduction `69` is primitive modulo `157`. -/
theorem teichmullerRoot157_isPrimitive :
    IsPrimitiveRoot (teichmullerRoot157 : ZMod 157) 156 := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun n hnlt hnpos ↦ ?_⟩
  have hn : n ∈ Ioo 0 156 := by simp [hnpos, hnlt]
  fin_cases hn <;> decide

/-- The complete diagonal character-sum calculation. -/
theorem characterSum157_eq (k n : Fin 77) :
    characterSum157 k n = if k = n then 78 else 0 := by
  let d := 157 * sourceIndex k - sourceIndex n
  let w : ZMod (157 ^ 2) :=
    (teichmullerRoot157 : ZMod (157 ^ 2)) ^ (2 * d)
  have hsum :
      characterSum157 k n = ∑ j ∈ range 78, w ^ j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [← pow_mul]
    congr 1
    simp only [characterExponent157, d]
    ring
  by_cases hkn : k = n
  · subst n
    rw [if_pos rfl, hsum]
    have hw : w = 1 := by
      simp only [w, d]
      have heq :
          2 * (157 * sourceIndex k - sourceIndex k) =
            156 * (2 * sourceIndex k) := by
        have hk : 0 < sourceIndex k := by simp [sourceIndex]
        omega
      rw [heq, pow_mul, teichmullerRoot157_pow_card_sub_one, one_pow]
    rw [hw]
    simp
  · rw [if_neg hkn, hsum]
    have hw156 : w ^ 156 = 1 := by
      simp only [w]
      rw [← pow_mul]
      rw [show 2 * d * 156 = 156 * (2 * d) by ring]
      rw [pow_mul, teichmullerRoot157_pow_card_sub_one, one_pow]
    have hord : orderOf w ∣ 156 :=
      orderOf_dvd_iff_pow_eq_one.mpr hw156
    have hcop : (orderOf w).Coprime (157 ^ 2) :=
      Nat.Coprime.of_dvd_left hord (by norm_num)
    have hw_ne : w ≠ 1 := by
      intro hw
      have hmap := congrArg
        (ZMod.castHom (by norm_num : 157 ∣ 157 ^ 2) (ZMod 157)) hw
      simp only [w, map_pow, map_natCast, map_one] at hmap
      have hdvd : 156 ∣ 2 * d :=
        (teichmullerRoot157_isPrimitive.pow_eq_one_iff_dvd _).mp hmap
      have hdvd' : 78 ∣ d := by
        have : 2 * 78 ∣ 2 * d := by simpa using hdvd
        exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp this
      obtain ⟨q, hq⟩ := hdvd'
      have hkpos : 0 < sourceIndex k := by simp [sourceIndex]
      have hnpos : 0 < sourceIndex n := by simp [sourceIndex]
      have hkle : sourceIndex k ≤ 77 := by
        have hk := k.isLt
        simp [sourceIndex]
      have hnle : sourceIndex n ≤ 77 := by
        have hn := n.isLt
        simp [sourceIndex]
      have hd :
          d + sourceIndex n = 157 * sourceIndex k := by
        simp only [d]
        omega
      have hindex : sourceIndex k = sourceIndex n := by
        omega
      apply hkn
      apply Fin.ext
      simpa [sourceIndex] using hindex
    obtain hwone | hunit :=
      ZMod.eq_one_or_isUnit_sub_one
        (p := 157) (k := 2) rfl w hcop
    · exact (hw_ne hwone).elim
    · have hw78 : w ^ 78 = 1 := by
        simp only [w]
        rw [← pow_mul]
        rw [show 2 * d * 78 = 156 * d by ring]
        rw [pow_mul, teichmullerRoot157_pow_card_sub_one, one_pow]
      have hgeom := mul_geom_sum w 78
      rw [hw78, sub_self] at hgeom
      exact hunit.mul_left_cancel (by simpa using hgeom)

/-- Off-diagonal character sums vanish modulo `157²`. -/
theorem characterSum157_eq_zero {k n : Fin 77} (hkn : k ≠ n) :
    characterSum157 k n = 0 := by
  rw [characterSum157_eq, if_neg hkn]

/-- A diagonal character sum has the expected seventy-eight terms. -/
theorem characterSum157_self (k : Fin 77) :
    characterSum157 k k = 78 := by
  rw [characterSum157_eq, if_pos rfl]

/-- Vandiver's positive exponent after multiplying the formal exponent by
`rho = r ^ (157²)`. -/
def positiveCharacterExponent157 (k n : Fin 77) (j : ℕ) : ℕ :=
  157 ^ 2 - 2 * sourceIndex n * j + 2 * 157 * sourceIndex k * j

/-- The same character sum in the positive-exponent presentation. -/
def positiveCharacterSum157 (k n : Fin 77) : ZMod (157 ^ 2) :=
  ∑ j ∈ range 78,
    (teichmullerRoot157 : ZMod (157 ^ 2)) ^
      positiveCharacterExponent157 k n j

/-- The positive-exponent sum is the original sum multiplied by
`rho = r^(157²)`. -/
theorem positiveCharacterSum157_eq_rho_mul (k n : Fin 77) :
    positiveCharacterSum157 k n =
      (teichmullerRoot157 : ZMod (157 ^ 2)) ^ (157 ^ 2) *
        characterSum157 k n := by
  rw [positiveCharacterSum157, characterSum157, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← pow_add]
  congr 1
  simp only [positiveCharacterExponent157, characterExponent157]
  have hjlt : j < 78 := Finset.mem_range.mp hj
  have hkpos : 0 < sourceIndex k := by simp [sourceIndex]
  have hnpos : 0 < sourceIndex n := by simp [sourceIndex]
  have hkle : sourceIndex k ≤ 77 := by
    have hk := k.isLt
    simp [sourceIndex]
  have hnle : sourceIndex n ≤ 77 := by
    have hn := n.isLt
    simp [sourceIndex]
  have hnPk : sourceIndex n ≤ 157 * sourceIndex k := by
    omega
  have hsmall :
      2 * sourceIndex n * j ≤ 157 ^ 2 := by
    calc
      2 * sourceIndex n * j ≤ 2 * 77 * 77 := by
        exact Nat.mul_le_mul
          (Nat.mul_le_mul_left 2 hnle)
          (Nat.le_of_lt_succ hjlt : j ≤ 77)
      _ ≤ 157 ^ 2 := by norm_num
  have hsmall' :
      2 * j * sourceIndex n ≤ 157 ^ 2 := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hsmall
  rw [show 2 * 157 * sourceIndex k * j =
      2 * j * (157 * sourceIndex k) by ring]
  rw [show 2 * sourceIndex n * j =
      2 * j * sourceIndex n by ring]
  rw [Nat.mul_sub_left_distrib]
  have hscaled :=
    Nat.mul_le_mul_left (2 * j) hnPk
  omega

/-- Positive-exponent form of the diagonal calculation. -/
theorem positiveCharacterSum157_eq (k n : Fin 77) :
    positiveCharacterSum157 k n =
      if k = n then
        78 * (teichmullerRoot157 : ZMod (157 ^ 2)) ^ (157 ^ 2)
      else 0 := by
  rw [positiveCharacterSum157_eq_rho_mul, characterSum157_eq]
  split_ifs <;> ring

/-- Since `157² ≡ 1 (mod 156)`, `rho` reduces to the Teichmüller root. -/
theorem rho157_eq_root :
    (teichmullerRoot157 : ZMod (157 ^ 2)) ^ (157 ^ 2) =
      teichmullerRoot157 := by
  rw [show 157 ^ 2 = 156 * 158 + 1 by norm_num, pow_add, pow_mul,
    teichmullerRoot157_pow_card_sub_one, one_pow, pow_one, one_mul]

/-- The exact diagonal residue is `17628`, equivalently `-7021`, modulo
`157²`; all off-diagonal residues vanish. -/
theorem positiveCharacterSum157_eq_neg7021_or_zero (k n : Fin 77) :
    positiveCharacterSum157 k n = if k = n then -7021 else 0 := by
  rw [positiveCharacterSum157_eq, rho157_eq_root]
  split_ifs <;> decide

/-- Multiplication by Vandiver's outer factor `p - 1 = 156` leaves the
`157`-adic unit `-1095276` on the diagonal and zero elsewhere. -/
theorem relationCharacterFactor157_eq (k n : Fin 77) :
    (156 : ZMod (157 ^ 2)) * positiveCharacterSum157 k n =
      if k = n then -1095276 else 0 := by
  rw [positiveCharacterSum157_eq_neg7021_or_zero]
  split_ifs <;> ring

end Fermat.OneHundredFiftySeven.VandiverDiagonalArithmetic
