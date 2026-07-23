import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.Tactic

/-!
# The finite diagonal calculation in Vandiver's Lemma II at 587

Vandiver indexes his independent real units by
`1 ≤ i ≤ (p - 3) / 2`.  At `p = 587` there are 292 units and
293 terms in each character sum.

We use the small Teichmüller lift `r = 6529` of the primitive root `72`
modulo `587`.  It satisfies `r ^ 586 = 1 (mod 587 ^ 2)`.  At derivative
order `2 * 587 * k`, the character sum in Vandiver's formula (4) is

`sum_{j=0}^{292} r ^ (2 * j * (587 * k - n))`.

The proof below is algebraic rather than a `292 × 292` case split.  Off the
diagonal, the summand ratio has order dividing `586`, is not one modulo
`587`, and hence differs from one by a unit modulo `587²`; cancellation in
the geometric-sum identity gives zero.  On the diagonal every summand is
one.

The positive-exponent presentation has diagonal residue
`293 * 6529 = 1912997 = -154417 (mod 587²)`.  This replaces the accidental
exponent-37 simplification to `-1`.
-/

namespace Fermat.FiveHundredEightySeven.VandiverDiagonalArithmetic

open Finset

set_option maxHeartbeats 0
set_option maxRecDepth 100000

local instance : Fact (Nat.Prime 587) := ⟨by norm_num⟩

/-- Vandiver's source indices `1, ..., 292`, represented by `Fin 292`. -/
def sourceIndex (i : Fin 292) : ℕ := i.val + 1

/-- The positive Teichmüller lift whose reduction lies in the canonical
real half and therefore matches circular-unit column `a = 72`. -/
def teichmullerRoot587 : ℕ := 6529

/-- The exponent in the row-`k`, column-`n` character sum. -/
def characterExponent587 (k n : Fin 292) (j : ℕ) : ℕ :=
  2 * j * (587 * sourceIndex k - sourceIndex n)

/-- The 293-term character sum in Vandiver's formula (4). -/
def characterSum587 (k n : Fin 292) : ZMod (587 ^ 2) :=
  ∑ j ∈ range 293,
    (teichmullerRoot587 : ZMod (587 ^ 2)) ^
      characterExponent587 k n j

/-- `6529` is a Teichmüller lift modulo `587²`. -/
theorem teichmullerRoot587_pow_card_sub_one :
    (teichmullerRoot587 : ZMod (587 ^ 2)) ^ 586 = 1 := by
  decide

/-- Its reduction `72` is primitive modulo `587`. -/
theorem teichmullerRoot587_isPrimitive :
    IsPrimitiveRoot (teichmullerRoot587 : ZMod 587) 586 := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun n hnlt hnpos ↦ ?_⟩
  have hn : n ∈ Ioo 0 586 := by simp [hnpos, hnlt]
  fin_cases hn <;> decide

/-- The complete diagonal character-sum calculation. -/
theorem characterSum587_eq (k n : Fin 292) :
    characterSum587 k n = if k = n then 293 else 0 := by
  let d := 587 * sourceIndex k - sourceIndex n
  let w : ZMod (587 ^ 2) :=
    (teichmullerRoot587 : ZMod (587 ^ 2)) ^ (2 * d)
  have hsum :
      characterSum587 k n = ∑ j ∈ range 293, w ^ j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [← pow_mul]
    congr 1
    simp only [characterExponent587, d]
    ring
  by_cases hkn : k = n
  · subst n
    rw [if_pos rfl, hsum]
    have hw : w = 1 := by
      simp only [w, d]
      have heq :
          2 * (587 * sourceIndex k - sourceIndex k) =
            586 * (2 * sourceIndex k) := by
        have hk : 0 < sourceIndex k := by simp [sourceIndex]
        omega
      rw [heq, pow_mul, teichmullerRoot587_pow_card_sub_one, one_pow]
    rw [hw]
    simp
  · rw [if_neg hkn, hsum]
    have hw586 : w ^ 586 = 1 := by
      simp only [w]
      rw [← pow_mul]
      rw [show 2 * d * 586 = 586 * (2 * d) by ring]
      rw [pow_mul, teichmullerRoot587_pow_card_sub_one, one_pow]
    have hord : orderOf w ∣ 586 :=
      orderOf_dvd_iff_pow_eq_one.mpr hw586
    have hcop : (orderOf w).Coprime (587 ^ 2) :=
      Nat.Coprime.of_dvd_left hord (by norm_num)
    have hw_ne : w ≠ 1 := by
      intro hw
      have hmap := congrArg
        (ZMod.castHom (by norm_num : 587 ∣ 587 ^ 2) (ZMod 587)) hw
      simp only [w, map_pow, map_natCast, map_one] at hmap
      have hdvd : 586 ∣ 2 * d :=
        (teichmullerRoot587_isPrimitive.pow_eq_one_iff_dvd _).mp hmap
      have hdvd' : 293 ∣ d := by
        have : 2 * 293 ∣ 2 * d := by simpa using hdvd
        exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp this
      obtain ⟨q, hq⟩ := hdvd'
      have hkpos : 0 < sourceIndex k := by simp [sourceIndex]
      have hnpos : 0 < sourceIndex n := by simp [sourceIndex]
      have hkle : sourceIndex k ≤ 292 := by
        have hk := k.isLt
        simp [sourceIndex]
      have hnle : sourceIndex n ≤ 292 := by
        have hn := n.isLt
        simp [sourceIndex]
      have hd :
          d + sourceIndex n = 587 * sourceIndex k := by
        simp only [d]
        omega
      have hindex : sourceIndex k = sourceIndex n := by
        omega
      apply hkn
      apply Fin.ext
      simpa [sourceIndex] using hindex
    obtain hwone | hunit :=
      ZMod.eq_one_or_isUnit_sub_one
        (p := 587) (k := 2) rfl w hcop
    · exact (hw_ne hwone).elim
    · have hw293 : w ^ 293 = 1 := by
        simp only [w]
        rw [← pow_mul]
        rw [show 2 * d * 293 = 586 * d by ring]
        rw [pow_mul, teichmullerRoot587_pow_card_sub_one, one_pow]
      have hgeom := mul_geom_sum w 293
      rw [hw293, sub_self] at hgeom
      exact hunit.mul_left_cancel (by simpa using hgeom)

/-- Off-diagonal character sums vanish modulo `587²`. -/
theorem characterSum587_eq_zero {k n : Fin 292} (hkn : k ≠ n) :
    characterSum587 k n = 0 := by
  rw [characterSum587_eq, if_neg hkn]

/-- A diagonal character sum has the expected 293 terms. -/
theorem characterSum587_self (k : Fin 292) :
    characterSum587 k k = 293 := by
  rw [characterSum587_eq, if_pos rfl]

/-- Vandiver's positive exponent after multiplying the formal exponent by
`rho = r ^ (587²)`. -/
def positiveCharacterExponent587 (k n : Fin 292) (j : ℕ) : ℕ :=
  587 ^ 2 - 2 * sourceIndex n * j + 2 * 587 * sourceIndex k * j

/-- The same character sum in the positive-exponent presentation. -/
def positiveCharacterSum587 (k n : Fin 292) : ZMod (587 ^ 2) :=
  ∑ j ∈ range 293,
    (teichmullerRoot587 : ZMod (587 ^ 2)) ^
      positiveCharacterExponent587 k n j

/-- The positive-exponent sum is the original sum multiplied by
`rho = r^(587²)`. -/
theorem positiveCharacterSum587_eq_rho_mul (k n : Fin 292) :
    positiveCharacterSum587 k n =
      (teichmullerRoot587 : ZMod (587 ^ 2)) ^ (587 ^ 2) *
        characterSum587 k n := by
  rw [positiveCharacterSum587, characterSum587, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← pow_add]
  congr 1
  simp only [positiveCharacterExponent587, characterExponent587]
  have hjlt : j < 293 := Finset.mem_range.mp hj
  have hkpos : 0 < sourceIndex k := by simp [sourceIndex]
  have hnpos : 0 < sourceIndex n := by simp [sourceIndex]
  have hkle : sourceIndex k ≤ 292 := by
    have hk := k.isLt
    simp [sourceIndex]
  have hnle : sourceIndex n ≤ 292 := by
    have hn := n.isLt
    simp [sourceIndex]
  have hnPk : sourceIndex n ≤ 587 * sourceIndex k := by
    omega
  have hsmall :
      2 * sourceIndex n * j ≤ 587 ^ 2 := by
    calc
      2 * sourceIndex n * j ≤ 2 * 292 * 292 := by
        exact Nat.mul_le_mul
          (Nat.mul_le_mul_left 2 hnle)
          (Nat.le_of_lt_succ hjlt : j ≤ 292)
      _ ≤ 587 ^ 2 := by norm_num
  have hsmall' :
      2 * j * sourceIndex n ≤ 587 ^ 2 := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hsmall
  rw [show 2 * 587 * sourceIndex k * j =
      2 * j * (587 * sourceIndex k) by ring]
  rw [show 2 * sourceIndex n * j =
      2 * j * sourceIndex n by ring]
  rw [Nat.mul_sub_left_distrib]
  have hscaled :=
    Nat.mul_le_mul_left (2 * j) hnPk
  omega

/-- Positive-exponent form of the diagonal calculation. -/
theorem positiveCharacterSum587_eq (k n : Fin 292) :
    positiveCharacterSum587 k n =
      if k = n then
        293 * (teichmullerRoot587 : ZMod (587 ^ 2)) ^ (587 ^ 2)
      else 0 := by
  rw [positiveCharacterSum587_eq_rho_mul, characterSum587_eq]
  split_ifs <;> ring

/-- Since `587² ≡ 1 (mod 586)`, `rho` reduces to the Teichmüller root. -/
theorem rho587_eq_root :
    (teichmullerRoot587 : ZMod (587 ^ 2)) ^ (587 ^ 2) =
      teichmullerRoot587 := by
  rw [show 587 ^ 2 = 586 * 588 + 1 by norm_num, pow_add, pow_mul,
    teichmullerRoot587_pow_card_sub_one, one_pow, pow_one, one_mul]

/-- The exact diagonal residue is `1912997`, equivalently `-154417`, modulo
`587²`; all off-diagonal residues vanish. -/
theorem positiveCharacterSum587_eq_neg154417_or_zero (k n : Fin 292) :
    positiveCharacterSum587 k n = if k = n then -154417 else 0 := by
  rw [positiveCharacterSum587_eq, rho587_eq_root]
  split_ifs <;> decide

/-- Multiplication by Vandiver's outer factor `p - 1 = 586` leaves the
exact coefficient `-90488362 = 586 * (-154417)` on the diagonal and zero
elsewhere.  Its canonical residue modulo `587²` is `133285`, hence it is
a `587`-adic unit. -/
theorem relationCharacterFactor587_eq (k n : Fin 292) :
    (586 : ZMod (587 ^ 2)) * positiveCharacterSum587 k n =
      if k = n then -90488362 else 0 := by
  rw [positiveCharacterSum587_eq_neg154417_or_zero]
  split_ifs <;> ring

end Fermat.FiveHundredEightySeven.VandiverDiagonalArithmetic
