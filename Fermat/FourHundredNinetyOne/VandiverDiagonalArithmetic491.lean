import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.Tactic

/-!
# The finite diagonal calculation in Vandiver's Lemma II at 491

Vandiver indexes his independent real units by
`1 ≤ i ≤ (p - 3) / 2`.  At `p = 491` there are 244 units and
245 terms in each character sum.

We use the small Teichmüller lift `r = 2512` of the primitive root `57`
modulo `491`.  It satisfies `r ^ 490 = 1 (mod 491 ^ 2)`.  At derivative
order `2 * 491 * k`, the character sum in Vandiver's formula (4) is

`sum_{j=0}^{244} r ^ (2 * j * (491 * k - n))`.

The proof below is algebraic rather than a `244 × 244` case split.  Off the
diagonal, the summand ratio has order dividing `490`, is not one modulo
`491`, and hence differs from one by a unit modulo `491²`; cancellation in
the geometric-sum identity gives zero.  On the diagonal every summand is
one.

The positive-exponent presentation has diagonal residue
`245 * 2512 = 615440 = -107803 (mod 491²)`.  This replaces the accidental
exponent-37 simplification to `-1`.
-/

namespace Fermat.FourHundredNinetyOne.VandiverDiagonalArithmetic

open Finset

set_option maxHeartbeats 0
set_option maxRecDepth 100000

local instance : Fact (Nat.Prime 491) := ⟨by norm_num⟩

/-- Vandiver's source indices `1, ..., 244`, represented by `Fin 244`. -/
def sourceIndex (i : Fin 244) : ℕ := i.val + 1

/-- The positive Teichmüller lift whose reduction lies in the canonical
real half and therefore matches circular-unit column `a = 57`. -/
def teichmullerRoot491 : ℕ := 2512

/-- The exponent in the row-`k`, column-`n` character sum. -/
def characterExponent491 (k n : Fin 244) (j : ℕ) : ℕ :=
  2 * j * (491 * sourceIndex k - sourceIndex n)

/-- The 245-term character sum in Vandiver's formula (4). -/
def characterSum491 (k n : Fin 244) : ZMod (491 ^ 2) :=
  ∑ j ∈ range 245,
    (teichmullerRoot491 : ZMod (491 ^ 2)) ^
      characterExponent491 k n j

/-- `2512` is a Teichmüller lift modulo `491²`. -/
theorem teichmullerRoot491_pow_card_sub_one :
    (teichmullerRoot491 : ZMod (491 ^ 2)) ^ 490 = 1 := by
  decide

/-- Its reduction `57` is primitive modulo `491`. -/
theorem teichmullerRoot491_isPrimitive :
    IsPrimitiveRoot (teichmullerRoot491 : ZMod 491) 490 := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun n hnlt hnpos ↦ ?_⟩
  have hn : n ∈ Ioo 0 490 := by simp [hnpos, hnlt]
  fin_cases hn <;> decide

/-- The complete diagonal character-sum calculation. -/
theorem characterSum491_eq (k n : Fin 244) :
    characterSum491 k n = if k = n then 245 else 0 := by
  let d := 491 * sourceIndex k - sourceIndex n
  let w : ZMod (491 ^ 2) :=
    (teichmullerRoot491 : ZMod (491 ^ 2)) ^ (2 * d)
  have hsum :
      characterSum491 k n = ∑ j ∈ range 245, w ^ j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [← pow_mul]
    congr 1
    simp only [characterExponent491, d]
    ring
  by_cases hkn : k = n
  · subst n
    rw [if_pos rfl, hsum]
    have hw : w = 1 := by
      simp only [w, d]
      have heq :
          2 * (491 * sourceIndex k - sourceIndex k) =
            490 * (2 * sourceIndex k) := by
        have hk : 0 < sourceIndex k := by simp [sourceIndex]
        omega
      rw [heq, pow_mul, teichmullerRoot491_pow_card_sub_one, one_pow]
    rw [hw]
    simp
  · rw [if_neg hkn, hsum]
    have hw490 : w ^ 490 = 1 := by
      simp only [w]
      rw [← pow_mul]
      rw [show 2 * d * 490 = 490 * (2 * d) by ring]
      rw [pow_mul, teichmullerRoot491_pow_card_sub_one, one_pow]
    have hord : orderOf w ∣ 490 :=
      orderOf_dvd_iff_pow_eq_one.mpr hw490
    have hcop : (orderOf w).Coprime (491 ^ 2) :=
      Nat.Coprime.of_dvd_left hord (by norm_num)
    have hw_ne : w ≠ 1 := by
      intro hw
      have hmap := congrArg
        (ZMod.castHom (by norm_num : 491 ∣ 491 ^ 2) (ZMod 491)) hw
      simp only [w, map_pow, map_natCast, map_one] at hmap
      have hdvd : 490 ∣ 2 * d :=
        (teichmullerRoot491_isPrimitive.pow_eq_one_iff_dvd _).mp hmap
      have hdvd' : 245 ∣ d := by
        have : 2 * 245 ∣ 2 * d := by simpa using hdvd
        exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp this
      obtain ⟨q, hq⟩ := hdvd'
      have hkpos : 0 < sourceIndex k := by simp [sourceIndex]
      have hnpos : 0 < sourceIndex n := by simp [sourceIndex]
      have hkle : sourceIndex k ≤ 244 := by
        have hk := k.isLt
        simp [sourceIndex]
      have hnle : sourceIndex n ≤ 244 := by
        have hn := n.isLt
        simp [sourceIndex]
      have hd :
          d + sourceIndex n = 491 * sourceIndex k := by
        simp only [d]
        omega
      have hindex : sourceIndex k = sourceIndex n := by
        omega
      apply hkn
      apply Fin.ext
      simpa [sourceIndex] using hindex
    obtain hwone | hunit :=
      ZMod.eq_one_or_isUnit_sub_one
        (p := 491) (k := 2) rfl w hcop
    · exact (hw_ne hwone).elim
    · have hw245 : w ^ 245 = 1 := by
        simp only [w]
        rw [← pow_mul]
        rw [show 2 * d * 245 = 490 * d by ring]
        rw [pow_mul, teichmullerRoot491_pow_card_sub_one, one_pow]
      have hgeom := mul_geom_sum w 245
      rw [hw245, sub_self] at hgeom
      exact hunit.mul_left_cancel (by simpa using hgeom)

/-- Off-diagonal character sums vanish modulo `491²`. -/
theorem characterSum491_eq_zero {k n : Fin 244} (hkn : k ≠ n) :
    characterSum491 k n = 0 := by
  rw [characterSum491_eq, if_neg hkn]

/-- A diagonal character sum has the expected 245 terms. -/
theorem characterSum491_self (k : Fin 244) :
    characterSum491 k k = 245 := by
  rw [characterSum491_eq, if_pos rfl]

/-- Vandiver's positive exponent after multiplying the formal exponent by
`rho = r ^ (491²)`. -/
def positiveCharacterExponent491 (k n : Fin 244) (j : ℕ) : ℕ :=
  491 ^ 2 - 2 * sourceIndex n * j + 2 * 491 * sourceIndex k * j

/-- The same character sum in the positive-exponent presentation. -/
def positiveCharacterSum491 (k n : Fin 244) : ZMod (491 ^ 2) :=
  ∑ j ∈ range 245,
    (teichmullerRoot491 : ZMod (491 ^ 2)) ^
      positiveCharacterExponent491 k n j

/-- The positive-exponent sum is the original sum multiplied by
`rho = r^(491²)`. -/
theorem positiveCharacterSum491_eq_rho_mul (k n : Fin 244) :
    positiveCharacterSum491 k n =
      (teichmullerRoot491 : ZMod (491 ^ 2)) ^ (491 ^ 2) *
        characterSum491 k n := by
  rw [positiveCharacterSum491, characterSum491, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← pow_add]
  congr 1
  simp only [positiveCharacterExponent491, characterExponent491]
  have hjlt : j < 245 := Finset.mem_range.mp hj
  have hkpos : 0 < sourceIndex k := by simp [sourceIndex]
  have hnpos : 0 < sourceIndex n := by simp [sourceIndex]
  have hkle : sourceIndex k ≤ 244 := by
    have hk := k.isLt
    simp [sourceIndex]
  have hnle : sourceIndex n ≤ 244 := by
    have hn := n.isLt
    simp [sourceIndex]
  have hnPk : sourceIndex n ≤ 491 * sourceIndex k := by
    omega
  have hsmall :
      2 * sourceIndex n * j ≤ 491 ^ 2 := by
    calc
      2 * sourceIndex n * j ≤ 2 * 244 * 244 := by
        exact Nat.mul_le_mul
          (Nat.mul_le_mul_left 2 hnle)
          (Nat.le_of_lt_succ hjlt : j ≤ 244)
      _ ≤ 491 ^ 2 := by norm_num
  have hsmall' :
      2 * j * sourceIndex n ≤ 491 ^ 2 := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hsmall
  rw [show 2 * 491 * sourceIndex k * j =
      2 * j * (491 * sourceIndex k) by ring]
  rw [show 2 * sourceIndex n * j =
      2 * j * sourceIndex n by ring]
  rw [Nat.mul_sub_left_distrib]
  have hscaled :=
    Nat.mul_le_mul_left (2 * j) hnPk
  omega

/-- Positive-exponent form of the diagonal calculation. -/
theorem positiveCharacterSum491_eq (k n : Fin 244) :
    positiveCharacterSum491 k n =
      if k = n then
        245 * (teichmullerRoot491 : ZMod (491 ^ 2)) ^ (491 ^ 2)
      else 0 := by
  rw [positiveCharacterSum491_eq_rho_mul, characterSum491_eq]
  split_ifs <;> ring

/-- Since `491² ≡ 1 (mod 490)`, `rho` reduces to the Teichmüller root. -/
theorem rho491_eq_root :
    (teichmullerRoot491 : ZMod (491 ^ 2)) ^ (491 ^ 2) =
      teichmullerRoot491 := by
  rw [show 491 ^ 2 = 490 * 492 + 1 by norm_num, pow_add, pow_mul,
    teichmullerRoot491_pow_card_sub_one, one_pow, pow_one, one_mul]

/-- The exact diagonal residue is `615440`, equivalently `-107803`, modulo
`491²`; all off-diagonal residues vanish. -/
theorem positiveCharacterSum491_eq_neg107803_or_zero (k n : Fin 244) :
    positiveCharacterSum491 k n = if k = n then -107803 else 0 := by
  rw [positiveCharacterSum491_eq, rho491_eq_root]
  split_ifs <;> decide

/-- Multiplication by Vandiver's outer factor `p - 1 = 490` leaves the
exact coefficient `-52823470 = 490 * (-107803)` on the diagonal and zero
elsewhere.  Its canonical residue modulo `491²` is `214350`, hence it is
a `491`-adic unit. -/
theorem relationCharacterFactor491_eq (k n : Fin 244) :
    (490 : ZMod (491 ^ 2)) * positiveCharacterSum491 k n =
      if k = n then -52823470 else 0 := by
  rw [positiveCharacterSum491_eq_neg107803_or_zero]
  split_ifs <;> ring

end Fermat.FourHundredNinetyOne.VandiverDiagonalArithmetic
