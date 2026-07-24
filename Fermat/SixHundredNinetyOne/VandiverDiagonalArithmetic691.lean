import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.Tactic

/-!
# The finite diagonal calculation in Vandiver's Lemma II at 691

Vandiver indexes his independent real units by
`1 ≤ i ≤ (p - 3) / 2`.  At `p = 691` there are 344 units and
345 terms in each character sum.

We use the small Teichmüller lift `r = 4955` of the primitive root `118`
modulo `691`.  It satisfies `r ^ 690 = 1 (mod 691 ^ 2)`.  At derivative
order `2 * 691 * k`, the character sum in Vandiver's formula (4) is

`sum_{j=0}^{344} r ^ (2 * j * (691 * k - n))`.

The proof below is algebraic rather than a `344 × 344` case split.  Off the
diagonal, the summand ratio has order dividing `690`, is not one modulo
`691`, and hence differs from one by a unit modulo `691²`; cancellation in
the geometric-sum identity gives zero.  On the diagonal every summand is
one.

The positive-exponent presentation has diagonal residue
`345 * 4955 = 1709475 = -200449 (mod 691²)`.  This replaces the accidental
exponent-37 simplification to `-1`.
-/

namespace Fermat.SixHundredNinetyOne.VandiverDiagonalArithmetic

open Finset

set_option maxHeartbeats 0
set_option maxRecDepth 100000

local instance : Fact (Nat.Prime 691) := ⟨by norm_num⟩

/-- Vandiver's source indices `1, ..., 344`, represented by `Fin 344`. -/
def sourceIndex (i : Fin 344) : ℕ := i.val + 1

/-- The positive Teichmüller lift whose reduction lies in the canonical
real half and therefore matches circular-unit column `a = 118`. -/
def teichmullerRoot691 : ℕ := 4955

/-- The exponent in the row-`k`, column-`n` character sum. -/
def characterExponent691 (k n : Fin 344) (j : ℕ) : ℕ :=
  2 * j * (691 * sourceIndex k - sourceIndex n)

/-- The 345-term character sum in Vandiver's formula (4). -/
def characterSum691 (k n : Fin 344) : ZMod (691 ^ 2) :=
  ∑ j ∈ range 345,
    (teichmullerRoot691 : ZMod (691 ^ 2)) ^
      characterExponent691 k n j

/-- `4955` is a Teichmüller lift modulo `691²`. -/
theorem teichmullerRoot691_pow_card_sub_one :
    (teichmullerRoot691 : ZMod (691 ^ 2)) ^ 690 = 1 := by
  decide

/-- Its reduction `118` is primitive modulo `691`. -/
theorem teichmullerRoot691_isPrimitive :
    IsPrimitiveRoot (teichmullerRoot691 : ZMod 691) 690 := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun n hnlt hnpos ↦ ?_⟩
  have hn : n ∈ Ioo 0 690 := by simp [hnpos, hnlt]
  fin_cases hn <;> decide

/-- The complete diagonal character-sum calculation. -/
theorem characterSum691_eq (k n : Fin 344) :
    characterSum691 k n = if k = n then 345 else 0 := by
  let d := 691 * sourceIndex k - sourceIndex n
  let w : ZMod (691 ^ 2) :=
    (teichmullerRoot691 : ZMod (691 ^ 2)) ^ (2 * d)
  have hsum :
      characterSum691 k n = ∑ j ∈ range 345, w ^ j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [← pow_mul]
    congr 1
    simp only [characterExponent691, d]
    ring
  by_cases hkn : k = n
  · subst n
    rw [if_pos rfl, hsum]
    have hw : w = 1 := by
      simp only [w, d]
      have heq :
          2 * (691 * sourceIndex k - sourceIndex k) =
            690 * (2 * sourceIndex k) := by
        have hk : 0 < sourceIndex k := by simp [sourceIndex]
        omega
      rw [heq, pow_mul, teichmullerRoot691_pow_card_sub_one, one_pow]
    rw [hw]
    simp
  · rw [if_neg hkn, hsum]
    have hw690 : w ^ 690 = 1 := by
      simp only [w]
      rw [← pow_mul]
      rw [show 2 * d * 690 = 690 * (2 * d) by ring]
      rw [pow_mul, teichmullerRoot691_pow_card_sub_one, one_pow]
    have hord : orderOf w ∣ 690 :=
      orderOf_dvd_iff_pow_eq_one.mpr hw690
    have hcop : (orderOf w).Coprime (691 ^ 2) :=
      Nat.Coprime.of_dvd_left hord (by norm_num)
    have hw_ne : w ≠ 1 := by
      intro hw
      have hmap := congrArg
        (ZMod.castHom (by norm_num : 691 ∣ 691 ^ 2) (ZMod 691)) hw
      simp only [w, map_pow, map_natCast, map_one] at hmap
      have hdvd : 690 ∣ 2 * d :=
        (teichmullerRoot691_isPrimitive.pow_eq_one_iff_dvd _).mp hmap
      have hdvd' : 345 ∣ d := by
        have : 2 * 345 ∣ 2 * d := by simpa using hdvd
        exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp this
      obtain ⟨q, hq⟩ := hdvd'
      have hkpos : 0 < sourceIndex k := by simp [sourceIndex]
      have hnpos : 0 < sourceIndex n := by simp [sourceIndex]
      have hkle : sourceIndex k ≤ 344 := by
        have hk := k.isLt
        simp [sourceIndex]
      have hnle : sourceIndex n ≤ 344 := by
        have hn := n.isLt
        simp [sourceIndex]
      have hd :
          d + sourceIndex n = 691 * sourceIndex k := by
        simp only [d]
        omega
      have hindex : sourceIndex k = sourceIndex n := by
        omega
      apply hkn
      apply Fin.ext
      simpa [sourceIndex] using hindex
    obtain hwone | hunit :=
      ZMod.eq_one_or_isUnit_sub_one
        (p := 691) (k := 2) rfl w hcop
    · exact (hw_ne hwone).elim
    · have hw345 : w ^ 345 = 1 := by
        simp only [w]
        rw [← pow_mul]
        rw [show 2 * d * 345 = 690 * d by ring]
        rw [pow_mul, teichmullerRoot691_pow_card_sub_one, one_pow]
      have hgeom := mul_geom_sum w 345
      rw [hw345, sub_self] at hgeom
      exact hunit.mul_left_cancel (by simpa using hgeom)

/-- Off-diagonal character sums vanish modulo `691²`. -/
theorem characterSum691_eq_zero {k n : Fin 344} (hkn : k ≠ n) :
    characterSum691 k n = 0 := by
  rw [characterSum691_eq, if_neg hkn]

/-- A diagonal character sum has the expected 345 terms. -/
theorem characterSum691_self (k : Fin 344) :
    characterSum691 k k = 345 := by
  rw [characterSum691_eq, if_pos rfl]

/-- Vandiver's positive exponent after multiplying the formal exponent by
`rho = r ^ (691²)`. -/
def positiveCharacterExponent691 (k n : Fin 344) (j : ℕ) : ℕ :=
  691 ^ 2 - 2 * sourceIndex n * j + 2 * 691 * sourceIndex k * j

/-- The same character sum in the positive-exponent presentation. -/
def positiveCharacterSum691 (k n : Fin 344) : ZMod (691 ^ 2) :=
  ∑ j ∈ range 345,
    (teichmullerRoot691 : ZMod (691 ^ 2)) ^
      positiveCharacterExponent691 k n j

/-- The positive-exponent sum is the original sum multiplied by
`rho = r^(691²)`. -/
theorem positiveCharacterSum691_eq_rho_mul (k n : Fin 344) :
    positiveCharacterSum691 k n =
      (teichmullerRoot691 : ZMod (691 ^ 2)) ^ (691 ^ 2) *
        characterSum691 k n := by
  rw [positiveCharacterSum691, characterSum691, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← pow_add]
  congr 1
  simp only [positiveCharacterExponent691, characterExponent691]
  have hjlt : j < 345 := Finset.mem_range.mp hj
  have hkpos : 0 < sourceIndex k := by simp [sourceIndex]
  have hnpos : 0 < sourceIndex n := by simp [sourceIndex]
  have hkle : sourceIndex k ≤ 344 := by
    have hk := k.isLt
    simp [sourceIndex]
  have hnle : sourceIndex n ≤ 344 := by
    have hn := n.isLt
    simp [sourceIndex]
  have hnPk : sourceIndex n ≤ 691 * sourceIndex k := by
    omega
  have hsmall :
      2 * sourceIndex n * j ≤ 691 ^ 2 := by
    calc
      2 * sourceIndex n * j ≤ 2 * 344 * 344 := by
        exact Nat.mul_le_mul
          (Nat.mul_le_mul_left 2 hnle)
          (Nat.le_of_lt_succ hjlt : j ≤ 344)
      _ ≤ 691 ^ 2 := by norm_num
  have hsmall' :
      2 * j * sourceIndex n ≤ 691 ^ 2 := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hsmall
  rw [show 2 * 691 * sourceIndex k * j =
      2 * j * (691 * sourceIndex k) by ring]
  rw [show 2 * sourceIndex n * j =
      2 * j * sourceIndex n by ring]
  rw [Nat.mul_sub_left_distrib]
  have hscaled :=
    Nat.mul_le_mul_left (2 * j) hnPk
  omega

/-- Positive-exponent form of the diagonal calculation. -/
theorem positiveCharacterSum691_eq (k n : Fin 344) :
    positiveCharacterSum691 k n =
      if k = n then
        345 * (teichmullerRoot691 : ZMod (691 ^ 2)) ^ (691 ^ 2)
      else 0 := by
  rw [positiveCharacterSum691_eq_rho_mul, characterSum691_eq]
  split_ifs <;> ring

/-- Since `691² ≡ 1 (mod 690)`, `rho` reduces to the Teichmüller root. -/
theorem rho691_eq_root :
    (teichmullerRoot691 : ZMod (691 ^ 2)) ^ (691 ^ 2) =
      teichmullerRoot691 := by
  rw [show 691 ^ 2 = 690 * 692 + 1 by norm_num, pow_add, pow_mul,
    teichmullerRoot691_pow_card_sub_one, one_pow, pow_one, one_mul]

/-- The exact diagonal residue is `1709475`, equivalently `-200449`, modulo
`691²`; all off-diagonal residues vanish. -/
theorem positiveCharacterSum691_eq_neg200449_or_zero (k n : Fin 344) :
    positiveCharacterSum691 k n = if k = n then -200449 else 0 := by
  rw [positiveCharacterSum691_eq, rho691_eq_root]
  split_ifs <;> decide

/-- Multiplication by Vandiver's outer factor `p - 1 = 690` leaves the
exact coefficient `-138309810 = 690 * (-200449)` on the diagonal and zero
elsewhere.  Its canonical residue modulo `691²` is `159680`, hence it is
a `691`-adic unit. -/
theorem relationCharacterFactor691_eq (k n : Fin 344) :
    (690 : ZMod (691 ^ 2)) * positiveCharacterSum691 k n =
      if k = n then -138309810 else 0 := by
  rw [positiveCharacterSum691_eq_neg200449_or_zero]
  split_ifs <;> ring

end Fermat.SixHundredNinetyOne.VandiverDiagonalArithmetic
