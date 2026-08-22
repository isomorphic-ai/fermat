import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.Tactic

/-!
# The finite diagonal calculation in Vandiver's Lemma 2 at `59`

Vandiver indexes the independent real units by
`1 ≤ i ≤ (p - 3) / 2`.  As in the checked exponent-`37` development, the
internally consistent range in the source is
`0 ≤ j ≤ (p - 3) / 2`: the displayed product therefore has twenty-nine
terms at `p = 59`.

The integer `946 = 2^59 mod 59^2` is the Teichmüller lift of the primitive
root `2` modulo `59`.  At derivative order `2 * 59 * k`, the character sum
in Vandiver's formula is diagonal modulo `59^2`.  Unlike the numerical
coincidence at exponent `37`, its positive-exponent diagonal is

`29 * 946 = 3067 = -414 (mod 59^2)`.

After multiplication by the outer factor `p - 1`, the complete diagonal
coefficient is `355`.  The important structural fact for the valuation
argument is that this coefficient is a `59`-adic unit.
-/

namespace Fermat.FiftyNine.VandiverDiagonalArithmetic

open Finset

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Vandiver's unit indices `1, ..., 28`, represented by `Fin 28`. -/
def sourceIndex (i : Fin 28) : ℕ := i.val + 1

/-- The Teichmüller primitive root used for the concrete `59` calculation. -/
def teichmullerRoot59 : ℕ := 946

/-- The exponent in the character sum obtained from the `2 * 59 * k`th
logarithmic derivative of Vandiver's unit `E_n`. -/
def characterExponent59 (k n : Fin 28) (j : ℕ) : ℕ :=
  2 * j * (59 * sourceIndex k - sourceIndex n)

/-- The twenty-nine-term character sum in Vandiver's formula. -/
def characterSum59 (k n : Fin 28) : ZMod (59 ^ 2) :=
  ∑ j ∈ range 29,
    (teichmullerRoot59 : ZMod (59 ^ 2)) ^ characterExponent59 k n j

/-- `946` is a Teichmüller lift modulo `59²`. -/
theorem teichmullerRoot59_pow_card_sub_one :
    (teichmullerRoot59 : ZMod (59 ^ 2)) ^ 58 = 1 := by
  decide

/-- The concrete root remains primitive modulo `59`. -/
theorem teichmullerRoot59_isPrimitive :
    IsPrimitiveRoot (teichmullerRoot59 : ZMod 59) 58 := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun n hnlt hnpos ↦ ?_⟩
  have hn : n ∈ Ioo 0 58 := by simp [hnpos, hnlt]
  fin_cases hn <;> decide

/-- The complete finite diagonal character-sum calculation. -/
theorem characterSum59_eq (k n : Fin 28) :
    characterSum59 k n = if k = n then 29 else 0 := by
  fin_cases k <;> fin_cases n <;> decide

/-- Off-diagonal character sums vanish modulo `59²`. -/
theorem characterSum59_eq_zero {k n : Fin 28} (hkn : k ≠ n) :
    characterSum59 k n = 0 := by
  rw [characterSum59_eq, if_neg hkn]

/-- A diagonal character sum has the expected twenty-nine terms. -/
theorem characterSum59_self (k : Fin 28) : characterSum59 k k = 29 := by
  rw [characterSum59_eq, if_pos rfl]

/-- Vandiver's positive exponent after multiplying the formal exponent
`r ^ (-2*n*j)` by `rho = r ^ (59²)`, and then taking the derivative of the
`r^j`-rescaled basic unit. -/
def positiveCharacterExponent59 (k n : Fin 28) (j : ℕ) : ℕ :=
  59 ^ 2 - 2 * sourceIndex n * j + 2 * 59 * sourceIndex k * j

/-- The character sum written using only the positive exponents that occur
in Vandiver's integral polynomial `(E_n(w))^rho`. -/
def positiveCharacterSum59 (k n : Fin 28) : ZMod (59 ^ 2) :=
  ∑ j ∈ range 29,
    (teichmullerRoot59 : ZMod (59 ^ 2)) ^
      positiveCharacterExponent59 k n j

/-- The positive-exponent sum is the original character sum multiplied by
the common factor `rho = r^(59²)`. -/
theorem positiveCharacterSum59_eq_rho_mul (k n : Fin 28) :
    positiveCharacterSum59 k n =
      (teichmullerRoot59 : ZMod (59 ^ 2)) ^ (59 ^ 2) *
        characterSum59 k n := by
  fin_cases k <;> fin_cases n <;> decide

/-- The positive-exponent form of the same diagonal calculation. -/
theorem positiveCharacterSum59_eq (k n : Fin 28) :
    positiveCharacterSum59 k n =
      if k = n then
        29 * (teichmullerRoot59 : ZMod (59 ^ 2)) ^ (59 ^ 2)
      else 0 := by
  rw [positiveCharacterSum59_eq_rho_mul, characterSum59_eq]
  split_ifs <;> ring

/-- Since `59² = 60 * 58 + 1`, `rho = r^(59²)` is congruent to `r`. -/
theorem rho59_eq_root :
    (teichmullerRoot59 : ZMod (59 ^ 2)) ^ (59 ^ 2) =
      teichmullerRoot59 := by
  decide

/-- The positive-exponent diagonal sum is `3067` modulo `59²`. -/
theorem positiveCharacterSum59_eq_diagonal (k n : Fin 28) :
    positiveCharacterSum59 k n = if k = n then 3067 else 0 := by
  rw [positiveCharacterSum59_eq, rho59_eq_root]
  split_ifs <;> decide

/-- Multiplication by the outer factor `p - 1` gives the complete
character coefficient `355` on the diagonal and zero elsewhere. -/
theorem relationCharacterFactor59_eq (k n : Fin 28) :
    (58 : ZMod (59 ^ 2)) * positiveCharacterSum59 k n =
      if k = n then 355 else 0 := by
  rw [positiveCharacterSum59_eq_diagonal]
  split_ifs <;> decide

/-- The diagonal coefficient is a `59`-adic unit. -/
theorem fiftyNine_not_dvd_relationCharacterCoefficient :
    ¬(59 : ℤ) ∣ 355 := by
  norm_num

end Fermat.FiftyNine.VandiverDiagonalArithmetic
