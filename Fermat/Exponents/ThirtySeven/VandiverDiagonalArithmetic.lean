import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.Tactic

/-!
# The finite diagonal calculation in Vandiver's Lemma 2 at `37`

Vandiver indexes his independent units by `1 ≤ i ≤ (p - 3) / 2`.  There is a
one-character typo in the first display defining `E_i(w)` on p. 617: its
lower limit is printed as `j = 1`.  The very next display, which rewrites
`(E_i(w))^rho` with positive exponents, has `j = 0`; formula (4) on p. 619
also begins with the `j = 0` term `1`.  We use that internally consistent
range `0 ≤ j ≤ (p - 3) / 2`.  Thus at `p = 37` there are seventeen units and
eighteen terms in each character sum.

We use the Teichmüller lift `r = 76` of the primitive root `2` modulo `37`.
It satisfies `r ^ 36 = 1 (mod 37 ^ 2)`.  At derivative order `2 * 37 * k`,
the character sum occurring in Vandiver's formula (4) is

`sum_{j=0}^{17} r ^ (2 * j * (37 * k - n))`.

The theorems below certify that this sum is zero modulo `37 ^ 2` off the
diagonal and is `18` on the diagonal.  They also record the equivalent form
with Vandiver's positive integral exponents after raising his formal units to
`rho = r ^ (37 ^ 2)`.
-/

namespace Fermat.ThirtySeven.VandiverDiagonalArithmetic

open Finset

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Vandiver's unit indices `1, ..., 17`, represented by `Fin 17`. -/
def sourceIndex (i : Fin 17) : ℕ := i.val + 1

/-- The Teichmüller primitive root used for the concrete `37` calculation. -/
def teichmullerRoot37 : ℕ := 76

/-- The exponent in the character sum obtained from the `2 * 37 * k`th
logarithmic derivative of Vandiver's unit `E_n`. -/
def characterExponent37 (k n : Fin 17) (j : ℕ) : ℕ :=
  2 * j * (37 * sourceIndex k - sourceIndex n)

/-- The eighteen-term character sum in Vandiver's formula (4). -/
def characterSum37 (k n : Fin 17) : ZMod (37 ^ 2) :=
  ∑ j ∈ range 18,
    (teichmullerRoot37 : ZMod (37 ^ 2)) ^ characterExponent37 k n j

/-- `76` is a Teichmüller lift modulo `37²`. -/
theorem teichmullerRoot37_pow_card_sub_one :
    (teichmullerRoot37 : ZMod (37 ^ 2)) ^ 36 = 1 := by
  decide

/-- The concrete root remains primitive modulo `37`. -/
theorem teichmullerRoot37_isPrimitive :
    IsPrimitiveRoot (teichmullerRoot37 : ZMod 37) 36 := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun n hnlt hnpos ↦ ?_⟩
  have hn : n ∈ Ioo 0 36 := by simp [hnpos, hnlt]
  fin_cases hn <;> decide

/-- The complete finite diagonal character-sum calculation. -/
theorem characterSum37_eq (k n : Fin 17) :
    characterSum37 k n = if k = n then 18 else 0 := by
  fin_cases k <;> fin_cases n <;> decide

/-- Off-diagonal character sums vanish modulo `37²`. -/
theorem characterSum37_eq_zero {k n : Fin 17} (hkn : k ≠ n) :
    characterSum37 k n = 0 := by
  rw [characterSum37_eq, if_neg hkn]

/-- A diagonal character sum has the expected eighteen terms. -/
theorem characterSum37_self (k : Fin 17) : characterSum37 k k = 18 := by
  rw [characterSum37_eq, if_pos rfl]

/-- Vandiver's positive exponent after multiplying the formal exponent
`r ^ (-2*n*j)` by `rho = r ^ (37²)`, and then taking the derivative of the
`r^j`-rescaled basic unit. -/
def positiveCharacterExponent37 (k n : Fin 17) (j : ℕ) : ℕ :=
  37 ^ 2 - 2 * sourceIndex n * j + 2 * 37 * sourceIndex k * j

/-- The character sum written using only the positive exponents that occur
in Vandiver's integral polynomial `(E_n(w))^rho`. -/
def positiveCharacterSum37 (k n : Fin 17) : ZMod (37 ^ 2) :=
  ∑ j ∈ range 18,
    (teichmullerRoot37 : ZMod (37 ^ 2)) ^
      positiveCharacterExponent37 k n j

/-- The positive-exponent sum is the original character sum multiplied by
the common factor `rho = r^(37²)`. -/
theorem positiveCharacterSum37_eq_rho_mul (k n : Fin 17) :
    positiveCharacterSum37 k n =
      (teichmullerRoot37 : ZMod (37 ^ 2)) ^ (37 ^ 2) * characterSum37 k n := by
  fin_cases k <;> fin_cases n <;> decide

/-- The positive-exponent form of the same diagonal calculation. -/
theorem positiveCharacterSum37_eq (k n : Fin 17) :
    positiveCharacterSum37 k n =
      if k = n then
        18 * (teichmullerRoot37 : ZMod (37 ^ 2)) ^ (37 ^ 2)
      else 0 := by
  rw [positiveCharacterSum37_eq_rho_mul, characterSum37_eq]
  split_ifs <;> ring

/-- Since `37² = 38 * 36 + 1`, Vandiver's `rho = r^(37²)` is congruent to
`r` for the chosen Teichmüller lift. -/
theorem rho37_eq_root :
    (teichmullerRoot37 : ZMod (37 ^ 2)) ^ (37 ^ 2) =
      teichmullerRoot37 := by
  decide

/-- At `37`, the positive-exponent diagonal sum simplifies further:
`18 * rho = 18 * 76 = -1 (mod 37²)`. -/
theorem positiveCharacterSum37_eq_neg_one_or_zero (k n : Fin 17) :
    positiveCharacterSum37 k n = if k = n then -1 else 0 := by
  rw [positiveCharacterSum37_eq, rho37_eq_root]
  split_ifs <;> decide

/-- Multiplication by the outer factor `p - 1` in Vandiver's relation gives
the complete character factor `-36` on the diagonal and zero elsewhere. -/
theorem relationCharacterFactor37_eq (k n : Fin 17) :
    (36 : ZMod (37 ^ 2)) * positiveCharacterSum37 k n =
      if k = n then -36 else 0 := by
  rw [positiveCharacterSum37_eq_neg_one_or_zero]
  split_ifs <;> ring

end Fermat.ThirtySeven.VandiverDiagonalArithmetic
