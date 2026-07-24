import Fermat.Irregular.VandiverDiagonalArithmeticPrime

/-!
# The finite diagonal calculation in Vandiver's Lemma II at 1381

Vandiver indexes his independent real units by
`1 ≤ i ≤ (p - 3) / 2`.  At `p = 1381` there are 689 units and
690 terms in each character sum.

We use the small Teichmüller lift `t = 653` modulo `1381²`.  It satisfies
`t ^ 1380 = 1 (mod 1381²)`, and its reduction is primitive modulo `1381`.
At derivative order `2 * 1381 * k`, the character sum in Vandiver's
formula (4) is

`sum_{j=0}^{689} t ^ (2 * j * (1381 * k - n))`.

The prime-generic diagonal calculation shows that this sum is `690` on the
diagonal and zero off it.  In the positive-exponent presentation the
diagonal residue is

`690 * 653 = 450570 (mod 1381²)`.

After multiplication by Vandiver's outer factor `1380`, the exact integer
coefficient is `621786600`; its canonical residue modulo `1381²` is
`52114`.
-/

namespace Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalArithmetic

open Finset

set_option maxHeartbeats 0
set_option maxRecDepth 100000

local instance : Fact (Nat.Prime 1381) := ⟨by norm_num⟩

/-- Vandiver's source indices `1, ..., 689`, represented by `Fin 689`. -/
def sourceIndex (i : Fin 689) : ℕ := i.val + 1

/-- The small Teichmüller lift used for the exponent-`1381` diagonal
calculation. -/
def teichmullerRoot1381 : ℕ := 653

/-- The exponent in the row-`k`, column-`n` character sum. -/
def characterExponent1381 (k n : Fin 689) (j : ℕ) : ℕ :=
  2 * j * (1381 * sourceIndex k - sourceIndex n)

/-- The 690-term character sum in Vandiver's formula (4). -/
def characterSum1381 (k n : Fin 689) : ZMod (1381 ^ 2) :=
  ∑ j ∈ range 690,
    (teichmullerRoot1381 : ZMod (1381 ^ 2)) ^
      characterExponent1381 k n j

/-- `653` is a Teichmüller lift modulo `1381²`. -/
theorem teichmullerRoot1381_pow_card_sub_one :
    (teichmullerRoot1381 : ZMod (1381 ^ 2)) ^ 1380 = 1 := by
  decide

/-- The reduction of `653` is primitive modulo `1381`. -/
theorem teichmullerRoot1381_isPrimitive :
    IsPrimitiveRoot (teichmullerRoot1381 : ZMod 1381) 1380 := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro q hq hqdiv
  have hfac : q ∣ 2 * (2 * (3 * (5 * 23))) := by
    simpa using hqdiv
  have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 23 := by
    rcases (hq.dvd_mul).mp hfac with h2 | hrest
    · exact Or.inl
        ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h2)
    rcases (hq.dvd_mul).mp hrest with h2 | hrest
    · exact Or.inl
        ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h2)
    rcases (hq.dvd_mul).mp hrest with h3 | hrest
    · exact Or.inr <| Or.inl
        ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h3)
    rcases (hq.dvd_mul).mp hrest with h5 | h23
    · exact Or.inr <| Or.inr <| Or.inl
        ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h5)
    · exact Or.inr <| Or.inr <| Or.inr
        ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h23)
  rcases hcases with rfl | rfl | rfl | rfl <;> decide

/-- The complete diagonal character-sum calculation. -/
theorem characterSum1381_eq (k n : Fin 689) :
    characterSum1381 k n = if k = n then 690 else 0 := by
  simpa only [characterSum1381, characterExponent1381, sourceIndex,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.characterSum,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.characterExponent,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.sourceIndex,
    Nat.cast_ite, Nat.cast_ofNat, Nat.cast_zero] using
      Fermat.Irregular.VandiverDiagonalArithmeticPrime.characterSum_eq
        (p := 1381) (r := 690) (t := teichmullerRoot1381)
        (by norm_num) (by norm_num)
        teichmullerRoot1381_pow_card_sub_one
        teichmullerRoot1381_isPrimitive k n

/-- Off-diagonal character sums vanish modulo `1381²`. -/
theorem characterSum1381_eq_zero {k n : Fin 689} (hkn : k ≠ n) :
    characterSum1381 k n = 0 := by
  rw [characterSum1381_eq, if_neg hkn]

/-- A diagonal character sum has the expected 690 terms. -/
theorem characterSum1381_self (k : Fin 689) :
    characterSum1381 k k = 690 := by
  rw [characterSum1381_eq, if_pos rfl]

/-- Vandiver's positive exponent after multiplying the formal exponent by
`rho = t ^ (1381²)`. -/
def positiveCharacterExponent1381 (k n : Fin 689) (j : ℕ) : ℕ :=
  1381 ^ 2 - 2 * sourceIndex n * j + 2 * 1381 * sourceIndex k * j

/-- The same character sum in the positive-exponent presentation. -/
def positiveCharacterSum1381 (k n : Fin 689) : ZMod (1381 ^ 2) :=
  ∑ j ∈ range 690,
    (teichmullerRoot1381 : ZMod (1381 ^ 2)) ^
      positiveCharacterExponent1381 k n j

/-- The positive-exponent sum is the original sum multiplied by
`rho = t ^ (1381²)`. -/
theorem positiveCharacterSum1381_eq_rho_mul (k n : Fin 689) :
    positiveCharacterSum1381 k n =
      (teichmullerRoot1381 : ZMod (1381 ^ 2)) ^ (1381 ^ 2) *
        characterSum1381 k n := by
  simpa only [positiveCharacterSum1381, positiveCharacterExponent1381,
    characterSum1381, characterExponent1381, sourceIndex,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.positiveCharacterSum,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.positiveCharacterExponent,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.characterSum,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.characterExponent,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.sourceIndex] using
      Fermat.Irregular.VandiverDiagonalArithmeticPrime.positiveCharacterSum_eq_rho_mul
        (p := 1381) (r := 690) (t := teichmullerRoot1381)
        (by norm_num) (by norm_num) k n

/-- Positive-exponent form of the diagonal calculation. -/
theorem positiveCharacterSum1381_eq (k n : Fin 689) :
    positiveCharacterSum1381 k n =
      if k = n then
        690 * (teichmullerRoot1381 : ZMod (1381 ^ 2)) ^ (1381 ^ 2)
      else 0 := by
  rw [positiveCharacterSum1381_eq_rho_mul, characterSum1381_eq]
  split_ifs <;> ring

/-- Since `1381² ≡ 1 (mod 1380)`, `rho` reduces to the Teichmüller root. -/
theorem rho1381_eq_root :
    (teichmullerRoot1381 : ZMod (1381 ^ 2)) ^ (1381 ^ 2) =
      teichmullerRoot1381 := by
  exact Fermat.Irregular.VandiverDiagonalArithmeticPrime.rho_eq_root
    (p := 1381) (r := 690) (t := teichmullerRoot1381)
    (by norm_num) (by norm_num)
    teichmullerRoot1381_pow_card_sub_one

/-- The exact diagonal residue is `450570` modulo `1381²`; all
off-diagonal residues vanish. -/
theorem positiveCharacterSum1381_eq_450570_or_zero (k n : Fin 689) :
    positiveCharacterSum1381 k n = if k = n then 450570 else 0 := by
  rw [positiveCharacterSum1381_eq, rho1381_eq_root]
  split_ifs <;> decide

/-- Multiplication by Vandiver's outer factor `p - 1 = 1380` leaves the
exact coefficient `621786600 = 1380 * 450570` on the diagonal and zero
elsewhere.  Its canonical residue modulo `1381²` is `52114`, hence it is
a `1381`-adic unit. -/
theorem relationCharacterFactor1381_eq (k n : Fin 689) :
    (1380 : ZMod (1381 ^ 2)) * positiveCharacterSum1381 k n =
      if k = n then 621786600 else 0 := by
  rw [positiveCharacterSum1381_eq_450570_or_zero]
  split_ifs <;> ring

end Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalArithmetic
