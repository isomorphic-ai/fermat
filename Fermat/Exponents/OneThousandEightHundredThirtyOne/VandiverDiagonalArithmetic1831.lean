import Fermat.Descent.Irregular.VandiverDiagonalArithmeticPrime

/-!
# The finite diagonal calculation in Vandiver's Lemma II at 1831

Vandiver indexes his independent real units by
`1 ≤ i ≤ (p - 3) / 2`.  At `p = 1831` there are 914 units and
915 terms in each character sum.

We use the small Teichmüller lift `t = 4746` modulo `1831²`.  It satisfies
`t ^ 1830 = 1 (mod 1831²)`, and its reduction is primitive modulo `1831`.
At derivative order `2 * 1831 * k`, the character sum in Vandiver's
formula (4) is

`sum_{j=0}^{914} t ^ (2 * j * (1831 * k - n))`.

The prime-generic diagonal calculation shows that this sum is `915` on the
diagonal and zero off it.  In the positive-exponent presentation the
diagonal residue is

`915 * 4746 = 4342590 (mod 1831²)`.

After multiplication by Vandiver's outer factor `1830`, the exact integer
coefficient is `7946939700`; its canonical residue modulo `1831²` is
`1370130`.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.VandiverDiagonalArithmetic

open Finset

set_option maxHeartbeats 0
set_option maxRecDepth 100000

local instance : Fact (Nat.Prime 1831) := ⟨by norm_num⟩

/-- Vandiver's source indices `1, ..., 914`, represented by `Fin 914`. -/
def sourceIndex (i : Fin 914) : ℕ := i.val + 1

/-- The small Teichmüller lift used for the exponent-`1831` diagonal
calculation. -/
def teichmullerRoot1831 : ℕ := 4746

/-- The exponent in the row-`k`, column-`n` character sum. -/
def characterExponent1831 (k n : Fin 914) (j : ℕ) : ℕ :=
  2 * j * (1831 * sourceIndex k - sourceIndex n)

/-- The 915-term character sum in Vandiver's formula (4). -/
def characterSum1831 (k n : Fin 914) : ZMod (1831 ^ 2) :=
  ∑ j ∈ range 915,
    (teichmullerRoot1831 : ZMod (1831 ^ 2)) ^
      characterExponent1831 k n j

/-- `4746` is a Teichmüller lift modulo `1831²`. -/
theorem teichmullerRoot1831_pow_card_sub_one :
    (teichmullerRoot1831 : ZMod (1831 ^ 2)) ^ 1830 = 1 := by
  decide

/-- The reduction of `4746` is primitive modulo `1831`. -/
theorem teichmullerRoot1831_isPrimitive :
    IsPrimitiveRoot (teichmullerRoot1831 : ZMod 1831) 1830 := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro q hq hqdiv
  have hfac : q ∣ 2 * (3 * (5 * 61)) := by
    simpa using hqdiv
  have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 61 := by
    rcases (hq.dvd_mul).mp hfac with h2 | hrest
    · exact Or.inl
        ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h2)
    rcases (hq.dvd_mul).mp hrest with h3 | hrest
    · exact Or.inr <| Or.inl
        ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h3)
    rcases (hq.dvd_mul).mp hrest with h5 | h61
    · exact Or.inr <| Or.inr <| Or.inl
        ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h5)
    · exact Or.inr <| Or.inr <| Or.inr
        ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h61)
  rcases hcases with rfl | rfl | rfl | rfl <;> decide

/-- The complete diagonal character-sum calculation. -/
theorem characterSum1831_eq (k n : Fin 914) :
    characterSum1831 k n = if k = n then 915 else 0 := by
  simpa only [characterSum1831, characterExponent1831, sourceIndex,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.characterSum,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.characterExponent,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.sourceIndex,
    Nat.cast_ite, Nat.cast_ofNat, Nat.cast_zero] using
      Fermat.Irregular.VandiverDiagonalArithmeticPrime.characterSum_eq
        (p := 1831) (r := 915) (t := teichmullerRoot1831)
        (by norm_num) (by norm_num)
        teichmullerRoot1831_pow_card_sub_one
        teichmullerRoot1831_isPrimitive k n

/-- Off-diagonal character sums vanish modulo `1831²`. -/
theorem characterSum1831_eq_zero {k n : Fin 914} (hkn : k ≠ n) :
    characterSum1831 k n = 0 := by
  rw [characterSum1831_eq, if_neg hkn]

/-- A diagonal character sum has the expected 915 terms. -/
theorem characterSum1831_self (k : Fin 914) :
    characterSum1831 k k = 915 := by
  rw [characterSum1831_eq, if_pos rfl]

/-- Vandiver's positive exponent after multiplying the formal exponent by
`rho = t ^ (1831²)`. -/
def positiveCharacterExponent1831 (k n : Fin 914) (j : ℕ) : ℕ :=
  1831 ^ 2 - 2 * sourceIndex n * j + 2 * 1831 * sourceIndex k * j

/-- The same character sum in the positive-exponent presentation. -/
def positiveCharacterSum1831 (k n : Fin 914) : ZMod (1831 ^ 2) :=
  ∑ j ∈ range 915,
    (teichmullerRoot1831 : ZMod (1831 ^ 2)) ^
      positiveCharacterExponent1831 k n j

/-- The positive-exponent sum is the original sum multiplied by
`rho = t ^ (1831²)`. -/
theorem positiveCharacterSum1831_eq_rho_mul (k n : Fin 914) :
    positiveCharacterSum1831 k n =
      (teichmullerRoot1831 : ZMod (1831 ^ 2)) ^ (1831 ^ 2) *
        characterSum1831 k n := by
  simpa only [positiveCharacterSum1831, positiveCharacterExponent1831,
    characterSum1831, characterExponent1831, sourceIndex,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.positiveCharacterSum,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.positiveCharacterExponent,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.characterSum,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.characterExponent,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.sourceIndex] using
      Fermat.Irregular.VandiverDiagonalArithmeticPrime.positiveCharacterSum_eq_rho_mul
        (p := 1831) (r := 915) (t := teichmullerRoot1831)
        (by norm_num) (by norm_num) k n

/-- Positive-exponent form of the diagonal calculation. -/
theorem positiveCharacterSum1831_eq (k n : Fin 914) :
    positiveCharacterSum1831 k n =
      if k = n then
        915 * (teichmullerRoot1831 : ZMod (1831 ^ 2)) ^ (1831 ^ 2)
      else 0 := by
  rw [positiveCharacterSum1831_eq_rho_mul, characterSum1831_eq]
  split_ifs <;> ring

/-- Since `1831² ≡ 1 (mod 1830)`, `rho` reduces to the Teichmüller root. -/
theorem rho1831_eq_root :
    (teichmullerRoot1831 : ZMod (1831 ^ 2)) ^ (1831 ^ 2) =
      teichmullerRoot1831 := by
  exact Fermat.Irregular.VandiverDiagonalArithmeticPrime.rho_eq_root
    (p := 1831) (r := 915) (t := teichmullerRoot1831)
    (by norm_num) (by norm_num)
    teichmullerRoot1831_pow_card_sub_one

/-- The exact diagonal residue is `4342590` modulo `1831²`; all
off-diagonal residues vanish. -/
theorem positiveCharacterSum1831_eq_4342590_or_zero (k n : Fin 914) :
    positiveCharacterSum1831 k n = if k = n then 4342590 else 0 := by
  rw [positiveCharacterSum1831_eq, rho1831_eq_root]
  split_ifs <;> decide

/-- Multiplication by Vandiver's outer factor `p - 1 = 1830` leaves the
exact coefficient `7946939700 = 1830 * 4342590` on the diagonal and zero
elsewhere.  Its canonical residue modulo `1831²` is `1370130`, hence it is
a `1831`-adic unit. -/
theorem relationCharacterFactor1831_eq (k n : Fin 914) :
    (1830 : ZMod (1831 ^ 2)) * positiveCharacterSum1831 k n =
      if k = n then 7946939700 else 0 := by
  rw [positiveCharacterSum1831_eq_4342590_or_zero]
  split_ifs <;> ring

end Fermat.OneThousandEightHundredThirtyOne.VandiverDiagonalArithmetic
