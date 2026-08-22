import Fermat.Descent.Irregular.VandiverDiagonalArithmeticPrime

/-!
# The finite diagonal calculation in Vandiver's Lemma II at 607

Vandiver indexes his independent real units by
`1 ≤ i ≤ (p - 3) / 2`.  At `p = 607` there are 302 units and
303 terms in each character sum.

We use the small Teichmüller lift `t = 813` modulo `607²`.  It satisfies
`t ^ 606 = 1 (mod 607²)`, and its reduction is primitive modulo `607`.
At derivative order `2 * 607 * k`, the character sum in Vandiver's
formula (4) is

`sum_{j=0}^{302} t ^ (2 * j * (607 * k - n))`.

The prime-generic diagonal calculation shows that this sum is `303` on the
diagonal and zero off it.  In the positive-exponent presentation the
diagonal residue is

`303 * 813 = 246339 (mod 607²)`.

After multiplication by Vandiver's outer factor `606`, the exact integer
coefficient is `149281434`; its canonical residue modulo `607²` is
`59589`.
-/

namespace Fermat.SixHundredSeven.VandiverDiagonalArithmetic

open Finset

set_option maxHeartbeats 0
set_option maxRecDepth 100000

local instance : Fact (Nat.Prime 607) := ⟨by norm_num⟩

/-- Vandiver's source indices `1, ..., 302`, represented by `Fin 302`. -/
def sourceIndex (i : Fin 302) : ℕ := i.val + 1

/-- The small Teichmüller lift used for the exponent-`607` diagonal
calculation. -/
def teichmullerRoot607 : ℕ := 813

/-- The exponent in the row-`k`, column-`n` character sum. -/
def characterExponent607 (k n : Fin 302) (j : ℕ) : ℕ :=
  2 * j * (607 * sourceIndex k - sourceIndex n)

/-- The 303-term character sum in Vandiver's formula (4). -/
def characterSum607 (k n : Fin 302) : ZMod (607 ^ 2) :=
  ∑ j ∈ range 303,
    (teichmullerRoot607 : ZMod (607 ^ 2)) ^
      characterExponent607 k n j

/-- `813` is a Teichmüller lift modulo `607²`. -/
theorem teichmullerRoot607_pow_card_sub_one :
    (teichmullerRoot607 : ZMod (607 ^ 2)) ^ 606 = 1 := by
  decide

/-- The reduction of `813` is primitive modulo `607`. -/
theorem teichmullerRoot607_isPrimitive :
    IsPrimitiveRoot (teichmullerRoot607 : ZMod 607) 606 := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro q hq hqdiv
  have hfac : q ∣ 2 * (3 * 101) := by
    simpa using hqdiv
  have hcases : q = 2 ∨ q = 3 ∨ q = 101 := by
    rcases (hq.dvd_mul).mp hfac with h2 | hrest
    · exact Or.inl
        ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h2)
    rcases (hq.dvd_mul).mp hrest with h3 | h101
    · exact Or.inr <| Or.inl
        ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h3)
    · exact Or.inr <| Or.inr
        ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h101)
  rcases hcases with rfl | rfl | rfl <;> decide

/-- The complete diagonal character-sum calculation. -/
theorem characterSum607_eq (k n : Fin 302) :
    characterSum607 k n = if k = n then 303 else 0 := by
  simpa only [characterSum607, characterExponent607, sourceIndex,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.characterSum,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.characterExponent,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.sourceIndex,
    Nat.cast_ite, Nat.cast_ofNat, Nat.cast_zero] using
      Fermat.Irregular.VandiverDiagonalArithmeticPrime.characterSum_eq
        (p := 607) (r := 303) (t := teichmullerRoot607)
        (by norm_num) (by norm_num)
        teichmullerRoot607_pow_card_sub_one
        teichmullerRoot607_isPrimitive k n

/-- Off-diagonal character sums vanish modulo `607²`. -/
theorem characterSum607_eq_zero {k n : Fin 302} (hkn : k ≠ n) :
    characterSum607 k n = 0 := by
  rw [characterSum607_eq, if_neg hkn]

/-- A diagonal character sum has the expected 303 terms. -/
theorem characterSum607_self (k : Fin 302) :
    characterSum607 k k = 303 := by
  rw [characterSum607_eq, if_pos rfl]

/-- Vandiver's positive exponent after multiplying the formal exponent by
`rho = t ^ (607²)`. -/
def positiveCharacterExponent607 (k n : Fin 302) (j : ℕ) : ℕ :=
  607 ^ 2 - 2 * sourceIndex n * j + 2 * 607 * sourceIndex k * j

/-- The same character sum in the positive-exponent presentation. -/
def positiveCharacterSum607 (k n : Fin 302) : ZMod (607 ^ 2) :=
  ∑ j ∈ range 303,
    (teichmullerRoot607 : ZMod (607 ^ 2)) ^
      positiveCharacterExponent607 k n j

/-- The positive-exponent sum is the original sum multiplied by
`rho = t ^ (607²)`. -/
theorem positiveCharacterSum607_eq_rho_mul (k n : Fin 302) :
    positiveCharacterSum607 k n =
      (teichmullerRoot607 : ZMod (607 ^ 2)) ^ (607 ^ 2) *
        characterSum607 k n := by
  simpa only [positiveCharacterSum607, positiveCharacterExponent607,
    characterSum607, characterExponent607, sourceIndex,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.positiveCharacterSum,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.positiveCharacterExponent,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.characterSum,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.characterExponent,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.sourceIndex] using
      Fermat.Irregular.VandiverDiagonalArithmeticPrime.positiveCharacterSum_eq_rho_mul
        (p := 607) (r := 303) (t := teichmullerRoot607)
        (by norm_num) (by norm_num) k n

/-- Positive-exponent form of the diagonal calculation. -/
theorem positiveCharacterSum607_eq (k n : Fin 302) :
    positiveCharacterSum607 k n =
      if k = n then
        303 * (teichmullerRoot607 : ZMod (607 ^ 2)) ^ (607 ^ 2)
      else 0 := by
  rw [positiveCharacterSum607_eq_rho_mul, characterSum607_eq]
  split_ifs <;> ring

/-- Since `607² ≡ 1 (mod 606)`, `rho` reduces to the Teichmüller root. -/
theorem rho607_eq_root :
    (teichmullerRoot607 : ZMod (607 ^ 2)) ^ (607 ^ 2) =
      teichmullerRoot607 := by
  exact Fermat.Irregular.VandiverDiagonalArithmeticPrime.rho_eq_root
    (p := 607) (r := 303) (t := teichmullerRoot607)
    (by norm_num) (by norm_num)
    teichmullerRoot607_pow_card_sub_one

/-- The exact diagonal residue is `246339` modulo `607²`; all
off-diagonal residues vanish. -/
theorem positiveCharacterSum607_eq_246339_or_zero (k n : Fin 302) :
    positiveCharacterSum607 k n = if k = n then 246339 else 0 := by
  rw [positiveCharacterSum607_eq, rho607_eq_root]
  split_ifs <;> decide

/-- Multiplication by Vandiver's outer factor `p - 1 = 606` leaves the
exact coefficient `149281434 = 606 * 246339` on the diagonal and zero
elsewhere.  Its canonical residue modulo `607²` is `59589`, hence it is
a `607`-adic unit. -/
theorem relationCharacterFactor607_eq (k n : Fin 302) :
    (606 : ZMod (607 ^ 2)) * positiveCharacterSum607 k n =
      if k = n then 149281434 else 0 := by
  rw [positiveCharacterSum607_eq_246339_or_zero]
  split_ifs <;> ring

end Fermat.SixHundredSeven.VandiverDiagonalArithmetic
