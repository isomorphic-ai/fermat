import Fermat.Irregular.VandiverDiagonalArithmeticPrime

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
  simpa only [characterSum691, characterExponent691, sourceIndex,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.characterSum,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.characterExponent,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.sourceIndex,
    Nat.cast_ite, Nat.cast_ofNat, Nat.cast_zero] using
      Fermat.Irregular.VandiverDiagonalArithmeticPrime.characterSum_eq
        (p := 691) (r := 345) (t := teichmullerRoot691)
        (by norm_num) (by norm_num)
        teichmullerRoot691_pow_card_sub_one
        teichmullerRoot691_isPrimitive k n

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
  simpa only [positiveCharacterSum691, positiveCharacterExponent691,
    characterSum691, characterExponent691, sourceIndex,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.positiveCharacterSum,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.positiveCharacterExponent,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.characterSum,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.characterExponent,
    Fermat.Irregular.VandiverDiagonalArithmeticPrime.sourceIndex] using
      Fermat.Irregular.VandiverDiagonalArithmeticPrime.positiveCharacterSum_eq_rho_mul
        (p := 691) (r := 345) (t := teichmullerRoot691)
        (by norm_num) (by norm_num) k n

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
  exact Fermat.Irregular.VandiverDiagonalArithmeticPrime.rho_eq_root
    (p := 691) (r := 345) (t := teichmullerRoot691)
    (by norm_num) (by norm_num)
    teichmullerRoot691_pow_card_sub_one

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
