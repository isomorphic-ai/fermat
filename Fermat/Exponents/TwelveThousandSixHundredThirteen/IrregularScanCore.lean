import Fermat.Descent.Irregular.ModularBernoulliScan

/-!
# Core definitions for the exponent-12613 irregular scan

The expensive finite scan is kept separate from its lightweight indexing
interface.  There are `6305` even indices in the classical range
`2 ≤ k ≤ 12610`.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScan

open Fermat.Irregular.ModularBernoulliScan
open Fermat.Irregular.Voronoi

/-- The four exceptional even indices reported by the finite package. -/
def irregularCandidates : Finset ℕ := {308, 502, 9400, 10536}

/-- The `i`-th even index in the classical range `2 ≤ k ≤ 12610`. -/
def scanIndex (i : Fin 6305) : ℕ := 2 * (i + 1)

/-- Embed a serialized scan block into the full `6305`-coordinate range. -/
def offsetIndex (offset size : ℕ) (h : offset + size ≤ 6305)
    (i : Fin size) : Fin 6305 :=
  ⟨offset + i.val, by omega⟩

theorem scanIndex_mem_irregularCandidates_iff (i : Fin 6305) :
    scanIndex i ∈ irregularCandidates ↔
      i.val = 153 ∨ i.val = 250 ∨ i.val = 4699 ∨ i.val = 5267 := by
  simp only [irregularCandidates, Finset.mem_insert, Finset.mem_singleton,
    scanIndex]
  omega

/-- At base two, the quotient weight vanishes on the lower half of the
standard representatives and is one on the upper half.  This form avoids
constructing enormous integer powers before reducing modulo `12613`. -/
theorem scanResidue_two_eq_upperSum (k : ℕ) :
    scanResidue 12613 2 k =
      ∑ m ∈ Finset.Ico 6307 12613,
        ((2 * m : ℕ) : ZMod 12613) ^ (k - 1) := by
  simp only [scanResidue, quotientPowerSum, Int.cast_sum, Int.cast_mul,
    Int.cast_natCast, Int.cast_pow, pow_one]
  rw [← Finset.sum_Ico_consecutive
    (fun m ↦ (((2 * m) / 12613 : ℕ) : ZMod 12613) *
      ((2 * m : ℕ) : ZMod 12613) ^ (k - 1))
    (by norm_num : 1 ≤ 6307) (by norm_num : 6307 ≤ 12613)]
  have hlow :
      (∑ m ∈ Finset.Ico 1 6307,
        (((2 * m) / 12613 : ℕ) : ZMod 12613) *
          ((2 * m : ℕ) : ZMod 12613) ^ (k - 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    have hm' := Finset.mem_Ico.mp hm
    have hdiv : 2 * m / 12613 = 0 :=
      Nat.div_eq_of_lt (by omega)
    simp [hdiv]
  rw [hlow, zero_add]
  apply Finset.sum_congr rfl
  intro m hm
  have hm' := Finset.mem_Ico.mp hm
  have hdiv : 2 * m / 12613 = 1 :=
    Nat.div_eq_of_lt_le (by omega) (by omega)
  simp [hdiv]

end Fermat.TwelveThousandSixHundredThirteen.IrregularScan
