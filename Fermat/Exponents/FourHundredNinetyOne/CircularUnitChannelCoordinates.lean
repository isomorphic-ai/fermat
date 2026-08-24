import Fermat.Descent.Irregular.CircularUnitResiduePresentation
import Fermat.Exponents.FourHundredNinetyOne.CircularUnitMatrix
import Mathlib.Tactic.NormNum.Prime

/-!
# Character coordinates at exponent 491

This module packages the p-dependent coordinate data shared by auxiliary
split primes at exponent `491`: the real cyclic generator, Fourier root,
source row and column permutations, and their checked square-coordinate
identities. It contains no auxiliary-prime phase or detector scalar.
-/

namespace Fermat.FourHundredNinetyOne.CircularUnitChannelCoordinates

noncomputable section

open Fermat.Irregular.AuxiliaryResidueChannels
open Fermat.FourHundredNinetyOne.CircularUnitCyclic
open Fermat.FourHundredNinetyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 491) := ⟨by norm_num⟩

/-- `4 = 2²` has exact order `245` modulo `491`. -/
theorem fourierRoot_isPrimitive : IsPrimitiveRoot (4 : ZMod 491) 245 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro q hq hqdiv
  have hfac : q ∣ 5 * (7 * 7) := by
    simpa using hqdiv
  have hcases : q = 5 ∨ q = 7 := by
    rcases (hq.dvd_mul).mp hfac with h5 | hrest
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by decide)).mp h5)
    rcases (hq.dvd_mul).mp hrest with h7 | h7
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by decide)).mp h7)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by decide)).mp h7)
  rcases hcases with rfl | rfl <;> decide

/-- Real Galois class `[245]·[2]^r`, represented modulo `491`. -/
def classExponent (r : Cyc) : ℕ :=
  ((245 : ZMod 491) * (2 : ZMod 491) ^ r.val).val

/-- All p-only real-character coordinates at exponent `491`. -/
def coordinates : ArithmeticCoordinates 491 (by norm_num) where
  generator := 2
  fourierRoot := 4
  fourierRoot_eq_generator_sq := by norm_num
  fourierRoot_isPrimitive := fourierRoot_isPrimitive
  column := columnPermutation
  column_square := by
    intro i
    decide +revert
  row := rowPermutation
  classExponent := classExponent
  classExponent_lt := by
    intro r
    exact ZMod.val_lt _
  classExponent_ne_zero := by
    intro r
    decide +revert
  classExponent_add_sq := by
    intro r s
    decide +revert
  row_square := by
    intro j
    decide +revert

end

end Fermat.FourHundredNinetyOne.CircularUnitChannelCoordinates
