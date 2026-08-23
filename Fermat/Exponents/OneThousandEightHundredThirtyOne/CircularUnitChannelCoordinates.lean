import Fermat.Descent.Irregular.CircularUnitResiduePresentation
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitEntryCoordinates

/-!
# Character coordinates at exponent 1831

This module packages the p-dependent coordinate data shared by every
auxiliary split prime: the real cyclic generator, Fourier root, source row and
column permutations, and their checked square-coordinate identities. It
contains no q-dependent phase or detector scalar.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitChannelCoordinates

noncomputable section

open Fermat.Irregular.AuxiliaryResidueChannels
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitEntryCertificate
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitMatrix

set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 1831) :=
  ⟨Fermat.OneThousandEightHundredThirtyOne.prime_1831⟩

/-- `9 = 3²` has exact order `915` modulo `1831`. -/
theorem fourierRoot_isPrimitive : IsPrimitiveRoot (9 : ZMod 1831) 915 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro q hq hqdiv
  have hfac : q ∣ 3 * (5 * 61) := by
    simpa using hqdiv
  have hcases : q = 3 ∨ q = 5 ∨ q = 61 := by
    rcases (hq.dvd_mul).mp hfac with h3 | hrest
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by decide)).mp h3)
    rcases (hq.dvd_mul).mp hrest with h5 | h61
    · exact Or.inr <| Or.inl
        ((Nat.prime_dvd_prime_iff_eq hq (by decide)).mp h5)
    · exact Or.inr <| Or.inr
        ((Nat.prime_dvd_prime_iff_eq hq (by decide)).mp h61)
  rcases hcases with rfl | rfl | rfl <;> decide

/-- All p-only real-class coordinates at exponent 1831. -/
def coordinates : ArithmeticCoordinates 1831 (by norm_num) where
  generator := 3
  fourierRoot := 9
  fourierRoot_eq_generator_sq := by norm_num
  fourierRoot_isPrimitive := fourierRoot_isPrimitive
  column := columnPermutation
  column_square := column_exponent_square_certificate
  row := rowPermutation
  classExponent := classExponent
  classExponent_lt := classExponent_lt
  classExponent_ne_zero := classExponent_ne_zero
  classExponent_add_sq := classExponent_add_sq
  row_square := row_exponent_square_certificate

/-- The sole possible irregular Bernoulli index `1274` is Kummer row `636`. -/
def irregularKummerRow : Fin 914 := 636

/-- Kummer row `636` means Bernoulli index `2 * (636 + 1) = 1274`. -/
theorem irregularKummerRow_bernoulliIndex :
    2 * KummerCriterion.CyclotomicUnits.kummerLogRowIndex
        (p := 1831) irregularKummerRow =
      1274 := by
  norm_num [irregularKummerRow,
    KummerCriterion.CyclotomicUnits.kummerLogRowIndex]

/-- Fourier coefficients omit frequency zero, so inverse character `278` is
stored at zero-based slot `277`. -/
theorem irregularKummerRow_frequency :
    coordinates.toCharacterCoordinates.frequency irregularKummerRow =
      (277 : Fin 914) := by
  rfl

end


end Fermat.OneThousandEightHundredThirtyOne.CircularUnitChannelCoordinates
