import Fermat.Descent.KummerIso.FermatEquationSevenDBruteForce
import Fermat.Exponents.ThirtySeven.CircularUnitResidues
import Fermat.Exponents.FiftyNine.CircularUnitResidues
import Fermat.Exponents.SixtySeven.CircularUnitResidues
import Fermat.Exponents.OneHundredFiftySeven.CircularUnitResidues
import Fermat.Exponents.FourHundredNinetyOne.CircularUnitResidues
import Fermat.Exponents.FiveHundredEightySeven.CircularUnitResidues
import Fermat.Exponents.SixHundredSeven.CircularUnitResidues
import Fermat.Exponents.SixHundredNinetyOne.CircularUnitResidues
import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitResidues
import Fermat.Exponents.ThirtySeven.FirstCase
import Fermat.Exponents.FiftyNine.FirstCase
import Fermat.Exponents.SixtySeven.FirstCase
import Fermat.Exponents.OneHundredFiftySeven.FirstCase
import Fermat.Exponents.FourHundredNinetyOne.FirstCase
import Fermat.Exponents.FiveHundredEightySeven.FirstCase
import Fermat.Exponents.SixHundredSeven.FirstCase
import Fermat.Exponents.SixHundredNinetyOne.FirstCase
import Fermat.Exponents.OneThousandThreeHundredEightyOne.FirstCase
import Fermat.Exponents.ThirtySeven.GenericSecondCase
import Fermat.Exponents.FiftyNine.GenericSecondCase
import Fermat.Exponents.SixtySeven.GenericSecondCase
import Fermat.Exponents.OneHundredFiftySeven.GenericSecondCase
import Fermat.Exponents.FourHundredNinetyOne.GenericSecondCase
import Fermat.Exponents.FiveHundredEightySeven.GenericSecondCase
import Fermat.Exponents.SixHundredSeven.GenericSecondCase
import Fermat.Exponents.SixHundredNinetyOne.GenericSecondCase
import Fermat.Exponents.OneThousandThreeHundredEightyOne.GenericSecondCase

/-!
# Fixed-exponent regressions from circular-unit residue certificates

These are the closed end-to-end FLT endpoints that bypass the temporary
`FermatEquationSevenD` seam. Each theorem feeds a finite, kernel-checked
circular-unit residue certificate and its determinant proof into the
prime-generic historical equations-(7)--(10) reduction. The canonical
cyclotomic field and primitive root are chosen by the shared closure helper,
so none of the regression statements carries algebraic infrastructure.

Exponent `37` predates the generic residue-certificate structure. Its finite
root, matrix entries, and determinant were already checked; the small adapter
below merely packages those existing theorems in the generic interface.

Each endpoint also instantiates its already checked fixed second-case
certificate and reuses its `unitSystem` and `channels` fields. Together those
fields bypass both the generic Morishima hypothesis and the temporary
canonical derivative-source seam. Case I is supplied by each exponent's
explicit finite, checked Sophie--Germain certificate, rather than by the
generic search. Consequently, these nine FLT endpoints use no project axioms.
-/

namespace Fermat.KummerIso.ResidueRegressions

open Fermat.Irregular.CircularUnitFamily
open Fermat.KummerIso.FermatEquationSevenDBruteForce

noncomputable section

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 149) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 59) :=
  ⟨Fermat.FiftyNine.prime_59⟩
local instance : Fact (Nat.Prime 827) :=
  ⟨Fermat.FiftyNine.prime_827⟩
local instance : Fact (Nat.Prime 67) :=
  ⟨Fermat.SixtySeven.prime_67⟩
local instance : Fact (Nat.Prime 269) :=
  ⟨Fermat.SixtySeven.prime_269⟩
local instance : Fact (Nat.Prime 157) :=
  ⟨Fermat.OneHundredFiftySeven.prime_157⟩
local instance : Fact (Nat.Prime 7537) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 491) :=
  ⟨Fermat.FourHundredNinetyOne.prime_491⟩
local instance : Fact (Nat.Prime 983) :=
  ⟨Fermat.FourHundredNinetyOne.prime_983⟩
local instance : Fact (Nat.Prime 587) :=
  ⟨Fermat.FiveHundredEightySeven.prime_587⟩
local instance : Fact (Nat.Prime 8219) :=
  ⟨Fermat.FiveHundredEightySeven.prime_8219⟩
local instance : Fact (Nat.Prime 607) :=
  ⟨Fermat.SixHundredSeven.prime_607⟩
local instance : Fact (Nat.Prime 20639) :=
  ⟨Fermat.SixHundredSeven.prime_20639⟩
local instance : Fact (Nat.Prime 691) :=
  ⟨Fermat.SixHundredNinetyOne.prime_691⟩
local instance : Fact (Nat.Prime 11057) :=
  ⟨Fermat.SixHundredNinetyOne.prime_11057⟩
local instance : Fact (Nat.Prime 1381) :=
  ⟨Fermat.OneThousandThreeHundredEightyOne.prime_1381⟩
local instance : Fact (Nat.Prime 38669) :=
  ⟨Fermat.OneThousandThreeHundredEightyOne.prime_38669⟩

/-! ## Adapter for the original exponent-37 certificate -/

private theorem normalizationExponent37_agrees (i : Fin 17) :
    Fermat.ThirtySeven.CircularUnitResidues.normalizationExponent i =
      canonicalNormalizationExponent (p := 37) (i.val + 2) := by
  rw [show
    Fermat.ThirtySeven.CircularUnitResidues.normalizationExponent i =
      Fermat.Irregular.CircularUnitIndex.normalizationExponent37 i by rfl]
  exact
    Fermat.Irregular.CircularUnitIndex.normalizationExponent37_eq_canonical i

/-- The original `q = 149` computation at exponent `37`, repackaged in the
prime-generic residue-certificate structure. No finite arithmetic is assumed
again here: the root order, all matrix entries, and nonsingularity are the
existing kernel-checked theorems. -/
def residueCertificate37 :
    Fermat.Irregular.CircularUnitResidues.Certificate 37 149 where
  hp2 := by norm_num
  symbolExponent := 4
  q_sub_one := by norm_num
  root := 16
  root_isPrimitive :=
    IsPrimitiveRoot.iff_orderOf.mpr
      Fermat.ThirtySeven.CircularUnitResidues.root_order
  matrix := Fermat.ThirtySeven.CircularUnitCertificate.matrix
  entry_certificate := by
    intro j i
    simpa [Fermat.Irregular.CircularUnitResidues.normalizedUnitValue,
      Fermat.Irregular.CircularUnitResidues.embeddingRoot,
      Fermat.ThirtySeven.CircularUnitResidues.normalizedUnitValue,
      Fermat.ThirtySeven.CircularUnitResidues.embeddingRoot,
      Fermat.ThirtySeven.CircularUnitResidues.unitIndex,
      normalizationExponent37_agrees] using
      Fermat.ThirtySeven.CircularUnitResidues.matrix_entry_certificate j i

/-! ## Closed FLT endpoints -/

/-- FLT at exponent `37`, with equation (7d) supplied by the finite
`q = 149` circular-unit residue certificate. -/
theorem holdsAt_thirtySeven : Fermat.HoldsAt 37 :=
  Fermat.holdsAt_of_auxiliaryPrime_of_secondCaseExcluded
    (by norm_num) (by norm_num) (by norm_num)
    Fermat.ThirtySeven.noConsecutivePowers_37_149
    Fermat.ThirtySeven.exponentNotPower_37_149
    (secondCaseExcluded_of_residueCertificate_canonical_of_fixedCertificate
      (by norm_num) residueCertificate37
      Fermat.ThirtySeven.CircularUnitCertificate.matrix_det_ne_zero
      (fun hζ ↦
        Fermat.ThirtySeven.GenericSecondCase.fixedSecondCaseCertificate37 hζ))

/-- FLT at exponent `59`, with equation (7d) supplied by the finite
`q = 827` circular-unit residue certificate. -/
theorem holdsAt_fiftyNine : Fermat.HoldsAt 59 :=
  Fermat.holdsAt_of_auxiliaryPrime_of_secondCaseExcluded
    Fermat.FiftyNine.prime_59 (by norm_num)
    Fermat.FiftyNine.prime_827
    Fermat.FiftyNine.noConsecutivePowers_59_827
    Fermat.FiftyNine.exponentNotPower_59_827
    (secondCaseExcluded_of_residueCertificate_canonical_of_fixedCertificate
      (by norm_num)
      Fermat.FiftyNine.CircularUnitResidues.residueCertificate
      Fermat.FiftyNine.CircularUnitCertificate.matrix_det_ne_zero
      (fun hζ ↦
        Fermat.FiftyNine.GenericSecondCase.fixedSecondCaseCertificate59 hζ))

/-- FLT at exponent `67`, with equation (7d) supplied by the finite
`q = 269` circular-unit residue certificate. -/
theorem holdsAt_sixtySeven : Fermat.HoldsAt 67 :=
  Fermat.holdsAt_of_auxiliaryPrime_of_secondCaseExcluded
    Fermat.SixtySeven.prime_67 (by norm_num)
    Fermat.SixtySeven.prime_269
    Fermat.SixtySeven.noConsecutivePowers_67_269
    Fermat.SixtySeven.exponentNotPower_67_269
    (secondCaseExcluded_of_residueCertificate_canonical_of_fixedCertificate
      (by norm_num)
      Fermat.SixtySeven.CircularUnitResidues.certificate
      Fermat.SixtySeven.CircularUnitCertificate.matrix_det_ne_zero
      (fun hζ ↦
        Fermat.SixtySeven.GenericSecondCase.fixedSecondCaseCertificate67 hζ))

/-- FLT at exponent `157`, with equation (7d) supplied by the finite
`q = 7537` circular-unit residue certificate. -/
theorem holdsAt_oneHundredFiftySeven : Fermat.HoldsAt 157 :=
  Fermat.holdsAt_of_auxiliaryPrime_of_secondCaseExcluded
    Fermat.OneHundredFiftySeven.prime_157 (by norm_num)
    Fermat.OneHundredFiftySeven.prime_1571
    Fermat.OneHundredFiftySeven.noConsecutivePowers_157_1571
    Fermat.OneHundredFiftySeven.exponentNotPower_157_1571
    (secondCaseExcluded_of_residueCertificate_canonical_of_fixedCertificate
      (by norm_num)
      Fermat.OneHundredFiftySeven.CircularUnitResidues.certificate
      Fermat.OneHundredFiftySeven.CircularUnitCertificate.matrix_det_ne_zero
      (fun hζ ↦
        Fermat.OneHundredFiftySeven.GenericSecondCase.fixedSecondCaseCertificate157
          hζ))

/-- FLT at exponent `491`, with equation (7d) supplied by the finite
`q = 983` circular-unit residue certificate. -/
theorem holdsAt_fourHundredNinetyOne : Fermat.HoldsAt 491 :=
  Fermat.holdsAt_of_auxiliaryPrime_of_secondCaseExcluded
    Fermat.FourHundredNinetyOne.prime_491 (by norm_num)
    Fermat.FourHundredNinetyOne.prime_983
    Fermat.FourHundredNinetyOne.noConsecutivePowers_491_983
    Fermat.FourHundredNinetyOne.exponentNotPower_491_983
    (secondCaseExcluded_of_residueCertificate_canonical_of_fixedCertificate
      (by norm_num)
      Fermat.FourHundredNinetyOne.CircularUnitResidues.certificate
      Fermat.FourHundredNinetyOne.CircularUnitCertificate.matrix_det_ne_zero
      (fun hζ ↦
        Fermat.FourHundredNinetyOne.GenericSecondCase.fixedSecondCaseCertificate491
          hζ))

/-- FLT at exponent `587`, with equation (7d) supplied by the finite
`q = 8219` circular-unit residue certificate. -/
theorem holdsAt_fiveHundredEightySeven : Fermat.HoldsAt 587 :=
  Fermat.holdsAt_of_auxiliaryPrime_of_secondCaseExcluded
    Fermat.FiveHundredEightySeven.prime_587 (by norm_num)
    Fermat.FiveHundredEightySeven.prime_8219
    Fermat.FiveHundredEightySeven.noConsecutivePowers_587_8219
    Fermat.FiveHundredEightySeven.exponentNotPower_587_8219
    (secondCaseExcluded_of_residueCertificate_canonical_of_fixedCertificate
      (by norm_num)
      Fermat.FiveHundredEightySeven.CircularUnitResidues.certificate
      Fermat.FiveHundredEightySeven.CircularUnitCertificate.matrix_det_ne_zero
      (fun hζ ↦
        Fermat.FiveHundredEightySeven.GenericSecondCase.fixedSecondCaseCertificate587
          hζ))

/-- FLT at exponent `607`, with equation (7d) supplied by the finite
`q = 20639` circular-unit residue certificate. -/
theorem holdsAt_sixHundredSeven : Fermat.HoldsAt 607 :=
  Fermat.holdsAt_of_auxiliaryPrime_of_secondCaseExcluded
    Fermat.SixHundredSeven.prime_607 (by norm_num)
    Fermat.SixHundredSeven.prime_20639
    Fermat.SixHundredSeven.noConsecutivePowers_607_20639
    Fermat.SixHundredSeven.exponentNotPower_607_20639
    (secondCaseExcluded_of_residueCertificate_canonical_of_fixedCertificate
      (by norm_num)
      Fermat.SixHundredSeven.CircularUnitResidues.certificate
      Fermat.SixHundredSeven.CircularUnitCertificate.matrix_det_ne_zero
      (fun hζ ↦
        Fermat.SixHundredSeven.GenericSecondCase.fixedSecondCaseCertificate607
          hζ))

/-- FLT at exponent `691`, with equation (7d) supplied by the finite
`q = 11057` circular-unit residue certificate. -/
theorem holdsAt_sixHundredNinetyOne : Fermat.HoldsAt 691 :=
  Fermat.holdsAt_of_auxiliaryPrime_of_secondCaseExcluded
    Fermat.SixHundredNinetyOne.prime_691 (by norm_num)
    Fermat.SixHundredNinetyOne.prime_11057
    Fermat.SixHundredNinetyOne.noConsecutivePowers_691_11057
    Fermat.SixHundredNinetyOne.exponentNotPower_691_11057
    (secondCaseExcluded_of_residueCertificate_canonical_of_fixedCertificate
      (by norm_num)
      Fermat.SixHundredNinetyOne.CircularUnitResidues.certificate
      Fermat.SixHundredNinetyOne.CircularUnitCertificate.matrix_det_ne_zero
      (fun hζ ↦
        Fermat.SixHundredNinetyOne.GenericSecondCase.fixedSecondCaseCertificate691
          hζ))

/-- FLT at exponent `1381`, with equation (7d) supplied by the finite
`q = 38669` circular-unit residue certificate. -/
theorem holdsAt_oneThousandThreeHundredEightyOne :
    Fermat.HoldsAt 1381 :=
  Fermat.holdsAt_of_auxiliaryPrime_of_secondCaseExcluded
    Fermat.OneThousandThreeHundredEightyOne.prime_1381 (by norm_num)
    Fermat.OneThousandThreeHundredEightyOne.prime_38669
    Fermat.OneThousandThreeHundredEightyOne.noConsecutivePowers_1381_38669
    Fermat.OneThousandThreeHundredEightyOne.exponentNotPower_1381_38669
    (secondCaseExcluded_of_residueCertificate_canonical_of_fixedCertificate
      (by norm_num)
      Fermat.OneThousandThreeHundredEightyOne.CircularUnitResidues.certificate
      Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate.matrix_det_ne_zero
      (fun hζ ↦
        Fermat.OneThousandThreeHundredEightyOne.GenericSecondCase.fixedSecondCaseCertificate1381
          hζ))

end

end Fermat.KummerIso.ResidueRegressions
