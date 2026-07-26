import Fermat.KummerIso.FermatEquationSevenDBruteForce
import Fermat.ThirtySeven.CircularUnitResidues
import Fermat.FiftyNine.CircularUnitResidues
import Fermat.SixtySeven.CircularUnitResidues
import Fermat.OneHundredFiftySeven.CircularUnitResidues
import Fermat.FourHundredNinetyOne.CircularUnitResidues
import Fermat.FiveHundredEightySeven.CircularUnitResidues
import Fermat.SixHundredSeven.CircularUnitResidues
import Fermat.SixHundredNinetyOne.CircularUnitResidues
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitResidues

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

Consequently, the only project axioms in these FLT endpoints are the
temporary `BernoulliValidationBound` and termination of the generic
Sophie--Germain search.
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
  holdsAt_of_residueCertificate_canonical
    (by norm_num) residueCertificate37
    Fermat.ThirtySeven.CircularUnitCertificate.matrix_det_ne_zero

/-- FLT at exponent `59`, with equation (7d) supplied by the finite
`q = 827` circular-unit residue certificate. -/
theorem holdsAt_fiftyNine : Fermat.HoldsAt 59 :=
  holdsAt_of_residueCertificate_canonical
    (by norm_num)
    Fermat.FiftyNine.CircularUnitResidues.residueCertificate
    Fermat.FiftyNine.CircularUnitCertificate.matrix_det_ne_zero

/-- FLT at exponent `67`, with equation (7d) supplied by the finite
`q = 269` circular-unit residue certificate. -/
theorem holdsAt_sixtySeven : Fermat.HoldsAt 67 :=
  holdsAt_of_residueCertificate_canonical
    (by norm_num)
    Fermat.SixtySeven.CircularUnitResidues.certificate
    Fermat.SixtySeven.CircularUnitCertificate.matrix_det_ne_zero

/-- FLT at exponent `157`, with equation (7d) supplied by the finite
`q = 7537` circular-unit residue certificate. -/
theorem holdsAt_oneHundredFiftySeven : Fermat.HoldsAt 157 :=
  holdsAt_of_residueCertificate_canonical
    (by norm_num)
    Fermat.OneHundredFiftySeven.CircularUnitResidues.certificate
    Fermat.OneHundredFiftySeven.CircularUnitCertificate.matrix_det_ne_zero

/-- FLT at exponent `491`, with equation (7d) supplied by the finite
`q = 983` circular-unit residue certificate. -/
theorem holdsAt_fourHundredNinetyOne : Fermat.HoldsAt 491 :=
  holdsAt_of_residueCertificate_canonical
    (by norm_num)
    Fermat.FourHundredNinetyOne.CircularUnitResidues.certificate
    Fermat.FourHundredNinetyOne.CircularUnitCertificate.matrix_det_ne_zero

/-- FLT at exponent `587`, with equation (7d) supplied by the finite
`q = 8219` circular-unit residue certificate. -/
theorem holdsAt_fiveHundredEightySeven : Fermat.HoldsAt 587 :=
  holdsAt_of_residueCertificate_canonical
    (by norm_num)
    Fermat.FiveHundredEightySeven.CircularUnitResidues.certificate
    Fermat.FiveHundredEightySeven.CircularUnitCertificate.matrix_det_ne_zero

/-- FLT at exponent `607`, with equation (7d) supplied by the finite
`q = 20639` circular-unit residue certificate. -/
theorem holdsAt_sixHundredSeven : Fermat.HoldsAt 607 :=
  holdsAt_of_residueCertificate_canonical
    (by norm_num)
    Fermat.SixHundredSeven.CircularUnitResidues.certificate
    Fermat.SixHundredSeven.CircularUnitCertificate.matrix_det_ne_zero

/-- FLT at exponent `691`, with equation (7d) supplied by the finite
`q = 11057` circular-unit residue certificate. -/
theorem holdsAt_sixHundredNinetyOne : Fermat.HoldsAt 691 :=
  holdsAt_of_residueCertificate_canonical
    (by norm_num)
    Fermat.SixHundredNinetyOne.CircularUnitResidues.certificate
    Fermat.SixHundredNinetyOne.CircularUnitCertificate.matrix_det_ne_zero

/-- FLT at exponent `1381`, with equation (7d) supplied by the finite
`q = 38669` circular-unit residue certificate. -/
theorem holdsAt_oneThousandThreeHundredEightyOne :
    Fermat.HoldsAt 1381 :=
  holdsAt_of_residueCertificate_canonical
    (by norm_num)
    Fermat.OneThousandThreeHundredEightyOne.CircularUnitResidues.certificate
    Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate.matrix_det_ne_zero

end

end Fermat.KummerIso.ResidueRegressions
