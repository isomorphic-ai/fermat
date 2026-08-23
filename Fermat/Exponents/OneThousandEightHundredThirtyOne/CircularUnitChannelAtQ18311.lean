import Fermat.Certificates.CaseII_1.CircularUnitIrregularChannel1831AtQ18311
import Fermat.Certificates.CaseII_1.CircularUnitResidueCertificate1831AtQ18311
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitChannelCoordinates

/-!
# The 1831 irregular channel at q = 18311

This q-specific adapter derives a cyclic presentation from the checked
residue certificate and transports the stored frequency-278 value `1165` to
the generic Kummer-channel factorization.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitChannelAtQ18311

noncomputable section

open Fermat.Irregular.AuxiliaryResidueChannels
open Fermat.Irregular.AuxiliaryResidueChannels.AutomaticPresentation
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitChannelCoordinates
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 1831) :=
  ⟨Fermat.OneThousandEightHundredThirtyOne.prime_1831⟩
local instance : Fact (Nat.Prime 18311) := ⟨by norm_num⟩

namespace QCertificate
abbrev certificate :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitResidueCertificate1831AtQ18311.certificate
end QCertificate

/-- The cyclic presentation reconstructed from the checked certificate. -/
def presentation := ofCertificate QCertificate.certificate coordinates

/-- Every Bernoulli row factors through its intrinsic Kummer channel. -/
def factorization (j : Fin 914) := presentation.factorization j

/-- The checked q=18311 phase presentation. -/
def storedPresentation : CyclicPresentation (by norm_num)
    QCertificate.certificate coordinates.toCharacterCoordinates where
  row := rowPermutation
  phase :=
    Fermat.OneThousandEightHundredThirtyOne.CircularUnitIrregularChannel1831AtQ18311.symbolPhase
  matrix_eq := rfl

def storedFactorization (j : Fin 914) := storedPresentation.factorization j

/-- The reconstructed and stored phases have the same nontrivial Fourier
scalar at every character. -/
theorem scalar_eq_stored (j : Fin 914) :
    (factorization j).scalar = (storedFactorization j).scalar :=
  CyclicPresentation.scalar_eq_of_row_eq presentation storedPresentation rfl j

/-- The checked frequency-278 receipt evaluates the irregular scalar to
`1165`. -/
theorem irregular_scalar_eq :
    (factorization irregularKummerRow).scalar = 1165 := by
  rw [scalar_eq_stored]
  change
    Fermat.OneThousandEightHundredThirtyOne.CircularUnitIrregularChannel1831AtQ18311.coefficient
      Fermat.OneThousandEightHundredThirtyOne.CircularUnitIrregularChannel1831AtQ18311.slot = 1165
  exact
    Fermat.OneThousandEightHundredThirtyOne.CircularUnitIrregularChannel1831AtQ18311.fhat_277_eq

end


end Fermat.OneThousandEightHundredThirtyOne.CircularUnitChannelAtQ18311
