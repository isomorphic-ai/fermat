import Fermat.Certificates.CaseII_1.CircularUnitIrregularChannel1831
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitChannelCoordinates
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitResiduesBase

/-!
# The 1831 irregular channel at q = 358877

This q-specific adapter derives a cyclic presentation from the checked
residue certificate and transports the stored frequency-278 value `882` to
the generic Kummer-channel factorization.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitChannelAtQ358877

noncomputable section

open Fermat.Irregular.AuxiliaryResidueChannels
open Fermat.Irregular.AuxiliaryResidueChannels.AutomaticPresentation
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitChannelCoordinates
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 1831) :=
  ⟨Fermat.OneThousandEightHundredThirtyOne.prime_1831⟩
local instance : Fact (Nat.Prime 358877) :=
  ⟨Fermat.OneThousandEightHundredThirtyOne.prime_358877⟩

namespace QCertificate
abbrev certificate :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitResidues.certificate
end QCertificate

/-- The cyclic presentation reconstructed from the checked certificate. -/
def presentation := ofCertificate QCertificate.certificate coordinates

/-- Every Bernoulli row factors through its intrinsic Kummer channel. -/
def factorization (j : Fin 914) := presentation.factorization j

/-- The original checked phase presentation. -/
def storedPresentation : CyclicPresentation (by norm_num)
    QCertificate.certificate coordinates.toCharacterCoordinates where
  row := rowPermutation
  phase := symbolPhase
  matrix_eq := rfl

def storedFactorization (j : Fin 914) := storedPresentation.factorization j

/-- The reconstructed and stored phases have the same nontrivial Fourier
scalar at every character. -/
theorem scalar_eq_stored (j : Fin 914) :
    (factorization j).scalar = (storedFactorization j).scalar :=
  CyclicPresentation.scalar_eq_of_row_eq presentation storedPresentation rfl j

/-- The checked frequency-278 receipt evaluates the irregular scalar to
`882`. -/
theorem irregular_scalar_eq :
    (factorization irregularKummerRow).scalar = 882 := by
  rw [scalar_eq_stored]
  change
    Fermat.OneThousandEightHundredThirtyOne.CircularUnitIrregularChannel.coefficient
      Fermat.OneThousandEightHundredThirtyOne.CircularUnitIrregularChannel.slot = 882
  exact
    Fermat.OneThousandEightHundredThirtyOne.CircularUnitIrregularChannel.fhat_277_eq

end


end Fermat.OneThousandEightHundredThirtyOne.CircularUnitChannelAtQ358877
