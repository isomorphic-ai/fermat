import Fermat.Certificates.CaseII_1.CircularUnitIrregularChannels157AtQ7537
import Fermat.Exponents.OneHundredFiftySeven.CircularUnitResiduesBase

/-!
# The exponent-157 irregular channels at q = 7537

This adapter reconstructs the canonical cyclic presentation from the
authenticated residue certificate and transports the two selected stored
Fourier values to generic Kummer-channel factorizations.
-/

namespace Fermat.OneHundredFiftySeven.CircularUnitChannelAtQ7537

noncomputable section

open Fermat.Irregular.AuxiliaryResidueChannels
open Fermat.Irregular.AuxiliaryResidueChannels.AutomaticPresentation
open Fermat.Irregular.CyclicDifferenceMatrix
open Fermat.OneHundredFiftySeven.CircularUnitChannelCoordinates
open Fermat.OneHundredFiftySeven.CircularUnitIrregularChannels157AtQ7537
open Fermat.OneHundredFiftySeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 157) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 7537) := ⟨by norm_num⟩

namespace QCertificate

abbrev certificate :=
  Fermat.OneHundredFiftySeven.CircularUnitResiduesBase.certificate

end QCertificate

/-- The cyclic presentation reconstructed from the authenticated finite-field
certificate. -/
def presentation := ofCertificate QCertificate.certificate coordinates

/-- Every Bernoulli row factors through its intrinsic Kummer channel. -/
def factorization (j : Fin 77) := presentation.factorization j

/-- The checked stored phase presentation. -/
def storedPresentation : CyclicPresentation (by norm_num)
    QCertificate.certificate coordinates.toCharacterCoordinates where
  row := rowPermutation
  phase := symbolPhase
  matrix_eq := by
    ext j i
    simp only [QCertificate.certificate,
      Fermat.OneHundredFiftySeven.CircularUnitResiduesBase.certificate,
      Matrix.reindex_apply, Matrix.submatrix_apply, differenceMatrix]
    exact matrix_entry_eq_phase j i

def storedFactorization (j : Fin 77) := storedPresentation.factorization j

/-- The reconstructed and stored phases have identical nontrivial Fourier
scalars. -/
theorem scalar_eq_stored (j : Fin 77) :
    (factorization j).scalar = (storedFactorization j).scalar :=
  CyclicPresentation.scalar_eq_of_row_eq presentation storedPresentation rfl j

/-- Transported scalar for the `B_62` Kummer row. -/
theorem sixtyTwo_scalar_eq :
    (factorization rowSixtyTwo).scalar = 5 := by
  rw [scalar_eq_stored]
  exact coefficient_sixtyTwo_eq

/-- Transported scalar for the `B_110` Kummer row. -/
theorem oneHundredTen_scalar_eq :
    (factorization rowOneHundredTen).scalar = 104 := by
  rw [scalar_eq_stored]
  exact coefficient_oneHundredTen_eq

end


end Fermat.OneHundredFiftySeven.CircularUnitChannelAtQ7537
