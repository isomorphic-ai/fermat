import Fermat.Exponents.FourHundredNinetyOne.CircularUnitChannelCoordinates
import Fermat.Exponents.FourHundredNinetyOne.CircularUnitEntryCertificate

/-!
# Three selective Case-II.1 channels for p = 491, q = 983

The existing authenticated `q = 983` phase is reused without importing the
historical full-determinant certificate. Its three Fourier coefficients at
the inverse characters reflected from Bernoulli indices `292`, `336`, and
`338` are checked directly. The q-dependent values are respectively
`467`, `92`, and `373` modulo `491`.
-/

namespace Fermat.FourHundredNinetyOne.CircularUnitIrregularChannels491AtQ983

noncomputable section

open Fermat.Irregular.AuxiliaryResidueChannels
open Fermat.Irregular.AuxiliaryResidueChannels.AutomaticPresentation
open Fermat.Irregular.CircularUnitResidues
open Fermat.FourHundredNinetyOne.CircularUnitChannelCoordinates
open Fermat.FourHundredNinetyOne.CircularUnitEntryCertificate
open Fermat.FourHundredNinetyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 491) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 983) := ⟨by norm_num⟩

namespace QCertificate

/-- A determinant-free copy of the authenticated `q = 983` residue
certificate. The new route consumes its entries but no matrix inverse. -/
def certificate : Certificate 491 983 where
  hp2 := by norm_num
  symbolExponent := 2
  q_sub_one := by norm_num
  root := 2
  root_isPrimitive := root_isPrimitive
  matrix := matrix
  entry_certificate := by
    intro j i
    exact matrix_entry_certificate j i

end QCertificate

/-- The reconstructed cyclic presentation of the checked residue matrix. -/
def presentation := ofCertificate QCertificate.certificate coordinates

/-- Every Bernoulli row factors through its intrinsic Kummer channel. -/
def factorization (j : Fin 244) := presentation.factorization j

/-- The original stored phase, presented in the same p-only coordinates. -/
def storedPresentation : CyclicPresentation (by norm_num)
    QCertificate.certificate coordinates.toCharacterCoordinates where
  row := rowPermutation
  phase := symbolPhase
  matrix_eq := rfl

def storedFactorization (j : Fin 244) := storedPresentation.factorization j

/-- The reconstructed and stored phases have the same nontrivial Fourier
scalar at every character. -/
theorem scalar_eq_stored (j : Fin 244) :
    (factorization j).scalar = (storedFactorization j).scalar :=
  CyclicPresentation.scalar_eq_of_row_eq
    presentation storedPresentation rfl j

/-- Nontrivial Fourier slot `k` denotes actual frequency `k + 1`. -/
abbrev coefficient (k : Fin 244) : ZMod 491 :=
  Fermat.Irregular.CyclicDifferenceMatrix.fourierCoeff
    (4 : ZMod 491) fourierRoot_isPrimitive.pow_eq_one symbolPhase k

/-- Bernoulli index `292`, Kummer row `145`, has actual frequency `99`. -/
def row292 : Fin 244 := 145
def slot292 : Fin 244 := 98

/-- Bernoulli index `336`, Kummer row `167`, has actual frequency `77`. -/
def row336 : Fin 244 := 167
def slot336 : Fin 244 := 76

/-- Bernoulli index `338`, Kummer row `168`, has actual frequency `76`. -/
def row338 : Fin 244 := 168
def slot338 : Fin 244 := 75

@[simp] theorem frequency_row292 :
    coordinates.toCharacterCoordinates.frequency row292 = slot292 := rfl

@[simp] theorem frequency_row336 :
    coordinates.toCharacterCoordinates.frequency row336 = slot336 := rfl

@[simp] theorem frequency_row338 :
    coordinates.toCharacterCoordinates.frequency row338 = slot338 := rfl

/-- The detector at actual frequency `99` is `467`. -/
theorem coefficient_slot292_eq : coefficient slot292 = 467 := by
  decide

/-- The detector at actual frequency `77` is `92`. -/
theorem coefficient_slot336_eq : coefficient slot336 = 92 := by
  decide

/-- The detector at actual frequency `76` is `373`. -/
theorem coefficient_slot338_eq : coefficient slot338 = 373 := by
  decide

/-- The q-dependent scalar on Bernoulli channel `292` is `467`. -/
theorem scalar_row292_eq : (factorization row292).scalar = 467 := by
  rw [scalar_eq_stored]
  change coefficient slot292 = 467
  exact coefficient_slot292_eq

/-- The q-dependent scalar on Bernoulli channel `336` is `92`. -/
theorem scalar_row336_eq : (factorization row336).scalar = 92 := by
  rw [scalar_eq_stored]
  change coefficient slot336 = 92
  exact coefficient_slot336_eq

/-- The q-dependent scalar on Bernoulli channel `338` is `373`. -/
theorem scalar_row338_eq : (factorization row338).scalar = 373 := by
  rw [scalar_eq_stored]
  change coefficient slot338 = 373
  exact coefficient_slot338_eq

end

end Fermat.FourHundredNinetyOne.CircularUnitIrregularChannels491AtQ983
