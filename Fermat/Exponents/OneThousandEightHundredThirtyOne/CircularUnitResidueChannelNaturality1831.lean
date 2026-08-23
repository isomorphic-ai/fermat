import Fermat.Descent.Irregular.AuxiliaryResidueCharacterNaturality
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitResiduesChannels
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitResiduesChannels18311

/-!
# Auxiliary-prime naturality of the 1831 irregular channel

The split primes `358877 = 196 * 1831 + 1` and
`18311 = 10 * 1831 + 1` produce different residue matrices and different
Fourier scalars. The generic theorem proves that every checked auxiliary-prime
certificate factors through an intrinsic Kummer character channel. Here both
receipts specialize to row `636`, hence Bernoulli index `1274` and inverse
Fourier frequency `278` (stored at zero-based slot `277`).

For the stored cyclic conventions the scalars are `882` and `1165`, with
`1165 = 1195 * 882 mod 1831`. Therefore the selected detectors are associates
and have exactly the same kernel. The q=18311 full matrix is nevertheless
singular, showing that characterwise equivalence is strictly weaker than
full-matrix equivalence.
-/

open scoped Matrix

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitResidueChannelNaturality1831

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Fermat.Irregular.AuxiliaryResidueChannels
open Fermat.Irregular.CircularUnitResidues
open Fermat.Irregular.CyclicDifferenceMatrix
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitChannelCoordinates
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitCyclic
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitMatrix

local instance : Fact (Nat.Prime 1831) :=
  ⟨Fermat.OneThousandEightHundredThirtyOne.prime_1831⟩
local instance : Fact (Nat.Prime 358877) :=
  ⟨Fermat.OneThousandEightHundredThirtyOne.prime_358877⟩
local instance : Fact (Nat.Prime 18311) := ⟨by norm_num⟩
local instance : Fact (2 < 1831) := ⟨by norm_num⟩

namespace OldResidues
abbrev certificate :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitResidues.certificate
end OldResidues

namespace NewResidues
abbrev certificate :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitResidueCertificate1831AtQ18311.certificate
abbrev matrix := certificate.matrix
end NewResidues

namespace NewPhase
abbrev symbolPhase :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitIrregularChannel1831AtQ18311.symbolPhase
abbrev regularZeroSlot :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitIrregularChannel1831AtQ18311.regularZeroSlot
abbrev fourierRoot_isPrimitive :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitIrregularChannel1831AtQ18311.fourierRoot_isPrimitive
abbrev fhat_635_eq_zero :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitIrregularChannel1831AtQ18311.fhat_635_eq_zero
end NewPhase

namespace OldChannel
abbrev factorization :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitChannelAtQ358877.factorization
    irregularKummerRow
abbrev scalar_eq :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitChannelAtQ358877.irregular_scalar_eq
end OldChannel

namespace NewAdapter
abbrev factorization :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitChannelAtQ18311.factorization
    irregularKummerRow
abbrev scalar_eq :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitChannelAtQ18311.irregular_scalar_eq
end NewAdapter

/-- The original q=358877 detector, packaged through the intrinsic row. -/
def q358877Factorization := OldChannel.factorization

/-- The original auxiliary scalar is `882`. -/
theorem q358877_scalar_eq : q358877Factorization.scalar = 882 :=
  OldChannel.scalar_eq

/-- The original auxiliary scalar is nonzero. -/
theorem q358877_scalar_ne_zero : q358877Factorization.scalar ≠ 0 := by
  rw [q358877_scalar_eq]
  decide

/-- The new auxiliary scalar is `1165`. -/
theorem q18311_scalar_eq : NewAdapter.factorization.scalar = 1165 :=
  NewAdapter.scalar_eq

/-- The new auxiliary scalar is nonzero. -/
theorem q18311_scalar_ne_zero : NewAdapter.factorization.scalar ≠ 0 := by
  rw [q18311_scalar_eq]
  decide

/-- The intrinsic projection selected by Bernoulli index `1274`. -/
def projection (e : Fin 914 → ZMod 1831) : ZMod 1831 :=
  canonicalKummerChannel 1831 (by norm_num) irregularKummerRow e

/-- The indexing statement linking the intrinsic row to Bernoulli `1274`. -/
theorem projection_bernoulliIndex :
    2 * KummerCriterion.CyclotomicUnits.kummerLogRowIndex
        (p := 1831) irregularKummerRow =
      1274 :=
  irregularKummerRow_bernoulliIndex

/-- The same row is inverse Fourier frequency `278`, stored at slot `277`. -/
theorem projection_frequency :
    coordinates.toCharacterCoordinates.frequency irregularKummerRow =
      (277 : Fin 914) :=
  irregularKummerRow_frequency

/-- Coordinate-free factorization of the old auxiliary-prime certificate. -/
def q358877UniversalFactorization :=
  OldResidues.certificate.canonicalBasisFreeFactorization
    (by norm_num) irregularKummerRow

/-- Coordinate-free factorization of the new auxiliary-prime certificate. -/
def q18311UniversalFactorization :=
  NewResidues.certificate.canonicalBasisFreeFactorization
    (by norm_num) irregularKummerRow

/-- The universal construction already shows, without cyclic coordinates,
that both auxiliary primes select the same intrinsic channel. -/
theorem universal_detector_cross_mul (e : Fin 914 → ZMod 1831) :
    q18311UniversalFactorization.scalar *
        q358877UniversalFactorization.residueDetector e =
      q358877UniversalFactorization.scalar *
        q18311UniversalFactorization.residueDetector e :=
  Factorization.cross_mul_residueDetectors
    q358877UniversalFactorization q18311UniversalFactorization e

/-- The stored q=358877 cyclic detector and its basis-free reconstruction
are projectively the same functional. -/
theorem q358877_coordinate_free_cross_mul (e : Fin 914 → ZMod 1831) :
    q358877UniversalFactorization.scalar *
        q358877Factorization.residueDetector e =
      q358877Factorization.scalar *
        q358877UniversalFactorization.residueDetector e :=
  Factorization.cross_mul_residueDetectors
    q358877Factorization q358877UniversalFactorization e

/-- The stored q=18311 cyclic detector and its basis-free reconstruction
are projectively the same functional. -/
theorem q18311_coordinate_free_cross_mul (e : Fin 914 → ZMod 1831) :
    q18311UniversalFactorization.scalar *
        NewAdapter.factorization.residueDetector e =
      NewAdapter.factorization.scalar *
        q18311UniversalFactorization.residueDetector e :=
  Factorization.cross_mul_residueDetectors
    NewAdapter.factorization q18311UniversalFactorization e

/-- The old cyclic detector factors as `882 * projection`. -/
theorem q358877_detector_eq_scalar_mul_projection
    (e : Fin 914 → ZMod 1831) :
    q358877Factorization.residueDetector e =
      882 * projection e := by
  simpa only [projection, q358877_scalar_eq] using
    q358877Factorization.residueDetector_eq_scalar_mul_canonical e

/-- The new cyclic detector factors as `1165 * projection`. -/
theorem q18311_detector_eq_scalar_mul_projection
    (e : Fin 914 → ZMod 1831) :
    NewAdapter.factorization.residueDetector e =
      1165 * projection e := by
  simpa only [projection, q18311_scalar_eq] using
    NewAdapter.factorization.residueDetector_eq_scalar_mul_canonical e

/-- Projective naturality for the two concrete cyclic detectors. -/
theorem detector_cross_mul (e : Fin 914 → ZMod 1831) :
    NewAdapter.factorization.scalar *
        q358877Factorization.residueDetector e =
      q358877Factorization.scalar *
        NewAdapter.factorization.residueDetector e :=
  Factorization.cross_mul_residueDetectors
    q358877Factorization NewAdapter.factorization e

/-- With the checked root conventions, the q=18311 detector is the nonzero
scalar `1195` times the q=358877 detector. -/
theorem q18311_detector_eq_scale_q358877 (e : Fin 914 → ZMod 1831) :
    NewAdapter.factorization.residueDetector e =
      1195 * q358877Factorization.residueDetector e := by
  rw [q18311_detector_eq_scalar_mul_projection,
    q358877_detector_eq_scalar_mul_projection]
  have hscale : (1165 : ZMod 1831) = 1195 * 882 := by decide
  rw [hscale]
  ring

/-- The two selected residue detectors have exactly the same zero locus. -/
theorem detectors_equivalent (e : Fin 914 → ZMod 1831) :
    q358877Factorization.residueDetector e = 0 ↔
      NewAdapter.factorization.residueDetector e = 0 :=
  Factorization.detectors_equivalent
    q358877Factorization NewAdapter.factorization
    q358877_scalar_ne_zero q18311_scalar_ne_zero e

/-- The q=18311 reduced difference matrix is singular at the unrelated
regular frequency `636`. -/
theorem q18311_differenceMatrix_det_eq_zero :
    (differenceMatrix NewPhase.symbolPhase).det = 0 := by
  by_contra hdet
  have hcoeff :=
    (differenceMatrix_det_ne_zero_iff_fourierCoeff
      (9 : ZMod 1831) NewPhase.fourierRoot_isPrimitive
        NewPhase.symbolPhase).mp hdet
  exact (hcoeff NewPhase.regularZeroSlot) NewPhase.fhat_635_eq_zero

/-- Consequently the actual source-order q=18311 residue matrix is singular,
even though its irregular detector is nonzero. -/
theorem q18311_matrix_det_eq_zero : NewResidues.matrix.det = 0 := by
  change (Matrix.reindex rowPermutation.symm columnPermutation.symm
    (differenceMatrix NewPhase.symbolPhase)).det = 0
  rw [Matrix.det_reindex, q18311_differenceMatrix_det_eq_zero, mul_zero]

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitResidueChannelNaturality1831
