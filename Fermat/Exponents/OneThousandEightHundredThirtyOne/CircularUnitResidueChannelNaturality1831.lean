import Fermat.Descent.Irregular.AuxiliaryResidueChannels
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitResiduesChannels
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitResiduesChannels18311

/-!
# Auxiliary-prime naturality of the 1831 irregular channel

The split primes `358877 = 196 * 1831 + 1` and
`18311 = 10 * 1831 + 1` produce different residue matrices and different
Fourier scalars. This file proves that their selected residue functionals
factor through the same canonical Kummer row `636`, hence through the same
Bernoulli character `1274`.

The scalars are `882` and `1165`, with `1165 = 1195 * 882 mod 1831`.
Therefore the two selected detectors are associates and have exactly the same
kernel. The q=18311 full matrix is singular, demonstrating that this
characterwise equivalence is strictly weaker than full-matrix equivalence.
-/

open scoped Matrix

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitResidueChannelNaturality1831

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Fermat.Irregular.AuxiliaryResidueChannels
open Fermat.Irregular.CyclicDifferenceMatrix
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitCyclic
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitMatrix
open KummerCriterion.CyclotomicUnits

namespace OldChannel
abbrev coefficient :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitIrregularChannel.coefficient
abbrev slot :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitIrregularChannel.slot
abbrev fourierRoot_isPrimitive :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitIrregularChannel.fourierRoot_isPrimitive
abbrev fhat_277_eq :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitIrregularChannel.fhat_277_eq
abbrev fhat_277_ne_zero :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitIrregularChannel.fhat_277_ne_zero
end OldChannel

namespace OldResidues
abbrev certificate :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitResidues.certificate
end OldResidues

namespace OldAdapter
abbrev irregularKummerRow :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitResiduesChannels.irregularKummerRow
abbrev inverseMoment_entry_eq_vandermonde :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitResiduesChannels.inverseMoment_entry_eq_vandermonde
end OldAdapter

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

namespace NewResidues
abbrev matrix :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitResidueCertificate1831AtQ18311.matrix
end NewResidues

namespace NewAdapter
abbrev factorization :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitResiduesChannels18311.factorization
abbrev factorization_scalar_ne_zero :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitResiduesChannels18311.factorization_scalar_ne_zero
end NewAdapter

local instance : Fact (Nat.Prime 1831) := ⟨by decide⟩
local instance : Fact (Nat.Prime 358877) :=
  ⟨Fermat.OneThousandEightHundredThirtyOne.prime_358877⟩
local instance : Fact (Nat.Prime 18311) := ⟨by norm_num⟩

/-- The original q=358877 detector, packaged as an exact factorization
through the canonical Kummer row `636`. -/
def q358877Factorization :
    Factorization 1831 358877 (by norm_num) OldResidues.certificate
      OldAdapter.irregularKummerRow where
  weights := fun sourceRow ↦
    positiveMomentMatrix (9 : ZMod 1831)
      OldChannel.fourierRoot_isPrimitive.pow_eq_one OldChannel.slot
        (rowPermutation sourceRow)
  scalar := OldChannel.coefficient OldChannel.slot
  factors := by
    intro e
    exact cyclic_reindexed_factorization
      rowPermutation columnPermutation matrix symbolPhase rfl
      (9 : ZMod 1831) OldChannel.fourierRoot_isPrimitive OldChannel.slot
      (fun i ↦
        vandermondeTeichmullerEvenSubOneMatrix (p := 1831) (by norm_num)
          OldAdapter.irregularKummerRow i)
      OldAdapter.inverseMoment_entry_eq_vandermonde e

/-- The original auxiliary scalar is `882`. -/
theorem q358877_scalar_eq : q358877Factorization.scalar = 882 :=
  OldChannel.fhat_277_eq

/-- The original auxiliary scalar is nonzero. -/
theorem q358877_scalar_ne_zero : q358877Factorization.scalar ≠ 0 :=
  OldChannel.fhat_277_ne_zero

/-- The new auxiliary scalar is `1165`. -/
theorem q18311_scalar_eq : NewAdapter.factorization.scalar = 1165 :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitIrregularChannel1831AtQ18311.fhat_277_eq

/-- Projective naturality: both auxiliary-prime functionals factor through
the same canonical Bernoulli/Kummer row. -/
theorem detector_cross_mul (e : Fin 914 → ZMod 1831) :
    NewAdapter.factorization.scalar * q358877Factorization.residueDetector e =
      q358877Factorization.scalar * NewAdapter.factorization.residueDetector e :=
  Factorization.cross_mul_residueDetectors
    q358877Factorization NewAdapter.factorization e

/-- With the concrete root conventions, the q=18311 detector is the nonzero
scalar `1195` times the q=358877 detector. -/
theorem q18311_detector_eq_scale_q358877 (e : Fin 914 → ZMod 1831) :
    NewAdapter.factorization.residueDetector e =
      1195 * q358877Factorization.residueDetector e := by
  rw [NewAdapter.factorization.residueDetector_eq_scalar_mul_canonical,
    q358877Factorization.residueDetector_eq_scalar_mul_canonical,
    q18311_scalar_eq, q358877_scalar_eq]
  change (1165 : ZMod 1831) *
      canonicalKummerChannel 1831 (by norm_num) (636 : Fin 914) e =
    1195 * ((882 : ZMod 1831) *
      canonicalKummerChannel 1831 (by norm_num) (636 : Fin 914) e)
  have hscale : (1165 : ZMod 1831) = 1195 * 882 := by decide
  rw [hscale]
  ring

/-- The two selected residue detectors have exactly the same zero locus. -/
theorem detectors_equivalent (e : Fin 914 → ZMod 1831) :
    q358877Factorization.residueDetector e = 0 ↔
      NewAdapter.factorization.residueDetector e = 0 :=
  Factorization.detectors_equivalent
    q358877Factorization NewAdapter.factorization
      q358877_scalar_ne_zero NewAdapter.factorization_scalar_ne_zero e

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
