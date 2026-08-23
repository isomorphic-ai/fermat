import Fermat.Certificates.CaseII_1.IrregularSupport1831
import Fermat.Descent.Irregular.SelectiveCircularUnitResidues
import Fermat.Descent.Irregular.SelectiveKummerSaturation
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitChannelAtQ358877

/-!
# Selective circular-unit residue route at exponent 1831

This is the determinant-free Case-II.1 route at `q = 358877`. The generic
auxiliary-prime constructor factors its residue detector through Kummer row
`636`, which is Bernoulli index `1274` and inverse Fourier frequency `278`.
The standalone receipt checks only that scalar, with value `882 ≠ 0`.

Every regular row is discharged by Kummer's logarithm matrix. Thus the proof
uses one numerical Fourier coefficient rather than nonsingularity of the full
`914 × 914` residue matrix.
-/

open scoped Matrix NumberField

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitResiduesChannels

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Fermat.Irregular.AuxiliaryResidueChannels
open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.SelectiveCircularUnitResidues
open Fermat.Irregular.SelectiveKummerSaturation
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitChannelCoordinates
open Fermat.OneThousandEightHundredThirtyOne.IrregularSupport
open KummerCriterion
open KummerCriterion.CyclotomicUnits

local instance : Fact (Nat.Prime 1831) :=
  ⟨Fermat.OneThousandEightHundredThirtyOne.prime_1831⟩
local instance : Fact (Nat.Prime 358877) :=
  ⟨Fermat.OneThousandEightHundredThirtyOne.prime_358877⟩

namespace QCertificate
abbrev certificate :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitResidues.certificate
end QCertificate

namespace QChannel
abbrev factorization :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitChannelAtQ358877.factorization
abbrev irregular_scalar_eq :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitChannelAtQ358877.irregular_scalar_eq
end QChannel

/-- Zero-based Kummer row for Bernoulli index `2 * (636 + 1) = 1274`. -/
abbrev irregularKummerRow : Fin (kummerLogRank 1831) :=
  CircularUnitChannelCoordinates.irregularKummerRow

/-- The exceptional-row predicate emitted by the 1831 irregular scan. -/
def exceptionalRow (j : Fin (kummerLogRank 1831)) : Prop :=
  j = irregularKummerRow

/-- The q-dependent detector factorization generated from the checked
`q = 358877` certificate. -/
abbrev factorization := QChannel.factorization irregularKummerRow

/-- The q-dependent scalar used on the exceptional canonical channel. -/
def detector (_j : Fin (kummerLogRank 1831)) : ZMod 1831 :=
  factorization.scalar

/-- The generated scalar agrees with the standalone frequency-278 receipt. -/
theorem factorization_scalar_eq : factorization.scalar = 882 :=
  QChannel.irregular_scalar_eq

/-- The sole required auxiliary scalar is nonzero. -/
theorem factorization_scalar_ne_zero : factorization.scalar ≠ 0 := by
  rw [factorization_scalar_eq]
  decide

/-- A residue-matrix kernel forces the selected intrinsic Kummer channel to
vanish after multiplication by its q-dependent scalar. -/
theorem detector_mul_canonical_of_matrix_mulVec_eq_zero
    (e : Fin 914 → ZMod 1831)
    (h : QCertificate.certificate.matrix *ᵥ e = 0) :
    factorization.scalar *
        canonicalKummerChannel 1831 (by norm_num) irregularKummerRow e = 0 := by
  have hf := factorization.residueDetector_eq_scalar_mul_canonical e
  rw [Factorization.residueDetector, h] at hf
  simpa using hf.symm

/-- The low scan confines every Bernoulli-divisible Kummer row to row 636. -/
theorem bernoulli_support (j : Fin (kummerLogRank 1831))
    (hdiv : (1831 : ℤ) ∣
      (bernoulli (2 * kummerLogRowIndex (p := 1831) j)).num) :
    exceptionalRow j := by
  have hmem : 2 * kummerLogRowIndex (p := 1831) j ∈
      Fermat.Irregular.VandiverData.indices 1831 := by
    simp only [Fermat.Irregular.VandiverData.indices,
      Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by
      have := kummerLogRowIndex_one_le (p := 1831) j
      omega, by
      simpa using
        two_mul_kummerLogRowIndex_le_sub_three (p := 1831) j⟩,
      even_two_mul _⟩
  have hindex := irregular_index_eq_1274
    (2 * kummerLogRowIndex (p := 1831) j) hmem hdiv
  unfold exceptionalRow
  apply Fin.ext
  change j.val = 636
  change 2 * (j.val + 1) = 1274 at hindex
  omega

/-- The one detector required by the exceptional-row predicate is nonzero. -/
theorem detector_ne_zero (j : Fin (kummerLogRank 1831))
    (_hj : exceptionalRow j) : detector j ≠ 0 :=
  factorization_scalar_ne_zero

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {1831} ℚ K]

local instance : NumberField.IsCMField K :=
  cyclotomicPrime_isCMField (p := 1831) (K := K) (by decide) (by norm_num)

/-- The selective residue receipt makes the real cyclotomic-unit subgroup
`1831`-saturated. This theorem uses only the detector at frequency `278`. -/
theorem CPlus_pSaturated_channels :
    pSaturated
      (CPlus (p := 1831) (K := K) (by norm_num))
      (EPlus (K := K)) 1831 := by
  apply CPlus_pSaturated_of_irregular_support_detectors
    (p := 1831) (K := K) (by norm_num) (by norm_num)
    exceptionalRow detector bernoulli_support detector_ne_zero
  intro s e hpow j hj
  have hmatrix :=
    matrix_mulVec_exponents_eq_zero_of_CPlus_product_mem_powers
      (K := K) QCertificate.certificate (by norm_num) s e hpow
  subst j
  exact detector_mul_canonical_of_matrix_mulVec_eq_zero
    (fun i ↦ (e i : ZMod 1831)) hmatrix

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitResiduesChannels
