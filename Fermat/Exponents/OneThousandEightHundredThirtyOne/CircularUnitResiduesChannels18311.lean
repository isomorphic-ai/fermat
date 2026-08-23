import Fermat.Certificates.CaseII_1.IrregularSupport1831
import Fermat.Descent.Irregular.SelectiveCircularUnitResidues
import Fermat.Descent.Irregular.SelectiveKummerSaturation
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitChannelAtQ18311

/-!
# Selective circular-unit residue route at q = 18311

This is the second auxiliary-prime implementation of the determinant-free
Case-II.1 route for exponent `1831`. The generic constructor factors its
residue detector through the same intrinsic Kummer row `636` as at
`q = 358877`. Its q-dependent scalar is `1165 ≠ 0`.

The full `q = 18311` residue matrix is singular; only the sole possible
irregular Bernoulli channel is required here.
-/

open scoped Matrix NumberField

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitResiduesChannels18311

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
local instance : Fact (Nat.Prime 18311) := ⟨by norm_num⟩

namespace QCertificate
abbrev certificate :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitResidueCertificate1831AtQ18311.certificate
end QCertificate


namespace QChannel
abbrev factorization :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitChannelAtQ18311.factorization
abbrev irregular_scalar_eq :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitChannelAtQ18311.irregular_scalar_eq
end QChannel

/-- Zero-based Kummer row for Bernoulli index `2 * (636 + 1) = 1274`. -/
abbrev irregularKummerRow : Fin (kummerLogRank 1831) :=
  CircularUnitChannelCoordinates.irregularKummerRow

/-- The exceptional-row predicate emitted by the 1831 irregular scan. -/
def exceptionalRow (j : Fin (kummerLogRank 1831)) : Prop :=
  j = irregularKummerRow

/-- The q-dependent detector factorization generated from the checked
`q = 18311` certificate. -/
abbrev factorization := QChannel.factorization irregularKummerRow

/-- The generated scalar agrees with the standalone frequency-278 receipt. -/
theorem factorization_scalar_eq : factorization.scalar = 1165 :=
  QChannel.irregular_scalar_eq

/-- The q-dependent scalar on the irregular channel is nonzero. -/
theorem factorization_scalar_ne_zero : factorization.scalar ≠ 0 := by
  rw [factorization_scalar_eq]
  decide

/-- A source-order q=18311 residue-matrix kernel forces the intrinsic
irregular Kummer channel to vanish after multiplication by its detector. -/
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

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {1831} ℚ K]

local instance : NumberField.IsCMField K :=
  cyclotomicPrime_isCMField (p := 1831) (K := K) (by decide) (by norm_num)

/-- The singular q=18311 residue matrix nevertheless makes the real
cyclotomic-unit subgroup `1831`-saturated, because its sole required
irregular detector is nonzero. -/
theorem CPlus_pSaturated_channels :
    pSaturated
      (CPlus (p := 1831) (K := K) (by norm_num))
      (EPlus (K := K)) 1831 := by
  apply CPlus_pSaturated_of_irregular_support_detectors
    (p := 1831) (K := K) (by norm_num) (by norm_num)
    exceptionalRow (fun _ ↦ factorization.scalar) bernoulli_support
    (fun _ _ ↦ factorization_scalar_ne_zero)
  intro s e hpow j hj
  have hmatrix :=
    matrix_mulVec_exponents_eq_zero_of_CPlus_product_mem_powers
      (K := K) QCertificate.certificate (by norm_num) s e hpow
  subst j
  exact detector_mul_canonical_of_matrix_mulVec_eq_zero
    (fun i ↦ (e i : ZMod 1831)) hmatrix

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitResiduesChannels18311
