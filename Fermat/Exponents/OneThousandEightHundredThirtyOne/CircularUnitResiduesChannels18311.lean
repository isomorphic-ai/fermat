import Fermat.Certificates.CaseII_1.CircularUnitResidueCertificate1831AtQ18311
import Fermat.Certificates.CaseII_1.IrregularSupport1831
import Fermat.Descent.Irregular.AuxiliaryResidueChannels
import Fermat.Descent.Irregular.SelectiveCircularUnitResidues
import Fermat.Descent.Irregular.SelectiveKummerSaturation

/-!
# Selective circular-unit residue route at q = 18311

This is a second auxiliary-prime implementation of the one-channel Case-II.1
route for exponent `1831`. The residue matrix at `q = 18311` is singular, but
its detector on the sole possible irregular Bernoulli row is `1165 != 0`.

The q-dependent Fourier functional is factored through Kummer's canonical row
`636`, corresponding to Bernoulli index `1274`. Every regular row is handled
by Kummer's logarithm matrix, so no full residue-matrix determinant is needed.
-/

open scoped Matrix NumberField

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitResiduesChannels18311

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Fermat.Irregular.AuxiliaryResidueChannels
open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CyclicDifferenceMatrix
open Fermat.Irregular.SelectiveCircularUnitResidues
open Fermat.Irregular.SelectiveKummerSaturation
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitCyclic
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitMatrix
open Fermat.OneThousandEightHundredThirtyOne.IrregularSupport
open KummerCriterion
open KummerCriterion.CyclotomicUnits

namespace QPhase
abbrev symbolPhase :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitIrregularChannel1831AtQ18311.symbolPhase
abbrev slot :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitIrregularChannel1831AtQ18311.slot
abbrev coefficient :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitIrregularChannel1831AtQ18311.coefficient
abbrev fourierRoot_isPrimitive :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitIrregularChannel1831AtQ18311.fourierRoot_isPrimitive
abbrev fhat_277_ne_zero :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitIrregularChannel1831AtQ18311.fhat_277_ne_zero
end QPhase

namespace QCertificate
abbrev matrix :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitResidueCertificate1831AtQ18311.matrix
abbrev certificate :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitResidueCertificate1831AtQ18311.certificate
end QCertificate

namespace SharedCoordinates
abbrev column_exponent_square_certificate :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitEntryCertificate.column_exponent_square_certificate
end SharedCoordinates

local instance : Fact (Nat.Prime 1831) := ⟨by decide⟩
local instance : Fact (Nat.Prime 18311) := ⟨by norm_num⟩

/-- Zero-based Kummer row for Bernoulli index `2 * (636 + 1) = 1274`. -/
def irregularKummerRow : Fin (kummerLogRank 1831) := 636

/-- The exceptional-row predicate emitted by the 1831 irregular scan. -/
def exceptionalRow (j : Fin (kummerLogRank 1831)) : Prop :=
  j = irregularKummerRow

/-- The inverse frequency `278` is exactly Kummer's row `636` after the
checked p-dependent column permutation. -/
theorem inverseMoment_entry_eq_vandermonde (i : Fin 914) :
    inverseMomentMatrix (9 : ZMod 1831)
        QPhase.fourierRoot_isPrimitive.pow_eq_one QPhase.slot
        (columnPermutation i) =
      vandermondeTeichmullerEvenSubOneMatrix (p := 1831) (by norm_num)
        irregularKummerRow i := by
  change
    fourierChar (9 : ZMod 1831)
        QPhase.fourierRoot_isPrimitive.pow_eq_one QPhase.slot
        (-Fermat.OneThousandEightHundredThirtyOne.CircularUnitCyclic.coord
          (columnPermutation i)) - 1 =
      (((i.val + 2 : ℕ) : ZMod 1831) ^ 2) ^ 637 - 1
  rw [AddChar.map_neg_eq_inv, fourierChar_apply]
  change ((9 : ZMod 1831) ^
    (278 * (Fermat.OneThousandEightHundredThirtyOne.CircularUnitCyclic.coord
      (columnPermutation i)).val))⁻¹ - 1 = _
  have hinv :
      ((9 : ZMod 1831) ^ (278 *
        (Fermat.OneThousandEightHundredThirtyOne.CircularUnitCyclic.coord
          (columnPermutation i)).val))⁻¹ =
        (9 : ZMod 1831) ^ (637 *
          (Fermat.OneThousandEightHundredThirtyOne.CircularUnitCyclic.coord
            (columnPermutation i)).val) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add]
    let s :=
      (Fermat.OneThousandEightHundredThirtyOne.CircularUnitCyclic.coord
        (columnPermutation i)).val
    calc
      (9 : ZMod 1831) ^ (278 * s + 637 * s) =
          (9 : ZMod 1831) ^ (915 * s) :=
        congrArg (fun m : ℕ ↦ (9 : ZMod 1831) ^ m) (by omega)
      _ = ((9 : ZMod 1831) ^ 915) ^ s := by rw [pow_mul]
      _ = 1 := by
        rw [QPhase.fourierRoot_isPrimitive.pow_eq_one, one_pow]
  rw [hinv]
  let s : ℕ :=
    (Fermat.OneThousandEightHundredThirtyOne.CircularUnitCyclic.coord
      (columnPermutation i)).val
  have hsquare :
      ((3 : ZMod 1831) ^ s) ^ 2 =
        (((i.val + 2 : ℕ) : ZMod 1831) ^ 2) :=
    SharedCoordinates.column_exponent_square_certificate i
  have hpow := congrArg (fun x : ZMod 1831 ↦ x ^ 637) hsquare
  rw [show (9 : ZMod 1831) = (3 : ZMod 1831) ^ 2 by norm_num]
  change (((3 : ZMod 1831) ^ 2) ^ (637 * s) - 1) = _
  have hleft :
      ((3 : ZMod 1831) ^ 2) ^ (637 * s) =
        (((3 : ZMod 1831) ^ s) ^ 2) ^ 637 := by
    calc
      ((3 : ZMod 1831) ^ 2) ^ (637 * s) =
          (3 : ZMod 1831) ^ (2 * (637 * s)) :=
            (pow_mul (3 : ZMod 1831) 2 (637 * s)).symm
      _ = (3 : ZMod 1831) ^ ((s * 2) * 637) :=
        congrArg (fun m : ℕ ↦ (3 : ZMod 1831) ^ m) (by omega)
      _ = ((3 : ZMod 1831) ^ (s * 2)) ^ 637 :=
        pow_mul (3 : ZMod 1831) (s * 2) 637
      _ = (((3 : ZMod 1831) ^ s) ^ 2) ^ 637 :=
        congrArg (fun x : ZMod 1831 ↦ x ^ 637)
          (pow_mul (3 : ZMod 1831) s 2)
  exact congrArg (fun x : ZMod 1831 ↦ x - 1) (hleft.trans hpow)

/-- Exact factorization of the `q = 18311` residue detector through the
canonical Kummer row for Bernoulli index `1274`. -/
def factorization :
    Factorization 1831 18311 (by norm_num) QCertificate.certificate
      irregularKummerRow where
  weights := fun sourceRow ↦
    positiveMomentMatrix (9 : ZMod 1831)
      QPhase.fourierRoot_isPrimitive.pow_eq_one QPhase.slot
        (rowPermutation sourceRow)
  scalar := QPhase.coefficient QPhase.slot
  factors := by
    intro e
    exact cyclic_reindexed_factorization
      rowPermutation columnPermutation QCertificate.matrix QPhase.symbolPhase rfl
      (9 : ZMod 1831) QPhase.fourierRoot_isPrimitive QPhase.slot
      (fun i ↦
        vandermondeTeichmullerEvenSubOneMatrix (p := 1831) (by norm_num)
          irregularKummerRow i)
      inverseMoment_entry_eq_vandermonde e

/-- The q-dependent scalar on the irregular channel is `1165 != 0`. -/
theorem factorization_scalar_ne_zero : factorization.scalar ≠ 0 :=
  QPhase.fhat_277_ne_zero

/-- A source-order q=18311 residue-matrix kernel forces the canonical
irregular Kummer moment to vanish after multiplication by its detector. -/
theorem detector_mul_canonical_of_matrix_mulVec_eq_zero
    (e : Fin 914 → ZMod 1831)
    (h : QCertificate.matrix *ᵥ e = 0) :
    factorization.scalar *
        canonicalKummerChannel 1831 (by norm_num) irregularKummerRow e = 0 := by
  have hf := factorization.residueDetector_eq_scalar_mul_canonical e
  change QCertificate.certificate.matrix *ᵥ e = 0 at h
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
