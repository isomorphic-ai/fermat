import Fermat.Certificates.CaseII_1.CircularUnitIrregularChannel1831
import Fermat.Certificates.CaseII_1.IrregularSupport1831
import Fermat.Descent.Irregular.CyclicDifferenceMatrixProjection
import Fermat.Descent.Irregular.SelectiveCircularUnitResidues
import Fermat.Descent.Irregular.SelectiveKummerSaturation
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitResiduesBase

/-!
# Selective circular-unit residue route at exponent 1831

This is the determinant-free Case-II.1 route. A `p`th-power relation among
the real cyclotomic-unit generators first gives a kernel vector for the
auxiliary-prime residue matrix. The inverse Fourier projection at frequency
`278` is exactly Kummer's canonical row for Bernoulli index `1274`.

The complete low Bernoulli scan makes row `636` the only exceptional row,
and the standalone receipt proves that its detector has value `882 ≠ 0`.
Every other row is discharged by Kummer's logarithm matrix itself. Thus the
proof uses one numerical Fourier coefficient rather than nonsingularity of
the full `914 × 914` matrix.
-/

open scoped Matrix NumberField

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitResiduesChannels

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Fermat.Irregular.CyclicDifferenceMatrix
open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.SelectiveCircularUnitResidues
open Fermat.Irregular.SelectiveKummerSaturation
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitCyclic
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitEntryCertificate
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitIrregularChannel
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitMatrix
open Fermat.OneThousandEightHundredThirtyOne.IrregularSupport
open KummerCriterion
open KummerCriterion.CyclotomicUnits

local instance : Fact (Nat.Prime 1831) :=
  ⟨Fermat.OneThousandEightHundredThirtyOne.prime_1831⟩
local instance : Fact (Nat.Prime 358877) :=
  ⟨Fermat.OneThousandEightHundredThirtyOne.prime_358877⟩

/-- Reindex an original circular-unit exponent vector by its cyclic column
coordinate. -/
def cyclicReindexVector (e : Fin 914 → ZMod 1831) : Fin 914 → ZMod 1831 :=
  e ∘ columnPermutation.symm

/-- Zero-based Kummer row for Bernoulli index `2 * (636 + 1) = 1274`. -/
def irregularKummerRow : Fin (kummerLogRank 1831) := 636

/-- The exceptional-row predicate emitted by the 1831 irregular scan. -/
def exceptionalRow (j : Fin (kummerLogRank 1831)) : Prop :=
  j = irregularKummerRow

/-- The q-dependent detector used on the exceptional canonical channel. -/
def detector (_j : Fin (kummerLogRank 1831)) : ZMod 1831 :=
  coefficient slot

/-- The inverse Fourier character at frequency `278` is Kummer's moment
character at Bernoulli index `1274`, after the checked column permutation.
-/
theorem inverseMoment_entry_eq_vandermonde (i : Fin 914) :
    inverseMomentMatrix (9 : ZMod 1831) fourierRoot_isPrimitive.pow_eq_one
        slot (columnPermutation i) =
      vandermondeTeichmullerEvenSubOneMatrix (p := 1831) (by norm_num)
        irregularKummerRow i := by
  change
    fourierChar (9 : ZMod 1831) fourierRoot_isPrimitive.pow_eq_one slot
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
      _ = 1 := by rw [fourierRoot_isPrimitive.pow_eq_one, one_pow]
  rw [hinv]
  let s : ℕ :=
    (Fermat.OneThousandEightHundredThirtyOne.CircularUnitCyclic.coord
      (columnPermutation i)).val
  have hsquare :
      ((3 : ZMod 1831) ^ s) ^ 2 =
        (((i.val + 2 : ℕ) : ZMod 1831) ^ 2) :=
    column_exponent_square_certificate i
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

/-- Transport a source-order residue-matrix kernel into cyclic order. -/
theorem differenceMatrix_mulVec_cyclicReindex_eq_zero
    (e : Fin 914 → ZMod 1831)
    (h : matrix *ᵥ e = 0) :
    differenceMatrix symbolPhase *ᵥ cyclicReindexVector e = 0 := by
  funext r
  have hr := congrFun h (rowPermutation.symm r)
  simp only [Pi.zero_apply] at hr ⊢
  rw [show (differenceMatrix symbolPhase *ᵥ cyclicReindexVector e) r =
      (matrix *ᵥ e) (rowPermutation.symm r) by
    symm
    exact mulVec_reindex_equiv rowPermutation columnPermutation
      (differenceMatrix symbolPhase) e r]
  exact hr

/-- The projected inverse-character moment is exactly Kummer's row `636`
in the original generator order. -/
theorem inverseMoment_mulVec_eq_kummerMoment
    (e : Fin 914 → ZMod 1831) :
    (inverseMomentMatrix (9 : ZMod 1831)
        fourierRoot_isPrimitive.pow_eq_one *ᵥ cyclicReindexVector e) slot =
      (vandermondeTeichmullerEvenSubOneMatrix (p := 1831) (by norm_num) *ᵥ e)
        irregularKummerRow := by
  classical
  simp only [Matrix.mulVec, dotProduct, cyclicReindexVector,
    Function.comp_apply]
  let F : Fin 914 → ZMod 1831 := fun s ↦
    inverseMomentMatrix (9 : ZMod 1831)
      fourierRoot_isPrimitive.pow_eq_one slot s *
        e (columnPermutation.symm s)
  calc
    (∑ s : Fin 914, F s) = ∑ i : Fin 914, F (columnPermutation i) :=
      (Equiv.sum_comp columnPermutation F).symm
    _ = ∑ i : Fin 914,
        vandermondeTeichmullerEvenSubOneMatrix (p := 1831) (by norm_num)
          irregularKummerRow i * e i := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [F]
      rw [Equiv.symm_apply_apply, inverseMoment_entry_eq_vandermonde]

/-- A source-order residue-matrix relation forces the exceptional Kummer
moment after multiplication by the single frequency-278 detector. -/
theorem detector_mul_kummerMoment_of_matrix_mulVec_eq_zero
    (e : Fin 914 → ZMod 1831)
    (h : matrix *ᵥ e = 0) :
    coefficient slot *
        (vandermondeTeichmullerEvenSubOneMatrix
          (p := 1831) (by norm_num) *ᵥ e) irregularKummerRow = 0 := by
  have hcyclic := differenceMatrix_mulVec_cyclicReindex_eq_zero e h
  have hprojected :=
    fourierCoeff_mul_inverseMoment_of_mulVec_eq_zero
      (n := 914) (R := ZMod 1831)
      (9 : ZMod 1831) fourierRoot_isPrimitive symbolPhase
      (cyclicReindexVector e) hcyclic slot
  rw [inverseMoment_mulVec_eq_kummerMoment] at hprojected
  exact hprojected

/-- The low scan confines every Bernoulli-divisible Kummer row to row 636.
-/
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

/-- The one detector required by the exceptional-row predicate is nonzero.
-/
theorem detector_ne_zero (j : Fin (kummerLogRank 1831))
    (_hj : exceptionalRow j) : detector j ≠ 0 := by
  exact fhat_277_ne_zero

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {1831} ℚ K]

local instance : NumberField.IsCMField K :=
  cyclotomicPrime_isCMField (p := 1831) (K := K) (by decide) (by norm_num)

/-- The selective residue receipt makes the real cyclotomic-unit subgroup
`1831`-saturated. This theorem uses only the detector at frequency `278`.
-/
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
      (K := K)
      Fermat.OneThousandEightHundredThirtyOne.CircularUnitResidues.certificate
      (by norm_num) s e hpow
  subst j
  exact detector_mul_kummerMoment_of_matrix_mulVec_eq_zero
    (fun i ↦ (e i : ZMod 1831)) hmatrix

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitResiduesChannels
