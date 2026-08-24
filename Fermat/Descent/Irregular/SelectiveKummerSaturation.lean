import KummerCriterion.CyclotomicUnits.KummerLogDeterminant
import KummerCriterion.CyclotomicUnits.LogDomain

/-!
# Selective Kummer saturation

Kummer's logarithm matrix factors as a diagonal matrix of Bernoulli row
factors followed by an invertible Vandermonde change of basis. Rows with a
nonzero Bernoulli factor therefore vanish automatically in every Kummer-log
relation. This module exposes the remaining rows as a small certificate
interface: an external detector only has to kill the Vandermonde coordinates
supported on irregular Bernoulli rows.

The detector is allowed to depend on an auxiliary split prime. Its relation
is stated against the canonical Vandermonde coordinate, so the Bernoulli
channel is independent of that choice.
-/

namespace Fermat.Irregular.SelectiveKummerSaturation

noncomputable section

open NumberField
open KummerCriterion
open KummerCriterion.CyclotomicUnits
open PadicLogSetup
open PadicLogSetup.DworkParameter

/-- Recover a vector from a diagonal-times-invertible relation when the
coordinates lost at zero diagonal entries are supplied separately. -/
theorem vector_eq_zero_of_diagonal_mul_relation_of_exceptional_rows
    {R ι : Type*} [CommRing R] [IsDomain R]
    [Fintype ι] [DecidableEq ι]
    (exceptional : ι → Prop)
    (d : ι → R) (V : Matrix ι ι R) (v : ι → R)
    (hVdet : V.det ≠ 0)
    (hdiag : (Matrix.diagonal d * V).mulVec v = 0)
    (hregular : ∀ j, ¬ exceptional j → d j ≠ 0)
    (hexceptional : ∀ j, exceptional j → V.mulVec v j = 0) :
    v = 0 := by
  apply Matrix.eq_zero_of_mulVec_eq_zero hVdet
  funext j
  by_cases hj : exceptional j
  · exact hexceptional j hj
  · have hrow := congr_fun hdiag j
    rw [← Matrix.mulVec_mulVec v (Matrix.diagonal d) V] at hrow
    rw [Matrix.mulVec_diagonal] at hrow
    exact (mul_eq_zero.mp hrow).resolve_left (hregular j hj)

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]

/-- A Kummer-log relation is zero modulo `p` when regular rows are supplied
by the Bernoulli diagonal and the exceptional Vandermonde coordinates are
supplied externally. -/
theorem exponents_modP_eq_zero_of_selective_kummer_rows
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (exceptional : Fin (kummerLogRank p) → Prop)
    (e : Fin (kummerLogRank p) → ℤ)
    (hlog : Matrix.mulVec
        (concreteKummerLogMatrix (p := p) (K := K) hp_three hp_five)
        (fun a => (e a : ZMod p)) = 0)
    (hregular : ∀ j, ¬ exceptional j →
      kummerLogDetRowFactor (p := p) j ≠ 0)
    (hexceptional : ∀ j, exceptional j →
      Matrix.mulVec
        (vandermondeTeichmullerEvenSubOneMatrix (p := p) hp_three)
        (fun a => (e a : ZMod p)) j = 0) :
    ∀ a, (e a : ZMod p) = 0 := by
  have hfactor : Matrix.mulVec
        (Matrix.diagonal (kummerLogDetRowFactor (p := p)) *
          vandermondeTeichmullerEvenSubOneMatrix (p := p) hp_three)
        (fun a => (e a : ZMod p)) = 0 := by
    rw [← concreteKummerLogMatrix_eq_diagonal_mul_vandermonde
      (p := p) (K := K) hp_three hp_five]
    exact hlog
  have hezero : (fun a => (e a : ZMod p)) = 0 :=
    vector_eq_zero_of_diagonal_mul_relation_of_exceptional_rows
      exceptional _ _ _
      (vandermonde_teichmuller_even_sub_one_det_ne_zero
        (p := p) hp_three)
      hfactor hregular hexceptional
  exact fun a => congr_fun hezero a

/-- Production seam before detector nonvanishing is applied: an auxiliary
certificate supplies exactly the exceptional Vandermonde coordinates for
every `CPlus` exponent product which is a `p`th power in the real-unit group.
-/
theorem CPlus_pSaturated_of_selective_kummer_rows
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (exceptional : Fin (kummerLogRank p) → Prop)
    (hregular : ∀ j, ¬ exceptional j →
      bernoulliFactor p (kummerLogRowIndex (p := p) j) ≠ 0)
    (hexceptional : ∀ (s : ℤ) (e : Fin (kummerLogRank p) → ℤ),
      CPlusExponentProduct (p := p) (K := K) hp_three s e ∈
          pPowerSubgroup (EPlus (K := K)) p →
      ∀ j, exceptional j →
        Matrix.mulVec
          (vandermondeTeichmullerEvenSubOneMatrix (p := p) hp_three)
          (fun a => (e a : ZMod p)) j = 0) :
    pSaturated (CPlus (p := p) (K := K) hp_three) (EPlus (K := K)) p := by
  refine CPlus_pSaturated_of_generator_exponents_modP_zero
    (p := p) (K := K) (by omega : p ≠ 2) hp_three ?_
  intro s e hpow
  have hcompleted :
      ∃ y : dworkFixedSubalgebra p K,
        p • y = ∑ a : Fin (kummerLogRank p),
          e a • concreteKummerLogVector (p := p) (K := K) hp_three a := by
    simpa [concreteKummerLogVector] using
      completedLog_relation_of_CPlus_product_mem_powers
        (p := p) (K := K) (by omega : p ≠ 2) hp_three s e hpow
  have hlog := concreteKummerLogMatrix_mulVec_exponents_eq_zero
    (p := p) (K := K) hp_three hp_five e hcompleted
  apply exponents_modP_eq_zero_of_selective_kummer_rows
    (p := p) (K := K) hp_three hp_five exceptional e hlog
  · intro j hj
    exact (kummerLogDetRowFactor_ne_zero_iff_bernoulliFactor_ne_zero
      (p := p) hp_five j).mpr (hregular j hj)
  · exact hexceptional s e hpow

/-- Q-free generator interface. A complete irregular scan supplies the
support of the possibly missing Bernoulli rows, while an intrinsic receipt
annihilates exactly those canonical Kummer coordinates on every power
relation. -/
theorem CPlus_pSaturated_of_irregular_support_kummer_rows
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (exceptional : Fin (kummerLogRank p) → Prop)
    (hsupport : ∀ j,
      (p : ℤ) ∣ (_root_.bernoulli
        (2 * kummerLogRowIndex (p := p) j)).num → exceptional j)
    (hexceptional : ∀ (s : ℤ) (e : Fin (kummerLogRank p) → ℤ),
      CPlusExponentProduct (p := p) (K := K) hp_three s e ∈
          pPowerSubgroup (EPlus (K := K)) p →
      ∀ j, exceptional j →
        Matrix.mulVec
          (vandermondeTeichmullerEvenSubOneMatrix (p := p) hp_three)
          (fun a => (e a : ZMod p)) j = 0) :
    pSaturated (CPlus (p := p) (K := K) hp_three) (EPlus (K := K)) p := by
  apply CPlus_pSaturated_of_selective_kummer_rows
    (p := p) (K := K) hp_three hp_five exceptional
  · intro j hj
    exact (bernoulliFactor_ne_zero_iff_not_dvd_bernoulli_num
      (p := p) (kummerLogRowIndex_one_le (p := p) j)
      (two_mul_kummerLogRowIndex_le_sub_three (p := p) j)).mpr
      (fun hdiv => hj (hsupport j hdiv))
  · exact hexceptional

/-- A generated detector may vary with the chosen auxiliary prime, but only
its value and relation on exceptional rows are used. -/
theorem CPlus_pSaturated_of_selective_detectors
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (exceptional : Fin (kummerLogRank p) → Prop)
    (detector : Fin (kummerLogRank p) → ZMod p)
    (hregular : ∀ j, ¬ exceptional j →
      bernoulliFactor p (kummerLogRowIndex (p := p) j) ≠ 0)
    (hdetector : ∀ j, exceptional j → detector j ≠ 0)
    (hdetector_relation :
      ∀ (s : ℤ) (e : Fin (kummerLogRank p) → ℤ),
        CPlusExponentProduct (p := p) (K := K) hp_three s e ∈
            pPowerSubgroup (EPlus (K := K)) p →
        ∀ j, exceptional j →
          detector j *
            Matrix.mulVec
              (vandermondeTeichmullerEvenSubOneMatrix (p := p) hp_three)
              (fun a => (e a : ZMod p)) j = 0) :
    pSaturated (CPlus (p := p) (K := K) hp_three) (EPlus (K := K)) p := by
  apply CPlus_pSaturated_of_selective_kummer_rows
    (p := p) (K := K) hp_three hp_five exceptional hregular
  intro s e hpow j hj
  exact (mul_eq_zero.mp (hdetector_relation s e hpow j hj)).resolve_left
    (hdetector j hj)

/-- Generator-facing interface. A complete irregular scan only has to show
that Bernoulli-divisible rows are exceptional; regularity of every other row
is recovered internally. -/
theorem CPlus_pSaturated_of_irregular_support_detectors
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (exceptional : Fin (kummerLogRank p) → Prop)
    (detector : Fin (kummerLogRank p) → ZMod p)
    (hsupport : ∀ j,
      (p : ℤ) ∣ (_root_.bernoulli
        (2 * kummerLogRowIndex (p := p) j)).num → exceptional j)
    (hdetector : ∀ j, exceptional j → detector j ≠ 0)
    (hdetector_relation :
      ∀ (s : ℤ) (e : Fin (kummerLogRank p) → ℤ),
        CPlusExponentProduct (p := p) (K := K) hp_three s e ∈
            pPowerSubgroup (EPlus (K := K)) p →
        ∀ j, exceptional j →
          detector j *
            Matrix.mulVec
              (vandermondeTeichmullerEvenSubOneMatrix (p := p) hp_three)
              (fun a => (e a : ZMod p)) j = 0) :
    pSaturated (CPlus (p := p) (K := K) hp_three) (EPlus (K := K)) p := by
  apply CPlus_pSaturated_of_irregular_support_kummer_rows
    (p := p) (K := K) hp_three hp_five exceptional hsupport
  intro s e hpow j hj
  exact (mul_eq_zero.mp (hdetector_relation s e hpow j hj)).resolve_left
    (hdetector j hj)

end

end Fermat.Irregular.SelectiveKummerSaturation
