import Fermat.Irregular.CyclotomicLogDetPrime
import Fermat.Irregular.CyclotomicSineProductPrime

/-!
# The prime cyclotomic sine determinant as a Fourier cofactor

The logarithmic sine determinant of the canonical circular units is an
augmentation cofactor on the real residue group.  The abstract finite-group
determinant formula therefore expresses it as the product of all nontrivial
Fourier coefficients.
-/

open scoped Classical BigOperators

namespace Fermat.Irregular.CyclotomicLogCofactorPrime

noncomputable section

open Fermat.Irregular.CyclotomicLogDet
open Fermat.Irregular.CyclotomicLogDetPrime
open Fermat.Irregular.CyclotomicPlacesPrime
open Fermat.Irregular.CyclotomicSineProductPrime
open Fermat.Irregular.CyclotomicCharactersPrime
open Fermat.Irregular.SinnottIndexPrime

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 < p)]

local notation3 "r" => (p - 3) / 2
local notation3 "n" => r + 1

local instance : Fintype (RealResidueGroup p →* ℂˣ) :=
  Fintype.ofFinite _

def etaUnit : ℂˣ :=
  Units.mk0 (eta (p := p))
    ((eta_primitive (p := p)).ne_zero
      (Nat.Prime.ne_zero (Fact.out : Nat.Prime p)))

theorem etaUnit_primitive :
    IsPrimitiveRoot (etaUnit (p := p)) p := by
  rw [← IsPrimitiveRoot.coe_units_iff]
  exact eta_primitive (p := p)

theorem etaUnit_pow_val (a : ZMod p) :
    ((((etaUnit_primitive (p := p)).zmodEquivZPowers a).toMul :
      Subgroup.zpowers (etaUnit (p := p))) : ℂˣ) =
      etaUnit (p := p) ^ a.val := by
  have h := (etaUnit_primitive (p := p)).zmodEquivZPowers_apply_coe_nat
    a.val
  rw [ZMod.natCast_zmod_val] at h
  exact congrArg
    (fun z : Additive (Subgroup.zpowers (etaUnit (p := p))) ↦
      ((z.toMul : Subgroup.zpowers (etaUnit (p := p))) : ℂˣ)) h

theorem eta_pow_neg_val (a : ZMod p) :
    eta (p := p) ^ (-a).val =
      (eta (p := p) ^ a.val)⁻¹ := by
  have hmap := map_neg
    (etaUnit_primitive (p := p)).zmodEquivZPowers a
  have hunit :
      etaUnit (p := p) ^ (-a).val =
        (etaUnit (p := p) ^ a.val)⁻¹ := by
    rw [← etaUnit_pow_val (p := p) (-a),
      ← etaUnit_pow_val (p := p) a]
    exact congrArg
      (fun z : Additive (Subgroup.zpowers (etaUnit (p := p))) ↦
        ((z.toMul : Subgroup.zpowers
          (etaUnit (p := p))) : ℂˣ)) hmap
  simpa [etaUnit, Units.val_inv_eq_inv_val] using
    congrArg Units.val hunit

def unitChordLog (u : (ZMod p)ˣ) : ℝ :=
  Real.log ‖1 - eta (p := p) ^ (u : ZMod p).val‖

theorem unitChordLog_neg (u : (ZMod p)ˣ) :
    unitChordLog (p := p) (-u) = unitChordLog (p := p) u := by
  simp only [unitChordLog, Units.val_neg]
  rw [eta_pow_neg_val]
  congr 1
  rw [norm_one_sub_inv_of_norm_one]
  rw [norm_pow, Complex.norm_eq_one_of_pow_eq_one
    (eta_primitive (p := p)).pow_eq_one
      (Nat.Prime.ne_zero (Fact.out : Nat.Prime p)), one_pow]

def realChordLogKernel : RealResidueGroup p → ℝ :=
  Quotient.lift (unitChordLog (p := p)) (by
    intro u v huv
    have hmem : u / v ∈ signSubgroup p :=
      QuotientGroup.eq_iff_div_mem.mp (Quotient.sound huv)
    rw [signSubgroup_mem_iff] at hmem
    rcases hmem with h | h
    · have huv' : u = v := div_eq_one.mp h
      rw [huv']
    · have huv' : u = -v := by
        calc
          u = (u / v) * v := (div_mul_cancel _ _).symm
          _ = (-1) * v := by rw [h]
          _ = -v := by simp
      have hvu : v = -u := by rw [huv', neg_neg]
      rw [hvu, unitChordLog_neg])

theorem realChordLogKernel_mk (u : (ZMod p)ˣ) :
    realChordLogKernel (p := p) (QuotientGroup.mk u) =
      unitChordLog (p := p) u := rfl

theorem eta_pow_val_eq_pow_of_coe_eq
    (a : ZMod p) (m : ℕ) (h : a = (m : ZMod p)) :
    eta (p := p) ^ a.val = eta (p := p) ^ m := by
  apply pow_eq_pow_of_modEq _
    (eta_primitive (p := p)).pow_eq_one
  apply (ZMod.natCast_eq_natCast_iff a.val m p).mp
  rw [ZMod.natCast_zmod_val, h]

theorem unitChordLog_standardUnit (j : Fin n) :
    unitChordLog (p := p) (standardUnit (p := p) j) =
      Real.log (chord (p := p) j) := by
  rw [unitChordLog]
  rw [eta_pow_val_eq_pow_of_coe_eq _ _
    (standardUnit_coe (p := p) j)]
  rw [chord_eq_norm]
  rfl

def sineChordNat (m : ℕ) : ℝ :=
  2 * |Real.sin (Real.pi * ((m : ℝ) / (p : ℝ)))|

theorem standardUnit_mul_coe (a k : Fin n) :
    ((standardUnit (p := p) a * standardUnit (p := p) k :
      (ZMod p)ˣ) : ZMod p) =
      (((a.val + 1) * (k.val + 1) : ℕ) : ZMod p) := by
  rw [Units.val_mul, standardUnit_coe, standardUnit_coe]
  norm_num

theorem unitChordLog_standardUnit_mul (a k : Fin n) :
    unitChordLog (p := p)
        (standardUnit (p := p) a * standardUnit (p := p) k) =
      Real.log
        (sineChordNat (p := p)
          ((a.val + 1) * (k.val + 1))) := by
  rw [unitChordLog]
  rw [eta_pow_val_eq_pow_of_coe_eq _ _
    (standardUnit_mul_coe (p := p) a k)]
  change Real.log
      ‖1 - Complex.exp (2 * Real.pi * Complex.I *
        (((1 : ℕ) : ℂ) / ((p : ℕ) : ℂ))) ^
          ((a.val + 1) * (k.val + 1))‖ = _
  rw [norm_one_sub_exp_two_pi_I_pow]
  simp only [sineChordNat, Nat.cast_one, Nat.cast_mul]
  congr 3
  ring_nf

def inverseIndex : Equiv.Perm (Fin n) :=
  ((standardRealResiduesEquiv (p := p)).trans
    (Equiv.inv (RealResidueGroup p))).trans
      (standardRealResiduesEquiv (p := p)).symm

@[simp]
theorem standardRealResiduesEquiv_inverseIndex (j : Fin n) :
    standardRealResiduesEquiv (p := p) (inverseIndex (p := p) j) =
      (standardRealResiduesEquiv (p := p) j)⁻¹ := by
  simp [inverseIndex]

def omittedInverseIndex : Fin n :=
  inverseIndex (p := p) (Fin.last r)

def inverseColumnsEquiv :
    Fin r ≃ {j : Fin n // j ≠ omittedInverseIndex (p := p)} :=
  (finSuccAboveEquiv (Fin.last r)).trans
    (Equiv.subtypeEquiv (inverseIndex (p := p)) fun j ↦ by
      change j ≠ Fin.last r ↔
        inverseIndex (p := p) j ≠
          inverseIndex (p := p) (Fin.last r)
      exact ((inverseIndex (p := p)).injective.ne_iff).symm)

theorem inverseColumnsEquiv_apply (j : Fin r) :
    (inverseColumnsEquiv (p := p) j).val =
      inverseIndex (p := p) j.castSucc := by
  simp [inverseColumnsEquiv, finSuccAboveEquiv_apply]

def inverseColumnReindex : Equiv.Perm (Fin r) :=
  (inverseColumnsEquiv (p := p)).trans
    (finSuccAboveEquiv (omittedInverseIndex (p := p))).symm

theorem succAbove_inverseColumnReindex_apply (j : Fin r) :
    Fin.succAbove (omittedInverseIndex (p := p))
        (inverseColumnReindex (p := p) j) =
      inverseIndex (p := p) j.castSucc := by
  calc
    Fin.succAbove (omittedInverseIndex (p := p))
        (inverseColumnReindex (p := p) j) =
      ((finSuccAboveEquiv (omittedInverseIndex (p := p)))
        (inverseColumnReindex (p := p) j)).val := rfl
    _ = (inverseColumnsEquiv (p := p) j).val := by
      simp [inverseColumnReindex]
    _ = inverseIndex (p := p) j.castSucc :=
      inverseColumnsEquiv_apply (p := p) j

theorem realChordLogKernel_standard_mul (a k : Fin n) :
    realChordLogKernel (p := p)
      (standardRealResiduesEquiv (p := p) a *
        standardRealResiduesEquiv (p := p) k) =
      Real.log (sineChordNat (p := p)
        ((a.val + 1) * (k.val + 1))) := by
  rw [standardRealResiduesEquiv_apply,
    standardRealResiduesEquiv_apply]
  change realChordLogKernel (p := p)
    (QuotientGroup.mk
      (standardUnit (p := p) a * standardUnit (p := p) k)) = _
  rw [realChordLogKernel_mk, unitChordLog_standardUnit_mul]

theorem realChordLogKernel_standard (k : Fin n) :
    realChordLogKernel (p := p)
        (standardRealResiduesEquiv (p := p) k) =
      Real.log (sineChordNat (p := p) (k.val + 1)) := by
  rw [standardRealResiduesEquiv_apply]
  change unitChordLog (p := p) (standardUnit (p := p) k) = _
  rw [unitChordLog_standardUnit]
  congr 1

def complexChordLogKernel (g : RealResidueGroup p) : ℂ :=
  realChordLogKernel (p := p) g

def logarithmicCofactor : Matrix (Fin r) (Fin r) ℂ :=
  (augmentationDifferenceMatrix
    (standardRealResiduesEquiv (p := p))
    (complexChordLogKernel (p := p))).submatrix
      (Fin.succAbove 0)
      (Fin.succAbove (omittedInverseIndex (p := p)))

def inverseAlignedLogarithmicCofactor :
    Matrix (Fin r) (Fin r) ℂ :=
  (logarithmicCofactor (p := p)).submatrix id
    (inverseColumnReindex (p := p))

theorem inverseAlignedLogarithmicCofactor_apply (i j : Fin r) :
    inverseAlignedLogarithmicCofactor (p := p) i j =
      (realChordLogKernel (p := p)
          (standardRealResiduesEquiv (p := p) i.succ *
            standardRealResiduesEquiv (p := p) j.castSucc) -
        realChordLogKernel (p := p)
          (standardRealResiduesEquiv (p := p) j.castSucc) : ℝ) := by
  rw [inverseAlignedLogarithmicCofactor, logarithmicCofactor]
  simp only [Matrix.submatrix_apply, id_eq]
  rw [succAbove_inverseColumnReindex_apply]
  rw [augmentationDifferenceMatrix_apply]
  rw [standardRealResiduesEquiv_symm_one]
  simp only [Fin.succAbove_zero, if_neg (Fin.succ_ne_zero i)]
  rw [standardRealResiduesEquiv_inverseIndex]
  simp only [inv_inv, complexChordLogKernel]
  norm_cast

theorem log_sineChordNat_sub (a k : ℕ)
    (hak : |Real.sin
      (Real.pi * (((a * k : ℕ) : ℝ) / p))| ≠ 0)
    (hk : |Real.sin
      (Real.pi * ((k : ℝ) / p))| ≠ 0) :
    Real.log (sineChordNat (p := p) (a * k)) -
        Real.log (sineChordNat (p := p) k) =
      Real.log |Real.sin
        (Real.pi * (((a * k : ℕ) : ℝ) / p))| -
      Real.log |Real.sin
        (Real.pi * ((k : ℝ) / p))| := by
  simp only [sineChordNat]
  rw [Real.log_mul (by norm_num) hak,
    Real.log_mul (by norm_num) hk]
  ring

theorem inverseAlignedLogarithmicCofactor_eq_map_logSineDifference :
    inverseAlignedLogarithmicCofactor (p := p) =
      (logSineDifferenceMatrix (p := p)).map
        (algebraMap ℝ ℂ) := by
  ext i j
  rw [inverseAlignedLogarithmicCofactor_apply]
  simp only [Matrix.map_apply, logSineDifferenceMatrix,
    Matrix.of_apply]
  rw [Complex.coe_algebraMap, Complex.ofReal_inj]
  rw [realChordLogKernel_standard_mul,
    realChordLogKernel_standard]
  let a := i.val + 2
  let k := j.val + 1
  have ha : ¬p ∣ a := by
    intro h
    have hle := Nat.le_of_dvd (by omega : 0 < a) h
    have hi := i.isLt
    have hpgt : 2 < p := Fact.out
    omega
  have hk : ¬p ∣ k := by
    intro h
    have hle := Nat.le_of_dvd (by omega : 0 < k) h
    have hj := j.isLt
    have hpgt : 2 < p := Fact.out
    omega
  have hak : ¬p ∣ a * k :=
    (Fact.out : Nat.Prime p).not_dvd_mul ha hk
  have hsak :
      |Real.sin
        (Real.pi * (((a * k : ℕ) : ℝ) / p))| ≠ 0 := by
    rw [abs_ne_zero]
    exact sin_pi_mul_div_ne_zero (p := p) (a * k) hak
  have hsk :
      |Real.sin (Real.pi * ((k : ℝ) / p))| ≠ 0 := by
    rw [abs_ne_zero]
    exact sin_pi_mul_div_ne_zero (p := p) k hk
  change Real.log (sineChordNat (p := p) (a * k)) -
      Real.log (sineChordNat (p := p) k) = _
  rw [log_sineChordNat_sub a k hsak hsk]
  dsimp [a, k]
  congr 2
  all_goals
    congr 2
    push_cast
    ring_nf

theorem inverseAlignedLogarithmicCofactor_det_eq_logSineDifferenceDet :
    (inverseAlignedLogarithmicCofactor (p := p)).det =
      ((logSineDifferenceMatrix (p := p)).det : ℂ) := by
  rw [inverseAlignedLogarithmicCofactor_eq_map_logSineDifference]
  exact (RingHom.map_det (algebraMap ℝ ℂ)
    (logSineDifferenceMatrix (p := p))).symm

theorem inverseAlignedLogarithmicCofactor_det_eq_sign_mul_cofactorDet :
    (inverseAlignedLogarithmicCofactor (p := p)).det =
      ((inverseColumnReindex (p := p)).sign : ℂ) *
        (logarithmicCofactor (p := p)).det :=
  Matrix.det_permute' (inverseColumnReindex (p := p))
    (logarithmicCofactor (p := p))

theorem sum_complexChordLogKernel :
    (∑ g : RealResidueGroup p,
      complexChordLogKernel (p := p) g) =
      (Real.log (Real.sqrt p) : ℂ) := by
  calc
    (∑ g : RealResidueGroup p,
      complexChordLogKernel (p := p) g) =
        ∑ j : Fin n, complexChordLogKernel (p := p)
          (standardRealResiduesEquiv (p := p) j) :=
      (Equiv.sum_comp (standardRealResiduesEquiv (p := p))
        (complexChordLogKernel (p := p))).symm
    _ = ∑ j : Fin n, (Real.log (chord (p := p) j) : ℂ) := by
      apply Fintype.sum_congr
      intro j
      rw [complexChordLogKernel, realChordLogKernel_standard]
      congr 1
    _ = (Real.log (Real.sqrt p) : ℂ) := by
      exact_mod_cast sum_log_chord (p := p)

theorem sum_complexChordLogKernel_ne_zero :
    (∑ g : RealResidueGroup p,
      complexChordLogKernel (p := p) g) ≠ 0 := by
  rw [sum_complexChordLogKernel]
  norm_cast
  apply ne_of_gt
  apply Real.log_pos
  have hsqrt_nonneg : 0 ≤ Real.sqrt p := Real.sqrt_nonneg _
  have hsqrt_sq : Real.sqrt p ^ 2 = p :=
    Real.sq_sqrt (by positivity)
  have hpgt : 2 < p := Fact.out
  have hpgtR : (2 : ℝ) < p := by exact_mod_cast hpgt
  nlinarith

theorem prod_nontrivial_fourierCoefficient_eq_signed_cofactorDet :
    (∏ χ : {χ : RealResidueGroup p →* ℂˣ // χ ≠ 1},
        fourierCoefficient (complexChordLogKernel (p := p)) χ) =
      (-1 : ℂ) ^ (omittedInverseIndex (p := p)).val *
        (logarithmicCofactor (p := p)).det := by
  have hall := prod_fourierCoefficient_eq_augmentation_mul_cofactor
    (standardRealResiduesEquiv (p := p))
    (complexChordLogKernel (p := p))
    (omittedInverseIndex (p := p))
  rw [Fintype.prod_eq_mul_prod_subtype_ne,
    fourierCoefficient_one,
    standardRealResiduesEquiv_symm_one] at hall
  apply mul_left_cancel₀
    (sum_complexChordLogKernel_ne_zero (p := p))
  calc
    (∑ g : RealResidueGroup p,
      complexChordLogKernel (p := p) g) *
      ∏ χ : {χ : RealResidueGroup p →* ℂˣ // χ ≠ 1},
        fourierCoefficient (complexChordLogKernel (p := p)) χ =
      (-1 : ℂ) ^ (omittedInverseIndex (p := p)).val *
        (∑ g : RealResidueGroup p,
          complexChordLogKernel (p := p) g) *
        (logarithmicCofactor (p := p)).det := by
      simpa [logarithmicCofactor] using hall
    _ = (∑ g : RealResidueGroup p,
        complexChordLogKernel (p := p) g) *
      ((-1 : ℂ) ^ (omittedInverseIndex (p := p)).val *
        (logarithmicCofactor (p := p)).det) := by ring

theorem norm_logSineDifferenceDet_eq_norm_prod_nontrivial_fourierCoefficient :
    ‖((logSineDifferenceMatrix (p := p)).det : ℂ)‖ =
      ‖∏ χ : {χ : RealResidueGroup p →* ℂˣ // χ ≠ 1},
        fourierCoefficient (complexChordLogKernel (p := p)) χ‖ := by
  rw [← inverseAlignedLogarithmicCofactor_det_eq_logSineDifferenceDet,
    inverseAlignedLogarithmicCofactor_det_eq_sign_mul_cofactorDet,
    prod_nontrivial_fourierCoefficient_eq_signed_cofactorDet]
  simp only [norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, one_mul]
  rw [Complex.norm_intCast, abs_unit_intCast, one_mul]

theorem abs_explicitSineDet_eq_pow_mul_norm_prod_nontrivial_fourierCoefficient :
    |(explicitSineMatrix (p := p)).det| =
      (2 : ℝ) ^ r *
        ‖∏ χ : {χ : RealResidueGroup p →* ℂˣ // χ ≠ 1},
          fourierCoefficient (complexChordLogKernel (p := p)) χ‖ := by
  rw [explicitSineMatrix_det_eq_pow_mul_logDifferenceDet,
    abs_mul, abs_pow]
  have habs : |(2 : ℝ)| = 2 := by norm_num
  rw [habs]
  rw [← norm_logSineDifferenceDet_eq_norm_prod_nontrivial_fourierCoefficient]
  rw [Complex.norm_real, Real.norm_eq_abs]

end

end Fermat.Irregular.CyclotomicLogCofactorPrime
