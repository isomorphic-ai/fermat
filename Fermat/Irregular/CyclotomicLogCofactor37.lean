import Fermat.Irregular.CyclotomicLogDet
import Fermat.Irregular.CyclotomicSineProduct37

/-!
# The fixed exponent-37 sine determinant as a Fourier cofactor

This file closes the finite algebraic seam between the canonical `17 × 17` logarithmic sine
matrix and the character-factorization of the real residue group.  The chord logarithm descends
from `(ZMod 37)ˣ` to the quotient by `{1, -1}`.  After deleting the identity row and the inverse
of the omitted column, the augmentation cofactor becomes the fixed sine-difference matrix, up to
the harmless permutation sign.

Consequently the absolute fixed circular regulator is `2^17` times the norm of the product of
the seventeen nontrivial Fourier coefficients.  Identifying those coefficients with the relevant
Dirichlet `L`-values is the remaining analytic input to the Sinnott--Kummer index formula.
-/

open scoped Classical BigOperators

namespace Fermat.Irregular.CyclotomicLogCofactor37

noncomputable section

open Fermat.Irregular.CyclotomicLogDet
open Fermat.Irregular.CyclotomicPlaces37
open Fermat.Irregular.CyclotomicSineProduct37

local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance : Fintype (RealResidueGroup37 →* ℂˣ) := Fintype.ofFinite _

/-- The standard complex primitive root, regarded as a unit. -/
def etaUnit37 : ℂˣ := Units.mk0 eta37 (eta37_primitive.ne_zero (by norm_num))

theorem etaUnit37_primitive : IsPrimitiveRoot etaUnit37 37 := by
  rw [← IsPrimitiveRoot.coe_units_iff]
  exact eta37_primitive

theorem etaUnit37_pow_val (a : ZMod 37) :
    (((etaUnit37_primitive.zmodEquivZPowers a).toMul :
      Subgroup.zpowers etaUnit37) : ℂˣ) = etaUnit37 ^ a.val := by
  have h := etaUnit37_primitive.zmodEquivZPowers_apply_coe_nat a.val
  rw [ZMod.natCast_zmod_val] at h
  exact congrArg
    (fun z : Additive (Subgroup.zpowers etaUnit37) ↦
      ((z.toMul : Subgroup.zpowers etaUnit37) : ℂˣ)) h

theorem eta37_pow_neg_val (a : ZMod 37) :
    eta37 ^ (-a).val = (eta37 ^ a.val)⁻¹ := by
  have hmap := map_neg etaUnit37_primitive.zmodEquivZPowers a
  have hunit : etaUnit37 ^ (-a).val = (etaUnit37 ^ a.val)⁻¹ := by
    rw [← etaUnit37_pow_val (-a), ← etaUnit37_pow_val a]
    exact congrArg
      (fun z : Additive (Subgroup.zpowers etaUnit37) ↦
        ((z.toMul : Subgroup.zpowers etaUnit37) : ℂˣ)) hmap
  simpa [etaUnit37, Units.val_inv_eq_inv_val] using congrArg Units.val hunit

/-- Logarithm of the cyclotomic chord attached to a nonzero residue class. -/
def unitChordLog37 (u : (ZMod 37)ˣ) : ℝ :=
  Real.log ‖1 - eta37 ^ (u : ZMod 37).val‖

theorem unitChordLog37_neg (u : (ZMod 37)ˣ) : unitChordLog37 (-u) = unitChordLog37 u := by
  simp only [unitChordLog37, Units.val_neg]
  rw [eta37_pow_neg_val]
  congr 1
  rw [Fermat.Irregular.CyclotomicSineProduct37.norm_one_sub_inv_of_norm_one]
  rw [norm_pow, Complex.norm_eq_one_of_pow_eq_one
    eta37_primitive.pow_eq_one (by norm_num), one_pow]

/-- The chord logarithm on the maximal-real residue group `(ZMod 37)ˣ / {±1}`. -/
def realChordLogKernel37 : RealResidueGroup37 → ℝ :=
  Quotient.lift unitChordLog37 (by
    intro u v huv
    have hmem : u / v ∈ signSubgroup37 :=
      QuotientGroup.eq_iff_div_mem.mp (Quotient.sound huv)
    rw [signSubgroup37_mem_iff] at hmem
    rcases hmem with h | h
    · have huv' : u = v := div_eq_one.mp h
      rw [huv']
    · have huv' : u = -v := by
        calc
          u = (u / v) * v := (div_mul_cancel _ _).symm
          _ = (-1) * v := by rw [h]
          _ = -v := by simp
      have hvu : v = -u := by rw [huv', neg_neg]
      rw [hvu, unitChordLog37_neg])

theorem realChordLogKernel37_mk (u : (ZMod 37)ˣ) :
    realChordLogKernel37 (QuotientGroup.mk u) = unitChordLog37 u := rfl

theorem eta37_pow_val_eq_pow_of_coe_eq (a : ZMod 37) (m : ℕ)
    (h : a = (m : ZMod 37)) : eta37 ^ a.val = eta37 ^ m := by
  apply pow_eq_pow_of_modEq _ eta37_primitive.pow_eq_one
  apply (ZMod.natCast_eq_natCast_iff a.val m 37).mp
  rw [ZMod.natCast_zmod_val, h]

theorem standardUnit37_coe (j : Fin 18) :
    (standardUnit37 j : ZMod 37) = (j.val + 1 : ℕ) := by
  exact ZMod.coe_unitOfCoprime _ _

theorem unitChordLog37_standardUnit (j : Fin 18) :
    unitChordLog37 (standardUnit37 j) = Real.log (chord37 j) := by
  rw [unitChordLog37]
  rw [eta37_pow_val_eq_pow_of_coe_eq _ _ (standardUnit37_coe j)]
  rw [chord37_eq_norm]
  rfl

/-- Twice the absolute sine at the rational angle `pi * m / 37`. -/
def sineChordNat37 (m : ℕ) : ℝ :=
  2 * |Real.sin (Real.pi * ((m : ℝ) / (37 : ℝ)))|

theorem standardUnit37_mul_coe (a k : Fin 18) :
    ((standardUnit37 a * standardUnit37 k : (ZMod 37)ˣ) : ZMod 37) =
      (((a.val + 1) * (k.val + 1) : ℕ) : ZMod 37) := by
  rw [Units.val_mul, standardUnit37_coe, standardUnit37_coe]
  norm_num

theorem unitChordLog37_standardUnit_mul (a k : Fin 18) :
    unitChordLog37 (standardUnit37 a * standardUnit37 k) =
      Real.log (sineChordNat37 ((a.val + 1) * (k.val + 1))) := by
  rw [unitChordLog37]
  rw [eta37_pow_val_eq_pow_of_coe_eq _ _ (standardUnit37_mul_coe a k)]
  change Real.log
      ‖1 - Complex.exp (2 * Real.pi * Complex.I *
        (((1 : ℕ) : ℂ) / ((37 : ℕ) : ℂ))) ^
          ((a.val + 1) * (k.val + 1))‖ = _
  rw [Fermat.Irregular.CyclotomicZeta.norm_one_sub_exp_two_pi_I_pow]
  simp only [sineChordNat37, Nat.cast_one, Nat.cast_ofNat, Nat.cast_mul]
  congr 3
  ring_nf

/-- The permutation induced by inversion on the fixed enumeration of real residue classes. -/
def inverseIndex37 : Equiv.Perm (Fin 18) :=
  (standardRealResiduesEquiv37.trans (Equiv.inv RealResidueGroup37)).trans
    standardRealResiduesEquiv37.symm

@[simp] theorem standardRealResiduesEquiv37_inverseIndex37 (j : Fin 18) :
    standardRealResiduesEquiv37 (inverseIndex37 j) =
      (standardRealResiduesEquiv37 j)⁻¹ := by
  simp [inverseIndex37]

/-- The inverse-class column deleted from the augmentation cofactor. -/
def omittedInverseIndex37 : Fin 18 :=
  inverseIndex37 (Fin.last 17)

def inverseColumnsEquiv37 :
    Fin 17 ≃ {j : Fin 18 // j ≠ omittedInverseIndex37} :=
  (finSuccAboveEquiv (Fin.last 17)).trans
    (Equiv.subtypeEquiv inverseIndex37 fun j ↦ by
      change j ≠ Fin.last 17 ↔
        inverseIndex37 j ≠ inverseIndex37 (Fin.last 17)
      exact (inverseIndex37.injective.ne_iff).symm)

theorem inverseColumnsEquiv37_apply (j : Fin 17) :
    (inverseColumnsEquiv37 j).val = inverseIndex37 j.castSucc := by
  simp [inverseColumnsEquiv37, finSuccAboveEquiv_apply]
  apply Fin.succAbove_of_castSucc_lt
  exact Fin.castSucc_lt_last _

/-- The permutation putting the remaining cofactor columns in inverse-residue order. -/
def inverseColumnReindex37 : Equiv.Perm (Fin 17) :=
  inverseColumnsEquiv37.trans (finSuccAboveEquiv omittedInverseIndex37).symm

theorem succAbove_inverseColumnReindex37_apply (j : Fin 17) :
    Fin.succAbove omittedInverseIndex37 (inverseColumnReindex37 j) =
      inverseIndex37 j.castSucc := by
  calc
    Fin.succAbove omittedInverseIndex37 (inverseColumnReindex37 j) =
        ((finSuccAboveEquiv omittedInverseIndex37)
          (inverseColumnReindex37 j)).val := rfl
    _ = (inverseColumnsEquiv37 j).val := by
      simp [inverseColumnReindex37]
    _ = inverseIndex37 j.castSucc := inverseColumnsEquiv37_apply j

theorem realChordLogKernel37_standard_mul (a k : Fin 18) :
    realChordLogKernel37
        (standardRealResiduesEquiv37 a * standardRealResiduesEquiv37 k) =
      Real.log (sineChordNat37 ((a.val + 1) * (k.val + 1))) := by
  rw [standardRealResiduesEquiv37_apply, standardRealResiduesEquiv37_apply]
  change realChordLogKernel37
      (QuotientGroup.mk (standardUnit37 a * standardUnit37 k)) = _
  rw [realChordLogKernel37_mk, unitChordLog37_standardUnit_mul]

theorem realChordLogKernel37_standard (k : Fin 18) :
    realChordLogKernel37 (standardRealResiduesEquiv37 k) =
      Real.log (sineChordNat37 (k.val + 1)) := by
  rw [standardRealResiduesEquiv37_apply]
  change unitChordLog37 (standardUnit37 k) = _
  rw [unitChordLog37_standardUnit]
  congr 1

def complexChordLogKernel37 (g : RealResidueGroup37) : ℂ :=
  realChordLogKernel37 g

/-- The augmentation cofactor with the identity row and omitted inverse column deleted. -/
def logarithmicCofactor37 : Matrix (Fin 17) (Fin 17) ℂ :=
  (augmentationDifferenceMatrix standardRealResiduesEquiv37 complexChordLogKernel37).submatrix
    (Fin.succAbove 0) (Fin.succAbove omittedInverseIndex37)

/-- The same cofactor, with columns arranged in the fixed sine-matrix order. -/
def inverseAlignedLogarithmicCofactor37 : Matrix (Fin 17) (Fin 17) ℂ :=
  logarithmicCofactor37.submatrix id inverseColumnReindex37

theorem inverseAlignedLogarithmicCofactor37_apply (i j : Fin 17) :
    inverseAlignedLogarithmicCofactor37 i j =
      (realChordLogKernel37
          (standardRealResiduesEquiv37 i.succ *
            standardRealResiduesEquiv37 j.castSucc) -
        realChordLogKernel37 (standardRealResiduesEquiv37 j.castSucc) : ℝ) := by
  rw [inverseAlignedLogarithmicCofactor37, logarithmicCofactor37]
  simp only [Matrix.submatrix_apply, id_eq]
  rw [succAbove_inverseColumnReindex37_apply]
  rw [augmentationDifferenceMatrix_apply]
  rw [standardRealResiduesEquiv37_symm_one]
  simp only [Fin.succAbove_zero, if_neg (Fin.succ_ne_zero i)]
  rw [standardRealResiduesEquiv37_inverseIndex37]
  simp only [inv_inv, complexChordLogKernel37]
  norm_cast

theorem log_sineChordNat37_sub (a k : ℕ)
    (hak : |Real.sin (Real.pi * (((a * k : ℕ) : ℝ) / 37))| ≠ 0)
    (hk : |Real.sin (Real.pi * ((k : ℝ) / 37))| ≠ 0) :
    Real.log (sineChordNat37 (a * k)) - Real.log (sineChordNat37 k) =
      Real.log |Real.sin (Real.pi * (((a * k : ℕ) : ℝ) / 37))| -
        Real.log |Real.sin (Real.pi * ((k : ℝ) / 37))| := by
  simp only [sineChordNat37]
  rw [Real.log_mul (by norm_num) hak, Real.log_mul (by norm_num) hk]
  ring

/-- The reindexed augmentation cofactor is exactly the complexification of the fixed
logarithmic sine-difference matrix. -/
theorem inverseAlignedLogarithmicCofactor37_eq_map_logSineDifference :
    inverseAlignedLogarithmicCofactor37 =
      logSineDifferenceMatrix37.map (algebraMap ℝ ℂ) := by
  ext i j
  rw [inverseAlignedLogarithmicCofactor37_apply]
  simp only [Matrix.map_apply, logSineDifferenceMatrix37, Matrix.of_apply]
  rw [Complex.coe_algebraMap]
  rw [Complex.ofReal_inj]
  rw [realChordLogKernel37_standard_mul, realChordLogKernel37_standard]
  let a := i.val + 2
  let k := j.val + 1
  have ha : ¬37 ∣ a := by
    intro h
    have hle := Nat.le_of_dvd (by omega : 0 < a) h
    omega
  have hk : ¬37 ∣ k := by
    intro h
    have hle := Nat.le_of_dvd (by omega : 0 < k) h
    omega
  have hak : ¬37 ∣ a * k := (by decide : Nat.Prime 37).not_dvd_mul ha hk
  have hsak : |Real.sin (Real.pi * (((a * k : ℕ) : ℝ) / 37))| ≠ 0 := by
    rw [abs_ne_zero]
    exact sin_pi_mul_div_37_ne_zero (a * k) hak
  have hsk : |Real.sin (Real.pi * ((k : ℝ) / 37))| ≠ 0 := by
    rw [abs_ne_zero]
    exact sin_pi_mul_div_37_ne_zero k hk
  change Real.log (sineChordNat37 (a * k)) - Real.log (sineChordNat37 k) = _
  rw [log_sineChordNat37_sub a k hsak hsk]
  dsimp [a, k]
  congr 2
  all_goals
    congr 2
    push_cast
    ring_nf

theorem inverseAlignedLogarithmicCofactor37_det_eq_logSineDifferenceDet :
    inverseAlignedLogarithmicCofactor37.det =
      (logSineDifferenceMatrix37.det : ℂ) := by
  rw [inverseAlignedLogarithmicCofactor37_eq_map_logSineDifference]
  exact (RingHom.map_det (algebraMap ℝ ℂ) logSineDifferenceMatrix37).symm

theorem inverseAlignedLogarithmicCofactor37_det_eq_sign_mul_cofactorDet :
    inverseAlignedLogarithmicCofactor37.det =
      (inverseColumnReindex37.sign : ℂ) * logarithmicCofactor37.det := by
  exact Matrix.det_permute' inverseColumnReindex37 logarithmicCofactor37

/-- The trivial-character factor is the logarithm of the classical half chord product. -/
theorem sum_complexChordLogKernel37 :
    (∑ g : RealResidueGroup37, complexChordLogKernel37 g) =
      (Real.log (Real.sqrt 37) : ℂ) := by
  calc
    (∑ g : RealResidueGroup37, complexChordLogKernel37 g) =
        ∑ j : Fin 18, complexChordLogKernel37
          (standardRealResiduesEquiv37 j) :=
      (Equiv.sum_comp standardRealResiduesEquiv37 complexChordLogKernel37).symm
    _ = ∑ j : Fin 18, (Real.log (chord37 j) : ℂ) := by
      apply Fintype.sum_congr
      intro j
      rw [complexChordLogKernel37, realChordLogKernel37_standard]
      congr 1
    _ = (Real.log (Real.sqrt 37) : ℂ) := by
      exact_mod_cast sum_log_chord37

theorem sum_complexChordLogKernel37_ne_zero :
    (∑ g : RealResidueGroup37, complexChordLogKernel37 g) ≠ 0 := by
  rw [sum_complexChordLogKernel37]
  norm_cast
  apply ne_of_gt
  apply Real.log_pos
  have hsqrt_nonneg : 0 ≤ Real.sqrt 37 := Real.sqrt_nonneg _
  have hsqrt_sq : Real.sqrt 37 ^ 2 = 37 := Real.sq_sqrt (by norm_num)
  nlinarith

/-- Removing the nonzero trivial Fourier factor leaves the signed augmentation cofactor. -/
theorem prod_nontrivial_fourierCoefficient_eq_signed_cofactorDet :
    (∏ χ : {χ : RealResidueGroup37 →* ℂˣ // χ ≠ 1},
        fourierCoefficient complexChordLogKernel37 χ) =
      (-1 : ℂ) ^ omittedInverseIndex37.val * logarithmicCofactor37.det := by
  have hall := prod_fourierCoefficient_eq_augmentation_mul_cofactor
    standardRealResiduesEquiv37 complexChordLogKernel37 omittedInverseIndex37
  rw [Fintype.prod_eq_mul_prod_subtype_ne, fourierCoefficient_one,
    standardRealResiduesEquiv37_symm_one] at hall
  apply mul_left_cancel₀ sum_complexChordLogKernel37_ne_zero
  calc
    (∑ g : RealResidueGroup37, complexChordLogKernel37 g) *
          ∏ χ : {χ : RealResidueGroup37 →* ℂˣ // χ ≠ 1},
            fourierCoefficient complexChordLogKernel37 χ =
        (-1 : ℂ) ^ omittedInverseIndex37.val *
          (∑ g : RealResidueGroup37, complexChordLogKernel37 g) *
            logarithmicCofactor37.det := by
      simpa [logarithmicCofactor37] using hall
    _ = (∑ g : RealResidueGroup37, complexChordLogKernel37 g) *
        ((-1 : ℂ) ^ omittedInverseIndex37.val * logarithmicCofactor37.det) := by
      ring

theorem norm_logSineDifferenceDet_eq_norm_prod_nontrivial_fourierCoefficient :
    ‖(logSineDifferenceMatrix37.det : ℂ)‖ =
      ‖∏ χ : {χ : RealResidueGroup37 →* ℂˣ // χ ≠ 1},
        fourierCoefficient complexChordLogKernel37 χ‖ := by
  rw [← inverseAlignedLogarithmicCofactor37_det_eq_logSineDifferenceDet,
    inverseAlignedLogarithmicCofactor37_det_eq_sign_mul_cofactorDet,
    prod_nontrivial_fourierCoefficient_eq_signed_cofactorDet]
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [Complex.norm_intCast]
  rw [abs_unit_intCast, one_mul]

/-- Final finite Fourier form of the canonical exponent-37 circular regulator determinant. -/
theorem abs_explicitSineDet_eq_pow_mul_norm_prod_nontrivial_fourierCoefficient :
    |explicitSineMatrix37.det| =
      (2 : ℝ) ^ 17 *
        ‖∏ χ : {χ : RealResidueGroup37 →* ℂˣ // χ ≠ 1},
          fourierCoefficient complexChordLogKernel37 χ‖ := by
  rw [explicitSineMatrix37_det_eq_pow_mul_logDifferenceDet, abs_mul, abs_pow]
  have habs : |(2 : ℝ)| = 2 := by norm_num
  rw [habs]
  rw [← norm_logSineDifferenceDet_eq_norm_prod_nontrivial_fourierCoefficient]
  rw [Complex.norm_real, Real.norm_eq_abs]

end
end Fermat.Irregular.CyclotomicLogCofactor37
