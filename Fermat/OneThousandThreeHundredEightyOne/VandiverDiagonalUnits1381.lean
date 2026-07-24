import Fermat.Irregular.VandiverDiagonalLogDerivative
import Fermat.Irregular.VandiverFiniteIndex
import Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalUnitResidues1381

/-!
# Vandiver's diagonal real-unit family at exponent 1381

This module realizes the integral diagonal family

`epsilon(w) = w^1055 * (w^653 - 1) / (w - 1)`.

The corrected source range is `j = 0, ..., 689`; the positive weight at
source index `i+1` is

`653^(1381^2 - 2*(i+1)*j)`.

Finite index is proved without a dense inverse table. The auxiliary-prime
evaluation matrix factors as the existing circular-unit matrix (with its
columns cyclically reordered) times the scaled Vandermonde matrix certified
in `VandiverDiagonalUnitResidues1381`.
-/

open scoped NumberField

namespace Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalUnits

noncomputable section

open Fermat.Irregular
open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitIndex
open Fermat.Irregular.CircularUnitResidues
open Fermat.Irregular.CircularUnitResidues.Certificate
open Fermat.Irregular.CircularUnits
open Fermat.Irregular.VandiverDiagonalLogDerivative
open Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalArithmetic
open Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalUnitResidues
open NumberField NumberField.Units

local instance : Fact (Nat.Prime 1381) :=
  ⟨Fermat.OneThousandThreeHundredEightyOne.prime_1381⟩
local instance : Fact (Nat.Prime 38669) :=
  ⟨Fermat.OneThousandThreeHundredEightyOne.prime_38669⟩

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The corrected source range `j = 0, ..., 689`. -/
abbrev VandiverFactorIndex1381 := Fin 690

theorem card_vandiverFactorIndex1381 :
    Fintype.card VandiverFactorIndex1381 = 690 := by decide

/-- The power of the chosen root occurring in the `j`th conjugate. -/
def conjugateExponent1381 (j : VandiverFactorIndex1381) : ℕ :=
  VandiverDiagonalUnitResidues.conjugateExponent1381 j

/-- Vandiver's literal positive integral weight. -/
def diagonalWeight1381 (i : Fin 689) (j : VandiverFactorIndex1381) : ℕ :=
  integralDiagonalWeight 1381 teichmullerRoot1381 (i.val + 1) j.val

theorem diagonalWeight1381_eq (i : Fin 689) (j : VandiverFactorIndex1381) :
    diagonalWeight1381 i j =
      653 ^ (1381 ^ 2 - 2 * (i.val + 1) * j.val) := by
  rfl

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {1381} ℚ K] [NumberField.IsCMField K]

omit [NumberField K] [IsCyclotomicExtension {1381} ℚ K]
    [NumberField.IsCMField K] in
theorem conjugate_isPrimitive {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1381)
    (j : VandiverFactorIndex1381) :
    IsPrimitiveRoot (zeta ^ conjugateExponent1381 j) 1381 := by
  apply hzeta.pow_of_coprime
  exact (by norm_num : Nat.Coprime 653 1381).pow_left j.val

/-- The literal basic factor of geometric length `653`. -/
def basicVandiverUnit1381 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1381)
    (j : VandiverFactorIndex1381) : (RingOfIntegers K)ˣ :=
  normalizedCircularUnit (p := 1381) (a := 653)
    (conjugate_isPrimitive hzeta j) (by norm_num) (by norm_num) 1055

omit [NumberField K] [IsCyclotomicExtension {1381} ℚ K]
    [NumberField.IsCMField K] in
theorem conjugate_toInteger {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1381)
    (j : VandiverFactorIndex1381) :
    (conjugate_isPrimitive hzeta j).toInteger =
      hzeta.toInteger ^ conjugateExponent1381 j := by
  apply RingOfIntegers.ext
  rfl

omit [IsCyclotomicExtension {1381} ℚ K] in
theorem basicVandiverUnit1381_mem_realUnits {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1381)
    (j : VandiverFactorIndex1381) :
    basicVandiverUnit1381 hzeta j ∈
      NumberField.IsCMField.realUnits K := by
  apply normalizedCircularUnit_mem_realUnits
    (p := 1381) (a := 653) (e := 1055)
  decide

/-- The ambient integral diagonal unit `(E_(i+1)(zeta))^rho`. -/
def diagonalVandiverUnit1381 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1381) (i : Fin 689) :
    (RingOfIntegers K)ˣ :=
  ∏ j : VandiverFactorIndex1381,
    basicVandiverUnit1381 hzeta j ^ diagonalWeight1381 i j

omit [IsCyclotomicExtension {1381} ℚ K] in
theorem diagonalVandiverUnit1381_mem_realUnits {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1381) (i : Fin 689) :
    diagonalVandiverUnit1381 hzeta i ∈
      NumberField.IsCMField.realUnits K := by
  apply Subgroup.prod_mem
  intro j hj
  exact Subgroup.pow_mem _
    (basicVandiverUnit1381_mem_realUnits hzeta j) _

/-- The 689 source units in the real-unit subgroup. -/
def diagonalVandiverUnitFamily1381 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1381) :
    Fin 689 → NumberField.IsCMField.realUnits K :=
  fun i ↦ ⟨diagonalVandiverUnit1381 hzeta i,
    diagonalVandiverUnit1381_mem_realUnits hzeta i⟩

omit [IsCyclotomicExtension {1381} ℚ K] in
@[simp]
theorem diagonalVandiverUnitFamily1381_coe {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1381) (i : Fin 689) :
    ((diagonalVandiverUnitFamily1381 hzeta i :
      NumberField.IsCMField.realUnits K) : (RingOfIntegers K)ˣ) =
      diagonalVandiverUnit1381 hzeta i := rfl

/-! ## Evaluation of the actual units -/

omit [NumberField.IsCMField K] in
theorem reductionHom_basicVandiverUnit1381 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1381) (row : Fin 689)
    (j : VandiverFactorIndex1381) :
    certificate1381.reductionHom hzeta row
        (basicVandiverUnit1381 hzeta j : RingOfIntegers K) =
      basicResidueValue1381 row j := by
  unfold basicVandiverUnit1381
  rw [normalizedCircularUnit_val]
  rw [conjugate_toInteger (hzeta := hzeta) j]
  simp only [map_mul, map_pow, map_sum, certificate1381.reductionHom_zeta]
  rfl

omit [IsCyclotomicExtension {1381} ℚ K] in
@[simp]
theorem realUnitNorm_basicVandiverUnit1381 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1381)
    (j : VandiverFactorIndex1381) :
    realUnitNorm (basicVandiverUnit1381 hzeta j) =
      basicVandiverUnit1381 hzeta j ^ 2 := by
  change basicVandiverUnit1381 hzeta j *
    NumberField.IsCMField.unitsComplexConj K
      (basicVandiverUnit1381 hzeta j) = _
  rw [(NumberField.IsCMField.unitsComplexConj_eq_self_iff K _).mpr
    (basicVandiverUnit1381_mem_realUnits hzeta j)]
  exact (pow_two _).symm

theorem correctedResidueLog_basicVandiverUnit1381 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1381) (row : Fin 689)
    (j : VandiverFactorIndex1381) :
    certificate1381.correctedResidueLog hzeta row
        (Additive.ofMul (basicVandiverUnit1381 hzeta j)) =
      basicEdgeSymbol1381 row j := by
  let u : (ZMod 38669)ˣ :=
    Units.map (certificate1381.reductionHom hzeta row)
      (realUnitNorm (basicVandiverUnit1381 hzeta j))
  have huval : (u : ZMod 38669) = basicResidueValue1381 row j ^ 2 := by
    dsimp [u]
    rw [realUnitNorm_basicVandiverUnit1381, Units.val_pow_eq_pow_val,
      map_pow, reductionHom_basicVandiverUnit1381]
  have hpow :
      ((u : ZMod 38669) ^ certificate1381.symbolExponent) =
      certificate1381.root ^ ((basicEdgeSymbol1381 row j).val * 2) := by
    change (u : ZMod 38669) ^ 28 =
      certificate1381.root ^ ((basicEdgeSymbol1381 row j).val * 2)
    calc
      (u : ZMod 38669) ^ 28 =
          (basicResidueValue1381 row j ^ 2) ^ 28 := by rw [huval]
      _ = (basicResidueValue1381 row j ^ 28) ^ 2 := by
        simp only [← pow_mul]
      _ = (certificate1381.root ^
          (basicEdgeSymbol1381 row j).val) ^ 2 := by
        rw [basicResidueValue1381_symbol]
      _ = certificate1381.root ^
          ((basicEdgeSymbol1381 row j).val * 2) := by rw [pow_mul]
  change (2 : ZMod 1381)⁻¹ *
      certificate1381.residueLog (Additive.ofMul u) =
    basicEdgeSymbol1381 row j
  rw [certificate1381.residueLog_eq_of_pow_eq u _ hpow]
  rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  have hhalf : (2 : ZMod 1381)⁻¹ * 2 = 1 :=
    inv_mul_cancel₀ (by
      intro h
      have hdiv : 1381 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 1381).mp h
      norm_num at hdiv)
  calc
    (2 : ZMod 1381)⁻¹ * (basicEdgeSymbol1381 row j * 2) =
        (2⁻¹ * 2) * basicEdgeSymbol1381 row j := by ring
    _ = basicEdgeSymbol1381 row j := by rw [hhalf, one_mul]

@[simp]
theorem quotientResidueLinear_basicVandiverUnit1381 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1381) (row : Fin 689)
    (j : VandiverFactorIndex1381) :
    certificate1381.quotientResidueLinear hzeta row
        (classOfUnit (basicVandiverUnit1381 hzeta j)) =
      basicEdgeSymbol1381 row j := by
  change certificate1381.quotientResidueLog hzeta row
    (classOfUnit (basicVandiverUnit1381 hzeta j)) = _
  rw [certificate1381.quotientResidueLog_classOfUnit]
  exact correctedResidueLog_basicVandiverUnit1381 hzeta row j

omit [NumberField K] [IsCyclotomicExtension {1381} ℚ K]
    [NumberField.IsCMField K] in
private theorem classOfUnit_prod_pow {I : Type*} [Fintype I]
    (u : I → (RingOfIntegers K)ˣ) (e : I → ℕ) :
    classOfUnit (∏ i, u i ^ e i) =
      ∑ i, e i • classOfUnit (u i) := by
  change Additive.ofMul
      ((QuotientGroup.mk' (NumberField.Units.torsion K))
        (∏ i, u i ^ e i)) = _
  rw [map_prod]
  change (∑ i, Additive.ofMul
    ((QuotientGroup.mk' (NumberField.Units.torsion K)) (u i ^ e i))) = _
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_pow]
  rfl

/-- Vandiver's positive weight reduced modulo `1381`. -/
def weightMod1381 (i : Fin 689) (j : VandiverFactorIndex1381) : ZMod 1381 :=
  (teichmullerRoot1381 : ZMod 1381) ^
    (1381 ^ 2 - 2 * (i.val + 1) * j.val)

theorem diagonalWeight1381_cast (i : Fin 689)
    (j : VandiverFactorIndex1381) :
    (diagonalWeight1381 i j : ZMod 1381) =
      weightMod1381 i j := by
  simp [diagonalWeight1381, integralDiagonalWeight, weightMod1381]

theorem quotientResidueLinear_diagonalVandiverUnit1381_formula
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 1381)
    (row i : Fin 689) :
    certificate1381.quotientResidueLinear hzeta row
        (classOfUnit (diagonalVandiverUnit1381 hzeta i)) =
      ∑ j : VandiverFactorIndex1381,
        weightMod1381 i j * basicEdgeSymbol1381 row j := by
  rw [diagonalVandiverUnit1381, classOfUnit_prod_pow]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_nsmul, quotientResidueLinear_basicVandiverUnit1381]
  simp only [nsmul_eq_mul]
  rw [diagonalWeight1381_cast]

/-! ## Algebraic Fourier factorization -/

theorem cycleClassSymbol1381_zero (row : Fin 689) :
    cycleClassSymbol1381 row 0 = 0 := by
  simp [cycleClassSymbol1381]

theorem cycleClassSymbol1381_succ (row j : Fin 689) :
    cycleClassSymbol1381 row (j.val + 1) =
      Fermat.OneThousandThreeHundredEightyOne.CircularUnitMatrix.matrix row
        (cycleColumn1381 j) := by
  rw [cycleClassSymbol1381, dif_pos]
  · congr
  · omega

theorem cycleClassSymbol1381_last (row : Fin 689) :
    cycleClassSymbol1381 row 690 = 0 := by
  simp [cycleClassSymbol1381]

theorem weighted_edge_sum1381 (row : Fin 689)
    (w : Fin 690 → ZMod 1381) :
    (∑ j : Fin 690, w j * basicEdgeSymbol1381 row j) =
      ∑ ell : Fin 689,
        Fermat.OneThousandThreeHundredEightyOne.CircularUnitMatrix.matrix row
            (cycleColumn1381 ell) *
          (w ell.castSucc - w ell.succ) := by
  simp_rw [basicEdgeSymbol1381, mul_sub]
  rw [Finset.sum_sub_distrib]
  have hfirst :
      (∑ j : Fin 690, w j * cycleClassSymbol1381 row (j.val + 1)) =
        ∑ ell : Fin 689,
          w ell.castSucc *
            Fermat.OneThousandThreeHundredEightyOne.CircularUnitMatrix.matrix row
              (cycleColumn1381 ell) := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, cycleClassSymbol1381_succ, Fin.val_last]
    rw [show 689 + 1 = 690 by norm_num, cycleClassSymbol1381_last,
      mul_zero, add_zero]
  have hsecond :
      (∑ j : Fin 690, w j * cycleClassSymbol1381 row j.val) =
        ∑ ell : Fin 689,
          w ell.succ *
            Fermat.OneThousandThreeHundredEightyOne.CircularUnitMatrix.matrix row
              (cycleColumn1381 ell) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, cycleClassSymbol1381_zero, mul_zero, zero_add,
      Fin.val_succ, cycleClassSymbol1381_succ]
  rw [hfirst, hsecond, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ell _
  ring

theorem weightMod1381_castSucc_sub_succ (ell i : Fin 689) :
    weightMod1381 i ell.castSucc - weightMod1381 i ell.succ =
      fourierChange1381 ell i := by
  let r : ZMod 1381 := teichmullerRoot1381
  let n := i.val + 1
  let L := ell.val + 1
  have hn : n ≤ 689 := by simp [n]
  have hL : L ≤ 689 := by simp [L]
  have hn2 : 2 * n ≤ 1380 := by omega
  have hpositive : 2 * n * L ≤ 1381 ^ 2 := by
    calc
      2 * n * L ≤ 2 * 689 * 689 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn) hL
      _ ≤ 1381 ^ 2 := by norm_num
  have hsplit :
      (1380 - 2 * n) * L = 1380 * L - 2 * n * L :=
    Nat.sub_mul 1380 (2 * n) L
  have hdecomp :
      1381 ^ 2 - 2 * n * L =
        1 + (1380 - 2 * n) * L + 1380 * (1382 - L) := by
    rw [hsplit]
    have hwithin : 2 * n * L ≤ 1380 * L :=
      Nat.mul_le_mul_right L hn2
    omega
  have hr1380 : r ^ 1380 = 1 :=
    teichmullerRoot1381_isPrimitive.pow_eq_one
  have hsecond :
      r ^ (1381 ^ 2 - 2 * n * L) =
        r * (r ^ (1380 - 2 * n)) ^ L := by
    rw [hdecomp, pow_add, pow_add]
    rw [show r ^ 1 = r by simp,
      show r ^ ((1380 - 2 * n) * L) =
          (r ^ (1380 - 2 * n)) ^ L by rw [pow_mul],
      show r ^ (1380 * (1382 - L)) = 1 by
        rw [pow_mul, hr1380, one_pow]]
    simp
  have hstep :
      2 * n * L = 2 * n * ell.val + 2 * n := by
    simp only [L]
    ring
  have hfirstExp :
      1381 ^ 2 - 2 * n * ell.val =
        (1381 ^ 2 - 2 * n * L) + 2 * n := by
    have hfirstBound : 2 * n * ell.val ≤ 1381 ^ 2 := by
      calc
        2 * n * ell.val ≤ 2 * n * L :=
          Nat.mul_le_mul_left (2 * n) (by simp [L])
        _ ≤ 1381 ^ 2 := hpositive
    omega
  rw [weightMod1381]
  change r ^ (1381 ^ 2 - 2 * n * ell.val) -
      r ^ (1381 ^ 2 - 2 * n * L) = fourierChange1381 ell i
  rw [hfirstExp, pow_add, hsecond, fourierChange1381_apply]
  simp only [vandermondeNode1381, fourierScale1381, n, L, r]
  rw [show 1378 - 2 * i.val = 1380 - 2 * (i.val + 1) by omega]
  rw [show ell.val + 1 = L by rfl]
  ring

noncomputable def cycleCircularMatrix1381 :
    Matrix (Fin 689) (Fin 689) (ZMod 1381) :=
  Fermat.OneThousandThreeHundredEightyOne.CircularUnitMatrix.matrix.submatrix id
    cycleColumnEquiv1381

theorem cycleCircularMatrix1381_det_ne_zero :
    cycleCircularMatrix1381.det ≠ 0 := by
  rw [cycleCircularMatrix1381, Matrix.det_permute']
  exact mul_ne_zero
    (by
      exact ((Equiv.Perm.sign cycleColumnEquiv1381).isUnit.map
        (Int.castRingHom (ZMod 1381))).ne_zero)
    Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate.matrix_det_ne_zero

/-- The actual diagonal residue matrix, factored into its circular and
Fourier components. -/
noncomputable def diagonalResidueMatrix1381 :
    Matrix (Fin 689) (Fin 689) (ZMod 1381) :=
  cycleCircularMatrix1381 * fourierChange1381

theorem diagonalResidueMatrix1381_det_ne_zero :
    diagonalResidueMatrix1381.det ≠ 0 := by
  rw [diagonalResidueMatrix1381, Matrix.det_mul]
  exact mul_ne_zero cycleCircularMatrix1381_det_ne_zero
    fourierChange1381_det_ne_zero

theorem weighted_edge_sum1381_eq_matrix (row i : Fin 689) :
    (∑ j : Fin 690, weightMod1381 i j * basicEdgeSymbol1381 row j) =
      diagonalResidueMatrix1381 row i := by
  rw [weighted_edge_sum1381]
  simp_rw [weightMod1381_castSucc_sub_succ]
  rfl

@[simp]
theorem quotientResidueLinear_diagonalVandiverUnit1381 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1381) (row i : Fin 689) :
    certificate1381.quotientResidueLinear hzeta row
        (classOfUnit (diagonalVandiverUnit1381 hzeta i)) =
      diagonalResidueMatrix1381 row i := by
  rw [quotientResidueLinear_diagonalVandiverUnit1381_formula]
  exact weighted_edge_sum1381_eq_matrix row i

theorem evalMatrix_diagonalVandiverUnit1381 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1381) :
    evalMatrix (classOfUnit ∘ diagonalVandiverUnit1381 hzeta)
        (certificate1381.residueFunctionals hzeta) =
      diagonalResidueMatrix1381 := by
  ext row i
  exact quotientResidueLinear_diagonalVandiverUnit1381 hzeta row i

theorem not_dvd_diagonalVandiverUnit1381_full_index {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1381) :
    ¬1381 ∣
      (Subgroup.closure (Set.range (diagonalVandiverUnit1381 hzeta)) ⊔
        NumberField.Units.torsion K).index := by
  apply not_dvd_unitIndex_of_eval_det_ne_zero
    (certificate1381.basisModTorsion (K := K))
      (diagonalVandiverUnit1381 hzeta)
      (certificate1381.residueFunctionals hzeta)
  rw [evalMatrix_diagonalVandiverUnit1381]
  exact diagonalResidueMatrix1381_det_ne_zero

theorem ambient_closure_finiteIndex {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1381) :
    (Subgroup.closure
      (Set.range (diagonalVandiverUnit1381 hzeta))).FiniteIndex := by
  have hnot := not_dvd_diagonalVandiverUnit1381_full_index hzeta
  have hsup :
      (Subgroup.closure (Set.range (diagonalVandiverUnit1381 hzeta)) ⊔
        NumberField.Units.torsion K).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff]
    intro hzero
    apply hnot
    rw [hzero]
    exact dvd_zero 1381
  exact (NumberField.Units.finiteIndex_iff_sup_torsion_finiteIndex
    (Subgroup.closure (Set.range
      (diagonalVandiverUnit1381 hzeta)))).2 hsup

theorem real_closure_finiteIndex {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1381) :
    (Subgroup.closure
      (Set.range (diagonalVandiverUnitFamily1381 hzeta))).FiniteIndex := by
  letI :
      (Subgroup.closure (Set.range fun i : Fin 689 ↦
        ((diagonalVandiverUnitFamily1381 hzeta i :
          NumberField.IsCMField.realUnits K) :
            (RingOfIntegers K)ˣ))).FiniteIndex := by
    simpa [diagonalVandiverUnitFamily1381] using
      ambient_closure_finiteIndex hzeta
  exact Fermat.Irregular.VandiverFiniteIndex.closure_range_subtype
    (NumberField.IsCMField.realUnits K)
      (diagonalVandiverUnitFamily1381 hzeta)

end

end Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalUnits
