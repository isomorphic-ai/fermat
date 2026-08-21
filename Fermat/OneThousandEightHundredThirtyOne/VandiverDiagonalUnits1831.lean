import Fermat.Irregular.VandiverDiagonalLogDerivative
import Fermat.Irregular.VandiverFiniteIndex
import Fermat.OneThousandEightHundredThirtyOne.VandiverDiagonalUnitResidues1831

/-!
# Vandiver's diagonal real-unit family at exponent 1831

This module realizes the integral diagonal family

`epsilon(w) = w^374 * (w^4746 - 1) / (w - 1)`.

The corrected source range is `j = 0, ..., 914`; the positive weight at
source index `i+1` is

`4746^(1831^2 - 2*(i+1)*j)`.

Finite index is proved without a dense inverse table. The auxiliary-prime
evaluation matrix factors as the existing circular-unit matrix (with its
columns cyclically reordered) times the scaled Vandermonde matrix certified
in `VandiverDiagonalUnitResidues1831`.
-/

open scoped NumberField

namespace Fermat.OneThousandEightHundredThirtyOne.VandiverDiagonalUnits

noncomputable section

open Fermat.Irregular
open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitIndex
open Fermat.Irregular.CircularUnitResidues
open Fermat.Irregular.CircularUnitResidues.Certificate
open Fermat.Irregular.CircularUnits
open Fermat.Irregular.VandiverDiagonalLogDerivative
open Fermat.OneThousandEightHundredThirtyOne.VandiverDiagonalArithmetic
open Fermat.OneThousandEightHundredThirtyOne.VandiverDiagonalUnitResidues
open NumberField NumberField.Units

local instance : Fact (Nat.Prime 1831) :=
  ⟨Fermat.OneThousandEightHundredThirtyOne.prime_1831⟩
local instance : Fact (Nat.Prime 358877) :=
  ⟨Fermat.OneThousandEightHundredThirtyOne.prime_358877⟩

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The corrected source range `j = 0, ..., 914`. -/
abbrev VandiverFactorIndex1831 := Fin 915

theorem card_vandiverFactorIndex1831 :
    Fintype.card VandiverFactorIndex1831 = 915 := by decide

/-- The power of the chosen root occurring in the `j`th conjugate. -/
def conjugateExponent1831 (j : VandiverFactorIndex1831) : ℕ :=
  VandiverDiagonalUnitResidues.conjugateExponent1831 j

/-- Vandiver's literal positive integral weight. -/
def diagonalWeight1831 (i : Fin 914) (j : VandiverFactorIndex1831) : ℕ :=
  integralDiagonalWeight 1831 teichmullerRoot1831 (i.val + 1) j.val

theorem diagonalWeight1831_eq (i : Fin 914) (j : VandiverFactorIndex1831) :
    diagonalWeight1831 i j =
      4746 ^ (1831 ^ 2 - 2 * (i.val + 1) * j.val) := by
  rfl

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {1831} ℚ K] [NumberField.IsCMField K]

omit [NumberField K] [IsCyclotomicExtension {1831} ℚ K]
    [NumberField.IsCMField K] in
theorem conjugate_isPrimitive {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1831)
    (j : VandiverFactorIndex1831) :
    IsPrimitiveRoot (zeta ^ conjugateExponent1831 j) 1831 := by
  apply hzeta.pow_of_coprime
  exact (by norm_num : Nat.Coprime 4746 1831).pow_left j.val

/-- The literal basic factor of geometric length `4746`. -/
def basicVandiverUnit1831 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1831)
    (j : VandiverFactorIndex1831) : (RingOfIntegers K)ˣ :=
  normalizedCircularUnit (p := 1831) (a := 4746)
    (conjugate_isPrimitive hzeta j) (by norm_num) (by norm_num) 374

omit [NumberField K] [IsCyclotomicExtension {1831} ℚ K]
    [NumberField.IsCMField K] in
theorem conjugate_toInteger {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1831)
    (j : VandiverFactorIndex1831) :
    (conjugate_isPrimitive hzeta j).toInteger =
      hzeta.toInteger ^ conjugateExponent1831 j := by
  apply RingOfIntegers.ext
  rfl

omit [IsCyclotomicExtension {1831} ℚ K] in
theorem basicVandiverUnit1831_mem_realUnits {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1831)
    (j : VandiverFactorIndex1831) :
    basicVandiverUnit1831 hzeta j ∈
      NumberField.IsCMField.realUnits K := by
  apply normalizedCircularUnit_mem_realUnits
    (p := 1831) (a := 4746) (e := 374)
  decide

/-- The ambient integral diagonal unit `(E_(i+1)(zeta))^rho`. -/
def diagonalVandiverUnit1831 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1831) (i : Fin 914) :
    (RingOfIntegers K)ˣ :=
  ∏ j : VandiverFactorIndex1831,
    basicVandiverUnit1831 hzeta j ^ diagonalWeight1831 i j

omit [IsCyclotomicExtension {1831} ℚ K] in
theorem diagonalVandiverUnit1831_mem_realUnits {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1831) (i : Fin 914) :
    diagonalVandiverUnit1831 hzeta i ∈
      NumberField.IsCMField.realUnits K := by
  apply Subgroup.prod_mem
  intro j hj
  exact Subgroup.pow_mem _
    (basicVandiverUnit1831_mem_realUnits hzeta j) _

/-- The 914 source units in the real-unit subgroup. -/
def diagonalVandiverUnitFamily1831 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1831) :
    Fin 914 → NumberField.IsCMField.realUnits K :=
  fun i ↦ ⟨diagonalVandiverUnit1831 hzeta i,
    diagonalVandiverUnit1831_mem_realUnits hzeta i⟩

omit [IsCyclotomicExtension {1831} ℚ K] in
@[simp]
theorem diagonalVandiverUnitFamily1831_coe {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1831) (i : Fin 914) :
    ((diagonalVandiverUnitFamily1831 hzeta i :
      NumberField.IsCMField.realUnits K) : (RingOfIntegers K)ˣ) =
      diagonalVandiverUnit1831 hzeta i := rfl

/-! ## Evaluation of the actual units -/

omit [NumberField.IsCMField K] in
theorem reductionHom_basicVandiverUnit1831 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1831) (row : Fin 914)
    (j : VandiverFactorIndex1831) :
    certificate1831.reductionHom hzeta row
        (basicVandiverUnit1831 hzeta j : RingOfIntegers K) =
      basicResidueValue1831 row j := by
  unfold basicVandiverUnit1831
  rw [normalizedCircularUnit_val]
  rw [conjugate_toInteger (hzeta := hzeta) j]
  simp only [map_mul, map_pow, map_sum, certificate1831.reductionHom_zeta]
  rfl

omit [IsCyclotomicExtension {1831} ℚ K] in
@[simp]
theorem realUnitNorm_basicVandiverUnit1831 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1831)
    (j : VandiverFactorIndex1831) :
    realUnitNorm (basicVandiverUnit1831 hzeta j) =
      basicVandiverUnit1831 hzeta j ^ 2 := by
  change basicVandiverUnit1831 hzeta j *
    NumberField.IsCMField.unitsComplexConj K
      (basicVandiverUnit1831 hzeta j) = _
  rw [(NumberField.IsCMField.unitsComplexConj_eq_self_iff K _).mpr
    (basicVandiverUnit1831_mem_realUnits hzeta j)]
  exact (pow_two _).symm

theorem correctedResidueLog_basicVandiverUnit1831 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1831) (row : Fin 914)
    (j : VandiverFactorIndex1831) :
    certificate1831.correctedResidueLog hzeta row
        (Additive.ofMul (basicVandiverUnit1831 hzeta j)) =
      basicEdgeSymbol1831 row j := by
  let u : (ZMod 358877)ˣ :=
    Units.map (certificate1831.reductionHom hzeta row)
      (realUnitNorm (basicVandiverUnit1831 hzeta j))
  have huval : (u : ZMod 358877) = basicResidueValue1831 row j ^ 2 := by
    dsimp [u]
    rw [realUnitNorm_basicVandiverUnit1831, Units.val_pow_eq_pow_val,
      map_pow, reductionHom_basicVandiverUnit1831]
  have hpow :
      ((u : ZMod 358877) ^ certificate1831.symbolExponent) =
      certificate1831.root ^ ((basicEdgeSymbol1831 row j).val * 2) := by
    change (u : ZMod 358877) ^ 196 =
      certificate1831.root ^ ((basicEdgeSymbol1831 row j).val * 2)
    calc
      (u : ZMod 358877) ^ 196 =
          (basicResidueValue1831 row j ^ 2) ^ 196 := by rw [huval]
      _ = (basicResidueValue1831 row j ^ 196) ^ 2 := by
        simp only [← pow_mul]
      _ = (certificate1831.root ^
          (basicEdgeSymbol1831 row j).val) ^ 2 := by
        rw [basicResidueValue1831_symbol]
      _ = certificate1831.root ^
          ((basicEdgeSymbol1831 row j).val * 2) := by rw [pow_mul]
  change (2 : ZMod 1831)⁻¹ *
      certificate1831.residueLog (Additive.ofMul u) =
    basicEdgeSymbol1831 row j
  rw [certificate1831.residueLog_eq_of_pow_eq u _ hpow]
  rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  have hhalf : (2 : ZMod 1831)⁻¹ * 2 = 1 :=
    inv_mul_cancel₀ (by
      intro h
      have hdiv : 1831 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 1831).mp h
      norm_num at hdiv)
  calc
    (2 : ZMod 1831)⁻¹ * (basicEdgeSymbol1831 row j * 2) =
        (2⁻¹ * 2) * basicEdgeSymbol1831 row j := by ring
    _ = basicEdgeSymbol1831 row j := by rw [hhalf, one_mul]

@[simp]
theorem quotientResidueLinear_basicVandiverUnit1831 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1831) (row : Fin 914)
    (j : VandiverFactorIndex1831) :
    certificate1831.quotientResidueLinear hzeta row
        (classOfUnit (basicVandiverUnit1831 hzeta j)) =
      basicEdgeSymbol1831 row j := by
  change certificate1831.quotientResidueLog hzeta row
    (classOfUnit (basicVandiverUnit1831 hzeta j)) = _
  rw [certificate1831.quotientResidueLog_classOfUnit]
  exact correctedResidueLog_basicVandiverUnit1831 hzeta row j

omit [NumberField K] [IsCyclotomicExtension {1831} ℚ K]
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

/-- Vandiver's positive weight reduced modulo `1831`. -/
def weightMod1831 (i : Fin 914) (j : VandiverFactorIndex1831) : ZMod 1831 :=
  (teichmullerRoot1831 : ZMod 1831) ^
    (1831 ^ 2 - 2 * (i.val + 1) * j.val)

theorem diagonalWeight1831_cast (i : Fin 914)
    (j : VandiverFactorIndex1831) :
    (diagonalWeight1831 i j : ZMod 1831) =
      weightMod1831 i j := by
  simp [diagonalWeight1831, integralDiagonalWeight, weightMod1831]

theorem quotientResidueLinear_diagonalVandiverUnit1831_formula
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 1831)
    (row i : Fin 914) :
    certificate1831.quotientResidueLinear hzeta row
        (classOfUnit (diagonalVandiverUnit1831 hzeta i)) =
      ∑ j : VandiverFactorIndex1831,
        weightMod1831 i j * basicEdgeSymbol1831 row j := by
  rw [diagonalVandiverUnit1831, classOfUnit_prod_pow]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_nsmul, quotientResidueLinear_basicVandiverUnit1831]
  simp only [nsmul_eq_mul]
  rw [diagonalWeight1831_cast]

/-! ## Algebraic Fourier factorization -/

theorem cycleClassSymbol1831_zero (row : Fin 914) :
    cycleClassSymbol1831 row 0 = 0 := by
  simp [cycleClassSymbol1831]

theorem cycleClassSymbol1831_succ (row j : Fin 914) :
    cycleClassSymbol1831 row (j.val + 1) =
      Fermat.OneThousandEightHundredThirtyOne.CircularUnitMatrix.matrix row
        (cycleColumn1831 j) := by
  rw [cycleClassSymbol1831, dif_pos]
  · congr
  · omega

theorem cycleClassSymbol1831_last (row : Fin 914) :
    cycleClassSymbol1831 row 915 = 0 := by
  simp [cycleClassSymbol1831]

theorem weighted_edge_sum1831 (row : Fin 914)
    (w : Fin 915 → ZMod 1831) :
    (∑ j : Fin 915, w j * basicEdgeSymbol1831 row j) =
      ∑ ell : Fin 914,
        Fermat.OneThousandEightHundredThirtyOne.CircularUnitMatrix.matrix row
            (cycleColumn1831 ell) *
          (w ell.castSucc - w ell.succ) := by
  simp_rw [basicEdgeSymbol1831, mul_sub]
  rw [Finset.sum_sub_distrib]
  have hfirst :
      (∑ j : Fin 915, w j * cycleClassSymbol1831 row (j.val + 1)) =
        ∑ ell : Fin 914,
          w ell.castSucc *
            Fermat.OneThousandEightHundredThirtyOne.CircularUnitMatrix.matrix row
              (cycleColumn1831 ell) := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, cycleClassSymbol1831_succ, Fin.val_last]
    rw [show 914 + 1 = 915 by norm_num, cycleClassSymbol1831_last,
      mul_zero, add_zero]
  have hsecond :
      (∑ j : Fin 915, w j * cycleClassSymbol1831 row j.val) =
        ∑ ell : Fin 914,
          w ell.succ *
            Fermat.OneThousandEightHundredThirtyOne.CircularUnitMatrix.matrix row
              (cycleColumn1831 ell) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, cycleClassSymbol1831_zero, mul_zero, zero_add,
      Fin.val_succ, cycleClassSymbol1831_succ]
  rw [hfirst, hsecond, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ell _
  ring

theorem weightMod1831_castSucc_sub_succ (ell i : Fin 914) :
    weightMod1831 i ell.castSucc - weightMod1831 i ell.succ =
      fourierChange1831 ell i := by
  let r : ZMod 1831 := teichmullerRoot1831
  let n := i.val + 1
  let L := ell.val + 1
  have hn : n ≤ 914 := by simp [n]
  have hL : L ≤ 914 := by simp [L]
  have hn2 : 2 * n ≤ 1830 := by omega
  have hpositive : 2 * n * L ≤ 1831 ^ 2 := by
    calc
      2 * n * L ≤ 2 * 914 * 914 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn) hL
      _ ≤ 1831 ^ 2 := by norm_num
  have hsplit :
      (1830 - 2 * n) * L = 1830 * L - 2 * n * L :=
    Nat.sub_mul 1830 (2 * n) L
  have hdecomp :
      1831 ^ 2 - 2 * n * L =
        1 + (1830 - 2 * n) * L + 1830 * (1832 - L) := by
    rw [hsplit]
    have hwithin : 2 * n * L ≤ 1830 * L :=
      Nat.mul_le_mul_right L hn2
    omega
  have hr1830 : r ^ 1830 = 1 :=
    teichmullerRoot1831_isPrimitive.pow_eq_one
  have hsecond :
      r ^ (1831 ^ 2 - 2 * n * L) =
        r * (r ^ (1830 - 2 * n)) ^ L := by
    rw [hdecomp, pow_add, pow_add]
    rw [show r ^ 1 = r by simp,
      show r ^ ((1830 - 2 * n) * L) =
          (r ^ (1830 - 2 * n)) ^ L by rw [pow_mul],
      show r ^ (1830 * (1832 - L)) = 1 by
        rw [pow_mul, hr1830, one_pow]]
    simp
  have hstep :
      2 * n * L = 2 * n * ell.val + 2 * n := by
    simp only [L]
    ring
  have hfirstExp :
      1831 ^ 2 - 2 * n * ell.val =
        (1831 ^ 2 - 2 * n * L) + 2 * n := by
    have hfirstBound : 2 * n * ell.val ≤ 1831 ^ 2 := by
      calc
        2 * n * ell.val ≤ 2 * n * L :=
          Nat.mul_le_mul_left (2 * n) (by simp [L])
        _ ≤ 1831 ^ 2 := hpositive
    omega
  rw [weightMod1831]
  change r ^ (1831 ^ 2 - 2 * n * ell.val) -
      r ^ (1831 ^ 2 - 2 * n * L) = fourierChange1831 ell i
  rw [hfirstExp, pow_add, hsecond, fourierChange1831_apply]
  simp only [vandermondeNode1831, fourierScale1831, n, L, r]
  rw [show 1828 - 2 * i.val = 1830 - 2 * (i.val + 1) by omega]
  rw [show ell.val + 1 = L by rfl]
  ring

noncomputable def cycleCircularMatrix1831 :
    Matrix (Fin 914) (Fin 914) (ZMod 1831) :=
  Fermat.OneThousandEightHundredThirtyOne.CircularUnitMatrix.matrix.submatrix id
    cycleColumnEquiv1831

theorem cycleCircularMatrix1831_det_ne_zero :
    cycleCircularMatrix1831.det ≠ 0 := by
  rw [cycleCircularMatrix1831, Matrix.det_permute']
  exact mul_ne_zero
    (by
      exact ((Equiv.Perm.sign cycleColumnEquiv1831).isUnit.map
        (Int.castRingHom (ZMod 1831))).ne_zero)
    Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate.matrix_det_ne_zero

/-- The actual diagonal residue matrix, factored into its circular and
Fourier components. -/
noncomputable def diagonalResidueMatrix1831 :
    Matrix (Fin 914) (Fin 914) (ZMod 1831) :=
  cycleCircularMatrix1831 * fourierChange1831

theorem diagonalResidueMatrix1831_det_ne_zero :
    diagonalResidueMatrix1831.det ≠ 0 := by
  rw [diagonalResidueMatrix1831, Matrix.det_mul]
  exact mul_ne_zero cycleCircularMatrix1831_det_ne_zero
    fourierChange1831_det_ne_zero

theorem weighted_edge_sum1831_eq_matrix (row i : Fin 914) :
    (∑ j : Fin 915, weightMod1831 i j * basicEdgeSymbol1831 row j) =
      diagonalResidueMatrix1831 row i := by
  rw [weighted_edge_sum1831]
  simp_rw [weightMod1831_castSucc_sub_succ]
  rfl

@[simp]
theorem quotientResidueLinear_diagonalVandiverUnit1831 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1831) (row i : Fin 914) :
    certificate1831.quotientResidueLinear hzeta row
        (classOfUnit (diagonalVandiverUnit1831 hzeta i)) =
      diagonalResidueMatrix1831 row i := by
  rw [quotientResidueLinear_diagonalVandiverUnit1831_formula]
  exact weighted_edge_sum1831_eq_matrix row i

theorem evalMatrix_diagonalVandiverUnit1831 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1831) :
    evalMatrix (classOfUnit ∘ diagonalVandiverUnit1831 hzeta)
        (certificate1831.residueFunctionals hzeta) =
      diagonalResidueMatrix1831 := by
  ext row i
  exact quotientResidueLinear_diagonalVandiverUnit1831 hzeta row i

theorem not_dvd_diagonalVandiverUnit1831_full_index {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1831) :
    ¬1831 ∣
      (Subgroup.closure (Set.range (diagonalVandiverUnit1831 hzeta)) ⊔
        NumberField.Units.torsion K).index := by
  apply not_dvd_unitIndex_of_eval_det_ne_zero
    (certificate1831.basisModTorsion (K := K))
      (diagonalVandiverUnit1831 hzeta)
      (certificate1831.residueFunctionals hzeta)
  rw [evalMatrix_diagonalVandiverUnit1831]
  exact diagonalResidueMatrix1831_det_ne_zero

theorem ambient_closure_finiteIndex {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1831) :
    (Subgroup.closure
      (Set.range (diagonalVandiverUnit1831 hzeta))).FiniteIndex := by
  have hnot := not_dvd_diagonalVandiverUnit1831_full_index hzeta
  have hsup :
      (Subgroup.closure (Set.range (diagonalVandiverUnit1831 hzeta)) ⊔
        NumberField.Units.torsion K).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff]
    intro hzero
    apply hnot
    rw [hzero]
    exact dvd_zero 1831
  exact (NumberField.Units.finiteIndex_iff_sup_torsion_finiteIndex
    (Subgroup.closure (Set.range
      (diagonalVandiverUnit1831 hzeta)))).2 hsup

theorem real_closure_finiteIndex {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1831) :
    (Subgroup.closure
      (Set.range (diagonalVandiverUnitFamily1831 hzeta))).FiniteIndex := by
  letI :
      (Subgroup.closure (Set.range fun i : Fin 914 ↦
        ((diagonalVandiverUnitFamily1831 hzeta i :
          NumberField.IsCMField.realUnits K) :
            (RingOfIntegers K)ˣ))).FiniteIndex := by
    simpa [diagonalVandiverUnitFamily1831] using
      ambient_closure_finiteIndex hzeta
  exact Fermat.Irregular.VandiverFiniteIndex.closure_range_subtype
    (NumberField.IsCMField.realUnits K)
      (diagonalVandiverUnitFamily1831 hzeta)

end

end Fermat.OneThousandEightHundredThirtyOne.VandiverDiagonalUnits
