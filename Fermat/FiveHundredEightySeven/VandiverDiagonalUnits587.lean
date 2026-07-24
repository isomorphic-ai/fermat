import Fermat.Irregular.VandiverDiagonalLogDerivative
import Fermat.Irregular.VandiverFiniteIndex
import Fermat.FiveHundredEightySeven.VandiverDiagonalUnitResidues587

/-!
# Vandiver's diagonal real-unit family at exponent 587

This module realizes the integral diagonal family used in Vandiver's
Lemma II:

`epsilon(w) = w^258 * (w^6529 - 1) / (w - 1)`.

The corrected source range is `j = 0, ..., 292`; the positive weight at
source index `i+1` is

`6529^(587^2 - 2*(i+1)*j)`.

Finite index is proved without a second giant inverse table.  The
auxiliary-prime evaluation matrix factors as the existing circular-unit
matrix (with its columns cyclically reordered) times the scaled
Vandermonde matrix certified in `VandiverDiagonalUnitResidues587`.
-/

open scoped NumberField

namespace Fermat.FiveHundredEightySeven.VandiverDiagonalUnits

noncomputable section

open Fermat.Irregular
open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitIndex
open Fermat.Irregular.CircularUnitResidues
open Fermat.Irregular.CircularUnitResidues.Certificate
open Fermat.Irregular.CircularUnits
open Fermat.Irregular.VandiverDiagonalLogDerivative
open Fermat.FiveHundredEightySeven.VandiverDiagonalArithmetic
open Fermat.FiveHundredEightySeven.VandiverDiagonalUnitResidues
open NumberField NumberField.Units

local instance : Fact (Nat.Prime 587) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 8219) := ⟨by norm_num⟩

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The corrected source range `j = 0, ..., 292`. -/
abbrev VandiverFactorIndex587 := Fin 293

theorem card_vandiverFactorIndex587 :
    Fintype.card VandiverFactorIndex587 = 293 := by decide

/-- The power of the chosen root occurring in the `j`th conjugate. -/
def conjugateExponent587 (j : VandiverFactorIndex587) : ℕ :=
  VandiverDiagonalUnitResidues.conjugateExponent587 j

/-- Vandiver's literal positive integral weight. -/
def diagonalWeight587 (i : Fin 292) (j : VandiverFactorIndex587) : ℕ :=
  integralDiagonalWeight 587 teichmullerRoot587 (i.val + 1) j.val

theorem diagonalWeight587_eq (i : Fin 292) (j : VandiverFactorIndex587) :
    diagonalWeight587 i j =
      6529 ^ (587 ^ 2 - 2 * (i.val + 1) * j.val) := by
  rfl

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {587} ℚ K] [NumberField.IsCMField K]

omit [NumberField K] [IsCyclotomicExtension {587} ℚ K]
    [NumberField.IsCMField K] in
theorem conjugate_isPrimitive {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 587)
    (j : VandiverFactorIndex587) :
    IsPrimitiveRoot (zeta ^ conjugateExponent587 j) 587 := by
  apply hzeta.pow_of_coprime
  exact (by norm_num : Nat.Coprime 6529 587).pow_left j.val

/-- The literal basic factor of geometric length `6529`. -/
def basicVandiverUnit587 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 587)
    (j : VandiverFactorIndex587) : (RingOfIntegers K)ˣ :=
  normalizedCircularUnit (p := 587) (a := 6529)
    (conjugate_isPrimitive hzeta j) (by norm_num) (by norm_num) 258

omit [NumberField K] [IsCyclotomicExtension {587} ℚ K]
    [NumberField.IsCMField K] in
theorem conjugate_toInteger {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 587)
    (j : VandiverFactorIndex587) :
    (conjugate_isPrimitive hzeta j).toInteger =
      hzeta.toInteger ^ conjugateExponent587 j := by
  apply RingOfIntegers.ext
  rfl

omit [IsCyclotomicExtension {587} ℚ K] in
theorem basicVandiverUnit587_mem_realUnits {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 587)
    (j : VandiverFactorIndex587) :
    basicVandiverUnit587 hzeta j ∈
      NumberField.IsCMField.realUnits K := by
  apply normalizedCircularUnit_mem_realUnits
    (p := 587) (a := 6529) (e := 258)
  decide

/-- The ambient integral diagonal unit `(E_(i+1)(zeta))^rho`. -/
def diagonalVandiverUnit587 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 587) (i : Fin 292) :
    (RingOfIntegers K)ˣ :=
  ∏ j : VandiverFactorIndex587,
    basicVandiverUnit587 hzeta j ^ diagonalWeight587 i j

omit [IsCyclotomicExtension {587} ℚ K] in
theorem diagonalVandiverUnit587_mem_realUnits {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 587) (i : Fin 292) :
    diagonalVandiverUnit587 hzeta i ∈
      NumberField.IsCMField.realUnits K := by
  apply Subgroup.prod_mem
  intro j hj
  exact Subgroup.pow_mem _
    (basicVandiverUnit587_mem_realUnits hzeta j) _

/-- The 292 source units in the real-unit subgroup. -/
def diagonalVandiverUnitFamily587 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 587) :
    Fin 292 → NumberField.IsCMField.realUnits K :=
  fun i ↦ ⟨diagonalVandiverUnit587 hzeta i,
    diagonalVandiverUnit587_mem_realUnits hzeta i⟩

omit [IsCyclotomicExtension {587} ℚ K] in
@[simp]
theorem diagonalVandiverUnitFamily587_coe {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 587) (i : Fin 292) :
    ((diagonalVandiverUnitFamily587 hzeta i :
      NumberField.IsCMField.realUnits K) : (RingOfIntegers K)ˣ) =
      diagonalVandiverUnit587 hzeta i := rfl

/-! ## Evaluation of the actual units -/

omit [NumberField.IsCMField K] in
theorem reductionHom_basicVandiverUnit587 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 587) (row : Fin 292)
    (j : VandiverFactorIndex587) :
    certificate587.reductionHom hzeta row
        (basicVandiverUnit587 hzeta j : RingOfIntegers K) =
      basicResidueValue587 row j := by
  unfold basicVandiverUnit587
  rw [normalizedCircularUnit_val]
  rw [conjugate_toInteger (hzeta := hzeta) j]
  simp only [map_mul, map_pow, map_sum, certificate587.reductionHom_zeta]
  rfl

omit [IsCyclotomicExtension {587} ℚ K] in
@[simp]
theorem realUnitNorm_basicVandiverUnit587 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 587)
    (j : VandiverFactorIndex587) :
    realUnitNorm (basicVandiverUnit587 hzeta j) =
      basicVandiverUnit587 hzeta j ^ 2 := by
  change basicVandiverUnit587 hzeta j *
    NumberField.IsCMField.unitsComplexConj K
      (basicVandiverUnit587 hzeta j) = _
  rw [(NumberField.IsCMField.unitsComplexConj_eq_self_iff K _).mpr
    (basicVandiverUnit587_mem_realUnits hzeta j)]
  exact (pow_two _).symm

theorem correctedResidueLog_basicVandiverUnit587 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 587) (row : Fin 292)
    (j : VandiverFactorIndex587) :
    certificate587.correctedResidueLog hzeta row
        (Additive.ofMul (basicVandiverUnit587 hzeta j)) =
      basicEdgeSymbol587 row j := by
  let u : (ZMod 8219)ˣ :=
    Units.map (certificate587.reductionHom hzeta row)
      (realUnitNorm (basicVandiverUnit587 hzeta j))
  have huval : (u : ZMod 8219) = basicResidueValue587 row j ^ 2 := by
    dsimp [u]
    rw [realUnitNorm_basicVandiverUnit587, Units.val_pow_eq_pow_val,
      map_pow, reductionHom_basicVandiverUnit587]
  have hpow : ((u : ZMod 8219) ^ 14) =
      certificate587.root ^ ((basicEdgeSymbol587 row j).val * 2) := by
    calc
      (u : ZMod 8219) ^ 14 =
          (basicResidueValue587 row j ^ 2) ^ 14 := by rw [huval]
      _ = (basicResidueValue587 row j ^ 14) ^ 2 := by ring
      _ = (certificate587.root ^
          (basicEdgeSymbol587 row j).val) ^ 2 := by
        rw [basicResidueValue587_symbol]
      _ = certificate587.root ^
          ((basicEdgeSymbol587 row j).val * 2) := by rw [pow_mul]
  change (2 : ZMod 587)⁻¹ *
      certificate587.residueLog (Additive.ofMul u) =
    basicEdgeSymbol587 row j
  rw [certificate587.residueLog_eq_of_pow_eq u _ hpow]
  rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  have hhalf : (2 : ZMod 587)⁻¹ * 2 = 1 :=
    inv_mul_cancel₀ (by
      intro h
      have hdiv : 587 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 587).mp h
      norm_num at hdiv)
  calc
    (2 : ZMod 587)⁻¹ * (basicEdgeSymbol587 row j * 2) =
        (2⁻¹ * 2) * basicEdgeSymbol587 row j := by ring
    _ = basicEdgeSymbol587 row j := by rw [hhalf, one_mul]

@[simp]
theorem quotientResidueLinear_basicVandiverUnit587 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 587) (row : Fin 292)
    (j : VandiverFactorIndex587) :
    certificate587.quotientResidueLinear hzeta row
        (classOfUnit (basicVandiverUnit587 hzeta j)) =
      basicEdgeSymbol587 row j := by
  change certificate587.quotientResidueLog hzeta row
    (classOfUnit (basicVandiverUnit587 hzeta j)) = _
  rw [certificate587.quotientResidueLog_classOfUnit]
  exact correctedResidueLog_basicVandiverUnit587 hzeta row j

omit [NumberField K] [IsCyclotomicExtension {587} ℚ K]
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

/-- Vandiver's positive weight reduced modulo `587`. -/
def weightMod587 (i : Fin 292) (j : VandiverFactorIndex587) : ZMod 587 :=
  (teichmullerRoot587 : ZMod 587) ^
    (587 ^ 2 - 2 * (i.val + 1) * j.val)

theorem diagonalWeight587_cast (i : Fin 292)
    (j : VandiverFactorIndex587) :
    (diagonalWeight587 i j : ZMod 587) =
      weightMod587 i j := by
  simp [diagonalWeight587, integralDiagonalWeight, weightMod587]

theorem quotientResidueLinear_diagonalVandiverUnit587_formula
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 587)
    (row i : Fin 292) :
    certificate587.quotientResidueLinear hzeta row
        (classOfUnit (diagonalVandiverUnit587 hzeta i)) =
      ∑ j : VandiverFactorIndex587,
        weightMod587 i j * basicEdgeSymbol587 row j := by
  rw [diagonalVandiverUnit587, classOfUnit_prod_pow]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_nsmul, quotientResidueLinear_basicVandiverUnit587]
  simp only [nsmul_eq_mul]
  rw [diagonalWeight587_cast]

/-! ## Algebraic Fourier factorization -/

theorem cycleClassSymbol587_zero (row : Fin 292) :
    cycleClassSymbol587 row 0 = 0 := by
  simp [cycleClassSymbol587]

theorem cycleClassSymbol587_succ (row j : Fin 292) :
    cycleClassSymbol587 row (j.val + 1) =
      Fermat.FiveHundredEightySeven.CircularUnitMatrix.matrix row
        (cycleColumn587 j) := by
  rw [cycleClassSymbol587, dif_pos]
  · congr
  · omega

theorem cycleClassSymbol587_last (row : Fin 292) :
    cycleClassSymbol587 row 293 = 0 := by
  simp [cycleClassSymbol587]

theorem weighted_edge_sum587 (row : Fin 292)
    (w : Fin 293 → ZMod 587) :
    (∑ j : Fin 293, w j * basicEdgeSymbol587 row j) =
      ∑ ell : Fin 292,
        Fermat.FiveHundredEightySeven.CircularUnitMatrix.matrix row
            (cycleColumn587 ell) *
          (w ell.castSucc - w ell.succ) := by
  simp_rw [basicEdgeSymbol587, mul_sub]
  rw [Finset.sum_sub_distrib]
  have hfirst :
      (∑ j : Fin 293, w j * cycleClassSymbol587 row (j.val + 1)) =
        ∑ ell : Fin 292,
          w ell.castSucc *
            Fermat.FiveHundredEightySeven.CircularUnitMatrix.matrix row
              (cycleColumn587 ell) := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, cycleClassSymbol587_succ, Fin.val_last]
    rw [show 292 + 1 = 293 by norm_num, cycleClassSymbol587_last,
      mul_zero, add_zero]
  have hsecond :
      (∑ j : Fin 293, w j * cycleClassSymbol587 row j.val) =
        ∑ ell : Fin 292,
          w ell.succ *
            Fermat.FiveHundredEightySeven.CircularUnitMatrix.matrix row
              (cycleColumn587 ell) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, cycleClassSymbol587_zero, mul_zero, zero_add,
      Fin.val_succ, cycleClassSymbol587_succ]
  rw [hfirst, hsecond, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ell _
  ring

theorem weightMod587_castSucc_sub_succ (ell i : Fin 292) :
    weightMod587 i ell.castSucc - weightMod587 i ell.succ =
      fourierChange587 ell i := by
  let r : ZMod 587 := teichmullerRoot587
  let n := i.val + 1
  let L := ell.val + 1
  have hn : n ≤ 292 := by simp [n]
  have hL : L ≤ 292 := by simp [L]
  have hn2 : 2 * n ≤ 586 := by omega
  have hpositive : 2 * n * L ≤ 587 ^ 2 := by
    calc
      2 * n * L ≤ 2 * 292 * 292 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn) hL
      _ ≤ 587 ^ 2 := by norm_num
  have hsplit :
      (586 - 2 * n) * L = 586 * L - 2 * n * L :=
    Nat.sub_mul 586 (2 * n) L
  have hdecomp :
      587 ^ 2 - 2 * n * L =
        1 + (586 - 2 * n) * L + 586 * (588 - L) := by
    rw [hsplit]
    have hwithin : 2 * n * L ≤ 586 * L :=
      Nat.mul_le_mul_right L hn2
    omega
  have hr586 : r ^ 586 = 1 :=
    teichmullerRoot587_isPrimitive.pow_eq_one
  have hsecond :
      r ^ (587 ^ 2 - 2 * n * L) =
        r * (r ^ (586 - 2 * n)) ^ L := by
    rw [hdecomp, pow_add, pow_add]
    rw [show r ^ 1 = r by simp,
      show r ^ ((586 - 2 * n) * L) =
          (r ^ (586 - 2 * n)) ^ L by rw [pow_mul],
      show r ^ (586 * (588 - L)) = 1 by
        rw [pow_mul, hr586, one_pow]]
    simp
  have hstep :
      2 * n * L = 2 * n * ell.val + 2 * n := by
    simp only [L]
    ring
  have hfirstExp :
      587 ^ 2 - 2 * n * ell.val =
        (587 ^ 2 - 2 * n * L) + 2 * n := by
    have hfirstBound : 2 * n * ell.val ≤ 587 ^ 2 := by
      calc
        2 * n * ell.val ≤ 2 * n * L :=
          Nat.mul_le_mul_left (2 * n) (by simp [L])
        _ ≤ 587 ^ 2 := hpositive
    omega
  rw [weightMod587]
  change r ^ (587 ^ 2 - 2 * n * ell.val) -
      r ^ (587 ^ 2 - 2 * n * L) = fourierChange587 ell i
  rw [hfirstExp, pow_add, hsecond, fourierChange587_apply]
  simp only [vandermondeNode587, fourierScale587, n, L, r]
  rw [show 584 - 2 * i.val = 586 - 2 * (i.val + 1) by omega]
  rw [show ell.val + 1 = L by rfl]
  ring

noncomputable def cycleCircularMatrix587 :
    Matrix (Fin 292) (Fin 292) (ZMod 587) :=
  Fermat.FiveHundredEightySeven.CircularUnitMatrix.matrix.submatrix id
    cycleColumnEquiv587

theorem cycleCircularMatrix587_det_ne_zero :
    cycleCircularMatrix587.det ≠ 0 := by
  rw [cycleCircularMatrix587, Matrix.det_permute']
  exact mul_ne_zero
    (by
      exact ((Equiv.Perm.sign cycleColumnEquiv587).isUnit.map
        (Int.castRingHom (ZMod 587))).ne_zero)
    Fermat.FiveHundredEightySeven.CircularUnitCertificate.matrix_det_ne_zero

/-- The actual diagonal residue matrix, factored into its circular and
Fourier components. -/
noncomputable def diagonalResidueMatrix587 :
    Matrix (Fin 292) (Fin 292) (ZMod 587) :=
  cycleCircularMatrix587 * fourierChange587

theorem diagonalResidueMatrix587_det_ne_zero :
    diagonalResidueMatrix587.det ≠ 0 := by
  rw [diagonalResidueMatrix587, Matrix.det_mul]
  exact mul_ne_zero cycleCircularMatrix587_det_ne_zero
    fourierChange587_det_ne_zero

theorem weighted_edge_sum587_eq_matrix (row i : Fin 292) :
    (∑ j : Fin 293, weightMod587 i j * basicEdgeSymbol587 row j) =
      diagonalResidueMatrix587 row i := by
  rw [weighted_edge_sum587]
  simp_rw [weightMod587_castSucc_sub_succ]
  rfl

@[simp]
theorem quotientResidueLinear_diagonalVandiverUnit587 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 587) (row i : Fin 292) :
    certificate587.quotientResidueLinear hzeta row
        (classOfUnit (diagonalVandiverUnit587 hzeta i)) =
      diagonalResidueMatrix587 row i := by
  rw [quotientResidueLinear_diagonalVandiverUnit587_formula]
  exact weighted_edge_sum587_eq_matrix row i

theorem evalMatrix_diagonalVandiverUnit587 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 587) :
    evalMatrix (classOfUnit ∘ diagonalVandiverUnit587 hzeta)
        (certificate587.residueFunctionals hzeta) =
      diagonalResidueMatrix587 := by
  ext row i
  exact quotientResidueLinear_diagonalVandiverUnit587 hzeta row i

theorem not_dvd_diagonalVandiverUnit587_full_index {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 587) :
    ¬587 ∣
      (Subgroup.closure (Set.range (diagonalVandiverUnit587 hzeta)) ⊔
        NumberField.Units.torsion K).index := by
  apply not_dvd_unitIndex_of_eval_det_ne_zero
    (certificate587.basisModTorsion (K := K))
      (diagonalVandiverUnit587 hzeta)
      (certificate587.residueFunctionals hzeta)
  rw [evalMatrix_diagonalVandiverUnit587]
  exact diagonalResidueMatrix587_det_ne_zero

theorem ambient_closure_finiteIndex {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 587) :
    (Subgroup.closure
      (Set.range (diagonalVandiverUnit587 hzeta))).FiniteIndex := by
  have hnot := not_dvd_diagonalVandiverUnit587_full_index hzeta
  have hsup :
      (Subgroup.closure (Set.range (diagonalVandiverUnit587 hzeta)) ⊔
        NumberField.Units.torsion K).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff]
    intro hzero
    apply hnot
    rw [hzero]
    exact dvd_zero 587
  exact (NumberField.Units.finiteIndex_iff_sup_torsion_finiteIndex
    (Subgroup.closure (Set.range
      (diagonalVandiverUnit587 hzeta)))).2 hsup

theorem real_closure_finiteIndex {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 587) :
    (Subgroup.closure
      (Set.range (diagonalVandiverUnitFamily587 hzeta))).FiniteIndex := by
  letI :
      (Subgroup.closure (Set.range fun i : Fin 292 ↦
        ((diagonalVandiverUnitFamily587 hzeta i :
          NumberField.IsCMField.realUnits K) :
            (RingOfIntegers K)ˣ))).FiniteIndex := by
    simpa [diagonalVandiverUnitFamily587] using
      ambient_closure_finiteIndex hzeta
  exact Fermat.Irregular.VandiverFiniteIndex.closure_range_subtype
    (NumberField.IsCMField.realUnits K)
      (diagonalVandiverUnitFamily587 hzeta)

end

end Fermat.FiveHundredEightySeven.VandiverDiagonalUnits
