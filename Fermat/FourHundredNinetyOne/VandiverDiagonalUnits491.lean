import Fermat.Irregular.VandiverDiagonalLogDerivative
import Fermat.Irregular.VandiverFiniteIndex
import Fermat.FourHundredNinetyOne.VandiverDiagonalUnitResidues491

/-!
# Vandiver's diagonal real-unit family at exponent 491

This module realizes the integral diagonal family

`epsilon(w) = w^463 * (w^2512 - 1) / (w - 1)`.

The corrected source range is `j = 0, ..., 244`; the positive weight at
source index `i+1` is

`2512^(491^2 - 2*(i+1)*j)`.

Finite index is proved without a dense inverse table.  The auxiliary-prime
evaluation matrix factors as the existing circular-unit matrix (with its
columns cyclically reordered) times the scaled Vandermonde matrix certified
in `VandiverDiagonalUnitResidues491`.
-/

open scoped NumberField

namespace Fermat.FourHundredNinetyOne.VandiverDiagonalUnits

noncomputable section

open Fermat.Irregular
open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitIndex
open Fermat.Irregular.CircularUnitResidues
open Fermat.Irregular.CircularUnitResidues.Certificate
open Fermat.Irregular.CircularUnits
open Fermat.Irregular.VandiverDiagonalLogDerivative
open Fermat.FourHundredNinetyOne.VandiverDiagonalArithmetic
open Fermat.FourHundredNinetyOne.VandiverDiagonalUnitResidues
open NumberField NumberField.Units

local instance : Fact (Nat.Prime 491) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 983) := ⟨by norm_num⟩

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The corrected source range `j = 0, ..., 244`. -/
abbrev VandiverFactorIndex491 := Fin 245

theorem card_vandiverFactorIndex491 :
    Fintype.card VandiverFactorIndex491 = 245 := by decide

/-- The power of the chosen root occurring in the `j`th conjugate. -/
def conjugateExponent491 (j : VandiverFactorIndex491) : ℕ :=
  VandiverDiagonalUnitResidues.conjugateExponent491 j

/-- Vandiver's literal positive integral weight. -/
def diagonalWeight491 (i : Fin 244) (j : VandiverFactorIndex491) : ℕ :=
  integralDiagonalWeight 491 teichmullerRoot491 (i.val + 1) j.val

theorem diagonalWeight491_eq (i : Fin 244) (j : VandiverFactorIndex491) :
    diagonalWeight491 i j =
      2512 ^ (491 ^ 2 - 2 * (i.val + 1) * j.val) := by
  rfl

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {491} ℚ K] [NumberField.IsCMField K]

omit [NumberField K] [IsCyclotomicExtension {491} ℚ K]
    [NumberField.IsCMField K] in
theorem conjugate_isPrimitive {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491)
    (j : VandiverFactorIndex491) :
    IsPrimitiveRoot (zeta ^ conjugateExponent491 j) 491 := by
  apply hzeta.pow_of_coprime
  exact (by norm_num : Nat.Coprime 2512 491).pow_left j.val

/-- The literal basic factor of geometric length `2512`. -/
def basicVandiverUnit491 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491)
    (j : VandiverFactorIndex491) : (RingOfIntegers K)ˣ :=
  normalizedCircularUnit (p := 491) (a := 2512)
    (conjugate_isPrimitive hzeta j) (by norm_num) (by norm_num) 463

omit [NumberField K] [IsCyclotomicExtension {491} ℚ K]
    [NumberField.IsCMField K] in
theorem conjugate_toInteger {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491)
    (j : VandiverFactorIndex491) :
    (conjugate_isPrimitive hzeta j).toInteger =
      hzeta.toInteger ^ conjugateExponent491 j := by
  apply RingOfIntegers.ext
  rfl

omit [IsCyclotomicExtension {491} ℚ K] in
theorem basicVandiverUnit491_mem_realUnits {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491)
    (j : VandiverFactorIndex491) :
    basicVandiverUnit491 hzeta j ∈
      NumberField.IsCMField.realUnits K := by
  apply normalizedCircularUnit_mem_realUnits
    (p := 491) (a := 2512) (e := 463)
  decide

/-- The ambient integral diagonal unit `(E_(i+1)(zeta))^rho`. -/
def diagonalVandiverUnit491 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491) (i : Fin 244) :
    (RingOfIntegers K)ˣ :=
  ∏ j : VandiverFactorIndex491,
    basicVandiverUnit491 hzeta j ^ diagonalWeight491 i j

omit [IsCyclotomicExtension {491} ℚ K] in
theorem diagonalVandiverUnit491_mem_realUnits {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491) (i : Fin 244) :
    diagonalVandiverUnit491 hzeta i ∈
      NumberField.IsCMField.realUnits K := by
  apply Subgroup.prod_mem
  intro j hj
  exact Subgroup.pow_mem _
    (basicVandiverUnit491_mem_realUnits hzeta j) _

/-- The 244 source units in the real-unit subgroup. -/
def diagonalVandiverUnitFamily491 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491) :
    Fin 244 → NumberField.IsCMField.realUnits K :=
  fun i ↦ ⟨diagonalVandiverUnit491 hzeta i,
    diagonalVandiverUnit491_mem_realUnits hzeta i⟩

omit [IsCyclotomicExtension {491} ℚ K] in
@[simp]
theorem diagonalVandiverUnitFamily491_coe {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491) (i : Fin 244) :
    ((diagonalVandiverUnitFamily491 hzeta i :
      NumberField.IsCMField.realUnits K) : (RingOfIntegers K)ˣ) =
      diagonalVandiverUnit491 hzeta i := rfl

/-! ## Evaluation of the actual units -/

omit [NumberField.IsCMField K] in
theorem reductionHom_basicVandiverUnit491 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491) (row : Fin 244)
    (j : VandiverFactorIndex491) :
    certificate491.reductionHom hzeta row
        (basicVandiverUnit491 hzeta j : RingOfIntegers K) =
      basicResidueValue491 row j := by
  unfold basicVandiverUnit491
  rw [normalizedCircularUnit_val]
  rw [conjugate_toInteger (hzeta := hzeta) j]
  simp only [map_mul, map_pow, map_sum, certificate491.reductionHom_zeta]
  rfl

omit [IsCyclotomicExtension {491} ℚ K] in
@[simp]
theorem realUnitNorm_basicVandiverUnit491 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491)
    (j : VandiverFactorIndex491) :
    realUnitNorm (basicVandiverUnit491 hzeta j) =
      basicVandiverUnit491 hzeta j ^ 2 := by
  change basicVandiverUnit491 hzeta j *
    NumberField.IsCMField.unitsComplexConj K
      (basicVandiverUnit491 hzeta j) = _
  rw [(NumberField.IsCMField.unitsComplexConj_eq_self_iff K _).mpr
    (basicVandiverUnit491_mem_realUnits hzeta j)]
  exact (pow_two _).symm

theorem correctedResidueLog_basicVandiverUnit491 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491) (row : Fin 244)
    (j : VandiverFactorIndex491) :
    certificate491.correctedResidueLog hzeta row
        (Additive.ofMul (basicVandiverUnit491 hzeta j)) =
      basicEdgeSymbol491 row j := by
  let u : (ZMod 983)ˣ :=
    Units.map (certificate491.reductionHom hzeta row)
      (realUnitNorm (basicVandiverUnit491 hzeta j))
  have huval : (u : ZMod 983) = basicResidueValue491 row j ^ 2 := by
    dsimp [u]
    rw [realUnitNorm_basicVandiverUnit491, Units.val_pow_eq_pow_val,
      map_pow, reductionHom_basicVandiverUnit491]
  have hpow : ((u : ZMod 983) ^ 2) =
      certificate491.root ^ ((basicEdgeSymbol491 row j).val * 2) := by
    calc
      (u : ZMod 983) ^ 2 =
          (basicResidueValue491 row j ^ 2) ^ 2 := by rw [huval]
      _ = (certificate491.root ^
          (basicEdgeSymbol491 row j).val) ^ 2 := by
        rw [basicResidueValue491_symbol]
      _ = certificate491.root ^
          ((basicEdgeSymbol491 row j).val * 2) := by rw [pow_mul]
  change (2 : ZMod 491)⁻¹ *
      certificate491.residueLog (Additive.ofMul u) =
    basicEdgeSymbol491 row j
  rw [certificate491.residueLog_eq_of_pow_eq u _ hpow]
  rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  have hhalf : (2 : ZMod 491)⁻¹ * 2 = 1 :=
    inv_mul_cancel₀ (by
      intro h
      have hdiv : 491 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 491).mp h
      norm_num at hdiv)
  calc
    (2 : ZMod 491)⁻¹ * (basicEdgeSymbol491 row j * 2) =
        (2⁻¹ * 2) * basicEdgeSymbol491 row j := by ring
    _ = basicEdgeSymbol491 row j := by rw [hhalf, one_mul]

@[simp]
theorem quotientResidueLinear_basicVandiverUnit491 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491) (row : Fin 244)
    (j : VandiverFactorIndex491) :
    certificate491.quotientResidueLinear hzeta row
        (classOfUnit (basicVandiverUnit491 hzeta j)) =
      basicEdgeSymbol491 row j := by
  change certificate491.quotientResidueLog hzeta row
    (classOfUnit (basicVandiverUnit491 hzeta j)) = _
  rw [certificate491.quotientResidueLog_classOfUnit]
  exact correctedResidueLog_basicVandiverUnit491 hzeta row j

omit [NumberField K] [IsCyclotomicExtension {491} ℚ K]
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

/-- Vandiver's positive weight reduced modulo `491`. -/
def weightMod491 (i : Fin 244) (j : VandiverFactorIndex491) : ZMod 491 :=
  (teichmullerRoot491 : ZMod 491) ^
    (491 ^ 2 - 2 * (i.val + 1) * j.val)

theorem diagonalWeight491_cast (i : Fin 244)
    (j : VandiverFactorIndex491) :
    (diagonalWeight491 i j : ZMod 491) =
      weightMod491 i j := by
  simp [diagonalWeight491, integralDiagonalWeight, weightMod491]

theorem quotientResidueLinear_diagonalVandiverUnit491_formula
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 491)
    (row i : Fin 244) :
    certificate491.quotientResidueLinear hzeta row
        (classOfUnit (diagonalVandiverUnit491 hzeta i)) =
      ∑ j : VandiverFactorIndex491,
        weightMod491 i j * basicEdgeSymbol491 row j := by
  rw [diagonalVandiverUnit491, classOfUnit_prod_pow]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_nsmul, quotientResidueLinear_basicVandiverUnit491]
  simp only [nsmul_eq_mul]
  rw [diagonalWeight491_cast]

/-! ## Algebraic Fourier factorization -/

theorem cycleClassSymbol491_zero (row : Fin 244) :
    cycleClassSymbol491 row 0 = 0 := by
  simp [cycleClassSymbol491]

theorem cycleClassSymbol491_succ (row j : Fin 244) :
    cycleClassSymbol491 row (j.val + 1) =
      Fermat.FourHundredNinetyOne.CircularUnitMatrix.matrix row
        (cycleColumn491 j) := by
  rw [cycleClassSymbol491, dif_pos]
  · congr
  · omega

theorem cycleClassSymbol491_last (row : Fin 244) :
    cycleClassSymbol491 row 245 = 0 := by
  simp [cycleClassSymbol491]

theorem weighted_edge_sum491 (row : Fin 244)
    (w : Fin 245 → ZMod 491) :
    (∑ j : Fin 245, w j * basicEdgeSymbol491 row j) =
      ∑ ell : Fin 244,
        Fermat.FourHundredNinetyOne.CircularUnitMatrix.matrix row
            (cycleColumn491 ell) *
          (w ell.castSucc - w ell.succ) := by
  simp_rw [basicEdgeSymbol491, mul_sub]
  rw [Finset.sum_sub_distrib]
  have hfirst :
      (∑ j : Fin 245, w j * cycleClassSymbol491 row (j.val + 1)) =
        ∑ ell : Fin 244,
          w ell.castSucc *
            Fermat.FourHundredNinetyOne.CircularUnitMatrix.matrix row
              (cycleColumn491 ell) := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, cycleClassSymbol491_succ, Fin.val_last]
    rw [show 244 + 1 = 245 by norm_num, cycleClassSymbol491_last,
      mul_zero, add_zero]
  have hsecond :
      (∑ j : Fin 245, w j * cycleClassSymbol491 row j.val) =
        ∑ ell : Fin 244,
          w ell.succ *
            Fermat.FourHundredNinetyOne.CircularUnitMatrix.matrix row
              (cycleColumn491 ell) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, cycleClassSymbol491_zero, mul_zero, zero_add,
      Fin.val_succ, cycleClassSymbol491_succ]
  rw [hfirst, hsecond, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ell _
  ring

theorem weightMod491_castSucc_sub_succ (ell i : Fin 244) :
    weightMod491 i ell.castSucc - weightMod491 i ell.succ =
      fourierChange491 ell i := by
  let r : ZMod 491 := teichmullerRoot491
  let n := i.val + 1
  let L := ell.val + 1
  have hn : n ≤ 244 := by simp [n]
  have hL : L ≤ 244 := by simp [L]
  have hn2 : 2 * n ≤ 490 := by omega
  have hpositive : 2 * n * L ≤ 491 ^ 2 := by
    calc
      2 * n * L ≤ 2 * 244 * 244 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn) hL
      _ ≤ 491 ^ 2 := by norm_num
  have hsplit :
      (490 - 2 * n) * L = 490 * L - 2 * n * L :=
    Nat.sub_mul 490 (2 * n) L
  have hdecomp :
      491 ^ 2 - 2 * n * L =
        1 + (490 - 2 * n) * L + 490 * (492 - L) := by
    rw [hsplit]
    have hwithin : 2 * n * L ≤ 490 * L :=
      Nat.mul_le_mul_right L hn2
    omega
  have hr490 : r ^ 490 = 1 :=
    teichmullerRoot491_isPrimitive.pow_eq_one
  have hsecond :
      r ^ (491 ^ 2 - 2 * n * L) =
        r * (r ^ (490 - 2 * n)) ^ L := by
    rw [hdecomp, pow_add, pow_add]
    rw [show r ^ 1 = r by simp,
      show r ^ ((490 - 2 * n) * L) =
          (r ^ (490 - 2 * n)) ^ L by rw [pow_mul],
      show r ^ (490 * (492 - L)) = 1 by
        rw [pow_mul, hr490, one_pow]]
    simp
  have hstep :
      2 * n * L = 2 * n * ell.val + 2 * n := by
    simp only [L]
    ring
  have hfirstExp :
      491 ^ 2 - 2 * n * ell.val =
        (491 ^ 2 - 2 * n * L) + 2 * n := by
    have hfirstBound : 2 * n * ell.val ≤ 491 ^ 2 := by
      calc
        2 * n * ell.val ≤ 2 * n * L :=
          Nat.mul_le_mul_left (2 * n) (by simp [L])
        _ ≤ 491 ^ 2 := hpositive
    omega
  rw [weightMod491]
  change r ^ (491 ^ 2 - 2 * n * ell.val) -
      r ^ (491 ^ 2 - 2 * n * L) = fourierChange491 ell i
  rw [hfirstExp, pow_add, hsecond, fourierChange491_apply]
  simp only [vandermondeNode491, fourierScale491, n, L, r]
  rw [show 488 - 2 * i.val = 490 - 2 * (i.val + 1) by omega]
  rw [show ell.val + 1 = L by rfl]
  ring

noncomputable def cycleCircularMatrix491 :
    Matrix (Fin 244) (Fin 244) (ZMod 491) :=
  Fermat.FourHundredNinetyOne.CircularUnitMatrix.matrix.submatrix id
    cycleColumnEquiv491

theorem cycleCircularMatrix491_det_ne_zero :
    cycleCircularMatrix491.det ≠ 0 := by
  rw [cycleCircularMatrix491, Matrix.det_permute']
  exact mul_ne_zero
    (by
      exact ((Equiv.Perm.sign cycleColumnEquiv491).isUnit.map
        (Int.castRingHom (ZMod 491))).ne_zero)
    Fermat.FourHundredNinetyOne.CircularUnitCertificate.matrix_det_ne_zero

/-- The actual diagonal residue matrix, factored into its circular and
Fourier components. -/
noncomputable def diagonalResidueMatrix491 :
    Matrix (Fin 244) (Fin 244) (ZMod 491) :=
  cycleCircularMatrix491 * fourierChange491

theorem diagonalResidueMatrix491_det_ne_zero :
    diagonalResidueMatrix491.det ≠ 0 := by
  rw [diagonalResidueMatrix491, Matrix.det_mul]
  exact mul_ne_zero cycleCircularMatrix491_det_ne_zero
    fourierChange491_det_ne_zero

theorem weighted_edge_sum491_eq_matrix (row i : Fin 244) :
    (∑ j : Fin 245, weightMod491 i j * basicEdgeSymbol491 row j) =
      diagonalResidueMatrix491 row i := by
  rw [weighted_edge_sum491]
  simp_rw [weightMod491_castSucc_sub_succ]
  rfl

@[simp]
theorem quotientResidueLinear_diagonalVandiverUnit491 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491) (row i : Fin 244) :
    certificate491.quotientResidueLinear hzeta row
        (classOfUnit (diagonalVandiverUnit491 hzeta i)) =
      diagonalResidueMatrix491 row i := by
  rw [quotientResidueLinear_diagonalVandiverUnit491_formula]
  exact weighted_edge_sum491_eq_matrix row i

theorem evalMatrix_diagonalVandiverUnit491 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491) :
    evalMatrix (classOfUnit ∘ diagonalVandiverUnit491 hzeta)
        (certificate491.residueFunctionals hzeta) =
      diagonalResidueMatrix491 := by
  ext row i
  exact quotientResidueLinear_diagonalVandiverUnit491 hzeta row i

theorem not_dvd_diagonalVandiverUnit491_full_index {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491) :
    ¬491 ∣
      (Subgroup.closure (Set.range (diagonalVandiverUnit491 hzeta)) ⊔
        NumberField.Units.torsion K).index := by
  apply not_dvd_unitIndex_of_eval_det_ne_zero
    (certificate491.basisModTorsion (K := K))
      (diagonalVandiverUnit491 hzeta)
      (certificate491.residueFunctionals hzeta)
  rw [evalMatrix_diagonalVandiverUnit491]
  exact diagonalResidueMatrix491_det_ne_zero

theorem ambient_closure_finiteIndex {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491) :
    (Subgroup.closure
      (Set.range (diagonalVandiverUnit491 hzeta))).FiniteIndex := by
  have hnot := not_dvd_diagonalVandiverUnit491_full_index hzeta
  have hsup :
      (Subgroup.closure (Set.range (diagonalVandiverUnit491 hzeta)) ⊔
        NumberField.Units.torsion K).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff]
    intro hzero
    apply hnot
    rw [hzero]
    exact dvd_zero 491
  exact (NumberField.Units.finiteIndex_iff_sup_torsion_finiteIndex
    (Subgroup.closure (Set.range
      (diagonalVandiverUnit491 hzeta)))).2 hsup

theorem real_closure_finiteIndex {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491) :
    (Subgroup.closure
      (Set.range (diagonalVandiverUnitFamily491 hzeta))).FiniteIndex := by
  letI :
      (Subgroup.closure (Set.range fun i : Fin 244 ↦
        ((diagonalVandiverUnitFamily491 hzeta i :
          NumberField.IsCMField.realUnits K) :
            (RingOfIntegers K)ˣ))).FiniteIndex := by
    simpa [diagonalVandiverUnitFamily491] using
      ambient_closure_finiteIndex hzeta
  exact Fermat.Irregular.VandiverFiniteIndex.closure_range_subtype
    (NumberField.IsCMField.realUnits K)
      (diagonalVandiverUnitFamily491 hzeta)

end

end Fermat.FourHundredNinetyOne.VandiverDiagonalUnits
