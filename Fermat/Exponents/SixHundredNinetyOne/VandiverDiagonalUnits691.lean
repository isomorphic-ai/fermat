import Fermat.Descent.Irregular.VandiverDiagonalLogDerivative
import Fermat.Descent.Irregular.VandiverFiniteIndex
import Fermat.Exponents.SixHundredNinetyOne.VandiverDiagonalUnitResidues691

/-!
# Vandiver's diagonal real-unit family at exponent 691

This module realizes the integral diagonal family

`epsilon(w) = w^287 * (w^4955 - 1) / (w - 1)`.

The corrected source range is `j = 0, ..., 344`; the positive weight at
source index `i+1` is

`4955^(691^2 - 2*(i+1)*j)`.

Finite index is proved without a dense inverse table.  The auxiliary-prime
evaluation matrix factors as the existing circular-unit matrix (with its
columns cyclically reordered) times the scaled Vandermonde matrix certified
in `VandiverDiagonalUnitResidues691`.
-/

open scoped NumberField

namespace Fermat.SixHundredNinetyOne.VandiverDiagonalUnits

noncomputable section

open Fermat.Irregular
open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitIndex
open Fermat.Irregular.CircularUnitResidues
open Fermat.Irregular.CircularUnitResidues.Certificate
open Fermat.Irregular.CircularUnits
open Fermat.Irregular.VandiverDiagonalLogDerivative
open Fermat.SixHundredNinetyOne.VandiverDiagonalArithmetic
open Fermat.SixHundredNinetyOne.VandiverDiagonalUnitResidues
open NumberField NumberField.Units

local instance : Fact (Nat.Prime 691) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 11057) := ⟨by norm_num⟩

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The corrected source range `j = 0, ..., 344`. -/
abbrev VandiverFactorIndex691 := Fin 345

theorem card_vandiverFactorIndex691 :
    Fintype.card VandiverFactorIndex691 = 345 := by decide

/-- The power of the chosen root occurring in the `j`th conjugate. -/
def conjugateExponent691 (j : VandiverFactorIndex691) : ℕ :=
  VandiverDiagonalUnitResidues.conjugateExponent691 j

/-- Vandiver's literal positive integral weight. -/
def diagonalWeight691 (i : Fin 344) (j : VandiverFactorIndex691) : ℕ :=
  integralDiagonalWeight 691 teichmullerRoot691 (i.val + 1) j.val

theorem diagonalWeight691_eq (i : Fin 344) (j : VandiverFactorIndex691) :
    diagonalWeight691 i j =
      4955 ^ (691 ^ 2 - 2 * (i.val + 1) * j.val) := by
  rfl

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {691} ℚ K] [NumberField.IsCMField K]

omit [NumberField K] [IsCyclotomicExtension {691} ℚ K]
    [NumberField.IsCMField K] in
theorem conjugate_isPrimitive {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 691)
    (j : VandiverFactorIndex691) :
    IsPrimitiveRoot (zeta ^ conjugateExponent691 j) 691 := by
  apply hzeta.pow_of_coprime
  exact (by norm_num : Nat.Coprime 4955 691).pow_left j.val

/-- The literal basic factor of geometric length `4955`. -/
def basicVandiverUnit691 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 691)
    (j : VandiverFactorIndex691) : (RingOfIntegers K)ˣ :=
  normalizedCircularUnit (p := 691) (a := 4955)
    (conjugate_isPrimitive hzeta j) (by norm_num) (by norm_num) 287

omit [NumberField K] [IsCyclotomicExtension {691} ℚ K]
    [NumberField.IsCMField K] in
theorem conjugate_toInteger {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 691)
    (j : VandiverFactorIndex691) :
    (conjugate_isPrimitive hzeta j).toInteger =
      hzeta.toInteger ^ conjugateExponent691 j := by
  apply RingOfIntegers.ext
  rfl

omit [IsCyclotomicExtension {691} ℚ K] in
theorem basicVandiverUnit691_mem_realUnits {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 691)
    (j : VandiverFactorIndex691) :
    basicVandiverUnit691 hzeta j ∈
      NumberField.IsCMField.realUnits K := by
  apply normalizedCircularUnit_mem_realUnits
    (p := 691) (a := 4955) (e := 287)
  decide

/-- The ambient integral diagonal unit `(E_(i+1)(zeta))^rho`. -/
def diagonalVandiverUnit691 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 691) (i : Fin 344) :
    (RingOfIntegers K)ˣ :=
  ∏ j : VandiverFactorIndex691,
    basicVandiverUnit691 hzeta j ^ diagonalWeight691 i j

omit [IsCyclotomicExtension {691} ℚ K] in
theorem diagonalVandiverUnit691_mem_realUnits {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 691) (i : Fin 344) :
    diagonalVandiverUnit691 hzeta i ∈
      NumberField.IsCMField.realUnits K := by
  apply Subgroup.prod_mem
  intro j hj
  exact Subgroup.pow_mem _
    (basicVandiverUnit691_mem_realUnits hzeta j) _

/-- The 344 source units in the real-unit subgroup. -/
def diagonalVandiverUnitFamily691 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 691) :
    Fin 344 → NumberField.IsCMField.realUnits K :=
  fun i ↦ ⟨diagonalVandiverUnit691 hzeta i,
    diagonalVandiverUnit691_mem_realUnits hzeta i⟩

omit [IsCyclotomicExtension {691} ℚ K] in
@[simp]
theorem diagonalVandiverUnitFamily691_coe {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 691) (i : Fin 344) :
    ((diagonalVandiverUnitFamily691 hzeta i :
      NumberField.IsCMField.realUnits K) : (RingOfIntegers K)ˣ) =
      diagonalVandiverUnit691 hzeta i := rfl

/-! ## Evaluation of the actual units -/

omit [NumberField.IsCMField K] in
theorem reductionHom_basicVandiverUnit691 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 691) (row : Fin 344)
    (j : VandiverFactorIndex691) :
    certificate691.reductionHom hzeta row
        (basicVandiverUnit691 hzeta j : RingOfIntegers K) =
      basicResidueValue691 row j := by
  unfold basicVandiverUnit691
  rw [normalizedCircularUnit_val]
  rw [conjugate_toInteger (hzeta := hzeta) j]
  simp only [map_mul, map_pow, map_sum, certificate691.reductionHom_zeta]
  rfl

omit [IsCyclotomicExtension {691} ℚ K] in
@[simp]
theorem realUnitNorm_basicVandiverUnit691 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 691)
    (j : VandiverFactorIndex691) :
    realUnitNorm (basicVandiverUnit691 hzeta j) =
      basicVandiverUnit691 hzeta j ^ 2 := by
  change basicVandiverUnit691 hzeta j *
    NumberField.IsCMField.unitsComplexConj K
      (basicVandiverUnit691 hzeta j) = _
  rw [(NumberField.IsCMField.unitsComplexConj_eq_self_iff K _).mpr
    (basicVandiverUnit691_mem_realUnits hzeta j)]
  exact (pow_two _).symm

theorem correctedResidueLog_basicVandiverUnit691 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 691) (row : Fin 344)
    (j : VandiverFactorIndex691) :
    certificate691.correctedResidueLog hzeta row
        (Additive.ofMul (basicVandiverUnit691 hzeta j)) =
      basicEdgeSymbol691 row j := by
  let u : (ZMod 11057)ˣ :=
    Units.map (certificate691.reductionHom hzeta row)
      (realUnitNorm (basicVandiverUnit691 hzeta j))
  have huval : (u : ZMod 11057) = basicResidueValue691 row j ^ 2 := by
    dsimp [u]
    rw [realUnitNorm_basicVandiverUnit691, Units.val_pow_eq_pow_val,
      map_pow, reductionHom_basicVandiverUnit691]
  have hpow :
      ((u : ZMod 11057) ^ certificate691.symbolExponent) =
      certificate691.root ^ ((basicEdgeSymbol691 row j).val * 2) := by
    change (u : ZMod 11057) ^ 16 =
      certificate691.root ^ ((basicEdgeSymbol691 row j).val * 2)
    calc
      (u : ZMod 11057) ^ 16 =
          (basicResidueValue691 row j ^ 2) ^ 16 := by rw [huval]
      _ = (basicResidueValue691 row j ^ 16) ^ 2 := by
        simp only [← pow_mul]
      _ = (certificate691.root ^
          (basicEdgeSymbol691 row j).val) ^ 2 := by
        rw [basicResidueValue691_symbol]
      _ = certificate691.root ^
          ((basicEdgeSymbol691 row j).val * 2) := by rw [pow_mul]
  change (2 : ZMod 691)⁻¹ *
      certificate691.residueLog (Additive.ofMul u) =
    basicEdgeSymbol691 row j
  rw [certificate691.residueLog_eq_of_pow_eq u _ hpow]
  rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  have hhalf : (2 : ZMod 691)⁻¹ * 2 = 1 :=
    inv_mul_cancel₀ (by
      intro h
      have hdiv : 691 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 691).mp h
      norm_num at hdiv)
  calc
    (2 : ZMod 691)⁻¹ * (basicEdgeSymbol691 row j * 2) =
        (2⁻¹ * 2) * basicEdgeSymbol691 row j := by ring
    _ = basicEdgeSymbol691 row j := by rw [hhalf, one_mul]

@[simp]
theorem quotientResidueLinear_basicVandiverUnit691 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 691) (row : Fin 344)
    (j : VandiverFactorIndex691) :
    certificate691.quotientResidueLinear hzeta row
        (classOfUnit (basicVandiverUnit691 hzeta j)) =
      basicEdgeSymbol691 row j := by
  change certificate691.quotientResidueLog hzeta row
    (classOfUnit (basicVandiverUnit691 hzeta j)) = _
  rw [certificate691.quotientResidueLog_classOfUnit]
  exact correctedResidueLog_basicVandiverUnit691 hzeta row j

omit [NumberField K] [IsCyclotomicExtension {691} ℚ K]
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

/-- Vandiver's positive weight reduced modulo `691`. -/
def weightMod691 (i : Fin 344) (j : VandiverFactorIndex691) : ZMod 691 :=
  (teichmullerRoot691 : ZMod 691) ^
    (691 ^ 2 - 2 * (i.val + 1) * j.val)

theorem diagonalWeight691_cast (i : Fin 344)
    (j : VandiverFactorIndex691) :
    (diagonalWeight691 i j : ZMod 691) =
      weightMod691 i j := by
  simp [diagonalWeight691, integralDiagonalWeight, weightMod691]

theorem quotientResidueLinear_diagonalVandiverUnit691_formula
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 691)
    (row i : Fin 344) :
    certificate691.quotientResidueLinear hzeta row
        (classOfUnit (diagonalVandiverUnit691 hzeta i)) =
      ∑ j : VandiverFactorIndex691,
        weightMod691 i j * basicEdgeSymbol691 row j := by
  rw [diagonalVandiverUnit691, classOfUnit_prod_pow]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_nsmul, quotientResidueLinear_basicVandiverUnit691]
  simp only [nsmul_eq_mul]
  rw [diagonalWeight691_cast]

/-! ## Algebraic Fourier factorization -/

theorem cycleClassSymbol691_zero (row : Fin 344) :
    cycleClassSymbol691 row 0 = 0 := by
  simp [cycleClassSymbol691]

theorem cycleClassSymbol691_succ (row j : Fin 344) :
    cycleClassSymbol691 row (j.val + 1) =
      Fermat.SixHundredNinetyOne.CircularUnitMatrix.matrix row
        (cycleColumn691 j) := by
  rw [cycleClassSymbol691, dif_pos]
  · congr
  · omega

theorem cycleClassSymbol691_last (row : Fin 344) :
    cycleClassSymbol691 row 345 = 0 := by
  simp [cycleClassSymbol691]

theorem weighted_edge_sum691 (row : Fin 344)
    (w : Fin 345 → ZMod 691) :
    (∑ j : Fin 345, w j * basicEdgeSymbol691 row j) =
      ∑ ell : Fin 344,
        Fermat.SixHundredNinetyOne.CircularUnitMatrix.matrix row
            (cycleColumn691 ell) *
          (w ell.castSucc - w ell.succ) := by
  simp_rw [basicEdgeSymbol691, mul_sub]
  rw [Finset.sum_sub_distrib]
  have hfirst :
      (∑ j : Fin 345, w j * cycleClassSymbol691 row (j.val + 1)) =
        ∑ ell : Fin 344,
          w ell.castSucc *
            Fermat.SixHundredNinetyOne.CircularUnitMatrix.matrix row
              (cycleColumn691 ell) := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, cycleClassSymbol691_succ, Fin.val_last]
    rw [show 344 + 1 = 345 by norm_num, cycleClassSymbol691_last,
      mul_zero, add_zero]
  have hsecond :
      (∑ j : Fin 345, w j * cycleClassSymbol691 row j.val) =
        ∑ ell : Fin 344,
          w ell.succ *
            Fermat.SixHundredNinetyOne.CircularUnitMatrix.matrix row
              (cycleColumn691 ell) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, cycleClassSymbol691_zero, mul_zero, zero_add,
      Fin.val_succ, cycleClassSymbol691_succ]
  rw [hfirst, hsecond, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ell _
  ring

theorem weightMod691_castSucc_sub_succ (ell i : Fin 344) :
    weightMod691 i ell.castSucc - weightMod691 i ell.succ =
      fourierChange691 ell i := by
  let r : ZMod 691 := teichmullerRoot691
  let n := i.val + 1
  let L := ell.val + 1
  have hn : n ≤ 344 := by simp [n]
  have hL : L ≤ 344 := by simp [L]
  have hn2 : 2 * n ≤ 690 := by omega
  have hpositive : 2 * n * L ≤ 691 ^ 2 := by
    calc
      2 * n * L ≤ 2 * 344 * 344 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn) hL
      _ ≤ 691 ^ 2 := by norm_num
  have hsplit :
      (690 - 2 * n) * L = 690 * L - 2 * n * L :=
    Nat.sub_mul 690 (2 * n) L
  have hdecomp :
      691 ^ 2 - 2 * n * L =
        1 + (690 - 2 * n) * L + 690 * (692 - L) := by
    rw [hsplit]
    have hwithin : 2 * n * L ≤ 690 * L :=
      Nat.mul_le_mul_right L hn2
    omega
  have hr690 : r ^ 690 = 1 :=
    teichmullerRoot691_isPrimitive.pow_eq_one
  have hsecond :
      r ^ (691 ^ 2 - 2 * n * L) =
        r * (r ^ (690 - 2 * n)) ^ L := by
    rw [hdecomp, pow_add, pow_add]
    rw [show r ^ 1 = r by simp,
      show r ^ ((690 - 2 * n) * L) =
          (r ^ (690 - 2 * n)) ^ L by rw [pow_mul],
      show r ^ (690 * (692 - L)) = 1 by
        rw [pow_mul, hr690, one_pow]]
    simp
  have hstep :
      2 * n * L = 2 * n * ell.val + 2 * n := by
    simp only [L]
    ring
  have hfirstExp :
      691 ^ 2 - 2 * n * ell.val =
        (691 ^ 2 - 2 * n * L) + 2 * n := by
    have hfirstBound : 2 * n * ell.val ≤ 691 ^ 2 := by
      calc
        2 * n * ell.val ≤ 2 * n * L :=
          Nat.mul_le_mul_left (2 * n) (by simp [L])
        _ ≤ 691 ^ 2 := hpositive
    omega
  rw [weightMod691]
  change r ^ (691 ^ 2 - 2 * n * ell.val) -
      r ^ (691 ^ 2 - 2 * n * L) = fourierChange691 ell i
  rw [hfirstExp, pow_add, hsecond, fourierChange691_apply]
  simp only [vandermondeNode691, fourierScale691, n, L, r]
  rw [show 688 - 2 * i.val = 690 - 2 * (i.val + 1) by omega]
  rw [show ell.val + 1 = L by rfl]
  ring

noncomputable def cycleCircularMatrix691 :
    Matrix (Fin 344) (Fin 344) (ZMod 691) :=
  Fermat.SixHundredNinetyOne.CircularUnitMatrix.matrix.submatrix id
    cycleColumnEquiv691

theorem cycleCircularMatrix691_det_ne_zero :
    cycleCircularMatrix691.det ≠ 0 := by
  rw [cycleCircularMatrix691, Matrix.det_permute']
  exact mul_ne_zero
    (by
      exact ((Equiv.Perm.sign cycleColumnEquiv691).isUnit.map
        (Int.castRingHom (ZMod 691))).ne_zero)
    Fermat.SixHundredNinetyOne.CircularUnitCertificate.matrix_det_ne_zero

/-- The actual diagonal residue matrix, factored into its circular and
Fourier components. -/
noncomputable def diagonalResidueMatrix691 :
    Matrix (Fin 344) (Fin 344) (ZMod 691) :=
  cycleCircularMatrix691 * fourierChange691

theorem diagonalResidueMatrix691_det_ne_zero :
    diagonalResidueMatrix691.det ≠ 0 := by
  rw [diagonalResidueMatrix691, Matrix.det_mul]
  exact mul_ne_zero cycleCircularMatrix691_det_ne_zero
    fourierChange691_det_ne_zero

theorem weighted_edge_sum691_eq_matrix (row i : Fin 344) :
    (∑ j : Fin 345, weightMod691 i j * basicEdgeSymbol691 row j) =
      diagonalResidueMatrix691 row i := by
  rw [weighted_edge_sum691]
  simp_rw [weightMod691_castSucc_sub_succ]
  rfl

@[simp]
theorem quotientResidueLinear_diagonalVandiverUnit691 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 691) (row i : Fin 344) :
    certificate691.quotientResidueLinear hzeta row
        (classOfUnit (diagonalVandiverUnit691 hzeta i)) =
      diagonalResidueMatrix691 row i := by
  rw [quotientResidueLinear_diagonalVandiverUnit691_formula]
  exact weighted_edge_sum691_eq_matrix row i

theorem evalMatrix_diagonalVandiverUnit691 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 691) :
    evalMatrix (classOfUnit ∘ diagonalVandiverUnit691 hzeta)
        (certificate691.residueFunctionals hzeta) =
      diagonalResidueMatrix691 := by
  ext row i
  exact quotientResidueLinear_diagonalVandiverUnit691 hzeta row i

theorem not_dvd_diagonalVandiverUnit691_full_index {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 691) :
    ¬691 ∣
      (Subgroup.closure (Set.range (diagonalVandiverUnit691 hzeta)) ⊔
        NumberField.Units.torsion K).index := by
  apply not_dvd_unitIndex_of_eval_det_ne_zero
    (certificate691.basisModTorsion (K := K))
      (diagonalVandiverUnit691 hzeta)
      (certificate691.residueFunctionals hzeta)
  rw [evalMatrix_diagonalVandiverUnit691]
  exact diagonalResidueMatrix691_det_ne_zero

theorem ambient_closure_finiteIndex {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 691) :
    (Subgroup.closure
      (Set.range (diagonalVandiverUnit691 hzeta))).FiniteIndex := by
  have hnot := not_dvd_diagonalVandiverUnit691_full_index hzeta
  have hsup :
      (Subgroup.closure (Set.range (diagonalVandiverUnit691 hzeta)) ⊔
        NumberField.Units.torsion K).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff]
    intro hzero
    apply hnot
    rw [hzero]
    exact dvd_zero 691
  exact (NumberField.Units.finiteIndex_iff_sup_torsion_finiteIndex
    (Subgroup.closure (Set.range
      (diagonalVandiverUnit691 hzeta)))).2 hsup

theorem real_closure_finiteIndex {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 691) :
    (Subgroup.closure
      (Set.range (diagonalVandiverUnitFamily691 hzeta))).FiniteIndex := by
  letI :
      (Subgroup.closure (Set.range fun i : Fin 344 ↦
        ((diagonalVandiverUnitFamily691 hzeta i :
          NumberField.IsCMField.realUnits K) :
            (RingOfIntegers K)ˣ))).FiniteIndex := by
    simpa [diagonalVandiverUnitFamily691] using
      ambient_closure_finiteIndex hzeta
  exact Fermat.Irregular.VandiverFiniteIndex.closure_range_subtype
    (NumberField.IsCMField.realUnits K)
      (diagonalVandiverUnitFamily691 hzeta)

end

end Fermat.SixHundredNinetyOne.VandiverDiagonalUnits
