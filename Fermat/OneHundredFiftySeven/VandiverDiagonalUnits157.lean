import Fermat.Irregular.VandiverDiagonalLogDerivative
import Fermat.Irregular.VandiverFiniteIndex
import Fermat.OneHundredFiftySeven.VandiverDiagonalUnitResidues157

/-!
# Vandiver's diagonal real-unit family at exponent 157

This module realizes the integral diagonal family used in Vandiver's
Lemma II:

`epsilon(w) = w^123 * (w^226 - 1) / (w - 1)`.

The corrected source range is `j = 0, ..., 77`; the positive weight at
source index `i+1` is

`226^(157^2 - 2*(i+1)*j)`.

Finite index is proved without a second giant inverse table.  The
auxiliary-prime evaluation matrix factors as the existing circular-unit
matrix (with its columns cyclically reordered) times the scaled
Vandermonde matrix certified in `VandiverDiagonalUnitResidues157`.
-/

open scoped NumberField

namespace Fermat.OneHundredFiftySeven.VandiverDiagonalUnits

noncomputable section

open Fermat.Irregular
open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitIndex
open Fermat.Irregular.CircularUnitResidues
open Fermat.Irregular.CircularUnitResidues.Certificate
open Fermat.Irregular.CircularUnits
open Fermat.Irregular.VandiverDiagonalLogDerivative
open Fermat.OneHundredFiftySeven.VandiverDiagonalArithmetic
open Fermat.OneHundredFiftySeven.VandiverDiagonalUnitResidues
open NumberField NumberField.Units

local instance : Fact (Nat.Prime 157) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 7537) := ⟨by norm_num⟩

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The corrected source range `j = 0, ..., 77`. -/
abbrev VandiverFactorIndex157 := Fin 78

theorem card_vandiverFactorIndex157 :
    Fintype.card VandiverFactorIndex157 = 78 := by decide

/-- Vandiver's literal positive integral weight. -/
def diagonalWeight157 (i : Fin 77) (j : VandiverFactorIndex157) : ℕ :=
  integralDiagonalWeight 157 teichmullerRoot157 (i.val + 1) j.val

theorem diagonalWeight157_eq (i : Fin 77) (j : VandiverFactorIndex157) :
    diagonalWeight157 i j =
      226 ^ (157 ^ 2 - 2 * (i.val + 1) * j.val) := by
  rfl

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {157} ℚ K] [NumberField.IsCMField K]

omit [NumberField K] [IsCyclotomicExtension {157} ℚ K]
    [NumberField.IsCMField K] in
theorem conjugate_isPrimitive {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 157)
    (j : VandiverFactorIndex157) :
    IsPrimitiveRoot (zeta ^ conjugateExponent157 j) 157 := by
  apply hzeta.pow_of_coprime
  exact (by norm_num : Nat.Coprime 226 157).pow_left j.val

/-- The literal basic factor of geometric length `226`. -/
def basicVandiverUnit157 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 157)
    (j : VandiverFactorIndex157) : (RingOfIntegers K)ˣ :=
  normalizedCircularUnit (p := 157) (a := 226)
    (conjugate_isPrimitive hzeta j) (by norm_num) (by norm_num) 123

omit [NumberField K] [IsCyclotomicExtension {157} ℚ K]
    [NumberField.IsCMField K] in
theorem conjugate_toInteger {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 157)
    (j : VandiverFactorIndex157) :
    (conjugate_isPrimitive hzeta j).toInteger =
      hzeta.toInteger ^ conjugateExponent157 j := by
  apply RingOfIntegers.ext
  rfl

omit [IsCyclotomicExtension {157} ℚ K] in
theorem basicVandiverUnit157_mem_realUnits {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 157)
    (j : VandiverFactorIndex157) :
    basicVandiverUnit157 hzeta j ∈
      NumberField.IsCMField.realUnits K := by
  apply normalizedCircularUnit_mem_realUnits
    (p := 157) (a := 226) (e := 123)
  decide

/-- The ambient integral diagonal unit `(E_(i+1)(zeta))^rho`. -/
def diagonalVandiverUnit157 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 157) (i : Fin 77) :
    (RingOfIntegers K)ˣ :=
  ∏ j : VandiverFactorIndex157,
    basicVandiverUnit157 hzeta j ^ diagonalWeight157 i j

omit [IsCyclotomicExtension {157} ℚ K] in
theorem diagonalVandiverUnit157_mem_realUnits {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 157) (i : Fin 77) :
    diagonalVandiverUnit157 hzeta i ∈
      NumberField.IsCMField.realUnits K := by
  apply Subgroup.prod_mem
  intro j hj
  exact Subgroup.pow_mem _
    (basicVandiverUnit157_mem_realUnits hzeta j) _

/-- The seventy-seven source units in the real-unit subgroup. -/
def diagonalVandiverUnitFamily157 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 157) :
    Fin 77 → NumberField.IsCMField.realUnits K :=
  fun i ↦ ⟨diagonalVandiverUnit157 hzeta i,
    diagonalVandiverUnit157_mem_realUnits hzeta i⟩

omit [IsCyclotomicExtension {157} ℚ K] in
@[simp]
theorem diagonalVandiverUnitFamily157_coe {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 157) (i : Fin 77) :
    ((diagonalVandiverUnitFamily157 hzeta i :
      NumberField.IsCMField.realUnits K) : (RingOfIntegers K)ˣ) =
      diagonalVandiverUnit157 hzeta i := rfl

/-! ## Evaluation of the actual units -/

omit [NumberField.IsCMField K] in
theorem reductionHom_basicVandiverUnit157 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 157) (row : Fin 77)
    (j : VandiverFactorIndex157) :
    certificate157.reductionHom hzeta row
        (basicVandiverUnit157 hzeta j : RingOfIntegers K) =
      basicResidueValue157 row j := by
  unfold basicVandiverUnit157
  rw [normalizedCircularUnit_val]
  rw [conjugate_toInteger (hzeta := hzeta) j]
  simp only [map_mul, map_pow, map_sum, certificate157.reductionHom_zeta]
  rfl

omit [IsCyclotomicExtension {157} ℚ K] in
@[simp]
theorem realUnitNorm_basicVandiverUnit157 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 157)
    (j : VandiverFactorIndex157) :
    realUnitNorm (basicVandiverUnit157 hzeta j) =
      basicVandiverUnit157 hzeta j ^ 2 := by
  change basicVandiverUnit157 hzeta j *
    NumberField.IsCMField.unitsComplexConj K
      (basicVandiverUnit157 hzeta j) = _
  rw [(NumberField.IsCMField.unitsComplexConj_eq_self_iff K _).mpr
    (basicVandiverUnit157_mem_realUnits hzeta j)]
  exact (pow_two _).symm

theorem correctedResidueLog_basicVandiverUnit157 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 157) (row : Fin 77)
    (j : VandiverFactorIndex157) :
    certificate157.correctedResidueLog hzeta row
        (Additive.ofMul (basicVandiverUnit157 hzeta j)) =
      basicEdgeSymbol157 row j := by
  let u : (ZMod 7537)ˣ :=
    Units.map (certificate157.reductionHom hzeta row)
      (realUnitNorm (basicVandiverUnit157 hzeta j))
  have huval : (u : ZMod 7537) = basicResidueValue157 row j ^ 2 := by
    dsimp [u]
    rw [realUnitNorm_basicVandiverUnit157, Units.val_pow_eq_pow_val,
      map_pow, reductionHom_basicVandiverUnit157]
  have hpow : ((u : ZMod 7537) ^ 48) =
      certificate157.root ^ ((basicEdgeSymbol157 row j).val * 2) := by
    calc
      (u : ZMod 7537) ^ 48 =
          (basicResidueValue157 row j ^ 2) ^ 48 := by rw [huval]
      _ = (basicResidueValue157 row j ^ 48) ^ 2 := by ring
      _ = (certificate157.root ^
          (basicEdgeSymbol157 row j).val) ^ 2 := by
        rw [basicResidueValue157_symbol]
      _ = certificate157.root ^
          ((basicEdgeSymbol157 row j).val * 2) := by rw [pow_mul]
  change (2 : ZMod 157)⁻¹ *
      certificate157.residueLog (Additive.ofMul u) =
    basicEdgeSymbol157 row j
  rw [certificate157.residueLog_eq_of_pow_eq u _ hpow]
  rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  have hhalf : (2 : ZMod 157)⁻¹ * 2 = 1 := by decide
  calc
    (2 : ZMod 157)⁻¹ * (basicEdgeSymbol157 row j * 2) =
        (2⁻¹ * 2) * basicEdgeSymbol157 row j := by ring
    _ = basicEdgeSymbol157 row j := by rw [hhalf, one_mul]

@[simp]
theorem quotientResidueLinear_basicVandiverUnit157 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 157) (row : Fin 77)
    (j : VandiverFactorIndex157) :
    certificate157.quotientResidueLinear hzeta row
        (classOfUnit (basicVandiverUnit157 hzeta j)) =
      basicEdgeSymbol157 row j := by
  change certificate157.quotientResidueLog hzeta row
    (classOfUnit (basicVandiverUnit157 hzeta j)) = _
  rw [certificate157.quotientResidueLog_classOfUnit]
  exact correctedResidueLog_basicVandiverUnit157 hzeta row j

omit [NumberField K] [IsCyclotomicExtension {157} ℚ K]
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

/-- Vandiver's positive weight reduced modulo `157`. -/
def weightMod157 (i : Fin 77) (j : VandiverFactorIndex157) : ZMod 157 :=
  (teichmullerRoot157 : ZMod 157) ^
    (157 ^ 2 - 2 * (i.val + 1) * j.val)

theorem diagonalWeight157_cast (i : Fin 77)
    (j : VandiverFactorIndex157) :
    (diagonalWeight157 i j : ZMod 157) =
      weightMod157 i j := by
  simp [diagonalWeight157, integralDiagonalWeight, weightMod157]

theorem quotientResidueLinear_diagonalVandiverUnit157_formula
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 157)
    (row i : Fin 77) :
    certificate157.quotientResidueLinear hzeta row
        (classOfUnit (diagonalVandiverUnit157 hzeta i)) =
      ∑ j : VandiverFactorIndex157,
        weightMod157 i j * basicEdgeSymbol157 row j := by
  rw [diagonalVandiverUnit157, classOfUnit_prod_pow]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_nsmul, quotientResidueLinear_basicVandiverUnit157]
  simp only [nsmul_eq_mul]
  rw [diagonalWeight157_cast]

/-! ## Algebraic Fourier factorization -/

theorem cycleClassSymbol157_zero (row : Fin 77) :
    cycleClassSymbol157 row 0 = 0 := by
  simp [cycleClassSymbol157]

theorem cycleClassSymbol157_succ (row j : Fin 77) :
    cycleClassSymbol157 row (j.val + 1) =
      Fermat.OneHundredFiftySeven.CircularUnitMatrix.matrix row
        (cycleColumn157 j) := by
  rw [cycleClassSymbol157, dif_pos]
  · congr
  · omega

theorem cycleClassSymbol157_last (row : Fin 77) :
    cycleClassSymbol157 row 78 = 0 := by
  simp [cycleClassSymbol157]

theorem weighted_edge_sum157 (row : Fin 77)
    (w : Fin 78 → ZMod 157) :
    (∑ j : Fin 78, w j * basicEdgeSymbol157 row j) =
      ∑ ell : Fin 77,
        Fermat.OneHundredFiftySeven.CircularUnitMatrix.matrix row
            (cycleColumn157 ell) *
          (w ell.castSucc - w ell.succ) := by
  simp_rw [basicEdgeSymbol157, mul_sub]
  rw [Finset.sum_sub_distrib]
  have hfirst :
      (∑ j : Fin 78, w j * cycleClassSymbol157 row (j.val + 1)) =
        ∑ ell : Fin 77,
          w ell.castSucc *
            Fermat.OneHundredFiftySeven.CircularUnitMatrix.matrix row
              (cycleColumn157 ell) := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, cycleClassSymbol157_succ, Fin.val_last]
    rw [show 77 + 1 = 78 by norm_num, cycleClassSymbol157_last,
      mul_zero, add_zero]
  have hsecond :
      (∑ j : Fin 78, w j * cycleClassSymbol157 row j.val) =
        ∑ ell : Fin 77,
          w ell.succ *
            Fermat.OneHundredFiftySeven.CircularUnitMatrix.matrix row
              (cycleColumn157 ell) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, cycleClassSymbol157_zero, mul_zero, zero_add,
      Fin.val_succ, cycleClassSymbol157_succ]
  rw [hfirst, hsecond, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ell _
  ring

theorem weightMod157_castSucc_sub_succ (ell i : Fin 77) :
    weightMod157 i ell.castSucc - weightMod157 i ell.succ =
      fourierChange157 ell i := by
  let r : ZMod 157 := teichmullerRoot157
  let n := i.val + 1
  let L := ell.val + 1
  have hn : n ≤ 77 := by simp [n]
  have hL : L ≤ 77 := by simp [L]
  have hn2 : 2 * n ≤ 156 := by omega
  have hpositive : 2 * n * L ≤ 157 ^ 2 := by
    calc
      2 * n * L ≤ 2 * 77 * 77 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn) hL
      _ ≤ 157 ^ 2 := by norm_num
  have hsplit :
      (156 - 2 * n) * L = 156 * L - 2 * n * L :=
    Nat.sub_mul 156 (2 * n) L
  have hdecomp :
      157 ^ 2 - 2 * n * L =
        1 + (156 - 2 * n) * L + 156 * (158 - L) := by
    rw [hsplit]
    have hwithin : 2 * n * L ≤ 156 * L :=
      Nat.mul_le_mul_right L hn2
    omega
  have hr156 : r ^ 156 = 1 :=
    teichmullerRoot157_isPrimitive.pow_eq_one
  have hsecond :
      r ^ (157 ^ 2 - 2 * n * L) =
        r * (r ^ (156 - 2 * n)) ^ L := by
    rw [hdecomp, pow_add, pow_add]
    rw [show r ^ 1 = r by simp,
      show r ^ ((156 - 2 * n) * L) =
          (r ^ (156 - 2 * n)) ^ L by rw [pow_mul],
      show r ^ (156 * (158 - L)) = 1 by
        rw [pow_mul, hr156, one_pow]]
    simp
  have hstep :
      2 * n * L = 2 * n * ell.val + 2 * n := by
    simp only [L]
    ring
  have hfirstExp :
      157 ^ 2 - 2 * n * ell.val =
        (157 ^ 2 - 2 * n * L) + 2 * n := by
    have hfirstBound : 2 * n * ell.val ≤ 157 ^ 2 := by
      calc
        2 * n * ell.val ≤ 2 * n * L :=
          Nat.mul_le_mul_left (2 * n) (by simp [L])
        _ ≤ 157 ^ 2 := hpositive
    omega
  rw [weightMod157]
  change r ^ (157 ^ 2 - 2 * n * ell.val) -
      r ^ (157 ^ 2 - 2 * n * L) = fourierChange157 ell i
  rw [hfirstExp, pow_add, hsecond, fourierChange157_apply]
  simp only [vandermondeNode157, fourierScale157, n, L, r]
  rw [show 154 - 2 * i.val = 156 - 2 * (i.val + 1) by omega]
  rw [show ell.val + 1 = L by rfl]
  ring

noncomputable def cycleCircularMatrix157 :
    Matrix (Fin 77) (Fin 77) (ZMod 157) :=
  Fermat.OneHundredFiftySeven.CircularUnitMatrix.matrix.submatrix id
    cycleColumnEquiv157

theorem cycleCircularMatrix157_det_ne_zero :
    cycleCircularMatrix157.det ≠ 0 := by
  rw [cycleCircularMatrix157, Matrix.det_permute']
  exact mul_ne_zero
    (by
      exact ((Equiv.Perm.sign cycleColumnEquiv157).isUnit.map
        (Int.castRingHom (ZMod 157))).ne_zero)
    Fermat.OneHundredFiftySeven.CircularUnitCertificate.matrix_det_ne_zero

/-- The actual diagonal residue matrix, factored into its circular and
Fourier components. -/
noncomputable def diagonalResidueMatrix157 :
    Matrix (Fin 77) (Fin 77) (ZMod 157) :=
  cycleCircularMatrix157 * fourierChange157

theorem diagonalResidueMatrix157_det_ne_zero :
    diagonalResidueMatrix157.det ≠ 0 := by
  rw [diagonalResidueMatrix157, Matrix.det_mul]
  exact mul_ne_zero cycleCircularMatrix157_det_ne_zero
    fourierChange157_det_ne_zero

theorem weighted_edge_sum157_eq_matrix (row i : Fin 77) :
    (∑ j : Fin 78, weightMod157 i j * basicEdgeSymbol157 row j) =
      diagonalResidueMatrix157 row i := by
  rw [weighted_edge_sum157]
  simp_rw [weightMod157_castSucc_sub_succ]
  rfl

@[simp]
theorem quotientResidueLinear_diagonalVandiverUnit157 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 157) (row i : Fin 77) :
    certificate157.quotientResidueLinear hzeta row
        (classOfUnit (diagonalVandiverUnit157 hzeta i)) =
      diagonalResidueMatrix157 row i := by
  rw [quotientResidueLinear_diagonalVandiverUnit157_formula]
  exact weighted_edge_sum157_eq_matrix row i

theorem evalMatrix_diagonalVandiverUnit157 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 157) :
    evalMatrix (classOfUnit ∘ diagonalVandiverUnit157 hzeta)
        (certificate157.residueFunctionals hzeta) =
      diagonalResidueMatrix157 := by
  ext row i
  exact quotientResidueLinear_diagonalVandiverUnit157 hzeta row i

theorem not_dvd_diagonalVandiverUnit157_full_index {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 157) :
    ¬157 ∣
      (Subgroup.closure (Set.range (diagonalVandiverUnit157 hzeta)) ⊔
        NumberField.Units.torsion K).index := by
  apply not_dvd_unitIndex_of_eval_det_ne_zero
    (certificate157.basisModTorsion (K := K))
      (diagonalVandiverUnit157 hzeta)
      (certificate157.residueFunctionals hzeta)
  rw [evalMatrix_diagonalVandiverUnit157]
  exact diagonalResidueMatrix157_det_ne_zero

theorem ambient_closure_finiteIndex {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 157) :
    (Subgroup.closure
      (Set.range (diagonalVandiverUnit157 hzeta))).FiniteIndex := by
  have hnot := not_dvd_diagonalVandiverUnit157_full_index hzeta
  have hsup :
      (Subgroup.closure (Set.range (diagonalVandiverUnit157 hzeta)) ⊔
        NumberField.Units.torsion K).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff]
    intro hzero
    apply hnot
    rw [hzero]
    exact dvd_zero 157
  exact (NumberField.Units.finiteIndex_iff_sup_torsion_finiteIndex
    (Subgroup.closure (Set.range
      (diagonalVandiverUnit157 hzeta)))).2 hsup

theorem real_closure_finiteIndex {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 157) :
    (Subgroup.closure
      (Set.range (diagonalVandiverUnitFamily157 hzeta))).FiniteIndex := by
  letI :
      (Subgroup.closure (Set.range fun i : Fin 77 ↦
        ((diagonalVandiverUnitFamily157 hzeta i :
          NumberField.IsCMField.realUnits K) :
            (RingOfIntegers K)ˣ))).FiniteIndex := by
    simpa [diagonalVandiverUnitFamily157] using
      ambient_closure_finiteIndex hzeta
  exact Fermat.Irregular.VandiverFiniteIndex.closure_range_subtype
    (NumberField.IsCMField.realUnits K)
      (diagonalVandiverUnitFamily157 hzeta)

end

end Fermat.OneHundredFiftySeven.VandiverDiagonalUnits
