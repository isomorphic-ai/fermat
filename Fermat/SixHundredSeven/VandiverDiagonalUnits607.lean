import Fermat.Irregular.VandiverDiagonalLogDerivative
import Fermat.Irregular.VandiverFiniteIndex
import Fermat.SixHundredSeven.VandiverDiagonalUnitResidues607

/-!
# Vandiver's diagonal real-unit family at exponent 607

This module realizes the integral diagonal family

`epsilon(w) = w^201 * (w^813 - 1) / (w - 1)`.

The corrected source range is `j = 0, ..., 302`; the positive weight at
source index `i+1` is

`813^(607^2 - 2*(i+1)*j)`.

Finite index is proved without a dense inverse table. The auxiliary-prime
evaluation matrix factors as the existing circular-unit matrix (with its
columns cyclically reordered) times the scaled Vandermonde matrix certified
in `VandiverDiagonalUnitResidues607`.
-/

open scoped NumberField

namespace Fermat.SixHundredSeven.VandiverDiagonalUnits

noncomputable section

open Fermat.Irregular
open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitIndex
open Fermat.Irregular.CircularUnitResidues
open Fermat.Irregular.CircularUnitResidues.Certificate
open Fermat.Irregular.CircularUnits
open Fermat.Irregular.VandiverDiagonalLogDerivative
open Fermat.SixHundredSeven.VandiverDiagonalArithmetic
open Fermat.SixHundredSeven.VandiverDiagonalUnitResidues
open NumberField NumberField.Units

local instance : Fact (Nat.Prime 607) :=
  ⟨Fermat.SixHundredSeven.prime_607⟩
local instance : Fact (Nat.Prime 20639) :=
  ⟨Fermat.SixHundredSeven.prime_20639⟩

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The corrected source range `j = 0, ..., 302`. -/
abbrev VandiverFactorIndex607 := Fin 303

theorem card_vandiverFactorIndex607 :
    Fintype.card VandiverFactorIndex607 = 303 := by decide

/-- The power of the chosen root occurring in the `j`th conjugate. -/
def conjugateExponent607 (j : VandiverFactorIndex607) : ℕ :=
  VandiverDiagonalUnitResidues.conjugateExponent607 j

/-- Vandiver's literal positive integral weight. -/
def diagonalWeight607 (i : Fin 302) (j : VandiverFactorIndex607) : ℕ :=
  integralDiagonalWeight 607 teichmullerRoot607 (i.val + 1) j.val

theorem diagonalWeight607_eq (i : Fin 302) (j : VandiverFactorIndex607) :
    diagonalWeight607 i j =
      813 ^ (607 ^ 2 - 2 * (i.val + 1) * j.val) := by
  rfl

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {607} ℚ K] [NumberField.IsCMField K]

omit [NumberField K] [IsCyclotomicExtension {607} ℚ K]
    [NumberField.IsCMField K] in
theorem conjugate_isPrimitive {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 607)
    (j : VandiverFactorIndex607) :
    IsPrimitiveRoot (zeta ^ conjugateExponent607 j) 607 := by
  apply hzeta.pow_of_coprime
  exact (by norm_num : Nat.Coprime 813 607).pow_left j.val

/-- The literal basic factor of geometric length `813`. -/
def basicVandiverUnit607 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 607)
    (j : VandiverFactorIndex607) : (RingOfIntegers K)ˣ :=
  normalizedCircularUnit (p := 607) (a := 813)
    (conjugate_isPrimitive hzeta j) (by norm_num) (by norm_num) 201

omit [NumberField K] [IsCyclotomicExtension {607} ℚ K]
    [NumberField.IsCMField K] in
theorem conjugate_toInteger {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 607)
    (j : VandiverFactorIndex607) :
    (conjugate_isPrimitive hzeta j).toInteger =
      hzeta.toInteger ^ conjugateExponent607 j := by
  apply RingOfIntegers.ext
  rfl

omit [IsCyclotomicExtension {607} ℚ K] in
theorem basicVandiverUnit607_mem_realUnits {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 607)
    (j : VandiverFactorIndex607) :
    basicVandiverUnit607 hzeta j ∈
      NumberField.IsCMField.realUnits K := by
  apply normalizedCircularUnit_mem_realUnits
    (p := 607) (a := 813) (e := 201)
  decide

/-- The ambient integral diagonal unit `(E_(i+1)(zeta))^rho`. -/
def diagonalVandiverUnit607 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 607) (i : Fin 302) :
    (RingOfIntegers K)ˣ :=
  ∏ j : VandiverFactorIndex607,
    basicVandiverUnit607 hzeta j ^ diagonalWeight607 i j

omit [IsCyclotomicExtension {607} ℚ K] in
theorem diagonalVandiverUnit607_mem_realUnits {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 607) (i : Fin 302) :
    diagonalVandiverUnit607 hzeta i ∈
      NumberField.IsCMField.realUnits K := by
  apply Subgroup.prod_mem
  intro j hj
  exact Subgroup.pow_mem _
    (basicVandiverUnit607_mem_realUnits hzeta j) _

/-- The 302 source units in the real-unit subgroup. -/
def diagonalVandiverUnitFamily607 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 607) :
    Fin 302 → NumberField.IsCMField.realUnits K :=
  fun i ↦ ⟨diagonalVandiverUnit607 hzeta i,
    diagonalVandiverUnit607_mem_realUnits hzeta i⟩

omit [IsCyclotomicExtension {607} ℚ K] in
@[simp]
theorem diagonalVandiverUnitFamily607_coe {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 607) (i : Fin 302) :
    ((diagonalVandiverUnitFamily607 hzeta i :
      NumberField.IsCMField.realUnits K) : (RingOfIntegers K)ˣ) =
      diagonalVandiverUnit607 hzeta i := rfl

/-! ## Evaluation of the actual units -/

omit [NumberField.IsCMField K] in
theorem reductionHom_basicVandiverUnit607 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 607) (row : Fin 302)
    (j : VandiverFactorIndex607) :
    certificate607.reductionHom hzeta row
        (basicVandiverUnit607 hzeta j : RingOfIntegers K) =
      basicResidueValue607 row j := by
  unfold basicVandiverUnit607
  rw [normalizedCircularUnit_val]
  rw [conjugate_toInteger (hzeta := hzeta) j]
  simp only [map_mul, map_pow, map_sum, certificate607.reductionHom_zeta]
  rfl

omit [IsCyclotomicExtension {607} ℚ K] in
@[simp]
theorem realUnitNorm_basicVandiverUnit607 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 607)
    (j : VandiverFactorIndex607) :
    realUnitNorm (basicVandiverUnit607 hzeta j) =
      basicVandiverUnit607 hzeta j ^ 2 := by
  change basicVandiverUnit607 hzeta j *
    NumberField.IsCMField.unitsComplexConj K
      (basicVandiverUnit607 hzeta j) = _
  rw [(NumberField.IsCMField.unitsComplexConj_eq_self_iff K _).mpr
    (basicVandiverUnit607_mem_realUnits hzeta j)]
  exact (pow_two _).symm

theorem correctedResidueLog_basicVandiverUnit607 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 607) (row : Fin 302)
    (j : VandiverFactorIndex607) :
    certificate607.correctedResidueLog hzeta row
        (Additive.ofMul (basicVandiverUnit607 hzeta j)) =
      basicEdgeSymbol607 row j := by
  let u : (ZMod 20639)ˣ :=
    Units.map (certificate607.reductionHom hzeta row)
      (realUnitNorm (basicVandiverUnit607 hzeta j))
  have huval : (u : ZMod 20639) = basicResidueValue607 row j ^ 2 := by
    dsimp [u]
    rw [realUnitNorm_basicVandiverUnit607, Units.val_pow_eq_pow_val,
      map_pow, reductionHom_basicVandiverUnit607]
  have hpow :
      ((u : ZMod 20639) ^ certificate607.symbolExponent) =
      certificate607.root ^ ((basicEdgeSymbol607 row j).val * 2) := by
    change (u : ZMod 20639) ^ 34 =
      certificate607.root ^ ((basicEdgeSymbol607 row j).val * 2)
    calc
      (u : ZMod 20639) ^ 34 =
          (basicResidueValue607 row j ^ 2) ^ 34 := by rw [huval]
      _ = (basicResidueValue607 row j ^ 34) ^ 2 := by
        simp only [← pow_mul]
      _ = (certificate607.root ^
          (basicEdgeSymbol607 row j).val) ^ 2 := by
        rw [basicResidueValue607_symbol]
      _ = certificate607.root ^
          ((basicEdgeSymbol607 row j).val * 2) := by rw [pow_mul]
  change (2 : ZMod 607)⁻¹ *
      certificate607.residueLog (Additive.ofMul u) =
    basicEdgeSymbol607 row j
  rw [certificate607.residueLog_eq_of_pow_eq u _ hpow]
  rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  have hhalf : (2 : ZMod 607)⁻¹ * 2 = 1 :=
    inv_mul_cancel₀ (by
      intro h
      have hdiv : 607 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 607).mp h
      norm_num at hdiv)
  calc
    (2 : ZMod 607)⁻¹ * (basicEdgeSymbol607 row j * 2) =
        (2⁻¹ * 2) * basicEdgeSymbol607 row j := by ring
    _ = basicEdgeSymbol607 row j := by rw [hhalf, one_mul]

@[simp]
theorem quotientResidueLinear_basicVandiverUnit607 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 607) (row : Fin 302)
    (j : VandiverFactorIndex607) :
    certificate607.quotientResidueLinear hzeta row
        (classOfUnit (basicVandiverUnit607 hzeta j)) =
      basicEdgeSymbol607 row j := by
  change certificate607.quotientResidueLog hzeta row
    (classOfUnit (basicVandiverUnit607 hzeta j)) = _
  rw [certificate607.quotientResidueLog_classOfUnit]
  exact correctedResidueLog_basicVandiverUnit607 hzeta row j

omit [NumberField K] [IsCyclotomicExtension {607} ℚ K]
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

/-- Vandiver's positive weight reduced modulo `607`. -/
def weightMod607 (i : Fin 302) (j : VandiverFactorIndex607) : ZMod 607 :=
  (teichmullerRoot607 : ZMod 607) ^
    (607 ^ 2 - 2 * (i.val + 1) * j.val)

theorem diagonalWeight607_cast (i : Fin 302)
    (j : VandiverFactorIndex607) :
    (diagonalWeight607 i j : ZMod 607) =
      weightMod607 i j := by
  simp [diagonalWeight607, integralDiagonalWeight, weightMod607]

theorem quotientResidueLinear_diagonalVandiverUnit607_formula
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 607)
    (row i : Fin 302) :
    certificate607.quotientResidueLinear hzeta row
        (classOfUnit (diagonalVandiverUnit607 hzeta i)) =
      ∑ j : VandiverFactorIndex607,
        weightMod607 i j * basicEdgeSymbol607 row j := by
  rw [diagonalVandiverUnit607, classOfUnit_prod_pow]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_nsmul, quotientResidueLinear_basicVandiverUnit607]
  simp only [nsmul_eq_mul]
  rw [diagonalWeight607_cast]

/-! ## Algebraic Fourier factorization -/

theorem cycleClassSymbol607_zero (row : Fin 302) :
    cycleClassSymbol607 row 0 = 0 := by
  simp [cycleClassSymbol607]

theorem cycleClassSymbol607_succ (row j : Fin 302) :
    cycleClassSymbol607 row (j.val + 1) =
      Fermat.SixHundredSeven.CircularUnitMatrix.matrix row
        (cycleColumn607 j) := by
  rw [cycleClassSymbol607, dif_pos]
  · congr
  · omega

theorem cycleClassSymbol607_last (row : Fin 302) :
    cycleClassSymbol607 row 303 = 0 := by
  simp [cycleClassSymbol607]

theorem weighted_edge_sum607 (row : Fin 302)
    (w : Fin 303 → ZMod 607) :
    (∑ j : Fin 303, w j * basicEdgeSymbol607 row j) =
      ∑ ell : Fin 302,
        Fermat.SixHundredSeven.CircularUnitMatrix.matrix row
            (cycleColumn607 ell) *
          (w ell.castSucc - w ell.succ) := by
  simp_rw [basicEdgeSymbol607, mul_sub]
  rw [Finset.sum_sub_distrib]
  have hfirst :
      (∑ j : Fin 303, w j * cycleClassSymbol607 row (j.val + 1)) =
        ∑ ell : Fin 302,
          w ell.castSucc *
            Fermat.SixHundredSeven.CircularUnitMatrix.matrix row
              (cycleColumn607 ell) := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, cycleClassSymbol607_succ, Fin.val_last]
    rw [show 302 + 1 = 303 by norm_num, cycleClassSymbol607_last,
      mul_zero, add_zero]
  have hsecond :
      (∑ j : Fin 303, w j * cycleClassSymbol607 row j.val) =
        ∑ ell : Fin 302,
          w ell.succ *
            Fermat.SixHundredSeven.CircularUnitMatrix.matrix row
              (cycleColumn607 ell) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, cycleClassSymbol607_zero, mul_zero, zero_add,
      Fin.val_succ, cycleClassSymbol607_succ]
  rw [hfirst, hsecond, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ell _
  ring

theorem weightMod607_castSucc_sub_succ (ell i : Fin 302) :
    weightMod607 i ell.castSucc - weightMod607 i ell.succ =
      fourierChange607 ell i := by
  let r : ZMod 607 := teichmullerRoot607
  let n := i.val + 1
  let L := ell.val + 1
  have hn : n ≤ 302 := by simp [n]
  have hL : L ≤ 302 := by simp [L]
  have hn2 : 2 * n ≤ 606 := by omega
  have hpositive : 2 * n * L ≤ 607 ^ 2 := by
    calc
      2 * n * L ≤ 2 * 302 * 302 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn) hL
      _ ≤ 607 ^ 2 := by norm_num
  have hsplit :
      (606 - 2 * n) * L = 606 * L - 2 * n * L :=
    Nat.sub_mul 606 (2 * n) L
  have hdecomp :
      607 ^ 2 - 2 * n * L =
        1 + (606 - 2 * n) * L + 606 * (608 - L) := by
    rw [hsplit]
    have hwithin : 2 * n * L ≤ 606 * L :=
      Nat.mul_le_mul_right L hn2
    omega
  have hr606 : r ^ 606 = 1 :=
    teichmullerRoot607_isPrimitive.pow_eq_one
  have hsecond :
      r ^ (607 ^ 2 - 2 * n * L) =
        r * (r ^ (606 - 2 * n)) ^ L := by
    rw [hdecomp, pow_add, pow_add]
    rw [show r ^ 1 = r by simp,
      show r ^ ((606 - 2 * n) * L) =
          (r ^ (606 - 2 * n)) ^ L by rw [pow_mul],
      show r ^ (606 * (608 - L)) = 1 by
        rw [pow_mul, hr606, one_pow]]
    simp
  have hstep :
      2 * n * L = 2 * n * ell.val + 2 * n := by
    simp only [L]
    ring
  have hfirstExp :
      607 ^ 2 - 2 * n * ell.val =
        (607 ^ 2 - 2 * n * L) + 2 * n := by
    have hfirstBound : 2 * n * ell.val ≤ 607 ^ 2 := by
      calc
        2 * n * ell.val ≤ 2 * n * L :=
          Nat.mul_le_mul_left (2 * n) (by simp [L])
        _ ≤ 607 ^ 2 := hpositive
    omega
  rw [weightMod607]
  change r ^ (607 ^ 2 - 2 * n * ell.val) -
      r ^ (607 ^ 2 - 2 * n * L) = fourierChange607 ell i
  rw [hfirstExp, pow_add, hsecond, fourierChange607_apply]
  simp only [vandermondeNode607, fourierScale607, n, L, r]
  rw [show 604 - 2 * i.val = 606 - 2 * (i.val + 1) by omega]
  rw [show ell.val + 1 = L by rfl]
  ring

noncomputable def cycleCircularMatrix607 :
    Matrix (Fin 302) (Fin 302) (ZMod 607) :=
  Fermat.SixHundredSeven.CircularUnitMatrix.matrix.submatrix id
    cycleColumnEquiv607

theorem cycleCircularMatrix607_det_ne_zero :
    cycleCircularMatrix607.det ≠ 0 := by
  rw [cycleCircularMatrix607, Matrix.det_permute']
  exact mul_ne_zero
    (by
      exact ((Equiv.Perm.sign cycleColumnEquiv607).isUnit.map
        (Int.castRingHom (ZMod 607))).ne_zero)
    Fermat.SixHundredSeven.CircularUnitCertificate.matrix_det_ne_zero

/-- The actual diagonal residue matrix, factored into its circular and
Fourier components. -/
noncomputable def diagonalResidueMatrix607 :
    Matrix (Fin 302) (Fin 302) (ZMod 607) :=
  cycleCircularMatrix607 * fourierChange607

theorem diagonalResidueMatrix607_det_ne_zero :
    diagonalResidueMatrix607.det ≠ 0 := by
  rw [diagonalResidueMatrix607, Matrix.det_mul]
  exact mul_ne_zero cycleCircularMatrix607_det_ne_zero
    fourierChange607_det_ne_zero

theorem weighted_edge_sum607_eq_matrix (row i : Fin 302) :
    (∑ j : Fin 303, weightMod607 i j * basicEdgeSymbol607 row j) =
      diagonalResidueMatrix607 row i := by
  rw [weighted_edge_sum607]
  simp_rw [weightMod607_castSucc_sub_succ]
  rfl

@[simp]
theorem quotientResidueLinear_diagonalVandiverUnit607 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 607) (row i : Fin 302) :
    certificate607.quotientResidueLinear hzeta row
        (classOfUnit (diagonalVandiverUnit607 hzeta i)) =
      diagonalResidueMatrix607 row i := by
  rw [quotientResidueLinear_diagonalVandiverUnit607_formula]
  exact weighted_edge_sum607_eq_matrix row i

theorem evalMatrix_diagonalVandiverUnit607 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 607) :
    evalMatrix (classOfUnit ∘ diagonalVandiverUnit607 hzeta)
        (certificate607.residueFunctionals hzeta) =
      diagonalResidueMatrix607 := by
  ext row i
  exact quotientResidueLinear_diagonalVandiverUnit607 hzeta row i

theorem not_dvd_diagonalVandiverUnit607_full_index {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 607) :
    ¬607 ∣
      (Subgroup.closure (Set.range (diagonalVandiverUnit607 hzeta)) ⊔
        NumberField.Units.torsion K).index := by
  apply not_dvd_unitIndex_of_eval_det_ne_zero
    (certificate607.basisModTorsion (K := K))
      (diagonalVandiverUnit607 hzeta)
      (certificate607.residueFunctionals hzeta)
  rw [evalMatrix_diagonalVandiverUnit607]
  exact diagonalResidueMatrix607_det_ne_zero

theorem ambient_closure_finiteIndex {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 607) :
    (Subgroup.closure
      (Set.range (diagonalVandiverUnit607 hzeta))).FiniteIndex := by
  have hnot := not_dvd_diagonalVandiverUnit607_full_index hzeta
  have hsup :
      (Subgroup.closure (Set.range (diagonalVandiverUnit607 hzeta)) ⊔
        NumberField.Units.torsion K).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff]
    intro hzero
    apply hnot
    rw [hzero]
    exact dvd_zero 607
  exact (NumberField.Units.finiteIndex_iff_sup_torsion_finiteIndex
    (Subgroup.closure (Set.range
      (diagonalVandiverUnit607 hzeta)))).2 hsup

theorem real_closure_finiteIndex {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 607) :
    (Subgroup.closure
      (Set.range (diagonalVandiverUnitFamily607 hzeta))).FiniteIndex := by
  letI :
      (Subgroup.closure (Set.range fun i : Fin 302 ↦
        ((diagonalVandiverUnitFamily607 hzeta i :
          NumberField.IsCMField.realUnits K) :
            (RingOfIntegers K)ˣ))).FiniteIndex := by
    simpa [diagonalVandiverUnitFamily607] using
      ambient_closure_finiteIndex hzeta
  exact Fermat.Irregular.VandiverFiniteIndex.closure_range_subtype
    (NumberField.IsCMField.realUnits K)
      (diagonalVandiverUnitFamily607 hzeta)

end

end Fermat.SixHundredSeven.VandiverDiagonalUnits
