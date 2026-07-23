import Fermat.Irregular.VandiverDiagonalLogDerivative
import Fermat.Irregular.VandiverFiniteIndex
import Fermat.ThirtySeven.ResidueHomomorphisms
import Fermat.ThirtySeven.VandiverDiagonalArithmetic

/-!
# Vandiver's diagonal real-unit family at exponent 37

This module realizes in the cyclotomic unit group the integral diagonal
family used in Vandiver's Lemma 2.  Put

`epsilon(w) = w^18 * (w^76 - 1) / (w - 1)`.

For `i = 1, ..., 17`, Vandiver first assigns the formal weights
`76^(-2*i*j)` to the conjugates `epsilon(zeta^(76^j))`.  Raising to
`rho = 76^(37^2)` replaces them by the positive integral weights
`76^(37^2 - 2*i*j)`.  The resulting units are the family defined here.

The first display on p. 617 prints the lower product limit as `j = 1`.
That is a one-character typo: the immediately following positive-exponent
display starts at `j = 0`, and formula (4) starts its character sum with
the `j = 0` term `1`.  Accordingly `VandiverFactorIndex37` is `Fin 18`,
machine-checking the source-faithful range `j = 0, ..., 17`.

Besides reality, this file proves that the seventeen diagonal units have
finite-index closure.  The proof evaluates them under the already
constructed power-residue functionals at the auxiliary prime `149` and
kernel-checks the resulting finite determinant.
-/

open scoped NumberField

namespace Fermat.ThirtySeven.VandiverDiagonalUnits

noncomputable section

open Fermat.Irregular
open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitIndex
open Fermat.Irregular.CircularUnits
open Fermat.Irregular.VandiverDiagonalLogDerivative
open Fermat.ThirtySeven.VandiverDiagonalArithmetic
open Fermat.ThirtySeven.ResidueHomomorphisms
open NumberField NumberField.Units

local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance : Fact (Nat.Prime 149) := ⟨by decide⟩

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The corrected source range `j = 0, ..., 17`.  In particular, the
constant term omitted by the p. 617 typo is an actual member of the type. -/
abbrev VandiverFactorIndex37 := Fin 18

theorem card_vandiverFactorIndex37 :
    Fintype.card VandiverFactorIndex37 = 18 := by decide

/-- The power of the chosen root occurring in the `j`th conjugate. -/
def conjugateExponent37 (j : VandiverFactorIndex37) : ℕ :=
  teichmullerRoot37 ^ j.val

/-- The least residue of the same source exponent modulo `37`.  This is
used only to keep finite-field normalization small; the actual unit above
continues to use the literal exponent `76^j`. -/
def reducedConjugateExponent37 (j : VandiverFactorIndex37) : ℕ :=
  ((teichmullerRoot37 : ZMod 37) ^ j.val).val

theorem conjugateExponent37_modEq_reduced (j : VandiverFactorIndex37) :
    conjugateExponent37 j ≡ reducedConjugateExponent37 j [MOD 37] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  simp [conjugateExponent37, reducedConjugateExponent37]

theorem pow_conjugateExponent37_eq_reduced {G : Type*} [Monoid G]
    (x : G) (hx : x ^ 37 = 1) (j : VandiverFactorIndex37) :
    x ^ conjugateExponent37 j = x ^ reducedConjugateExponent37 j :=
  pow_eq_pow_of_modEq (conjugateExponent37_modEq_reduced j) hx

/-- Vandiver's integral positive weight for unit index `i + 1` and
conjugate index `j`.  This is definitionally the weight used by the formal
power-series diagonalization. -/
def diagonalWeight37 (i : Fin 17) (j : VandiverFactorIndex37) : ℕ :=
  integralDiagonalWeight 37 teichmullerRoot37 (i.val + 1) j.val

theorem diagonalWeight37_eq (i : Fin 17) (j : VandiverFactorIndex37) :
    diagonalWeight37 i j =
      76 ^ (37 ^ 2 - 2 * (i.val + 1) * j.val) := by
  rfl

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K]

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] in
/-- Each `zeta^(76^j)` is again a primitive 37th root. -/
theorem conjugate_isPrimitive {zeta : K} (hzeta : IsPrimitiveRoot zeta 37)
    (j : VandiverFactorIndex37) :
    IsPrimitiveRoot (zeta ^ conjugateExponent37 j) 37 := by
  apply hzeta.pow_of_coprime
  exact (by norm_num : Nat.Coprime 76 37).pow_left j.val

/-- The basic real unit `epsilon(zeta^(76^j))`.  Its geometric length is
literally `76`, rather than being reduced modulo `37`, so its definition
matches Vandiver's integral polynomial. -/
def basicVandiverUnit37 {zeta : K} (hzeta : IsPrimitiveRoot zeta 37)
    (j : VandiverFactorIndex37) : (RingOfIntegers K)ˣ :=
  normalizedCircularUnit (p := 37) (a := 76)
    (conjugate_isPrimitive hzeta j) (by norm_num) (by norm_num) 18

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] in
/-- The integral lift of a conjugate root is the corresponding power of
the chosen integral lift. -/
theorem conjugate_toInteger {zeta : K} (hzeta : IsPrimitiveRoot zeta 37)
    (j : VandiverFactorIndex37) :
    (conjugate_isPrimitive hzeta j).toInteger =
      hzeta.toInteger ^ conjugateExponent37 j := by
  apply RingOfIntegers.ext
  rfl

omit [IsCyclotomicExtension {37} ℚ K] in
/-- The normalization `2*18 + 76 = 1 (mod 37)` makes every basic factor
real. -/
theorem basicVandiverUnit37_mem_realUnits {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) (j : VandiverFactorIndex37) :
    basicVandiverUnit37 hzeta j ∈ NumberField.IsCMField.realUnits K := by
  apply normalizedCircularUnit_mem_realUnits (p := 37) (a := 76) (e := 18)
  decide

/-- The ambient integral diagonal unit `(E_(i+1)(zeta))^rho`. -/
def diagonalVandiverUnit37 {zeta : K} (hzeta : IsPrimitiveRoot zeta 37)
    (i : Fin 17) : (RingOfIntegers K)ˣ :=
  ∏ j : VandiverFactorIndex37,
    basicVandiverUnit37 hzeta j ^ diagonalWeight37 i j

omit [IsCyclotomicExtension {37} ℚ K] in
theorem diagonalVandiverUnit37_mem_realUnits {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) (i : Fin 17) :
    diagonalVandiverUnit37 hzeta i ∈ NumberField.IsCMField.realUnits K := by
  apply Subgroup.prod_mem
  intro j hj
  exact Subgroup.pow_mem _ (basicVandiverUnit37_mem_realUnits hzeta j) _

/-- Vandiver's seventeen integral diagonal units, typed in the real-unit
subgroup consumed by Lemma II. -/
def diagonalVandiverUnitFamily37 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) :
    Fin 17 → NumberField.IsCMField.realUnits K :=
  fun i ↦ ⟨diagonalVandiverUnit37 hzeta i,
    diagonalVandiverUnit37_mem_realUnits hzeta i⟩

omit [IsCyclotomicExtension {37} ℚ K] in
@[simp]
theorem diagonalVandiverUnitFamily37_coe {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) (i : Fin 17) :
    ((diagonalVandiverUnitFamily37 hzeta i :
      NumberField.IsCMField.realUnits K) : (RingOfIntegers K)ˣ) =
      diagonalVandiverUnit37 hzeta i := rfl

/-! ## The auxiliary-prime evaluation matrix -/

/-- The geometric sum in the reduction of a basic Vandiver factor. -/
def basicResidueGeomSum37 (row : Fin 17) (j : VandiverFactorIndex37) :
    ZMod 149 :=
  let w := Fermat.ThirtySeven.CircularUnitResidues.embeddingRoot row ^
    conjugateExponent37 j
  ∑ k ∈ Finset.range 76, w ^ k

/-- The value of the `j`th basic factor after sending `zeta` to the
`row`th primitive root modulo `149`. -/
def basicResidueValue37 (row : Fin 17) (j : VandiverFactorIndex37) :
    ZMod 149 :=
  let w := Fermat.ThirtySeven.CircularUnitResidues.embeddingRoot row ^
    conjugateExponent37 j
  w ^ 18 * basicResidueGeomSum37 row j

/-- Since the evaluated root has order `37`, the geometric sum of length
`76 = 2*37+2` reduces exactly to `1+w`.  Keeping this as an algebraic lemma
also makes the later finite certificate small. -/
theorem basicResidueGeomSum37_eq (row : Fin 17)
    (j : VandiverFactorIndex37) :
    basicResidueGeomSum37 row j =
      1 + Fermat.ThirtySeven.CircularUnitResidues.embeddingRoot row ^
        conjugateExponent37 j := by
  let w : ZMod 149 :=
    Fermat.ThirtySeven.CircularUnitResidues.embeddingRoot row ^
      conjugateExponent37 j
  have hwroot : IsPrimitiveRoot w 37 := by
    apply (Fermat.ThirtySeven.ResidueHomomorphisms.embeddingRoot_isPrimitive
      row).pow_of_coprime
    exact (by norm_num : Nat.Coprime 76 37).pow_left j.val
  have hwne : w - 1 ≠ 0 :=
    sub_ne_zero.mpr (hwroot.ne_one (by norm_num))
  apply mul_left_cancel₀ (a := w - 1) hwne
  rw [show (w - 1) * basicResidueGeomSum37 row j = w ^ 76 - 1 by
    simpa [basicResidueGeomSum37, w] using (mul_geom_sum w 76)]
  change w ^ 76 - 1 = (w - 1) * (1 + w)
  rw [show 76 = 37 * 2 + 2 by norm_num, pow_add, pow_mul,
    hwroot.pow_eq_one]
  ring

/-- Fourth-power discrete logs of `epsilon(w)` for the eighteen real
classes `w = 16^s`, `s = 1, ..., 18`.  The first seventeen entries are
the first column of the existing circular-unit certificate; the last
entry is its missing real conjugacy class. -/
def basicSymbolByRealExponent37 : Fin 18 → Fin 37 := ![
  11, 0, 30, 13, 33, 2, 21, 31, 26,
  35, 36, 27, 16, 9, 24, 27, 17, 12
]

/-- Reduce `(row+1) * 76^j` modulo `37`, identify a residue with its
negative, and turn the resulting real class `1, ..., 18` into a
zero-based table index. -/
def conjugateRealIndex37 (row : Fin 17) (j : VandiverFactorIndex37) :
    Fin 18 :=
  let s := ((row.val + 1) * reducedConjugateExponent37 j) % 37
  let a := min s (37 - s)
  ⟨(a - 1) % 18, Nat.mod_lt _ (by norm_num)⟩

/-- The certified fourth-power residue exponent of a basic factor. -/
def basicSymbolExponent37 (row : Fin 17) (j : VandiverFactorIndex37) :
    Fin 37 :=
  basicSymbolByRealExponent37 (conjugateRealIndex37 row j)

/-- Direct finite-field check of all `17 * 18` basic-factor symbols. -/
theorem basicResidueValue37_fourthPower (row : Fin 17)
    (j : VandiverFactorIndex37) :
    basicResidueValue37 row j ^ 4 =
      (16 : ZMod 149) ^ (basicSymbolExponent37 row j).val := by
  rw [basicResidueValue37, basicResidueGeomSum37_eq]
  rw [pow_conjugateExponent37_eq_reduced _
    (Fermat.ThirtySeven.ResidueHomomorphisms.embeddingRoot_isPrimitive
      row).pow_eq_one]
  fin_cases row <;> fin_cases j <;> decide

omit [NumberField.IsCMField K] in
/-- Reduction of the actual cyclotomic unit is exactly the finite
geometric value above. -/
theorem reductionHom_basicVandiverUnit37 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) (row : Fin 17)
    (j : VandiverFactorIndex37) :
    reductionHom hzeta row (basicVandiverUnit37 hzeta j : RingOfIntegers K) =
      basicResidueValue37 row j := by
  unfold basicVandiverUnit37
  rw [normalizedCircularUnit_val]
  rw [conjugate_toInteger (hzeta := hzeta) j]
  simp only [map_mul, map_pow, map_sum, reductionHom_zeta]
  rfl

omit [IsCyclotomicExtension {37} ℚ K] in
/-- The CM norm squares a basic Vandiver factor because the factor is
real. -/
@[simp]
theorem realUnitNorm_basicVandiverUnit37 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) (j : VandiverFactorIndex37) :
    realUnitNorm (basicVandiverUnit37 hzeta j) =
      basicVandiverUnit37 hzeta j ^ 2 := by
  change basicVandiverUnit37 hzeta j *
    NumberField.IsCMField.unitsComplexConj K
      (basicVandiverUnit37 hzeta j) = _
  rw [(NumberField.IsCMField.unitsComplexConj_eq_self_iff K _).mpr
    (basicVandiverUnit37_mem_realUnits hzeta j)]
  exact (pow_two _).symm

/-- The corrected residue logarithm of each actual basic factor is the
finite exponent certified above. -/
theorem correctedResidueLog_basicVandiverUnit37 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) (row : Fin 17)
    (j : VandiverFactorIndex37) :
    correctedResidueLog (hζ := hzeta) row
        (Additive.ofMul (basicVandiverUnit37 hzeta j)) =
      ((basicSymbolExponent37 row j).val : ZMod 37) := by
  let u : (ZMod 149)ˣ :=
    Units.map (reductionHom hzeta row)
      (realUnitNorm (basicVandiverUnit37 hzeta j))
  have huval : (u : ZMod 149) = basicResidueValue37 row j ^ 2 := by
    dsimp [u]
    rw [realUnitNorm_basicVandiverUnit37, Units.val_pow_eq_pow_val,
      map_pow, reductionHom_basicVandiverUnit37]
  have hpow : ((u : ZMod 149) ^ 4) =
      (16 : ZMod 149) ^ ((basicSymbolExponent37 row j).val * 2) := by
    calc
      (u : ZMod 149) ^ 4 = (basicResidueValue37 row j ^ 2) ^ 4 := by
        rw [huval]
      _ = (basicResidueValue37 row j ^ 4) ^ 2 := by ring
      _ = ((16 : ZMod 149) ^
          (basicSymbolExponent37 row j).val) ^ 2 := by
        rw [basicResidueValue37_fourthPower]
      _ = (16 : ZMod 149) ^
          ((basicSymbolExponent37 row j).val * 2) := by rw [pow_mul]
  change 19 * residueLog (Additive.ofMul u) =
    ((basicSymbolExponent37 row j).val : ZMod 37)
  rw [residueLog_eq_of_pow_eq u _ hpow]
  rw [Nat.cast_mul]
  have hhalf : (19 : ZMod 37) * 2 = 1 := by decide
  calc
    19 * ((basicSymbolExponent37 row j).val * 2 : ZMod 37) =
        (19 * 2) * (basicSymbolExponent37 row j).val := by ring
    _ = ((basicSymbolExponent37 row j).val : ZMod 37) := by
      rw [hhalf, one_mul]

@[simp]
theorem quotientResidueLinear_basicVandiverUnit37 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) (row : Fin 17)
    (j : VandiverFactorIndex37) :
    quotientResidueLinear hzeta row
        (classOfUnit (basicVandiverUnit37 hzeta j)) =
      ((basicSymbolExponent37 row j).val : ZMod 37) := by
  change quotientResidueLog hzeta row
    (classOfUnit (basicVandiverUnit37 hzeta j)) = _
  rw [quotientResidueLog_classOfUnit]
  exact correctedResidueLog_basicVandiverUnit37 hzeta row j

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K]
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

/-- Casting the source's enormous positive integral weight modulo `37`
can be performed before exponentiation. -/
theorem diagonalWeight37_cast (i : Fin 17) (j : VandiverFactorIndex37) :
    (diagonalWeight37 i j : ZMod 37) =
      (teichmullerRoot37 : ZMod 37) ^
        (37 ^ 2 - 2 * (i.val + 1) * j.val) := by
  simp [diagonalWeight37, integralDiagonalWeight]

/-- Evaluation of a diagonal unit is the weighted sum of its eighteen
basic-factor symbols. -/
theorem quotientResidueLinear_diagonalVandiverUnit37_formula {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) (row i : Fin 17) :
    quotientResidueLinear hzeta row
        (classOfUnit (diagonalVandiverUnit37 hzeta i)) =
      ∑ j : VandiverFactorIndex37,
        (teichmullerRoot37 : ZMod 37) ^
            (37 ^ 2 - 2 * (i.val + 1) * j.val) *
          ((basicSymbolExponent37 row j).val : ZMod 37) := by
  rw [diagonalVandiverUnit37, classOfUnit_prod_pow]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_nsmul, quotientResidueLinear_basicVandiverUnit37]
  simp only [nsmul_eq_mul]
  rw [diagonalWeight37_cast]

/-- The kernel-checked evaluation matrix of Vandiver's seventeen diagonal
units under the seventeen auxiliary-prime residue functionals. -/
def diagonalResidueMatrix37 : Matrix (Fin 17) (Fin 17) (ZMod 37) := ![
  ![13, 14, 22, 20, 14, 29, 4, 17, 16, 7, 23, 12, 9, 16, 17, 8, 7],
  ![15, 2, 2, 14, 17, 14, 9, 5, 21, 9, 2, 9, 27, 7, 2, 19, 11],
  ![6, 24, 17, 18, 32, 31, 27, 6, 16, 26, 13, 16, 34, 26, 22, 17, 9],
  ![23, 32, 17, 32, 18, 31, 11, 8, 16, 1, 5, 16, 7, 10, 22, 22, 12],
  ![29, 18, 20, 24, 13, 31, 1, 23, 21, 10, 18, 16, 4, 1, 15, 35, 21],
  ![24, 14, 15, 20, 23, 29, 33, 17, 21, 7, 14, 12, 28, 16, 20, 8, 30],
  ![8, 18, 17, 24, 24, 31, 36, 23, 16, 10, 19, 16, 33, 1, 22, 35, 16],
  ![18, 31, 15, 15, 6, 29, 34, 35, 21, 33, 31, 12, 21, 9, 20, 6, 3],
  ![17, 20, 35, 31, 15, 14, 25, 13, 16, 12, 17, 9, 1, 33, 35, 13, 1],
  ![5, 29, 22, 2, 29, 29, 30, 22, 16, 34, 8, 12, 12, 12, 17, 23, 33],
  ![19, 31, 22, 15, 31, 29, 3, 35, 16, 33, 6, 12, 16, 9, 17, 6, 34],
  ![22, 2, 35, 14, 20, 14, 28, 5, 16, 9, 35, 9, 10, 7, 35, 19, 26],
  ![14, 32, 20, 32, 19, 31, 26, 8, 21, 1, 32, 16, 30, 10, 15, 22, 25],
  ![32, 29, 15, 2, 8, 29, 7, 22, 21, 34, 29, 12, 25, 12, 20, 23, 4],
  ![2, 15, 2, 29, 35, 14, 16, 19, 21, 16, 15, 9, 11, 34, 2, 5, 27],
  ![35, 15, 35, 29, 2, 14, 21, 19, 16, 16, 22, 9, 26, 34, 35, 5, 10],
  ![20, 20, 2, 31, 22, 14, 12, 13, 21, 12, 20, 9, 36, 33, 2, 13, 36]
]

/-- An explicit inverse of `diagonalResidueMatrix37`. -/
def diagonalResidueMatrixInverse37 :
    Matrix (Fin 17) (Fin 17) (ZMod 37) := ![
  ![9, 2, 24, 28, 3, 15, 21, 16, 1, 19, 8, 22, 33, 5, 11, 13, 23],
  ![18, 33, 0, 27, 1, 18, 1, 22, 8, 25, 22, 33, 27, 25, 24, 24, 8],
  ![36, 25, 15, 15, 0, 16, 15, 16, 27, 36, 36, 27, 0, 16, 25, 27, 25],
  ![7, 17, 0, 26, 36, 7, 36, 23, 21, 32, 23, 17, 26, 32, 24, 24, 21],
  ![14, 19, 23, 34, 27, 9, 33, 5, 20, 21, 18, 4, 26, 2, 31, 29, 3],
  ![3, 33, 0, 0, 0, 3, 0, 3, 33, 3, 3, 33, 0, 3, 33, 33, 33],
  ![33, 23, 30, 35, 13, 34, 17, 28, 9, 10, 2, 7, 32, 20, 1, 29, 21],
  ![14, 32, 0, 34, 4, 14, 4, 26, 22, 35, 26, 32, 34, 35, 21, 21, 22],
  ![9, 0, 9, 9, 0, 0, 9, 0, 9, 9, 9, 9, 0, 0, 0, 9, 0],
  ![25, 28, 0, 18, 5, 25, 5, 2, 26, 33, 2, 28, 18, 33, 6, 6, 26],
  ![13, 33, 31, 4, 1, 18, 30, 22, 23, 6, 9, 35, 27, 25, 24, 7, 8],
  ![20, 22, 0, 0, 0, 20, 0, 20, 22, 20, 20, 22, 0, 20, 22, 22, 22],
  ![21, 28, 26, 18, 31, 5, 32, 27, 11, 19, 36, 35, 8, 7, 33, 30, 15],
  ![6, 25, 0, 5, 18, 6, 18, 28, 2, 26, 28, 25, 5, 26, 33, 33, 2],
  ![36, 9, 20, 20, 0, 21, 20, 21, 11, 36, 36, 11, 0, 21, 9, 11, 9],
  ![20, 7, 0, 21, 12, 20, 12, 23, 8, 27, 23, 7, 21, 27, 18, 18, 8],
  ![13, 28, 16, 14, 22, 3, 31, 32, 6, 27, 21, 25, 2, 26, 23, 30, 10]
]

theorem diagonalResidueFormula_eq_matrix (row i : Fin 17) :
    (∑ j : VandiverFactorIndex37,
        (teichmullerRoot37 : ZMod 37) ^
            (37 ^ 2 - 2 * (i.val + 1) * j.val) *
          ((basicSymbolExponent37 row j).val : ZMod 37)) =
      diagonalResidueMatrix37 row i := by
  fin_cases row <;> fin_cases i <;> decide

theorem diagonalResidueMatrix_mul_inverse :
    diagonalResidueMatrix37 * diagonalResidueMatrixInverse37 = 1 := by
  decide

theorem diagonalResidueMatrix_det_ne_zero :
    diagonalResidueMatrix37.det ≠ 0 := by
  intro hzero
  have hdet := congrArg Matrix.det diagonalResidueMatrix_mul_inverse
  rw [Matrix.det_mul, hzero, zero_mul, Matrix.det_one] at hdet
  exact (by decide : (0 : ZMod 37) ≠ 1) hdet

@[simp]
theorem quotientResidueLinear_diagonalVandiverUnit37 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) (row i : Fin 17) :
    quotientResidueLinear hzeta row
        (classOfUnit (diagonalVandiverUnit37 hzeta i)) =
      diagonalResidueMatrix37 row i := by
  rw [quotientResidueLinear_diagonalVandiverUnit37_formula]
  exact diagonalResidueFormula_eq_matrix row i

/-- The residue functionals realize the complete diagonal-unit matrix. -/
theorem evalMatrix_diagonalVandiverUnit37 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) :
    evalMatrix (classOfUnit ∘ diagonalVandiverUnit37 hzeta)
        (residueFunctionals hzeta) = diagonalResidueMatrix37 := by
  ext row i
  exact quotientResidueLinear_diagonalVandiverUnit37 hzeta row i

/-- The actual diagonal units have full ambient unit index prime to `37`. -/
theorem not_dvd_diagonalVandiverUnit37_full_index {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) :
    ¬37 ∣ (Subgroup.closure (Set.range (diagonalVandiverUnit37 hzeta)) ⊔
      NumberField.Units.torsion K).index := by
  apply not_dvd_unitIndex_of_eval_det_ne_zero
    (basisModTorsion37 (K := K)) (diagonalVandiverUnit37 hzeta)
      (residueFunctionals hzeta)
  rw [evalMatrix_diagonalVandiverUnit37]
  exact diagonalResidueMatrix_det_ne_zero

/-- The closure of Vandiver's diagonal family has finite index in the
ambient unit group. -/
theorem ambient_closure_finiteIndex {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) :
    (Subgroup.closure
      (Set.range (diagonalVandiverUnit37 hzeta))).FiniteIndex := by
  have hnot := not_dvd_diagonalVandiverUnit37_full_index hzeta
  have hsup :
      (Subgroup.closure (Set.range (diagonalVandiverUnit37 hzeta)) ⊔
        NumberField.Units.torsion K).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff]
    intro hzero
    apply hnot
    rw [hzero]
    exact dvd_zero 37
  exact (NumberField.Units.finiteIndex_iff_sup_torsion_finiteIndex
    (Subgroup.closure (Set.range (diagonalVandiverUnit37 hzeta)))).2 hsup

/-- The same family has finite-index closure in the real-unit subgroup,
the exact group used by Vandiver's Lemma II bridge. -/
theorem real_closure_finiteIndex {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) :
    (Subgroup.closure
      (Set.range (diagonalVandiverUnitFamily37 hzeta))).FiniteIndex := by
  letI :
      (Subgroup.closure (Set.range fun i : Fin 17 ↦
        ((diagonalVandiverUnitFamily37 hzeta i :
          NumberField.IsCMField.realUnits K) : (RingOfIntegers K)ˣ))).FiniteIndex := by
    simpa [diagonalVandiverUnitFamily37] using
      ambient_closure_finiteIndex hzeta
  exact Fermat.Irregular.VandiverFiniteIndex.closure_range_subtype
    (NumberField.IsCMField.realUnits K)
      (diagonalVandiverUnitFamily37 hzeta)

end

end Fermat.ThirtySeven.VandiverDiagonalUnits
