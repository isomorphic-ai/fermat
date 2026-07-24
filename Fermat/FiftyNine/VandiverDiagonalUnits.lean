import Fermat.Irregular.VandiverDiagonalLogDerivative
import Fermat.Irregular.VandiverFiniteIndex
import Fermat.FiftyNine.CircularUnitResidues
import Fermat.FiftyNine.VandiverDiagonalArithmetic

/-!
# Vandiver's diagonal real-unit family at exponent 59

This module realizes in the cyclotomic unit group the integral diagonal
family used in Vandiver's Lemma 2.  Put

`epsilon(w) = w^29 * (w^946 - 1) / (w - 1)`.

For `i = 1, ..., 28`, Vandiver first assigns the formal weights
`946^(-2*i*j)` to the conjugates `epsilon(zeta^(946^j))`.  Raising to
`rho = 946^(59^2)` replaces them by the positive integral weights
`946^(59^2 - 2*i*j)`.  The resulting units are the family defined here.

The first display on p. 617 prints the lower product limit as `j = 1`.
That is a one-character typo: the immediately following positive-exponent
display starts at `j = 0`, and formula (4) starts its character sum with
the `j = 0` term `1`. Accordingly `VandiverFactorIndex59` is `Fin 29`,
machine-checking the source-faithful range `j = 0, ..., 28`.

Besides reality, this file proves that the twenty-eight diagonal units have
finite-index closure.  The proof evaluates them under the already
constructed power-residue functionals at the auxiliary prime `827` and
kernel-checks the resulting finite determinant.
-/

open scoped NumberField

namespace Fermat.FiftyNine.VandiverDiagonalUnits

noncomputable section

open Fermat.Irregular
open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitIndex
open Fermat.Irregular.CircularUnitResidues
open Fermat.Irregular.CircularUnitResidues.Certificate
open Fermat.Irregular.CircularUnits
open Fermat.Irregular.VandiverDiagonalLogDerivative
open Fermat.FiftyNine.VandiverDiagonalArithmetic
open NumberField NumberField.Units

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 59) := ⟨Fermat.FiftyNine.prime_59⟩
local instance : Fact (Nat.Prime 827) := ⟨Fermat.FiftyNine.prime_827⟩

abbrev certificate59 : Certificate 59 827 :=
  Fermat.FiftyNine.CircularUnitResidues.residueCertificate

/-- The corrected source range `j = 0, ..., 28`.  In particular, the
constant term omitted by the p. 617 typo is an actual member of the type. -/
abbrev VandiverFactorIndex59 := Fin 29

theorem card_vandiverFactorIndex59 :
    Fintype.card VandiverFactorIndex59 = 29 := by decide

/-- The power of the chosen root occurring in the `j`th conjugate. -/
def conjugateExponent59 (j : VandiverFactorIndex59) : ℕ :=
  teichmullerRoot59 ^ j.val

/-- The least residue of the same source exponent modulo `59`.  This is
used only to keep finite-field normalization small; the actual unit above
continues to use the literal exponent `946^j`. -/
def reducedConjugateExponent59 (j : VandiverFactorIndex59) : ℕ :=
  ((teichmullerRoot59 : ZMod 59) ^ j.val).val

theorem conjugateExponent59_modEq_reduced (j : VandiverFactorIndex59) :
    conjugateExponent59 j ≡ reducedConjugateExponent59 j [MOD 59] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  simp [conjugateExponent59, reducedConjugateExponent59]

theorem pow_conjugateExponent59_eq_reduced {G : Type*} [Monoid G]
    (x : G) (hx : x ^ 59 = 1) (j : VandiverFactorIndex59) :
    x ^ conjugateExponent59 j = x ^ reducedConjugateExponent59 j :=
  pow_eq_pow_of_modEq (conjugateExponent59_modEq_reduced j) hx

/-- Vandiver's integral positive weight for unit index `i + 1` and
conjugate index `j`.  This is definitionally the weight used by the formal
power-series diagonalization. -/
def diagonalWeight59 (i : Fin 28) (j : VandiverFactorIndex59) : ℕ :=
  integralDiagonalWeight 59 teichmullerRoot59 (i.val + 1) j.val

theorem diagonalWeight59_eq (i : Fin 28) (j : VandiverFactorIndex59) :
    diagonalWeight59 i j =
      946 ^ (59 ^ 2 - 2 * (i.val + 1) * j.val) := by
  rfl

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K] [NumberField.IsCMField K]

omit [NumberField K] [IsCyclotomicExtension {59} ℚ K]
    [NumberField.IsCMField K] in
/-- Each `zeta^(946^j)` is again a primitive 59th root. -/
theorem conjugate_isPrimitive {zeta : K} (hzeta : IsPrimitiveRoot zeta 59)
    (j : VandiverFactorIndex59) :
    IsPrimitiveRoot (zeta ^ conjugateExponent59 j) 59 := by
  apply hzeta.pow_of_coprime
  exact (by norm_num : Nat.Coprime 946 59).pow_left j.val

/-- The basic real unit `epsilon(zeta^(946^j))`.  Its geometric length is
literally `946`, rather than being reduced modulo `59`, so its definition
matches Vandiver's integral polynomial. -/
def basicVandiverUnit59 {zeta : K} (hzeta : IsPrimitiveRoot zeta 59)
    (j : VandiverFactorIndex59) : (RingOfIntegers K)ˣ :=
  normalizedCircularUnit (p := 59) (a := 946)
    (conjugate_isPrimitive hzeta j) (by norm_num) (by norm_num) 29

omit [NumberField K] [IsCyclotomicExtension {59} ℚ K]
    [NumberField.IsCMField K] in
/-- The integral lift of a conjugate root is the corresponding power of
the chosen integral lift. -/
theorem conjugate_toInteger {zeta : K} (hzeta : IsPrimitiveRoot zeta 59)
    (j : VandiverFactorIndex59) :
    (conjugate_isPrimitive hzeta j).toInteger =
      hzeta.toInteger ^ conjugateExponent59 j := by
  apply RingOfIntegers.ext
  rfl

omit [IsCyclotomicExtension {59} ℚ K] in
/-- The normalization `2*29 + 946 = 1 (mod 59)` makes every basic factor
real. -/
theorem basicVandiverUnit59_mem_realUnits {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 59) (j : VandiverFactorIndex59) :
    basicVandiverUnit59 hzeta j ∈ NumberField.IsCMField.realUnits K := by
  apply normalizedCircularUnit_mem_realUnits (p := 59) (a := 946) (e := 29)
  decide

/-- The ambient integral diagonal unit `(E_(i+1)(zeta))^rho`. -/
def diagonalVandiverUnit59 {zeta : K} (hzeta : IsPrimitiveRoot zeta 59)
    (i : Fin 28) : (RingOfIntegers K)ˣ :=
  ∏ j : VandiverFactorIndex59,
    basicVandiverUnit59 hzeta j ^ diagonalWeight59 i j

omit [IsCyclotomicExtension {59} ℚ K] in
theorem diagonalVandiverUnit59_mem_realUnits {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 59) (i : Fin 28) :
    diagonalVandiverUnit59 hzeta i ∈ NumberField.IsCMField.realUnits K := by
  apply Subgroup.prod_mem
  intro j hj
  exact Subgroup.pow_mem _ (basicVandiverUnit59_mem_realUnits hzeta j) _

/-- Vandiver's twenty-eight integral diagonal units, typed in the real-unit
subgroup consumed by Lemma II. -/
def diagonalVandiverUnitFamily59 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 59) :
    Fin 28 → NumberField.IsCMField.realUnits K :=
  fun i ↦ ⟨diagonalVandiverUnit59 hzeta i,
    diagonalVandiverUnit59_mem_realUnits hzeta i⟩

omit [IsCyclotomicExtension {59} ℚ K] in
@[simp]
theorem diagonalVandiverUnitFamily59_coe {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 59) (i : Fin 28) :
    ((diagonalVandiverUnitFamily59 hzeta i :
      NumberField.IsCMField.realUnits K) : (RingOfIntegers K)ˣ) =
      diagonalVandiverUnit59 hzeta i := rfl

/-! ## The auxiliary-prime evaluation matrix -/

/-- The geometric sum in the reduction of a basic Vandiver factor. -/
def basicResidueGeomSum59 (row : Fin 28) (j : VandiverFactorIndex59) :
    ZMod 827 :=
  let w := Fermat.FiftyNine.CircularUnitResidues.embeddingRoot row ^
    conjugateExponent59 j
  ∑ k ∈ Finset.range 946, w ^ k

/-- The value of the `j`th basic factor after sending `zeta` to the
`row`th primitive root modulo `827`. -/
def basicResidueValue59 (row : Fin 28) (j : VandiverFactorIndex59) :
    ZMod 827 :=
  let w := Fermat.FiftyNine.CircularUnitResidues.embeddingRoot row ^
    conjugateExponent59 j
  w ^ 29 * basicResidueGeomSum59 row j

/-- Since the evaluated root has order `59`, the geometric sum of length
`946 = 16*59+2` reduces exactly to `1+w`. Keeping this as an algebraic lemma
also makes the later finite certificate small. -/
theorem basicResidueGeomSum59_eq (row : Fin 28)
    (j : VandiverFactorIndex59) :
    basicResidueGeomSum59 row j =
      1 + Fermat.FiftyNine.CircularUnitResidues.embeddingRoot row ^
        conjugateExponent59 j := by
  let w : ZMod 827 :=
    Fermat.FiftyNine.CircularUnitResidues.embeddingRoot row ^
      conjugateExponent59 j
  have hwroot : IsPrimitiveRoot w 59 := by
    apply (Fermat.FiftyNine.CircularUnitResidues.embeddingRoot_isPrimitive
      row).pow_of_coprime
    exact (by norm_num : Nat.Coprime 946 59).pow_left j.val
  have hwne : w - 1 ≠ 0 :=
    sub_ne_zero.mpr (hwroot.ne_one (by norm_num))
  apply mul_left_cancel₀ (a := w - 1) hwne
  rw [show (w - 1) * basicResidueGeomSum59 row j = w ^ 946 - 1 by
    simpa [basicResidueGeomSum59, w] using (mul_geom_sum w 946)]
  change w ^ 946 - 1 = (w - 1) * (1 + w)
  rw [show 946 = 59 * 16 + 2 by norm_num, pow_add, pow_mul,
    hwroot.pow_eq_one]
  ring

/-- Fourteenth-power discrete logs of `epsilon(w)` for the twenty-nine real
classes `w = 671^s`, `s = 1, ..., 29`. The first twenty-eight entries are
the first column of the existing circular-unit certificate; the last
entry is its missing real conjugacy class. -/
def basicSymbolByRealExponent59 : Fin 29 → Fin 59 := ![
  48, 35, 14, 4, 45, 5, 39, 3, 19, 22,
  35, 51, 46, 36, 30, 12, 3, 41, 54, 34,
  15, 31, 20, 4, 54, 25, 58, 48, 54
]

/-- Reduce `(row+1) * 946^j` modulo `59`, identify a residue with its
negative, and turn the resulting real class `1, ..., 29` into a
zero-based table index. -/
def conjugateRealIndex59 (row : Fin 28) (j : VandiverFactorIndex59) :
    Fin 29 :=
  let s := ((row.val + 1) * reducedConjugateExponent59 j) % 59
  let a := min s (59 - s)
  ⟨(a - 1) % 29, Nat.mod_lt _ (by norm_num)⟩

/-- The certified fourteenth-power residue exponent of a basic factor. -/
def basicSymbolExponent59 (row : Fin 28) (j : VandiverFactorIndex59) :
    Fin 59 :=
  basicSymbolByRealExponent59 (conjugateRealIndex59 row j)

/-- Direct finite-field check of all `28 * 29` basic-factor symbols. -/
theorem basicResidueValue59_fourteenthPower (row : Fin 28)
    (j : VandiverFactorIndex59) :
    basicResidueValue59 row j ^ 14 =
      (671 : ZMod 827) ^ (basicSymbolExponent59 row j).val := by
  rw [basicResidueValue59, basicResidueGeomSum59_eq]
  rw [pow_conjugateExponent59_eq_reduced _
    (Fermat.FiftyNine.CircularUnitResidues.embeddingRoot_isPrimitive
      row).pow_eq_one]
  fin_cases row <;> fin_cases j <;> decide

omit [NumberField.IsCMField K] in
/-- Reduction of the actual cyclotomic unit is exactly the finite
geometric value above. -/
theorem reductionHom_basicVandiverUnit59 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 59) (row : Fin 28)
    (j : VandiverFactorIndex59) :
    certificate59.reductionHom hzeta row
        (basicVandiverUnit59 hzeta j : RingOfIntegers K) =
      basicResidueValue59 row j := by
  unfold basicVandiverUnit59
  rw [normalizedCircularUnit_val]
  rw [conjugate_toInteger (hzeta := hzeta) j]
  simp only [map_mul, map_pow, map_sum, certificate59.reductionHom_zeta]
  rfl

omit [IsCyclotomicExtension {59} ℚ K] in
/-- The CM norm squares a basic Vandiver factor because the factor is
real. -/
@[simp]
theorem realUnitNorm_basicVandiverUnit59 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 59) (j : VandiverFactorIndex59) :
    realUnitNorm (basicVandiverUnit59 hzeta j) =
      basicVandiverUnit59 hzeta j ^ 2 := by
  change basicVandiverUnit59 hzeta j *
    NumberField.IsCMField.unitsComplexConj K
      (basicVandiverUnit59 hzeta j) = _
  rw [(NumberField.IsCMField.unitsComplexConj_eq_self_iff K _).mpr
    (basicVandiverUnit59_mem_realUnits hzeta j)]
  exact (pow_two _).symm

/-- The corrected residue logarithm of each actual basic factor is the
finite exponent certified above. -/
theorem correctedResidueLog_basicVandiverUnit59 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 59) (row : Fin 28)
    (j : VandiverFactorIndex59) :
    certificate59.correctedResidueLog hzeta row
        (Additive.ofMul (basicVandiverUnit59 hzeta j)) =
      ((basicSymbolExponent59 row j).val : ZMod 59) := by
  let u : (ZMod 827)ˣ :=
    Units.map (certificate59.reductionHom hzeta row)
      (realUnitNorm (basicVandiverUnit59 hzeta j))
  have huval : (u : ZMod 827) = basicResidueValue59 row j ^ 2 := by
    dsimp [u]
    rw [realUnitNorm_basicVandiverUnit59, Units.val_pow_eq_pow_val,
      map_pow, reductionHom_basicVandiverUnit59]
  have hpow : ((u : ZMod 827) ^ 14) =
      (671 : ZMod 827) ^ ((basicSymbolExponent59 row j).val * 2) := by
    calc
      (u : ZMod 827) ^ 14 = (basicResidueValue59 row j ^ 2) ^ 14 := by
        rw [huval]
      _ = (basicResidueValue59 row j ^ 14) ^ 2 := by ring
      _ = ((671 : ZMod 827) ^
          (basicSymbolExponent59 row j).val) ^ 2 := by
        rw [basicResidueValue59_fourteenthPower]
      _ = (671 : ZMod 827) ^
          ((basicSymbolExponent59 row j).val * 2) := by rw [pow_mul]
  change (2 : ZMod 59)⁻¹ * certificate59.residueLog (Additive.ofMul u) =
    ((basicSymbolExponent59 row j).val : ZMod 59)
  rw [certificate59.residueLog_eq_of_pow_eq u _ hpow]
  rw [Nat.cast_mul]
  have hhalf : (2 : ZMod 59)⁻¹ * 2 = 1 :=
    inv_mul_cancel₀ (by
      intro h
      have hdiv : 59 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 59).mp h
      norm_num at hdiv)
  calc
    (2 : ZMod 59)⁻¹ *
        ((basicSymbolExponent59 row j).val * 2 : ZMod 59) =
        (2⁻¹ * 2) * (basicSymbolExponent59 row j).val := by ring
    _ = ((basicSymbolExponent59 row j).val : ZMod 59) := by
      rw [hhalf, one_mul]

@[simp]
theorem quotientResidueLinear_basicVandiverUnit59 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 59) (row : Fin 28)
    (j : VandiverFactorIndex59) :
    certificate59.quotientResidueLinear hzeta row
        (classOfUnit (basicVandiverUnit59 hzeta j)) =
      ((basicSymbolExponent59 row j).val : ZMod 59) := by
  change certificate59.quotientResidueLog hzeta row
    (classOfUnit (basicVandiverUnit59 hzeta j)) = _
  rw [certificate59.quotientResidueLog_classOfUnit]
  exact correctedResidueLog_basicVandiverUnit59 hzeta row j

omit [NumberField K] [IsCyclotomicExtension {59} ℚ K]
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

/-- Casting the source's enormous positive integral weight modulo `59`
can be performed before exponentiation. -/
theorem diagonalWeight59_cast (i : Fin 28) (j : VandiverFactorIndex59) :
    (diagonalWeight59 i j : ZMod 59) =
      (teichmullerRoot59 : ZMod 59) ^
        (59 ^ 2 - 2 * (i.val + 1) * j.val) := by
  simp [diagonalWeight59, integralDiagonalWeight]

/-- Evaluation of a diagonal unit is the weighted sum of its twenty-nine
basic-factor symbols. -/
theorem quotientResidueLinear_diagonalVandiverUnit59_formula {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 59) (row i : Fin 28) :
    certificate59.quotientResidueLinear hzeta row
        (classOfUnit (diagonalVandiverUnit59 hzeta i)) =
      ∑ j : VandiverFactorIndex59,
        (teichmullerRoot59 : ZMod 59) ^
            (59 ^ 2 - 2 * (i.val + 1) * j.val) *
          ((basicSymbolExponent59 row j).val : ZMod 59) := by
  rw [diagonalVandiverUnit59, classOfUnit_prod_pow]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_nsmul, quotientResidueLinear_basicVandiverUnit59]
  simp only [nsmul_eq_mul]
  rw [diagonalWeight59_cast]

/-- The kernel-checked evaluation matrix of Vandiver's twenty-eight
diagonal units under the twenty-eight auxiliary-prime residue
functionals. -/
def diagonalResidueMatrix59 : Matrix (Fin 28) (Fin 28) (ZMod 59) := ![
  ![39, 38, 14, 41, 56, 21, 15, 13, 49, 1, 51, 22, 16, 43, 9, 53, 33, 40, 9, 46, 6, 21, 32, 42, 57, 31, 55, 43],
  ![38, 18, 11, 53, 55, 53, 25, 8, 48, 28, 48, 3, 57, 8, 41, 48, 6, 13, 53, 15, 54, 48, 6, 2, 53, 18, 44, 55],
  ![56, 10, 58, 20, 30, 57, 4, 43, 20, 41, 57, 20, 29, 34, 27, 15, 54, 42, 29, 36, 32, 5, 18, 43, 49, 38, 32, 31],
  ![34, 52, 55, 57, 34, 27, 22, 14, 41, 17, 7, 46, 15, 55, 36, 29, 44, 47, 4, 19, 14, 17, 38, 31, 41, 39, 47, 58],
  ![31, 32, 37, 16, 47, 35, 35, 11, 29, 16, 45, 48, 36, 44, 45, 17, 52, 6, 19, 35, 50, 9, 31, 40, 17, 50, 10, 56],
  ![47, 42, 54, 46, 40, 9, 46, 31, 22, 27, 12, 51, 48, 42, 5, 57, 42, 52, 20, 22, 52, 3, 55, 47, 29, 43, 2, 52],
  ![23, 24, 42, 9, 44, 12, 7, 18, 25, 25, 53, 12, 20, 23, 4, 7, 31, 14, 57, 17, 24, 45, 56, 32, 4, 30, 33, 37],
  ![18, 6, 39, 19, 6, 26, 17, 54, 51, 4, 17, 17, 35, 2, 46, 4, 8, 2, 17, 28, 8, 22, 44, 38, 5, 55, 14, 44],
  ![32, 43, 38, 4, 54, 3, 5, 56, 19, 29, 29, 45, 12, 31, 22, 51, 24, 50, 41, 41, 33, 4, 47, 37, 9, 58, 39, 10],
  ![6, 40, 8, 25, 43, 49, 19, 34, 26, 35, 25, 28, 25, 37, 28, 41, 47, 58, 7, 5, 37, 29, 39, 30, 51, 10, 8, 14],
  ![58, 47, 24, 17, 38, 28, 1, 38, 53, 49, 4, 26, 46, 39, 19, 21, 37, 38, 5, 57, 30, 20, 24, 6, 16, 23, 52, 34],
  ![11, 23, 34, 35, 14, 48, 57, 10, 36, 48, 46, 15, 53, 38, 49, 16, 13, 11, 26, 20, 55, 49, 14, 50, 28, 44, 37, 13],
  ![42, 13, 30, 22, 10, 29, 45, 42, 27, 57, 49, 16, 41, 33, 1, 25, 38, 32, 25, 7, 44, 7, 13, 11, 7, 42, 11, 2],
  ![33, 30, 33, 3, 39, 5, 51, 2, 57, 51, 36, 7, 27, 18, 51, 3, 11, 37, 21, 53, 39, 27, 40, 24, 12, 6, 50, 24],
  ![43, 55, 10, 15, 2, 36, 29, 50, 1, 7, 26, 49, 21, 54, 17, 46, 10, 24, 35, 12, 11, 19, 58, 55, 26, 8, 38, 39],
  ![13, 37, 18, 26, 8, 1, 48, 6, 3, 53, 16, 5, 3, 58, 26, 27, 39, 39, 28, 4, 13, 25, 23, 58, 15, 11, 23, 11],
  ![2, 11, 44, 36, 23, 22, 49, 52, 4, 26, 9, 1, 1, 6, 35, 22, 18, 30, 48, 3, 31, 57, 52, 33, 1, 34, 13, 42],
  ![10, 39, 13, 21, 13, 16, 28, 39, 15, 45, 3, 41, 28, 14, 15, 5, 58, 31, 12, 48, 2, 26, 42, 13, 27, 47, 43, 32],
  ![37, 33, 23, 29, 24, 4, 20, 23, 35, 5, 15, 21, 5, 24, 53, 28, 43, 18, 49, 29, 47, 1, 50, 39, 46, 24, 24, 23],
  ![24, 50, 40, 28, 18, 45, 12, 30, 5, 36, 27, 36, 19, 11, 3, 26, 30, 10, 15, 26, 38, 41, 11, 52, 35, 2, 30, 33],
  ![30, 56, 56, 49, 32, 41, 53, 55, 9, 22, 28, 27, 51, 47, 12, 12, 40, 56, 46, 21, 10, 36, 2, 44, 20, 52, 31, 50],
  ![55, 44, 2, 45, 31, 51, 41, 37, 17, 15, 35, 25, 9, 10, 21, 9, 55, 33, 36, 25, 34, 12, 34, 34, 48, 40, 18, 38],
  ![40, 34, 6, 7, 37, 46, 27, 24, 46, 21, 41, 19, 26, 52, 29, 19, 32, 44, 51, 49, 18, 51, 30, 54, 22, 33, 58, 8],
  ![44, 14, 52, 51, 58, 20, 36, 47, 16, 46, 19, 53, 45, 40, 20, 49, 56, 8, 22, 45, 23, 53, 10, 8, 25, 56, 6, 18],
  ![8, 58, 43, 12, 11, 19, 3, 32, 28, 20, 5, 35, 22, 56, 48, 1, 14, 54, 27, 51, 43, 46, 54, 10, 3, 54, 34, 40],
  ![50, 31, 32, 27, 33, 17, 16, 44, 12, 3, 1, 29, 17, 13, 57, 36, 23, 34, 3, 1, 42, 16, 43, 23, 21, 32, 56, 30],
  ![52, 2, 31, 48, 50, 25, 21, 40, 21, 9, 22, 57, 7, 30, 7, 20, 50, 23, 1, 9, 58, 15, 8, 14, 45, 14, 42, 47],
  ![14, 8, 47, 1, 52, 7, 26, 33, 45, 12, 20, 9, 4, 50, 16, 35, 2, 43, 45, 16, 56, 28, 37, 18, 36, 13, 40, 6]
]

/-- An explicit inverse of `diagonalResidueMatrix59`. -/
def diagonalResidueMatrixInverse59 :
    Matrix (Fin 28) (Fin 28) (ZMod 59) := ![
  ![41, 7, 16, 28, 14, 45, 58, 48, 46, 15, 37, 8, 49, 26, 13, 53, 34, 23, 19, 30, 31, 6, 32, 43, 20, 9, 10, 18],
  ![7, 48, 23, 10, 46, 49, 30, 15, 13, 32, 45, 58, 53, 31, 6, 19, 8, 41, 26, 9, 16, 43, 28, 18, 37, 14, 34, 20],
  ![9, 58, 28, 56, 10, 50, 40, 32, 57, 11, 21, 19, 22, 17, 14, 39, 34, 44, 49, 23, 7, 25, 6, 1, 4, 37, 5, 36],
  ![11, 44, 18, 25, 46, 6, 50, 27, 53, 31, 10, 29, 40, 43, 16, 33, 1, 52, 28, 45, 36, 41, 49, 39, 14, 13, 51, 22],
  ![26, 16, 41, 38, 55, 42, 53, 25, 10, 23, 17, 28, 33, 51, 44, 30, 9, 4, 40, 58, 56, 24, 29, 47, 18, 36, 19, 20],
  ![36, 28, 9, 56, 13, 34, 57, 17, 27, 20, 29, 35, 12, 43, 44, 6, 24, 30, 37, 25, 54, 23, 49, 2, 11, 53, 15, 33],
  ![25, 40, 3, 49, 38, 15, 58, 19, 9, 36, 31, 34, 50, 48, 37, 1, 45, 54, 27, 23, 53, 20, 22, 10, 52, 55, 2, 42],
  ![16, 42, 35, 40, 30, 36, 11, 22, 38, 50, 29, 45, 12, 56, 31, 37, 32, 4, 21, 53, 28, 41, 52, 8, 9, 6, 54, 48],
  ![46, 2, 28, 21, 38, 50, 41, 49, 37, 43, 54, 11, 23, 35, 32, 53, 4, 26, 39, 10, 1, 20, 16, 56, 55, 24, 3, 51],
  ![54, 18, 43, 42, 19, 45, 4, 26, 1, 2, 9, 24, 57, 12, 22, 17, 6, 14, 32, 33, 13, 48, 25, 38, 50, 16, 23, 46],
  ![46, 58, 32, 56, 48, 21, 51, 17, 35, 38, 1, 13, 43, 8, 40, 53, 57, 50, 23, 20, 52, 36, 18, 34, 7, 29, 47, 25],
  ![46, 49, 24, 12, 57, 45, 20, 16, 47, 51, 39, 22, 52, 55, 42, 6, 28, 17, 58, 7, 19, 37, 33, 50, 35, 34, 31, 56],
  ![10, 48, 51, 39, 24, 15, 41, 52, 37, 54, 29, 8, 34, 36, 16, 7, 45, 9, 23, 50, 3, 14, 56, 5, 4, 33, 13, 17],
  ![26, 33, 41, 19, 56, 3, 12, 47, 27, 32, 54, 20, 39, 2, 13, 50, 28, 31, 43, 21, 58, 36, 23, 45, 29, 7, 44, 22],
  ![19, 39, 41, 29, 10, 28, 22, 34, 9, 14, 55, 5, 50, 8, 38, 2, 57, 44, 13, 12, 42, 21, 56, 46, 20, 53, 18, 15],
  ![3, 10, 34, 46, 28, 43, 8, 12, 57, 29, 11, 5, 49, 2, 24, 31, 58, 18, 4, 51, 32, 9, 45, 54, 40, 19, 36, 47],
  ![57, 46, 31, 15, 41, 21, 45, 51, 2, 17, 50, 25, 38, 39, 54, 13, 20, 9, 44, 3, 4, 37, 18, 47, 49, 30, 40, 6],
  ![26, 47, 43, 39, 9, 4, 12, 28, 3, 31, 1, 2, 40, 13, 24, 35, 25, 8, 42, 17, 10, 20, 37, 14, 53, 22, 52, 7],
  ![4, 57, 41, 7, 40, 31, 38, 23, 24, 3, 13, 46, 44, 6, 42, 58, 5, 27, 49, 29, 19, 14, 52, 53, 26, 56, 35, 54],
  ![52, 3, 47, 14, 16, 27, 56, 32, 57, 46, 12, 5, 36, 31, 1, 40, 30, 38, 15, 20, 39, 18, 23, 28, 26, 9, 37, 33],
  ![42, 27, 14, 45, 36, 37, 57, 47, 53, 46, 58, 33, 11, 9, 35, 21, 41, 2, 13, 34, 50, 55, 16, 26, 40, 17, 5, 43],
  ![23, 22, 30, 40, 21, 14, 12, 11, 24, 58, 48, 7, 20, 43, 57, 2, 55, 4, 52, 41, 31, 44, 10, 15, 36, 17, 46, 16],
  ![20, 48, 22, 40, 47, 39, 49, 17, 19, 15, 4, 51, 27, 6, 11, 32, 43, 23, 42, 41, 8, 2, 5, 56, 33, 46, 53, 52],
  ![33, 18, 56, 57, 16, 29, 30, 50, 3, 15, 58, 52, 51, 14, 49, 21, 10, 37, 25, 53, 27, 12, 43, 4, 7, 42, 2, 32],
  ![57, 17, 9, 43, 42, 1, 26, 32, 23, 12, 19, 18, 22, 46, 6, 48, 54, 45, 38, 2, 50, 24, 13, 4, 16, 25, 14, 33],
  ![54, 29, 47, 22, 49, 53, 12, 46, 18, 4, 39, 24, 30, 55, 1, 48, 9, 26, 11, 15, 50, 13, 7, 56, 40, 27, 58, 34],
  ![6, 43, 46, 45, 23, 34, 26, 18, 41, 20, 10, 19, 8, 9, 7, 58, 53, 13, 30, 31, 14, 48, 37, 15, 28, 16, 49, 32],
  ![13, 6, 14, 37, 16, 10, 19, 43, 23, 18, 28, 53, 34, 30, 41, 8, 49, 46, 58, 26, 9, 7, 20, 48, 32, 31, 45, 15]
]

theorem diagonalResidueFormula_eq_matrix (row i : Fin 28) :
    (∑ j : VandiverFactorIndex59,
        (teichmullerRoot59 : ZMod 59) ^
            (59 ^ 2 - 2 * (i.val + 1) * j.val) *
          ((basicSymbolExponent59 row j).val : ZMod 59)) =
      diagonalResidueMatrix59 row i := by
  fin_cases row <;> fin_cases i <;> decide

theorem diagonalResidueMatrix_mul_inverse :
    diagonalResidueMatrix59 * diagonalResidueMatrixInverse59 = 1 := by
  decide

theorem diagonalResidueMatrix_det_ne_zero :
    diagonalResidueMatrix59.det ≠ 0 := by
  intro hzero
  have hdet := congrArg Matrix.det diagonalResidueMatrix_mul_inverse
  rw [Matrix.det_mul, hzero, zero_mul, Matrix.det_one] at hdet
  exact (by decide : (0 : ZMod 59) ≠ 1) hdet

@[simp]
theorem quotientResidueLinear_diagonalVandiverUnit59 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 59) (row i : Fin 28) :
    certificate59.quotientResidueLinear hzeta row
        (classOfUnit (diagonalVandiverUnit59 hzeta i)) =
      diagonalResidueMatrix59 row i := by
  rw [quotientResidueLinear_diagonalVandiverUnit59_formula]
  exact diagonalResidueFormula_eq_matrix row i

/-- The residue functionals realize the complete diagonal-unit matrix. -/
theorem evalMatrix_diagonalVandiverUnit59 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 59) :
    evalMatrix (classOfUnit ∘ diagonalVandiverUnit59 hzeta)
        (certificate59.residueFunctionals hzeta) =
      diagonalResidueMatrix59 := by
  ext row i
  exact quotientResidueLinear_diagonalVandiverUnit59 hzeta row i

/-- The actual diagonal units have full ambient unit index prime to `59`. -/
theorem not_dvd_diagonalVandiverUnit59_full_index {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 59) :
    ¬59 ∣ (Subgroup.closure (Set.range (diagonalVandiverUnit59 hzeta)) ⊔
      NumberField.Units.torsion K).index := by
  apply not_dvd_unitIndex_of_eval_det_ne_zero
    (certificate59.basisModTorsion (K := K))
      (diagonalVandiverUnit59 hzeta)
      (certificate59.residueFunctionals hzeta)
  rw [evalMatrix_diagonalVandiverUnit59]
  exact diagonalResidueMatrix_det_ne_zero

/-- The closure of Vandiver's diagonal family has finite index in the
ambient unit group. -/
theorem ambient_closure_finiteIndex {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 59) :
    (Subgroup.closure
      (Set.range (diagonalVandiverUnit59 hzeta))).FiniteIndex := by
  have hnot := not_dvd_diagonalVandiverUnit59_full_index hzeta
  have hsup :
      (Subgroup.closure (Set.range (diagonalVandiverUnit59 hzeta)) ⊔
        NumberField.Units.torsion K).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff]
    intro hzero
    apply hnot
    rw [hzero]
    exact dvd_zero 59
  exact (NumberField.Units.finiteIndex_iff_sup_torsion_finiteIndex
    (Subgroup.closure (Set.range (diagonalVandiverUnit59 hzeta)))).2 hsup

/-- The same family has finite-index closure in the real-unit subgroup,
the exact group used by Vandiver's Lemma II bridge. -/
theorem real_closure_finiteIndex {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 59) :
    (Subgroup.closure
      (Set.range (diagonalVandiverUnitFamily59 hzeta))).FiniteIndex := by
  letI :
      (Subgroup.closure (Set.range fun i : Fin 28 ↦
        ((diagonalVandiverUnitFamily59 hzeta i :
          NumberField.IsCMField.realUnits K) : (RingOfIntegers K)ˣ))).FiniteIndex := by
    simpa [diagonalVandiverUnitFamily59] using
      ambient_closure_finiteIndex hzeta
  exact Fermat.Irregular.VandiverFiniteIndex.closure_range_subtype
    (NumberField.IsCMField.realUnits K)
      (diagonalVandiverUnitFamily59 hzeta)

end

end Fermat.FiftyNine.VandiverDiagonalUnits
