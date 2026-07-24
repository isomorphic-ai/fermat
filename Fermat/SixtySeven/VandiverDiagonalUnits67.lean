import Fermat.Irregular.VandiverDiagonalLogDerivative
import Fermat.Irregular.VandiverFiniteIndex
import Fermat.SixtySeven.CircularUnitResidues
import Fermat.SixtySeven.VandiverDiagonalArithmetic67

/-!
# Vandiver's diagonal real-unit family at exponent 67

This module realizes in the cyclotomic unit group the integral diagonal
family used in Vandiver's Lemma 2.  Put

`epsilon(w) = w^33 * (w^1342 - 1) / (w - 1)`.

For `i = 1, ..., 32`, Vandiver first assigns the formal weights
`1342^(-2*i*j)` to the conjugates `epsilon(zeta^(1342^j))`.  Raising to
`rho = 1342^(67^2)` replaces them by the positive integral weights
`1342^(67^2 - 2*i*j)`.  The resulting units are the family defined here.

The first display on p. 617 prints the lower product limit as `j = 1`.
That is a one-character typo: the immediately following positive-exponent
display starts at `j = 0`, and formula (4) starts its character sum with
the `j = 0` term `1`. Accordingly `VandiverFactorIndex67` is `Fin 33`,
machine-checking the source-faithful range `j = 0, ..., 32`.

Besides reality, this file proves that the thirty-two diagonal units have
finite-index closure.  The proof evaluates them under the already
constructed power-residue functionals at the auxiliary prime `269` and
kernel-checks the resulting finite determinant.
-/

open scoped NumberField

namespace Fermat.SixtySeven.VandiverDiagonalUnits

noncomputable section

open Fermat.Irregular
open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitIndex
open Fermat.Irregular.CircularUnitResidues
open Fermat.Irregular.CircularUnitResidues.Certificate
open Fermat.Irregular.CircularUnits
open Fermat.Irregular.VandiverDiagonalLogDerivative
open Fermat.SixtySeven.VandiverDiagonalArithmetic
open NumberField NumberField.Units

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 67) := ⟨Fermat.SixtySeven.prime_67⟩
local instance : Fact (Nat.Prime 269) := ⟨Fermat.SixtySeven.prime_269⟩

abbrev certificate67 : Certificate 67 269 :=
  Fermat.SixtySeven.CircularUnitResidues.certificate

/-- The corrected source range `j = 0, ..., 32`.  In particular, the
constant term omitted by the p. 617 typo is an actual member of the type. -/
abbrev VandiverFactorIndex67 := Fin 33

theorem card_vandiverFactorIndex67 :
    Fintype.card VandiverFactorIndex67 = 33 := by decide

/-- The power of the chosen root occurring in the `j`th conjugate. -/
def conjugateExponent67 (j : VandiverFactorIndex67) : ℕ :=
  teichmullerRoot67 ^ j.val

/-- The least residue of the same source exponent modulo `67`.  This is
used only to keep finite-field normalization small; the actual unit above
continues to use the literal exponent `1342^j`. -/
def reducedConjugateExponent67 (j : VandiverFactorIndex67) : ℕ :=
  ((teichmullerRoot67 : ZMod 67) ^ j.val).val

theorem conjugateExponent67_modEq_reduced (j : VandiverFactorIndex67) :
    conjugateExponent67 j ≡ reducedConjugateExponent67 j [MOD 67] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  simp [conjugateExponent67, reducedConjugateExponent67]

theorem pow_conjugateExponent67_eq_reduced {G : Type*} [Monoid G]
    (x : G) (hx : x ^ 67 = 1) (j : VandiverFactorIndex67) :
    x ^ conjugateExponent67 j = x ^ reducedConjugateExponent67 j :=
  pow_eq_pow_of_modEq (conjugateExponent67_modEq_reduced j) hx

/-- Vandiver's integral positive weight for unit index `i + 1` and
conjugate index `j`.  This is definitionally the weight used by the formal
power-series diagonalization. -/
def diagonalWeight67 (i : Fin 32) (j : VandiverFactorIndex67) : ℕ :=
  integralDiagonalWeight 67 teichmullerRoot67 (i.val + 1) j.val

theorem diagonalWeight67_eq (i : Fin 32) (j : VandiverFactorIndex67) :
    diagonalWeight67 i j =
      1342 ^ (67 ^ 2 - 2 * (i.val + 1) * j.val) := by
  rfl

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {67} ℚ K] [NumberField.IsCMField K]

omit [NumberField K] [IsCyclotomicExtension {67} ℚ K]
    [NumberField.IsCMField K] in
/-- Each `zeta^(1342^j)` is again a primitive 67th root. -/
theorem conjugate_isPrimitive {zeta : K} (hzeta : IsPrimitiveRoot zeta 67)
    (j : VandiverFactorIndex67) :
    IsPrimitiveRoot (zeta ^ conjugateExponent67 j) 67 := by
  apply hzeta.pow_of_coprime
  exact (by norm_num : Nat.Coprime 1342 67).pow_left j.val

/-- The basic real unit `epsilon(zeta^(1342^j))`.  Its geometric length is
literally `1342`, rather than being reduced modulo `67`, so its definition
matches Vandiver's integral polynomial. -/
def basicVandiverUnit67 {zeta : K} (hzeta : IsPrimitiveRoot zeta 67)
    (j : VandiverFactorIndex67) : (RingOfIntegers K)ˣ :=
  normalizedCircularUnit (p := 67) (a := 1342)
    (conjugate_isPrimitive hzeta j) (by norm_num) (by norm_num) 33

omit [NumberField K] [IsCyclotomicExtension {67} ℚ K]
    [NumberField.IsCMField K] in
/-- The integral lift of a conjugate root is the corresponding power of
the chosen integral lift. -/
theorem conjugate_toInteger {zeta : K} (hzeta : IsPrimitiveRoot zeta 67)
    (j : VandiverFactorIndex67) :
    (conjugate_isPrimitive hzeta j).toInteger =
      hzeta.toInteger ^ conjugateExponent67 j := by
  apply RingOfIntegers.ext
  rfl

omit [IsCyclotomicExtension {67} ℚ K] in
/-- The normalization `2*33 + 1342 = 1 (mod 67)` makes every basic factor
real. -/
theorem basicVandiverUnit67_mem_realUnits {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 67) (j : VandiverFactorIndex67) :
    basicVandiverUnit67 hzeta j ∈ NumberField.IsCMField.realUnits K := by
  apply normalizedCircularUnit_mem_realUnits (p := 67) (a := 1342) (e := 33)
  decide

/-- The ambient integral diagonal unit `(E_(i+1)(zeta))^rho`. -/
def diagonalVandiverUnit67 {zeta : K} (hzeta : IsPrimitiveRoot zeta 67)
    (i : Fin 32) : (RingOfIntegers K)ˣ :=
  ∏ j : VandiverFactorIndex67,
    basicVandiverUnit67 hzeta j ^ diagonalWeight67 i j

omit [IsCyclotomicExtension {67} ℚ K] in
theorem diagonalVandiverUnit67_mem_realUnits {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 67) (i : Fin 32) :
    diagonalVandiverUnit67 hzeta i ∈ NumberField.IsCMField.realUnits K := by
  apply Subgroup.prod_mem
  intro j hj
  exact Subgroup.pow_mem _ (basicVandiverUnit67_mem_realUnits hzeta j) _

/-- Vandiver's thirty-two integral diagonal units, typed in the real-unit
subgroup consumed by Lemma II. -/
def diagonalVandiverUnitFamily67 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 67) :
    Fin 32 → NumberField.IsCMField.realUnits K :=
  fun i ↦ ⟨diagonalVandiverUnit67 hzeta i,
    diagonalVandiverUnit67_mem_realUnits hzeta i⟩

omit [IsCyclotomicExtension {67} ℚ K] in
@[simp]
theorem diagonalVandiverUnitFamily67_coe {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 67) (i : Fin 32) :
    ((diagonalVandiverUnitFamily67 hzeta i :
      NumberField.IsCMField.realUnits K) : (RingOfIntegers K)ˣ) =
      diagonalVandiverUnit67 hzeta i := rfl

/-! ## The auxiliary-prime evaluation matrix -/

/-- Every row root `16^(row+1)` has exact order `67` modulo `269`. -/
theorem embeddingRoot67_isPrimitive (row : Fin 32) :
    IsPrimitiveRoot
      (Fermat.SixtySeven.CircularUnitResidues.embeddingRoot row) 67 := by
  have h16 : IsPrimitiveRoot (16 : ZMod 269) 67 :=
    IsPrimitiveRoot.iff_orderOf.mpr
      Fermat.SixtySeven.CircularUnitResidues.root_order
  apply h16.pow_of_coprime
  exact Nat.Coprime.symm <| Nat.coprime_of_lt_prime
    (by omega) (by omega) Fermat.SixtySeven.prime_67

/-- The geometric sum in the reduction of a basic Vandiver factor. -/
def basicResidueGeomSum67 (row : Fin 32) (j : VandiverFactorIndex67) :
    ZMod 269 :=
  let w := Fermat.SixtySeven.CircularUnitResidues.embeddingRoot row ^
    conjugateExponent67 j
  ∑ k ∈ Finset.range 1342, w ^ k

/-- The value of the `j`th basic factor after sending `zeta` to the
`row`th primitive root modulo `269`. -/
def basicResidueValue67 (row : Fin 32) (j : VandiverFactorIndex67) :
    ZMod 269 :=
  let w := Fermat.SixtySeven.CircularUnitResidues.embeddingRoot row ^
    conjugateExponent67 j
  w ^ 33 * basicResidueGeomSum67 row j

/-- Since the evaluated root has order `67`, the geometric sum of length
`1342 = 20*67+2` reduces exactly to `1+w`. Keeping this as an algebraic lemma
also makes the later finite certificate small. -/
theorem basicResidueGeomSum67_eq (row : Fin 32)
    (j : VandiverFactorIndex67) :
    basicResidueGeomSum67 row j =
      1 + Fermat.SixtySeven.CircularUnitResidues.embeddingRoot row ^
        conjugateExponent67 j := by
  let w : ZMod 269 :=
    Fermat.SixtySeven.CircularUnitResidues.embeddingRoot row ^
      conjugateExponent67 j
  have hwroot : IsPrimitiveRoot w 67 := by
    apply (embeddingRoot67_isPrimitive row).pow_of_coprime
    exact (by norm_num : Nat.Coprime 1342 67).pow_left j.val
  have hwne : w - 1 ≠ 0 :=
    sub_ne_zero.mpr (hwroot.ne_one (by norm_num))
  apply mul_left_cancel₀ (a := w - 1) hwne
  rw [show (w - 1) * basicResidueGeomSum67 row j = w ^ 1342 - 1 by
    simpa [basicResidueGeomSum67, w] using (mul_geom_sum w 1342)]
  change w ^ 1342 - 1 = (w - 1) * (1 + w)
  rw [show 1342 = 67 * 20 + 2 by norm_num, pow_add, pow_mul,
    hwroot.pow_eq_one]
  ring

/-- Fourth-power discrete logs of `epsilon(w)` for the thirty-three real
classes `w = 16^s`, `s = 1, ..., 33`. The first thirty-two entries are
the first column of the existing circular-unit certificate; the last
entry is its missing real conjugacy class. -/
def basicSymbolByRealExponent67 : Fin 33 → Fin 67 := ![
  36, 40, 53, 38, 39, 19, 18, 30, 42, 0, 5,
  13, 32, 62, 6, 22, 29, 29, 51, 42, 28, 60,
  24, 27, 50, 36, 19, 25, 64, 2, 57, 33, 41
]

/-- Reduce `(row+1) * 1342^j` modulo `67`, identify a residue with its
negative, and turn the resulting real class `1, ..., 33` into a
zero-based table index. -/
def conjugateRealIndex67 (row : Fin 32) (j : VandiverFactorIndex67) :
    Fin 33 :=
  let s := ((row.val + 1) * reducedConjugateExponent67 j) % 67
  let a := min s (67 - s)
  ⟨(a - 1) % 33, Nat.mod_lt _ (by norm_num)⟩

/-- The certified fourth-power residue exponent of a basic factor. -/
def basicSymbolExponent67 (row : Fin 32) (j : VandiverFactorIndex67) :
    Fin 67 :=
  basicSymbolByRealExponent67 (conjugateRealIndex67 row j)

/-- Direct finite-field check of all `32 * 33` basic-factor symbols. -/
theorem basicResidueValue67_fourthPower (row : Fin 32)
    (j : VandiverFactorIndex67) :
    basicResidueValue67 row j ^ 4 =
      (16 : ZMod 269) ^ (basicSymbolExponent67 row j).val := by
  rw [basicResidueValue67, basicResidueGeomSum67_eq]
  rw [pow_conjugateExponent67_eq_reduced _
    (embeddingRoot67_isPrimitive row).pow_eq_one]
  fin_cases row <;> fin_cases j <;> decide

omit [NumberField.IsCMField K] in
/-- Reduction of the actual cyclotomic unit is exactly the finite
geometric value above. -/
theorem reductionHom_basicVandiverUnit67 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 67) (row : Fin 32)
    (j : VandiverFactorIndex67) :
    certificate67.reductionHom hzeta row
        (basicVandiverUnit67 hzeta j : RingOfIntegers K) =
      basicResidueValue67 row j := by
  unfold basicVandiverUnit67
  rw [normalizedCircularUnit_val]
  rw [conjugate_toInteger (hzeta := hzeta) j]
  simp only [map_mul, map_pow, map_sum, certificate67.reductionHom_zeta]
  rfl

omit [IsCyclotomicExtension {67} ℚ K] in
/-- The CM norm squares a basic Vandiver factor because the factor is
real. -/
@[simp]
theorem realUnitNorm_basicVandiverUnit67 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 67) (j : VandiverFactorIndex67) :
    realUnitNorm (basicVandiverUnit67 hzeta j) =
      basicVandiverUnit67 hzeta j ^ 2 := by
  change basicVandiverUnit67 hzeta j *
    NumberField.IsCMField.unitsComplexConj K
      (basicVandiverUnit67 hzeta j) = _
  rw [(NumberField.IsCMField.unitsComplexConj_eq_self_iff K _).mpr
    (basicVandiverUnit67_mem_realUnits hzeta j)]
  exact (pow_two _).symm

/-- The corrected residue logarithm of each actual basic factor is the
finite exponent certified above. -/
theorem correctedResidueLog_basicVandiverUnit67 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 67) (row : Fin 32)
    (j : VandiverFactorIndex67) :
    certificate67.correctedResidueLog hzeta row
        (Additive.ofMul (basicVandiverUnit67 hzeta j)) =
      ((basicSymbolExponent67 row j).val : ZMod 67) := by
  let u : (ZMod 269)ˣ :=
    Units.map (certificate67.reductionHom hzeta row)
      (realUnitNorm (basicVandiverUnit67 hzeta j))
  have huval : (u : ZMod 269) = basicResidueValue67 row j ^ 2 := by
    dsimp [u]
    rw [realUnitNorm_basicVandiverUnit67, Units.val_pow_eq_pow_val,
      map_pow, reductionHom_basicVandiverUnit67]
  have hpow : ((u : ZMod 269) ^ 4) =
      (16 : ZMod 269) ^ ((basicSymbolExponent67 row j).val * 2) := by
    calc
      (u : ZMod 269) ^ 4 = (basicResidueValue67 row j ^ 2) ^ 4 := by
        rw [huval]
      _ = (basicResidueValue67 row j ^ 4) ^ 2 := by ring
      _ = ((16 : ZMod 269) ^
          (basicSymbolExponent67 row j).val) ^ 2 := by
        rw [basicResidueValue67_fourthPower]
      _ = (16 : ZMod 269) ^
          ((basicSymbolExponent67 row j).val * 2) := by rw [pow_mul]
  change (2 : ZMod 67)⁻¹ * certificate67.residueLog (Additive.ofMul u) =
    ((basicSymbolExponent67 row j).val : ZMod 67)
  rw [certificate67.residueLog_eq_of_pow_eq u _ hpow]
  rw [Nat.cast_mul]
  have hhalf : (2 : ZMod 67)⁻¹ * 2 = 1 :=
    inv_mul_cancel₀ (by
      intro h
      have hdiv : 67 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 67).mp h
      norm_num at hdiv)
  calc
    (2 : ZMod 67)⁻¹ *
        ((basicSymbolExponent67 row j).val * 2 : ZMod 67) =
        (2⁻¹ * 2) * (basicSymbolExponent67 row j).val := by ring
    _ = ((basicSymbolExponent67 row j).val : ZMod 67) := by
      rw [hhalf, one_mul]

@[simp]
theorem quotientResidueLinear_basicVandiverUnit67 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 67) (row : Fin 32)
    (j : VandiverFactorIndex67) :
    certificate67.quotientResidueLinear hzeta row
        (classOfUnit (basicVandiverUnit67 hzeta j)) =
      ((basicSymbolExponent67 row j).val : ZMod 67) := by
  change certificate67.quotientResidueLog hzeta row
    (classOfUnit (basicVandiverUnit67 hzeta j)) = _
  rw [certificate67.quotientResidueLog_classOfUnit]
  exact correctedResidueLog_basicVandiverUnit67 hzeta row j

omit [NumberField K] [IsCyclotomicExtension {67} ℚ K]
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

/-- Casting the source's enormous positive integral weight modulo `67`
can be performed before exponentiation. -/
theorem diagonalWeight67_cast (i : Fin 32) (j : VandiverFactorIndex67) :
    (diagonalWeight67 i j : ZMod 67) =
      (teichmullerRoot67 : ZMod 67) ^
        (67 ^ 2 - 2 * (i.val + 1) * j.val) := by
  simp [diagonalWeight67, integralDiagonalWeight]

/-- Evaluation of a diagonal unit is the weighted sum of its thirty-three
basic-factor symbols. -/
theorem quotientResidueLinear_diagonalVandiverUnit67_formula {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 67) (row i : Fin 32) :
    certificate67.quotientResidueLinear hzeta row
        (classOfUnit (diagonalVandiverUnit67 hzeta i)) =
      ∑ j : VandiverFactorIndex67,
        (teichmullerRoot67 : ZMod 67) ^
            (67 ^ 2 - 2 * (i.val + 1) * j.val) *
          ((basicSymbolExponent67 row j).val : ZMod 67) := by
  rw [diagonalVandiverUnit67, classOfUnit_prod_pow]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_nsmul, quotientResidueLinear_basicVandiverUnit67]
  simp only [nsmul_eq_mul]
  rw [diagonalWeight67_cast]

/-- The kernel-checked evaluation matrix of Vandiver's thirty-two
diagonal units under the thirty-two auxiliary-prime residue
functionals. -/
def diagonalResidueMatrix67 : Matrix (Fin 32) (Fin 32) (ZMod 67) := ![
  ![62, 25, 40, 1, 29, 46, 18, 55, 57, 19, 11, 50, 29, 28, 40, 23, 12, 12, 43, 6, 7, 54, 11, 60, 25, 40, 9, 37, 25, 47, 61, 54],
  ![47, 65, 14, 55, 15, 12, 45, 14, 2, 25, 5, 30, 16, 41, 62, 22, 43, 38, 31, 36, 34, 25, 3, 35, 36, 16, 1, 9, 37, 29, 8, 47],
  ![22, 15, 15, 62, 35, 63, 50, 35, 28, 17, 11, 48, 4, 44, 1, 37, 31, 11, 3, 10, 38, 54, 32, 36, 1, 1, 64, 23, 62, 36, 57, 6],
  ![54, 35, 25, 10, 17, 41, 12, 6, 13, 47, 51, 18, 25, 5, 9, 56, 48, 31, 13, 15, 12, 55, 13, 26, 17, 60, 15, 4, 36, 35, 34, 62],
  ![9, 14, 24, 15, 21, 38, 28, 47, 30, 49, 11, 44, 35, 57, 64, 49, 7, 41, 27, 49, 11, 54, 7, 47, 15, 64, 25, 16, 24, 56, 18, 37],
  ![21, 39, 22, 60, 62, 31, 58, 15, 48, 40, 5, 2, 23, 7, 25, 15, 5, 46, 38, 60, 41, 25, 27, 21, 47, 54, 22, 40, 6, 55, 58, 35],
  ![23, 60, 14, 54, 19, 12, 32, 49, 2, 55, 51, 30, 62, 43, 62, 35, 50, 38, 28, 59, 34, 55, 44, 35, 39, 56, 1, 60, 29, 29, 31, 64],
  ![15, 24, 59, 14, 55, 34, 30, 60, 51, 16, 11, 51, 60, 48, 24, 39, 38, 20, 53, 23, 20, 54, 34, 4, 62, 24, 24, 39, 64, 33, 44, 49],
  ![64, 9, 14, 25, 33, 12, 57, 4, 2, 54, 11, 30, 56, 50, 62, 10, 41, 38, 8, 39, 34, 54, 20, 35, 59, 62, 1, 65, 1, 29, 28, 23],
  ![36, 23, 62, 21, 64, 7, 3, 1, 61, 1, 5, 13, 17, 38, 59, 9, 53, 7, 7, 26, 63, 25, 8, 33, 35, 39, 40, 22, 65, 26, 43, 26],
  ![65, 4, 24, 19, 6, 38, 31, 23, 30, 4, 51, 44, 22, 45, 64, 4, 2, 41, 61, 14, 11, 55, 2, 47, 19, 47, 25, 56, 26, 56, 63, 1],
  ![17, 21, 1, 17, 39, 11, 11, 16, 44, 35, 51, 28, 15, 27, 22, 26, 57, 34, 57, 25, 46, 55, 50, 29, 65, 35, 62, 55, 33, 4, 12, 59],
  ![26, 6, 1, 26, 59, 11, 5, 62, 44, 22, 5, 28, 19, 46, 22, 24, 45, 34, 32, 55, 46, 25, 43, 29, 60, 10, 62, 25, 19, 4, 42, 36],
  ![25, 22, 25, 22, 26, 41, 13, 21, 13, 23, 11, 18, 55, 51, 9, 16, 34, 31, 42, 19, 12, 54, 12, 26, 24, 9, 15, 49, 59, 35, 48, 16],
  ![14, 62, 9, 59, 60, 20, 48, 36, 50, 65, 11, 61, 21, 13, 15, 6, 46, 32, 5, 37, 31, 54, 63, 55, 14, 15, 14, 19, 22, 60, 30, 19],
  ![60, 49, 24, 33, 40, 38, 8, 64, 30, 14, 5, 44, 10, 32, 64, 14, 58, 41, 46, 4, 11, 25, 58, 47, 33, 23, 25, 62, 17, 56, 53, 29],
  ![29, 37, 64, 47, 14, 32, 27, 24, 18, 59, 5, 57, 39, 63, 14, 25, 3, 63, 34, 56, 32, 25, 66, 56, 21, 49, 59, 24, 49, 21, 5, 60],
  ![55, 10, 25, 35, 24, 41, 42, 40, 13, 64, 5, 18, 54, 11, 9, 62, 52, 31, 12, 33, 12, 25, 42, 26, 26, 65, 15, 14, 39, 35, 52, 56],
  ![4, 16, 9, 36, 9, 20, 52, 59, 50, 9, 5, 61, 6, 12, 15, 40, 27, 32, 11, 29, 31, 25, 53, 55, 4, 19, 14, 15, 10, 60, 66, 33],
  ![10, 33, 15, 16, 10, 63, 41, 10, 28, 26, 51, 48, 14, 3, 1, 29, 28, 11, 44, 22, 38, 55, 57, 36, 37, 29, 64, 47, 56, 36, 32, 40],
  ![6, 36, 22, 65, 16, 31, 7, 19, 48, 21, 51, 2, 64, 58, 25, 33, 51, 46, 30, 9, 41, 55, 61, 21, 23, 55, 22, 21, 21, 55, 7, 22],
  ![59, 64, 62, 40, 47, 7, 44, 29, 61, 37, 11, 13, 26, 30, 59, 65, 63, 7, 58, 17, 63, 54, 31, 33, 22, 59, 40, 10, 9, 26, 50, 17],
  ![35, 19, 15, 56, 22, 63, 43, 22, 28, 24, 5, 48, 49, 20, 1, 1, 8, 11, 20, 35, 38, 25, 45, 36, 29, 37, 64, 64, 16, 36, 45, 21],
  ![1, 1, 64, 64, 4, 32, 61, 26, 18, 39, 11, 57, 36, 18, 14, 54, 20, 63, 52, 16, 32, 54, 38, 56, 40, 14, 59, 17, 14, 21, 51, 65],
  ![24, 40, 1, 24, 36, 11, 51, 56, 44, 10, 11, 28, 33, 61, 22, 17, 32, 34, 45, 54, 46, 54, 41, 29, 9, 22, 62, 54, 15, 4, 13, 39],
  ![37, 29, 64, 23, 49, 32, 46, 17, 18, 36, 51, 57, 59, 53, 14, 55, 44, 63, 48, 62, 32, 55, 30, 56, 6, 4, 59, 26, 4, 21, 11, 9],
  ![40, 59, 22, 9, 56, 31, 2, 33, 48, 6, 11, 2, 47, 2, 25, 19, 11, 46, 66, 65, 41, 54, 46, 21, 64, 25, 22, 6, 40, 55, 2, 10],
  ![33, 17, 59, 4, 25, 34, 66, 9, 51, 62, 5, 51, 65, 34, 24, 59, 66, 20, 63, 47, 20, 25, 52, 4, 56, 17, 24, 59, 23, 33, 3, 4],
  ![16, 55, 40, 37, 37, 46, 63, 54, 57, 33, 51, 50, 1, 8, 40, 47, 13, 12, 50, 40, 7, 55, 51, 60, 54, 21, 9, 29, 55, 47, 46, 25],
  ![56, 54, 40, 29, 1, 46, 53, 25, 57, 15, 5, 50, 37, 31, 40, 64, 42, 12, 41, 21, 7, 25, 5, 60, 55, 6, 9, 1, 54, 47, 27, 55],
  ![19, 26, 59, 49, 54, 34, 38, 65, 51, 56, 51, 51, 9, 52, 24, 36, 30, 20, 18, 64, 20, 55, 48, 4, 16, 26, 24, 36, 47, 33, 20, 14],
  ![39, 47, 62, 6, 23, 7, 20, 37, 61, 29, 51, 13, 24, 66, 59, 60, 18, 7, 2, 24, 63, 55, 28, 33, 10, 36, 40, 35, 60, 26, 41, 24]
]

/-- An explicit inverse of `diagonalResidueMatrix67`. -/
def diagonalResidueMatrixInverse67 :
    Matrix (Fin 32) (Fin 32) (ZMod 67) := ![
  ![39, 32, 58, 47, 22, 20, 49, 34, 8, 11, 53, 44, 21, 1, 4, 14, 45, 41, 18, 25, 7, 2, 6, 50, 24, 61, 62, 56, 10, 40, 66, 9],
  ![28, 13, 61, 33, 31, 36, 41, 51, 49, 9, 45, 47, 34, 18, 66, 27, 21, 52, 37, 16, 38, 35, 26, 10, 22, 5, 29, 4, 1, 7, 48, 59],
  ![40, 49, 12, 46, 2, 36, 49, 47, 49, 17, 2, 28, 28, 46, 0, 2, 53, 46, 0, 12, 36, 17, 12, 53, 28, 53, 36, 47, 40, 40, 47, 17],
  ![41, 32, 30, 16, 25, 5, 38, 62, 59, 11, 57, 35, 12, 49, 60, 47, 23, 64, 2, 1, 44, 53, 31, 66, 15, 40, 13, 9, 52, 36, 58, 65],
  ![59, 48, 20, 58, 34, 53, 13, 55, 3, 22, 21, 23, 16, 35, 28, 9, 18, 38, 36, 39, 24, 46, 5, 32, 25, 14, 54, 15, 8, 64, 61, 63],
  ![12, 58, 14, 11, 54, 21, 58, 43, 58, 18, 54, 59, 59, 11, 0, 54, 26, 11, 0, 14, 21, 18, 14, 26, 59, 26, 21, 43, 12, 12, 43, 18],
  ![56, 65, 12, 15, 47, 34, 50, 62, 31, 48, 45, 16, 17, 9, 57, 54, 61, 55, 22, 35, 42, 7, 32, 49, 46, 36, 3, 6, 38, 52, 11, 24],
  ![32, 62, 64, 65, 23, 25, 58, 5, 9, 41, 40, 1, 30, 11, 2, 66, 15, 53, 60, 16, 57, 36, 49, 12, 31, 35, 47, 13, 38, 59, 44, 52],
  ![19, 58, 35, 64, 50, 45, 58, 34, 58, 37, 50, 62, 62, 64, 0, 50, 44, 64, 0, 35, 45, 37, 35, 44, 62, 44, 45, 34, 19, 19, 34, 37],
  ![52, 54, 30, 18, 53, 48, 27, 63, 33, 36, 4, 59, 44, 35, 39, 57, 55, 61, 8, 7, 6, 47, 10, 62, 11, 64, 60, 25, 42, 20, 26, 31],
  ![37, 38, 37, 0, 37, 38, 0, 37, 37, 38, 0, 0, 38, 37, 37, 38, 38, 38, 38, 0, 0, 37, 38, 37, 37, 0, 37, 38, 0, 38, 0, 0],
  ![30, 13, 8, 7, 25, 21, 13, 64, 13, 27, 25, 65, 65, 7, 0, 25, 49, 7, 0, 8, 21, 27, 8, 49, 65, 49, 21, 64, 30, 30, 64, 27],
  ![50, 15, 23, 6, 11, 54, 44, 19, 45, 49, 63, 39, 4, 46, 25, 30, 14, 52, 12, 9, 13, 26, 5, 16, 61, 7, 37, 58, 55, 66, 27, 29],
  ![59, 47, 19, 29, 43, 54, 44, 2, 24, 23, 10, 6, 48, 58, 21, 62, 50, 28, 27, 60, 46, 7, 36, 1, 61, 64, 15, 12, 66, 57, 34, 18],
  ![28, 5, 16, 55, 41, 34, 5, 57, 5, 35, 41, 24, 24, 55, 0, 41, 37, 55, 0, 16, 34, 35, 16, 37, 24, 37, 34, 57, 28, 28, 57, 35],
  ![29, 38, 41, 20, 47, 14, 53, 56, 5, 2, 65, 1, 4, 57, 54, 51, 48, 19, 42, 25, 36, 33, 30, 27, 24, 21, 46, 49, 12, 55, 58, 61],
  ![33, 50, 63, 8, 60, 35, 30, 29, 53, 3, 21, 49, 16, 18, 54, 52, 66, 40, 12, 65, 64, 56, 5, 42, 1, 25, 34, 24, 27, 6, 13, 7],
  ![32, 28, 33, 62, 52, 53, 28, 41, 28, 59, 52, 17, 17, 62, 0, 52, 55, 62, 0, 33, 53, 59, 33, 55, 17, 55, 53, 41, 32, 32, 41, 59],
  ![53, 66, 2, 30, 15, 32, 1, 6, 8, 63, 3, 52, 4, 9, 38, 57, 21, 36, 37, 28, 16, 55, 45, 43, 19, 11, 27, 59, 33, 56, 10, 24],
  ![24, 28, 42, 51, 17, 31, 19, 66, 26, 38, 21, 18, 58, 16, 11, 35, 57, 6, 62, 8, 39, 61, 23, 27, 64, 56, 3, 49, 12, 37, 25, 41],
  ![64, 22, 33, 37, 38, 57, 22, 46, 22, 60, 38, 58, 58, 37, 0, 38, 5, 37, 0, 33, 57, 60, 33, 5, 58, 5, 57, 46, 64, 64, 46, 60],
  ![6, 27, 6, 0, 6, 27, 0, 6, 6, 27, 0, 0, 27, 6, 6, 27, 27, 27, 27, 0, 0, 6, 27, 6, 6, 0, 6, 27, 0, 27, 0, 0],
  ![27, 59, 61, 20, 53, 5, 18, 11, 35, 65, 14, 23, 43, 26, 49, 45, 17, 66, 63, 42, 60, 56, 9, 22, 46, 6, 47, 33, 57, 28, 1, 58],
  ![40, 32, 37, 47, 58, 46, 32, 44, 32, 15, 58, 4, 4, 47, 0, 58, 66, 47, 0, 37, 46, 15, 37, 66, 4, 66, 46, 44, 40, 40, 44, 15],
  ![1, 11, 50, 44, 34, 32, 9, 39, 2, 6, 66, 53, 14, 24, 4, 56, 20, 21, 18, 61, 49, 58, 45, 62, 22, 7, 8, 40, 47, 41, 10, 25],
  ![6, 21, 61, 25, 19, 58, 51, 35, 50, 20, 43, 17, 36, 33, 45, 60, 11, 64, 10, 56, 52, 13, 5, 15, 2, 29, 12, 55, 31, 18, 32, 22],
  ![18, 46, 4, 30, 64, 54, 46, 20, 46, 58, 64, 35, 35, 30, 0, 64, 65, 30, 0, 4, 54, 58, 4, 65, 35, 65, 54, 20, 18, 18, 20, 58],
  ![5, 33, 60, 29, 21, 6, 25, 20, 64, 2, 51, 52, 12, 11, 10, 50, 35, 15, 45, 43, 31, 36, 19, 55, 58, 32, 18, 13, 56, 61, 22, 17],
  ![62, 55, 33, 5, 18, 1, 39, 2, 44, 47, 15, 50, 60, 63, 52, 38, 61, 3, 19, 34, 14, 16, 4, 65, 28, 12, 56, 43, 35, 41, 26, 8],
  ![18, 31, 64, 59, 26, 27, 31, 42, 31, 7, 26, 4, 4, 59, 0, 26, 6, 59, 0, 64, 27, 7, 64, 6, 4, 6, 27, 42, 18, 18, 42, 7],
  ![38, 43, 20, 56, 45, 23, 34, 63, 36, 21, 27, 4, 44, 46, 51, 41, 6, 11, 62, 39, 31, 1, 54, 35, 65, 5, 59, 37, 25, 50, 13, 24],
  ![13, 65, 40, 5, 27, 39, 41, 33, 15, 54, 16, 35, 44, 43, 32, 11, 47, 6, 22, 28, 24, 10, 53, 19, 42, 55, 58, 51, 34, 7, 37, 57]
]

theorem diagonalResidueFormula_eq_matrix (row i : Fin 32) :
    (∑ j : VandiverFactorIndex67,
        (teichmullerRoot67 : ZMod 67) ^
            (67 ^ 2 - 2 * (i.val + 1) * j.val) *
          ((basicSymbolExponent67 row j).val : ZMod 67)) =
      diagonalResidueMatrix67 row i := by
  fin_cases row <;> fin_cases i <;> decide

theorem diagonalResidueMatrix_mul_inverse :
    diagonalResidueMatrix67 * diagonalResidueMatrixInverse67 = 1 := by
  decide

theorem diagonalResidueMatrix_det_ne_zero :
    diagonalResidueMatrix67.det ≠ 0 := by
  intro hzero
  have hdet := congrArg Matrix.det diagonalResidueMatrix_mul_inverse
  rw [Matrix.det_mul, hzero, zero_mul, Matrix.det_one] at hdet
  exact (by decide : (0 : ZMod 67) ≠ 1) hdet

@[simp]
theorem quotientResidueLinear_diagonalVandiverUnit67 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 67) (row i : Fin 32) :
    certificate67.quotientResidueLinear hzeta row
        (classOfUnit (diagonalVandiverUnit67 hzeta i)) =
      diagonalResidueMatrix67 row i := by
  rw [quotientResidueLinear_diagonalVandiverUnit67_formula]
  exact diagonalResidueFormula_eq_matrix row i

/-- The residue functionals realize the complete diagonal-unit matrix. -/
theorem evalMatrix_diagonalVandiverUnit67 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 67) :
    evalMatrix (classOfUnit ∘ diagonalVandiverUnit67 hzeta)
        (certificate67.residueFunctionals hzeta) =
      diagonalResidueMatrix67 := by
  ext row i
  exact quotientResidueLinear_diagonalVandiverUnit67 hzeta row i

/-- The actual diagonal units have full ambient unit index prime to `67`. -/
theorem not_dvd_diagonalVandiverUnit67_full_index {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 67) :
    ¬67 ∣ (Subgroup.closure (Set.range (diagonalVandiverUnit67 hzeta)) ⊔
      NumberField.Units.torsion K).index := by
  apply not_dvd_unitIndex_of_eval_det_ne_zero
    (certificate67.basisModTorsion (K := K))
      (diagonalVandiverUnit67 hzeta)
      (certificate67.residueFunctionals hzeta)
  rw [evalMatrix_diagonalVandiverUnit67]
  exact diagonalResidueMatrix_det_ne_zero

/-- The closure of Vandiver's diagonal family has finite index in the
ambient unit group. -/
theorem ambient_closure_finiteIndex {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 67) :
    (Subgroup.closure
      (Set.range (diagonalVandiverUnit67 hzeta))).FiniteIndex := by
  have hnot := not_dvd_diagonalVandiverUnit67_full_index hzeta
  have hsup :
      (Subgroup.closure (Set.range (diagonalVandiverUnit67 hzeta)) ⊔
        NumberField.Units.torsion K).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff]
    intro hzero
    apply hnot
    rw [hzero]
    exact dvd_zero 67
  exact (NumberField.Units.finiteIndex_iff_sup_torsion_finiteIndex
    (Subgroup.closure (Set.range (diagonalVandiverUnit67 hzeta)))).2 hsup

/-- The same family has finite-index closure in the real-unit subgroup,
the exact group used by Vandiver's Lemma II bridge. -/
theorem real_closure_finiteIndex {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 67) :
    (Subgroup.closure
      (Set.range (diagonalVandiverUnitFamily67 hzeta))).FiniteIndex := by
  letI :
      (Subgroup.closure (Set.range fun i : Fin 32 ↦
        ((diagonalVandiverUnitFamily67 hzeta i :
          NumberField.IsCMField.realUnits K) : (RingOfIntegers K)ˣ))).FiniteIndex := by
    simpa [diagonalVandiverUnitFamily67] using
      ambient_closure_finiteIndex hzeta
  exact Fermat.Irregular.VandiverFiniteIndex.closure_range_subtype
    (NumberField.IsCMField.realUnits K)
      (diagonalVandiverUnitFamily67 hzeta)

end

end Fermat.SixtySeven.VandiverDiagonalUnits
