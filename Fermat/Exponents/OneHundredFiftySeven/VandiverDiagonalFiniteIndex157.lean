import Fermat.Descent.Irregular.FiniteIndexLogTransform
import Fermat.Descent.KummerIso.UnitAdaptiveRelationHarness
import Fermat.Exponents.OneHundredFiftySeven.VandiverDiagonalUnits157

open scoped BigOperators NumberField

/-!
# A q-determinant-free finite-index proof for the diagonal units at 157

This module gives a second finite-index proof for the historical diagonal
Vandiver unit family. It normalizes the units along the Teichmüller orbit,
identifies their Dirichlet logarithms with a nonsingular integral Fourier
transform of canonical circular-unit logarithms, and transports Sinnott's
finite-index theorem through that transform.

The auxiliary-prime evaluation determinant is not used by this proof. The
historical route remains available in `VandiverDiagonalUnits157`.
-/

namespace Fermat.OneHundredFiftySeven.VandiverDiagonalFiniteIndex

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open NumberField NumberField.Units
open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.FiniteIndexLogTransform
open Fermat.OneHundredFiftySeven.VandiverDiagonalArithmetic
open Fermat.OneHundredFiftySeven.VandiverDiagonalUnitResidues
open Fermat.OneHundredFiftySeven.VandiverDiagonalUnits

local instance : Fact (Nat.Prime 157) := ⟨by norm_num⟩

theorem cycleColumn157_realRepresentative (ell : Fin 77) :
    let a := ((cycleColumn157 ell).val + 2 : ZMod 157)
    let d := (teichmullerRoot157 : ZMod 157) ^ (ell.val + 1)
    a = d ∨ a = -d := by
  decide +revert

theorem weightedTelescope77 {V : Type*} [AddCommGroup V]
    (w : Fin 78 → ℤ) (u : ℕ → V) :
    (∑ j : Fin 78, w j • (u (j.val + 1) - u j.val)) =
      (∑ ell : Fin 77,
        (w ell.castSucc - w ell.succ) • u (ell.val + 1)) +
        w (Fin.last 77) • u 78 - w 0 • u 0 := by
  simp_rw [smul_sub, sub_smul]
  rw [Finset.sum_sub_distrib]
  have hfirst :
      (∑ j : Fin 78, w j • u (j.val + 1)) =
        (∑ ell : Fin 77, w ell.castSucc • u (ell.val + 1)) +
          w (Fin.last 77) • u 78 := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
  have hsecond :
      (∑ j : Fin 78, w j • u j.val) =
        w 0 • u 0 +
          ∑ ell : Fin 77, w ell.succ • u (ell.val + 1) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ]
  rw [hfirst, hsecond]
  rw [show
      (∑ ell : Fin 77, w ell.castSucc • u (ell.val + 1)) +
            w (Fin.last 77) • u 78 -
          (w 0 • u 0 +
            ∑ ell : Fin 77, w ell.succ • u (ell.val + 1)) =
        ((∑ ell : Fin 77, w ell.castSucc • u (ell.val + 1)) -
          ∑ ell : Fin 77, w ell.succ • u (ell.val + 1)) +
            w (Fin.last 77) • u 78 - w 0 • u 0 by abel]
  rw [← Finset.sum_sub_distrib]

section Units157

variable {K : Type} [Field K]

/-- The canonical normalization at the literal orbit exponent `226^j`. -/
def orbitUnit157 {zeta : K} (hzeta : IsPrimitiveRoot zeta 157)
    (j : ℕ) : (RingOfIntegers K)ˣ :=
  normalizedCircularUnit hzeta (by norm_num)
    ((by norm_num : Nat.Coprime 226 157).pow_left j)
    (canonicalNormalizationExponent (p := 157) (226 ^ j))

def canonicalNormalizedUnit157 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 157) (a : ℕ) (ha : a.Coprime 157) :
    (RingOfIntegers K)ˣ :=
  normalizedCircularUnit hzeta (by norm_num) ha
    (canonicalNormalizationExponent (p := 157) a)

theorem canonicalNormalizedUnit157_eq_of_cast_eq
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 157)
    (a b : ℕ) (ha : a.Coprime 157) (hb : b.Coprime 157)
    (hab : (a : ZMod 157) = b) :
    canonicalNormalizedUnit157 hzeta a ha =
      canonicalNormalizedUnit157 hzeta b hb := by
  apply Units.ext
  apply RingOfIntegers.ext
  simp only [canonicalNormalizedUnit157]
  rw [normalizedCircularUnit_coe, normalizedCircularUnit_coe]
  have habMod : a ≡ b [MOD 157] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    exact hab
  have hpowAB : zeta ^ a = zeta ^ b :=
    pow_eq_pow_of_modEq habMod hzeta.pow_eq_one
  have he :
      (canonicalNormalizationExponent (p := 157) a : ZMod 157) =
        canonicalNormalizationExponent (p := 157) b := by
    simp only [canonicalNormalizationExponent, ZMod.natCast_zmod_val]
    rw [hab]
  have heMod :
      canonicalNormalizationExponent (p := 157) a ≡
        canonicalNormalizationExponent (p := 157) b [MOD 157] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    exact he
  rw [hpowAB, pow_eq_pow_of_modEq heMod hzeta.pow_eq_one]

theorem canonicalNormalizedUnit157_eq_neg_of_cast_eq_neg
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 157)
    (a b : ℕ) (ha : a.Coprime 157) (hb : b.Coprime 157)
    (hab : (a : ZMod 157) = -(b : ZMod 157)) :
    canonicalNormalizedUnit157 hzeta a ha =
      -canonicalNormalizedUnit157 hzeta b hb := by
  apply Units.ext
  apply RingOfIntegers.ext
  simp only [canonicalNormalizedUnit157, Units.val_neg, map_neg]
  rw [← RingOfIntegers.coe_eq_algebraMap]
  rw [normalizedCircularUnit_coe, normalizedCircularUnit_coe]
  have hbprim : IsPrimitiveRoot (zeta ^ b) 157 :=
    hzeta.pow_of_coprime b hb
  have hpowAB : zeta ^ a = (zeta ^ b)⁻¹ := by
    have habZero : a + b ≡ 0 [MOD 157] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      simpa only [Nat.cast_add, Nat.cast_zero,
        add_eq_zero_iff_eq_neg] using hab
    have hprod : zeta ^ a * zeta ^ b = 1 := by
      rw [← pow_add]
      simpa using pow_eq_pow_of_modEq habZero hzeta.pow_eq_one
    exact (mul_eq_one_iff_eq_inv₀
      (hbprim.ne_zero (by norm_num))).mp hprod
  have he :
      (canonicalNormalizationExponent (p := 157) a : ZMod 157) =
        canonicalNormalizationExponent (p := 157) b + b := by
    simp only [canonicalNormalizationExponent, ZMod.natCast_zmod_val]
    rw [hab]
    have htwo : (2 : ZMod 157) ≠ 0 := by decide
    field_simp
    ring
  have heMod :
      canonicalNormalizationExponent (p := 157) a ≡
        canonicalNormalizationExponent (p := 157) b + b [MOD 157] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simpa only [Nat.cast_add] using he
  have hpowE :
      zeta ^ canonicalNormalizationExponent (p := 157) a =
        zeta ^ canonicalNormalizationExponent (p := 157) b * zeta ^ b := by
    rw [← pow_add]
    exact pow_eq_pow_of_modEq heMod hzeta.pow_eq_one
  rw [hpowAB, hpowE]
  have hzb0 : zeta ^ b ≠ 0 := hbprim.ne_zero (by norm_num)
  have hz1 : 1 - zeta ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (hzeta.ne_one (by norm_num)))
  field_simp [hzb0, hz1]
  ring

theorem orbitNormalization_step (j : ℕ) :
    226 ^ j * 123 +
        canonicalNormalizationExponent (p := 157) (226 ^ j) ≡
      canonicalNormalizationExponent (p := 157) (226 ^ (j + 1))
        [MOD 157] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
    canonicalNormalizationExponent, ZMod.natCast_zmod_val]
  have htwo : (2 : ZMod 157) ≠ 0 := by decide
  norm_num at ⊢
  field_simp
  have hc : (123 : ZMod 157) * 2 = 1 - 226 := by decide
  calc
    (226 : ZMod 157) ^ j * 123 * 2 +
          (1 - (226 : ZMod 157) ^ j) =
        (226 : ZMod 157) ^ j * (123 * 2) +
          (1 - (226 : ZMod 157) ^ j) := by ring
    _ = (226 : ZMod 157) ^ j * (1 - 226) +
          (1 - (226 : ZMod 157) ^ j) := by rw [hc]
    _ = 1 - (226 : ZMod 157) ^ j * 226 := by ring
    _ = 1 - (226 : ZMod 157) ^ (j + 1) := by rw [pow_succ]

theorem basicVandiverUnit157_mul_orbitUnit157
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 157) (j : Fin 78) :
    basicVandiverUnit157 hzeta j * orbitUnit157 hzeta j.val =
      orbitUnit157 hzeta (j.val + 1) := by
  apply Units.ext
  apply RingOfIntegers.ext
  simp only [Units.val_mul, map_mul]
  rw [basicVandiverUnit157, orbitUnit157, orbitUnit157]
  simp only [← RingOfIntegers.coe_eq_algebraMap]
  rw [normalizedCircularUnit_coe, normalizedCircularUnit_coe,
    normalizedCircularUnit_coe]
  have hconj :
      Fermat.OneHundredFiftySeven.VandiverDiagonalUnits.conjugateExponent157 j =
        226 ^ j.val := rfl
  rw [hconj]
  rw [show (zeta ^
      (226 ^ j.val)) ^ 226 =
      zeta ^ (226 ^ (j.val + 1)) by
    rw [← pow_mul]
    congr 1]
  have hpow :
      zeta ^ (226 ^ j.val * 123 +
          canonicalNormalizationExponent (p := 157) (226 ^ j.val)) =
        zeta ^ canonicalNormalizationExponent (p := 157)
          (226 ^ (j.val + 1)) :=
    pow_eq_pow_of_modEq (orbitNormalization_step j.val) hzeta.pow_eq_one
  rw [pow_add] at hpow
  have hz1 : 1 - zeta ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (hzeta.ne_one (by norm_num)))
  have hzj : 1 - zeta ^ (226 ^ j.val) ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm
      ((conjugate_isPrimitive hzeta j).ne_one (by norm_num)))
  rw [← pow_mul]
  field_simp [hz1, hzj]
  calc
    zeta ^ (226 ^ j.val * 123) *
          (1 - zeta ^ 226 ^ (j.val + 1)) *
          zeta ^ canonicalNormalizationExponent (p := 157) (226 ^ j.val) =
        (1 - zeta ^ 226 ^ (j.val + 1)) *
          (zeta ^ (226 ^ j.val * 123) *
            zeta ^ canonicalNormalizationExponent (p := 157)
              (226 ^ j.val)) := by ring
    _ = (1 - zeta ^ 226 ^ (j.val + 1)) *
          zeta ^ canonicalNormalizationExponent (p := 157)
            (226 ^ (j.val + 1)) := by rw [hpow]

theorem orbitUnit157_zero {zeta : K} (hzeta : IsPrimitiveRoot zeta 157) :
    orbitUnit157 hzeta 0 = 1 := by
  apply Units.ext
  apply RingOfIntegers.ext
  simp [orbitUnit157, normalizedCircularUnit_val,
    canonicalNormalizationExponent]

theorem orbitExponent_78_modEq_negOne :
    226 ^ 78 ≡ 156 [MOD 157] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  decide

theorem orbitNormalization_78 :
    canonicalNormalizationExponent (p := 157) (226 ^ 78) ≡ 1
      [MOD 157] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  simp only [canonicalNormalizationExponent, ZMod.natCast_zmod_val,
    Nat.cast_one]
  change (1 - (226 : ZMod 157) ^ 78) / 2 = 1
  rw [show (226 : ZMod 157) ^ 78 = 156 by decide]
  have htwo : (2 : ZMod 157) ≠ 0 := by decide
  field_simp
  decide

theorem orbitUnit157_78 {zeta : K} (hzeta : IsPrimitiveRoot zeta 157) :
    orbitUnit157 hzeta 78 = -1 := by
  apply Units.ext
  apply RingOfIntegers.ext
  change (((orbitUnit157 hzeta 78 : (RingOfIntegers K)ˣ) :
    RingOfIntegers K) : K) = ((-1 : (RingOfIntegers K)ˣ) : K)
  rw [orbitUnit157]
  rw [normalizedCircularUnit_coe]
  have hpowA : zeta ^ (226 ^ 78) = zeta ^ 156 :=
    pow_eq_pow_of_modEq orbitExponent_78_modEq_negOne hzeta.pow_eq_one
  have hpowE :
      zeta ^ canonicalNormalizationExponent (p := 157) (226 ^ 78) =
        zeta := by
    simpa using pow_eq_pow_of_modEq orbitNormalization_78 hzeta.pow_eq_one
  rw [hpowA, hpowE]
  have hzpow : zeta ^ 156 = zeta⁻¹ := by
    apply (mul_eq_one_iff_eq_inv₀ (hzeta.ne_zero (by norm_num))).mp
    rw [← pow_succ]
    simpa using hzeta.pow_eq_one
  rw [hzpow]
  have hz0 : zeta ≠ 0 := hzeta.ne_zero (by norm_num)
  have hz1 : 1 - zeta ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (hzeta.ne_one (by norm_num)))
  simp only [Units.val_neg, Units.val_one, map_neg, map_one]
  field_simp [hz0, hz1]
  ring

variable [NumberField K]

theorem logEmbedding_basicVandiverUnit157
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 157) (j : Fin 78) :
    logEmbedding K (Additive.ofMul (basicVandiverUnit157 hzeta j)) =
      logEmbedding K (Additive.ofMul (orbitUnit157 hzeta (j.val + 1))) -
        logEmbedding K (Additive.ofMul (orbitUnit157 hzeta j.val)) := by
  have h := congrArg
    (fun u : (RingOfIntegers K)ˣ ↦ logEmbedding K (Additive.ofMul u))
    (basicVandiverUnit157_mul_orbitUnit157 hzeta j)
  have h' :
      logEmbedding K (Additive.ofMul (basicVandiverUnit157 hzeta j)) +
          logEmbedding K (Additive.ofMul (orbitUnit157 hzeta j.val)) =
        logEmbedding K (Additive.ofMul (orbitUnit157 hzeta (j.val + 1))) := by
    simpa only [ofMul_mul, map_add] using h
  exact eq_sub_of_add_eq h'

@[simp] theorem logEmbedding_orbitUnit157_zero
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 157) :
    logEmbedding K (Additive.ofMul (orbitUnit157 hzeta 0)) = 0 := by
  rw [orbitUnit157_zero hzeta]
  exact map_zero (logEmbedding K)

@[simp] theorem logEmbedding_orbitUnit157_78
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 157) :
    logEmbedding K (Additive.ofMul (orbitUnit157 hzeta 78)) = 0 := by
  rw [orbitUnit157_78 hzeta]
  have htors : (-1 : (RingOfIntegers K)ˣ) ∈ NumberField.Units.torsion K := by
    rw [NumberField.Units.torsion, CommGroup.mem_torsion,
      isOfFinOrder_iff_pow_eq_one]
    exact ⟨2, by norm_num, by norm_num⟩
  exact NumberField.Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff.mpr htors

omit [NumberField K] in
theorem orbitUnit157_eq_or_neg_circularCycle
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 157) (ell : Fin 77) :
    orbitUnit157 hzeta (ell.val + 1) =
        circularUnitFamily hzeta (by norm_num) (cycleColumn157 ell) ∨
      orbitUnit157 hzeta (ell.val + 1) =
        -circularUnitFamily hzeta (by norm_num) (cycleColumn157 ell) := by
  let a : ℕ := (cycleColumn157 ell).val + 2
  let b : ℕ := 226 ^ (ell.val + 1)
  have ha0 : a ≠ 0 := by simp [a]
  have halt : a < 157 := by
    dsimp [a]
    have h := (cycleColumn157 ell).isLt
    omega
  have ha : a.Coprime 157 :=
    (Nat.coprime_of_lt_prime ha0 halt (by norm_num)).symm
  have hb : b.Coprime 157 :=
    (by norm_num : Nat.Coprime 226 157).pow_left (ell.val + 1)
  have horbit :
      orbitUnit157 hzeta (ell.val + 1) =
        canonicalNormalizedUnit157 hzeta b hb := by
    rfl
  have hcycle :
      circularUnitFamily hzeta (by norm_num) (cycleColumn157 ell) =
        canonicalNormalizedUnit157 hzeta a ha := by
    rfl
  have hrep : (a : ZMod 157) = (b : ZMod 157) ∨
      (a : ZMod 157) = -(b : ZMod 157) := by
    simpa [a, b, teichmullerRoot157] using
      cycleColumn157_realRepresentative ell
  rcases hrep with hab | hab
  · left
    rw [horbit, hcycle]
    exact (canonicalNormalizedUnit157_eq_of_cast_eq
      hzeta a b ha hb hab).symm
  · right
    have hneg := canonicalNormalizedUnit157_eq_neg_of_cast_eq_neg
      hzeta a b ha hb hab
    rw [horbit, hcycle, hneg]
    simp

theorem logEmbedding_neg_unit (u : (RingOfIntegers K)ˣ) :
    logEmbedding K (Additive.ofMul (-u)) =
      logEmbedding K (Additive.ofMul u) := by
  have htors : (-1 : (RingOfIntegers K)ˣ) ∈ NumberField.Units.torsion K := by
    rw [NumberField.Units.torsion, CommGroup.mem_torsion,
      isOfFinOrder_iff_pow_eq_one]
    exact ⟨2, by norm_num, by norm_num⟩
  have hzero : logEmbedding K (Additive.ofMul (-1 : (RingOfIntegers K)ˣ)) = 0 :=
    NumberField.Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff.mpr htors
  rw [show -u = (-1 : (RingOfIntegers K)ˣ) * u by simp]
  simp only [ofMul_mul, map_add, hzero, zero_add]

theorem logEmbedding_orbitUnit157_eq_circularCycle
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 157) (ell : Fin 77) :
    logEmbedding K
        (Additive.ofMul (orbitUnit157 hzeta (ell.val + 1))) =
      logEmbedding K (Additive.ofMul
        (circularUnitFamily hzeta (by norm_num) (cycleColumn157 ell))) := by
  rcases orbitUnit157_eq_or_neg_circularCycle hzeta ell with h | h
  · rw [h]
  · rw [h, logEmbedding_neg_unit]

/-- The literal integral Fourier/change-of-basis matrix. -/
def integerFourierChange157 : Matrix (Fin 77) (Fin 77) ℤ :=
  fun ell i ↦
    (diagonalWeight157 i ell.castSucc : ℤ) -
      (diagonalWeight157 i ell.succ : ℤ)

theorem integerFourierChange157_mod :
    integerFourierChange157.map (Int.castRingHom (ZMod 157)) =
      fourierChange157 := by
  ext ell i
  simp only [integerFourierChange157, Matrix.map_apply, map_sub]
  change (diagonalWeight157 i ell.castSucc : ZMod 157) -
      (diagonalWeight157 i ell.succ : ZMod 157) =
    fourierChange157 ell i
  rw [diagonalWeight157_cast, diagonalWeight157_cast]
  exact weightMod157_castSucc_sub_succ ell i

theorem integerFourierChange157_det_ne_zero :
    integerFourierChange157.det ≠ 0 := by
  intro hzero
  have hcast :
      ((integerFourierChange157.det : ℤ) : ZMod 157) = 0 := by
    rw [hzero]
    simp
  have hmapdet :
      (integerFourierChange157.map
        (Int.castRingHom (ZMod 157))).det = 0 := by
    calc
      _ = (Int.castRingHom (ZMod 157)) integerFourierChange157.det :=
        ((Int.castRingHom (ZMod 157)).map_det
          integerFourierChange157).symm
      _ = 0 := hcast
  rw [integerFourierChange157_mod] at hmapdet
  exact fourierChange157_det_ne_zero hmapdet

def realFourierChange157 : Matrix (Fin 77) (Fin 77) ℝ :=
  integerFourierChange157.map (Int.castRingHom ℝ)

theorem realFourierChange157_det_ne_zero :
    realFourierChange157.det ≠ 0 := by
  intro hzero
  have hcast : ((integerFourierChange157.det : ℤ) : ℝ) = 0 := by
    calc
      _ = realFourierChange157.det := by
        exact (Int.castRingHom ℝ).map_det integerFourierChange157
      _ = 0 := hzero
  have hint : integerFourierChange157.det = 0 := by
    exact_mod_cast hcast
  exact integerFourierChange157_det_ne_zero hint

theorem logEmbedding_diagonalVandiverUnit157
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 157) (i : Fin 77) :
    logEmbedding K (Additive.ofMul (diagonalVandiverUnit157 hzeta i)) =
      ∑ ell : Fin 77, integerFourierChange157 ell i •
        logEmbedding K
          (Additive.ofMul (orbitUnit157 hzeta (ell.val + 1))) := by
  rw [diagonalVandiverUnit157]
  simp only [ofMul_prod, map_sum]
  simp_rw [ofMul_pow, map_nsmul,
    logEmbedding_basicVandiverUnit157 hzeta]
  have ht := weightedTelescope77
    (fun j : Fin 78 ↦ (diagonalWeight157 i j : ℤ))
    (fun j : ℕ ↦ logEmbedding K (Additive.ofMul (orbitUnit157 hzeta j)))
  simpa only [integerFourierChange157,
    logEmbedding_orbitUnit157_zero hzeta,
    logEmbedding_orbitUnit157_78 hzeta, smul_zero, add_zero, sub_zero,
    Int.ofNat_eq_natCast, natCast_zsmul] using ht

theorem logEmbedding_diagonalVandiverUnit157_real
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 157) (i : Fin 77) :
    logEmbedding K (Additive.ofMul (diagonalVandiverUnit157 hzeta i)) =
      ∑ ell : Fin 77, realFourierChange157 ell i •
        logEmbedding K
          (Additive.ofMul (orbitUnit157 hzeta (ell.val + 1))) := by
  rw [logEmbedding_diagonalVandiverUnit157 hzeta i]
  apply Finset.sum_congr rfl
  intro ell _
  simp only [realFourierChange157, Matrix.map_apply]
  exact (Int.cast_smul_eq_zsmul ℝ (integerFourierChange157 ell i)
    (logEmbedding K
      (Additive.ofMul (orbitUnit157 hzeta (ell.val + 1))))).symm

/-- Determinant-free finite index for the literal diagonal family at 157.

The only finite-index input is the generic Sinnott theorem for the canonical
circular-unit family. The mod-157 Fourier calculation is used only to prove
that the integral logarithmic change of basis is nonsingular over the reals. -/
theorem ambient_closure_finiteIndex_qfree
    [IsCyclotomicExtension {157} ℚ K] [NumberField.IsCMField K]
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 157) :
    (Subgroup.closure
      (Set.range (diagonalVandiverUnit157 hzeta))).FiniteIndex := by
  let base : Fin 77 → (RingOfIntegers K)ˣ :=
    fun ell ↦ circularUnitFamily hzeta (by norm_num) (cycleColumn157 ell)
  let target : Fin 77 → (RingOfIntegers K)ˣ :=
    diagonalVandiverUnit157 hzeta
  have hrange :
      Set.range base =
        Set.range (circularUnitFamily hzeta (by norm_num)) := by
    ext u
    constructor
    · rintro ⟨ell, rfl⟩
      exact ⟨cycleColumn157 ell, rfl⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨ell, hell⟩ := cycleColumn157_bijective.2 i
      exact ⟨ell, by simp only [base, hell]⟩
  letI : (Subgroup.closure (Set.range base)).FiniteIndex := by
    rw [hrange]
    exact
      Fermat.KummerIso.UnitAdaptiveRelationHarness.ambient_closure_finiteIndex
        (p := 157) (by norm_num) hzeta
  have hlog : ∀ i,
      logEmbedding K (Additive.ofMul (target i)) =
        ∑ ell, realFourierChange157 ell i •
          logEmbedding K (Additive.ofMul (base ell)) := by
    intro i
    dsimp only [target, base]
    rw [logEmbedding_diagonalVandiverUnit157_real hzeta i]
    apply Finset.sum_congr rfl
    intro ell _
    rw [logEmbedding_orbitUnit157_eq_circularCycle hzeta ell]
  have hrank : NumberField.Units.rank K = 77 := by
    simpa using
      (cyclotomicPrime_unitRank (K := K)
        (by norm_num : Nat.Prime 157) (by norm_num : 157 ≠ 2))
  have htransport :=
    @closure_range_finiteIndex_of_log_transform K _ _
  rw [hrank] at htransport
  exact htransport base target realFourierChange157
    realFourierChange157_det_ne_zero hlog

theorem real_closure_finiteIndex_qfree
    [IsCyclotomicExtension {157} ℚ K] [NumberField.IsCMField K]
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 157) :
    (Subgroup.closure
      (Set.range (diagonalVandiverUnitFamily157 hzeta))).FiniteIndex := by
  letI :
      (Subgroup.closure (Set.range fun i : Fin 77 ↦
        ((diagonalVandiverUnitFamily157 hzeta i :
          NumberField.IsCMField.realUnits K) :
            (RingOfIntegers K)ˣ))).FiniteIndex := by
    simpa only [diagonalVandiverUnitFamily157_coe] using
      ambient_closure_finiteIndex_qfree hzeta
  exact Fermat.Irregular.VandiverFiniteIndex.closure_range_subtype
    (NumberField.IsCMField.realUnits K)
      (diagonalVandiverUnitFamily157 hzeta)

end Units157

end

end Fermat.OneHundredFiftySeven.VandiverDiagonalFiniteIndex
