import Fermat.Descent.KummerIso.UnitAdaptiveRelationHarness
import Fermat.Descent.Irregular.FiniteIndexLogTransform
import Fermat.Exponents.FourHundredNinetyOne.VandiverDiagonalUnits491

open scoped BigOperators NumberField

/-!
# A determinant-free finite-index proof for the diagonal units at 491

This module gives a second finite-index proof for the historical diagonal
Vandiver unit family. It normalizes the units along the Teichmüller orbit,
identifies their Dirichlet logarithms with a nonsingular integral Fourier
transform of canonical circular-unit logarithms, and transports Sinnott's
finite-index theorem through that transform.

The proof does not use the auxiliary-prime evaluation determinant. The
historical route remains available in `VandiverDiagonalUnits491`.
-/

namespace Fermat.FourHundredNinetyOne.VandiverDiagonalFiniteIndex

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open NumberField NumberField.Units
open Fermat.Irregular.CircularUnitFamily
open Fermat.FourHundredNinetyOne.VandiverDiagonalArithmetic
open Fermat.FourHundredNinetyOne.VandiverDiagonalUnitResidues
open Fermat.FourHundredNinetyOne.VandiverDiagonalUnits

local instance : Fact (Nat.Prime 491) := ⟨by norm_num⟩

theorem weightedTelescope244 {V : Type*} [AddCommGroup V]
    (w : Fin 245 → ℤ) (u : ℕ → V) :
    (∑ j : Fin 245, w j • (u (j.val + 1) - u j.val)) =
      (∑ ell : Fin 244,
        (w ell.castSucc - w ell.succ) • u (ell.val + 1)) +
        w (Fin.last 244) • u 245 - w 0 • u 0 := by
  simp_rw [smul_sub, sub_smul]
  rw [Finset.sum_sub_distrib]
  have hfirst :
      (∑ j : Fin 245, w j • u (j.val + 1)) =
        (∑ ell : Fin 244, w ell.castSucc • u (ell.val + 1)) +
          w (Fin.last 244) • u 245 := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
  have hsecond :
      (∑ j : Fin 245, w j • u j.val) =
        w 0 • u 0 +
          ∑ ell : Fin 244, w ell.succ • u (ell.val + 1) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ]
  rw [hfirst, hsecond]
  rw [show
      (∑ ell : Fin 244, w ell.castSucc • u (ell.val + 1)) +
            w (Fin.last 244) • u 245 -
          (w 0 • u 0 +
            ∑ ell : Fin 244, w ell.succ • u (ell.val + 1)) =
        ((∑ ell : Fin 244, w ell.castSucc • u (ell.val + 1)) -
          ∑ ell : Fin 244, w ell.succ • u (ell.val + 1)) +
            w (Fin.last 244) • u 245 - w 0 • u 0 by abel]
  rw [← Finset.sum_sub_distrib]

section Units491

variable {K : Type} [Field K]

/-- The canonical normalization at the literal orbit exponent `2512^j`. -/
def orbitUnit491 {zeta : K} (hzeta : IsPrimitiveRoot zeta 491)
    (j : ℕ) : (RingOfIntegers K)ˣ :=
  normalizedCircularUnit hzeta (by norm_num)
    ((by norm_num : Nat.Coprime 2512 491).pow_left j)
    (canonicalNormalizationExponent (p := 491) (2512 ^ j))

def canonicalNormalizedUnit491 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491) (a : ℕ) (ha : a.Coprime 491) :
    (RingOfIntegers K)ˣ :=
  normalizedCircularUnit hzeta (by norm_num) ha
    (canonicalNormalizationExponent (p := 491) a)

theorem canonicalNormalizedUnit491_eq_of_cast_eq
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 491)
    (a b : ℕ) (ha : a.Coprime 491) (hb : b.Coprime 491)
    (hab : (a : ZMod 491) = b) :
    canonicalNormalizedUnit491 hzeta a ha =
      canonicalNormalizedUnit491 hzeta b hb := by
  apply Units.ext
  apply RingOfIntegers.ext
  simp only [canonicalNormalizedUnit491]
  rw [normalizedCircularUnit_coe, normalizedCircularUnit_coe]
  have habMod : a ≡ b [MOD 491] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    exact hab
  have hpowAB : zeta ^ a = zeta ^ b :=
    pow_eq_pow_of_modEq habMod hzeta.pow_eq_one
  have he :
      (canonicalNormalizationExponent (p := 491) a : ZMod 491) =
        canonicalNormalizationExponent (p := 491) b := by
    simp only [canonicalNormalizationExponent, ZMod.natCast_zmod_val]
    rw [hab]
  have heMod :
      canonicalNormalizationExponent (p := 491) a ≡
        canonicalNormalizationExponent (p := 491) b [MOD 491] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    exact he
  rw [hpowAB, pow_eq_pow_of_modEq heMod hzeta.pow_eq_one]

theorem canonicalNormalizedUnit491_eq_neg_of_cast_eq_neg
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 491)
    (a b : ℕ) (ha : a.Coprime 491) (hb : b.Coprime 491)
    (hab : (a : ZMod 491) = -(b : ZMod 491)) :
    canonicalNormalizedUnit491 hzeta a ha =
      -canonicalNormalizedUnit491 hzeta b hb := by
  apply Units.ext
  apply RingOfIntegers.ext
  simp only [canonicalNormalizedUnit491, Units.val_neg, map_neg]
  rw [← RingOfIntegers.coe_eq_algebraMap]
  rw [normalizedCircularUnit_coe, normalizedCircularUnit_coe]
  have hbprim : IsPrimitiveRoot (zeta ^ b) 491 :=
    hzeta.pow_of_coprime b hb
  have hpowAB : zeta ^ a = (zeta ^ b)⁻¹ := by
    have habZero : a + b ≡ 0 [MOD 491] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      simpa only [Nat.cast_add, Nat.cast_zero,
        add_eq_zero_iff_eq_neg] using hab
    have hprod : zeta ^ a * zeta ^ b = 1 := by
      rw [← pow_add]
      simpa using pow_eq_pow_of_modEq habZero hzeta.pow_eq_one
    exact (mul_eq_one_iff_eq_inv₀
      (hbprim.ne_zero (by norm_num))).mp hprod
  have he :
      (canonicalNormalizationExponent (p := 491) a : ZMod 491) =
        canonicalNormalizationExponent (p := 491) b + b := by
    simp only [canonicalNormalizationExponent, ZMod.natCast_zmod_val]
    rw [hab]
    have htwo : (2 : ZMod 491) ≠ 0 := by decide
    field_simp
    ring
  have heMod :
      canonicalNormalizationExponent (p := 491) a ≡
        canonicalNormalizationExponent (p := 491) b + b [MOD 491] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simpa only [Nat.cast_add] using he
  have hpowE :
      zeta ^ canonicalNormalizationExponent (p := 491) a =
        zeta ^ canonicalNormalizationExponent (p := 491) b * zeta ^ b := by
    rw [← pow_add]
    exact pow_eq_pow_of_modEq heMod hzeta.pow_eq_one
  rw [hpowAB, hpowE]
  have hzb0 : zeta ^ b ≠ 0 := hbprim.ne_zero (by norm_num)
  have hz1 : 1 - zeta ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (hzeta.ne_one (by norm_num)))
  field_simp [hzb0, hz1]
  ring

theorem orbitNormalization_step (j : ℕ) :
    2512 ^ j * 463 +
        canonicalNormalizationExponent (p := 491) (2512 ^ j) ≡
      canonicalNormalizationExponent (p := 491) (2512 ^ (j + 1))
        [MOD 491] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
    canonicalNormalizationExponent, ZMod.natCast_zmod_val]
  have htwo : (2 : ZMod 491) ≠ 0 := by decide
  norm_num at ⊢
  field_simp
  have hc : (463 : ZMod 491) * 2 = 1 - 2512 := by decide
  calc
    (2512 : ZMod 491) ^ j * 463 * 2 +
          (1 - (2512 : ZMod 491) ^ j) =
        (2512 : ZMod 491) ^ j * (463 * 2) +
          (1 - (2512 : ZMod 491) ^ j) := by ring
    _ = (2512 : ZMod 491) ^ j * (1 - 2512) +
          (1 - (2512 : ZMod 491) ^ j) := by rw [hc]
    _ = 1 - (2512 : ZMod 491) ^ j * 2512 := by ring
    _ = 1 - (2512 : ZMod 491) ^ (j + 1) := by rw [pow_succ]

theorem basicVandiverUnit491_mul_orbitUnit491
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 491) (j : Fin 245) :
    basicVandiverUnit491 hzeta j * orbitUnit491 hzeta j.val =
      orbitUnit491 hzeta (j.val + 1) := by
  apply Units.ext
  apply RingOfIntegers.ext
  simp only [Units.val_mul, map_mul]
  rw [basicVandiverUnit491, orbitUnit491, orbitUnit491]
  simp only [← RingOfIntegers.coe_eq_algebraMap]
  rw [normalizedCircularUnit_coe, normalizedCircularUnit_coe,
    normalizedCircularUnit_coe]
  rw [show (zeta ^
      Fermat.FourHundredNinetyOne.VandiverDiagonalUnits.conjugateExponent491 j) ^ 2512 =
      zeta ^ (2512 ^ (j.val + 1)) by
    rw [← pow_mul]
    congr 1]
  rw [show zeta ^
      Fermat.FourHundredNinetyOne.VandiverDiagonalUnits.conjugateExponent491 j =
        zeta ^ (2512 ^ j.val) by
    rfl]
  have hpow :
      zeta ^ (2512 ^ j.val * 463 +
          canonicalNormalizationExponent (p := 491) (2512 ^ j.val)) =
        zeta ^ canonicalNormalizationExponent (p := 491)
          (2512 ^ (j.val + 1)) :=
    pow_eq_pow_of_modEq (orbitNormalization_step j.val) hzeta.pow_eq_one
  rw [pow_add] at hpow
  have hz1 : 1 - zeta ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (hzeta.ne_one (by norm_num)))
  have hzj : 1 - zeta ^ (2512 ^ j.val) ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm
      ((conjugate_isPrimitive hzeta j).ne_one (by norm_num)))
  rw [← pow_mul]
  field_simp [hz1, hzj]
  calc
    zeta ^ (2512 ^ j.val * 463) *
          (1 - zeta ^ 2512 ^ (j.val + 1)) *
          zeta ^ canonicalNormalizationExponent (p := 491) (2512 ^ j.val) =
        (1 - zeta ^ 2512 ^ (j.val + 1)) *
          (zeta ^ (2512 ^ j.val * 463) *
            zeta ^ canonicalNormalizationExponent (p := 491)
              (2512 ^ j.val)) := by ring
    _ = (1 - zeta ^ 2512 ^ (j.val + 1)) *
          zeta ^ canonicalNormalizationExponent (p := 491)
            (2512 ^ (j.val + 1)) := by rw [hpow]

theorem orbitUnit491_zero {zeta : K} (hzeta : IsPrimitiveRoot zeta 491) :
    orbitUnit491 hzeta 0 = 1 := by
  apply Units.ext
  apply RingOfIntegers.ext
  simp [orbitUnit491, normalizedCircularUnit_val,
    canonicalNormalizationExponent]

theorem orbitExponent_245_modEq_negOne :
    2512 ^ 245 ≡ 490 [MOD 491] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  decide

theorem orbitNormalization_245 :
    canonicalNormalizationExponent (p := 491) (2512 ^ 245) ≡ 1
      [MOD 491] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  simp only [canonicalNormalizationExponent, ZMod.natCast_zmod_val,
    Nat.cast_one]
  change (1 - (2512 : ZMod 491) ^ 245) / 2 = 1
  rw [show (2512 : ZMod 491) ^ 245 = 490 by decide]
  have htwo : (2 : ZMod 491) ≠ 0 := by decide
  field_simp
  decide

theorem orbitUnit491_245 {zeta : K} (hzeta : IsPrimitiveRoot zeta 491) :
    orbitUnit491 hzeta 245 = -1 := by
  apply Units.ext
  apply RingOfIntegers.ext
  change (((orbitUnit491 hzeta 245 : (RingOfIntegers K)ˣ) :
    RingOfIntegers K) : K) = ((-1 : (RingOfIntegers K)ˣ) : K)
  rw [orbitUnit491]
  rw [normalizedCircularUnit_coe]
  have hpowA : zeta ^ (2512 ^ 245) = zeta ^ 490 :=
    pow_eq_pow_of_modEq orbitExponent_245_modEq_negOne hzeta.pow_eq_one
  have hpowE :
      zeta ^ canonicalNormalizationExponent (p := 491) (2512 ^ 245) =
        zeta := by
    simpa using pow_eq_pow_of_modEq orbitNormalization_245 hzeta.pow_eq_one
  rw [hpowA, hpowE]
  have hzpow : zeta ^ 490 = zeta⁻¹ := by
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

theorem logEmbedding_basicVandiverUnit491
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 491) (j : Fin 245) :
    logEmbedding K (Additive.ofMul (basicVandiverUnit491 hzeta j)) =
      logEmbedding K (Additive.ofMul (orbitUnit491 hzeta (j.val + 1))) -
        logEmbedding K (Additive.ofMul (orbitUnit491 hzeta j.val)) := by
  have h := congrArg
    (fun u : (RingOfIntegers K)ˣ ↦ logEmbedding K (Additive.ofMul u))
    (basicVandiverUnit491_mul_orbitUnit491 hzeta j)
  have h' :
      logEmbedding K (Additive.ofMul (basicVandiverUnit491 hzeta j)) +
          logEmbedding K (Additive.ofMul (orbitUnit491 hzeta j.val)) =
        logEmbedding K (Additive.ofMul (orbitUnit491 hzeta (j.val + 1))) := by
    simpa only [ofMul_mul, map_add] using h
  exact eq_sub_of_add_eq h'

@[simp] theorem logEmbedding_orbitUnit491_zero
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 491) :
    logEmbedding K (Additive.ofMul (orbitUnit491 hzeta 0)) = 0 := by
  rw [orbitUnit491_zero hzeta]
  exact map_zero (logEmbedding K)

@[simp] theorem logEmbedding_orbitUnit491_245
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 491) :
    logEmbedding K (Additive.ofMul (orbitUnit491 hzeta 245)) = 0 := by
  rw [orbitUnit491_245 hzeta]
  have htors : (-1 : (RingOfIntegers K)ˣ) ∈ NumberField.Units.torsion K := by
    rw [NumberField.Units.torsion, CommGroup.mem_torsion,
      isOfFinOrder_iff_pow_eq_one]
    exact ⟨2, by norm_num, by norm_num⟩
  exact NumberField.Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff.mpr htors

omit [NumberField K] in
theorem orbitUnit491_eq_or_neg_circularCycle
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 491) (ell : Fin 244) :
    orbitUnit491 hzeta (ell.val + 1) =
        circularUnitFamily hzeta (by norm_num) (cycleColumn491 ell) ∨
      orbitUnit491 hzeta (ell.val + 1) =
        -circularUnitFamily hzeta (by norm_num) (cycleColumn491 ell) := by
  let a : ℕ := (cycleColumn491 ell).val + 2
  let b : ℕ := 2512 ^ (ell.val + 1)
  have ha0 : a ≠ 0 := by simp [a]
  have halt : a < 491 := by
    dsimp [a]
    have h := (cycleColumn491 ell).isLt
    omega
  have ha : a.Coprime 491 :=
    (Nat.coprime_of_lt_prime ha0 halt (by norm_num)).symm
  have hb : b.Coprime 491 :=
    (by norm_num : Nat.Coprime 2512 491).pow_left (ell.val + 1)
  have horbit :
      orbitUnit491 hzeta (ell.val + 1) =
        canonicalNormalizedUnit491 hzeta b hb := by
    rfl
  have hcycle :
      circularUnitFamily hzeta (by norm_num) (cycleColumn491 ell) =
        canonicalNormalizedUnit491 hzeta a ha := by
    rfl
  have hrep : (a : ZMod 491) = (b : ZMod 491) ∨
      (a : ZMod 491) = -(b : ZMod 491) := by
    simpa [a, b, teichmullerRoot491] using
      cycleColumn491_realRepresentative ell
  rcases hrep with hab | hab
  · left
    rw [horbit, hcycle]
    exact (canonicalNormalizedUnit491_eq_of_cast_eq
      hzeta a b ha hb hab).symm
  · right
    have hneg := canonicalNormalizedUnit491_eq_neg_of_cast_eq_neg
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

theorem logEmbedding_orbitUnit491_eq_circularCycle
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 491) (ell : Fin 244) :
    logEmbedding K
        (Additive.ofMul (orbitUnit491 hzeta (ell.val + 1))) =
      logEmbedding K (Additive.ofMul
        (circularUnitFamily hzeta (by norm_num) (cycleColumn491 ell))) := by
  rcases orbitUnit491_eq_or_neg_circularCycle hzeta ell with h | h
  · rw [h]
  · rw [h, logEmbedding_neg_unit]

/-- The literal integral Fourier/change-of-basis matrix. -/
def integerFourierChange491 : Matrix (Fin 244) (Fin 244) ℤ :=
  fun ell i ↦
    (diagonalWeight491 i ell.castSucc : ℤ) -
      (diagonalWeight491 i ell.succ : ℤ)

theorem logEmbedding_diagonalVandiverUnit491
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 491) (i : Fin 244) :
    logEmbedding K (Additive.ofMul (diagonalVandiverUnit491 hzeta i)) =
      ∑ ell : Fin 244, integerFourierChange491 ell i •
        logEmbedding K
          (Additive.ofMul (orbitUnit491 hzeta (ell.val + 1))) := by
  rw [diagonalVandiverUnit491]
  change logEmbedding K
      (Additive.ofMul
        (∏ j : Fin 245,
          basicVandiverUnit491 hzeta j ^ diagonalWeight491 i j)) = _
  simp only [ofMul_prod, map_sum]
  simp_rw [ofMul_pow, map_nsmul,
    logEmbedding_basicVandiverUnit491 hzeta]
  have ht := weightedTelescope244
    (fun j : Fin 245 ↦ (diagonalWeight491 i j : ℤ))
    (fun j : ℕ ↦ logEmbedding K (Additive.ofMul (orbitUnit491 hzeta j)))
  simpa only [integerFourierChange491,
    logEmbedding_orbitUnit491_zero hzeta,
    logEmbedding_orbitUnit491_245 hzeta, smul_zero, add_zero, sub_zero,
    Int.ofNat_eq_natCast, natCast_zsmul] using ht

theorem integerFourierChange491_cast_entry (ell i : Fin 244) :
    (Int.castRingHom (ZMod 491)) (integerFourierChange491 ell i) =
      fourierChange491 ell i := by
  rw [integerFourierChange491]
  calc
    (Int.castRingHom (ZMod 491))
          ((diagonalWeight491 i ell.castSucc : ℤ) -
            (diagonalWeight491 i ell.succ : ℤ)) =
        (diagonalWeight491 i ell.castSucc : ZMod 491) -
          (diagonalWeight491 i ell.succ : ZMod 491) := by simp
    _ = weightMod491 i ell.castSucc - weightMod491 i ell.succ := by
      rw [diagonalWeight491_cast, diagonalWeight491_cast]
    _ = fourierChange491 ell i :=
      weightMod491_castSucc_sub_succ ell i

theorem integerFourierChange491_map_zmod :
    (Int.castRingHom (ZMod 491)).mapMatrix integerFourierChange491 =
      fourierChange491 := by
  ext ell i
  exact integerFourierChange491_cast_entry ell i

theorem integerFourierChange491_det_ne_zero :
    integerFourierChange491.det ≠ 0 := by
  intro hzero
  have hdet := RingHom.map_det (Int.castRingHom (ZMod 491))
    integerFourierChange491
  rw [integerFourierChange491_map_zmod] at hdet
  rw [hzero, map_zero] at hdet
  exact fourierChange491_det_ne_zero hdet.symm

noncomputable def realFourierChange491 : Matrix (Fin 244) (Fin 244) ℝ :=
  (Int.castRingHom ℝ).mapMatrix integerFourierChange491

theorem realFourierChange491_det_ne_zero :
    realFourierChange491.det ≠ 0 := by
  have hdet := RingHom.map_det (Int.castRingHom ℝ)
    integerFourierChange491
  change (integerFourierChange491.det : ℝ) =
    realFourierChange491.det at hdet
  rw [← hdet]
  exact Int.cast_ne_zero.mpr integerFourierChange491_det_ne_zero

variable [NumberField.IsCMField K] [IsCyclotomicExtension {491} ℚ K]

theorem orbitLog491_linearIndependent
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 491) :
    LinearIndependent ℝ (fun ell : Fin 244 ↦
      logEmbedding K
        (Additive.ofMul (orbitUnit491 hzeta (ell.val + 1)))) := by
  have hfinite :=
    Fermat.KummerIso.UnitAdaptiveRelationHarness.ambient_closure_finiteIndex
      (p := 491) (K := K) (by norm_num) hzeta
  have hrank : NumberField.Units.rank K = 244 := by
    simpa using cyclotomicPrime_unitRank (K := K) (by norm_num : Nat.Prime 491)
      (by norm_num)
  let e : Fin (NumberField.Units.rank K) ≃ Fin 244 := finCongr hrank
  let baseRank : Fin (NumberField.Units.rank K) → (RingOfIntegers K)ˣ :=
    fun i ↦ circularUnitFamily hzeta (by norm_num) (e i)
  have hrange : Set.range baseRank =
      Set.range (circularUnitFamily hzeta (by norm_num)) := by
    ext u
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, by simp [baseRank]⟩
  have hbaseRankFinite :
      (Subgroup.closure (Set.range baseRank)).FiniteIndex := by
    rw [hrange]
    exact hfinite
  letI := hbaseRankFinite
  have hmax : NumberField.Units.IsMaxRank baseRank :=
    NumberField.Units.isMaxRank_iff_closure_finiteIndex.mpr hbaseRankFinite
  have hcanonical :
      LinearIndependent ℝ (fun i : Fin 244 ↦
        logEmbedding K (Additive.ofMul
          (circularUnitFamily hzeta (by norm_num) i))) := by
    have h := hmax.comp e.symm e.symm.injective
    convert h using 1
  have hcycle :
      LinearIndependent ℝ (fun ell : Fin 244 ↦
        logEmbedding K (Additive.ofMul
          (circularUnitFamily hzeta (by norm_num)
            (cycleColumn491 ell)))) :=
    hcanonical.comp cycleColumn491 cycleColumn491_bijective.injective
  have heq :
      (fun ell : Fin 244 ↦ logEmbedding K
          (Additive.ofMul (orbitUnit491 hzeta (ell.val + 1)))) =
        (fun ell : Fin 244 ↦ logEmbedding K (Additive.ofMul
          (circularUnitFamily hzeta (by norm_num)
            (cycleColumn491 ell)))) := by
    funext ell
    exact logEmbedding_orbitUnit491_eq_circularCycle hzeta ell
  rw [heq]
  exact hcycle

theorem orbit_closure_finiteIndex
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 491) :
    (Subgroup.closure (Set.range fun ell : Fin 244 ↦
      orbitUnit491 hzeta (ell.val + 1))).FiniteIndex := by
  have hrank : NumberField.Units.rank K = 244 := by
    simpa using cyclotomicPrime_unitRank (K := K) (by norm_num : Nat.Prime 491)
      (by norm_num)
  let e : Fin (NumberField.Units.rank K) ≃ Fin 244 := finCongr hrank
  let baseRank : Fin (NumberField.Units.rank K) → (RingOfIntegers K)ˣ :=
    fun i ↦ orbitUnit491 hzeta ((e i).val + 1)
  have hliRank : LinearIndependent ℝ (fun i ↦
      logEmbedding K (Additive.ofMul (baseRank i))) := by
    have h := (orbitLog491_linearIndependent hzeta).comp e e.injective
    convert h using 1
  have hfiniteRank :
      (Subgroup.closure (Set.range baseRank)).FiniteIndex :=
    NumberField.Units.isMaxRank_iff_closure_finiteIndex.mp hliRank
  have hrange : Set.range baseRank =
      Set.range (fun ell : Fin 244 ↦ orbitUnit491 hzeta (ell.val + 1)) := by
    ext u
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, by simp [baseRank]⟩
  rw [← hrange]
  exact hfiniteRank

theorem ambient_closure_finiteIndex_qfree_via_logTransform
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 491) :
    (Subgroup.closure
      (Set.range (diagonalVandiverUnit491 hzeta))).FiniteIndex := by
  have hrank : NumberField.Units.rank K = 244 := by
    simpa using cyclotomicPrime_unitRank (K := K) (by norm_num : Nat.Prime 491)
      (by norm_num)
  let e : Fin (NumberField.Units.rank K) ≃ Fin 244 := finCongr hrank
  let baseRank : Fin (NumberField.Units.rank K) → (RingOfIntegers K)ˣ :=
    fun j ↦ orbitUnit491 hzeta ((e j).val + 1)
  let targetRank : Fin (NumberField.Units.rank K) → (RingOfIntegers K)ˣ :=
    fun i ↦ diagonalVandiverUnit491 hzeta (e i)
  let A : Matrix (Fin (NumberField.Units.rank K))
      (Fin (NumberField.Units.rank K)) ℝ :=
    Matrix.reindex e.symm e.symm realFourierChange491
  have hbase :
      (Subgroup.closure (Set.range baseRank)).FiniteIndex := by
    have h := orbit_closure_finiteIndex hzeta
    have hrange : Set.range baseRank =
        Set.range (fun ell : Fin 244 ↦ orbitUnit491 hzeta (ell.val + 1)) := by
      ext u
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨e i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨e.symm i, by simp [baseRank]⟩
    rw [hrange]
    exact h
  letI := hbase
  have hdet : A.det ≠ 0 := by
    simp only [A, Matrix.det_reindex_self]
    exact realFourierChange491_det_ne_zero
  have hlog : ∀ i,
      logEmbedding K (Additive.ofMul (targetRank i)) =
        ∑ j, A j i • logEmbedding K (Additive.ofMul (baseRank j)) := by
    intro i
    change logEmbedding K
        (Additive.ofMul (diagonalVandiverUnit491 hzeta (e i))) = _
    rw [logEmbedding_diagonalVandiverUnit491]
    have hsum := (e.sum_comp (fun ell : Fin 244 ↦
      realFourierChange491 ell (e i) •
        logEmbedding K
          (Additive.ofMul (orbitUnit491 hzeta (ell.val + 1))))).symm
    calc
      _ = ∑ ell : Fin 244, realFourierChange491 ell (e i) •
          logEmbedding K
            (Additive.ofMul (orbitUnit491 hzeta (ell.val + 1))) := by
        apply Finset.sum_congr rfl
        intro ell _
        simp only [realFourierChange491, RingHom.mapMatrix_apply,
          Matrix.map_apply]
        exact (Int.cast_smul_eq_zsmul ℝ (integerFourierChange491 ell (e i))
          (logEmbedding K
            (Additive.ofMul (orbitUnit491 hzeta (ell.val + 1))))).symm
      _ = _ := by
        simpa only [A, baseRank, Matrix.reindex_apply,
          Matrix.submatrix_apply, Equiv.symm_symm,
          Equiv.apply_symm_apply] using hsum
  have hfiniteRank :=
    Fermat.Irregular.FiniteIndexLogTransform.closure_range_finiteIndex_of_log_transform
      baseRank targetRank A hdet hlog
  have hrange : Set.range targetRank =
      Set.range (diagonalVandiverUnit491 hzeta) := by
    ext u
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, by simp [targetRank]⟩
  rw [← hrange]
  exact hfiniteRank

theorem ambient_closure_finiteIndex_qfree
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 491) :
    (Subgroup.closure
      (Set.range (diagonalVandiverUnit491 hzeta))).FiniteIndex := by
  exact ambient_closure_finiteIndex_qfree_via_logTransform hzeta

theorem real_closure_finiteIndex_qfree
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 491) :
    (Subgroup.closure
      (Set.range (diagonalVandiverUnitFamily491 hzeta))).FiniteIndex := by
  letI :
      (Subgroup.closure (Set.range fun i : Fin 244 ↦
        ((diagonalVandiverUnitFamily491 hzeta i :
          NumberField.IsCMField.realUnits K) :
            (RingOfIntegers K)ˣ))).FiniteIndex := by
    simpa [diagonalVandiverUnitFamily491] using
      ambient_closure_finiteIndex_qfree hzeta
  exact Fermat.Irregular.VandiverFiniteIndex.closure_range_subtype
    (NumberField.IsCMField.realUnits K)
      (diagonalVandiverUnitFamily491 hzeta)

end Units491

end

end Fermat.FourHundredNinetyOne.VandiverDiagonalFiniteIndex
