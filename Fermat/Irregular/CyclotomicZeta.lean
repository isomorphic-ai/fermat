import Fermat.Irregular.SinnottIndex
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The explicit circular-unit regulator at exponent 37

This file reduces the remaining exponent-`37` Sinnott--Kummer identity to an explicit
logarithmic determinant.  Under a complex embedding, the root-of-unity normalization in each
circular unit has norm one, leaving the familiar quotient

`|1 - sigma(zeta)^a| / |1 - sigma(zeta)|`.

Mathlib's regulator determinant formula then identifies the circular-unit regulator with the
absolute determinant of the resulting `17 x 17` matrix.  What remains beyond this file is the
analytic evaluation of the maximal-real cyclotomic Dedekind-zeta residue by that determinant.
-/

open scoped NumberField

namespace Fermat.Irregular.CyclotomicZeta

noncomputable section

open scoped Classical

open NumberField NumberField.Units
open Fermat.Irregular.CircularUnitIndex
open Fermat.Irregular.SinnottIndex

variable {K : Type*} [Field K] [NumberField K]

/-- The absolute value of a circular unit at an infinite place is the quotient of the two
cyclotomic chord lengths.  In particular, the normalization power of `zeta` contributes no
factor to the logarithmic embedding. -/
theorem infinitePlace_circularUnit37 {zeta : K} (hzeta : IsPrimitiveRoot zeta 37)
    (w : NumberField.InfinitePlace K) (i : Fin 17) :
    w (((circularUnit37 hzeta i).val : NumberField.RingOfIntegers K) : K) =
      ‖1 - (w.embedding zeta) ^ (i.val + 2)‖ / ‖1 - w.embedding zeta‖ := by
  rw [← NumberField.InfinitePlace.norm_embedding_eq]
  rw [circularUnit37_coe]
  simp only [map_mul, map_div₀, map_pow, map_sub, map_one, norm_mul, norm_div, norm_pow]
  have hnorm : ‖w.embedding zeta‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one
      ((hzeta.map_of_injective w.embedding.injective).pow_eq_one) (by norm_num)
  rw [hnorm, one_pow, one_mul]

/-- A chord cut out by the point `exp (2 pi i x)` on the unit circle has length
`2 |sin (pi x)|`. -/
theorem norm_one_sub_exp_two_pi_I (x : ℝ) :
    ‖1 - Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))‖ =
      2 * |Real.sin (Real.pi * x)| := by
  rw [show 1 - Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) =
      -(Complex.exp (Complex.I * (2 * Real.pi * x : ℝ)) - 1) by
    have harg : 2 * Real.pi * Complex.I * (x : ℂ) =
        Complex.I * (2 * Real.pi * x : ℝ) := by
      push_cast
      ring
    rw [harg]
    ring]
  rw [norm_neg, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show 2 * Real.pi * x / 2 = Real.pi * x by ring]
  norm_num [Real.norm_eq_abs]

/-- The chord formula after raising a standard complex root of unity to a natural power. -/
theorem norm_one_sub_exp_two_pi_I_pow (k a n : ℕ) :
    ‖1 - Complex.exp
        (2 * Real.pi * Complex.I * ((k : ℂ) / (n : ℂ))) ^ a‖ =
      2 * |Real.sin (Real.pi * ((a : ℝ) * (k : ℝ) / (n : ℝ)))| := by
  rw [← Complex.exp_nat_mul]
  rw [show (a : ℂ) * (2 * Real.pi * Complex.I * ((k : ℂ) / (n : ℂ))) =
      2 * Real.pi * Complex.I *
        (((a : ℝ) * (k : ℝ) / (n : ℝ) : ℝ) : ℂ) by
    push_cast
    ring]
  exact norm_one_sub_exp_two_pi_I _

omit [NumberField K] in
private theorem exists_infinitePlaceExponent37 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) (w : NumberField.InfinitePlace K) :
    ∃ k : ℕ, k < 37 ∧ k.Coprime 37 ∧
      Complex.exp (2 * Real.pi * Complex.I * ((k : ℂ) / ((37 : ℕ) : ℂ))) =
        w.embedding zeta := by
  obtain ⟨k, hklt, hkcop, hk⟩ := (Complex.isPrimitiveRoot_iff _ 37 (by norm_num)).mp
    (hzeta.map_of_injective w.embedding.injective)
  exact ⟨k, hklt, hkcop, hk⟩

/-- The exponent `1 <= k <= 36` through which the chosen representative embedding of an
infinite place sends a primitive `37`th root of unity. -/
def infinitePlaceExponent37 {zeta : K} (hzeta : IsPrimitiveRoot zeta 37)
    (w : NumberField.InfinitePlace K) : ℕ :=
  (exists_infinitePlaceExponent37 hzeta w).choose

omit [NumberField K] in
theorem infinitePlaceExponent37_lt {zeta : K} (hzeta : IsPrimitiveRoot zeta 37)
    (w : NumberField.InfinitePlace K) : infinitePlaceExponent37 hzeta w < 37 :=
  (exists_infinitePlaceExponent37 hzeta w).choose_spec.1

omit [NumberField K] in
theorem infinitePlaceExponent37_coprime {zeta : K} (hzeta : IsPrimitiveRoot zeta 37)
    (w : NumberField.InfinitePlace K) : (infinitePlaceExponent37 hzeta w).Coprime 37 :=
  (exists_infinitePlaceExponent37 hzeta w).choose_spec.2.1

omit [NumberField K] in
theorem infinitePlaceExponent37_pos {zeta : K} (hzeta : IsPrimitiveRoot zeta 37)
    (w : NumberField.InfinitePlace K) : 0 < infinitePlaceExponent37 hzeta w := by
  have hne : infinitePlaceExponent37 hzeta w ≠ 0 := by
    intro hk
    have hcop := infinitePlaceExponent37_coprime hzeta w
    simp [hk] at hcop
  omega

omit [NumberField K] in
theorem infinitePlaceExponent37_image {zeta : K} (hzeta : IsPrimitiveRoot zeta 37)
    (w : NumberField.InfinitePlace K) :
    Complex.exp (2 * Real.pi * Complex.I *
        ((infinitePlaceExponent37 hzeta w : ℂ) / ((37 : ℕ) : ℂ))) =
      w.embedding zeta :=
  (exists_infinitePlaceExponent37 hzeta w).choose_spec.2.2

/-- At every infinite place, a circular unit is an explicit quotient of two sine values at
rational multiples of `pi`. -/
theorem infinitePlace_circularUnit37_eq_sineRatio {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) (w : NumberField.InfinitePlace K) (i : Fin 17) :
    w (((circularUnit37 hzeta i).val : NumberField.RingOfIntegers K) : K) =
      |Real.sin (Real.pi *
          (((i.val + 2 : ℕ) : ℝ) * (infinitePlaceExponent37 hzeta w : ℝ) /
            ((37 : ℕ) : ℝ)))| /
        |Real.sin (Real.pi *
          ((infinitePlaceExponent37 hzeta w : ℝ) / ((37 : ℕ) : ℝ)))| := by
  rw [infinitePlace_circularUnit37 hzeta, ← infinitePlaceExponent37_image hzeta w]
  rw [norm_one_sub_exp_two_pi_I_pow]
  have hden :
      ‖1 - Complex.exp (2 * Real.pi * Complex.I *
        ((infinitePlaceExponent37 hzeta w : ℂ) / ((37 : ℕ) : ℂ)))‖ =
        2 * |Real.sin (Real.pi *
          ((infinitePlaceExponent37 hzeta w : ℝ) / (37 : ℝ)))| := by
    simpa using norm_one_sub_exp_two_pi_I_pow
      (infinitePlaceExponent37 hzeta w) 1 37
  rw [hden]
  field_simp
  norm_num

/-- The explicit logarithmic matrix of the seventeen exponent-`37` circular units.  Its rows
are indexed by the units `a = 2, ..., 18`; its columns are all infinite places except one.
The equivalence `e` only chooses an ordering for those rows. -/
def circularLogMatrix37 (zeta : K)
    (w₀ : NumberField.InfinitePlace K)
    (e : {w : NumberField.InfinitePlace K // w ≠ w₀} ≃ Fin 17) :
    Matrix {w : NumberField.InfinitePlace K // w ≠ w₀}
      {w : NumberField.InfinitePlace K // w ≠ w₀} ℝ :=
  Matrix.of fun i w ↦
    2 * Real.log
      (‖1 - (w.val.embedding zeta) ^ ((e i).val + 2)‖ / ‖1 - w.val.embedding zeta‖)

/-- The same regulator matrix written purely as sine values at rational multiples of `pi`.
The finite exponent attached to each column lies in `1, ..., 36` and is prime to `37`. -/
def circularSineMatrix37 {zeta : K} (hzeta : IsPrimitiveRoot zeta 37)
    (w₀ : NumberField.InfinitePlace K)
    (e : {w : NumberField.InfinitePlace K // w ≠ w₀} ≃ Fin 17) :
    Matrix {w : NumberField.InfinitePlace K // w ≠ w₀}
      {w : NumberField.InfinitePlace K // w ≠ w₀} ℝ :=
  Matrix.of fun i w ↦
    2 * Real.log
      (|Real.sin (Real.pi * ((((e i).val + 2 : ℕ) : ℝ) *
          (infinitePlaceExponent37 hzeta w.val : ℝ) / ((37 : ℕ) : ℝ)))| /
        |Real.sin (Real.pi *
          ((infinitePlaceExponent37 hzeta w.val : ℝ) / ((37 : ℕ) : ℝ)))|)

/-- The chord-length and sine-value descriptions of the circular logarithm matrix agree. -/
theorem circularLogMatrix37_eq_circularSineMatrix37 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) (w₀ : NumberField.InfinitePlace K)
    (e : {w : NumberField.InfinitePlace K // w ≠ w₀} ≃ Fin 17) :
    circularLogMatrix37 zeta w₀ e = circularSineMatrix37 hzeta w₀ e := by
  ext i w
  simp only [circularLogMatrix37, circularSineMatrix37, Matrix.of_apply]
  rw [← infinitePlace_circularUnit37 hzeta w.val (e i),
    infinitePlace_circularUnit37_eq_sineRatio hzeta w.val (e i)]

variable [IsCyclotomicExtension {37} ℚ K]

local instance : NumberField.IsCMField K := cyclotomic37_isCMField (K := K)

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- The circular-unit regulator is the absolute determinant of the explicit logarithmic
cyclotomic matrix. -/
theorem circularUnit37_regOfFamily_eq_abs_det {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) (w₀ : NumberField.InfinitePlace K)
    (e : {w : NumberField.InfinitePlace K // w ≠ w₀} ≃ Fin 17) :
    NumberField.Units.regOfFamily (circularUnitRegFamily37 hzeta) =
      |(circularLogMatrix37 zeta w₀ e).det| := by
  classical
  let eRank : {w : NumberField.InfinitePlace K // w ≠ w₀} ≃
      Fin (NumberField.Units.rank K) :=
    e.trans (finCongr (cyclotomic37_unitRank (K := K))).symm
  rw [NumberField.Units.regOfFamily_eq_det (circularUnitRegFamily37 hzeta) w₀ eRank]
  apply congrArg abs
  apply congrArg Matrix.det
  ext i w
  simp only [Matrix.of_apply, circularLogMatrix37,
    NumberField.IsTotallyComplex.mult_eq, Nat.cast_ofNat]
  rw [show circularUnitRegFamily37 hzeta (eRank i) = circularUnit37 hzeta (e i) by
    simp [circularUnitRegFamily37, eRank]]
  rw [infinitePlace_circularUnit37 hzeta]

/-- Equivalently, the circular-unit regulator is the absolute determinant of the fully
trigonometric matrix whose entries involve only `sin (pi * m / 37)`. -/
theorem circularUnit37_regOfFamily_eq_abs_sineDet {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) (w₀ : NumberField.InfinitePlace K)
    (e : {w : NumberField.InfinitePlace K // w ≠ w₀} ≃ Fin 17) :
    NumberField.Units.regOfFamily (circularUnitRegFamily37 hzeta) =
      |(circularSineMatrix37 hzeta w₀ e).det| := by
  rw [circularUnit37_regOfFamily_eq_abs_det hzeta w₀ e,
    circularLogMatrix37_eq_circularSineMatrix37 hzeta w₀ e]

/-- The exponent-`37` real circular-unit index formula is equivalent to a completely explicit
Dedekind-zeta residue / logarithmic-determinant identity.  This removes the abstract regulator
from the remaining analytic boundary. -/
theorem circularUnit37_realIndex_eq_classNumber_iff_logDet {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) (w₀ : NumberField.InfinitePlace K)
    (e : {w : NumberField.InfinitePlace K // w ≠ w₀} ≃ Fin 17) :
    realUnitRelIndex (circularUnit37 hzeta) = NumberField.classNumber K⁺ ↔
      NumberField.dedekindZeta_residue K⁺ =
        |(circularLogMatrix37 zeta w₀ e).det| /
          Real.sqrt |(NumberField.discr K⁺ : ℝ)| := by
  classical
  rw [circularUnit37_realIndex_eq_classNumber_iff hzeta,
    circularUnit37_regOfFamily_eq_abs_det hzeta w₀ e]

/-- Final finite form of the exponent-`37` analytic boundary: the circular-unit index equals
the real class number exactly when the Dedekind-zeta residue is the explicit sine determinant,
divided by the square root of the real cyclotomic discriminant. -/
theorem circularUnit37_realIndex_eq_classNumber_iff_sineDet {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) (w₀ : NumberField.InfinitePlace K)
    (e : {w : NumberField.InfinitePlace K // w ≠ w₀} ≃ Fin 17) :
    realUnitRelIndex (circularUnit37 hzeta) = NumberField.classNumber K⁺ ↔
      NumberField.dedekindZeta_residue K⁺ =
        |(circularSineMatrix37 hzeta w₀ e).det| /
          Real.sqrt |(NumberField.discr K⁺ : ℝ)| := by
  rw [circularUnit37_realIndex_eq_classNumber_iff_logDet hzeta w₀ e,
    circularLogMatrix37_eq_circularSineMatrix37 hzeta w₀ e]

end

end Fermat.Irregular.CyclotomicZeta
