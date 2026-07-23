import Fermat.Irregular.VandiverLogDerivative
import Mathlib.RingTheory.PowerSeries.Exp

/-!
# Formal logarithmic derivatives for Vandiver's calculation

This file supplies the multiplicative algebra used between Vandiver's
polynomial remainder identity and the Bernoulli generating series.  All
objects are formal power series over `ℚ`; no analytic logarithm or
convergence assertion is used.
-/

namespace Fermat.Irregular.VandiverPowerSeriesLog

open PowerSeries
open Fermat.Irregular.VandiverLogDerivative

noncomputable section

/-- The formal logarithmic derivative `f' / f`.  The hypotheses in the
lemmas below ensure that the constant coefficient of `f` is nonzero, so
the power-series inverse is genuine. -/
def logarithmicDerivative (f : PowerSeries ℚ) : PowerSeries ℚ :=
  d⁄dX ℚ f * f⁻¹

theorem logarithmicDerivative_mul
    (f g : PowerSeries ℚ)
    (hf : PowerSeries.constantCoeff f ≠ 0)
    (hg : PowerSeries.constantCoeff g ≠ 0) :
    logarithmicDerivative (f * g) =
      logarithmicDerivative f + logarithmicDerivative g := by
  have hfinv : f * f⁻¹ = 1 := PowerSeries.mul_inv_cancel f hf
  have hginv : g * g⁻¹ = 1 := PowerSeries.mul_inv_cancel g hg
  rw [logarithmicDerivative, Derivation.leibniz,
    PowerSeries.mul_inv_rev]
  simp only [smul_eq_mul]
  rw [logarithmicDerivative, logarithmicDerivative]
  calc
    (f * d⁄dX ℚ g + g * d⁄dX ℚ f) * (g⁻¹ * f⁻¹) =
        d⁄dX ℚ f * (g * g⁻¹) * f⁻¹ +
          d⁄dX ℚ g * (f * f⁻¹) * g⁻¹ := by ring
    _ = d⁄dX ℚ f * f⁻¹ + d⁄dX ℚ g * g⁻¹ := by rw [hginv, hfinv]; ring

theorem constantCoeff_pow_ne_zero (f : PowerSeries ℚ) (n : ℕ)
    (hf : PowerSeries.constantCoeff f ≠ 0) :
    PowerSeries.constantCoeff (f ^ n) ≠ 0 := by
  simp only [map_pow]
  exact pow_ne_zero n hf

theorem logarithmicDerivative_pow
    (f : PowerSeries ℚ) (n : ℕ)
    (hf : PowerSeries.constantCoeff f ≠ 0) :
    logarithmicDerivative (f ^ n) =
      PowerSeries.C (n : ℚ) * logarithmicDerivative f := by
  induction n with
  | zero => simp [logarithmicDerivative]
  | succ n ih =>
      rw [pow_succ, logarithmicDerivative_mul]
      · rw [ih]
        simp only [Nat.cast_add, Nat.cast_one, map_add, map_natCast, map_one]
        ring
      · exact constantCoeff_pow_ne_zero f n hf
      · exact hf

theorem formalDerivativeAtZero_add (n : ℕ) (f g : PowerSeries ℚ) :
    formalDerivativeAtZero n (f + g) =
      formalDerivativeAtZero n f + formalDerivativeAtZero n g := by
  simp [formalDerivativeAtZero]
  ring

theorem formalDerivativeAtZero_sum
    {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℚ) (n : ℕ) :
    formalDerivativeAtZero n (∑ i ∈ s, f i) =
      ∑ i ∈ s, formalDerivativeAtZero n (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [formalDerivativeAtZero]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [formalDerivativeAtZero_add, ih]

theorem formalDerivativeAtZero_C_mul
    (c : ℚ) (f : PowerSeries ℚ) (n : ℕ) :
    formalDerivativeAtZero n (PowerSeries.C c * f) =
      c * formalDerivativeAtZero n f := by
  simp [formalDerivativeAtZero]
  ring

/-! ## The cyclotomic geometric sum -/

/-- The formal series obtained by substituting `exp X` into
`1 + W + ... + W^(r-1)`. -/
def geomExp (r : ℕ) : PowerSeries ℚ :=
  ∑ j ∈ Finset.range r, PowerSeries.exp ℚ ^ j

@[simp]
theorem constantCoeff_geomExp (r : ℕ) :
    PowerSeries.constantCoeff (geomExp r) = (r : ℚ) := by
  simp [geomExp]

theorem exp_sub_one_mul_geomExp (r : ℕ) :
    (PowerSeries.exp ℚ - 1) * geomExp r =
      PowerSeries.exp ℚ ^ r - 1 := by
  simp only [geomExp]
  exact mul_geom_sum (PowerSeries.exp ℚ) r

private theorem exp_sub_one_ne_zero :
    PowerSeries.exp ℚ - 1 ≠ 0 := by
  intro h
  have hcoeff := congrArg (PowerSeries.coeff 1) h
  norm_num at hcoeff

private theorem derivative_geomExp_identity (r : ℕ) :
    (PowerSeries.exp ℚ - 1) * d⁄dX ℚ (geomExp r) =
      PowerSeries.C (r : ℚ) * (PowerSeries.exp ℚ ^ r) -
        PowerSeries.exp ℚ * geomExp r := by
  have h := congrArg (PowerSeries.derivative ℚ)
    (exp_sub_one_mul_geomExp r)
  simp only [map_sub, Derivation.map_one_eq_zero,
    PowerSeries.derivative_exp, sub_zero, Derivation.leibniz, smul_eq_mul,
    PowerSeries.derivative_pow] at h
  calc
    (PowerSeries.exp ℚ - 1) * d⁄dX ℚ (geomExp r) =
        (r : PowerSeries ℚ) * PowerSeries.exp ℚ ^ (r - 1) *
            PowerSeries.exp ℚ - PowerSeries.exp ℚ * geomExp r := by
      linear_combination h
    _ = PowerSeries.C (r : ℚ) * (PowerSeries.exp ℚ ^ r) -
        PowerSeries.exp ℚ * geomExp r := by
      cases r with
      | zero => simp
      | succ r =>
          simp only [Nat.succ_sub_one, pow_succ]
          norm_num
          ring

/-- The regularized Bernoulli series is exactly the formal logarithmic
derivative of the cyclotomic geometric sum. -/
theorem logarithmicDerivative_geomExp (r : ℕ) (hr : 0 < r) :
    logarithmicDerivative (geomExp r) =
      vandiverLogDerivative (r : ℚ) := by
  let e : PowerSeries ℚ := PowerSeries.exp ℚ
  let g : PowerSeries ℚ := geomExp r
  let L : PowerSeries ℚ := vandiverLogDerivative (r : ℚ)
  have hgeom : (e - 1) * g = e ^ r - 1 := by
    simpa [e, g] using exp_sub_one_mul_geomExp r
  have hder : (e - 1) * d⁄dX ℚ g =
      PowerSeries.C (r : ℚ) * e ^ r - e * g := by
    simpa [e, g] using derivative_geomExp_identity r
  have hcross := vandiverLogDerivative_mul_exp_factors (r : ℚ)
  rw [← PowerSeries.exp_pow_eq_rescale_exp (A := ℚ) r] at hcross
  have hmul : (e - 1) * (e - 1) * (L * g) =
      (e - 1) * (e - 1) * d⁄dX ℚ g := by
    calc
      (e - 1) * (e - 1) * (L * g) =
          L * (e ^ r - 1) * (e - 1) := by rw [← hgeom]; ring
      _ = PowerSeries.C (r : ℚ) * e ^ r * (e - 1) -
          e * (e ^ r - 1) := by simpa [e, L] using hcross
      _ = (PowerSeries.C (r : ℚ) * e ^ r - e * g) * (e - 1) := by
        rw [← hgeom]
        ring
      _ = (e - 1) * (e - 1) * d⁄dX ℚ g := by
        calc
          (PowerSeries.C (r : ℚ) * e ^ r - e * g) * (e - 1) =
              (e - 1) * (PowerSeries.C (r : ℚ) * e ^ r - e * g) := by ring
          _ = (e - 1) * ((e - 1) * d⁄dX ℚ g) := by rw [hder]
          _ = (e - 1) * (e - 1) * d⁄dX ℚ g := by ring
  have he : e - 1 ≠ 0 := by simpa [e] using exp_sub_one_ne_zero
  have hLg : L * g = d⁄dX ℚ g :=
    mul_left_cancel₀ (mul_ne_zero he he) hmul
  have hg : PowerSeries.constantCoeff g ≠ 0 := by
    simpa [g] using (show (r : ℚ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hr)
  calc
    logarithmicDerivative (geomExp r) = d⁄dX ℚ g * g⁻¹ := by
      simp only [logarithmicDerivative, g]
    _ = (L * g) * g⁻¹ := by rw [hLg]
    _ = L * (g * g⁻¹) := by ring
    _ = L := by rw [PowerSeries.mul_inv_cancel g hg, mul_one]
    _ = vandiverLogDerivative (r : ℚ) := rfl

end

end Fermat.Irregular.VandiverPowerSeriesLog
