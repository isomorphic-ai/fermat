/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Multiplicative absorption of triangular spectral remainders

If the nonconstant coefficients of a normalized polynomial lie strictly
inside the base unit ball, its evaluated triangular product has spectral
norm exactly one.  The additive remainder supplied by triangular
factorization may therefore be divided by this base product without losing
any of its quadratic spectral contraction, and reinserted as one
multiplicative principal factor.
-/
import Fermat.Experiments.Conservation.PrimeTriangularNormBounds
import Fermat.Experiments.Conservation.PrimeTriangularSpectralContraction
import Mathlib.Tactic

open Polynomial

noncomputable section

namespace Fermat.Conservation.PrimeTriangularSpectralAbsorption

open PrimeTriangularUnitFactorization
open PrimeTriangularNormBounds
open PrimeTriangularSpectralContraction
open SpectralNormProductRemainder

variable {F E : Type*}
variable [NontriviallyNormedField F] [Field E] [Algebra F E]
variable [Algebra.IsAlgebraic F E] [IsUltrametricDist F] [CompleteSpace F]

omit [CompleteSpace F] in
private theorem spectralNorm_eq_one_of_sub_one_lt_one (z : E)
    (hz : spectralNorm F E (z - 1) < 1) :
    spectralNorm F E z = 1 := by
  have hna := isNonarchimedean_spectralNorm (K := F) (L := E)
  have hle : spectralNorm F E z ≤ 1 := by
    calc
      spectralNorm F E z = spectralNorm F E (1 + (z - 1)) := by ring_nf
      _ ≤ max (spectralNorm F E (1 : E))
          (spectralNorm F E (z - 1)) := hna _ _
      _ ≤ 1 := by
        rw [spectralNorm_one]
        exact max_le le_rfl hz.le
  apply le_antisymm hle
  apply le_of_not_gt
  intro hlt
  have hone : spectralNorm F E (1 : E) < 1 := by
    calc
      spectralNorm F E (1 : E) = spectralNorm F E (z - (z - 1)) := by ring_nf
      _ ≤ max (spectralNorm F E z)
          (spectralNorm F E (-(z - 1))) := by
        simpa [sub_eq_add_neg] using hna z (-(z - 1))
      _ < 1 := by
        rw [spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic (z - 1))]
        exact max_lt hlt hz
  exact (lt_irrefl (1 : ℝ)) (by simpa only [spectralNorm_one] using hone)

/-- A triangular product whose installed coefficients are strictly inside
the base unit ball evaluates to a spectral unit. -/
theorem evaluated_triangularProduct_spectralNorm_eq_one
    (f : F[X]) (n : ℕ) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hq_lt : q < 1)
    (hf : ∀ j : ℕ, 0 < j → ‖f.coeff j‖ ≤ q)
    (alpha : E) (halpha : spectralNorm F E alpha ≤ 1) :
    spectralNorm F E (aeval alpha (triangularProduct f n)) = 1 := by
  let x : ℕ → E := fun j ↦
    algebraMap F E (triangularCoefficient f j) * alpha ^ j
  have hc := triangularCoefficient_norm_le f q hq0 hq1 hf
  have hx : ∀ j ∈ Finset.Icc 1 n, spectralNorm F E (x j) ≤ q := by
    intro j hj
    have hjpos : 0 < j := (Finset.mem_Icc.mp hj).1
    change spectralNorm F E
      (algebraMap F E (triangularCoefficient f j) * alpha ^ j) ≤ q
    rw [← spectralMulAlgNorm_def, map_mul, map_pow,
      spectralMulAlgNorm_def, spectralMulAlgNorm_def,
      spectralNorm_extends]
    calc
      ‖triangularCoefficient f j‖ * spectralNorm F E alpha ^ j ≤
          q * 1 := mul_le_mul (hc j hjpos)
            (pow_le_one₀ (spectralNorm_nonneg alpha) halpha)
            (pow_nonneg (spectralNorm_nonneg alpha) j) hq0
      _ = q := mul_one q
  have hprod :=
    (prod_one_add_first_order_bound
      (s := Finset.Icc 1 n) x q hq0 hq1 hx).1
  have heval :
      aeval alpha (triangularProduct f n) =
        ∏ j ∈ Finset.Icc 1 n, (1 + x j) := by
    rw [triangularProduct_eq_prod]
    simp only [map_prod, map_add, map_one, map_mul, aeval_C, map_pow,
      aeval_X, x]
  apply spectralNorm_eq_one_of_sub_one_lt_one
  rw [heval]
  exact hprod.trans_lt hq_lt

/-- When the evaluation point itself is strictly inside the spectral unit
ball, integral nonconstant coefficients suffice: every positive-degree
triangular perturbation is strict because it contains a positive power of
`alpha`.  This is the boundary-`q = 1` form needed for the first contraction
round of an arbitrary integral Kummer element. -/
theorem evaluated_triangularProduct_spectralNorm_eq_one_of_alpha_lt_one
    (f : F[X]) (n : ℕ)
    (hf : ∀ j : ℕ, 0 < j → ‖f.coeff j‖ ≤ 1)
    (alpha : E) (halpha_lt : spectralNorm F E alpha < 1) :
    spectralNorm F E (aeval alpha (triangularProduct f n)) = 1 := by
  let x : ℕ → E := fun j ↦
    algebraMap F E (triangularCoefficient f j) * alpha ^ j
  have hc := triangularCoefficient_norm_le f 1 (by norm_num) (by norm_num) hf
  have hx : ∀ j ∈ Finset.Icc 1 n, spectralNorm F E (x j) < 1 := by
    intro j hj
    have hjpos : 0 < j := (Finset.mem_Icc.mp hj).1
    change spectralNorm F E
      (algebraMap F E (triangularCoefficient f j) * alpha ^ j) < 1
    rw [← spectralMulAlgNorm_def, map_mul, map_pow,
      spectralMulAlgNorm_def, spectralMulAlgNorm_def,
      spectralNorm_extends]
    exact mul_lt_one_of_nonneg_of_lt_one_right (hc j hjpos)
      (pow_nonneg (spectralNorm_nonneg alpha) j)
      (pow_lt_one₀ (spectralNorm_nonneg alpha) halpha_lt
        (Nat.ne_of_gt hjpos))
  rw [triangularProduct_eq_prod]
  simp only [map_prod, map_add, map_one, map_mul, aeval_C, map_pow,
    aeval_X]
  change spectralMulAlgNorm F E
      (∏ j ∈ Finset.Icc 1 n, (1 + x j)) = 1
  rw [map_prod]
  apply Finset.prod_eq_one
  intro j hj
  change spectralNorm F E (1 + x j) = 1
  apply spectralNorm_eq_one_of_sub_one_lt_one
  simpa only [add_sub_cancel_left] using hx j hj

/-- Dividing by a spectral unit preserves a spectral bound. -/
theorem spectralNorm_div_le_of_eq_one
    (y P : E) (hP : spectralNorm F E P = 1) (q : ℝ)
    (hy : spectralNorm F E y ≤ q) :
    spectralNorm F E (y / P) ≤ q := by
  rw [← spectralMulAlgNorm_def, map_div₀ (spectralMulAlgNorm F E),
    spectralMulAlgNorm_def, spectralMulAlgNorm_def, hP, div_one]
  exact hy

/-- An additive remainder can be divided by a spectral unit, with no loss
of depth, and then reinserted multiplicatively. -/
theorem absorb_additive_remainder_by_spectral_unit
    (P y : E) (a : F) (hP : spectralNorm F E P = 1)
    (q : ℝ) (hy : spectralNorm F E y ≤ q) :
    P + algebraMap F E a * y =
        P * (1 + algebraMap F E a * (y / P)) ∧
      spectralNorm F E (y / P) ≤ q := by
  have hP0 : P ≠ 0 := by
    intro hzero
    rw [hzero, spectralNorm_zero] at hP
    norm_num at hP
  constructor
  · field_simp [hP0]
  · exact spectralNorm_div_le_of_eq_one y P hP q hy

/-- The additive triangular remainder can be absorbed multiplicatively
without losing its quadratic spectral contraction. -/
theorem exists_evaluated_triangular_absorption_spectralNorm_le_sq
    (f : F[X]) (hf0 : f.coeff 0 = 1)
    (p : ℕ) (hp : 0 < p) (hdeg : f.natDegree < p)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hq_lt : q < 1)
    (hf : ∀ j : ℕ, 0 < j → ‖f.coeff j‖ ≤ q)
    (alpha : E) (a : F) (halpha : alpha ^ p = algebraMap F E a)
    (halphaNorm : spectralNorm F E alpha ≤ 1) :
    ∃ z : E,
      aeval alpha f =
          aeval alpha (triangularProduct f (p - 1)) *
            (1 + algebraMap F E a * z) ∧
      spectralNorm F E z ≤ q ^ 2 := by
  obtain ⟨y, hyEq, hy⟩ :=
    exists_evaluated_triangular_remainder_spectralNorm_le_sq
      f hf0 p hp hdeg q hq0 hq1 hf alpha a halpha halphaNorm
  let P : E := aeval alpha (triangularProduct f (p - 1))
  have hP : spectralNorm F E P = 1 := by
    exact evaluated_triangularProduct_spectralNorm_eq_one
      f (p - 1) q hq0 hq1 hq_lt hf alpha halphaNorm
  have hP0 : P ≠ 0 := by
    intro hzero
    rw [hzero, spectralNorm_zero] at hP
    norm_num at hP
  refine ⟨y / P, ?_, spectralNorm_div_le_of_eq_one y P hP (q ^ 2) hy⟩
  change aeval alpha f = P * (1 + algebraMap F E a * (y / P))
  rw [hyEq]
  change P + algebraMap F E a * y =
    P * (1 + algebraMap F E a * (y / P))
  field_simp [hP0]

end Fermat.Conservation.PrimeTriangularSpectralAbsorption
