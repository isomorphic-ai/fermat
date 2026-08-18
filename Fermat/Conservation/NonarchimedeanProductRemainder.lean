/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# First-order finite-product bounds over a nonarchimedean absolute value

The product `∏ (1 + xᵢ)` differs from `1 + ∑ xᵢ` only quadratically in
the common bound on the `xᵢ`.  The result is also packaged for the
coefficient-supremum Gauss norm on polynomials over an ultrametric field.
This is the bookkeeping engine for finite triangular Kummer-factor
contractions; it contains no prime-specific arithmetic.
-/
import Mathlib.RingTheory.Polynomial.GaussNorm
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Analysis.Polynomial.Norm
import Mathlib.Tactic

noncomputable section

open scoped BigOperators
open Polynomial

namespace Fermat.Conservation.NonarchimedeanProductRemainder

variable {R ι : Type*} [CommRing R] [Nontrivial R]

/-- Simultaneous linear and quadratic estimates for a finite product of
one-units under a nonarchimedean absolute value. -/
theorem prod_one_add_first_order_bound
    (v : AbsoluteValue R ℝ) (hna : IsNonarchimedean v)
    (s : Finset ι) (x : ι → R) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hx : ∀ i ∈ s, v (x i) ≤ q) :
    v ((s.prod fun i ↦ 1 + x i) - 1) ≤ q ∧
      v ((s.prod fun i ↦ 1 + x i) - 1 - s.sum x) ≤ q ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hq0]
  | @insert i s hi ih =>
      have hxi : v (x i) ≤ q := hx i (Finset.mem_insert_self i s)
      have hxs : ∀ j ∈ s, v (x j) ≤ q := by
        intro j hj
        exact hx j (Finset.mem_insert_of_mem hj)
      obtain ⟨hfirst, hsecond⟩ := ih hxs
      let P : R := s.prod fun j ↦ 1 + x j
      let S : R := s.sum x
      have hPsub : v (P - 1) ≤ q := by
        simpa [P] using hfirst
      have hP : v P ≤ 1 := by
        calc
          v P = v (1 + (P - 1)) := by ring_nf
          _ ≤ max (v (1 : R)) (v (P - 1)) := hna _ _
          _ ≤ 1 := by
            rw [v.map_one]
            exact max_le le_rfl (hPsub.trans hq1)
      have hmulP : v (x i * P) ≤ q := by
        rw [v.map_mul]
        calc
          v (x i) * v P ≤ q * 1 :=
            mul_le_mul hxi hP (v.nonneg _) hq0
          _ = q := mul_one q
      have hfirst' : v ((1 + x i) * P - 1) ≤ q := by
        calc
          v ((1 + x i) * P - 1) = v ((P - 1) + x i * P) := by ring_nf
          _ ≤ max (v (P - 1)) (v (x i * P)) := hna _ _
          _ ≤ q := max_le hPsub hmulP
      have hmulR : v (x i * (P - 1)) ≤ q ^ 2 := by
        rw [v.map_mul]
        simpa [pow_two] using mul_le_mul hxi hPsub (v.nonneg _) hq0
      have hsecondP : v (P - 1 - S) ≤ q ^ 2 := by
        simpa [P, S] using hsecond
      have hsecond' :
          v ((1 + x i) * P - 1 - (x i + S)) ≤ q ^ 2 := by
        calc
          v ((1 + x i) * P - 1 - (x i + S)) =
              v ((P - 1 - S) + x i * (P - 1)) := by ring_nf
          _ ≤ max (v (P - 1 - S)) (v (x i * (P - 1))) := hna _ _
          _ ≤ q ^ 2 := max_le hsecondP hmulR
      simpa [Finset.prod_insert hi, Finset.sum_insert hi, P, S] using
        And.intro hfirst' hsecond'

section Polynomial

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]

/-- The coefficient-supremum Gauss norm as a bundled absolute value. -/
noncomputable def polynomialSupAbsoluteValue : AbsoluteValue F[X] ℝ :=
  let v := NormedField.toAbsoluteValue F
  letI : IsAbsoluteValue (Polynomial.gaussNorm v 1) :=
    Polynomial.gaussNorm_isAbsoluteValue
      (v := v) IsUltrametricDist.isNonarchimedean_norm
      (by norm_num : (0 : ℝ) < 1)
  IsAbsoluteValue.toAbsoluteValue (Polynomial.gaussNorm v 1)

@[simp]
theorem polynomialSupAbsoluteValue_apply (f : F[X]) :
    polynomialSupAbsoluteValue f = f.supNorm := by
  rfl

/-- Polynomial version of the quadratic finite-product estimate. -/
theorem polynomial_prod_one_add_first_order_bound
    (s : Finset ι) (x : ι → F[X]) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hx : ∀ i ∈ s, (x i).supNorm ≤ q) :
    ((s.prod fun i ↦ 1 + x i) - 1).supNorm ≤ q ∧
      ((s.prod fun i ↦ 1 + x i) - 1 - s.sum x).supNorm ≤ q ^ 2 := by
  simpa only [polynomialSupAbsoluteValue_apply] using
    prod_one_add_first_order_bound polynomialSupAbsoluteValue
      (by
        intro f g
        change (f + g).supNorm ≤ max f.supNorm g.supNorm
        exact Polynomial.isNonarchimedean_gaussNorm
          (v := NormedField.toAbsoluteValue F)
          IsUltrametricDist.isNonarchimedean_norm
          (by norm_num : (0 : ℝ) ≤ 1) f g)
      s x q hq0 hq1 hx

end Polynomial

end Fermat.Conservation.NonarchimedeanProductRemainder
