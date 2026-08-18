/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# A quadratic spectral bound for finite products of one-units

This file records the first-order Taylor estimate needed for norm
filtrations in wildly ramified Kummer extensions.  It is independent of a
prime and of the concrete Kummer presentation.

For a finite family with spectral sizes at most `q ≤ 1`, the product
`∏ (1 + xᵢ)` differs from `1 + ∑ xᵢ` by spectral size at most `q²`.
Applied to all Galois conjugates, this says that

`Norm(1 + a*y) - 1 - a*Trace(y)`

has base norm at most `‖a‖²` whenever `y` is spectrally integral.
-/
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic

noncomputable section

open scoped BigOperators

namespace Fermat.Conservation.SpectralNormProductRemainder

variable {F E ι : Type*}
variable [NontriviallyNormedField F] [Field E] [Algebra F E]
variable [Algebra.IsAlgebraic F E] [IsUltrametricDist F] [CompleteSpace F]

/-- A finite product of spectral one-units is controlled to first order,
simultaneously with its quadratic Taylor remainder. -/
theorem prod_one_add_first_order_bound
    (s : Finset ι) (x : ι → E) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hx : ∀ i ∈ s, spectralNorm F E (x i) ≤ q) :
    spectralNorm F E ((s.prod fun i ↦ 1 + x i) - 1) ≤ q ∧
      spectralNorm F E
          ((s.prod fun i ↦ 1 + x i) - 1 - s.sum x) ≤ q ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty, sub_self]
      constructor
      · simpa only [spectralNorm_zero] using hq0
      · simpa only [spectralNorm_zero] using sq_nonneg q
  | @insert i s hi ih =>
      have hxi : spectralNorm F E (x i) ≤ q := hx i (Finset.mem_insert_self i s)
      have hxs : ∀ j ∈ s, spectralNorm F E (x j) ≤ q := by
        intro j hj
        exact hx j (Finset.mem_insert_of_mem hj)
      obtain ⟨hfirst, hsecond⟩ := ih hxs
      let P : E := s.prod fun j ↦ 1 + x j
      let S : E := s.sum x
      have hPsub : spectralNorm F E (P - 1) ≤ q := by
        simpa [P] using hfirst
      have hP : spectralNorm F E P ≤ 1 := by
        have hna := isNonarchimedean_spectralNorm (K := F) (L := E)
        calc
          spectralNorm F E P = spectralNorm F E (1 + (P - 1)) := by ring_nf
          _ ≤ max (spectralNorm F E (1 : E))
                (spectralNorm F E (P - 1)) := hna _ _
          _ ≤ 1 := by
            rw [spectralNorm_one]
            exact max_le le_rfl (hPsub.trans hq1)
      have hmulP : spectralNorm F E (x i * P) ≤ q := by
        rw [← spectralMulAlgNorm_def, map_mul, spectralMulAlgNorm_def,
          spectralMulAlgNorm_def]
        calc
          spectralNorm F E (x i) * spectralNorm F E P ≤ q * 1 :=
            mul_le_mul hxi hP (spectralNorm_nonneg _) hq0
          _ = q := mul_one q
      have hfirst' :
          spectralNorm F E ((1 + x i) * P - 1) ≤ q := by
        have hna := isNonarchimedean_spectralNorm (K := F) (L := E)
        calc
          spectralNorm F E ((1 + x i) * P - 1) =
              spectralNorm F E ((P - 1) + x i * P) := by ring_nf
          _ ≤ max (spectralNorm F E (P - 1))
                (spectralNorm F E (x i * P)) := hna _ _
          _ ≤ q := max_le hPsub hmulP
      have hmulR : spectralNorm F E (x i * (P - 1)) ≤ q ^ 2 := by
        rw [← spectralMulAlgNorm_def, map_mul, spectralMulAlgNorm_def,
          spectralMulAlgNorm_def]
        simpa [pow_two] using mul_le_mul hxi hPsub
          (spectralNorm_nonneg _) hq0
      have hsecondP : spectralNorm F E (P - 1 - S) ≤ q ^ 2 := by
        simpa [P, S] using hsecond
      have hsecond' :
          spectralNorm F E
              ((1 + x i) * P - 1 - (x i + S)) ≤ q ^ 2 := by
        have hna := isNonarchimedean_spectralNorm (K := F) (L := E)
        calc
          spectralNorm F E ((1 + x i) * P - 1 - (x i + S)) =
              spectralNorm F E ((P - 1 - S) + x i * (P - 1)) := by ring_nf
          _ ≤ max (spectralNorm F E (P - 1 - S))
                (spectralNorm F E (x i * (P - 1))) := hna _ _
          _ ≤ q ^ 2 := max_le hsecondP hmulR
      simpa [Finset.prod_insert hi, Finset.sum_insert hi, P, S] using
        And.intro hfirst' hsecond'

/-- In a finite Galois extension, the field norm of `1 + a*y` differs
from its linear trace approximation by at most `‖a‖²`, provided `a` and
`y` lie in the respective spectral unit balls. -/
theorem norm_one_add_sub_trace_norm_le_sq
    [FiniteDimensional F E] [IsGalois F E]
    (a : F) (y : E) (ha : ‖a‖ ≤ 1)
    (hy : spectralNorm F E y ≤ 1) :
    ‖Algebra.norm F (1 + algebraMap F E a * y) -
        1 - a * Algebra.trace F E y‖ ≤ ‖a‖ ^ 2 := by
  classical
  let x : (E ≃ₐ[F] E) → E := fun sigma ↦
    algebraMap F E a * sigma y
  have hx (sigma : E ≃ₐ[F] E) :
      spectralNorm F E (x sigma) ≤ ‖a‖ := by
    rw [← spectralMulAlgNorm_def, map_mul, spectralMulAlgNorm_def,
      spectralMulAlgNorm_def]
    rw [spectralNorm_extends]
    have hinv : spectralNorm F E (sigma y) = spectralNorm F E y := by
      simpa using (spectralNorm_eq_of_equiv (K := F) (x := y) sigma).symm
    rw [hinv]
    simpa using mul_le_mul_of_nonneg_left hy (norm_nonneg a)
  have hbound :=
    (prod_one_add_first_order_bound
      (s := Finset.univ) x ‖a‖ (norm_nonneg a) ha
      (fun sigma _ ↦ hx sigma)).2
  have hprod :
      (Finset.univ.prod fun sigma : E ≃ₐ[F] E ↦ 1 + x sigma) =
        algebraMap F E
          (Algebra.norm F (1 + algebraMap F E a * y)) := by
    rw [Algebra.norm_eq_prod_automorphisms]
    apply Finset.prod_congr rfl
    intro sigma hsigma
    simp only [x, map_add, map_one, map_mul,
      AlgEquiv.commutes]
  have hsum :
      (Finset.univ.sum fun sigma : E ≃ₐ[F] E ↦ x sigma) =
        algebraMap F E (a * Algebra.trace F E y) := by
    simp only [x, ← Finset.mul_sum, trace_eq_sum_automorphisms,
      map_mul]
  rw [hprod, hsum] at hbound
  rw [← map_one (algebraMap F E), ← map_sub, ← map_sub,
    spectralNorm_extends] at hbound
  simpa only [map_one] using hbound

end Fermat.Conservation.SpectralNormProductRemainder
