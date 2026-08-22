/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Dominant terms in nonarchimedean products

For a finite product of principal one-units, a unique shallowest
perturbation survives in the product.  Consequently, if the nonzero
perturbations have pairwise distinct valuations, a depth bound on the whole
product forces the same bound on every perturbation.  This is the generic
cancellation engine for the explicit triangular Kummer norm.
-/
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Fermat.Conservation.ValuationProductDominant

variable {F Γ₀ ι : Type*} [Field F]
variable [LinearOrderedCommMonoidWithZero Γ₀]

/-- If every perturbation has valuation at most `q < 1`, then so does the
perturbation of their product. -/
theorem prod_one_add_sub_one_le
    (v : Valuation F Γ₀) (s : Finset ι) (x : ι → F) (q : Γ₀)
    (hq1 : q < 1)
    (hx : ∀ i ∈ s, v (x i) ≤ q) :
    v ((∏ i ∈ s, (1 + x i)) - 1) ≤ q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hxi : v (x i) ≤ q := hx i (Finset.mem_insert_self i s)
      have hxs : ∀ j ∈ s, v (x j) ≤ q := by
        intro j hj
        exact hx j (Finset.mem_insert_of_mem hj)
      have hprev := ih hxs
      let P : F := ∏ j ∈ s, (1 + x j)
      have hPsub : v (P - 1) ≤ q := by simpa [P] using hprev
      have hP : v P = 1 := by
        have hrewrite : P = 1 + (P - 1) := by ring
        rw [hrewrite]
        exact v.map_one_add_of_lt (hPsub.trans_lt hq1)
      have hmul : v (x i * P) ≤ q := by
        rw [map_mul, hP, mul_one]
        exact hxi
      have hid : (1 + x i) * P - 1 = (P - 1) + x i * P := by ring
      rw [Finset.prod_insert hi]
      rw [hid]
      exact v.map_add_le hPsub hmul

/-- If every perturbation is strictly below `q < 1`, so is the perturbation
of their product. -/
theorem prod_one_add_sub_one_lt
    (v : Valuation F Γ₀) (s : Finset ι) (x : ι → F) (q : Γ₀)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hx : ∀ i ∈ s, v (x i) < q) :
    v ((∏ i ∈ s, (1 + x i)) - 1) < q := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hq0
  | @insert i s hi ih =>
      have hxi : v (x i) < q := hx i (Finset.mem_insert_self i s)
      have hxs : ∀ j ∈ s, v (x j) < q := by
        intro j hj
        exact hx j (Finset.mem_insert_of_mem hj)
      have hprev := ih hxs
      let P : F := ∏ j ∈ s, (1 + x j)
      have hPsub : v (P - 1) < q := by simpa [P] using hprev
      have hP : v P = 1 := by
        have hrewrite : P = 1 + (P - 1) := by ring
        rw [hrewrite]
        exact v.map_one_add_of_lt (hPsub.trans hq1)
      have hmul : v (x i * P) < q := by
        rw [map_mul, hP, mul_one]
        exact hxi
      have hid : (1 + x i) * P - 1 = (P - 1) + x i * P := by ring
      rw [Finset.prod_insert hi]
      rw [hid]
      exact (map_add_le_max v _ _).trans_lt (max_lt hPsub hmul)

/-- A unique maximal perturbation determines the valuation of the entire
product-minus-one. -/
theorem valuation_prod_one_add_eq_of_unique_dominant
    [Nontrivial Γ₀]
    (v : Valuation F Γ₀) (s : Finset ι) (x : ι → F) (k : ι)
    (hk : k ∈ s) (hxk0 : x k ≠ 0) (hxk1 : v (x k) < 1)
    (hdominant : ∀ i ∈ s, i ≠ k → v (x i) < v (x k)) :
    v ((∏ i ∈ s, (1 + x i)) - 1) = v (x k) := by
  classical
  let Q : F := ∏ i ∈ s.erase k, (1 + x i)
  have hq0 : 0 < v (x k) := by
    rw [pos_iff_ne_zero]
    intro hzero
    exact hxk0 ((Valuation.zero_iff v).mp hzero)
  have hQsub : v (Q - 1) < v (x k) := by
    apply prod_one_add_sub_one_lt v (s.erase k) x (v (x k)) hq0 hxk1
    intro i hi
    exact hdominant i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
  have hxunit : v (1 + x k) = 1 := v.map_one_add_of_lt hxk1
  have hsmall : v ((1 + x k) * (Q - 1)) < v (x k) := by
    rw [map_mul, hxunit, one_mul]
    exact hQsub
  have hprod : (∏ i ∈ s, (1 + x i)) = (1 + x k) * Q := by
    exact (Finset.mul_prod_erase s (fun i => 1 + x i) hk).symm
  rw [hprod]
  have hid : (1 + x k) * Q - 1 = x k + (1 + x k) * (Q - 1) := by ring
  rw [hid]
  exact v.map_add_eq_of_lt_left hsmall

/-- If all nonzero perturbations have distinct valuations below one, a
depth bound on the product-minus-one applies to every perturbation.  Zero
perturbations are handled automatically. -/
theorem each_valuation_le_of_prod_one_add_sub_one_le
    [Nontrivial Γ₀]
    (v : Valuation F Γ₀) (s : Finset ι) (x : ι → F) (bound : Γ₀)
    (hx1 : ∀ i ∈ s, v (x i) < 1)
    (hdistinct : ∀ i ∈ s, ∀ j ∈ s,
      x i ≠ 0 → x j ≠ 0 → i ≠ j → v (x i) ≠ v (x j))
    (hprod : v ((∏ i ∈ s, (1 + x i)) - 1) ≤ bound) :
    ∀ i ∈ s, v (x i) ≤ bound := by
  classical
  intro i hi
  by_cases hxi0 : x i = 0
  · simp [hxi0]
  let t := s.filter fun j => x j ≠ 0
  have hit : i ∈ t := Finset.mem_filter.mpr ⟨hi, hxi0⟩
  obtain ⟨k, hkt, hmax⟩ :=
    Finset.exists_max_image t (fun j => v (x j)) ⟨i, hit⟩
  have hks : k ∈ s := (Finset.mem_filter.mp hkt).1
  have hxk0 : x k ≠ 0 := (Finset.mem_filter.mp hkt).2
  have hdominant : ∀ j ∈ t, j ≠ k → v (x j) < v (x k) := by
    intro j hj hjk
    have hjs : j ∈ s := (Finset.mem_filter.mp hj).1
    have hxj0 : x j ≠ 0 := (Finset.mem_filter.mp hj).2
    exact lt_of_le_of_ne (hmax j hj)
      (hdistinct j hjs k hks hxj0 hxk0 hjk)
  have htprod : (∏ j ∈ t, (1 + x j)) = ∏ j ∈ s, (1 + x j) := by
    apply Finset.prod_subset
    · intro j hj
      exact (Finset.mem_filter.mp hj).1
    · intro j hjs hjt
      have hxj : x j = 0 := by
        by_contra hxj0
        exact hjt (Finset.mem_filter.mpr ⟨hjs, hxj0⟩)
      simp [hxj]
  have hdom := valuation_prod_one_add_eq_of_unique_dominant
    v t x k hkt hxk0 (hx1 k hks) hdominant
  rw [htprod] at hdom
  exact (hmax i hit).trans (hdom ▸ hprod)

end Fermat.Conservation.ValuationProductDominant
