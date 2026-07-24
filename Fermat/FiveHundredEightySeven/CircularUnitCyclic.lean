import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Cyclic compression of the exponent-587 circular-unit matrix

Let `Cyc = ZMod 293`.  A cyclic correlation inverse

`∑ u, f u * g (u + d) = δ(d,0)`

induces an inverse for the `292 × 292` reduced difference matrices

`D_h(i,j) = h(i+j) - h(i)`.

The proof extends the nonzero-coordinate sum by its vanishing zero term,
reindexes two cyclic sums by translation, and reduces each matrix entry to

`δ(coord k - coord i, 0) - δ(-coord i, 0) = δ(i,k)`.

This packages the compression identity independently of the concrete
correlation certificate used later in the exponent-587 development.
-/

namespace Fermat.FiveHundredEightySeven.CircularUnitCyclic

open scoped BigOperators Matrix

/-- The cyclic group of order `(587 - 1) / 2 = 293`. -/
abbrev Cyc := ZMod 293

private def succCoord (n : ℕ) [NeZero (n + 1)] (i : Fin n) : ZMod (n + 1) :=
  ZMod.finEquiv (n + 1) i.succ

/-- Enumeration of the nonzero elements of `ZMod 293`. -/
def coord (i : Fin 292) : Cyc :=
  succCoord 292 i

/-- The reduced difference matrix attached to a cyclic function. -/
def differenceMatrix (h : Cyc → ZMod 587) :
    Matrix (Fin 292) (Fin 292) (ZMod 587) :=
  fun i j ↦ h (coord i + coord j) - h (coord i)

/-- The nonzero-coordinate enumeration is injective. -/
theorem coord_injective : Function.Injective coord := by
  intro i j hij
  apply Fin.succ_injective
  exact (ZMod.finEquiv 293).injective hij

/-- Every enumerated coordinate is nonzero. -/
theorem coord_ne_zero (i : Fin 292) : coord i ≠ 0 := by
  intro hi
  have : i.succ = (0 : Fin 293) :=
    (ZMod.finEquiv 293).injective (by
      change ZMod.finEquiv 293 i.succ = 0 at hi
      simpa only [map_zero] using hi)
  exact Fin.succ_ne_zero i this

/-- Generic finite-sum decomposition of `ZMod (n+1)` into zero and the
coordinates enumerated by successors.  Keeping this generic prevents the
elaborator from unfolding all 293 concrete coordinates. -/
private theorem sum_zmod_succ_eq_zero_add_coord
    {n : ℕ} [NeZero (n + 1)] {A : Type*} [AddCommMonoid A]
    (F : ZMod (n + 1) → A) :
    (∑ u : ZMod (n + 1), F u) =
      F 0 + ∑ i : Fin n, F (succCoord n i) := by
  calc
    (∑ u : ZMod (n + 1), F u) =
        ∑ i : Fin (n + 1), F (ZMod.finEquiv (n + 1) i) := by
      exact (Equiv.sum_comp (ZMod.finEquiv (n + 1)).toEquiv F).symm
    _ = F (ZMod.finEquiv (n + 1) 0) +
        ∑ i : Fin n, F (ZMod.finEquiv (n + 1) i.succ) := by
      exact Fin.sum_univ_succ _
    _ = F 0 + ∑ i : Fin n, F (succCoord n i) := by
      rfl

/-- Split a cyclic sum into its zero term and its 292 nonzero terms. -/
theorem sum_cyc_eq_zero_add_coord (F : Cyc → ZMod 587) :
    (∑ u : Cyc, F u) = F 0 + ∑ i : Fin 292, F (coord i) := by
  exact sum_zmod_succ_eq_zero_add_coord F

/-- A sum over the nonzero coordinates can be extended to the whole cycle
when its zero summand vanishes. -/
theorem sum_coord_eq_sum_cyc_of_zero
    (F : Cyc → ZMod 587) (hF : F 0 = 0) :
    (∑ i : Fin 292, F (coord i)) = ∑ u : Cyc, F u := by
  rw [sum_cyc_eq_zero_add_coord, hF, zero_add]

/-- Cyclic translation does not change a finite sum. -/
theorem sum_add_right (F : Cyc → ZMod 587) (a : Cyc) :
    (∑ u : Cyc, F (u + a)) = ∑ u : Cyc, F u := by
  simpa using Equiv.sum_comp (Equiv.addRight a) F

/-- Reindex a shifted product by the translation `v ↦ x + v`. -/
theorem sum_shifted_product (f g : Cyc → ZMod 587) (x z : Cyc) :
    (∑ v : Cyc, f (x + v) * g (v + z)) =
      ∑ u : Cyc, f u * g (u + (z - x)) := by
  let H : Cyc → ZMod 587 := fun u ↦ f u * g (u + (z - x))
  calc
    (∑ v : Cyc, f (x + v) * g (v + z)) =
        ∑ v : Cyc, H (x + v) := by
      apply Fintype.sum_congr
      intro v
      dsimp [H]
      congr 2
      ring
    _ = ∑ u : Cyc, H u := by
      exact Equiv.sum_comp (Equiv.addLeft x) H
    _ = ∑ u : Cyc, f u * g (u + (z - x)) := rfl

/-- The product of two finite differences is the difference of two cyclic
correlations.  The remaining translated `g`-sums cancel. -/
theorem sum_difference_products (f g : Cyc → ZMod 587) (x z : Cyc) :
    (∑ v : Cyc, (f (x + v) - f x) * (g (v + z) - g v)) =
      (∑ u : Cyc, f u * g (u + (z - x))) -
        ∑ u : Cyc, f u * g (u + (-x)) := by
  calc
    (∑ v : Cyc, (f (x + v) - f x) * (g (v + z) - g v)) =
        (∑ v : Cyc, f (x + v) * g (v + z)) -
          (∑ v : Cyc, f (x + v) * g v) -
          f x * (∑ v : Cyc, g (v + z)) +
          f x * (∑ v : Cyc, g v) := by
      simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      ring
    _ = (∑ v : Cyc, f (x + v) * g (v + z)) -
          (∑ v : Cyc, f (x + v) * g v) := by
      rw [sum_add_right g z]
      ring
    _ = (∑ u : Cyc, f u * g (u + (z - x))) -
          ∑ u : Cyc, f u * g (u + (-x)) := by
      rw [sum_shifted_product f g x z]
      simpa using congrArg
        (fun q : ZMod 587 ↦
          (∑ u : Cyc, f u * g (u + (z - x))) - q)
        (sum_shifted_product f g x 0)

/-- A cyclic correlation inverse induces an inverse for the reduced
difference matrices. -/
theorem differenceMatrix_mul_eq_one
    (f g : Cyc → ZMod 587)
    (hcorr : ∀ d : Cyc,
      (∑ u : Cyc, f u * g (u + d)) = if d = 0 then 1 else 0) :
    differenceMatrix f * differenceMatrix g = 1 := by
  ext i k
  rw [Matrix.mul_apply]
  let F : Cyc → ZMod 587 := fun v ↦
    (f (coord i + v) - f (coord i)) *
      (g (v + coord k) - g v)
  have hFzero : F 0 = 0 := by
    simp [F]
  change (∑ j : Fin 292, F (coord j)) =
    (1 : Matrix (Fin 292) (Fin 292) (ZMod 587)) i k
  rw [sum_coord_eq_sum_cyc_of_zero F hFzero]
  change (∑ v : Cyc,
      (f (coord i + v) - f (coord i)) *
        (g (v + coord k) - g v)) = _
  rw [sum_difference_products, hcorr, hcorr]
  have hneg : -(coord i) ≠ 0 := neg_ne_zero.mpr (coord_ne_zero i)
  rw [if_neg hneg, sub_zero]
  by_cases hik : i = k
  · subst k
    simp
  · have hcoords : coord k - coord i ≠ 0 := by
      rw [sub_ne_zero]
      exact fun h ↦ hik (coord_injective h.symm)
    rw [if_neg hcoords]
    simp [hik]

end Fermat.FiveHundredEightySeven.CircularUnitCyclic
