import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Cyclic compression of the exponent-491 circular-unit matrix

Let `Cyc = ZMod 245`.  A cyclic correlation inverse

`∑ u, f u * g (u + d) = δ(d,0)`

induces an inverse for the `244 × 244` reduced difference matrices

`D_h(i,j) = h(i+j) - h(i)`.

The proof extends the nonzero-coordinate sum by its vanishing zero term,
reindexes two cyclic sums by translation, and reduces each matrix entry to

`δ(coord k - coord i, 0) - δ(-coord i, 0) = δ(i,k)`.
-/

namespace Fermat.FourHundredNinetyOne.CircularUnitCyclic

open scoped BigOperators Matrix

/-- The real residue group has order `(491 - 1) / 2 = 245`. -/
abbrev Cyc := ZMod 245

private def succCoord (n : ℕ) [NeZero (n + 1)] (i : Fin n) : ZMod (n + 1) :=
  ZMod.finEquiv (n + 1) i.succ

/-- Enumeration of the nonzero elements of `ZMod 245`. -/
def coord (i : Fin 244) : Cyc :=
  succCoord 244 i

/-- The reduced difference matrix attached to a cyclic function. -/
def differenceMatrix (h : Cyc → ZMod 491) :
    Matrix (Fin 244) (Fin 244) (ZMod 491) :=
  fun i j ↦ h (coord i + coord j) - h (coord i)

/-- The nonzero-coordinate enumeration is injective. -/
theorem coord_injective : Function.Injective coord := by
  intro i j hij
  apply Fin.succ_injective
  exact (ZMod.finEquiv 245).injective hij

/-- Every enumerated coordinate is nonzero. -/
theorem coord_ne_zero (i : Fin 244) : coord i ≠ 0 := by
  intro hi
  have : i.succ = (0 : Fin 245) :=
    (ZMod.finEquiv 245).injective (by
      change ZMod.finEquiv 245 i.succ = 0 at hi
      simpa only [map_zero] using hi)
  exact Fin.succ_ne_zero i this

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

/-- Split a cyclic sum into its zero term and its 244 nonzero terms. -/
theorem sum_cyc_eq_zero_add_coord (F : Cyc → ZMod 491) :
    (∑ u : Cyc, F u) = F 0 + ∑ i : Fin 244, F (coord i) := by
  exact sum_zmod_succ_eq_zero_add_coord F

/-- A sum over nonzero coordinates extends to the whole cycle when the
zero summand vanishes. -/
theorem sum_coord_eq_sum_cyc_of_zero
    (F : Cyc → ZMod 491) (hF : F 0 = 0) :
    (∑ i : Fin 244, F (coord i)) = ∑ u : Cyc, F u := by
  rw [sum_cyc_eq_zero_add_coord, hF, zero_add]

/-- Cyclic translation does not change a finite sum. -/
theorem sum_add_right (F : Cyc → ZMod 491) (a : Cyc) :
    (∑ u : Cyc, F (u + a)) = ∑ u : Cyc, F u := by
  simpa using Equiv.sum_comp (Equiv.addRight a) F

/-- Reindex a shifted product by the translation `v ↦ x + v`. -/
theorem sum_shifted_product (f g : Cyc → ZMod 491) (x z : Cyc) :
    (∑ v : Cyc, f (x + v) * g (v + z)) =
      ∑ u : Cyc, f u * g (u + (z - x)) := by
  let H : Cyc → ZMod 491 := fun u ↦ f u * g (u + (z - x))
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

/-- A product of finite differences is a difference of correlations. -/
theorem sum_difference_products (f g : Cyc → ZMod 491) (x z : Cyc) :
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
        (fun q : ZMod 491 ↦
          (∑ u : Cyc, f u * g (u + (z - x))) - q)
        (sum_shifted_product f g x 0)

/-- A cyclic correlation inverse induces an inverse for the reduced
difference matrices. -/
theorem differenceMatrix_mul_eq_one
    (f g : Cyc → ZMod 491)
    (hcorr : ∀ d : Cyc,
      (∑ u : Cyc, f u * g (u + d)) = if d = 0 then 1 else 0) :
    differenceMatrix f * differenceMatrix g = 1 := by
  ext i k
  rw [Matrix.mul_apply]
  let F : Cyc → ZMod 491 := fun v ↦
    (f (coord i + v) - f (coord i)) *
      (g (v + coord k) - g v)
  have hFzero : F 0 = 0 := by
    simp [F]
  change (∑ j : Fin 244, F (coord j)) =
    (1 : Matrix (Fin 244) (Fin 244) (ZMod 491)) i k
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

end Fermat.FourHundredNinetyOne.CircularUnitCyclic
