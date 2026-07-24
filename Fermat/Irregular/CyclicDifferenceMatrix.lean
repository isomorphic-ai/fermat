import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Reduced difference matrices on a finite cycle

Write a cyclic group of order `n + 1` as `ZMod (n + 1)`, and enumerate its
nonzero elements by

`coord i = i + 1`, for `i : Fin n`.

For a function `h` from the cycle to a commutative ring, its reduced
difference matrix is

`D_h(i,j) = h(coord i + coord j) - h(coord i)`.

The main theorem packages the compression used by the circular-unit
certificates in this repository. If `f` and `g` have delta cyclic
correlation

`∑ u, f u * g (u + d) = if d = 0 then 1 else 0`,

then `D_f * D_g = 1`. Consequently `D_f` is nonsingular over every
nontrivial commutative coefficient ring.

The parameter `n` is the number of nonzero coordinates; the cycle itself
has length `n + 1`.
-/

namespace Fermat.Irregular.CyclicDifferenceMatrix

open scoped BigOperators Matrix

/-- The cyclic group with one zero coordinate and `n` nonzero
coordinates. -/
abbrev Cyc (n : ℕ) := ZMod (n + 1)

/-- Enumeration `1, ..., n` of the nonzero elements of `ZMod (n + 1)`. -/
def coord (n : ℕ) [NeZero (n + 1)] (i : Fin n) : Cyc n :=
  ZMod.finEquiv (n + 1) i.succ

/-- The reduced difference matrix attached to a function on the cycle. -/
def differenceMatrix (n : ℕ) [NeZero (n + 1)]
    {R : Type*} [CommRing R] (h : Cyc n → R) :
    Matrix (Fin n) (Fin n) R :=
  fun i j ↦ h (coord n i + coord n j) - h (coord n i)

/-- The nonzero-coordinate enumeration is injective. -/
theorem coord_injective (n : ℕ) [NeZero (n + 1)] :
    Function.Injective (coord n) := by
  intro i j hij
  apply Fin.succ_injective
  exact (ZMod.finEquiv (n + 1)).injective hij

/-- Every enumerated coordinate is nonzero. -/
theorem coord_ne_zero (n : ℕ) [NeZero (n + 1)] (i : Fin n) :
    coord n i ≠ 0 := by
  intro hi
  have : i.succ = (0 : Fin (n + 1)) :=
    (ZMod.finEquiv (n + 1)).injective (by
      change ZMod.finEquiv (n + 1) i.succ = 0 at hi
      simpa only [map_zero] using hi)
  exact Fin.succ_ne_zero i this

/-- Split a sum over the cycle into its zero term and the `n` enumerated
nonzero terms. -/
theorem sum_cyc_eq_zero_add_coord
    {n : ℕ} [NeZero (n + 1)] {A : Type*} [AddCommMonoid A]
    (F : Cyc n → A) :
    (∑ u : Cyc n, F u) =
      F 0 + ∑ i : Fin n, F (coord n i) := by
  calc
    (∑ u : Cyc n, F u) =
        ∑ i : Fin (n + 1), F (ZMod.finEquiv (n + 1) i) := by
      exact (Equiv.sum_comp (ZMod.finEquiv (n + 1)).toEquiv F).symm
    _ = F (ZMod.finEquiv (n + 1) 0) +
        ∑ i : Fin n, F (ZMod.finEquiv (n + 1) i.succ) := by
      exact Fin.sum_univ_succ _
    _ = F 0 + ∑ i : Fin n, F (coord n i) := by
      rfl

/-- A sum over nonzero coordinates extends to the whole cycle when its
zero summand vanishes. -/
theorem sum_coord_eq_sum_cyc_of_zero
    {n : ℕ} [NeZero (n + 1)] {A : Type*} [AddCommMonoid A]
    (F : Cyc n → A) (hF : F 0 = 0) :
    (∑ i : Fin n, F (coord n i)) = ∑ u : Cyc n, F u := by
  rw [sum_cyc_eq_zero_add_coord, hF, zero_add]

/-- Cyclic translation does not change a finite sum. -/
theorem sum_add_right
    {n : ℕ} [NeZero (n + 1)] {A : Type*} [AddCommMonoid A]
    (F : Cyc n → A) (a : Cyc n) :
    (∑ u : Cyc n, F (u + a)) = ∑ u : Cyc n, F u := by
  simpa using Equiv.sum_comp (Equiv.addRight a) F

/-- Reindex a shifted product by the translation `v ↦ x + v`. -/
theorem sum_shifted_product
    {n : ℕ} [NeZero (n + 1)] {R : Type*} [CommRing R]
    (f g : Cyc n → R) (x z : Cyc n) :
    (∑ v : Cyc n, f (x + v) * g (v + z)) =
      ∑ u : Cyc n, f u * g (u + (z - x)) := by
  let H : Cyc n → R := fun u ↦ f u * g (u + (z - x))
  calc
    (∑ v : Cyc n, f (x + v) * g (v + z)) =
        ∑ v : Cyc n, H (x + v) := by
      apply Fintype.sum_congr
      intro v
      dsimp [H]
      congr 2
      ring
    _ = ∑ u : Cyc n, H u := by
      exact Equiv.sum_comp (Equiv.addLeft x) H
    _ = ∑ u : Cyc n, f u * g (u + (z - x)) := rfl

/-- A product of finite differences is a difference of correlations. -/
theorem sum_difference_products
    {n : ℕ} [NeZero (n + 1)] {R : Type*} [CommRing R]
    (f g : Cyc n → R) (x z : Cyc n) :
    (∑ v : Cyc n, (f (x + v) - f x) * (g (v + z) - g v)) =
      (∑ u : Cyc n, f u * g (u + (z - x))) -
        ∑ u : Cyc n, f u * g (u + (-x)) := by
  calc
    (∑ v : Cyc n, (f (x + v) - f x) * (g (v + z) - g v)) =
        (∑ v : Cyc n, f (x + v) * g (v + z)) -
          (∑ v : Cyc n, f (x + v) * g v) -
          f x * (∑ v : Cyc n, g (v + z)) +
          f x * (∑ v : Cyc n, g v) := by
      simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      ring
    _ = (∑ v : Cyc n, f (x + v) * g (v + z)) -
          (∑ v : Cyc n, f (x + v) * g v) := by
      rw [sum_add_right g z]
      ring
    _ = (∑ u : Cyc n, f u * g (u + (z - x))) -
          ∑ u : Cyc n, f u * g (u + (-x)) := by
      rw [sum_shifted_product f g x z]
      simpa using congrArg
        (fun q : R ↦
          (∑ u : Cyc n, f u * g (u + (z - x))) - q)
        (sum_shifted_product f g x 0)

/-- A delta cyclic correlation induces an inverse for the reduced
difference matrices. -/
theorem differenceMatrix_mul_eq_one
    {n : ℕ} [NeZero (n + 1)] {R : Type*} [CommRing R]
    (f g : Cyc n → R)
    (hcorr : ∀ d : Cyc n,
      (∑ u : Cyc n, f u * g (u + d)) = if d = 0 then 1 else 0) :
    differenceMatrix n f * differenceMatrix n g = 1 := by
  ext i k
  rw [Matrix.mul_apply]
  let F : Cyc n → R := fun v ↦
    (f (coord n i + v) - f (coord n i)) *
      (g (v + coord n k) - g v)
  have hFzero : F 0 = 0 := by
    simp [F]
  change (∑ j : Fin n, F (coord n j)) =
    (1 : Matrix (Fin n) (Fin n) R) i k
  rw [sum_coord_eq_sum_cyc_of_zero F hFzero]
  change (∑ v : Cyc n,
      (f (coord n i + v) - f (coord n i)) *
        (g (v + coord n k) - g v)) = _
  rw [sum_difference_products, hcorr, hcorr]
  have hneg : -(coord n i) ≠ 0 := neg_ne_zero.mpr (coord_ne_zero n i)
  rw [if_neg hneg, sub_zero]
  by_cases hik : i = k
  · subst k
    simp
  · have hcoords : coord n k - coord n i ≠ 0 := by
      rw [sub_ne_zero]
      exact fun h ↦ hik ((coord_injective n) h.symm)
    rw [if_neg hcoords]
    simp [hik]

/-- A delta cyclic correlation makes the reduced difference matrix
nonsingular. -/
theorem differenceMatrix_det_ne_zero
    {n : ℕ} [NeZero (n + 1)] {R : Type*}
    [CommRing R] [Nontrivial R]
    (f g : Cyc n → R)
    (hcorr : ∀ d : Cyc n,
      (∑ u : Cyc n, f u * g (u + d)) = if d = 0 then 1 else 0) :
    (differenceMatrix n f).det ≠ 0 := by
  intro hzero
  have hdet := congrArg Matrix.det
    (differenceMatrix_mul_eq_one f g hcorr)
  rw [Matrix.det_mul, hzero, zero_mul, Matrix.det_one] at hdet
  exact zero_ne_one hdet

end Fermat.Irregular.CyclicDifferenceMatrix
