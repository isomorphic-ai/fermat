import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring

/-!
# Basis-free character projection of finite-group differences

A phase on a finite abelian group gives a difference operator
`phase (x * a) - phase x`. Projecting its complete orbit against an inverse
character always factors as

`phase Fourier scalar * intrinsic character moment`.

This is the generator-free form of the cyclic Fourier identity used by the
selective circular-unit certificates. It also explains why deleting one
orbit coordinate is harmless: subtracting its character weight changes the
detector by the total sum of a difference column, which is zero.
-/

open scoped BigOperators

namespace Fermat.Irregular.AuxiliaryResidueChannels

noncomputable section

variable {G I R : Type*} [CommGroup G] [Fintype G]
  [Fintype I] [CommRing R]

/-- The inverse-character scalar of a phase on a finite group. -/
def orbitScalar (chi : G →* Rˣ) (phase : G → R) : R :=
  ∑ x : G, phase x * ((chi x)⁻¹ : Rˣ)

/-- The intrinsic character moment of a coefficient vector. -/
def characterChannel (chi : G →* Rˣ) (node : I → G)
    (e : I → R) : R :=
  ∑ i : I, ((chi (node i) : R) - 1) * e i

/-- Fourier projection of the full orbit of a difference phase. -/
def orbitDetector (chi : G →* Rˣ) (phase : G → R)
    (node : I → G) (e : I → R) : R :=
  ∑ x : G, (((chi x)⁻¹ : Rˣ) : R) *
    ∑ i : I, (phase (x * node i) - phase x) * e i

/-- The full-orbit detector with its weight normalized to vanish at one
omitted base coordinate. -/
def deletedOrbitDetector (chi : G →* Rˣ) (phase : G → R)
    (base : G) (node : I → G) (e : I → R) : R :=
  ∑ x : G,
    ((((chi x)⁻¹ : Rˣ) : R) - (((chi base)⁻¹ : Rˣ) : R)) *
      ∑ i : I, (phase (x * node i) - phase x) * e i

private theorem sum_phase_mul_inverseCharacter_shift
    (chi : G →* Rˣ) (phase : G → R) (a : G) :
    (∑ x : G, (((chi x)⁻¹ : Rˣ) : R) * phase (x * a)) =
      (chi a : R) *
        ∑ x : G, (((chi x)⁻¹ : Rˣ) : R) * phase x := by
  let F : G → R := fun x ↦ (((chi x)⁻¹ : Rˣ) : R) * phase (x * a)
  let H : G → R := fun y ↦
    (chi a : R) * ((((chi y)⁻¹ : Rˣ) : R) * phase y)
  calc
    (∑ x : G, (((chi x)⁻¹ : Rˣ) : R) * phase (x * a)) =
        ∑ x : G, F x := rfl
    _ = ∑ y : G, F (y * a⁻¹) := by
      simpa using (Equiv.sum_comp (Equiv.mulRight a⁻¹) F).symm
    _ = ∑ y : G, H y := by
      apply Finset.sum_congr rfl
      intro y _
      simp only [F, H, inv_mul_cancel_right]
      rw [map_mul, map_inv]
      change ((((chi y * (chi a)⁻¹)⁻¹ : Rˣ) : R) * phase y) = _
      rw [mul_inv_rev, inv_inv]
      simp only [Units.val_mul]
      ring
    _ = (chi a : R) *
        ∑ x : G, (((chi x)⁻¹ : Rˣ) : R) * phase x := by
      simp only [H, Finset.mul_sum]

private theorem sum_orbitDifference_eq_zero
    (phase : G → R) (a : G) :
    (∑ x : G, (phase (x * a) - phase x)) = 0 := by
  have hshift : (∑ x : G, phase (x * a)) = ∑ x : G, phase x := by
    simpa using Equiv.sum_comp (Equiv.mulRight a) phase
  calc
    (∑ x : G, (phase (x * a) - phase x)) =
        (∑ x : G, phase (x * a)) - ∑ x : G, phase x :=
      by
        exact (Finset.sum_sub_distrib (s := Finset.univ)
          (fun x : G ↦ phase (x * a)) phase)
    _ = 0 := by rw [hshift, sub_self]

/-- Subtracting the character value at one omitted orbit point does not
change the detector. -/
theorem deletedOrbitDetector_eq_orbitDetector
    (chi : G →* Rˣ) (phase : G → R) (base : G)
    (node : I → G) (e : I → R) :
    deletedOrbitDetector chi phase base node e =
      orbitDetector chi phase node e := by
  classical
  let F : G → R := fun x ↦
    ∑ i : I, (phase (x * node i) - phase x) * e i
  have htotal : (∑ x : G, F x) = 0 := by
    dsimp only [F]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i _
    rw [← Finset.sum_mul]
    exact mul_eq_zero_of_left
      (sum_orbitDifference_eq_zero (G := G) phase (node i)) (e i)
  change
    (∑ x : G,
      ((((chi x)⁻¹ : Rˣ) : R) - (((chi base)⁻¹ : Rˣ) : R)) * F x) =
      ∑ x : G, (((chi x)⁻¹ : Rˣ) : R) * F x
  calc
    _ = (∑ x : G, (((chi x)⁻¹ : Rˣ) : R) * F x) -
        ∑ x : G, (((chi base)⁻¹ : Rˣ) : R) * F x := by
      simp_rw [sub_mul]
      exact (Finset.sum_sub_distrib (s := Finset.univ)
        (fun x : G ↦ (((chi x)⁻¹ : Rˣ) : R) * F x)
        (fun x : G ↦ (((chi base)⁻¹ : Rˣ) : R) * F x))
    _ = (∑ x : G, (((chi x)⁻¹ : Rˣ) : R) * F x) -
        (((chi base)⁻¹ : Rˣ) : R) * ∑ x : G, F x := by
      rw [Finset.mul_sum]
    _ = _ := by rw [htotal, mul_zero, sub_zero]

/-- A full-orbit residue detector is a q-dependent scalar times the
intrinsic character channel. This statement uses no cyclic generator. -/
theorem orbitDetector_eq_scalar_mul_characterChannel
    (chi : G →* Rˣ) (phase : G → R) (node : I → G) (e : I → R) :
    orbitDetector chi phase node e =
      orbitScalar chi phase * characterChannel chi node e := by
  classical
  simp only [orbitDetector, orbitScalar, characterChannel]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ x : G, (((chi x)⁻¹ : Rˣ) : R) *
        ((phase (x * node i) - phase x) * e i)) =
        (∑ x : G, (((chi x)⁻¹ : Rˣ) : R) *
          (phase (x * node i) - phase x)) * e i := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = ((chi (node i) : R) *
          ∑ x : G, (((chi x)⁻¹ : Rˣ) : R) * phase x -
        ∑ x : G, (((chi x)⁻¹ : Rˣ) : R) * phase x) * e i := by
      congr 1
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      rw [sum_phase_mul_inverseCharacter_shift chi phase (node i)]
    _ = (∑ x : G, phase x * (((chi x)⁻¹ : Rˣ) : R)) *
        (((chi (node i) : R) - 1) * e i) := by
      have hcomm :
          (∑ x : G, (((chi x)⁻¹ : Rˣ) : R) * phase x) =
            ∑ x : G, phase x * (((chi x)⁻¹ : Rˣ) : R) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      rw [hcomm]
      ring

end

end Fermat.Irregular.AuxiliaryResidueChannels
