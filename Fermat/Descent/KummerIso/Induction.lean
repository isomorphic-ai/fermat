import Fermat.Descent.KummerIso.DeepRatio

/-!
# Removing the weights after corrected unit extraction

The weighted cyclotomic induction produces

`ε₁ * x ^ p + ε₂ * y ^ p = ε₃ * (π ^ m * z) ^ p`.

If the displayed ratio `ε₁ / ε₂` is a `p`-th power `v ^ p`, multiplying
`x` by `v` and dividing the equation by `ε₂` gives the unweighted equation

`(v * x) ^ p + y ^ p = (ε₃ / ε₂) * (π ^ m * z) ^ p`.

The first section proves this over an arbitrary commutative ring.  The
cyclotomic corollary then composes the construction with
`DeepRatio.regularUnitRatio_isPower`.  Its depth hypothesis remains an
explicit premise; this file does not assert or weaken it.
-/

namespace Fermat.KummerIso

/-- The unweighted equation consumed by the next induction step.

The right-hand coefficient remains a unit.  All three nondivisibility facts
from the weighted equation are retained, although the historical private
step needs only those for `y` and `z`. -/
structure UnweightedSolution (R : Type*) [CommRing R]
    (p m : ℕ) (π : R) where
  x : R
  y : R
  z : R
  coefficient : Rˣ
  not_pi_dvd_x : ¬π ∣ x
  not_pi_dvd_y : ¬π ∣ y
  not_pi_dvd_z : ¬π ∣ z
  equation :
    x ^ p + y ^ p =
      (coefficient : R) * (π ^ m * z) ^ p

namespace Induction

variable {R : Type*} [CommRing R]
variable {p m : ℕ} {π : R}

/-- Absorb a certified `p`-th root of the exact weight ratio into `x`.

The assignments and coefficient are exactly those in the private
`VandiverCriterion` induction step:

* `x := v * w.x`;
* `y := w.y`;
* `z := w.z`;
* `coefficient := w.ε₃ / w.ε₂`.
-/
def unweight (w : WeightedSolution R p m π) (v : Rˣ)
    (hroot : w.unitRatio = v ^ p) :
    UnweightedSolution R p m π where
  x := v * w.x
  y := w.y
  z := w.z
  coefficient := w.ε₃ / w.ε₂
  not_pi_dvd_x := by
    intro hdiv
    exact w.not_pi_dvd_x (v.isUnit.dvd_mul_left.mp hdiv)
  not_pi_dvd_y := w.not_pi_dvd_y
  not_pi_dvd_z := w.not_pi_dvd_z
  equation := by
    change w.ε₁ / w.ε₂ = v ^ p at hroot
    rw [mul_pow, ← Units.val_pow_eq_pow_val, ← hroot,
      ← w.ε₂.isUnit.mul_right_inj, mul_add,
      ← mul_assoc, ← Units.val_mul, mul_div_cancel,
      ← mul_assoc, ← Units.val_mul, mul_div_cancel]
    exact w.equation

@[simp]
theorem unweight_x (w : WeightedSolution R p m π) (v : Rˣ)
    (hroot : w.unitRatio = v ^ p) :
    (unweight w v hroot).x = (v : R) * w.x :=
  rfl

@[simp]
theorem unweight_y (w : WeightedSolution R p m π) (v : Rˣ)
    (hroot : w.unitRatio = v ^ p) :
    (unweight w v hroot).y = w.y :=
  rfl

@[simp]
theorem unweight_z (w : WeightedSolution R p m π) (v : Rˣ)
    (hroot : w.unitRatio = v ^ p) :
    (unweight w v hroot).z = w.z :=
  rfl

@[simp]
theorem unweight_coefficient
    (w : WeightedSolution R p m π) (v : Rˣ)
    (hroot : w.unitRatio = v ^ p) :
    (unweight w v hroot).coefficient = w.ε₃ / w.ε₂ :=
  rfl

/-- Existential form of `unweight`, convenient for induction clients. -/
theorem exists_unweightedSolution_of_unitRatio_eq_pow
    (w : WeightedSolution R p m π) (v : Rˣ)
    (hroot : w.unitRatio = v ^ p) :
    Nonempty (UnweightedSolution R p m π) :=
  ⟨unweight w v hroot⟩

/-! ## Cyclotomic correction corollary -/

open scoped NumberField

open Fermat.GenericIrregular.LemmaTwo
open Fermat.Irregular.VandiverLemmaTwoCore

variable {K : Type} [Fact p.Prime]
  [Field K] [NumberField K] [NumberField.IsCMField K]
  [IsCyclotomicExtension {p} ℚ K]

/-- After the explicit depth premise for the regular-style ratio, every
remaining unit-extraction and unweighting step is closed.

`DeepRatio.regularUnitRatio_isPower` routes through
`UnitExtraction.isPower_of_unitSystem_of_noBernoulliObstruction`, hence
through the normalized automorphism in `Correction`. -/
theorem exists_unweightedSolution_of_regularUnitRatioDeep
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (system : LemmaTwoUnitSystem K p)
    (hno : NoBernoulliObstruction p)
    (w : WeightedSolution (𝓞 K) p m
      ((hζ.unit' : 𝓞 K) - 1))
    (hdeep : DeepRatio.RegularUnitRatioDeep hζ w) :
    Nonempty
      (UnweightedSolution (𝓞 K) p m
        ((hζ.unit' : 𝓞 K) - 1)) := by
  obtain ⟨v, hv⟩ :=
    DeepRatio.regularUnitRatio_isPower
      hp5 hζ system hno w hdeep
  exact ⟨unweight w v hv⟩

end Induction

end Fermat.KummerIso
