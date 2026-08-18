/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The normalized continuous H² readout on the cyclic quotient at 59

For the finite discrete cyclic group `C_59`, summing a homogeneous
two-cocycle once around the chosen generator kills every continuous
two-boundary.  It therefore descends to Mathlib's actual continuous
homology, and the explicit carry class reads as exactly `1`.

This supplies a genuine normalized scalar readout on
`H²(C_59, F_59)`, together with a canonical split generator line.  It is
the finite-quotient normalization which a future local invariant or
inflation comparison must preserve.  It is not itself an invariant on the
absolute Galois group and makes no Hilbert-symbol claim.
-/
import Fermat.Conservation.CyclicCarryH2Class59

noncomputable section

open CategoryTheory ContinuousCohomology
open Fermat.Conservation.ContinuousKummerTateCupRaw
open Fermat.Conservation.ContinuousKummerTateCup.Nominal

namespace Fermat.Conservation.ContinuousCyclicH2Readout59

open Fermat.Conservation.CyclicCarryH2Class59
open Fermat.Conservation.DiscreteToContinuousH2
open Fermat.Conservation.FiniteCyclicH2Generator59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩
local instance : Fintype CyclicGroup59 := inferInstanceAs (Fintype (ZMod 59))
local instance : TopologicalSpace (ZMod 59) := ⊥
local instance : DiscreteTopology (ZMod 59) := ⟨rfl⟩
local instance : TopologicalSpace CyclicGroup59 := ⊥
local instance : DiscreteTopology CyclicGroup59 := ⟨rfl⟩

/-- One summand of the generator-loop evaluation of a homogeneous cycle. -/
def cyclicCycleValue59
    (z : Cycle continuousCoefficients59 2 3)
    (h : CyclicGroup59) : ZMod 59 :=
  show ZMod 59 from
    twoValue z.cochain.val 1 generator59 (generator59 * h)

/-- Sum a continuous homogeneous two-cycle once around the chosen generator
of `C_59`. -/
def cyclicCycleSum59 :
    Cycle continuousCoefficients59 2 3 →ₗ[ZMod 59] ZMod 59 where
  toFun z := ∑ h : CyclicGroup59, cyclicCycleValue59 z h
  map_add' x y := by
    have hvalue (h : CyclicGroup59) :
        cyclicCycleValue59 (x + y) h =
          cyclicCycleValue59 x h + cyclicCycleValue59 y h := by
      rfl
    simp_rw [hvalue]
    rw [Finset.sum_add_distrib]
  map_smul' a x := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rfl

/-- The explicit continuous carry cycle has normalized generator-loop sum
equal to one. -/
theorem cyclicCycleSum59_continuousCarryCycle59 :
    cyclicCycleSum59 continuousCarryCycle59 = 1 := by
  change (∑ h : CyclicGroup59,
    carryCocycle59 (generator59, h)) = 1
  exact sum_carryCocycle59_generator59

/-- The same generator-loop sum telescopes to zero on every continuous
homogeneous two-boundary. -/
theorem sum_continuousBoundary_generator59
    (b : Cochain continuousCoefficients59 1) :
    ∑ h : CyclicGroup59,
      twoValue (differential continuousCoefficients59 1 2 b).val
        1 generator59 (generator59 * h) = 0 := by
  let b' : CyclicGroup59 → coefficients59 := fun g ↦ oneValue b.val 1 g
  have hpoint (h : CyclicGroup59) :
      twoValue (differential continuousCoefficients59 1 2 b).val
          1 generator59 (generator59 * h) =
        (groupCohomology.d₁₂ coefficients59).hom b'
          (generator59, h) := by
    rw [differential_val, continuousOneDifferential_apply]
    change oneValue b.val generator59 (generator59 * h) -
        (oneValue b.val 1 (generator59 * h) -
          oneValue b.val 1 generator59) = _
    have hinv := oneValue_invariant b.val generator59
      generator59 (generator59 * h)
    have hinv' : oneValue b.val 1 h =
        oneValue b.val generator59 (generator59 * h) := by
      simpa using hinv
    rw [← hinv']
    simp only [groupCohomology.d₁₂_hom_apply]
    change oneValue b.val 1 h -
        (oneValue b.val 1 (generator59 * h) -
          oneValue b.val 1 generator59) =
      oneValue b.val 1 h - oneValue b.val 1 (generator59 * h) +
        oneValue b.val 1 generator59
    abel
  simp_rw [hpoint]
  exact sum_discreteBoundary_generator59 b'

/-- Hence the cycle sum vanishes on the kernel of the honest continuous
homology projection. -/
theorem cyclicCycleSum59_eq_zero_of_h2Projection_eq_zero
    (z : Cycle continuousCoefficients59 2 3)
    (hz : h2Projection continuousCoefficients59 z = 0) :
    cyclicCycleSum59 z = 0 := by
  obtain ⟨b, hb⟩ :=
    (h2Projection_eq_zero_iff continuousCoefficients59 z).mp hz
  change (∑ h : CyclicGroup59,
    twoValue z.cochain.val 1 generator59 (generator59 * h)) = 0
  have hbval := congrArg Cochain.val hb
  rw [differential_val, cycleCochain_val] at hbval
  rw [← hbval]
  exact sum_continuousBoundary_generator59 b

theorem ker_h2Projection_le_ker_cyclicCycleSum59 :
    LinearMap.ker (h2Projection continuousCoefficients59) ≤
      LinearMap.ker cyclicCycleSum59 := by
  intro z hz
  rw [LinearMap.mem_ker] at hz ⊢
  exact cyclicCycleSum59_eq_zero_of_h2Projection_eq_zero z hz

theorem h2Projection_surjective59 :
    Function.Surjective (h2Projection continuousCoefficients59) :=
  cycleToHomology_surjective continuousCoefficients59 2 3
    ((ComplexShape.up ℕ).next_eq' (by simp))

/-- The generator-loop sum descended through the actual continuous
homology quotient. -/
noncomputable def continuousCyclicH2Readout59 :
    Homology continuousCoefficients59 2 →ₗ[ZMod 59] ZMod 59 :=
  ((LinearMap.ker (h2Projection continuousCoefficients59)).liftQ
      cyclicCycleSum59 ker_h2Projection_le_ker_cyclicCycleSum59).comp
    ((h2Projection continuousCoefficients59).quotKerEquivOfSurjective
      h2Projection_surjective59).symm.toLinearMap

/-- The descended readout is computed by the original cycle sum on every
closed representative. -/
@[simp]
theorem continuousCyclicH2Readout59_h2Projection
    (z : Cycle continuousCoefficients59 2 3) :
    continuousCyclicH2Readout59
        (h2Projection continuousCoefficients59 z) =
      cyclicCycleSum59 z := by
  change ((LinearMap.ker (h2Projection continuousCoefficients59)).liftQ
      cyclicCycleSum59 ker_h2Projection_le_ker_cyclicCycleSum59)
    (((h2Projection continuousCoefficients59).quotKerEquivOfSurjective
      h2Projection_surjective59).symm
        (h2Projection continuousCoefficients59 z)) = _
  rw [(h2Projection continuousCoefficients59).quotKerEquivOfSurjective_symm_apply]
  exact Submodule.liftQ_apply _ _ _

/-- The same normalized readout on Mathlib's exposed actual continuous
cohomology object. -/
noncomputable def actualContinuousCyclicH2Readout59 :
    (continuousCohomology (ZMod 59) CyclicGroup59 2).obj
        continuousCoefficients59 →ₗ[ZMod 59] ZMod 59 :=
  continuousCyclicH2Readout59.comp
    (homologyLinearEquiv continuousCoefficients59 2).symm.toLinearMap

/-- Normalization: the genuine continuous carry class reads exactly one. -/
@[simp]
theorem actualContinuousCyclicH2Readout59_continuousCarryH2Class59 :
    actualContinuousCyclicH2Readout59 continuousCarryH2Class59 = 1 := by
  change continuousCyclicH2Readout59
      (h2Projection continuousCoefficients59 continuousCarryCycle59) = 1
  rw [continuousCyclicH2Readout59_h2Projection]
  exact cyclicCycleSum59_continuousCarryCycle59

/-- The canonical scalar multiples of the continuous carry class. -/
def actualContinuousCyclicH2Generator59 :
    ZMod 59 →ₗ[ZMod 59]
      (continuousCohomology (ZMod 59) CyclicGroup59 2).obj
        continuousCoefficients59 where
  toFun a := a • continuousCarryH2Class59
  map_add' a b := add_smul a b continuousCarryH2Class59
  map_smul' a b := by simp [mul_smul]

/-- Readout and generator are an exact split pair on every scalar. -/
@[simp]
theorem actualContinuousCyclicH2Readout59_generator59 (a : ZMod 59) :
    actualContinuousCyclicH2Readout59
        (actualContinuousCyclicH2Generator59 a) = a := by
  simp [actualContinuousCyclicH2Generator59]

theorem actualContinuousCyclicH2Readout59_surjective :
    Function.Surjective actualContinuousCyclicH2Readout59 :=
  fun a ↦ ⟨actualContinuousCyclicH2Generator59 a, by simp⟩

theorem actualContinuousCyclicH2Generator59_injective :
    Function.Injective actualContinuousCyclicH2Generator59 :=
  Function.LeftInverse.injective
    actualContinuousCyclicH2Readout59_generator59

end Fermat.Conservation.ContinuousCyclicH2Readout59
