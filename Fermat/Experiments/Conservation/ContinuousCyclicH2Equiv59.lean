/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The continuous cyclic H² readout at 59 is an equivalence

Every homogeneous continuous two-cycle on the finite discrete group `C₅₉`
has exact inhomogeneous coordinates, and transferring those coordinates back
recovers the original cycle.  The construction also sends every discrete
boundary to a continuous homogeneous boundary, complementing the reverse
implication already proved by the discrete-to-continuous bridge.

The known one-dimensional computation of discrete `H²(C₅₉, F₅₉)` then
shows that every actual continuous class is a scalar multiple of the carry
class.  Consequently the normalized generator-loop readout is bijective and
defines a linear equivalence with `ZMod 59`, whose inverse is exactly the
carry-generator map.
-/
import Fermat.Experiments.Conservation.ContinuousCyclicH2Readout59

noncomputable section

open CategoryTheory ContinuousCohomology
open Fermat.Conservation.ContinuousKummerTateCupRaw
open Fermat.Conservation.ContinuousKummerTateCup.Nominal

namespace Fermat.Conservation.ContinuousCyclicH2Equiv59

open Fermat.Conservation.CyclicCarryH2Class59
open Fermat.Conservation.DiscreteToContinuousH2
open Fermat.Conservation.FiniteCyclicH2Generator59
open Fermat.Conservation.ContinuousCyclicH2Readout59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩
local instance : Fintype CyclicGroup59 := inferInstanceAs (Fintype (ZMod 59))
local instance : TopologicalSpace (ZMod 59) := ⊥
local instance : DiscreteTopology (ZMod 59) := ⟨rfl⟩
local instance : TopologicalSpace CyclicGroup59 := ⊥
local instance : DiscreteTopology CyclicGroup59 := ⟨rfl⟩

/-- The nested continuous map underlying a homogeneous degree-three cochain. -/
private def threeValue59
    (f : ((homogeneousCochains (ZMod 59) CyclicGroup59).obj
      continuousCoefficients59).X 3) :
    C(CyclicGroup59, C(CyclicGroup59, C(CyclicGroup59,
      C(CyclicGroup59, ZMod 59)))) := by
  change {x : C(CyclicGroup59, C(CyclicGroup59, C(CyclicGroup59,
    C(CyclicGroup59, ZMod 59)))) // ∀ g : CyclicGroup59, _} at f
  exact f.1

/-- Pointwise form of the homogeneous degree-two cocycle equation. -/
private theorem continuousTwoCycle_identity59
    (f : ((homogeneousCochains (ZMod 59) CyclicGroup59).obj
      continuousCoefficients59).X 2)
    (hf : (((homogeneousCochains (ZMod 59) CyclicGroup59).obj
      continuousCoefficients59).d 2 3).hom f = 0)
    (w x y z : CyclicGroup59) :
    twoValue f x y z -
      (twoValue f w y z -
        (twoValue f w x z - twoValue f w x y)) = 0 := by
  have h := congrArg
    (fun q : ((homogeneousCochains (ZMod 59) CyclicGroup59).obj
      continuousCoefficients59).X 3 => threeValue59 q w x y z) hf
  exact h

/-- Diagonal invariance of a homogeneous degree-two cochain for the trivial
coefficient line. -/
private theorem twoValue_invariant59
    (f : ((homogeneousCochains (ZMod 59) CyclicGroup59).obj
      continuousCoefficients59).X 2)
    (a x y z : CyclicGroup59) :
    (continuousCoefficients59.ρ a).hom
        (twoValue f (a⁻¹ * x) (a⁻¹ * y) (a⁻¹ * z)) =
      twoValue f x y z := by
  change {q : C(CyclicGroup59, C(CyclicGroup59, C(CyclicGroup59, ZMod 59))) //
    ∀ g : CyclicGroup59, _} at f
  exact congrArg
    (fun q : C(CyclicGroup59, C(CyclicGroup59, C(CyclicGroup59, ZMod 59))) =>
      q x y z) (f.2 a)

/-- Evaluate a homogeneous continuous two-cycle in inhomogeneous coordinates. -/
def discreteTwoOfContinuous59
    (z : Cycle continuousCoefficients59 2 3) :
    CyclicGroup59 × CyclicGroup59 → coefficients59 :=
  fun gh ↦ twoValue z.cochain.val 1 gh.1 (gh.1 * gh.2)

/-- The inhomogeneous coordinates of a homogeneous cycle satisfy the
ordinary discrete cocycle equation. -/
theorem discreteTwoOfContinuous59_mem_cocycles₂
    (z : Cycle continuousCoefficients59 2 3) :
    discreteTwoOfContinuous59 z ∈
      groupCohomology.cocycles₂ coefficients59 := by
  rw [groupCohomology.mem_cocycles₂_def]
  intro g h k
  have hzval := congrArg Cochain.val z.isCycle
  rw [differential_val] at hzval
  have hz := continuousTwoCycle_identity59 z.cochain.val hzval
    1 g (g * h) ((g * h) * k)
  have hinv := twoValue_invariant59 z.cochain.val g g (g * h) ((g * h) * k)
  rw [show g⁻¹ * ((g * h) * k) = h * k by group] at hinv
  have hinv' : twoValue z.cochain.val 1 h (h * k) =
      twoValue z.cochain.val g (g * h) ((g * h) * k) := by
    simpa [trivialAction_action] using hinv
  change
    discreteTwoOfContinuous59 z (h, k) -
      discreteTwoOfContinuous59 z (g * h, k) +
      discreteTwoOfContinuous59 z (g, h * k) -
      discreteTwoOfContinuous59 z (g, h) = 0
  change
    twoValue z.cochain.val 1 h (h * k) -
      twoValue z.cochain.val 1 (g * h) ((g * h) * k) +
      twoValue z.cochain.val 1 g (g * (h * k)) -
      twoValue z.cochain.val 1 g (g * h) = 0
  rw [hinv']
  rw [show g * (h * k) = (g * h) * k by group]
  calc
    twoValue z.cochain.val g (g * h) ((g * h) * k) -
          twoValue z.cochain.val 1 (g * h) ((g * h) * k) +
          twoValue z.cochain.val 1 g ((g * h) * k) -
          twoValue z.cochain.val 1 g (g * h) =
        twoValue z.cochain.val g (g * h) ((g * h) * k) -
          (twoValue z.cochain.val 1 (g * h) ((g * h) * k) -
            (twoValue z.cochain.val 1 g ((g * h) * k) -
              twoValue z.cochain.val 1 g (g * h))) := by abel
    _ = 0 := hz

/-- Bundle the extracted inhomogeneous cocycle. -/
def discreteCocycleOfContinuous59
    (z : Cycle continuousCoefficients59 2 3) :
    groupCohomology.cocycles₂ coefficients59 :=
  ⟨discreteTwoOfContinuous59 z, discreteTwoOfContinuous59_mem_cocycles₂ z⟩

/-- Transferring the extracted inhomogeneous cocycle recovers the original
homogeneous cycle exactly. -/
theorem continuousCycleOfDiscrete_discreteCocycleOfContinuous59
    (z : Cycle continuousCoefficients59 2 3) :
    continuousCycleOfDiscrete (discreteCocycleOfContinuous59 z) = z := by
  apply Cycle.ext
  apply Cochain.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  apply ContinuousMap.ext
  intro w
  change twoValue z.cochain.val 1 (x⁻¹ * y)
      ((x⁻¹ * y) * (y⁻¹ * w)) = twoValue z.cochain.val x y w
  have hinv := twoValue_invariant59 z.cochain.val x x y w
  have hinv' : twoValue z.cochain.val 1 (x⁻¹ * y) (x⁻¹ * w) =
      twoValue z.cochain.val x y w := by
    simpa [trivialAction_action] using hinv
  rw [show (x⁻¹ * y) * (y⁻¹ * w) = x⁻¹ * w by group]
  exact hinv'

/-- The homogeneous degree-one cochain attached to an inhomogeneous
one-cochain. -/
private def rawHomogeneousOne59
    (b : CyclicGroup59 → coefficients59) :
    C(CyclicGroup59, C(CyclicGroup59, ZMod 59)) :=
  ⟨fun x ↦
    ⟨fun y ↦ b (x⁻¹ * y), continuous_of_discreteTopology⟩,
    continuous_of_discreteTopology⟩

/-- Bundle the homogeneous one-cochain and its diagonal invariance. -/
private def homogeneousOneOfDiscrete59
    (b : CyclicGroup59 → coefficients59) :
    ((homogeneousCochains (ZMod 59) CyclicGroup59).obj
      continuousCoefficients59).X 1 := by
  refine ⟨rawHomogeneousOne59 b, ?_⟩
  intro a
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  change b ((a⁻¹ * x)⁻¹ * (a⁻¹ * y)) = b (x⁻¹ * y)
  congr 1
  group

/-- The nominal continuous primitive attached to a discrete one-cochain. -/
private def continuousOneOfDiscrete59
    (b : CyclicGroup59 → coefficients59) :
    Cochain continuousCoefficients59 1 :=
  ⟨homogeneousOneOfDiscrete59 b⟩

/-- Pointwise compatibility of the discrete and homogeneous degree-one
differentials. -/
private theorem differential_continuousOneOfDiscrete59_apply
    (b : CyclicGroup59 → coefficients59) (x y z : CyclicGroup59) :
    twoValue (differential continuousCoefficients59 1 2
      (continuousOneOfDiscrete59 b)).val x y z =
      (groupCohomology.d₁₂ coefficients59).hom b
        (x⁻¹ * y, y⁻¹ * z) := by
  rw [differential_val, continuousOneDifferential_apply]
  simp only [groupCohomology.d₁₂_hom_apply]
  change b (y⁻¹ * z) - (b (x⁻¹ * z) - b (x⁻¹ * y)) =
    b (y⁻¹ * z) - b ((x⁻¹ * y) * (y⁻¹ * z)) + b (x⁻¹ * y)
  rw [show (x⁻¹ * y) * (y⁻¹ * z) = x⁻¹ * z by group]
  abel

/-- Every discrete two-boundary transfers to a continuous homogeneous
two-boundary.  Together with the existing reflection theorem, this closes
the boundary comparison in degree two. -/
theorem continuousBoundary_of_mem_discreteCoboundaries59
    (c : groupCohomology.cocycles₂ coefficients59)
    (hc : ⇑c ∈ groupCohomology.coboundaries₂ coefficients59) :
    ∃ b : Cochain continuousCoefficients59 1,
      differential continuousCoefficients59 1 2 b =
        cycleCochain continuousCoefficients59 2 3
          (continuousCycleOfDiscrete c) := by
  obtain ⟨b, hb⟩ := hc
  refine ⟨continuousOneOfDiscrete59 b, ?_⟩
  apply Cochain.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  apply ContinuousMap.ext
  intro z
  change twoValue (differential continuousCoefficients59 1 2
      (continuousOneOfDiscrete59 b)).val x y z =
    twoValue (cycleCochain continuousCoefficients59 2 3
      (continuousCycleOfDiscrete c)).val x y z
  rw [differential_continuousOneOfDiscrete59_apply]
  change (groupCohomology.d₁₂ coefficients59).hom b
      (x⁻¹ * y, y⁻¹ * z) = c (x⁻¹ * y, y⁻¹ * z)
  exact congrFun hb (x⁻¹ * y, y⁻¹ * z)

/-- The discrete-to-continuous cycle comparison is linear. -/
def continuousCycleOfDiscreteLinear59 :
    groupCohomology.cocycles₂ coefficients59 →ₗ[ZMod 59]
      Cycle continuousCoefficients59 2 3 where
  toFun := continuousCycleOfDiscrete
  map_add' c d := by
    apply Cycle.ext
    apply Cochain.ext
    rfl
  map_smul' a c := by
    apply Cycle.ext
    apply Cochain.ext
    rfl

/-- The discrete carry class itself is nonzero in ordinary discrete H². -/
theorem discreteCarryH2Class59_ne_zero :
    (groupCohomology.H2π coefficients59).hom carryCocycle59 ≠ 0 := by
  intro hzero
  exact carryCocycle59_not_mem_coboundaries₂
    ((groupCohomology.H2π_eq_zero_iff carryCocycle59).mp hzero)

/-- Since discrete H² is one-dimensional and the carry class is nonzero,
the carry class spans every discrete H² class. -/
theorem discreteCarryH2Class59_spans
    (x : groupCohomology coefficients59 2) :
    ∃ a : ZMod 59,
      a • (groupCohomology.H2π coefficients59).hom carryCocycle59 = x := by
  obtain ⟨u, hu⟩ := finiteCyclicH2Class59_spans
    ((groupCohomology.H2π coefficients59).hom carryCocycle59)
  have hu0 : u ≠ 0 := by
    intro hzero
    apply discreteCarryH2Class59_ne_zero
    rw [← hu, hzero, zero_smul]
  obtain ⟨v, hv⟩ := finiteCyclicH2Class59_spans x
  refine ⟨v * u⁻¹, ?_⟩
  rw [← hu, ← hv]
  simp [smul_smul, hu0]

/-- Every genuine homogeneous continuous H² representative is cohomologous
to a unique scalar multiple of the carry cycle. -/
theorem continuousCarryCycle59_spans_h2Projection
    (z : Cycle continuousCoefficients59 2 3) :
    ∃ a : ZMod 59,
      a • h2Projection continuousCoefficients59 continuousCarryCycle59 =
        h2Projection continuousCoefficients59 z := by
  let c := discreteCocycleOfContinuous59 z
  obtain ⟨a, ha⟩ := discreteCarryH2Class59_spans
    ((groupCohomology.H2π coefficients59).hom c)
  have heq :
      (groupCohomology.H2π coefficients59).hom c =
        (groupCohomology.H2π coefficients59).hom (a • carryCocycle59) := by
    simpa using ha.symm
  have hcoboundary :
      ⇑(c - a • carryCocycle59) ∈
        groupCohomology.coboundaries₂ coefficients59 := by
    exact (groupCohomology.H2π_eq_iff c (a • carryCocycle59)).mp heq
  obtain ⟨b, hb⟩ := continuousBoundary_of_mem_discreteCoboundaries59
    (c - a • carryCocycle59) hcoboundary
  have hzero :
      h2Projection continuousCoefficients59
        (continuousCycleOfDiscreteLinear59 (c - a • carryCocycle59)) = 0 := by
    apply (h2Projection_eq_zero_iff continuousCoefficients59 _).mpr
    exact ⟨b, hb⟩
  have hrecover : continuousCycleOfDiscreteLinear59 c = z :=
    continuousCycleOfDiscrete_discreteCocycleOfContinuous59 z
  rw [map_sub, map_smul, hrecover] at hzero
  change h2Projection continuousCoefficients59
      (z - a • continuousCarryCycle59) = 0 at hzero
  rw [map_sub, map_smul] at hzero
  exact ⟨a, (sub_eq_zero.mp hzero).symm⟩

/-- The explicit continuous carry class spans all of Mathlib's exposed
continuous H² object. -/
theorem continuousCarryH2Class59_spans
    (x : (continuousCohomology (ZMod 59) CyclicGroup59 2).obj
      continuousCoefficients59) :
    ∃ a : ZMod 59, a • continuousCarryH2Class59 = x := by
  let e := homologyLinearEquiv continuousCoefficients59 2
  obtain ⟨z, hz⟩ := h2Projection_surjective59 (e.symm x)
  obtain ⟨a, ha⟩ := continuousCarryCycle59_spans_h2Projection z
  refine ⟨a, ?_⟩
  change a • e (h2Projection continuousCoefficients59 continuousCarryCycle59) = x
  rw [← e.map_smul, ha, hz]
  exact e.apply_symm_apply x

/-- The normalized continuous cyclic readout is injective. -/
theorem actualContinuousCyclicH2Readout59_injective :
    Function.Injective actualContinuousCyclicH2Readout59 := by
  intro x y hxy
  obtain ⟨a, ha⟩ := continuousCarryH2Class59_spans x
  obtain ⟨b, hb⟩ := continuousCarryH2Class59_spans y
  have hab : a = b := by
    rw [← ha, ← hb] at hxy
    simpa using hxy
  rw [← ha, ← hb, hab]

/-- The normalized continuous cyclic readout is bijective. -/
theorem actualContinuousCyclicH2Readout59_bijective :
    Function.Bijective actualContinuousCyclicH2Readout59 :=
  ⟨actualContinuousCyclicH2Readout59_injective,
    actualContinuousCyclicH2Readout59_surjective⟩

/-- The actual continuous H² of `C₅₉` with trivial `F₅₉` coefficients,
oriented by the carry class. -/
noncomputable def actualContinuousCyclicH2LinearEquiv59 :
    (continuousCohomology (ZMod 59) CyclicGroup59 2).obj
        continuousCoefficients59 ≃ₗ[ZMod 59] ZMod 59 :=
  LinearEquiv.ofBijective actualContinuousCyclicH2Readout59
    actualContinuousCyclicH2Readout59_bijective

@[simp]
theorem actualContinuousCyclicH2LinearEquiv59_apply
    (x : (continuousCohomology (ZMod 59) CyclicGroup59 2).obj
      continuousCoefficients59) :
    actualContinuousCyclicH2LinearEquiv59 x =
      actualContinuousCyclicH2Readout59 x :=
  rfl

@[simp]
theorem actualContinuousCyclicH2LinearEquiv59_symm_apply
    (a : ZMod 59) :
    actualContinuousCyclicH2LinearEquiv59.symm a =
      actualContinuousCyclicH2Generator59 a := by
  apply actualContinuousCyclicH2Readout59_injective
  simp [actualContinuousCyclicH2LinearEquiv59]

end Fermat.Conservation.ContinuousCyclicH2Equiv59
