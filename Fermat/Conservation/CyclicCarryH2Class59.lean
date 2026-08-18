/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# An explicit nonzero carry class in continuous H²(C₅₉, F₅₉)

The standard-representative carry is the concrete Bockstein cocycle for the
cyclic group `Multiplicative (ZMod 59)`.  This file proves its cocycle law by
standard-representative arithmetic, proves it is not a discrete boundary by
a finite-sum functional, and transports the same named cocycle into
Mathlib's genuine continuous homogeneous cohomology using the
discrete-to-continuous bridge.

The resulting continuous class is explicit and nonzero.  This file does not
inflate it to an absolute Galois group: survival under such an inflation is a
separate arithmetic obligation, and can fail when the quotient character
lifts to a cyclic group of order `59²`.
-/
import Fermat.Conservation.DiscreteToContinuousH2
import Fermat.Conservation.FiniteCyclicH2Generator59

noncomputable section

open CategoryTheory
open ContinuousCohomology
open Fermat.Conservation.ContinuousKummerTateCup.Nominal

namespace Fermat.Conservation.CyclicCarryH2Class59

open Fermat.Conservation.FiniteCyclicH2Generator59
open Fermat.Conservation.DiscreteToContinuousH2

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩
local instance : Fintype CyclicGroup59 := inferInstanceAs (Fintype (ZMod 59))
local instance : TopologicalSpace (ZMod 59) := ⊥
local instance : DiscreteTopology (ZMod 59) := ⟨rfl⟩
local instance : TopologicalSpace CyclicGroup59 := ⊥
local instance : DiscreteTopology CyclicGroup59 := ⟨rfl⟩

/-- The base-`59` carry of the standard representatives. -/
def carry59 (a b : ZMod 59) : ZMod 59 :=
  if 59 ≤ a.val + b.val then 1 else 0

/-- The carry as an inhomogeneous two-cochain on the multiplicative
presentation of the additive cyclic group. -/
def carryFunction59 : CyclicGroup59 × CyclicGroup59 → coefficients59 :=
  fun gh ↦ carry59 gh.1.toAdd gh.2.toAdd

/-- The carry satisfies the inhomogeneous degree-two cocycle equation.
The proof is the ordinary four-region carry identity, with the two modular
sum representatives split at `59`. -/
theorem carryFunction59_mem_cocycles₂ :
    carryFunction59 ∈ groupCohomology.cocycles₂ coefficients59 := by
  rw [groupCohomology.mem_cocycles₂_def]
  change ∀ (a b c : ZMod 59),
    carry59 b c - carry59 (a + b) c +
      carry59 a (b + c) - carry59 a b = 0
  intro a b c
  have ha : a.val < 59 := a.val_lt
  have hb : b.val < 59 := b.val_lt
  have hc : c.val < 59 := c.val_lt
  have hab_val : (a + b).val =
      if 59 ≤ a.val + b.val then a.val + b.val - 59 else a.val + b.val := by
    split_ifs with h
    · exact ZMod.val_add_of_le h
    · exact ZMod.val_add_of_lt (lt_of_not_ge h)
  have hbc_val : (b + c).val =
      if 59 ≤ b.val + c.val then b.val + c.val - 59 else b.val + c.val := by
    split_ifs with h
    · exact ZMod.val_add_of_le h
    · exact ZMod.val_add_of_lt (lt_of_not_ge h)
  simp only [carry59]
  split_ifs with hbc hab_c ha_bc hab <;>
    simp_all <;>
    norm_num <;>
    omega

/-- The explicit discrete carry cocycle. -/
def carryCocycle59 : groupCohomology.cocycles₂ coefficients59 :=
  ⟨carryFunction59, carryFunction59_mem_cocycles₂⟩

@[simp]
theorem carryCocycle59_apply (g h : CyclicGroup59) :
    carryCocycle59 (g, h) = carry59 g.toAdd h.toAdd :=
  rfl

/-- Summing the carry against the cyclic generator reads exactly one. -/
theorem sum_carryCocycle59_generator59 :
    ∑ h : CyclicGroup59, carryCocycle59 (generator59, h) = 1 := by
  change (∑ h : CyclicGroup59, carry59 generator59.toAdd h.toAdd) =
    (1 : ZMod 59)
  decide

/-- The same sum kills every discrete two-boundary. -/
theorem sum_discreteBoundary_generator59
    (b : CyclicGroup59 → coefficients59) :
    ∑ h : CyclicGroup59,
      (groupCohomology.d₁₂ coefficients59).hom b (generator59, h) = 0 := by
  simp only [groupCohomology.d₁₂_hom_apply]
  change ∑ h : CyclicGroup59,
      (b h - b (generator59 * h) + b generator59) = 0
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hperm : (∑ h : CyclicGroup59, b (generator59 * h)) =
      ∑ h : CyclicGroup59, b h :=
    (Group.mulLeft_bijective generator59).sum_comp b
  rw [hperm, sub_self, zero_add, Finset.sum_const, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card, cyclicGroup59_card]
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

/-- The explicit carry cocycle is not a discrete two-boundary. -/
theorem carryCocycle59_not_mem_coboundaries₂ :
    ⇑carryCocycle59 ∉ groupCohomology.coboundaries₂ coefficients59 := by
  intro hboundary
  obtain ⟨b, hb⟩ := hboundary
  have hsum := congrArg
    (fun f : CyclicGroup59 × CyclicGroup59 → coefficients59 ↦
      ∑ h : CyclicGroup59, f (generator59, h)) hb
  rw [sum_discreteBoundary_generator59,
    sum_carryCocycle59_generator59] at hsum
  exact zero_ne_one hsum

/-- The trivial continuous coefficient line for the finite discrete cyclic
group. -/
abbrev continuousCoefficients59 :=
  trivialAction (R := ZMod 59) (G := CyclicGroup59)

/-- The same named carry cocycle as a closed homogeneous continuous
two-cochain. -/
def continuousCarryCycle59 : Cycle continuousCoefficients59 2 3 :=
  continuousCycleOfDiscrete carryCocycle59

/-- The continuous carry cycle is not a continuous boundary. -/
theorem continuousCarryCycle59_not_boundary :
    ¬ ∃ b : Cochain continuousCoefficients59 1,
      differential continuousCoefficients59 1 2 b =
        cycleCochain continuousCoefficients59 2 3 continuousCarryCycle59 :=
  continuousCycleOfDiscrete_not_boundary carryCocycle59
    carryCocycle59_not_mem_coboundaries₂

/-- The actual continuous `H²` class represented by the carry cycle. -/
def continuousCarryH2Class59 :
    (continuousCohomology (ZMod 59) CyclicGroup59 2).obj
      continuousCoefficients59 :=
  homologyLinearEquiv continuousCoefficients59 2
    (h2Projection continuousCoefficients59 continuousCarryCycle59)

/-- The actual continuous carry class is nonzero. -/
theorem continuousCarryH2Class59_ne_zero :
    continuousCarryH2Class59 ≠ 0 := by
  intro hzero
  have hprojection :
      h2Projection continuousCoefficients59 continuousCarryCycle59 = 0 := by
    let e := homologyLinearEquiv continuousCoefficients59 2
    change e (h2Projection continuousCoefficients59 continuousCarryCycle59) = 0 at hzero
    exact e.injective (hzero.trans e.map_zero.symm)
  exact continuousCarryCycle59_not_boundary
    ((h2Projection_eq_zero_iff continuousCoefficients59
      continuousCarryCycle59).mp hprojection)

end Fermat.Conservation.CyclicCarryH2Class59
