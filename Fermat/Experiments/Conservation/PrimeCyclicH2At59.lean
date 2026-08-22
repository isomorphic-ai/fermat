/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The generic prime-cyclic H² construction specializes definitionally at 59

This compatibility layer records that the existing `59`-specific carry,
continuous class, generator-loop readout, and final linear equivalence are
definitionally the specialization of `PrimeCyclicH2`.  The historical
modules remain unchanged while downstream code can migrate to the generic
API one declaration at a time.
-/
import Fermat.Experiments.Conservation.PrimeCyclicH2
import Fermat.Experiments.Conservation.ContinuousCyclicH2Equiv59

noncomputable section

open CategoryTheory ContinuousCohomology
open Fermat.Conservation.ContinuousKummerTateCup.Nominal

namespace Fermat.Conservation.PrimeCyclicH2At59

open Fermat.Conservation.PrimeCyclicH2
open Fermat.Conservation.FiniteCyclicH2Generator59
open Fermat.Conservation.CyclicCarryH2Class59
open Fermat.Conservation.ContinuousCyclicH2Readout59
open Fermat.Conservation.ContinuousCyclicH2Equiv59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩
local instance : Fintype CyclicGroup59 := inferInstanceAs (Fintype (ZMod 59))
local instance : TopologicalSpace (ZMod 59) := ⊥
local instance : DiscreteTopology (ZMod 59) := ⟨rfl⟩
local instance : TopologicalSpace CyclicGroup59 := ⊥
local instance : DiscreteTopology CyclicGroup59 := ⟨rfl⟩

theorem generator_eq_generator59 : generator 59 = generator59 := rfl

theorem carry_eq_carry59 : carry 59 = carry59 := rfl

theorem carryCocycle_eq_carryCocycle59 :
    carryCocycle 59 = carryCocycle59 := rfl

theorem continuousCarryCycle_eq_continuousCarryCycle59 :
    continuousCarryCycle 59 = continuousCarryCycle59 := rfl

theorem continuousCarryH2Class_eq_continuousCarryH2Class59 :
    continuousCarryH2Class 59 = continuousCarryH2Class59 := rfl

theorem cyclicCycleSum_eq_cyclicCycleSum59 :
    cyclicCycleSum 59 = cyclicCycleSum59 := rfl

theorem actualContinuousCyclicH2Readout_eq_59 :
    actualContinuousCyclicH2Readout 59 =
      actualContinuousCyclicH2Readout59 := rfl

theorem actualContinuousCyclicH2Generator_eq_59 :
    actualContinuousCyclicH2Generator 59 =
      actualContinuousCyclicH2Generator59 := rfl

theorem actualContinuousCyclicH2LinearEquiv_eq_59 :
    actualContinuousCyclicH2LinearEquiv 59 =
      actualContinuousCyclicH2LinearEquiv59 := rfl

end Fermat.Conservation.PrimeCyclicH2At59
