/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Coordinate naturality of the cyclic lift obstruction at 59

The explicit carry class detects whether a continuous `C59` character lifts
through `C59²`.  This property must not depend on a harmless rotation of the
chosen cyclic coordinate.  This file proves that invariance constructively.

First, any pair of compatible continuous cyclic automorphisms transports
lifts in both directions.  Second, every scalar rotation modulo 59 lifts to
a scalar rotation modulo `59²`, using surjectivity on unit groups.  Thus the
no-lift obstruction is invariant under every unit rescaling which can arise
from changing a primitive-root coordinate.

This is finite group plumbing only.  It does not assert that two particular
Kummer characters differ by such a rotation; that comparison remains a
separate theorem.
-/
import Fermat.Experiments.Conservation.ContinuousCarryLiftObstruction59
import Mathlib.Data.ZMod.Aut
import Mathlib.Data.ZMod.Units

noncomputable section

namespace Fermat.Conservation.CyclicLiftNaturality59

open Fermat.Conservation.ContinuousCarryLiftObstruction59
open Fermat.Conservation.FiniteCyclicH2Generator59

local instance cyclic59Topology : TopologicalSpace CyclicGroup59 := ⊥
local instance cyclic59Discrete : DiscreteTopology CyclicGroup59 := ⟨rfl⟩
local instance cyclic59SquaredTopology : TopologicalSpace CyclicGroup59Squared := ⊥
local instance cyclic59SquaredDiscrete : DiscreteTopology CyclicGroup59Squared := ⟨rfl⟩

variable {G : Type} [Group G] [TopologicalSpace G]

/-- Regard a continuous multiplicative equivalence as a continuous
multiplicative homomorphism. -/
def continuousHomOfMulEquiv {A B : Type}
    [TopologicalSpace A] [TopologicalSpace B] [Monoid A] [Monoid B]
    (e : A ≃ₜ* B) : A →ₜ* B :=
  ContinuousMonoidHom.toContinuousMonoidHom e

/-- A compatible change of cyclic coordinates transports a lift through
the reduction map. -/
def transportLift59
    (e59sq : CyclicGroup59Squared ≃ₜ* CyclicGroup59Squared)
    (psi : G →ₜ* CyclicGroup59Squared) :
    G →ₜ* CyclicGroup59Squared :=
  (continuousHomOfMulEquiv e59sq).comp psi

theorem reduction59_comp_transportLift59
    (e59 : CyclicGroup59 ≃ₜ* CyclicGroup59)
    (e59sq : CyclicGroup59Squared ≃ₜ* CyclicGroup59Squared)
    (hcompat : ∀ x : CyclicGroup59Squared,
      reduction59 (e59sq x) = e59 (reduction59 x))
    (chi : G →ₜ* CyclicGroup59)
    (psi : G →ₜ* CyclicGroup59Squared)
    (hlift : reduction59.comp psi = chi) :
    reduction59.comp (transportLift59 e59sq psi) =
      (continuousHomOfMulEquiv e59).comp chi := by
  ext g
  change reduction59 (e59sq (psi g)) = e59 (chi g)
  rw [hcompat]
  exact congrArg e59 (DFunLike.congr_fun hlift g)

theorem reduction59_symm_compat
    (e59 : CyclicGroup59 ≃ₜ* CyclicGroup59)
    (e59sq : CyclicGroup59Squared ≃ₜ* CyclicGroup59Squared)
    (hcompat : ∀ x : CyclicGroup59Squared,
      reduction59 (e59sq x) = e59 (reduction59 x))
    (x : CyclicGroup59Squared) :
    reduction59 (e59sq.symm x) = e59.symm (reduction59 x) := by
  apply e59.injective
  rw [e59.apply_symm_apply]
  simpa using (hcompat (e59sq.symm x)).symm

/-- Existence of a continuous `C59²` lift is invariant under every cyclic
coordinate change which itself lifts compatibly through reduction. -/
theorem exists_continuous_lift_iff_of_compatible_equiv
    (e59 : CyclicGroup59 ≃ₜ* CyclicGroup59)
    (e59sq : CyclicGroup59Squared ≃ₜ* CyclicGroup59Squared)
    (hcompat : ∀ x : CyclicGroup59Squared,
      reduction59 (e59sq x) = e59 (reduction59 x))
    (chi : G →ₜ* CyclicGroup59) :
    (∃ psi : G →ₜ* CyclicGroup59Squared,
        reduction59.comp psi = chi) ↔
      ∃ psi : G →ₜ* CyclicGroup59Squared,
        reduction59.comp psi = (continuousHomOfMulEquiv e59).comp chi := by
  constructor
  · rintro ⟨psi, hpsi⟩
    exact ⟨transportLift59 e59sq psi,
      reduction59_comp_transportLift59 e59 e59sq hcompat chi psi hpsi⟩
  · rintro ⟨psi, hpsi⟩
    let psi' : G →ₜ* CyclicGroup59Squared :=
      (continuousHomOfMulEquiv e59sq.symm).comp psi
    refine ⟨psi', ?_⟩
    ext g
    change reduction59 (e59sq.symm (psi g)) = chi g
    rw [reduction59_symm_compat e59 e59sq hcompat]
    have hpoint := DFunLike.congr_fun hpsi g
    change reduction59 (psi g) = e59 (chi g) at hpoint
    rw [hpoint, e59.symm_apply_apply]

/-- The corresponding no-lift obstruction is coordinate invariant. -/
theorem noContinuousLift_iff_of_compatible_equiv
    (e59 : CyclicGroup59 ≃ₜ* CyclicGroup59)
    (e59sq : CyclicGroup59Squared ≃ₜ* CyclicGroup59Squared)
    (hcompat : ∀ x : CyclicGroup59Squared,
      reduction59 (e59sq x) = e59 (reduction59 x))
    (chi : G →ₜ* CyclicGroup59) :
    NoContinuousLift chi ↔
      NoContinuousLift ((continuousHomOfMulEquiv e59).comp chi) := by
  exact not_congr
    (exists_continuous_lift_iff_of_compatible_equiv
      e59 e59sq hcompat chi)

/-! ## Every scalar coordinate change at 59 lifts -/

/-- Multiplication by a unit is the corresponding continuous automorphism
of the multiplicatively presented additive cyclic group. -/
def scalarRotation59 (u : (ZMod 59)ˣ) :
    CyclicGroup59 ≃ₜ* CyclicGroup59 :=
  { ((ZMod.AddAutEquivUnits 59).symm (Additive.ofMul u)).toMultiplicative with
    continuous_toFun := continuous_of_discreteTopology
    continuous_invFun := continuous_of_discreteTopology }

/-- The same scalar rotation one level upstairs. -/
def scalarRotation59Squared (u : (ZMod (59 ^ 2))ˣ) :
    CyclicGroup59Squared ≃ₜ* CyclicGroup59Squared :=
  { ((ZMod.AddAutEquivUnits (59 ^ 2)).symm
      (Additive.ofMul u)).toMultiplicative with
    continuous_toFun := continuous_of_discreteTopology
    continuous_invFun := continuous_of_discreteTopology }

@[simp]
theorem scalarRotation59_apply_toAdd
    (u : (ZMod 59)ˣ) (x : CyclicGroup59) :
    (scalarRotation59 u x).toAdd = (u : ZMod 59) * x.toAdd :=
  rfl

@[simp]
theorem scalarRotation59Squared_apply_toAdd
    (u : (ZMod (59 ^ 2))ˣ) (x : CyclicGroup59Squared) :
    (scalarRotation59Squared u x).toAdd =
      (u : ZMod (59 ^ 2)) * x.toAdd :=
  rfl

/-- The divisibility witness used by the canonical reduction from `59²` to
`59`.  It is public so downstream coordinate-comparison statements do not
contain an inaccessible private constant. -/
abbrev reductionDvd59 : 59 ∣ 59 ^ 2 := by norm_num

/-- Reducing a unit and then rotating agrees with rotating upstairs and
then reducing. -/
theorem reduction59_scalarRotation59Squared
    (u : (ZMod (59 ^ 2))ˣ) (x : CyclicGroup59Squared) :
    reduction59 (scalarRotation59Squared u x) =
      scalarRotation59 (ZMod.unitsMap reductionDvd59 u) (reduction59 x) := by
  apply Multiplicative.toAdd.injective
  change ZMod.castHom reductionDvd59 (ZMod 59)
      ((u : ZMod (59 ^ 2)) * x.toAdd) =
    (ZMod.unitsMap reductionDvd59 u : ZMod 59) *
      ZMod.castHom reductionDvd59 (ZMod 59) x.toAdd
  rw [map_mul]
  rfl

/-- Every unit coordinate rotation modulo 59 has a compatible unit rotation
modulo `59²`. -/
theorem exists_compatible_scalarRotation59 (u : (ZMod 59)ˣ) :
    ∃ uSq : (ZMod (59 ^ 2))ˣ,
      ZMod.unitsMap reductionDvd59 uSq = u ∧
      ∀ x : CyclicGroup59Squared,
        reduction59 (scalarRotation59Squared uSq x) =
          scalarRotation59 u (reduction59 x) := by
  letI : NeZero (59 ^ 2) := ⟨by norm_num⟩
  obtain ⟨uSq, huSq⟩ := ZMod.unitsMap_surjective reductionDvd59 u
  refine ⟨uSq, huSq, ?_⟩
  intro x
  rw [← huSq]
  exact reduction59_scalarRotation59Squared uSq x

/-- No-liftability is invariant under every scalar rotation of the cyclic
coordinate.  This is the root-choice/primitive-coordinate robustness needed
when comparing two concrete Kummer character constructions. -/
theorem noContinuousLift_iff_scalarRotation59
    (u : (ZMod 59)ˣ) (chi : G →ₜ* CyclicGroup59) :
    NoContinuousLift chi ↔
      NoContinuousLift
        ((continuousHomOfMulEquiv (scalarRotation59 u)).comp chi) := by
  obtain ⟨uSq, _, hcompat⟩ := exists_compatible_scalarRotation59 u
  exact noContinuousLift_iff_of_compatible_equiv
    (scalarRotation59 u) (scalarRotation59Squared uSq) hcompat chi

end Fermat.Conservation.CyclicLiftNaturality59
