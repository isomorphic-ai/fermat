/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Prime Kummer norm, cyclic lift, and actual H² criterion

For every prime `p` over a characteristic-zero field, this module composes
the two generic Albert directions with the actual continuous carry class and
the unconditional compatible-root cup bridge.  It identifies, without
additional interface data or a per-prime certificate:

* the primitive root being a norm from the concrete Kummer extension;
* existence of a compatible continuous `C_(p²)` lift;
* vanishing of the pulled carry class in genuine continuous `H²`;
* vanishing of the same obstruction as the oriented or roots-valued genuine
  Kummer cup.

The negated/nonzero/no-lift forms are recorded explicitly as well.
-/
import Fermat.Conservation.PrimeAlbertCyclicConverse
import Fermat.Conservation.PrimeKummerCarryLiftCriterion
import Fermat.Conservation.PrimeOrientedCarryH2Class
import Fermat.Conservation.PrimeCompatibleKummerLift

noncomputable section

namespace Fermat.Conservation.PrimeKummerNormLiftH2Criterion

open Fermat.Conservation.PrimeAlbertCyclicConverse
open Fermat.Conservation.PrimeKummerCarryLiftCriterion
open Fermat.Conservation.PrimeKummerCyclicQuotient
open Fermat.Conservation.PrimeKummerCharacterComparison
open Fermat.Conservation.PrimeOrientedCarryH2Class
open Fermat.Conservation.PrimeCyclicExtension
open Fermat.Conservation.PrimeContinuousCarryLift
open Fermat.Conservation.ContinuousKummerH1
open Fermat.Conservation.ContinuousKummerOrientation
open Fermat.Conservation.ContinuousKummerTateAlgebra
open Fermat.Conservation.LocalKummerH1
open Fermat.Conservation.KummerOrientation

open scoped Fermat.Conservation.LocalKummerH1.KummerRootsDiscrete

attribute [local instance]
  PrimeCyclicExtension.instTopologicalSpaceCyclicGroup
  PrimeCyclicExtension.instDiscreteTopologyCyclicGroup
  PrimeCyclicExtension.instTopologicalSpaceCyclicGroupSquared
  PrimeCyclicExtension.instDiscreteTopologyCyclicGroupSquared

variable (p : ℕ) [Fact p.Prime]

local instance : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
local instance : NeZero (p ^ 2) :=
  ⟨pow_ne_zero 2 (Fact.out : Nat.Prime p).ne_zero⟩

variable (F : Type) [Field F] [CharZero F]
variable (zeta a : F)
variable (hzeta : IsPrimitiveRoot zeta p)
variable (ha : ∀ b : F, b ^ p ≠ a)

/-- The concrete arithmetic assertion that the selected primitive root is a
norm from the actual Kummer splitting field. -/
abbrev PrimitiveRootIsNorm : Prop :=
  ∃ beta : kummerExtension p F a, Algebra.norm F beta = zeta

/-- The actual continuous lift condition for the concrete Kummer
character. -/
abbrev CompatibleContinuousLift : Prop :=
  ∃ psi : Field.absoluteGaloisGroup F →ₜ* CyclicGroupSquared p,
    (reduction p).comp psi = kummerCharacter p F zeta a hzeta ha

/-- The pulled carry class transported back to roots-of-unity
coefficients. -/
abbrev kummerRootsCarryH2Class :=
  rootsCarryH2Class F zeta hzeta
    (kummerCharacter p F zeta a hzeta ha)

/-- The roots-valued genuine Kummer cup obstruction for the radicand against
the chosen primitive root. -/
def rootsKummerCupObstruction :=
  kummerCupH1 p F
    (orientH1 p F zeta hzeta
      (continuousClassOfUnit p F (radicandUnit p F a ha)))
    (continuousClassOfUnit p F (primitiveUnit p F zeta hzeta))

/-- The same Kummer cup obstruction in the oriented trivial-coefficient
presentation. -/
def orientedKummerCupObstruction :=
  orientH2 p F zeta hzeta
    (rootsKummerCupObstruction p F zeta a hzeta ha)

/-- The pulled carry class of the concrete splitting-field character is
exactly the oriented genuine Kummer cup. -/
theorem kummerCarryH2Class_eq_orientedKummerCupObstruction :
    kummerCarryH2Class p F zeta a hzeta ha =
      orientedKummerCupObstruction p F zeta a hzeta ha := by
  change pulledCarryH2Class (kummerCharacter p F zeta a hzeta ha) =
    orientH2 p F zeta hzeta
      (kummerCupH1 p F
        (orientH1 p F zeta hzeta
          (continuousClassOfUnit p F (radicandUnit p F a ha)))
        (continuousClassOfUnit p F (primitiveUnit p F zeta hzeta)))
  rw [kummerCharacter_eq_orientedKummerCharacter p F zeta a hzeta ha]
  exact
    Fermat.Conservation.PrimeCompatibleKummerLift.pulledCarry_actualH2_eq_orientedKummerCup
      (p := p) F zeta hzeta (radicandUnit p F a ha)

/-- In roots-valued coefficients, the pulled carry class is exactly the
unoriented genuine Kummer cup. -/
theorem kummerRootsCarryH2Class_eq_rootsKummerCupObstruction :
    kummerRootsCarryH2Class p F zeta a hzeta ha =
      rootsKummerCupObstruction p F zeta a hzeta ha := by
  apply (orientH2Equiv p F zeta hzeta).injective
  rw [orientH2Equiv_rootsCarryH2Class]
  rw [orientH2Equiv_apply]
  exact kummerCarryH2Class_eq_orientedKummerCupObstruction
    p F zeta a hzeta ha

/-- The oriented obstruction vanishes exactly when its roots-valued source
does; coefficient orientation is a genuine equivalence. -/
theorem orientedKummerCupObstruction_eq_zero_iff_roots :
    orientedKummerCupObstruction p F zeta a hzeta ha = 0 ↔
      rootsKummerCupObstruction p F zeta a hzeta ha = 0 := by
  constructor
  · intro h
    apply (orientH2Equiv p F zeta hzeta).injective
    rw [orientH2Equiv_apply]
    simpa [orientedKummerCupObstruction] using h
  · intro h
    simp [orientedKummerCupObstruction, h]

/-- Generic Albert criterion: norm is equivalent to compatible continuous
liftability. -/
theorem primitiveRoot_isNorm_iff_exists_compatibleLift :
    PrimitiveRootIsNorm p F zeta a ↔
      CompatibleContinuousLift p F zeta a hzeta ha := by
  exact concreteKummer_norm_iff_exists_albertCharacter
    p F zeta a hzeta ha

/-- Norm is equivalent to vanishing of the actual pulled carry class. -/
theorem primitiveRoot_isNorm_iff_kummerCarryH2Class_eq_zero :
    PrimitiveRootIsNorm p F zeta a ↔
      kummerCarryH2Class p F zeta a hzeta ha = 0 :=
  (primitiveRoot_isNorm_iff_exists_compatibleLift p F zeta a hzeta ha).trans
    (kummerCarryH2Class_eq_zero_iff_exists_continuous_lift
      p F zeta a hzeta ha).symm

/-- Norm is equivalent to vanishing of the oriented genuine Kummer cup. -/
theorem primitiveRoot_isNorm_iff_orientedKummerCupObstruction_eq_zero :
    PrimitiveRootIsNorm p F zeta a ↔
      orientedKummerCupObstruction p F zeta a hzeta ha = 0 := by
  have hEq := kummerCarryH2Class_eq_orientedKummerCupObstruction
    p F zeta a hzeta ha
  rw [← hEq]
  exact primitiveRoot_isNorm_iff_kummerCarryH2Class_eq_zero
    p F zeta a hzeta ha

/-- Norm is equivalent to vanishing of the roots-valued genuine Kummer
cup. -/
theorem primitiveRoot_isNorm_iff_rootsKummerCupObstruction_eq_zero :
    PrimitiveRootIsNorm p F zeta a ↔
      rootsKummerCupObstruction p F zeta a hzeta ha = 0 :=
  (primitiveRoot_isNorm_iff_orientedKummerCupObstruction_eq_zero
      p F zeta a hzeta ha).trans
    (orientedKummerCupObstruction_eq_zero_iff_roots
      p F zeta a hzeta ha)

omit [CharZero F] in
/-- Compatible liftability is equivalent to vanishing of the actual pulled
carry class. -/
theorem compatibleLift_iff_kummerCarryH2Class_eq_zero :
    CompatibleContinuousLift p F zeta a hzeta ha ↔
      kummerCarryH2Class p F zeta a hzeta ha = 0 :=
  (kummerCarryH2Class_eq_zero_iff_exists_continuous_lift
    p F zeta a hzeta ha).symm

/-- Compatible liftability is equivalent to vanishing of the oriented
genuine Kummer cup. -/
theorem compatibleLift_iff_orientedKummerCupObstruction_eq_zero :
    CompatibleContinuousLift p F zeta a hzeta ha ↔
      orientedKummerCupObstruction p F zeta a hzeta ha = 0 :=
  (primitiveRoot_isNorm_iff_exists_compatibleLift
      p F zeta a hzeta ha).symm.trans
    (primitiveRoot_isNorm_iff_orientedKummerCupObstruction_eq_zero
      p F zeta a hzeta ha)

/-- Compatible liftability is equivalent to vanishing of the roots-valued
genuine Kummer cup. -/
theorem compatibleLift_iff_rootsKummerCupObstruction_eq_zero :
    CompatibleContinuousLift p F zeta a hzeta ha ↔
      rootsKummerCupObstruction p F zeta a hzeta ha = 0 :=
  (primitiveRoot_isNorm_iff_exists_compatibleLift
      p F zeta a hzeta ha).symm.trans
    (primitiveRoot_isNorm_iff_rootsKummerCupObstruction_eq_zero
      p F zeta a hzeta ha)

/-- The pulled carry class and oriented Kummer cup vanish together. -/
theorem kummerCarryH2Class_eq_zero_iff_orientedKummerCupObstruction :
    kummerCarryH2Class p F zeta a hzeta ha = 0 ↔
      orientedKummerCupObstruction p F zeta a hzeta ha = 0 := by
  have hEq := kummerCarryH2Class_eq_orientedKummerCupObstruction
    p F zeta a hzeta ha
  constructor
  · intro h
    exact hEq ▸ h
  · intro h
    exact hEq.symm ▸ h

/-- The pulled carry class and roots-valued Kummer cup vanish together. -/
theorem kummerCarryH2Class_eq_zero_iff_rootsKummerCupObstruction :
    kummerCarryH2Class p F zeta a hzeta ha = 0 ↔
      rootsKummerCupObstruction p F zeta a hzeta ha = 0 :=
  (kummerCarryH2Class_eq_zero_iff_orientedKummerCupObstruction
      p F zeta a hzeta ha).trans
    (orientedKummerCupObstruction_eq_zero_iff_roots
      p F zeta a hzeta ha)

/-- The roots-valued carry class itself vanishes exactly when the
roots-valued Kummer cup does. -/
theorem kummerRootsCarryH2Class_eq_zero_iff_rootsKummerCupObstruction :
    kummerRootsCarryH2Class p F zeta a hzeta ha = 0 ↔
      rootsKummerCupObstruction p F zeta a hzeta ha = 0 := by
  have hEq := kummerRootsCarryH2Class_eq_rootsKummerCupObstruction
    p F zeta a hzeta ha
  constructor
  · intro h
    exact hEq ▸ h
  · intro h
    exact hEq.symm ▸ h

/-- A primitive-root nonnorm is exactly non-liftability of the concrete
Kummer character. -/
theorem primitiveRoot_not_norm_iff_noContinuousLift :
    ¬ PrimitiveRootIsNorm p F zeta a ↔
      KummerNoContinuousLift p F zeta a hzeta ha := by
  exact not_congr
    (primitiveRoot_isNorm_iff_exists_compatibleLift p F zeta a hzeta ha)

/-- A primitive-root nonnorm is exactly survival of the actual pulled carry
class. -/
theorem primitiveRoot_not_norm_iff_kummerCarryH2Class_ne_zero :
    ¬ PrimitiveRootIsNorm p F zeta a ↔
      kummerCarryH2Class p F zeta a hzeta ha ≠ 0 :=
  not_congr
    (primitiveRoot_isNorm_iff_kummerCarryH2Class_eq_zero
      p F zeta a hzeta ha)

/-- A primitive-root nonnorm is exactly nonvanishing of the oriented genuine
Kummer cup. -/
theorem primitiveRoot_not_norm_iff_orientedKummerCupObstruction_ne_zero :
    ¬ PrimitiveRootIsNorm p F zeta a ↔
      orientedKummerCupObstruction p F zeta a hzeta ha ≠ 0 :=
  not_congr
    (primitiveRoot_isNorm_iff_orientedKummerCupObstruction_eq_zero
      p F zeta a hzeta ha)

/-- A primitive-root nonnorm is exactly nonvanishing of the roots-valued
genuine Kummer cup. -/
theorem primitiveRoot_not_norm_iff_rootsKummerCupObstruction_ne_zero :
    ¬ PrimitiveRootIsNorm p F zeta a ↔
      rootsKummerCupObstruction p F zeta a hzeta ha ≠ 0 :=
  not_congr
    (primitiveRoot_isNorm_iff_rootsKummerCupObstruction_eq_zero
      p F zeta a hzeta ha)

/-- The oriented cup survives exactly when the concrete character has no
continuous `C_(p²)` lift. -/
theorem orientedKummerCupObstruction_ne_zero_iff_noContinuousLift :
    orientedKummerCupObstruction p F zeta a hzeta ha ≠ 0 ↔
      KummerNoContinuousLift p F zeta a hzeta ha :=
  (primitiveRoot_not_norm_iff_orientedKummerCupObstruction_ne_zero
      p F zeta a hzeta ha).symm.trans
    (primitiveRoot_not_norm_iff_noContinuousLift
      p F zeta a hzeta ha)

/-- The roots-valued cup survives exactly when the concrete character has no
continuous `C_(p²)` lift. -/
theorem rootsKummerCupObstruction_ne_zero_iff_noContinuousLift :
    rootsKummerCupObstruction p F zeta a hzeta ha ≠ 0 ↔
      KummerNoContinuousLift p F zeta a hzeta ha :=
  (primitiveRoot_not_norm_iff_rootsKummerCupObstruction_ne_zero
      p F zeta a hzeta ha).symm.trans
    (primitiveRoot_not_norm_iff_noContinuousLift
      p F zeta a hzeta ha)

end Fermat.Conservation.PrimeKummerNormLiftH2Criterion
