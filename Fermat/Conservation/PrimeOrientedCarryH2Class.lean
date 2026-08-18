/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Prime-parametric carry classes in Kummer coefficients

For every prime `p`, a continuous `C_p` character has an actual carry class
in continuous `H²` with trivial `F_p` coefficients.  A supplied primitive
`p`-th root of unity transports that class, losslessly, to the roots-valued
coefficient representation used by the continuous Kummer cup.

This is only coefficient orientation.  It does not assert a cup-product or
local-reciprocity value.
-/
import Fermat.Conservation.PrimeContinuousCarryLift
import Fermat.Conservation.ContinuousKummerOrientation

noncomputable section

namespace Fermat.Conservation.PrimeOrientedCarryH2Class

open Fermat.Conservation.ContinuousKummerH1
open Fermat.Conservation.ContinuousKummerOrientation
open Fermat.Conservation.PrimeCyclicExtension
open Fermat.Conservation.PrimeContinuousCarryLift

variable {p : ℕ} [Fact p.Prime]
variable (F : Type) [Field F]
variable (zeta : F) (hzeta : IsPrimitiveRoot zeta p)

/-- The pulled carry class in the oriented trivial-coefficient
presentation. -/
def orientedCarryH2Class
    (chi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup p) :
    OrientedContinuousH2 p F :=
  pulledCarryH2Class chi

/-- A no-lift witness makes the oriented carry class nonzero. -/
theorem orientedCarryH2Class_ne_zero_of_noContinuousLift
    (chi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup p)
    (hnolift : NoContinuousLift chi) :
    orientedCarryH2Class F chi ≠ 0 :=
  pulledCarryH2Class_ne_zero_of_noContinuousLift chi hnolift

/-- Vanishing of the oriented class is exactly existence of a continuous
lift through `C_(p²) → C_p`. -/
theorem orientedCarryH2Class_eq_zero_iff_exists_continuous_lift
    (chi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup p) :
    orientedCarryH2Class F chi = 0 ↔
      ∃ psi : Field.absoluteGaloisGroup F →ₜ* CyclicGroupSquared p,
        (reduction p).comp psi = chi :=
  pulledCarryH2Class_eq_zero_iff_exists_continuous_lift chi

/-- The same actual `H²` class in the roots-of-unity coefficient
presentation retained by the canonical Kummer cup. -/
def rootsCarryH2Class
    (chi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup p) :
    ((continuousCohomology (ZMod p) (Field.absoluteGaloisGroup F) 2).obj
      (rootsTopRepresentation p F)) :=
  (orientH2Equiv p F zeta hzeta).symm (orientedCarryH2Class F chi)

/-- Orienting the roots-valued carry class recovers the original
trivial-line class exactly. -/
@[simp]
theorem orientH2Equiv_rootsCarryH2Class
    (chi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup p) :
    orientH2Equiv p F zeta hzeta (rootsCarryH2Class F zeta hzeta chi) =
      orientedCarryH2Class F chi := by
  simp [rootsCarryH2Class]

/-- Non-liftability survives inverse coefficient orientation. -/
theorem rootsCarryH2Class_ne_zero_of_noContinuousLift
    (chi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup p)
    (hnolift : NoContinuousLift chi) :
    rootsCarryH2Class F zeta hzeta chi ≠ 0 := by
  intro hzero
  have horiented := congrArg (orientH2Equiv p F zeta hzeta) hzero
  rw [orientH2Equiv_rootsCarryH2Class, map_zero] at horiented
  exact orientedCarryH2Class_ne_zero_of_noContinuousLift F chi hnolift horiented

/-- The roots-valued class is zero under precisely the same cyclic-lift
condition, since coefficient orientation is an equivalence. -/
theorem rootsCarryH2Class_eq_zero_iff_exists_continuous_lift
    (chi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup p) :
    rootsCarryH2Class F zeta hzeta chi = 0 ↔
      ∃ psi : Field.absoluteGaloisGroup F →ₜ* CyclicGroupSquared p,
        (reduction p).comp psi = chi := by
  constructor
  · intro hroots
    have horiented : orientedCarryH2Class F chi = 0 := by
      calc
        orientedCarryH2Class F chi =
            orientH2Equiv p F zeta hzeta
              (rootsCarryH2Class F zeta hzeta chi) := by
                symm
                exact orientH2Equiv_rootsCarryH2Class F zeta hzeta chi
        _ = orientH2Equiv p F zeta hzeta 0 :=
          congrArg (orientH2Equiv p F zeta hzeta) hroots
        _ = 0 := map_zero _
    exact
      (orientedCarryH2Class_eq_zero_iff_exists_continuous_lift F chi).mp
        horiented
  · intro hlift
    have horiented : orientedCarryH2Class F chi = 0 :=
      (orientedCarryH2Class_eq_zero_iff_exists_continuous_lift F chi).mpr
        hlift
    simp [rootsCarryH2Class, horiented]

end Fermat.Conservation.PrimeOrientedCarryH2Class
