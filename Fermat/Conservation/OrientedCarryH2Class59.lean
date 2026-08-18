/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The continuous carry class in oriented Kummer coefficients

For an absolute-Galois character with no continuous C59-squared lift, the
explicit carry construction gives a nonzero continuous H2 class with trivial
F59 coefficients.  A primitive 59th root of unity identifies that line with
the roots-of-unity coefficient representation used by the Kummer cup.

This is a lossless coefficient change only.  It does not assert that the
resulting roots-valued class is the cup of two particular Kummer classes;
that is the separate Bockstein/cup comparison.
-/
import Fermat.Conservation.ContinuousCarryLiftObstruction59
import Fermat.Conservation.ContinuousKummerOrientation

noncomputable section

namespace Fermat.Conservation.OrientedCarryH2Class59

open ContinuousCarryLiftObstruction59
open ContinuousKummerH1
open ContinuousKummerOrientation
open FiniteCyclicH2Generator59

variable (F : Type) [Field F]
variable (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)

/-- The pulled carry class, exposed in the oriented trivial-coefficient
presentation used by the left Kummer seat. -/
def orientedCarryH2Class59
    (chi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup59) :
    OrientedContinuousH2 59 F :=
  pulledCarryH2Class59 chi

/-- A no-lift witness makes the oriented carry class nonzero. -/
theorem orientedCarryH2Class59_ne_zero_of_noContinuousLift
    (chi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup59)
    (hnolift : NoContinuousLift chi) :
    orientedCarryH2Class59 F chi ≠ 0 :=
  pulledCarryH2Class59_ne_zero_of_noContinuousLift chi hnolift

/-- The same actual H2 class in the roots-of-unity coefficient
presentation retained by the canonical Kummer cup. -/
def rootsCarryH2Class59
    (chi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup59) :
    ((continuousCohomology (ZMod 59) (Field.absoluteGaloisGroup F) 2).obj
      (rootsTopRepresentation 59 F)) :=
  (orientH2Equiv 59 F zeta hzeta).symm (orientedCarryH2Class59 F chi)

/-- Orienting the roots-valued carry class recovers the original trivial-line
class exactly. -/
@[simp]
theorem orientH2Equiv_rootsCarryH2Class59
    (chi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup59) :
    orientH2Equiv 59 F zeta hzeta (rootsCarryH2Class59 F zeta hzeta chi) =
      orientedCarryH2Class59 F chi := by
  simp [rootsCarryH2Class59]

/-- Non-liftability survives the inverse coefficient orientation, producing
a nonzero roots-of-unity-valued actual continuous H2 class. -/
theorem rootsCarryH2Class59_ne_zero_of_noContinuousLift
    (chi : Field.absoluteGaloisGroup F →ₜ* CyclicGroup59)
    (hnolift : NoContinuousLift chi) :
    rootsCarryH2Class59 F zeta hzeta chi ≠ 0 := by
  intro hzero
  have horiented := congrArg (orientH2Equiv 59 F zeta hzeta) hzero
  rw [orientH2Equiv_rootsCarryH2Class59, map_zero] at horiented
  exact orientedCarryH2Class59_ne_zero_of_noContinuousLift F chi hnolift horiented

end Fermat.Conservation.OrientedCarryH2Class59
