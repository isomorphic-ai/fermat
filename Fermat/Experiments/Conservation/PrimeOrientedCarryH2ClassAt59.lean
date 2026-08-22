/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Compatibility of prime-oriented carry classes at 59

The original oriented and roots-valued order-59 carry classes are
definitionally the specialization of the prime-parametric implementation.
-/
import Fermat.Experiments.Conservation.OrientedCarryH2Class59
import Fermat.Experiments.Conservation.PrimeContinuousCarryLiftAt59
import Fermat.Experiments.Conservation.PrimeOrientedCarryH2Class

noncomputable section

namespace Fermat.Conservation.PrimeOrientedCarryH2ClassAt59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (F : Type) [Field F]
variable (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)

theorem orientedCarryH2Class_eq_59
    (chi : Field.absoluteGaloisGroup F →ₜ*
      PrimeCyclicExtension.CyclicGroup 59) :
    OrientedCarryH2Class59.orientedCarryH2Class59 F chi =
      PrimeOrientedCarryH2Class.orientedCarryH2Class F chi :=
  rfl

theorem rootsCarryH2Class_eq_59
    (chi : Field.absoluteGaloisGroup F →ₜ*
      PrimeCyclicExtension.CyclicGroup 59) :
    OrientedCarryH2Class59.rootsCarryH2Class59 F zeta hzeta chi =
      PrimeOrientedCarryH2Class.rootsCarryH2Class F zeta hzeta chi :=
  rfl

end Fermat.Conservation.PrimeOrientedCarryH2ClassAt59
