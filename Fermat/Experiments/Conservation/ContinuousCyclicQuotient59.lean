/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Continuous cyclic quotients of an absolute Galois group at 59

This file is the API-compatible order-59 specialization of
`ContinuousCyclicQuotient`.  Restriction from an absolute Galois group to
the Galois group of a supplied normal subextension is continuous and
surjective.  Composing restriction with a supplied continuous
identification of that Galois group with `Multiplicative (ZMod 59)` gives
an honest continuous cyclic quotient.

The two inputs are deliberately visible: this file does **not** choose the
normal subextension and does **not** construct its cyclic identification.
It also does not define an inflation map on continuous cohomology, compare
discrete and continuous cohomology, or prove that an inflated `H²` class is
nonzero.  Those are separate cohomological and arithmetic obligations.
-/
import Fermat.Experiments.Conservation.ContinuousCyclicQuotient

noncomputable section

namespace Fermat.Conservation.ContinuousCyclicQuotient59

/-- The finite cyclic group used as the quotient target.  It is written
multiplicatively because absolute Galois groups are multiplicative groups. -/
abbrev CyclicGroup59 := Multiplicative (ZMod 59)

local instance : TopologicalSpace CyclicGroup59 := ⊥
local instance : DiscreteTopology CyclicGroup59 := ⟨rfl⟩

variable (F : Type*) [Field F]

/-- Restriction to a supplied normal intermediate field, packaged as a
continuous homomorphism out of the absolute Galois group. -/
def absoluteGaloisRestriction
    (L : IntermediateField F (AlgebraicClosure F)) [Normal F L] :
    Field.absoluteGaloisGroup F →ₜ* (L ≃ₐ[F] L) :=
  ContinuousCyclicQuotient.absoluteGaloisRestriction F L

/-- Restriction from the absolute Galois group to a normal subextension is
surjective. -/
theorem absoluteGaloisRestriction_surjective
    (L : IntermediateField F (AlgebraicClosure F)) [Normal F L] :
    Function.Surjective (absoluteGaloisRestriction F L) := by
  exact ContinuousCyclicQuotient.absoluteGaloisRestriction_surjective F L

/-- An honest continuous `C₅₉` quotient obtained from a supplied normal
subextension and a supplied continuous cyclic identification of its Galois
group.

This construction is intentionally conditional on `L` and `e`; it is not an
arithmetic existence theorem for either datum. -/
def cyclicQuotient59
    (L : IntermediateField F (AlgebraicClosure F)) [Normal F L]
    (e : (L ≃ₐ[F] L) ≃ₜ* CyclicGroup59) :
    Field.absoluteGaloisGroup F →ₜ* CyclicGroup59 :=
  ContinuousCyclicQuotient.cyclicQuotient F 59 L e

@[simp]
theorem cyclicQuotient59_apply
    (L : IntermediateField F (AlgebraicClosure F)) [Normal F L]
    (e : (L ≃ₐ[F] L) ≃ₜ* CyclicGroup59)
    (g : Field.absoluteGaloisGroup F) :
    cyclicQuotient59 F L e g = e (AlgEquiv.restrictNormalHom L g) :=
  ContinuousCyclicQuotient.cyclicQuotient_apply F 59 L e g

/-- The resulting continuous cyclic homomorphism is a quotient map in the
algebraic sense: its underlying function is surjective. -/
theorem cyclicQuotient59_surjective
    (L : IntermediateField F (AlgebraicClosure F)) [Normal F L]
    (e : (L ≃ₐ[F] L) ≃ₜ* CyclicGroup59) :
    Function.Surjective (cyclicQuotient59 F L e) := by
  exact ContinuousCyclicQuotient.cyclicQuotient_surjective F 59 L e

end Fermat.Conservation.ContinuousCyclicQuotient59
