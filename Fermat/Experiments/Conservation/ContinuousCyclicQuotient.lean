/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Generic continuous cyclic quotients of absolute Galois groups

For a normal intermediate field in a chosen algebraic closure, restriction
from the absolute Galois group is continuous and surjective.  Composing it
with a continuous identification of the finite Galois group with
`Multiplicative (ZMod n)` gives a continuous surjective cyclic quotient.

This module is deliberately only the generic transport plumbing.  It does
not construct the normal intermediate field or its cyclic identification;
arithmetic modules supply those two inputs.
-/
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Instances.ZMod

noncomputable section

namespace Fermat.Conservation.ContinuousCyclicQuotient

/-- The cyclic quotient target, written multiplicatively to match Galois
groups. -/
abbrev CyclicGroup (n : ℕ) := Multiplicative (ZMod n)

local instance (n : ℕ) : TopologicalSpace (CyclicGroup n) := ⊥
local instance (n : ℕ) : DiscreteTopology (CyclicGroup n) := ⟨rfl⟩

variable (F : Type*) [Field F]

/-- Restriction to a normal intermediate field, as a continuous group
homomorphism. -/
def absoluteGaloisRestriction
    (L : IntermediateField F (AlgebraicClosure F)) [Normal F L] :
    Field.absoluteGaloisGroup F →ₜ* (L ≃ₐ[F] L) where
  toMonoidHom := AlgEquiv.restrictNormalHom L
  continuous_toFun := InfiniteGalois.restrictNormalHom_continuous L

theorem absoluteGaloisRestriction_surjective
    (L : IntermediateField F (AlgebraicClosure F)) [Normal F L] :
    Function.Surjective (absoluteGaloisRestriction F L) := by
  change Function.Surjective
    (AlgEquiv.restrictNormalHom (F := F) (K₁ := AlgebraicClosure F) L)
  exact AlgEquiv.restrictNormalHom_surjective
    (F := F) (K₁ := L) (E := AlgebraicClosure F)

/-- Compose absolute-Galois restriction with a supplied cyclic
identification of the finite quotient. -/
def cyclicQuotient
    (n : ℕ)
    (L : IntermediateField F (AlgebraicClosure F)) [Normal F L]
    (e : (L ≃ₐ[F] L) ≃ₜ* CyclicGroup n) :
    Field.absoluteGaloisGroup F →ₜ* CyclicGroup n :=
  (ContinuousMonoidHom.toContinuousMonoidHom e).comp
    (absoluteGaloisRestriction F L)

@[simp]
theorem cyclicQuotient_apply
    (n : ℕ)
    (L : IntermediateField F (AlgebraicClosure F)) [Normal F L]
    (e : (L ≃ₐ[F] L) ≃ₜ* CyclicGroup n)
    (g : Field.absoluteGaloisGroup F) :
    cyclicQuotient F n L e g = e (AlgEquiv.restrictNormalHom L g) :=
  rfl

theorem cyclicQuotient_surjective
    (n : ℕ)
    (L : IntermediateField F (AlgebraicClosure F)) [Normal F L]
    (e : (L ≃ₐ[F] L) ≃ₜ* CyclicGroup n) :
    Function.Surjective (cyclicQuotient F n L e) := by
  change Function.Surjective
    (fun g ↦ e (absoluteGaloisRestriction F L g))
  exact e.surjective.comp (absoluteGaloisRestriction_surjective F L)

end Fermat.Conservation.ContinuousCyclicQuotient
