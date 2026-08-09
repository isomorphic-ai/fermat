/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The conormal coordinate of focus

The Boolean fixed/steerable branch is the zero/nonzero shadow of a retained
linear class.  For `F : V → U` and `lambda : Vᵛ`, that class is

`a_F(lambda) = [lambda] ∈ coker(Fᵛ)`.

The canonical equivalence

`coker(Fᵛ) ≃ (ker F)ᵛ`

sends it to the restriction `lambda|ker F`.  Thus the class vanishes exactly
when `lambda` is pulled back from the output dual.  The quotient and the
restriction are choice-free; only the displayed inverse equivalence extends
functionals off a subspace and is therefore noncomputable.

This file is deliberately below `SteeringFiber` in the import graph, so the
old dichotomy can be derived from this class rather than duplicated beside
it.  No complement, section, product decomposition, or arithmetic premise is
constructed.
-/
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic

noncomputable section

namespace Fermat.Conservation.FocusConormal

universe uK uV uU

variable {K : Type uK} [Field K]
  {V : Type uV} [AddCommGroup V] [Module K V]
  {U : Type uU} [AddCommGroup U] [Module K U]

/-- The literal cokernel of the dual map `Fᵛ`. -/
abbrev CokernelDual (F : V →ₗ[K] U) :=
  Module.Dual K V ⧸ LinearMap.range F.dualMap

/-- The quotient map `lambda ↦ [lambda]` into `coker(Fᵛ)`. -/
def conormalClassMap (F : V →ₗ[K] U) :
    Module.Dual K V →ₗ[K] CokernelDual F :=
  (LinearMap.range F.dualMap).mkQ

/-- The retained focus coordinate `a_F(lambda)`. -/
def conormalClass (F : V →ₗ[K] U) (lambda : Module.Dual K V) :
    CokernelDual F :=
  conormalClassMap F lambda

/-- The same coordinate realized as restriction to `ker F`. -/
def conormalRestriction (F : V →ₗ[K] U) :
    Module.Dual K V →ₗ[K] Module.Dual K F.ker :=
  F.ker.dualRestrict

/-- The canonical linear equivalence `coker(Fᵛ) ≃ (ker F)ᵛ`.  Its inverse
uses Mathlib's extension of a functional from a subspace, but it exposes no
splitting of `V`. -/
noncomputable def cokernelDualEquivKernelDual (F : V →ₗ[K] U) :
    CokernelDual F ≃ₗ[K] Module.Dual K F.ker :=
  (Submodule.quotEquivOfEq _ _
      (LinearMap.range_dualMap_eq_dualAnnihilator_ker F)).trans
    (Subspace.quotAnnihilatorEquiv F.ker)

/-- Under the canonical equivalence, the retained quotient class is exactly
the restriction of `lambda` to `ker F`. -/
@[simp]
theorem cokernelDualEquivKernelDual_apply
    (F : V →ₗ[K] U) (lambda : Module.Dual K V) :
    cokernelDualEquivKernelDual F (conormalClass F lambda) =
      conormalRestriction F lambda := by
  simp [cokernelDualEquivKernelDual, conormalClass, conormalClassMap,
    conormalRestriction]

/-- The conormal class vanishes exactly when `lambda` lies in the image of
the dual map. -/
theorem conormalClass_eq_zero_iff_mem_range_dualMap
    (F : V →ₗ[K] U) (lambda : Module.Dual K V) :
    conormalClass F lambda = 0 ↔
      lambda ∈ LinearMap.range F.dualMap := by
  change
    (Submodule.Quotient.mk lambda :
      Module.Dual K V ⧸ LinearMap.range F.dualMap) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]

/-- Equivalently, the restriction to the lawful-flow kernel vanishes. -/
theorem conormalClass_eq_zero_iff_restriction_eq_zero
    (F : V →ₗ[K] U) (lambda : Module.Dual K V) :
    conormalClass F lambda = 0 ↔ conormalRestriction F lambda = 0 := by
  rw [conormalClass_eq_zero_iff_mem_range_dualMap,
    LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    Submodule.mem_dualAnnihilator]
  constructor
  · intro h
    ext k
    simpa [conormalRestriction] using h k.1 k.2
  · intro h k hk
    have hvalue := LinearMap.congr_fun h ⟨k, hk⟩
    simpa [conormalRestriction] using hvalue

/-- The intrinsic fixed condition: `lambda` vanishes on every lawful-flow
direction in `ker F`. -/
theorem conormalClass_eq_zero_iff_ker_le
    (F : V →ₗ[K] U) (lambda : Module.Dual K V) :
    conormalClass F lambda = 0 ↔ F.ker ≤ lambda.ker := by
  rw [conormalClass_eq_zero_iff_mem_range_dualMap,
    LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    Submodule.mem_dualAnnihilator]
  constructor <;> intro h k hk
  · exact LinearMap.mem_ker.mpr (h k hk)
  · exact LinearMap.mem_ker.mp (h hk)

/-- Vanishing is precisely factorization as a pullback along `F`. -/
theorem conormalClass_eq_zero_iff_exists_dual_pullback
    (F : V →ₗ[K] U) (lambda : Module.Dual K V) :
    conormalClass F lambda = 0 ↔
      ∃ phi : Module.Dual K U, phi.comp F = lambda := by
  rw [conormalClass_eq_zero_iff_mem_range_dualMap]
  constructor
  · rintro ⟨phi, hphi⟩
    exact ⟨phi, by simpa only [LinearMap.dualMap_apply'] using hphi⟩
  · rintro ⟨phi, hphi⟩
    exact ⟨phi, by simpa only [LinearMap.dualMap_apply'] using hphi⟩

/-- The retained class, not a separately postulated bit, supplies the
exhaustive zero/nonzero projection. -/
theorem conormalClass_zero_or_nonzero
    (F : V →ₗ[K] U) (lambda : Module.Dual K V) :
    conormalClass F lambda = 0 ∨ conormalClass F lambda ≠ 0 := by
  classical
  exact eq_or_ne _ 0

end Fermat.Conservation.FocusConormal
