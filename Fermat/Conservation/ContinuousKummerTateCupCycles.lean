/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Actual cycles for the continuous Kummer--Tate cup product

This file places the raw Alexander--Whitney cup from
`ContinuousKummerTateCupRaw` in Mathlib's genuine categorical cycles.  The
separate `ContinuousKummerTateCup` module uses these banked declarations to
descend through the continuous-homology quotients without forcing Lean to
re-expand all three homogeneous complexes in one declaration.
-/
import Fermat.Conservation.ContinuousKummerTateCupRaw

noncomputable section

namespace Fermat.Conservation.ContinuousKummerTateCup

open CategoryTheory
open ContinuousCohomology
open ContinuousKummerTateCupRaw

universe u

/-! ## Concrete facts about homology in `TopModuleCat` -/

section TopModuleHomology

variable {R : Type u} [CommRing R] [TopologicalSpace R]

/-- The underlying function of any chosen categorical cokernel projection in
`TopModuleCat` is surjective.

`TopModuleCat` does not identify arbitrary epimorphisms with surjections, so
we compare the chosen cokernel with its concrete quotient model. -/
theorem cokernelProjection_surjective
    {M N Q : TopModuleCat R} (f : M ⟶ N) (π : N ⟶ Q)
    (hzero : f ≫ π = 0)
    (h : Limits.IsColimit (Limits.CokernelCofork.ofπ π hzero)) :
    Function.Surjective π.hom := by
  let hstd := TopModuleCat.isColimitCoker f
  let e := h.coconePointUniqueUpToIso hstd
  have heq := h.comp_coconePointUniqueUpToIso_hom hstd (.one)
  intro q
  obtain ⟨x, hx⟩ := TopModuleCat.cokerπ_surjective f (e.hom q)
  refine ⟨x, (ConcreteCategory.bijective_of_isIso e.hom).1 ?_⟩
  change e.hom (π x) = e.hom q
  rw [show e.hom (π x) = TopModuleCat.cokerπ f x by
    exact ConcreteCategory.congr_hom heq x]
  exact hx

/-- Elementwise kernel criterion for any chosen categorical cokernel in
`TopModuleCat`. -/
theorem cokernelProjection_eq_zero_iff
    {M N Q : TopModuleCat R} (f : M ⟶ N) (π : N ⟶ Q)
    (hzero : f ≫ π = 0)
    (h : Limits.IsColimit (Limits.CokernelCofork.ofπ π hzero))
    (x : N) :
    π x = 0 ↔ x ∈ LinearMap.range f.hom.toLinearMap := by
  let hstd := TopModuleCat.isColimitCoker f
  let e := h.coconePointUniqueUpToIso hstd
  have heq := h.comp_coconePointUniqueUpToIso_hom hstd (.one)
  constructor
  · intro hx
    have hx' := ConcreteCategory.congr_hom heq x
    change e.hom (π x) = TopModuleCat.cokerπ f x at hx'
    rw [hx] at hx'
    have hx'' : TopModuleCat.cokerπ f x = 0 := by
      calc
        TopModuleCat.cokerπ f x = e.hom 0 := hx'.symm
        _ = 0 := e.hom.hom.map_zero
    change Submodule.mkQ (LinearMap.range f.hom.toLinearMap) x = 0 at hx''
    exact (Submodule.Quotient.mk_eq_zero
      (LinearMap.range f.hom.toLinearMap)).mp hx''
  · rintro ⟨y, rfl⟩
    exact ConcreteCategory.congr_hom hzero y

variable {K : CochainComplex (TopModuleCat R) ℕ}

/-- Mathlib's genuine homology projection has a surjective underlying
function in `TopModuleCat`. -/
theorem homologyProjection_surjective (K : CochainComplex (TopModuleCat R) ℕ)
    (i : ℕ) :
    Function.Surjective (K.homologyπ i).hom := by
  rw [show K.homologyπ i =
      (K.sc i).leftHomologyπ ≫ (K.sc i).leftHomologyIso.hom by rfl]
  have hIso : Function.Surjective ((K.sc i).leftHomologyIso.hom).hom :=
    (ConcreteCategory.bijective_of_isIso _).2
  have hLeft : Function.Surjective ((K.sc i).leftHomologyπ).hom :=
    cokernelProjection_surjective _ _ _ (K.sc i).leftHomologyData.hπ
  exact hIso.comp hLeft

/-- A class in the cycles object maps to zero in homology exactly when it is
in the range of the preceding differential lifted to cycles. -/
theorem homologyProjection_eq_zero_iff_range_toCycles
    (K : CochainComplex (TopModuleCat R) ℕ) (i j : ℕ)
    (hi : (ComplexShape.up ℕ).prev j = i) (z : K.cycles j) :
    (K.homologyπ j).hom z = 0 ↔
      z ∈ LinearMap.range (K.toCycles i j).hom.toLinearMap := by
  exact cokernelProjection_eq_zero_iff
    (K.toCycles i j) (K.homologyπ j)
    (K.toCycles_comp_homologyπ i j)
    (K.homologyIsCokernel i j hi) z

/-- The underlying function of the genuine cycles inclusion is injective. -/
theorem cyclesInclusion_injective
    (K : CochainComplex (TopModuleCat R) ℕ) (i : ℕ) :
    Function.Injective (K.iCycles i).hom := by
  have h : Function.Injective
      ((forget₂ (TopModuleCat R) TopCat).map (K.iCycles i)) :=
    ConcreteCategory.injective_of_mono_of_preservesPullback
      ((forget₂ (TopModuleCat R) TopCat).map (K.iCycles i))
  exact h

/-- Evaluation of `toCycles_i` on an element. -/
@[simp]
theorem toCycles_i_apply
    (K : CochainComplex (TopModuleCat R) ℕ) (i j : ℕ) (x : K.X i) :
    (K.iCycles j).hom ((K.toCycles i j).hom x) = (K.d i j).hom x :=
  ConcreteCategory.congr_hom (K.toCycles_i i j) x

/-- The canonical comparison from a concrete differential kernel to
Mathlib's chosen categorical cycles object. -/
def concreteKernelToCycles
    (K : CochainComplex (TopModuleCat R) ℕ) (i j : ℕ)
    (hj : (ComplexShape.up ℕ).next i = j) :
    TopModuleCat.ker (K.d i j) ⟶ K.cycles i :=
  K.liftCycles (TopModuleCat.kerι (K.d i j)) j hj (by simp)

/-- Morphism-level construction receipt for `concreteKernelToCycles`. -/
@[reassoc (attr := simp)]
theorem concreteKernelToCycles_i
    (K : CochainComplex (TopModuleCat R) ℕ) (i j : ℕ)
    (hj : (ComplexShape.up ℕ).next i = j) :
    concreteKernelToCycles K i j hj ≫ K.iCycles i =
      TopModuleCat.kerι (K.d i j) :=
  K.liftCycles_i (TopModuleCat.kerι (K.d i j)) j hj (by simp)

end TopModuleHomology

/-! ## The cup on actual categorical cycles -/

section Cup

variable {R G : Type u} [CommRing R] [TopologicalSpace R]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable {A B C : Action (TopModuleCat R) G}

/-- The degree-one cochain underlying an element of Mathlib's actual cycles
object. -/
def oneCycleCochain
    (A : Action (TopModuleCat R) G)
    (z : ((homogeneousCochains R G).obj A).cycles 1) :
    ((homogeneousCochains R G).obj A).X 1 :=
  (((homogeneousCochains R G).obj A).iCycles 1).hom z

/-- The cochain underlying an actual degree-one cycle is killed by the
differential. -/
theorem oneCycleCochain_isCycle
    (A : Action (TopModuleCat R) G)
    (z : ((homogeneousCochains R G).obj A).cycles 1) :
    (((homogeneousCochains R G).obj A).d 1 2).hom
      (oneCycleCochain A z) = 0 := by
  let K := (homogeneousCochains R G).obj A
  exact ConcreteCategory.congr_hom (K.iCycles_d 1 2) z

/-- Readback of a degree-zero boundary after it has been lifted to the actual
degree-one cycles object. -/
@[simp]
theorem oneCycleCochain_toCycles
    (A : Action (TopModuleCat R) G)
    (a : ((homogeneousCochains R G).obj A).X 0) :
    @Eq (((homogeneousCochains R G).obj A).X 1)
      (oneCycleCochain A
        ((((homogeneousCochains R G).obj A).toCycles 0 1).hom a))
      ((((homogeneousCochains R G).obj A).d 0 1).hom a) :=
  toCycles_i_apply ((homogeneousCochains R G).obj A) 0 1 a

variable [LocallyCompactSpace G]

set_option maxHeartbeats 800000 in
/-- The raw cup of two actual one-cycles, bundled in the concrete kernel of
the degree-two differential. -/
def cupKernel
    (p : ContinuousEquivariantPairing A B C)
    (f : ((homogeneousCochains R G).obj A).cycles 1)
    (g : ((homogeneousCochains R G).obj B).cycles 1) :
    TopModuleCat.ker (((homogeneousCochains R G).obj C).d 2 3) := by
  refine ⟨cupCochain p (oneCycleCochain A f) (oneCycleCochain B g), ?_⟩
  exact cupCochain_isCycle p (oneCycleCochain A f) (oneCycleCochain B g)
    (oneCycleCochain_isCycle A f) (oneCycleCochain_isCycle B g)

set_option maxHeartbeats 800000 in
/-- The canonical comparison from the concrete degree-two kernel to
Mathlib's chosen categorical cycles object. -/
def twoKernelToCycles (C : Action (TopModuleCat R) G) :
    TopModuleCat.ker (((homogeneousCochains R G).obj C).d 2 3) ⟶
      ((homogeneousCochains R G).obj C).cycles 2 :=
  let K := (homogeneousCochains R G).obj C
  K.liftCycles (TopModuleCat.kerι (K.d 2 3)) 3
    ((ComplexShape.up ℕ).next_eq' (by simp)) (by simp)

/-- The raw cup of two actual degree-one cycles, now placed in Mathlib's
actual degree-two cycles object. -/
def cupCycle
    (p : ContinuousEquivariantPairing A B C)
    (f : ((homogeneousCochains R G).obj A).cycles 1)
    (g : ((homogeneousCochains R G).obj B).cycles 1) :
    ((homogeneousCochains R G).obj C).cycles 2 :=
  (twoKernelToCycles C).hom (cupKernel p f g)

end Cup

end Fermat.Conservation.ContinuousKummerTateCup
