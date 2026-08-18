/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Nominal carriers for the continuous Kummer--Tate cup

Mathlib's concrete homogeneous continuous-cochain carriers are deeply nested
subtypes of iterated continuous maps. Repeatedly exposing those carriers in
bilinear public declarations can make elaboration unfold the entire complex.

This module puts honest, small nominal shells around cochains, cocycles, and
genuine categorical homology. Every shell is linearly
equivalent to the object it wraps. The Alexander--Whitney cup is transported
to those shells, explicit primitives prove that it kills boundaries in both
arguments, and `LinearMap.liftQ₂` descends it through the two actual homology
projections. No representative is chosen and no mathematical content is
weakened; the wrappers are solely an elaboration boundary.
-/
import Fermat.Conservation.ContinuousKummerTateCupCycles
import Mathlib.LinearAlgebra.Quotient.Bilinear

noncomputable section

namespace Fermat.Conservation.ContinuousKummerTateCup.Nominal

open CategoryTheory
open ContinuousCohomology
open Fermat.Conservation.ContinuousKummerTateCupRaw
open Fermat.Conservation.ContinuousKummerTateCup

universe u v

variable {R G : Type u} [CommRing R] [TopologicalSpace R]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable {A B C : Action (TopModuleCat R) G}

/-! A genuinely nominal shell: users see `Cochain A i`, rather than the
very large concrete homogeneous-cochain carrier. -/

structure Cochain (A : Action (TopModuleCat R) G) (i : ℕ) where
  val : ((homogeneousCochains R G).obj A).X i

@[ext]
theorem Cochain.ext {A : Action (TopModuleCat R) G} {i : ℕ}
    {x y : Cochain A i} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  cases h
  rfl

def cochainEquiv (A : Action (TopModuleCat R) G) (i : ℕ) :
    Cochain A i ≃ ((homogeneousCochains R G).obj A).X i where
  toFun := Cochain.val
  invFun := Cochain.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance cochainAddCommGroup
    (A : Action (TopModuleCat R) G) (i : ℕ) : AddCommGroup (Cochain A i) :=
  Equiv.addCommGroup (cochainEquiv A i)

instance cochainModule
    (A : Action (TopModuleCat R) G) (i : ℕ) : Module R (Cochain A i) :=
  Equiv.module R (cochainEquiv A i)

def cochainLinearEquiv (A : Action (TopModuleCat R) G) (i : ℕ) :
    Cochain A i ≃ₗ[R] ((homogeneousCochains R G).obj A).X i :=
  (cochainEquiv A i).linearEquiv R

@[simp]
theorem cochainLinearEquiv_apply
    (A : Action (TopModuleCat R) G) (i : ℕ) (x : Cochain A i) :
    cochainLinearEquiv A i x = x.val := rfl

@[simp]
theorem cochainLinearEquiv_symm_apply
    (A : Action (TopModuleCat R) G) (i : ℕ)
    (x : ((homogeneousCochains R G).obj A).X i) :
    (cochainLinearEquiv A i).symm x = ⟨x⟩ := rfl

/-- The actual homogeneous differential, transported to nominal shells. -/
def differential (A : Action (TopModuleCat R) G) (i j : ℕ) :
    Cochain A i →ₗ[R] Cochain A j :=
  (cochainLinearEquiv A j).symm.toLinearMap.comp
    ((((homogeneousCochains R G).obj A).d i j).hom.toLinearMap.comp
      (cochainLinearEquiv A i).toLinearMap)

@[simp]
theorem differential_val
    (A : Action (TopModuleCat R) G) (i j : ℕ) (x : Cochain A i) :
    (differential A i j x).val =
      (((homogeneousCochains R G).obj A).d i j).hom x.val := rfl

/-! The cycle shell stores a nominal cochain and its nominal closedness
proof. The concrete differential kernel is reached only through an explicit
linear equivalence below. -/

structure Cycle (A : Action (TopModuleCat R) G) (i j : ℕ) where
  cochain : Cochain A i
  isCycle : differential A i j cochain = 0

@[ext]
theorem Cycle.ext {A : Action (TopModuleCat R) G} {i j : ℕ}
    {x y : Cycle A i j} (h : x.cochain = y.cochain) : x = y := by
  cases x
  cases y
  cases h
  rfl

def cycleEquiv (A : Action (TopModuleCat R) G) (i j : ℕ) :
    Cycle A i j ≃ LinearMap.ker (differential A i j) where
  toFun z := ⟨z.cochain, z.isCycle⟩
  invFun z := ⟨z.1, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance cycleAddCommGroup
    (A : Action (TopModuleCat R) G) (i j : ℕ) : AddCommGroup (Cycle A i j) :=
  Equiv.addCommGroup (cycleEquiv A i j)

instance cycleModule
    (A : Action (TopModuleCat R) G) (i j : ℕ) : Module R (Cycle A i j) :=
  Equiv.module R (cycleEquiv A i j)

def cycleLinearEquiv (A : Action (TopModuleCat R) G) (i j : ℕ) :
    Cycle A i j ≃ₗ[R] LinearMap.ker (differential A i j) :=
  (cycleEquiv A i j).linearEquiv R

/-- Forget closedness but keep the nominal cochain carrier. -/
def cycleCochain (A : Action (TopModuleCat R) G) (i j : ℕ) :
    Cycle A i j →ₗ[R] Cochain A i :=
  (LinearMap.ker (differential A i j)).subtype.comp
    (cycleLinearEquiv A i j).toLinearMap

@[simp]
theorem cycleCochain_val
    (A : Action (TopModuleCat R) G) (i j : ℕ) (z : Cycle A i j) :
    cycleCochain A i j z = z.cochain := rfl

@[simp]
theorem differential_cycleCochain
    (A : Action (TopModuleCat R) G) (i j : ℕ) (z : Cycle A i j) :
    differential A i j (cycleCochain A i j z) = 0 := by
  exact z.isCycle

/-- The nominal cycle shell is honestly linearly equivalent to the concrete
kernel of Mathlib's homogeneous differential. -/
def cycleConcreteEquiv (A : Action (TopModuleCat R) G) (i j : ℕ) :
    Cycle A i j ≃ TopModuleCat.ker (((homogeneousCochains R G).obj A).d i j) where
  toFun z := ⟨z.cochain.val, by
    exact congrArg Cochain.val z.isCycle⟩
  invFun z := ⟨⟨z.1⟩, by
    apply Cochain.ext
    exact z.2⟩
  left_inv z := by
    apply Cycle.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    rfl

def cycleConcreteLinearEquiv (A : Action (TopModuleCat R) G) (i j : ℕ) :
    Cycle A i j ≃ₗ[R]
      TopModuleCat.ker (((homogeneousCochains R G).obj A).d i j) where
  __ := cycleConcreteEquiv A i j
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' r x := by
    apply Subtype.ext
    rfl

variable [LocallyCompactSpace G]

/-! The closed nominal cup. Keeping the proof in a helper constructor banks
the only expansion of the degree-two homogeneous carrier. -/

set_option maxHeartbeats 800000 in
def cupCycleValue
    (p : ContinuousEquivariantPairing A B C)
    (f : Cycle A 1 2) (g : Cycle B 1 2) : Cycle C 2 3 :=
  by
    refine ⟨⟨cupCochain p f.cochain.val g.cochain.val⟩, ?_⟩
    apply Cochain.ext
    apply cupCochain_isCycle
    · exact congrArg Cochain.val f.isCycle
    · exact congrArg Cochain.val g.isCycle

@[simp]
theorem cupCycleValue_cochain
    (p : ContinuousEquivariantPairing A B C)
    (f : Cycle A 1 2) (g : Cycle B 1 2) :
    (cupCycleValue p f g).cochain =
      ⟨cupCochain p f.cochain.val g.cochain.val⟩ := rfl

set_option maxHeartbeats 800000 in
def nominalCycleCup
    (p : ContinuousEquivariantPairing A B C) :
    Cycle A 1 2 →ₗ[R] Cycle B 1 2 →ₗ[R] Cycle C 2 3 :=
  LinearMap.mk₂ R (cupCycleValue p)
    (by
      intro f₁ f₂ g
      apply Cycle.ext
      apply Cochain.ext
      exact (cupCochainLinear p).map_add₂
        f₁.cochain.val f₂.cochain.val g.cochain.val)
    (by
      intro r f g
      apply Cycle.ext
      apply Cochain.ext
      exact (cupCochainLinear p).map_smul₂ r f.cochain.val g.cochain.val)
    (by
      intro f g₁ g₂
      apply Cycle.ext
      apply Cochain.ext
      exact ((cupCochainLinear p) f.cochain.val).map_add
        g₁.cochain.val g₂.cochain.val)
    (by
      intro r f g
      apply Cycle.ext
      apply Cochain.ext
      exact ((cupCochainLinear p) f.cochain.val).map_smul r g.cochain.val)

/-! ## Small public route to genuine continuous homology

The target is wrapped too, so consumers need not carry the implementation
of Mathlib's categorical homology object in every subsequent type. -/

structure Homology (A : Action (TopModuleCat R) G) (i : ℕ) where
  val : ((homogeneousCochains R G).obj A).homology i

def homologyEquiv (A : Action (TopModuleCat R) G) (i : ℕ) :
    Homology A i ≃ ((homogeneousCochains R G).obj A).homology i where
  toFun := Homology.val
  invFun := Homology.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance homologyAddCommGroup
    (A : Action (TopModuleCat R) G) (i : ℕ) : AddCommGroup (Homology A i) :=
  Equiv.addCommGroup (homologyEquiv A i)

instance homologyModule
    (A : Action (TopModuleCat R) G) (i : ℕ) : Module R (Homology A i) :=
  Equiv.module R (homologyEquiv A i)

def homologyLinearEquiv (A : Action (TopModuleCat R) G) (i : ℕ) :
    Homology A i ≃ₗ[R] ((homogeneousCochains R G).obj A).homology i :=
  (homologyEquiv A i).linearEquiv R

/-- Compare a concrete differential kernel with Mathlib's chosen cycles
object. This is the same universal construction used by the active cup
implementation, restated here so its result remains behind a nominal shell. -/
def kernelToCategoricalCycles
    (K : CochainComplex (TopModuleCat R) ℕ) (i j : ℕ)
    (hnext : (ComplexShape.up ℕ).next i = j) :
    TopModuleCat.ker (K.d i j) ⟶ K.cycles i :=
  K.liftCycles (TopModuleCat.kerι (K.d i j)) j hnext (by simp)

@[reassoc (attr := simp)]
theorem kernelToCategoricalCycles_i
    (K : CochainComplex (TopModuleCat R) ℕ) (i j : ℕ)
    (hnext : (ComplexShape.up ℕ).next i = j) :
    kernelToCategoricalCycles K i j hnext ≫ K.iCycles i =
      TopModuleCat.kerι (K.d i j) :=
  K.liftCycles_i (TopModuleCat.kerι (K.d i j)) j hnext (by simp)

theorem kernelToCategoricalCycles_surjective
    (K : CochainComplex (TopModuleCat R) ℕ) (i j : ℕ)
    (hnext : (ComplexShape.up ℕ).next i = j) :
    Function.Surjective (kernelToCategoricalCycles K i j hnext).hom := by
  intro z
  let q : TopModuleCat.ker (K.d i j) :=
    ⟨(K.iCycles i).hom z, by
      exact ConcreteCategory.congr_hom (K.iCycles_d i j) z⟩
  refine ⟨q, ?_⟩
  apply cyclesInclusion_injective K i
  exact ConcreteCategory.congr_hom
    (kernelToCategoricalCycles_i K i j hnext) q

def kernelHomologyProjection
    (K : CochainComplex (TopModuleCat R) ℕ) (i j : ℕ)
    (hnext : (ComplexShape.up ℕ).next i = j) :
    TopModuleCat.ker (K.d i j) →ₗ[R] K.homology i :=
  (K.homologyπ i).hom.toLinearMap.comp
    (kernelToCategoricalCycles K i j hnext).hom.toLinearMap

theorem kernelHomologyProjection_surjective
    (K : CochainComplex (TopModuleCat R) ℕ) (i j : ℕ)
    (hnext : (ComplexShape.up ℕ).next i = j) :
    Function.Surjective (kernelHomologyProjection K i j hnext) :=
  (homologyProjection_surjective K i).comp
    (kernelToCategoricalCycles_surjective K i j hnext)

theorem kernelHomologyProjection_eq_zero_iff
    (K : CochainComplex (TopModuleCat R) ℕ) (k i j : ℕ)
    (hnext : (ComplexShape.up ℕ).next i = j)
    (hprev : (ComplexShape.up ℕ).prev i = k)
    (z : TopModuleCat.ker (K.d i j)) :
    kernelHomologyProjection K i j hnext z = 0 ↔
      ∃ x : K.X k, (K.d k i).hom x = z.1 := by
  constructor
  · intro hz
    have hz' : (K.homologyπ i).hom
        ((kernelToCategoricalCycles K i j hnext).hom z) = 0 := hz
    rw [homologyProjection_eq_zero_iff_range_toCycles K k i hprev] at hz'
    obtain ⟨x, hx⟩ := hz'
    refine ⟨x, ?_⟩
    have hxi := congrArg (K.iCycles i).hom hx
    have hleft := toCycles_i_apply K k i x
    have hright := ConcreteCategory.congr_hom
      (kernelToCategoricalCycles_i K i j hnext) z
    calc
      (K.d k i).hom x =
          (K.iCycles i).hom (↑((K.toCycles k i).hom x)) := hleft.symm
      _ = (K.iCycles i).hom
          ((kernelToCategoricalCycles K i j hnext).hom z) := hxi
      _ = z.1 := hright
  · rintro ⟨x, hx⟩
    change (K.homologyπ i).hom
      ((kernelToCategoricalCycles K i j hnext).hom z) = 0
    rw [homologyProjection_eq_zero_iff_range_toCycles K k i hprev]
    refine ⟨x, ?_⟩
    apply cyclesInclusion_injective K i
    calc
      (K.iCycles i).hom (↑((K.toCycles k i).hom x)) =
          (K.d k i).hom x := toCycles_i_apply K k i x
      _ = z.1 := hx
      _ = (K.iCycles i).hom
          ((kernelToCategoricalCycles K i j hnext).hom z) := by
        symm
        exact ConcreteCategory.congr_hom
          (kernelToCategoricalCycles_i K i j hnext) z

/-- A nominal closed cochain projected all the way into genuine categorical
continuous homology. Its exposed type contains only nominal carriers. -/
def cycleToHomology
    (A : Action (TopModuleCat R) G) (i j : ℕ)
    (hnext : (ComplexShape.up ℕ).next i = j) :
    Cycle A i j →ₗ[R] Homology A i :=
  (homologyLinearEquiv A i).symm.toLinearMap.comp
    ((kernelHomologyProjection
      ((homogeneousCochains R G).obj A) i j hnext).comp
      (cycleConcreteLinearEquiv A i j).toLinearMap)

omit [LocallyCompactSpace G] in
theorem cycleToHomology_surjective
    (A : Action (TopModuleCat R) G) (i j : ℕ)
    (hnext : (ComplexShape.up ℕ).next i = j) :
    Function.Surjective (cycleToHomology A i j hnext) :=
  (homologyLinearEquiv A i).symm.surjective.comp
    ((kernelHomologyProjection_surjective
      ((homogeneousCochains R G).obj A) i j hnext).comp
      (cycleConcreteLinearEquiv A i j).surjective)

omit [LocallyCompactSpace G] in
theorem cycleToHomology_eq_zero_iff
    (A : Action (TopModuleCat R) G) (k i j : ℕ)
    (hnext : (ComplexShape.up ℕ).next i = j)
    (hprev : (ComplexShape.up ℕ).prev i = k)
    (z : Cycle A i j) :
    cycleToHomology A i j hnext z = 0 ↔
      ∃ x : Cochain A k,
        differential A k i x = cycleCochain A i j z := by
  rw [show cycleToHomology A i j hnext z = 0 ↔
      kernelHomologyProjection ((homogeneousCochains R G).obj A)
        i j hnext (cycleConcreteLinearEquiv A i j z) = 0 by
    exact (homologyLinearEquiv A i).symm.injective.eq_iff]
  rw [kernelHomologyProjection_eq_zero_iff
    ((homogeneousCochains R G).obj A) k i j hnext hprev]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨(cochainLinearEquiv A k).symm x, ?_⟩
    apply Cochain.ext
    exact hx
  · rintro ⟨x, hx⟩
    refine ⟨(cochainLinearEquiv A k) x, ?_⟩
    exact congrArg Cochain.val hx

def h1Projection (A : Action (TopModuleCat R) G) :
    Cycle A 1 2 →ₗ[R] Homology A 1 :=
  cycleToHomology A 1 2 ((ComplexShape.up ℕ).next_eq' (by simp))

def h2Projection (A : Action (TopModuleCat R) G) :
    Cycle A 2 3 →ₗ[R] Homology A 2 :=
  cycleToHomology A 2 3 ((ComplexShape.up ℕ).next_eq' (by simp))

omit [LocallyCompactSpace G] in
theorem h1Projection_surjective (A : Action (TopModuleCat R) G) :
    Function.Surjective (h1Projection A) :=
  cycleToHomology_surjective A 1 2
    ((ComplexShape.up ℕ).next_eq' (by simp))

omit [LocallyCompactSpace G] in
theorem h1Projection_eq_zero_iff
    (A : Action (TopModuleCat R) G) (z : Cycle A 1 2) :
    h1Projection A z = 0 ↔
      ∃ x : Cochain A 0,
        differential A 0 1 x = cycleCochain A 1 2 z :=
  cycleToHomology_eq_zero_iff A 0 1 2
    ((ComplexShape.up ℕ).next_eq' (by simp))
    ((ComplexShape.up ℕ).prev_eq' (by simp)) z

omit [LocallyCompactSpace G] in
theorem h2Projection_eq_zero_iff
    (A : Action (TopModuleCat R) G) (z : Cycle A 2 3) :
    h2Projection A z = 0 ↔
      ∃ x : Cochain A 1,
        differential A 1 2 x = cycleCochain A 2 3 z :=
  cycleToHomology_eq_zero_iff A 1 2 3
    ((ComplexShape.up ℕ).next_eq' (by simp))
    ((ComplexShape.up ℕ).prev_eq' (by simp)) z

/-- The closed raw cup followed by the honest projection into second
continuous homology. This is the small bilinear input used by the double
quotient descent below. -/
def nominalCycleCupToH2
    (p : ContinuousEquivariantPairing A B C) :
    Cycle A 1 2 →ₗ[R] Cycle B 1 2 →ₗ[R] Homology C 2 :=
  (nominalCycleCup p).compr₂ (h2Projection C)

theorem nominalCycleCupToH2_kills_left
    (p : ContinuousEquivariantPairing A B C)
    (f : Cycle A 1 2) (hf : h1Projection A f = 0)
    (g : Cycle B 1 2) :
    nominalCycleCupToH2 p f g = 0 := by
  rw [h1Projection_eq_zero_iff] at hf
  obtain ⟨a, ha⟩ := hf
  change h2Projection C (cupCycleValue p f g) = 0
  rw [h2Projection_eq_zero_iff]
  refine ⟨⟨cupZeroOne p a.val g.cochain.val⟩, ?_⟩
  rw [cycleCochain_val, cupCycleValue_cochain]
  have haNom : differential A 0 1 a = f.cochain := by
    simpa only [cycleCochain_val] using ha
  rw [← haNom]
  apply Cochain.ext
  rw [differential_val, differential_val]
  exact (cupCochain_zeroBoundary_left p a.val g.cochain.val
    (congrArg Cochain.val g.isCycle)).symm

theorem nominalCycleCupToH2_kills_right
    (p : ContinuousEquivariantPairing A B C)
    (f : Cycle A 1 2)
    (g : Cycle B 1 2) (hg : h1Projection B g = 0) :
    nominalCycleCupToH2 p f g = 0 := by
  rw [h1Projection_eq_zero_iff] at hg
  obtain ⟨b, hb⟩ := hg
  change h2Projection C (cupCycleValue p f g) = 0
  rw [h2Projection_eq_zero_iff]
  refine ⟨⟨cupOneZeroNegative p f.cochain.val b.val⟩, ?_⟩
  rw [cycleCochain_val, cupCycleValue_cochain]
  have hbNom : differential B 0 1 b = g.cochain := by
    simpa only [cycleCochain_val] using hb
  rw [← hbNom]
  apply Cochain.ext
  rw [differential_val, differential_val]
  exact (cupCochain_zeroBoundary_right p f.cochain.val
    (congrArg Cochain.val f.isCycle) b.val).symm

/-! The abstract quotient combinator is deliberately declared after the
nominal cochain algebra. This keeps semilinear-composition elaboration from
polluting the large transported maps above. -/

omit [TopologicalSpace R] in
theorem ker_le_bilinear_ker_left
    {M N P M' : Type v}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [AddCommGroup M'] [Module R M] [Module R N] [Module R P] [Module R M']
    (f : M →ₗ[R] N →ₗ[R] P) (qM : M →ₗ[R] M')
    (h : ∀ m, qM m = 0 → ∀ n, f m n = 0) :
    LinearMap.ker qM ≤ LinearMap.ker f := by
  intro m hm
  rw [LinearMap.mem_ker] at hm ⊢
  ext n
  exact h m hm n

omit [TopologicalSpace R] in
theorem ker_le_bilinear_ker_right
    {M N P N' : Type v}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [AddCommGroup N'] [Module R M] [Module R N] [Module R P] [Module R N']
    (f : M →ₗ[R] N →ₗ[R] P) (qN : N →ₗ[R] N')
    (h : ∀ n, qN n = 0 → ∀ m, f m n = 0) :
    LinearMap.ker qN ≤ LinearMap.ker f.flip := by
  intro n hn
  rw [LinearMap.mem_ker] at hn ⊢
  ext m
  exact h n hn m

noncomputable def descendBilinearAlongSurjectionsOfPointwiseZero
    {M N P M' N' : Type v}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [AddCommGroup M'] [AddCommGroup N']
    [Module R M] [Module R N] [Module R P]
    [Module R M'] [Module R N']
    (f : M →ₗ[R] N →ₗ[R] P)
    (qM : M →ₗ[R] M') (qN : N →ₗ[R] N')
    (hqM : Function.Surjective qM) (hqN : Function.Surjective qN)
    (hM : ∀ m, qM m = 0 → ∀ n, f m n = 0)
    (hN : ∀ n, qN n = 0 → ∀ m, f m n = 0) :
    M' →ₗ[R] N' →ₗ[R] P :=
  (f.liftQ₂ (LinearMap.ker qM) (LinearMap.ker qN)
      (ker_le_bilinear_ker_left f qM hM)
      (ker_le_bilinear_ker_right f qN hN)).compl₁₂
    (qM.quotKerEquivOfSurjective hqM).symm.toLinearMap
    (qN.quotKerEquivOfSurjective hqN).symm.toLinearMap

omit [TopologicalSpace R] in
@[simp]
theorem descendBilinearAlongSurjectionsOfPointwiseZero_apply
    {M N P M' N' : Type v}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [AddCommGroup M'] [AddCommGroup N']
    [Module R M] [Module R N] [Module R P]
    [Module R M'] [Module R N']
    (f : M →ₗ[R] N →ₗ[R] P)
    (qM : M →ₗ[R] M') (qN : N →ₗ[R] N')
    (hqM : Function.Surjective qM) (hqN : Function.Surjective qN)
    (hM : ∀ m, qM m = 0 → ∀ n, f m n = 0)
    (hN : ∀ n, qN n = 0 → ∀ m, f m n = 0)
    (m : M) (n : N) :
    descendBilinearAlongSurjectionsOfPointwiseZero
        f qM qN hqM hqN hM hN (qM m) (qN n) = f m n := by
  change
    (f.liftQ₂ (LinearMap.ker qM) (LinearMap.ker qN)
      (ker_le_bilinear_ker_left f qM hM)
      (ker_le_bilinear_ker_right f qN hN))
        ((qM.quotKerEquivOfSurjective hqM).symm (qM m))
        ((qN.quotKerEquivOfSurjective hqN).symm (qN n)) = f m n
  rw [qM.quotKerEquivOfSurjective_symm_apply hqM m,
    qN.quotKerEquivOfSurjective_symm_apply hqN n,
    LinearMap.liftQ₂_mk]

/-- A descended bilinear map bundled with its computation rule. Banking the
rule with the abstract construction prevents later specializations from
re-elaborating the quotient internals. -/
structure DescendedBilinearReceipt
    {M N P M' N' : Type v}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [AddCommGroup M'] [AddCommGroup N']
    [Module R M] [Module R N] [Module R P]
    [Module R M'] [Module R N']
    (f : M →ₗ[R] N →ₗ[R] P)
    (qM : M →ₗ[R] M') (qN : N →ₗ[R] N') where
  map : M' →ₗ[R] N' →ₗ[R] P
  map_projection : ∀ m n, map (qM m) (qN n) = f m n

noncomputable def descendBilinearReceipt
    {M N P M' N' : Type v}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [AddCommGroup M'] [AddCommGroup N']
    [Module R M] [Module R N] [Module R P]
    [Module R M'] [Module R N']
    (f : M →ₗ[R] N →ₗ[R] P)
    (qM : M →ₗ[R] M') (qN : N →ₗ[R] N')
    (hqM : Function.Surjective qM) (hqN : Function.Surjective qN)
    (hM : ∀ m, qM m = 0 → ∀ n, f m n = 0)
    (hN : ∀ n, qN n = 0 → ∀ m, f m n = 0) :
    DescendedBilinearReceipt f qM qN where
  map := descendBilinearAlongSurjectionsOfPointwiseZero
    f qM qN hqM hqN hM hN
  map_projection := descendBilinearAlongSurjectionsOfPointwiseZero_apply
    f qM qN hqM hqN hM hN

/-- The specialized continuous-cup receipt. Its carriers stay nominal while
its computation rule records projection from arbitrary honest cocycles. -/
structure NominalCupReceipt
    (p : ContinuousEquivariantPairing A B C) where
  map : Homology A 1 →ₗ[R] Homology B 1 →ₗ[R] Homology C 2
  map_projection : ∀ (f : Cycle A 1 2) (g : Cycle B 1 2),
    map (h1Projection A f) (h1Projection B g) =
      nominalCycleCupToH2 p f g

noncomputable def nominalCupReceipt
    (p : ContinuousEquivariantPairing A B C) : NominalCupReceipt p := by
  let r := descendBilinearReceipt
    (R := R)
    (nominalCycleCupToH2 p)
    (h1Projection A) (h1Projection B)
    (h1Projection_surjective A) (h1Projection_surjective B)
    (fun f hf g => nominalCycleCupToH2_kills_left p f hf g)
    (fun g hg f => nominalCycleCupToH2_kills_right p f g hg)
  exact ⟨r.map, r.map_projection⟩

/-! No representatives are selected: `liftQ₂` performs both quotient
descents inside `descendBilinearReceipt`. -/
/-- The honest cup product on genuine first continuous homology, expressed
through nominal shells so the public type stays cheap for Lean to elaborate. -/
noncomputable def nominalCupH1
    (p : ContinuousEquivariantPairing A B C) :
    Homology A 1 →ₗ[R] Homology B 1 →ₗ[R] Homology C 2 :=
  (nominalCupReceipt p).map

/-- Representative-independent computation rule for the descended cup. -/
@[simp]
theorem nominalCupH1_projection
    (p : ContinuousEquivariantPairing A B C)
    (f : Cycle A 1 2) (g : Cycle B 1 2) :
    nominalCupH1 p (h1Projection A f) (h1Projection B g) =
      nominalCycleCupToH2 p f g := by
  exact (nominalCupReceipt p).map_projection f g

end Fermat.Conservation.ContinuousKummerTateCup.Nominal
