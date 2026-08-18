/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Prime-parametric continuous carry lift obstruction

For every prime `p`, the standard carry cocycle is the extension class of
`C_(p²) → C_p`.  Pulling it back along a continuous character
`χ : G → C_p` gives a boundary exactly when `χ` lifts continuously to
`C_(p²)`.  Both implications construct their witnesses explicitly, and
the equivalence is then transported through genuine continuous homology.
-/
import Fermat.Conservation.PrimeCyclicExtension
import Fermat.Conservation.PrimeContinuousHomogeneousPullback

noncomputable section

open CategoryTheory ContinuousCohomology
open Fermat.Conservation.ContinuousKummerTateCupRaw
open Fermat.Conservation.ContinuousKummerTateCup.Nominal

namespace Fermat.Conservation.PrimeContinuousCarryLift

open Fermat.Conservation.PrimeCyclicExtension
open Fermat.Conservation.PrimeContinuousHomogeneousPullback

variable {p : ℕ} [Fact p.Prime]
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

local instance : ContinuousMul (CyclicGroupSquared p) :=
  ⟨continuous_of_discreteTopology⟩

@[simp] theorem standardSection_one : standardSection p 1 = 1 := by
  simp [standardSection]

/-- Pull the explicit continuous carry cycle back along `chi`. -/
def pulledCarryCycle (chi : G →ₜ* CyclicGroup p) :
    Cycle (coefficients p G) 2 3 :=
  pullbackCycleTwo p chi (PrimeCyclicH2.continuousCarryCycle p)

/-- The assertion that a continuous character has no continuous lift through
reduction from `C_(p²)`. -/
abbrev NoContinuousLift (chi : G →ₜ* CyclicGroup p) : Prop :=
  ¬ ∃ psi : G →ₜ* CyclicGroupSquared p, (reduction p).comp psi = chi

/-- Evaluate a homogeneous boundary primitive at `(1,g)`. -/
def primitiveValue
    (b : Cochain (coefficients p G) 1) (g : G) : ZMod p :=
  oneValue b.val 1 g

/-- Correct the standard section by the negative of the supplied primitive. -/
def liftedValue
    (chi : G →ₜ* CyclicGroup p)
    (b : Cochain (coefficients p G) 1) (g : G) : CyclicGroupSquared p :=
  standardSection p (chi g) *
    (kernelEmbed p (Multiplicative.ofAdd (primitiveValue b g)))⁻¹

@[simp] theorem coefficientsOneDifferential_apply
    (b : Cochain (coefficients p G) 1) (w x y : G) :
    twoValue
      ((((homogeneousCochains (ZMod p) G).obj
        (coefficients p G)).d 1 2).hom b.val) w x y =
      oneValue b.val x y - (oneValue b.val w y - oneValue b.val w x) :=
  rfl

@[simp] theorem pulledCarryCycle_apply
    (chi : G →ₜ* CyclicGroup p) (w x y : G) :
    twoValue (pulledCarryCycle chi).cochain.val w x y =
      PrimeCyclicH2.carry p ((chi w)⁻¹ * chi x).toAdd ((chi x)⁻¹ * chi y).toAdd := by
  rfl

/-- The boundary equation, written as the inhomogeneous correction law
needed by the lift. -/
theorem boundary_primitive_equation
    (chi : G →ₜ* CyclicGroup p)
    (b : Cochain (coefficients p G) 1)
    (hb : differential (coefficients p G) 1 2 b =
      cycleCochain (coefficients p G) 2 3
        (pulledCarryCycle chi))
    (g h : G) :
    primitiveValue b h - primitiveValue b (g * h) + primitiveValue b g =
      PrimeCyclicH2.carry p (chi g).toAdd (chi h).toAdd := by
  have hpoint := congrArg
    (fun q : Cochain (coefficients p G) 2 ↦ twoValue q.val 1 g (g * h)) hb
  rw [differential_val, cycleCochain_val] at hpoint
  rw [coefficientsOneDifferential_apply, pulledCarryCycle_apply] at hpoint
  simp only [map_one, inv_one, one_mul, map_mul, inv_mul_cancel_left] at hpoint
  change
    (show ZMod p from oneValue b.val g (g * h)) -
        ((show ZMod p from oneValue b.val 1 (g * h)) -
          (show ZMod p from oneValue b.val 1 g)) =
      PrimeCyclicH2.carry p (chi g).toAdd (chi h).toAdd at hpoint
  have hinv := oneValue_invariant b.val g g (g * h)
  have hinv' : oneValue b.val 1 h = oneValue b.val g (g * h) := by
    simpa using hinv
  rw [primitiveValue, primitiveValue, primitiveValue, hinv']
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hpoint

theorem primitiveValue_one
    (chi : G →ₜ* CyclicGroup p)
    (b : Cochain (coefficients p G) 1)
    (hb : differential (coefficients p G) 1 2 b =
      cycleCochain (coefficients p G) 2 3
        (pulledCarryCycle chi)) :
    primitiveValue b 1 = 0 := by
  have h := boundary_primitive_equation chi b hb 1 1
  simpa [PrimeCyclicH2.carry, (Fact.out : Nat.Prime p).ne_zero] using h

theorem liftedValue_one
    (chi : G →ₜ* CyclicGroup p)
    (b : Cochain (coefficients p G) 1)
    (hb : differential (coefficients p G) 1 2 b =
      cycleCochain (coefficients p G) 2 3
        (pulledCarryCycle chi)) :
    liftedValue chi b 1 = 1 := by
  simp [liftedValue, primitiveValue_one chi b hb]

/-- The finite cyclic algebra identity converting the primitive equation
into the multiplication law for the corrected section. -/
theorem liftAlgebra_identity
    (x y : CyclicGroup p) (qx qy qxy : ZMod p)
    (hq : qx + qy = qxy + PrimeCyclicH2.carry p x.toAdd y.toAdd) :
    standardSection p (x * y) *
        (kernelEmbed p (Multiplicative.ofAdd qxy))⁻¹ =
      (standardSection p x *
          (kernelEmbed p (Multiplicative.ofAdd qx))⁻¹) *
        (standardSection p y *
          (kernelEmbed p (Multiplicative.ofAdd qy))⁻¹) := by
  have hqmul :
      Multiplicative.ofAdd qx * Multiplicative.ofAdd qy =
        Multiplicative.ofAdd qxy *
          Multiplicative.ofAdd (PrimeCyclicH2.carry p x.toAdd y.toAdd) := by
    exact congrArg Multiplicative.ofAdd hq
  have hK := congrArg (kernelEmbed p) hqmul
  simp only [map_mul] at hK
  symm
  calc
    (standardSection p x *
          (kernelEmbed p (Multiplicative.ofAdd qx))⁻¹) *
        (standardSection p y *
          (kernelEmbed p (Multiplicative.ofAdd qy))⁻¹) =
      (standardSection p x * standardSection p y) *
        (kernelEmbed p (Multiplicative.ofAdd qx) *
          kernelEmbed p (Multiplicative.ofAdd qy))⁻¹ := by
            rw [mul_inv_rev]
            ac_rfl
    _ = (standardSection p (x * y) *
          kernelEmbed p
            (Multiplicative.ofAdd (PrimeCyclicH2.carry p x.toAdd y.toAdd))) *
        (kernelEmbed p (Multiplicative.ofAdd qx) *
          kernelEmbed p (Multiplicative.ofAdd qy))⁻¹ := by
            rw [standardSection_mul p]
    _ = (standardSection p (x * y) *
          kernelEmbed p
            (Multiplicative.ofAdd (PrimeCyclicH2.carry p x.toAdd y.toAdd))) *
        (kernelEmbed p (Multiplicative.ofAdd qxy) *
          kernelEmbed p
            (Multiplicative.ofAdd (PrimeCyclicH2.carry p x.toAdd y.toAdd)))⁻¹ := by
            rw [hK]
    _ = standardSection p (x * y) *
        (kernelEmbed p (Multiplicative.ofAdd qxy))⁻¹ := by
          rw [mul_inv_rev]
          simp [mul_assoc]

theorem liftedValue_mul
    (chi : G →ₜ* CyclicGroup p)
    (b : Cochain (coefficients p G) 1)
    (hb : differential (coefficients p G) 1 2 b =
      cycleCochain (coefficients p G) 2 3
        (pulledCarryCycle chi))
    (g h : G) :
    liftedValue chi b (g * h) = liftedValue chi b g * liftedValue chi b h := by
  rw [liftedValue, liftedValue, liftedValue, map_mul]
  apply liftAlgebra_identity
  have hboundary := boundary_primitive_equation chi b hb g h
  calc
    primitiveValue b g + primitiveValue b h =
        primitiveValue b (g * h) +
          (primitiveValue b h - primitiveValue b (g * h) +
            primitiveValue b g) := by abel
    _ = primitiveValue b (g * h) +
        PrimeCyclicH2.carry p (chi g).toAdd (chi h).toAdd := by rw [hboundary]

theorem continuous_primitiveValue (b : Cochain (coefficients p G) 1) :
    Continuous (primitiveValue b) := by
  exact (oneValue b.val 1).continuous

theorem continuous_liftedValue
    (chi : G →ₜ* CyclicGroup p)
    (b : Cochain (coefficients p G) 1) :
    Continuous (liftedValue chi b) := by
  unfold liftedValue
  have hsection : Continuous (fun g : G ↦ standardSection p (chi g)) :=
    (standardSection p).continuous.comp chi.continuous
  have hofAdd : Continuous (fun x : ZMod p ↦ Multiplicative.ofAdd x) :=
    continuous_of_discreteTopology
  have hkernel : Continuous
      (fun g : G ↦
    kernelEmbed p (Multiplicative.ofAdd (primitiveValue b g))) :=
    (kernelEmbed p).continuous.comp
      (hofAdd.comp (continuous_primitiveValue b))
  exact hsection.mul hkernel.inv

/-- The actual continuous `C_(p²)`-valued lift manufactured by a boundary
primitive. -/
def boundaryLift
    (chi : G →ₜ* CyclicGroup p)
    (b : Cochain (coefficients p G) 1)
    (hb : differential (coefficients p G) 1 2 b =
      cycleCochain (coefficients p G) 2 3
        (pulledCarryCycle chi)) :
    G →ₜ* CyclicGroupSquared p where
  toFun := liftedValue chi b
  map_one' := liftedValue_one chi b hb
  map_mul' := liftedValue_mul chi b hb
  continuous_toFun := continuous_liftedValue chi b

@[simp] theorem reduction_liftedValue
    (chi : G →ₜ* CyclicGroup p)
    (b : Cochain (coefficients p G) 1) (g : G) :
    reduction p (liftedValue chi b g) = chi g := by
  have hkernel :
      reduction p
        (kernelEmbed p (Multiplicative.ofAdd (primitiveValue b g))) = 1 :=
    reduction_kernelEmbedValue p _
  rw [liftedValue, map_mul, reduction_standardSection, map_inv,
    hkernel, inv_one, mul_one]

theorem reduction_comp_boundaryLift
    (chi : G →ₜ* CyclicGroup p)
    (b : Cochain (coefficients p G) 1)
    (hb : differential (coefficients p G) 1 2 b =
      cycleCochain (coefficients p G) 2 3
        (pulledCarryCycle chi)) :
    (reduction p).comp (boundaryLift chi b hb) = chi := by
  ext g
  exact reduction_liftedValue chi b g

/-- If the pulled explicit carry is a continuous boundary, the quotient
character lifts continuously through `C_(p²)`. -/
theorem exists_continuous_lift_of_pulledCarryCycle_boundary
    (chi : G →ₜ* CyclicGroup p)
    (hboundary : ∃ b : Cochain (coefficients p G) 1,
      differential (coefficients p G) 1 2 b =
        cycleCochain (coefficients p G) 2 3
          (pulledCarryCycle chi)) :
    ∃ psi : G →ₜ* CyclicGroupSquared p, (reduction p).comp psi = chi := by
  obtain ⟨b, hb⟩ := hboundary
  exact ⟨boundaryLift chi b hb, reduction_comp_boundaryLift chi b hb⟩

/-- Therefore any explicit obstruction to a continuous `C_(p²)`-lift proves
that the pulled carry cycle is not a boundary. -/
theorem pulledCarryCycle_not_boundary_of_noContinuousLift
    (chi : G →ₜ* CyclicGroup p)
    (hnolift : NoContinuousLift chi) :
    ¬ ∃ b : Cochain (coefficients p G) 1,
      differential (coefficients p G) 1 2 b =
        cycleCochain (coefficients p G) 2 3
          (pulledCarryCycle chi) := by
  intro hboundary
  exact hnolift
    (exists_continuous_lift_of_pulledCarryCycle_boundary chi hboundary)

/-- The actual continuous `H²(G, F_p)` class represented by the pulled
carry cycle. -/
def pulledCarryH2Class (chi : G →ₜ* CyclicGroup p) :
    (continuousCohomology (ZMod p) G 2).obj (coefficients p G) :=
  homologyLinearEquiv (coefficients p G) 2
    (h2Projection (coefficients p G) (pulledCarryCycle chi))

/-- Non-liftability through `C_(p²)` makes the actual pulled continuous `H²`
class nonzero. -/
theorem pulledCarryH2Class_ne_zero_of_noContinuousLift
    (chi : G →ₜ* CyclicGroup p)
    (hnolift : NoContinuousLift chi) :
    pulledCarryH2Class chi ≠ 0 := by
  intro hzero
  have hprojection :
      h2Projection (coefficients p G) (pulledCarryCycle chi) = 0 := by
    let e := homologyLinearEquiv (coefficients p G) 2
    change e (h2Projection (coefficients p G) (pulledCarryCycle chi)) = 0
      at hzero
    exact e.injective (hzero.trans e.map_zero.symm)
  exact pulledCarryCycle_not_boundary_of_noContinuousLift chi hnolift
    ((h2Projection_eq_zero_iff (coefficients p G)
      (pulledCarryCycle chi)).mp hprojection)

/-! ## Converse: a lift constructs a boundary primitive -/

/-- The kernel coordinate comparing a lift with the standard section. -/
def liftCorrection
    (chi : G →ₜ* CyclicGroup p)
    (psi : G →ₜ* CyclicGroupSquared p) (g : G) : ZMod p :=
  (kernelCoordinate p (standardSection p (chi g) * (psi g)⁻¹)).toAdd

omit [IsTopologicalGroup G] in
/-- The comparison between a section and a genuine lift lies in the kernel
of reduction. -/
theorem comparison_mem_kernel
    (chi : G →ₜ* CyclicGroup p)
    (psi : G →ₜ* CyclicGroupSquared p)
    (hlift : (reduction p).comp psi = chi) (g : G) :
    reduction p (standardSection p (chi g) * (psi g)⁻¹) = 1 := by
  have hpoint := DFunLike.congr_fun hlift g
  have hred : reduction p (psi g) = chi g := by
    change reduction p (psi g) = chi g at hpoint
    exact hpoint
  simp [hred]

omit [IsTopologicalGroup G] in
/-- Re-embedding the correction recovers the section/lift comparison. -/
theorem comparison_eq_kernelEmbed
    (chi : G →ₜ* CyclicGroup p)
    (psi : G →ₜ* CyclicGroupSquared p)
    (hlift : (reduction p).comp psi = chi) (g : G) :
    standardSection p (chi g) * (psi g)⁻¹ =
      kernelEmbed p (Multiplicative.ofAdd (liftCorrection chi psi g)) := by
  symm
  exact kernelEmbed_kernelCoordinate p _
    (comparison_mem_kernel chi psi hlift g)

omit [IsTopologicalGroup G] in
/-- Factor the standard section into the genuine lift and its correction. -/
theorem section_eq_lift_mul_kernel
    (chi : G →ₜ* CyclicGroup p)
    (psi : G →ₜ* CyclicGroupSquared p)
    (hlift : (reduction p).comp psi = chi) (g : G) :
    standardSection p (chi g) = psi g *
      kernelEmbed p (Multiplicative.ofAdd (liftCorrection chi psi g)) := by
  have h := comparison_eq_kernelEmbed chi psi hlift g
  calc
    standardSection p (chi g) =
        (standardSection p (chi g) * (psi g)⁻¹) * psi g := by simp
    _ = kernelEmbed p
        (Multiplicative.ofAdd (liftCorrection chi psi g)) * psi g := by rw [h]
    _ = psi g *
        kernelEmbed p (Multiplicative.ofAdd (liftCorrection chi psi g)) := by
      ac_rfl

omit [IsTopologicalGroup G] in
/-- The correction coordinate satisfies exactly the carry coboundary law. -/
theorem liftCorrection_add
    (chi : G →ₜ* CyclicGroup p)
    (psi : G →ₜ* CyclicGroupSquared p)
    (hlift : (reduction p).comp psi = chi) (g h : G) :
    liftCorrection chi psi g + liftCorrection chi psi h =
      liftCorrection chi psi (g * h) +
        PrimeCyclicH2.carry p (chi g).toAdd (chi h).toAdd := by
  have hg := section_eq_lift_mul_kernel chi psi hlift g
  have hh := section_eq_lift_mul_kernel chi psi hlift h
  have hgh := section_eq_lift_mul_kernel chi psi hlift (g * h)
  have hprod :
      psi (g * h) *
          (kernelEmbed p (Multiplicative.ofAdd (liftCorrection chi psi g)) *
            kernelEmbed p (Multiplicative.ofAdd (liftCorrection chi psi h))) =
        psi (g * h) *
          (kernelEmbed p
              (Multiplicative.ofAdd (liftCorrection chi psi (g * h))) *
            kernelEmbed p
              (Multiplicative.ofAdd
                (PrimeCyclicH2.carry p (chi g).toAdd (chi h).toAdd))) := by
    calc
      psi (g * h) *
          (kernelEmbed p (Multiplicative.ofAdd (liftCorrection chi psi g)) *
            kernelEmbed p (Multiplicative.ofAdd (liftCorrection chi psi h))) =
        (psi g *
            kernelEmbed p (Multiplicative.ofAdd (liftCorrection chi psi g))) *
          (psi h *
            kernelEmbed p (Multiplicative.ofAdd (liftCorrection chi psi h))) := by
              rw [map_mul]
              ac_rfl
      _ = standardSection p (chi g) * standardSection p (chi h) := by
            rw [← hg, ← hh]
      _ = standardSection p (chi g * chi h) *
          kernelEmbed p
            (Multiplicative.ofAdd
              (PrimeCyclicH2.carry p (chi g).toAdd (chi h).toAdd)) := by
            rw [standardSection_mul p]
      _ = standardSection p (chi (g * h)) *
          kernelEmbed p
            (Multiplicative.ofAdd
              (PrimeCyclicH2.carry p (chi g).toAdd (chi h).toAdd)) := by
            congr 1
            exact congrArg (standardSection p) (chi.map_mul g h).symm
      _ = (psi (g * h) *
          kernelEmbed p
            (Multiplicative.ofAdd (liftCorrection chi psi (g * h)))) *
          kernelEmbed p
            (Multiplicative.ofAdd
              (PrimeCyclicH2.carry p (chi g).toAdd (chi h).toAdd)) := by rw [hgh]
      _ = psi (g * h) *
          (kernelEmbed p
              (Multiplicative.ofAdd (liftCorrection chi psi (g * h))) *
            kernelEmbed p
              (Multiplicative.ofAdd
                (PrimeCyclicH2.carry p (chi g).toAdd (chi h).toAdd))) := by ac_rfl
  have hkernel := mul_left_cancel hprod
  have hcoordinate :
      Multiplicative.ofAdd (liftCorrection chi psi g) *
          Multiplicative.ofAdd (liftCorrection chi psi h) =
        Multiplicative.ofAdd (liftCorrection chi psi (g * h)) *
          Multiplicative.ofAdd
            (PrimeCyclicH2.carry p (chi g).toAdd (chi h).toAdd) := by
    apply kernelEmbed_injective p
    simpa only [map_mul] using hkernel
  exact congrArg Multiplicative.toAdd hcoordinate

omit [IsTopologicalGroup G] in
/-- The lift correction is continuous. -/
theorem continuous_liftCorrection
    (chi : G →ₜ* CyclicGroup p)
    (psi : G →ₜ* CyclicGroupSquared p) :
    Continuous (liftCorrection chi psi) := by
  letI : ContinuousMul (CyclicGroupSquared p) :=
    ⟨continuous_of_discreteTopology⟩
  have hsection : Continuous (fun g : G ↦ standardSection p (chi g)) := by
    exact (continuous_of_discreteTopology :
      Continuous (fun x : CyclicGroup p ↦ standardSection p x)).comp
        chi.continuous
  have hcomparison : Continuous
      (fun g : G ↦ standardSection p (chi g) * (psi g)⁻¹) :=
    hsection.mul psi.continuous.inv
  have hcoordinate : Continuous
      (fun z : CyclicGroupSquared p ↦ (kernelCoordinate p z).toAdd) :=
    continuous_of_discreteTopology
  exact hcoordinate.comp hcomparison

/-- The invariant homogeneous one-cochain obtained from the correction
coordinate of a supplied lift. -/
def liftPrimitiveRaw
    (chi : G →ₜ* CyclicGroup p)
    (psi : G →ₜ* CyclicGroupSquared p) : C(G, C(G, ZMod p)) where
  toFun x :=
    ⟨fun y ↦ liftCorrection chi psi (x⁻¹ * y),
      (continuous_liftCorrection chi psi).comp
        (continuous_const.mul continuous_id)⟩
  continuous_toFun := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (continuous_liftCorrection chi psi).comp
      (continuous_fst.inv.mul continuous_snd)

@[simp] theorem liftPrimitiveRaw_apply
    (chi : G →ₜ* CyclicGroup p)
    (psi : G →ₜ* CyclicGroupSquared p) (x y : G) :
    liftPrimitiveRaw chi psi x y = liftCorrection chi psi (x⁻¹ * y) :=
  rfl

/-- The correction cochain bundled in Mathlib's continuous homogeneous
degree-one complex. -/
def liftPrimitive
    (chi : G →ₜ* CyclicGroup p)
    (psi : G →ₜ* CyclicGroupSquared p) :
    Cochain (coefficients p G) 1 := by
  refine ⟨⟨liftPrimitiveRaw chi psi, ?_⟩⟩
  intro a
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  change liftCorrection chi psi ((a⁻¹ * x)⁻¹ * (a⁻¹ * y)) =
    liftCorrection chi psi (x⁻¹ * y)
  congr 1
  group

@[simp] theorem liftPrimitive_oneValue
    (chi : G →ₜ* CyclicGroup p)
    (psi : G →ₜ* CyclicGroupSquared p) (x y : G) :
    oneValue (liftPrimitive chi psi).val x y =
      liftCorrection chi psi (x⁻¹ * y) :=
  rfl

/-- A supplied continuous lift gives an explicit primitive of the pulled
carry cycle. -/
theorem differential_liftPrimitive
    (chi : G →ₜ* CyclicGroup p)
    (psi : G →ₜ* CyclicGroupSquared p)
    (hlift : (reduction p).comp psi = chi) :
    differential (coefficients p G) 1 2 (liftPrimitive chi psi) =
      cycleCochain (coefficients p G) 2 3 (pulledCarryCycle chi) := by
  apply Cochain.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro w
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  change
    liftCorrection chi psi (x⁻¹ * y) -
        (liftCorrection chi psi (w⁻¹ * y) -
          liftCorrection chi psi (w⁻¹ * x)) =
      PrimeCyclicH2.carry p ((chi w)⁻¹ * chi x).toAdd ((chi x)⁻¹ * chi y).toAdd
  have hc := liftCorrection_add chi psi hlift (w⁻¹ * x) (x⁻¹ * y)
  have hprod : (w⁻¹ * x) * (x⁻¹ * y) = w⁻¹ * y := by group
  have hchiwx : chi (w⁻¹ * x) = (chi w)⁻¹ * chi x := by simp
  have hchixy : chi (x⁻¹ * y) = (chi x)⁻¹ * chi y := by simp
  rw [hprod, hchiwx, hchixy] at hc
  calc
    liftCorrection chi psi (x⁻¹ * y) -
        (liftCorrection chi psi (w⁻¹ * y) -
          liftCorrection chi psi (w⁻¹ * x)) =
      liftCorrection chi psi (w⁻¹ * x) +
          liftCorrection chi psi (x⁻¹ * y) -
        liftCorrection chi psi (w⁻¹ * y) := by abel
    _ = PrimeCyclicH2.carry p ((chi w)⁻¹ * chi x).toAdd
        ((chi x)⁻¹ * chi y).toAdd := by
      rw [hc]
      abel

/-- Any supplied continuous lift gives a continuous boundary primitive for
the pulled carry cycle. -/
theorem pulledCarryCycle_boundary_of_exists_continuous_lift
    (chi : G →ₜ* CyclicGroup p)
    (hlift : ∃ psi : G →ₜ* CyclicGroupSquared p,
      (reduction p).comp psi = chi) :
    ∃ b : Cochain (coefficients p G) 1,
      differential (coefficients p G) 1 2 b =
        cycleCochain (coefficients p G) 2 3
          (pulledCarryCycle chi) := by
  obtain ⟨psi, hpsi⟩ := hlift
  exact ⟨liftPrimitive chi psi,
    differential_liftPrimitive chi psi hpsi⟩

/-- The pulled carry cycle is a boundary exactly when the quotient
character lifts continuously through `C_(p²)`. -/
theorem pulledCarryCycle_boundary_iff_exists_continuous_lift
    (chi : G →ₜ* CyclicGroup p) :
    (∃ b : Cochain (coefficients p G) 1,
      differential (coefficients p G) 1 2 b =
        cycleCochain (coefficients p G) 2 3
          (pulledCarryCycle chi)) ↔
      ∃ psi : G →ₜ* CyclicGroupSquared p,
        (reduction p).comp psi = chi := by
  constructor
  · exact exists_continuous_lift_of_pulledCarryCycle_boundary chi
  · exact pulledCarryCycle_boundary_of_exists_continuous_lift chi

/-- Equivalently, the pulled carry cycle is not a boundary exactly when
the character has no continuous `C_(p²)`-valued lift. -/
theorem pulledCarryCycle_not_boundary_iff_noContinuousLift
    (chi : G →ₜ* CyclicGroup p) :
    (¬ ∃ b : Cochain (coefficients p G) 1,
      differential (coefficients p G) 1 2 b =
        cycleCochain (coefficients p G) 2 3
          (pulledCarryCycle chi)) ↔ NoContinuousLift chi := by
  exact not_congr (pulledCarryCycle_boundary_iff_exists_continuous_lift chi)



/-! ## Actual continuous H² criterion -/

/-- The actual pulled continuous carry class vanishes exactly when its
character admits a continuous lift from `C_p` to `C_(p²)`. -/
theorem pulledCarryH2Class_eq_zero_iff_exists_continuous_lift
    (chi : G →ₜ* CyclicGroup p) :
    pulledCarryH2Class chi = 0 ↔
      ∃ psi : G →ₜ* CyclicGroupSquared p,
        (reduction p).comp psi = chi := by
  rw [← pulledCarryCycle_boundary_iff_exists_continuous_lift chi]
  constructor
  · intro hzero
    have hprojection :
        h2Projection (coefficients p G) (pulledCarryCycle chi) = 0 := by
      let e := homologyLinearEquiv (coefficients p G) 2
      change e (h2Projection (coefficients p G) (pulledCarryCycle chi)) = 0
        at hzero
      exact e.injective (hzero.trans e.map_zero.symm)
    exact (h2Projection_eq_zero_iff (coefficients p G)
      (pulledCarryCycle chi)).mp hprojection
  · intro hboundary
    unfold pulledCarryH2Class
    rw [(h2Projection_eq_zero_iff (coefficients p G)
      (pulledCarryCycle chi)).mpr hboundary]
    exact map_zero _

/-- Negating the vanishing criterion identifies nonzero carry classes with
the genuine obstruction to a continuous `C_(p²)` lift. -/
theorem pulledCarryH2Class_ne_zero_iff_noContinuousLift
    (chi : G →ₜ* CyclicGroup p) :
    pulledCarryH2Class chi ≠ 0 ↔ NoContinuousLift chi := by
  simpa [NoContinuousLift] using
    not_congr (pulledCarryH2Class_eq_zero_iff_exists_continuous_lift chi)

end Fermat.Conservation.PrimeContinuousCarryLift
