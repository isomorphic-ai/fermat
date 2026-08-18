/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The C₅₉² lift obstruction for the explicit continuous carry class

The standard carry cocycle is the extension class of the reduction map
`C₅₉² → C₅₉`.  This file proves that statement directly at the cochain
level.  If the pullback of the carry cycle along a continuous character
`χ : G → C₅₉` is a continuous boundary, its boundary primitive corrects the
standard-representative section into a continuous homomorphism
`ψ : G → C₅₉²` reducing to `χ`.

Consequently, an explicit assertion that `χ` has no continuous C₅₉² lift
proves that the pulled carry cycle is not a boundary.  The file makes no
arithmetic claim that a particular Galois character satisfies this
non-liftability condition.
-/
import Fermat.Conservation.CyclicCarryH2Class59
import Fermat.Conservation.ContinuousHomogeneousPullback59

noncomputable section

open CategoryTheory
open ContinuousCohomology
open Fermat.Conservation.ContinuousKummerTateCupRaw
open Fermat.Conservation.ContinuousKummerTateCup.Nominal

namespace Fermat.Conservation.ContinuousCarryLiftObstruction59

open Fermat.Conservation.CyclicCarryH2Class59
open Fermat.Conservation.ContinuousHomogeneousPullback59
open Fermat.Conservation.FiniteCyclicH2Generator59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

/-- The additive cyclic group of order `59²`, written multiplicatively. -/
abbrev CyclicGroup59Squared := Multiplicative (ZMod (59 ^ 2))

/-- Reduction from the additive cyclic group of order `59²` to the one of
order `59`. -/
def reduction59 : CyclicGroup59Squared →ₜ* CyclicGroup59 where
  toFun x := Multiplicative.ofAdd
    (ZMod.castHom (by norm_num : 59 ∣ 59 ^ 2) (ZMod 59) x.toAdd)
  map_one' := by simp
  map_mul' x y := by
    change Multiplicative.ofAdd
        (ZMod.castHom (by norm_num : 59 ∣ 59 ^ 2) (ZMod 59)
          (x.toAdd + y.toAdd)) = _
    simp
  continuous_toFun := continuous_of_discreteTopology

/-- The standard representative section.  It is continuous but deliberately
not a homomorphism. -/
def standardSection59 : C(CyclicGroup59, CyclicGroup59Squared) where
  toFun x := Multiplicative.ofAdd (x.toAdd.val : ZMod (59 ^ 2))
  continuous_toFun := continuous_of_discreteTopology

set_option maxRecDepth 100000 in
/-- Multiplication by `59` identifies the kernel of reduction with C₅₉. -/
def kernelEmbed59 : CyclicGroup59 →ₜ* CyclicGroup59Squared where
  toFun x := Multiplicative.ofAdd ((59 * x.toAdd.val : ℕ) : ZMod (59 ^ 2))
  map_one' := by decide
  map_mul' := by decide +revert
  continuous_toFun := continuous_of_discreteTopology

@[simp] theorem reduction59_standardSection59 (x : CyclicGroup59) :
    reduction59 (standardSection59 x) = x := by decide +revert

@[simp] theorem reduction59_kernelEmbed59 (x : CyclicGroup59) :
    reduction59 (kernelEmbed59 x) = 1 := by decide +revert

set_option maxRecDepth 100000 in
/-- The failure of the standard section to be multiplicative is precisely
the explicit carry cocycle. -/
theorem standardSection59_mul (x y : CyclicGroup59) :
    standardSection59 x * standardSection59 y =
      standardSection59 (x * y) *
        kernelEmbed59 (Multiplicative.ofAdd (carry59 x.toAdd y.toAdd)) := by
  decide +revert

@[simp] theorem standardSection59_one : standardSection59 1 = 1 := by
  rfl

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Pull the explicit continuous carry cycle back along `chi`. -/
def pulledCarryCycle59 (chi : G →ₜ* CyclicGroup59) :
    Cycle (coefficients G) 2 3 :=
  pullbackCycleTwo chi continuousCarryCycle59

/-- The assertion that a continuous character has no continuous lift through
reduction from C₅₉². -/
abbrev NoContinuousLift (chi : G →ₜ* CyclicGroup59) : Prop :=
  ¬ ∃ psi : G →ₜ* CyclicGroup59Squared, reduction59.comp psi = chi

/-- Evaluate a homogeneous boundary primitive at `(1,g)`. -/
def primitiveValue
    (b : Cochain (coefficients G) 1) (g : G) : ZMod 59 :=
  oneValue b.val 1 g

/-- Correct the standard section by the negative of the supplied primitive. -/
def liftedValue
    (chi : G →ₜ* CyclicGroup59)
    (b : Cochain (coefficients G) 1) (g : G) : CyclicGroup59Squared :=
  standardSection59 (chi g) *
    (kernelEmbed59 (Multiplicative.ofAdd (primitiveValue b g)))⁻¹

@[simp] theorem coefficientsOneDifferential_apply
    (b : Cochain (coefficients G) 1) (w x y : G) :
    twoValue
      ((((homogeneousCochains (ZMod 59) G).obj
        (coefficients G)).d 1 2).hom b.val) w x y =
      oneValue b.val x y - (oneValue b.val w y - oneValue b.val w x) :=
  rfl

@[simp] theorem pulledCarryCycle59_apply
    (chi : G →ₜ* CyclicGroup59) (w x y : G) :
    twoValue (pulledCarryCycle59 chi).cochain.val w x y =
      carry59 ((chi w)⁻¹ * chi x).toAdd ((chi x)⁻¹ * chi y).toAdd := by
  rfl

/-- The boundary equation, written as the inhomogeneous correction law
needed by the lift. -/
theorem boundary_primitive_equation
    (chi : G →ₜ* CyclicGroup59)
    (b : Cochain (coefficients G) 1)
    (hb : differential (coefficients G) 1 2 b =
      cycleCochain (coefficients G) 2 3
        (pulledCarryCycle59 chi))
    (g h : G) :
    primitiveValue b h - primitiveValue b (g * h) + primitiveValue b g =
      carry59 (chi g).toAdd (chi h).toAdd := by
  have hpoint := congrArg
    (fun q : Cochain (coefficients G) 2 ↦ twoValue q.val 1 g (g * h)) hb
  rw [differential_val, cycleCochain_val] at hpoint
  rw [coefficientsOneDifferential_apply, pulledCarryCycle59_apply] at hpoint
  simp only [map_one, inv_one, one_mul, map_mul, inv_mul_cancel_left] at hpoint
  change
    (show ZMod 59 from oneValue b.val g (g * h)) -
        ((show ZMod 59 from oneValue b.val 1 (g * h)) -
          (show ZMod 59 from oneValue b.val 1 g)) =
      carry59 (chi g).toAdd (chi h).toAdd at hpoint
  have hinv := oneValue_invariant b.val g g (g * h)
  have hinv' : oneValue b.val 1 h = oneValue b.val g (g * h) := by
    simpa using hinv
  rw [primitiveValue, primitiveValue, primitiveValue, hinv']
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hpoint

theorem primitiveValue_one
    (chi : G →ₜ* CyclicGroup59)
    (b : Cochain (coefficients G) 1)
    (hb : differential (coefficients G) 1 2 b =
      cycleCochain (coefficients G) 2 3
        (pulledCarryCycle59 chi)) :
    primitiveValue b 1 = 0 := by
  have h := boundary_primitive_equation chi b hb 1 1
  simpa [carry59] using h

theorem liftedValue_one
    (chi : G →ₜ* CyclicGroup59)
    (b : Cochain (coefficients G) 1)
    (hb : differential (coefficients G) 1 2 b =
      cycleCochain (coefficients G) 2 3
        (pulledCarryCycle59 chi)) :
    liftedValue chi b 1 = 1 := by
  simp [liftedValue, primitiveValue_one chi b hb]

/-- The finite cyclic algebra identity converting the primitive equation
into the multiplication law for the corrected section. -/
theorem liftAlgebra_identity
    (x y : CyclicGroup59) (qx qy qxy : ZMod 59)
    (hq : qx + qy = qxy + carry59 x.toAdd y.toAdd) :
    standardSection59 (x * y) *
        (kernelEmbed59 (Multiplicative.ofAdd qxy))⁻¹ =
      (standardSection59 x *
          (kernelEmbed59 (Multiplicative.ofAdd qx))⁻¹) *
        (standardSection59 y *
          (kernelEmbed59 (Multiplicative.ofAdd qy))⁻¹) := by
  have hqmul :
      Multiplicative.ofAdd qx * Multiplicative.ofAdd qy =
        Multiplicative.ofAdd qxy *
          Multiplicative.ofAdd (carry59 x.toAdd y.toAdd) := by
    exact congrArg Multiplicative.ofAdd hq
  have hK := congrArg kernelEmbed59 hqmul
  simp only [map_mul] at hK
  symm
  calc
    (standardSection59 x *
          (kernelEmbed59 (Multiplicative.ofAdd qx))⁻¹) *
        (standardSection59 y *
          (kernelEmbed59 (Multiplicative.ofAdd qy))⁻¹) =
      (standardSection59 x * standardSection59 y) *
        (kernelEmbed59 (Multiplicative.ofAdd qx) *
          kernelEmbed59 (Multiplicative.ofAdd qy))⁻¹ := by
            rw [mul_inv_rev]
            ac_rfl
    _ = (standardSection59 (x * y) *
          kernelEmbed59
            (Multiplicative.ofAdd (carry59 x.toAdd y.toAdd))) *
        (kernelEmbed59 (Multiplicative.ofAdd qx) *
          kernelEmbed59 (Multiplicative.ofAdd qy))⁻¹ := by
            rw [standardSection59_mul]
    _ = (standardSection59 (x * y) *
          kernelEmbed59
            (Multiplicative.ofAdd (carry59 x.toAdd y.toAdd))) *
        (kernelEmbed59 (Multiplicative.ofAdd qxy) *
          kernelEmbed59
            (Multiplicative.ofAdd (carry59 x.toAdd y.toAdd)))⁻¹ := by
            rw [hK]
    _ = standardSection59 (x * y) *
        (kernelEmbed59 (Multiplicative.ofAdd qxy))⁻¹ := by
          rw [mul_inv_rev]
          simp [mul_assoc]

theorem liftedValue_mul
    (chi : G →ₜ* CyclicGroup59)
    (b : Cochain (coefficients G) 1)
    (hb : differential (coefficients G) 1 2 b =
      cycleCochain (coefficients G) 2 3
        (pulledCarryCycle59 chi))
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
        carry59 (chi g).toAdd (chi h).toAdd := by rw [hboundary]

theorem continuous_primitiveValue (b : Cochain (coefficients G) 1) :
    Continuous (primitiveValue b) := by
  exact (oneValue b.val 1).continuous

theorem continuous_liftedValue
    (chi : G →ₜ* CyclicGroup59)
    (b : Cochain (coefficients G) 1) :
    Continuous (liftedValue chi b) := by
  unfold liftedValue
  have hsection : Continuous (fun g : G ↦ standardSection59 (chi g)) :=
    standardSection59.continuous.comp chi.continuous
  have hofAdd : Continuous (fun x : ZMod 59 ↦ Multiplicative.ofAdd x) :=
    continuous_of_discreteTopology
  have hkernel : Continuous
      (fun g : G ↦
        kernelEmbed59 (Multiplicative.ofAdd (primitiveValue b g))) :=
    kernelEmbed59.continuous.comp
      (hofAdd.comp (continuous_primitiveValue b))
  exact hsection.mul hkernel.inv

/-- The actual continuous C₅₉²-valued lift manufactured by a boundary
primitive. -/
def boundaryLift59
    (chi : G →ₜ* CyclicGroup59)
    (b : Cochain (coefficients G) 1)
    (hb : differential (coefficients G) 1 2 b =
      cycleCochain (coefficients G) 2 3
        (pulledCarryCycle59 chi)) :
    G →ₜ* CyclicGroup59Squared where
  toFun := liftedValue chi b
  map_one' := liftedValue_one chi b hb
  map_mul' := liftedValue_mul chi b hb
  continuous_toFun := continuous_liftedValue chi b

@[simp] theorem reduction59_liftedValue
    (chi : G →ₜ* CyclicGroup59)
    (b : Cochain (coefficients G) 1) (g : G) :
    reduction59 (liftedValue chi b g) = chi g := by
  simp [liftedValue]

theorem reduction59_comp_boundaryLift59
    (chi : G →ₜ* CyclicGroup59)
    (b : Cochain (coefficients G) 1)
    (hb : differential (coefficients G) 1 2 b =
      cycleCochain (coefficients G) 2 3
        (pulledCarryCycle59 chi)) :
    reduction59.comp (boundaryLift59 chi b hb) = chi := by
  ext g
  exact reduction59_liftedValue chi b g

/-- If the pulled explicit carry is a continuous boundary, the quotient
character lifts continuously through C₅₉². -/
theorem exists_continuous_lift_of_pulledCarryCycle59_boundary
    (chi : G →ₜ* CyclicGroup59)
    (hboundary : ∃ b : Cochain (coefficients G) 1,
      differential (coefficients G) 1 2 b =
        cycleCochain (coefficients G) 2 3
          (pulledCarryCycle59 chi)) :
    ∃ psi : G →ₜ* CyclicGroup59Squared, reduction59.comp psi = chi := by
  obtain ⟨b, hb⟩ := hboundary
  exact ⟨boundaryLift59 chi b hb, reduction59_comp_boundaryLift59 chi b hb⟩

/-- Therefore any explicit obstruction to a continuous C₅₉²-lift proves
that the pulled carry cycle is not a boundary. -/
theorem pulledCarryCycle59_not_boundary_of_noContinuousLift
    (chi : G →ₜ* CyclicGroup59)
    (hnolift : NoContinuousLift chi) :
    ¬ ∃ b : Cochain (coefficients G) 1,
      differential (coefficients G) 1 2 b =
        cycleCochain (coefficients G) 2 3
          (pulledCarryCycle59 chi) := by
  intro hboundary
  exact hnolift
    (exists_continuous_lift_of_pulledCarryCycle59_boundary chi hboundary)

/-- The actual continuous `H²(G, F₅₉)` class represented by the pulled
carry cycle. -/
def pulledCarryH2Class59 (chi : G →ₜ* CyclicGroup59) :
    (continuousCohomology (ZMod 59) G 2).obj (coefficients G) :=
  homologyLinearEquiv (coefficients G) 2
    (h2Projection (coefficients G) (pulledCarryCycle59 chi))

/-- Non-liftability through C₅₉² makes the actual pulled continuous `H²`
class nonzero. -/
theorem pulledCarryH2Class59_ne_zero_of_noContinuousLift
    (chi : G →ₜ* CyclicGroup59)
    (hnolift : NoContinuousLift chi) :
    pulledCarryH2Class59 chi ≠ 0 := by
  intro hzero
  have hprojection :
      h2Projection (coefficients G) (pulledCarryCycle59 chi) = 0 := by
    let e := homologyLinearEquiv (coefficients G) 2
    change e (h2Projection (coefficients G) (pulledCarryCycle59 chi)) = 0
      at hzero
    exact e.injective (hzero.trans e.map_zero.symm)
  exact pulledCarryCycle59_not_boundary_of_noContinuousLift chi hnolift
    ((h2Projection_eq_zero_iff (coefficients G)
      (pulledCarryCycle59 chi)).mp hprojection)

/-! ## Converse: a lift constructs a boundary primitive -/

/-- Divide a kernel element by `59`, using standard representatives. -/
def kernelCoordinate59 (z : CyclicGroup59Squared) : CyclicGroup59 :=
  Multiplicative.ofAdd ((z.toAdd.val / 59 : ℕ) : ZMod 59)

set_option maxRecDepth 100000 in
/-- The kernel coordinate is a right inverse to the kernel embedding on
elements killed by reduction. -/
theorem kernelEmbed59_kernelCoordinate59
    (z : CyclicGroup59Squared) (hz : reduction59 z = 1) :
    kernelEmbed59 (kernelCoordinate59 z) = z := by
  decide +revert

/-- Multiplication by `59` is injective from C₅₉ into C₅₉². -/
theorem kernelEmbed59_injective : Function.Injective kernelEmbed59 := by
  have hleft : Function.LeftInverse kernelCoordinate59 kernelEmbed59 := by
    intro x
    decide +revert
  exact hleft.injective

/-- The kernel coordinate comparing a lift with the standard section. -/
def liftCorrection59
    (chi : G →ₜ* CyclicGroup59)
    (psi : G →ₜ* CyclicGroup59Squared) (g : G) : ZMod 59 :=
  (kernelCoordinate59 (standardSection59 (chi g) * (psi g)⁻¹)).toAdd

omit [IsTopologicalGroup G] in
/-- The comparison between a section and a genuine lift lies in the kernel
of reduction. -/
theorem comparison_mem_kernel59
    (chi : G →ₜ* CyclicGroup59)
    (psi : G →ₜ* CyclicGroup59Squared)
    (hlift : reduction59.comp psi = chi) (g : G) :
    reduction59 (standardSection59 (chi g) * (psi g)⁻¹) = 1 := by
  have hpoint := DFunLike.congr_fun hlift g
  have hred : reduction59 (psi g) = chi g := by
    change reduction59 (psi g) = chi g at hpoint
    exact hpoint
  simp [hred]

omit [IsTopologicalGroup G] in
/-- Re-embedding the correction recovers the section/lift comparison. -/
theorem comparison_eq_kernelEmbed59
    (chi : G →ₜ* CyclicGroup59)
    (psi : G →ₜ* CyclicGroup59Squared)
    (hlift : reduction59.comp psi = chi) (g : G) :
    standardSection59 (chi g) * (psi g)⁻¹ =
      kernelEmbed59 (Multiplicative.ofAdd (liftCorrection59 chi psi g)) := by
  symm
  exact kernelEmbed59_kernelCoordinate59 _
    (comparison_mem_kernel59 chi psi hlift g)

omit [IsTopologicalGroup G] in
/-- Factor the standard section into the genuine lift and its correction. -/
theorem section_eq_lift_mul_kernel59
    (chi : G →ₜ* CyclicGroup59)
    (psi : G →ₜ* CyclicGroup59Squared)
    (hlift : reduction59.comp psi = chi) (g : G) :
    standardSection59 (chi g) = psi g *
      kernelEmbed59 (Multiplicative.ofAdd (liftCorrection59 chi psi g)) := by
  have h := comparison_eq_kernelEmbed59 chi psi hlift g
  calc
    standardSection59 (chi g) =
        (standardSection59 (chi g) * (psi g)⁻¹) * psi g := by simp
    _ = kernelEmbed59
        (Multiplicative.ofAdd (liftCorrection59 chi psi g)) * psi g := by rw [h]
    _ = psi g *
        kernelEmbed59 (Multiplicative.ofAdd (liftCorrection59 chi psi g)) := by
      ac_rfl

omit [IsTopologicalGroup G] in
/-- The correction coordinate satisfies exactly the carry coboundary law. -/
theorem liftCorrection59_add
    (chi : G →ₜ* CyclicGroup59)
    (psi : G →ₜ* CyclicGroup59Squared)
    (hlift : reduction59.comp psi = chi) (g h : G) :
    liftCorrection59 chi psi g + liftCorrection59 chi psi h =
      liftCorrection59 chi psi (g * h) +
        carry59 (chi g).toAdd (chi h).toAdd := by
  have hg := section_eq_lift_mul_kernel59 chi psi hlift g
  have hh := section_eq_lift_mul_kernel59 chi psi hlift h
  have hgh := section_eq_lift_mul_kernel59 chi psi hlift (g * h)
  have hprod :
      psi (g * h) *
          (kernelEmbed59 (Multiplicative.ofAdd (liftCorrection59 chi psi g)) *
            kernelEmbed59 (Multiplicative.ofAdd (liftCorrection59 chi psi h))) =
        psi (g * h) *
          (kernelEmbed59
              (Multiplicative.ofAdd (liftCorrection59 chi psi (g * h))) *
            kernelEmbed59
              (Multiplicative.ofAdd
                (carry59 (chi g).toAdd (chi h).toAdd))) := by
    calc
      psi (g * h) *
          (kernelEmbed59 (Multiplicative.ofAdd (liftCorrection59 chi psi g)) *
            kernelEmbed59 (Multiplicative.ofAdd (liftCorrection59 chi psi h))) =
        (psi g *
            kernelEmbed59 (Multiplicative.ofAdd (liftCorrection59 chi psi g))) *
          (psi h *
            kernelEmbed59 (Multiplicative.ofAdd (liftCorrection59 chi psi h))) := by
              rw [map_mul]
              ac_rfl
      _ = standardSection59 (chi g) * standardSection59 (chi h) := by
            rw [← hg, ← hh]
      _ = standardSection59 (chi g * chi h) *
          kernelEmbed59
            (Multiplicative.ofAdd
              (carry59 (chi g).toAdd (chi h).toAdd)) := by
            rw [standardSection59_mul]
      _ = standardSection59 (chi (g * h)) *
          kernelEmbed59
            (Multiplicative.ofAdd
              (carry59 (chi g).toAdd (chi h).toAdd)) := by
            congr 1
            exact congrArg standardSection59 (chi.map_mul g h).symm
      _ = (psi (g * h) *
          kernelEmbed59
            (Multiplicative.ofAdd (liftCorrection59 chi psi (g * h)))) *
          kernelEmbed59
            (Multiplicative.ofAdd
              (carry59 (chi g).toAdd (chi h).toAdd)) := by rw [hgh]
      _ = psi (g * h) *
          (kernelEmbed59
              (Multiplicative.ofAdd (liftCorrection59 chi psi (g * h))) *
            kernelEmbed59
              (Multiplicative.ofAdd
                (carry59 (chi g).toAdd (chi h).toAdd))) := by ac_rfl
  have hkernel := mul_left_cancel hprod
  have hcoordinate :
      Multiplicative.ofAdd (liftCorrection59 chi psi g) *
          Multiplicative.ofAdd (liftCorrection59 chi psi h) =
        Multiplicative.ofAdd (liftCorrection59 chi psi (g * h)) *
          Multiplicative.ofAdd
            (carry59 (chi g).toAdd (chi h).toAdd) := by
    apply kernelEmbed59_injective
    simpa only [map_mul] using hkernel
  exact congrArg Multiplicative.toAdd hcoordinate

omit [IsTopologicalGroup G] in
/-- The lift correction is continuous. -/
theorem continuous_liftCorrection59
    (chi : G →ₜ* CyclicGroup59)
    (psi : G →ₜ* CyclicGroup59Squared) :
    Continuous (liftCorrection59 chi psi) := by
  have hcomparison : Continuous
      (fun g : G ↦ standardSection59 (chi g) * (psi g)⁻¹) :=
    (standardSection59.continuous.comp chi.continuous).mul psi.continuous.inv
  have hcoordinate : Continuous
      (fun z : CyclicGroup59Squared ↦ (kernelCoordinate59 z).toAdd) :=
    continuous_of_discreteTopology
  exact hcoordinate.comp hcomparison

/-- The invariant homogeneous one-cochain obtained from the correction
coordinate of a supplied lift. -/
def liftPrimitiveRaw59
    (chi : G →ₜ* CyclicGroup59)
    (psi : G →ₜ* CyclicGroup59Squared) : C(G, C(G, ZMod 59)) where
  toFun x :=
    ⟨fun y ↦ liftCorrection59 chi psi (x⁻¹ * y),
      (continuous_liftCorrection59 chi psi).comp
        (continuous_const.mul continuous_id)⟩
  continuous_toFun := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (continuous_liftCorrection59 chi psi).comp
      (continuous_fst.inv.mul continuous_snd)

@[simp] theorem liftPrimitiveRaw59_apply
    (chi : G →ₜ* CyclicGroup59)
    (psi : G →ₜ* CyclicGroup59Squared) (x y : G) :
    liftPrimitiveRaw59 chi psi x y = liftCorrection59 chi psi (x⁻¹ * y) :=
  rfl

/-- The correction cochain bundled in Mathlib's continuous homogeneous
degree-one complex. -/
def liftPrimitive59
    (chi : G →ₜ* CyclicGroup59)
    (psi : G →ₜ* CyclicGroup59Squared) :
    Cochain (coefficients G) 1 := by
  refine ⟨⟨liftPrimitiveRaw59 chi psi, ?_⟩⟩
  intro a
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  change liftCorrection59 chi psi ((a⁻¹ * x)⁻¹ * (a⁻¹ * y)) =
    liftCorrection59 chi psi (x⁻¹ * y)
  congr 1
  group

@[simp] theorem liftPrimitive59_oneValue
    (chi : G →ₜ* CyclicGroup59)
    (psi : G →ₜ* CyclicGroup59Squared) (x y : G) :
    oneValue (liftPrimitive59 chi psi).val x y =
      liftCorrection59 chi psi (x⁻¹ * y) :=
  rfl

/-- A supplied continuous lift gives an explicit primitive of the pulled
carry cycle. -/
theorem differential_liftPrimitive59
    (chi : G →ₜ* CyclicGroup59)
    (psi : G →ₜ* CyclicGroup59Squared)
    (hlift : reduction59.comp psi = chi) :
    differential (coefficients G) 1 2 (liftPrimitive59 chi psi) =
      cycleCochain (coefficients G) 2 3 (pulledCarryCycle59 chi) := by
  apply Cochain.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro w
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  change
    liftCorrection59 chi psi (x⁻¹ * y) -
        (liftCorrection59 chi psi (w⁻¹ * y) -
          liftCorrection59 chi psi (w⁻¹ * x)) =
      carry59 ((chi w)⁻¹ * chi x).toAdd ((chi x)⁻¹ * chi y).toAdd
  have hc := liftCorrection59_add chi psi hlift (w⁻¹ * x) (x⁻¹ * y)
  have hprod : (w⁻¹ * x) * (x⁻¹ * y) = w⁻¹ * y := by group
  have hchiwx : chi (w⁻¹ * x) = (chi w)⁻¹ * chi x := by simp
  have hchixy : chi (x⁻¹ * y) = (chi x)⁻¹ * chi y := by simp
  rw [hprod, hchiwx, hchixy] at hc
  calc
    liftCorrection59 chi psi (x⁻¹ * y) -
        (liftCorrection59 chi psi (w⁻¹ * y) -
          liftCorrection59 chi psi (w⁻¹ * x)) =
      liftCorrection59 chi psi (w⁻¹ * x) +
          liftCorrection59 chi psi (x⁻¹ * y) -
        liftCorrection59 chi psi (w⁻¹ * y) := by abel
    _ = carry59 ((chi w)⁻¹ * chi x).toAdd
        ((chi x)⁻¹ * chi y).toAdd := by
      rw [hc]
      abel

/-- Any supplied continuous lift gives a continuous boundary primitive for
the pulled carry cycle. -/
theorem pulledCarryCycle59_boundary_of_exists_continuous_lift
    (chi : G →ₜ* CyclicGroup59)
    (hlift : ∃ psi : G →ₜ* CyclicGroup59Squared,
      reduction59.comp psi = chi) :
    ∃ b : Cochain (coefficients G) 1,
      differential (coefficients G) 1 2 b =
        cycleCochain (coefficients G) 2 3
          (pulledCarryCycle59 chi) := by
  obtain ⟨psi, hpsi⟩ := hlift
  exact ⟨liftPrimitive59 chi psi,
    differential_liftPrimitive59 chi psi hpsi⟩

/-- The pulled carry cycle is a boundary exactly when the quotient
character lifts continuously through C₅₉². -/
theorem pulledCarryCycle59_boundary_iff_exists_continuous_lift
    (chi : G →ₜ* CyclicGroup59) :
    (∃ b : Cochain (coefficients G) 1,
      differential (coefficients G) 1 2 b =
        cycleCochain (coefficients G) 2 3
          (pulledCarryCycle59 chi)) ↔
      ∃ psi : G →ₜ* CyclicGroup59Squared,
        reduction59.comp psi = chi := by
  constructor
  · exact exists_continuous_lift_of_pulledCarryCycle59_boundary chi
  · exact pulledCarryCycle59_boundary_of_exists_continuous_lift chi

/-- Equivalently, the pulled carry cycle is not a boundary exactly when
the character has no continuous C₅₉²-valued lift. -/
theorem pulledCarryCycle59_not_boundary_iff_noContinuousLift
    (chi : G →ₜ* CyclicGroup59) :
    (¬ ∃ b : Cochain (coefficients G) 1,
      differential (coefficients G) 1 2 b =
        cycleCochain (coefficients G) 2 3
          (pulledCarryCycle59 chi)) ↔ NoContinuousLift chi := by
  exact not_congr (pulledCarryCycle59_boundary_iff_exists_continuous_lift chi)

end Fermat.Conservation.ContinuousCarryLiftObstruction59
