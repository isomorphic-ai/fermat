/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Prime-parametric twisted Kummer lift and cup comparison

For every prime p, concrete reduction and cyclotomic twisted-action data for
a continuous C_(p²)-valued cochain identify the pulled carry class with the
genuine oriented Kummer cup in actual continuous cohomology.  No arithmetic
non-liftability value or prime-specific certificate is assumed.
-/
import Fermat.Experiments.Conservation.PrimeConcreteTwistedLiftCupBridge
import Fermat.Experiments.Conservation.PrimeKummerCharacterComparison
import Fermat.Experiments.Conservation.PrimeOrientedCarryH2Class
import Fermat.Experiments.Conservation.ContinuousKummerTateAlgebra

noncomputable section

open CategoryTheory ContinuousCohomology
open Fermat.Conservation.ContinuousKummerTateCupRaw
open Fermat.Conservation.ContinuousKummerTateCup.Nominal

namespace Fermat.Conservation.PrimeIntegratedTwistedKummerCup

open Fermat.Conservation.PrimeCyclicExtension
open Fermat.Conservation.PrimeContinuousCarryLift
open Fermat.Conservation.PrimeContinuousHomogeneousPullback
open Fermat.Conservation.PrimeConcreteTwistedLiftCupBridge
open Fermat.Conservation.PrimeKummerCharacterComparison
open Fermat.Conservation.PrimeOrientedCarryH2Class
open Fermat.Conservation.ContinuousKummerH1
open Fermat.Conservation.ContinuousKummerOrientation
open Fermat.Conservation.ContinuousKummerTateAlgebra
open Fermat.Conservation.LocalKummerH1

open scoped Fermat.Conservation.LocalKummerH1.KummerRootsDiscrete

attribute [local instance]
  PrimeCyclicExtension.instTopologicalSpaceCyclicGroup
  PrimeCyclicExtension.instDiscreteTopologyCyclicGroup
  PrimeCyclicExtension.instTopologicalSpaceCyclicGroupSquared
  PrimeCyclicExtension.instDiscreteTopologyCyclicGroupSquared

variable {p : ℕ} [Fact p.Prime]
local instance zmodContinuousSMul : ContinuousSMul (ZMod p) (ZMod p) :=
  ⟨continuous_of_discreteTopology⟩

/-! ## Continuous cyclic characters as nominal cycles -/

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The additively written value of a continuous cyclic character. -/
def characterValue (chi : G →ₜ* CyclicGroup p) : C(G, ZMod p) where
  toFun g := (chi g).toAdd
  continuous_toFun := chi.continuous

omit [IsTopologicalGroup G] in
theorem characterValue_mul (chi : G →ₜ* CyclicGroup p) (g h : G) :
    characterValue chi (g * h) = characterValue chi g + characterValue chi h := by
  exact congrArg Multiplicative.toAdd (map_mul chi g h)

/-- A continuous cyclic character as a nominal homogeneous one-cochain. -/
def characterCochain (chi : G →ₜ* CyclicGroup p) :
    Cochain (coefficients p G) 1 :=
  ⟨Fermat.Conservation.ContinuousKummerH1.homogeneousOneCochain
    (coefficients p G) (characterValue chi) (characterValue_mul chi)⟩

/-- A continuous cyclic character as a nominal homogeneous one-cycle. -/
def characterCycle (chi : G →ₜ* CyclicGroup p) :
    Cycle (coefficients p G) 1 2 :=
  ⟨characterCochain chi, by
    apply Cochain.ext
    exact Fermat.Conservation.ContinuousKummerH1.homogeneousOneCochain_isCycle
      (coefficients p G) (characterValue chi) (characterValue_mul chi)⟩

/-- Multiplication on the trivial coefficient line. -/
def multiplicationPairing :
    ContinuousEquivariantPairing
      (coefficients p G) (coefficients p G) (coefficients p G) where
  toLinearMap := LinearMap.mul (ZMod p) (ZMod p)
  continuous_uncurry := by
    change Continuous (fun x : ZMod p × ZMod p ↦ x.1 * x.2)
    exact continuous_fst.mul continuous_snd
  equivariant g a b := by simp

variable [LocallyCompactSpace G]

/-- The nominal cup cycle of two continuous cyclic characters. -/
def characterCupCycle
    (chi eta : G →ₜ* CyclicGroup p) : Cycle (coefficients p G) 2 3 :=
  cupCycleValue (multiplicationPairing (G := G))
    (characterCycle chi) (characterCycle eta)


/-! ## Oriented Kummer representatives in degree one -/

variable (F : Type) [Field F]

/-- The nominal roots-valued cycle of the public continuous Kummer
cocycle. -/
def kummerNominalCycle (a : Fˣ) :
    Cycle (rootsTopRepresentation p F) 1 2 :=
  ⟨⟨kummerHomogeneousOneCochain p F a⟩, by
    apply Cochain.ext
    exact kummerHomogeneousOneCochain_isCycle p F a⟩

/-- The nominal Kummer cycle projects to the public continuous Kummer
class. -/
theorem kummerNominalCycle_actualClass (a : Fˣ) :
    homologyLinearEquiv (rootsTopRepresentation p F) 1
        (h1Projection (rootsTopRepresentation p F) (kummerNominalCycle (p := p) F a)) =
      continuousClassOfUnit p F a := by
  rfl


/-- The same oriented Kummer cocycle in the nominal cycle shell. -/
def orientedKummerNominalCycle
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) (a : Fˣ) :
    Cycle (trivialTopLine p F) 1 2 := by
  let c := orientedKummerValue p F zeta hzeta a
  let hc := orientedKummerValue_mul p F zeta hzeta a
  exact ⟨⟨homogeneousOneCochain (trivialTopLine p F) c hc⟩, by
    apply Cochain.ext
    exact homogeneousOneCochain_isCycle (trivialTopLine p F) c hc⟩

/-- Direct projection of the oriented representative into genuine
continuous cohomology. -/
theorem orientedKummerNominalCycle_rawClass
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) (a : Fˣ) :
    homologyLinearEquiv (trivialTopLine p F) 1
        (h1Projection (trivialTopLine p F)
          (orientedKummerNominalCycle (p := p) F zeta hzeta a)) =
      homogeneousOneClass (trivialTopLine p F)
        (orientedKummerValue p F zeta hzeta a)
        (orientedKummerValue_mul p F zeta hzeta a) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Coefficient orientation sends the genuine roots-valued Kummer class to
the displayed primitive-root-coordinate representative. -/
theorem orient_continuousClassOfUnit_representative
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) (a : Fˣ) :
    orientH1 p F zeta hzeta (continuousClassOfUnit p F a) =
      homogeneousOneClass (trivialTopLine p F)
        (orientedKummerValue p F zeta hzeta a)
        (orientedKummerValue_mul p F zeta hzeta a) := by
  let phi := (homogeneousCochains (ZMod p) (AbsoluteGalois F)).map
    (rootsTopRepresentationEquivTrivial p F zeta hzeta).hom
  let sourceCycle := homogeneousOneCycle (rootsTopRepresentation p F)
    (continuousCocycle p F a) (continuousCocycle_crossed p F a)
  let targetCycle := homogeneousOneCycle (trivialTopLine p F)
    (orientedKummerValue p F zeta hzeta a)
    (orientedKummerValue_mul p F zeta hzeta a)
  have hcycles : (HomologicalComplex.cyclesMap phi 1).hom sourceCycle =
      targetCycle := by
    apply Fermat.Conservation.ContinuousKummerTateCup.cyclesInclusion_injective
      ((homogeneousCochains (ZMod p) (AbsoluteGalois F)).obj
        (trivialTopLine p F)) 1
    simp only [sourceCycle, targetCycle, homogeneousOneCycle,
      ← ConcreteCategory.comp_apply, Category.assoc,
      HomologicalComplex.cyclesMap_i,
      HomologicalComplex.liftCycles_i_assoc,
      HomologicalComplex.liftCycles_i]
    rw [ConcreteCategory.comp_apply]
    apply Subtype.ext
    apply ContinuousMap.ext
    intro g
    apply ContinuousMap.ext
    intro h
    dsimp only [phi]
    change coordinateContinuousLinearEquiv p F zeta hzeta
        (continuousCocycle p F a h - continuousCocycle p F a g) =
      coordinateContinuousLinearEquiv p F zeta hzeta
          (continuousCocycle p F a h) -
        coordinateContinuousLinearEquiv p F zeta hzeta
          (continuousCocycle p F a g)
    exact map_sub (coordinateContinuousLinearEquiv p F zeta hzeta) _ _
  have hnat := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (φ := phi) (i := 1)) sourceCycle
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hnat
  rw [hcycles] at hnat
  change (HomologicalComplex.homologyMap phi 1).hom
      ((((homogeneousCochains (ZMod p) (AbsoluteGalois F)).obj
        (rootsTopRepresentation p F)).homologyπ 1).hom sourceCycle) =
    (((homogeneousCochains (ZMod p) (AbsoluteGalois F)).obj
      (trivialTopLine p F)).homologyπ 1).hom targetCycle
  exact hnat

/-- The generic character-cycle construction agrees definitionally with
the pointwise oriented Kummer cycle. -/
theorem characterCycle_orientedKummerCharacter
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) (a : Fˣ) :
    characterCycle (orientedKummerCharacter p F zeta hzeta a) =
      orientedKummerNominalCycle (p := p) F zeta hzeta a := by
  apply Cycle.ext
  apply Cochain.ext
  rfl

theorem coefficients_absoluteGalois_eq_trivialTopLine :
    coefficients p (AbsoluteGalois F) = trivialTopLine p F :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The character-cycle projection is the genuinely oriented public Kummer
class. -/
theorem characterCycle_actualClass_eq_orientedKummer
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) (a : Fˣ) :
    homologyLinearEquiv (coefficients p (AbsoluteGalois F)) 1
        (h1Projection (coefficients p (AbsoluteGalois F))
          (characterCycle (orientedKummerCharacter p F zeta hzeta a))) =
      orientH1 p F zeta hzeta (continuousClassOfUnit p F a) := by
  change homologyLinearEquiv (trivialTopLine p F) 1
      (h1Projection (trivialTopLine p F)
        (characterCycle (orientedKummerCharacter p F zeta hzeta a))) = _
  rw [characterCycle_orientedKummerCharacter]
  rw [orientedKummerNominalCycle_rawClass]
  exact (orient_continuousClassOfUnit_representative
    (p := p) F zeta hzeta a).symm

/-! ## Tracking the genuine Kummer cup in degree two -/

local instance absoluteGaloisCompactSpace [CharZero F] :
    CompactSpace (AbsoluteGalois F) := by
  change CompactSpace (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
  infer_instance

local instance absoluteGaloisT2Space [CharZero F] :
    T2Space (AbsoluteGalois F) := by
  change T2Space (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
  infer_instance

variable [CharZero F]

/-- The concrete roots-valued cup cycle underlying the existing Kummer cup
on the representatives `a` and `b`. -/
def kummerCupNominalCycle
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) (a b : Fˣ) :
    Cycle (rootsTopRepresentation p F) 2 3 :=
  cupCycleValue (scalarTimesRootPairing p F)
    (orientedKummerNominalCycle (p := p) F zeta hzeta a)
    (kummerNominalCycle (p := p) F b)

/-- The existing actual Kummer cup is represented by the explicit nominal
cup cycle above. -/
theorem kummerCupH1_representative
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) (a b : Fˣ) :
    kummerCupH1 p F
        (orientH1 p F zeta hzeta (continuousClassOfUnit p F a))
        (continuousClassOfUnit p F b) =
      homologyLinearEquiv (rootsTopRepresentation p F) 2
        (h2Projection (rootsTopRepresentation p F)
          (kummerCupNominalCycle (p := p) F zeta hzeta a b)) := by
  rw [orient_continuousClassOfUnit_representative]
  rw [← orientedKummerNominalCycle_rawClass]
  rw [← kummerNominalCycle_actualClass]
  unfold kummerCupH1
  rw [Fermat.Conservation.ContinuousKummerTateCup.cupH1_projection]
  rfl

/-- Apply primitive-root coordinates pointwise to a roots-valued nominal
degree-two cycle. -/
def orientNominalCycleTwo
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (z : Cycle (rootsTopRepresentation p F) 2 3) :
    Cycle (trivialTopLine p F) 2 3 := by
  let phi := (homogeneousCochains (ZMod p) (AbsoluteGalois F)).map
    (rootsTopRepresentationEquivTrivial p F zeta hzeta).hom
  refine ⟨⟨(phi.f 2).hom z.cochain.val⟩, ?_⟩
  apply Cochain.ext
  have hz :
      (((homogeneousCochains (ZMod p) (AbsoluteGalois F)).obj
        (rootsTopRepresentation p F)).d 2 3).hom z.cochain.val = 0 :=
    congrArg Cochain.val z.isCycle
  have hcomm := ConcreteCategory.congr_hom (phi.comm 2 3) z.cochain.val
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hcomm
  change (((homogeneousCochains (ZMod p) (AbsoluteGalois F)).obj
      (trivialTopLine p F)).d 2 3).hom ((phi.f 2).hom z.cochain.val) = 0
  rw [hcomm, hz, map_zero]

/-- Pointwise coefficient orientation sends the concrete Kummer cup cycle
to the multiplication cup of the two oriented Kummer characters. -/
theorem orientNominalCycleTwo_kummerCup
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) (a b : Fˣ) :
    orientNominalCycleTwo (p := p) F zeta hzeta
        (kummerCupNominalCycle (p := p) F zeta hzeta a b) =
      characterCupCycle
        (orientedKummerCharacter p F zeta hzeta a)
        (orientedKummerCharacter p F zeta hzeta b) := by
  apply Cycle.ext
  apply Cochain.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  apply ContinuousMap.ext
  intro z
  change coordinateContinuousLinearEquiv p F zeta hzeta
      ((orientedKummerValue p F zeta hzeta a y -
          orientedKummerValue p F zeta hzeta a x) •
        (continuousCocycle p F b z - continuousCocycle p F b y)) =
    (orientedKummerValue p F zeta hzeta a y -
        orientedKummerValue p F zeta hzeta a x) *
      (orientedKummerValue p F zeta hzeta b z -
        orientedKummerValue p F zeta hzeta b y)
  rw [map_smul]
  rw [map_sub]
  rfl

/-- Readback of the nominal degree-two projection as the categorical
homology projection of the corresponding concrete kernel element. -/
theorem homologyLinearEquiv_h2Projection_apply
    {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (A : Action (TopModuleCat (ZMod p)) H)
    (z : Cycle A 2 3) :
    homologyLinearEquiv A 2 (h2Projection A z) =
      (((homogeneousCochains (ZMod p) H).obj A).homologyπ 2).hom
        ((kernelToCategoricalCycles
          ((homogeneousCochains (ZMod p) H).obj A) 2 3
          ((ComplexShape.up ℕ).next_eq' (by simp))).hom
            (cycleConcreteLinearEquiv A 2 3 z)) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
omit [CharZero F] in
/-- Coefficient orientation commutes with the genuine degree-two homology
projection of a nominal cycle. -/
theorem orientH2_h2Projection
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (z : Cycle (rootsTopRepresentation p F) 2 3) :
    orientH2 p F zeta hzeta
        (homologyLinearEquiv (rootsTopRepresentation p F) 2
          (h2Projection (rootsTopRepresentation p F) z)) =
      homologyLinearEquiv (trivialTopLine p F) 2
        (h2Projection (trivialTopLine p F)
          (orientNominalCycleTwo (p := p) F zeta hzeta z)) := by
  let phi := (homogeneousCochains (ZMod p) (AbsoluteGalois F)).map
    (rootsTopRepresentationEquivTrivial p F zeta hzeta).hom
  let sourceCycle :=
    (kernelToCategoricalCycles
      ((homogeneousCochains (ZMod p) (AbsoluteGalois F)).obj
        (rootsTopRepresentation p F)) 2 3
      ((ComplexShape.up ℕ).next_eq' (by simp))).hom
        (cycleConcreteLinearEquiv (rootsTopRepresentation p F) 2 3 z)
  let targetCycle :=
    (kernelToCategoricalCycles
      ((homogeneousCochains (ZMod p) (AbsoluteGalois F)).obj
        (trivialTopLine p F)) 2 3
      ((ComplexShape.up ℕ).next_eq' (by simp))).hom
        (cycleConcreteLinearEquiv (trivialTopLine p F) 2 3
          (orientNominalCycleTwo (p := p) F zeta hzeta z))
  have hcycles : (HomologicalComplex.cyclesMap phi 2).hom sourceCycle =
      targetCycle := by
    apply Fermat.Conservation.ContinuousKummerTateCup.cyclesInclusion_injective
      ((homogeneousCochains (ZMod p) (AbsoluteGalois F)).obj
        (trivialTopLine p F)) 2
    simp only [sourceCycle, targetCycle,
      ← ConcreteCategory.comp_apply, Category.assoc,
      HomologicalComplex.cyclesMap_i,
      kernelToCategoricalCycles_i_assoc,
      kernelToCategoricalCycles_i]
    rw [ConcreteCategory.comp_apply]
    rfl
  have hnat := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (φ := phi) (i := 2)) sourceCycle
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hnat
  rw [hcycles] at hnat
  rw [homologyLinearEquiv_h2Projection_apply,
    homologyLinearEquiv_h2Projection_apply]
  change (HomologicalComplex.homologyMap phi 2).hom
      ((((homogeneousCochains (ZMod p) (AbsoluteGalois F)).obj
        (rootsTopRepresentation p F)).homologyπ 2).hom sourceCycle) =
    (((homogeneousCochains (ZMod p) (AbsoluteGalois F)).obj
      (trivialTopLine p F)).homologyπ 2).hom targetCycle
  exact hnat

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The oriented existing Kummer cup is exactly the multiplication cup of
the two genuinely oriented Kummer classes. -/
theorem orientH2_kummerCupH1
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) (a b : Fˣ) :
    orientH2 p F zeta hzeta
        (kummerCupH1 p F
          (orientH1 p F zeta hzeta (continuousClassOfUnit p F a))
          (continuousClassOfUnit p F b)) =
      Fermat.Conservation.ContinuousKummerTateCup.cupH1
        (multiplicationPairing (G := AbsoluteGalois F))
        (orientH1 p F zeta hzeta (continuousClassOfUnit p F a))
        (orientH1 p F zeta hzeta (continuousClassOfUnit p F b)) := by
  rw [kummerCupH1_representative]
  rw [orientH2_h2Projection]
  rw [orientNominalCycleTwo_kummerCup]
  rw [← characterCycle_actualClass_eq_orientedKummer (p := p) F zeta hzeta a]
  rw [← characterCycle_actualClass_eq_orientedKummer (p := p) F zeta hzeta b]
  rw [Fermat.Conservation.ContinuousKummerTateCup.cupH1_projection]
  rfl


/-! ## The twisted carry-to-cup boundary -/


variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [LocallyCompactSpace G]

/-- Turn an inhomogeneous continuous one-cochain into an invariant
homogeneous one-cochain for trivial coefficients. -/
def homogeneousPrimitiveValue (r : C(G, ZMod p)) : C(G, C(G, ZMod p)) := by
  let f : C(G × G, ZMod p) :=
    ⟨fun wx ↦ r (wx.1⁻¹ * wx.2),
      r.continuous.comp (continuous_fst.inv.mul continuous_snd)⟩
  exact ContinuousMap.curry f

/-- The nominal homogeneous primitive associated to an inhomogeneous
continuous one-cochain. -/
def homogeneousPrimitive (r : C(G, ZMod p)) :
    Cochain (coefficients p G) 1 := by
  refine ⟨⟨homogeneousPrimitiveValue r, ?_⟩⟩
  intro a
  apply ContinuousMap.ext
  intro w
  apply ContinuousMap.ext
  intro x
  change r ((a⁻¹ * w)⁻¹ * (a⁻¹ * x)) = r (w⁻¹ * x)
  congr 1
  group

omit [LocallyCompactSpace G] in
@[simp]
theorem homogeneousPrimitive_differential_apply
    (r : C(G, ZMod p)) (w x y : G) :
    twoValue
        (differential (coefficients p G) 1 2 (homogeneousPrimitive r)).val
        w x y =
      r (x⁻¹ * y) - r (w⁻¹ * y) + r (w⁻¹ * x) := by
  change r (x⁻¹ * y) - (r (w⁻¹ * y) - r (w⁻¹ * x)) = _
  abel

/-- The concrete `C_(p²)` root/reduction/action data produce a boundary
between the explicit pulled carry and the character cup. -/
theorem pulledCarry_sub_characterCup_eq_boundary_of_twistedLift
    (chi eta : G →ₜ* CyclicGroup p)
    (q : C(G, CyclicGroupSquared p))
    (hred : ∀ g, reduction p (q g) = chi g)
    (htwist : ∀ g h,
      q (g * h) = q g * q h *
        kernelEmbed p (Multiplicative.ofAdd
          ((eta g).toAdd * (chi h).toAdd))) :
    differential (coefficients p G) 1 2
        (homogeneousPrimitive (twistedCupPrimitive chi eta q)) =
      cycleCochain (coefficients p G) 2 3
        (pulledCarryCycle chi - characterCupCycle chi eta) := by
  apply Cochain.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro w
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  change twoValue
      (differential (coefficients p G) 1 2
        (homogeneousPrimitive (twistedCupPrimitive chi eta q))).val
        w x y =
    twoValue
      (cycleCochain (coefficients p G) 2 3
        (pulledCarryCycle chi - characterCupCycle chi eta)).val w x y
  rw [homogeneousPrimitive_differential_apply, cycleCochain_val]
  change
    twistedCupPrimitive chi eta q (x⁻¹ * y) -
        twistedCupPrimitive chi eta q (w⁻¹ * y) +
        twistedCupPrimitive chi eta q (w⁻¹ * x) =
      PrimeCyclicH2.carry p
          (((chi w)⁻¹ * chi x).toAdd)
          (((chi x)⁻¹ * chi y).toAdd) -
        (((chi x).toAdd - (chi w).toAdd) *
          ((eta y).toAdd - (eta x).toAdd))
  rw [show w⁻¹ * y = (w⁻¹ * x) * (x⁻¹ * y) by group]
  rw [twistedCupPrimitive_equation chi eta q hred htwist]
  congr 1
  · congr 1 <;>
      simp only [map_mul, map_inv, toAdd_mul, toAdd_inv]
  · congr 1 <;>
      simp only [map_mul, map_inv, toAdd_mul, toAdd_inv] <;> abel

/-- Hence the pulled carry and character cup have the same nominal `H²`
class under concrete twisted-lift data. -/
theorem h2Projection_pulledCarry_eq_characterCup_of_twistedLift
    (chi eta : G →ₜ* CyclicGroup p)
    (q : C(G, CyclicGroupSquared p))
    (hred : ∀ g, reduction p (q g) = chi g)
    (htwist : ∀ g h,
      q (g * h) = q g * q h *
        kernelEmbed p (Multiplicative.ofAdd
          ((eta g).toAdd * (chi h).toAdd))) :
    h2Projection (coefficients p G) (pulledCarryCycle chi) =
      h2Projection (coefficients p G) (characterCupCycle chi eta) := by
  rw [← sub_eq_zero]
  rw [← map_sub]
  rw [h2Projection_eq_zero_iff]
  exact ⟨homogeneousPrimitive (twistedCupPrimitive chi eta q),
    pulledCarry_sub_characterCup_eq_boundary_of_twistedLift
      chi eta q hred htwist⟩

/-- The same equality in Mathlib's actual continuous-cohomology object. -/
theorem actualH2_pulledCarry_eq_characterCup_of_twistedLift
    (chi eta : G →ₜ* CyclicGroup p)
    (q : C(G, CyclicGroupSquared p))
    (hred : ∀ g, reduction p (q g) = chi g)
    (htwist : ∀ g h,
      q (g * h) = q g * q h *
        kernelEmbed p (Multiplicative.ofAdd
          ((eta g).toAdd * (chi h).toAdd))) :
    homologyLinearEquiv (coefficients p G) 2
        (h2Projection (coefficients p G) (pulledCarryCycle chi)) =
      Fermat.Conservation.ContinuousKummerTateCup.cupH1
        (multiplicationPairing (G := G))
        (homologyLinearEquiv (coefficients p G) 1
          (h1Projection (coefficients p G) (characterCycle chi)))
        (homologyLinearEquiv (coefficients p G) 1
          (h1Projection (coefficients p G) (characterCycle eta))) := by
  rw [Fermat.Conservation.ContinuousKummerTateCup.cupH1_projection]
  congr 1
  exact h2Projection_pulledCarry_eq_characterCup_of_twistedLift
    chi eta q hred htwist

/-! ## Specialization to the genuine Kummer cup -/

open Fermat.Conservation.ContinuousKummerH1
open Fermat.Conservation.ContinuousKummerOrientation
open Fermat.Conservation.ContinuousKummerTateAlgebra
open Fermat.Conservation.LocalKummerH1

open scoped Fermat.Conservation.LocalKummerH1.KummerRootsDiscrete

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- With an actual compatible `C_(p²)` Kummer coordinate satisfying its
reduction and cyclotomic action laws, the pulled carry class is the oriented
existing Kummer cup. -/
theorem pulledCarry_actualH2_eq_orientedKummerCup_of_twistedLift
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) (a : Fˣ)
    (q : C(AbsoluteGalois F, CyclicGroupSquared p))
    (hred : ∀ g, reduction p (q g) =
      orientedKummerCharacter p F zeta hzeta a g)
    (htwist : ∀ g h,
      q (g * h) = q g * q h *
        kernelEmbed p (Multiplicative.ofAdd
          ((orientedKummerCharacter p F zeta hzeta
              (Fermat.Conservation.KummerOrientation.primitiveUnit
                p F zeta hzeta) g).toAdd *
            (orientedKummerCharacter p F zeta hzeta a h).toAdd))) :
    orientedCarryH2Class F
        (orientedKummerCharacter p F zeta hzeta a) =
      orientH2 p F zeta hzeta
        (kummerCupH1 p F
          (orientH1 p F zeta hzeta (continuousClassOfUnit p F a))
          (continuousClassOfUnit p F
            (Fermat.Conservation.KummerOrientation.primitiveUnit
              p F zeta hzeta))) := by
  let chi := orientedKummerCharacter p F zeta hzeta a
  let eta := orientedKummerCharacter p F zeta hzeta
    (Fermat.Conservation.KummerOrientation.primitiveUnit p F zeta hzeta)
  calc
    orientedCarryH2Class F chi =
      Fermat.Conservation.ContinuousKummerTateCup.cupH1
        (multiplicationPairing (G := AbsoluteGalois F))
        (homologyLinearEquiv (coefficients p (AbsoluteGalois F)) 1
          (h1Projection (coefficients p (AbsoluteGalois F))
            (characterCycle chi)))
        (homologyLinearEquiv (coefficients p (AbsoluteGalois F)) 1
          (h1Projection (coefficients p (AbsoluteGalois F))
            (characterCycle eta))) :=
      actualH2_pulledCarry_eq_characterCup_of_twistedLift
        chi eta q hred htwist
    _ = Fermat.Conservation.ContinuousKummerTateCup.cupH1
        (multiplicationPairing (G := AbsoluteGalois F))
        (orientH1 p F zeta hzeta (continuousClassOfUnit p F a))
        (orientH1 p F zeta hzeta
          (continuousClassOfUnit p F
            (Fermat.Conservation.KummerOrientation.primitiveUnit
              p F zeta hzeta))) := by
      rw [characterCycle_actualClass_eq_orientedKummer]
      rw [characterCycle_actualClass_eq_orientedKummer]
    _ = orientH2 p F zeta hzeta
        (kummerCupH1 p F
          (orientH1 p F zeta hzeta (continuousClassOfUnit p F a))
          (continuousClassOfUnit p F
            (Fermat.Conservation.KummerOrientation.primitiveUnit
              p F zeta hzeta))) :=
      (orientH2_kummerCupH1 F zeta hzeta a
        (Fermat.Conservation.KummerOrientation.primitiveUnit
          p F zeta hzeta)).symm

end Fermat.Conservation.PrimeIntegratedTwistedKummerCup
