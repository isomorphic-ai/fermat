/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Explicit oriented representatives for the continuous Kummer cup at 59

This file identifies the public roots-valued continuous Kummer cocycle with
its primitive-root coordinate character and tracks that representative
through the existing degree-one and degree-two continuous-cohomology APIs.

In particular, it proves that coefficient orientation sends the genuine
roots-valued Kummer cup to the multiplication cup of the two oriented Kummer
characters.  It makes no Bockstein, carry, or non-liftability claim.
-/
import Fermat.Experiments.Conservation.FiniteCyclicH2Generator59
import Fermat.Experiments.Conservation.ContinuousHomogeneousPullback59
import Fermat.Experiments.Conservation.ContinuousKummerH1
import Fermat.Experiments.Conservation.ContinuousKummerTateCup
import Fermat.Experiments.Conservation.ContinuousKummerTateAlgebra

noncomputable section

open CategoryTheory
open ContinuousCohomology
open Fermat.Conservation.ContinuousKummerTateCupRaw
open Fermat.Conservation.ContinuousKummerTateCup.Nominal

namespace Fermat.Conservation.OrientedKummerRepresentative59

open Fermat.Conservation.FiniteCyclicH2Generator59
open Fermat.Conservation.ContinuousHomogeneousPullback59
open Fermat.Conservation.ContinuousKummerH1
open Fermat.Conservation.ContinuousKummerOrientation
open Fermat.Conservation.ContinuousKummerTateAlgebra
open Fermat.Conservation.LocalKummerH1
open Fermat.Conservation.TameSymbol

open scoped Fermat.Conservation.LocalKummerH1.KummerRootsDiscrete

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩
local instance zmodContinuousSMul : ContinuousSMul (ZMod 59) (ZMod 59) :=
  ⟨continuous_of_discreteTopology⟩

/-! ## Continuous cyclic characters as nominal cycles -/

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The additively written value of a continuous cyclic character. -/
def characterValue (chi : G →ₜ* CyclicGroup59) : C(G, ZMod 59) where
  toFun g := (chi g).toAdd
  continuous_toFun := chi.continuous

omit [IsTopologicalGroup G] in
theorem characterValue_mul (chi : G →ₜ* CyclicGroup59) (g h : G) :
    characterValue chi (g * h) = characterValue chi g + characterValue chi h := by
  exact congrArg Multiplicative.toAdd (map_mul chi g h)

/-- A continuous cyclic character as a nominal homogeneous one-cochain. -/
def characterCochain (chi : G →ₜ* CyclicGroup59) :
    Cochain (coefficients G) 1 :=
  ⟨Fermat.Conservation.ContinuousKummerH1.homogeneousOneCochain
    (coefficients G) (characterValue chi) (characterValue_mul chi)⟩

/-- A continuous cyclic character as a nominal homogeneous one-cycle. -/
def characterCycle (chi : G →ₜ* CyclicGroup59) :
    Cycle (coefficients G) 1 2 :=
  ⟨characterCochain chi, by
    apply Cochain.ext
    exact Fermat.Conservation.ContinuousKummerH1.homogeneousOneCochain_isCycle
      (coefficients G) (characterValue chi) (characterValue_mul chi)⟩

/-- Multiplication on the trivial coefficient line. -/
def multiplicationPairing :
    ContinuousEquivariantPairing
      (coefficients G) (coefficients G) (coefficients G) where
  toLinearMap := LinearMap.mul (ZMod 59) (ZMod 59)
  continuous_uncurry := by
    change Continuous (fun x : ZMod 59 × ZMod 59 ↦ x.1 * x.2)
    exact continuous_fst.mul continuous_snd
  equivariant g a b := by simp

variable [LocallyCompactSpace G]

/-- The nominal cup cycle of two continuous cyclic characters. -/
def characterCupCycle
    (chi eta : G →ₜ* CyclicGroup59) : Cycle (coefficients G) 2 3 :=
  cupCycleValue (multiplicationPairing (G := G))
    (characterCycle chi) (characterCycle eta)

/-! ## Genuine Kummer representatives in degree one -/

variable (F : Type) [Field F]

/-- The nominal roots-valued cycle of the public continuous Kummer
cocycle. -/
def kummerNominalCycle (a : Fˣ) :
    Cycle (rootsTopRepresentation 59 F) 1 2 :=
  ⟨⟨kummerHomogeneousOneCochain 59 F a⟩, by
    apply Cochain.ext
    exact kummerHomogeneousOneCochain_isCycle 59 F a⟩

/-- The nominal Kummer cycle projects to the public continuous Kummer
class. -/
theorem kummerNominalCycle_actualClass (a : Fˣ) :
    homologyLinearEquiv (rootsTopRepresentation 59 F) 1
        (h1Projection (rootsTopRepresentation 59 F) (kummerNominalCycle F a)) =
      continuousClassOfUnit 59 F a := by
  rfl

/-- Primitive-root coordinates of the roots-valued Kummer cocycle. -/
def orientedKummerValue
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) (a : Fˣ) :
    C(AbsoluteGalois F, ZMod 59) where
  toFun g := coordinateContinuousLinearEquiv 59 F zeta hzeta
    (continuousCocycle 59 F a g)
  continuous_toFun :=
    (coordinateContinuousLinearEquiv 59 F zeta hzeta).continuous.comp
      (continuousCocycle 59 F a).continuous

/-- Once the base field contains the chosen primitive root, the oriented
Kummer cocycle is an ordinary additive character. -/
theorem orientedKummerValue_mul
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) (a : Fˣ)
    (g h : AbsoluteGalois F) :
    orientedKummerValue F zeta hzeta a (g * h) =
      orientedKummerValue F zeta hzeta a g +
        orientedKummerValue F zeta hzeta a h := by
  change coordinateContinuousLinearEquiv 59 F zeta hzeta
      (continuousCocycle 59 F a (g * h)) = _
  rw [continuousCocycle_crossed]
  rw [map_add]
  congr 1
  exact congrArg (coordinateContinuousLinearEquiv 59 F zeta hzeta)
    (Fermat.Conservation.KummerOrientation.absoluteGalois_smul_root_eq
      59 F zeta hzeta g (continuousCocycle 59 F a h))

/-- The oriented Kummer cocycle as a continuous homomorphism to `C₅₉`. -/
def orientedKummerCharacter
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) (a : Fˣ) :
    AbsoluteGalois F →ₜ* CyclicGroup59 where
  toFun g := Multiplicative.ofAdd (orientedKummerValue F zeta hzeta a g)
  map_one' := by
    change orientedKummerValue F zeta hzeta a 1 = 0
    have h := orientedKummerValue_mul F zeta hzeta a 1 1
    simp only [one_mul] at h
    apply add_left_cancel (a := orientedKummerValue F zeta hzeta a 1)
    simpa using h.symm
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    simpa using orientedKummerValue_mul F zeta hzeta a g h
  continuous_toFun := (orientedKummerValue F zeta hzeta a).continuous

/-- The same oriented Kummer cocycle in the nominal cycle shell. -/
def orientedKummerNominalCycle
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) (a : Fˣ) :
    Cycle (trivialTopLine 59 F) 1 2 := by
  let c := orientedKummerValue F zeta hzeta a
  let hc := orientedKummerValue_mul F zeta hzeta a
  exact ⟨⟨homogeneousOneCochain (trivialTopLine 59 F) c hc⟩, by
    apply Cochain.ext
    exact homogeneousOneCochain_isCycle (trivialTopLine 59 F) c hc⟩

/-- Direct projection of the oriented representative into genuine
continuous cohomology. -/
theorem orientedKummerNominalCycle_rawClass
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) (a : Fˣ) :
    homologyLinearEquiv (trivialTopLine 59 F) 1
        (h1Projection (trivialTopLine 59 F)
          (orientedKummerNominalCycle F zeta hzeta a)) =
      homogeneousOneClass (trivialTopLine 59 F)
        (orientedKummerValue F zeta hzeta a)
        (orientedKummerValue_mul F zeta hzeta a) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Coefficient orientation sends the genuine roots-valued Kummer class to
the displayed primitive-root-coordinate representative. -/
theorem orient_continuousClassOfUnit_representative
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) (a : Fˣ) :
    orientH1 59 F zeta hzeta (continuousClassOfUnit 59 F a) =
      homogeneousOneClass (trivialTopLine 59 F)
        (orientedKummerValue F zeta hzeta a)
        (orientedKummerValue_mul F zeta hzeta a) := by
  let phi := (homogeneousCochains (ZMod 59) (AbsoluteGalois F)).map
    (rootsTopRepresentationEquivTrivial 59 F zeta hzeta).hom
  let sourceCycle := homogeneousOneCycle (rootsTopRepresentation 59 F)
    (continuousCocycle 59 F a) (continuousCocycle_crossed 59 F a)
  let targetCycle := homogeneousOneCycle (trivialTopLine 59 F)
    (orientedKummerValue F zeta hzeta a)
    (orientedKummerValue_mul F zeta hzeta a)
  have hcycles : (HomologicalComplex.cyclesMap phi 1).hom sourceCycle =
      targetCycle := by
    apply Fermat.Conservation.ContinuousKummerTateCup.cyclesInclusion_injective
      ((homogeneousCochains (ZMod 59) (AbsoluteGalois F)).obj
        (trivialTopLine 59 F)) 1
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
    change coordinateContinuousLinearEquiv 59 F zeta hzeta
        (continuousCocycle 59 F a h - continuousCocycle 59 F a g) =
      coordinateContinuousLinearEquiv 59 F zeta hzeta
          (continuousCocycle 59 F a h) -
        coordinateContinuousLinearEquiv 59 F zeta hzeta
          (continuousCocycle 59 F a g)
    exact map_sub (coordinateContinuousLinearEquiv 59 F zeta hzeta) _ _
  have hnat := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (φ := phi) (i := 1)) sourceCycle
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hnat
  rw [hcycles] at hnat
  change (HomologicalComplex.homologyMap phi 1).hom
      ((((homogeneousCochains (ZMod 59) (AbsoluteGalois F)).obj
        (rootsTopRepresentation 59 F)).homologyπ 1).hom sourceCycle) =
    (((homogeneousCochains (ZMod 59) (AbsoluteGalois F)).obj
      (trivialTopLine 59 F)).homologyπ 1).hom targetCycle
  exact hnat

/-- The generic character-cycle construction agrees definitionally with
the pointwise oriented Kummer cycle. -/
theorem characterCycle_orientedKummerCharacter
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) (a : Fˣ) :
    characterCycle (orientedKummerCharacter F zeta hzeta a) =
      orientedKummerNominalCycle F zeta hzeta a := by
  apply Cycle.ext
  apply Cochain.ext
  rfl

theorem coefficients_absoluteGalois_eq_trivialTopLine :
    coefficients (AbsoluteGalois F) = trivialTopLine 59 F :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The character-cycle projection is the genuinely oriented public Kummer
class. -/
theorem characterCycle_actualClass_eq_orientedKummer
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) (a : Fˣ) :
    homologyLinearEquiv (coefficients (AbsoluteGalois F)) 1
        (h1Projection (coefficients (AbsoluteGalois F))
          (characterCycle (orientedKummerCharacter F zeta hzeta a))) =
      orientH1 59 F zeta hzeta (continuousClassOfUnit 59 F a) := by
  change homologyLinearEquiv (trivialTopLine 59 F) 1
      (h1Projection (trivialTopLine 59 F)
        (characterCycle (orientedKummerCharacter F zeta hzeta a))) = _
  rw [characterCycle_orientedKummerCharacter]
  rw [orientedKummerNominalCycle_rawClass]
  exact (orient_continuousClassOfUnit_representative F zeta hzeta a).symm

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
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) (a b : Fˣ) :
    Cycle (rootsTopRepresentation 59 F) 2 3 :=
  cupCycleValue (scalarTimesRootPairing 59 F)
    (orientedKummerNominalCycle F zeta hzeta a)
    (kummerNominalCycle F b)

/-- The existing actual Kummer cup is represented by the explicit nominal
cup cycle above. -/
theorem kummerCupH1_representative
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) (a b : Fˣ) :
    kummerCupH1 59 F
        (orientH1 59 F zeta hzeta (continuousClassOfUnit 59 F a))
        (continuousClassOfUnit 59 F b) =
      homologyLinearEquiv (rootsTopRepresentation 59 F) 2
        (h2Projection (rootsTopRepresentation 59 F)
          (kummerCupNominalCycle F zeta hzeta a b)) := by
  rw [orient_continuousClassOfUnit_representative]
  rw [← orientedKummerNominalCycle_rawClass]
  rw [← kummerNominalCycle_actualClass]
  unfold kummerCupH1
  rw [Fermat.Conservation.ContinuousKummerTateCup.cupH1_projection]
  rfl

/-- Apply primitive-root coordinates pointwise to a roots-valued nominal
degree-two cycle. -/
def orientNominalCycleTwo
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (z : Cycle (rootsTopRepresentation 59 F) 2 3) :
    Cycle (trivialTopLine 59 F) 2 3 := by
  let phi := (homogeneousCochains (ZMod 59) (AbsoluteGalois F)).map
    (rootsTopRepresentationEquivTrivial 59 F zeta hzeta).hom
  refine ⟨⟨(phi.f 2).hom z.cochain.val⟩, ?_⟩
  apply Cochain.ext
  have hz :
      (((homogeneousCochains (ZMod 59) (AbsoluteGalois F)).obj
        (rootsTopRepresentation 59 F)).d 2 3).hom z.cochain.val = 0 :=
    congrArg Cochain.val z.isCycle
  have hcomm := ConcreteCategory.congr_hom (phi.comm 2 3) z.cochain.val
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hcomm
  change (((homogeneousCochains (ZMod 59) (AbsoluteGalois F)).obj
      (trivialTopLine 59 F)).d 2 3).hom ((phi.f 2).hom z.cochain.val) = 0
  rw [hcomm, hz, map_zero]

/-- Pointwise coefficient orientation sends the concrete Kummer cup cycle
to the multiplication cup of the two oriented Kummer characters. -/
theorem orientNominalCycleTwo_kummerCup
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) (a b : Fˣ) :
    orientNominalCycleTwo F zeta hzeta
        (kummerCupNominalCycle F zeta hzeta a b) =
      characterCupCycle
        (orientedKummerCharacter F zeta hzeta a)
        (orientedKummerCharacter F zeta hzeta b) := by
  apply Cycle.ext
  apply Cochain.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  apply ContinuousMap.ext
  intro z
  change coordinateContinuousLinearEquiv 59 F zeta hzeta
      ((orientedKummerValue F zeta hzeta a y -
          orientedKummerValue F zeta hzeta a x) •
        (continuousCocycle 59 F b z - continuousCocycle 59 F b y)) =
    (orientedKummerValue F zeta hzeta a y -
        orientedKummerValue F zeta hzeta a x) *
      (orientedKummerValue F zeta hzeta b z -
        orientedKummerValue F zeta hzeta b y)
  rw [map_smul]
  rw [map_sub]
  rfl

/-- Readback of the nominal degree-two projection as the categorical
homology projection of the corresponding concrete kernel element. -/
theorem homologyLinearEquiv_h2Projection_apply
    {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (A : Action (TopModuleCat (ZMod 59)) H)
    (z : Cycle A 2 3) :
    homologyLinearEquiv A 2 (h2Projection A z) =
      (((homogeneousCochains (ZMod 59) H).obj A).homologyπ 2).hom
        ((kernelToCategoricalCycles
          ((homogeneousCochains (ZMod 59) H).obj A) 2 3
          ((ComplexShape.up ℕ).next_eq' (by simp))).hom
            (cycleConcreteLinearEquiv A 2 3 z)) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
omit [CharZero F] in
/-- Coefficient orientation commutes with the genuine degree-two homology
projection of a nominal cycle. -/
theorem orientH2_h2Projection
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (z : Cycle (rootsTopRepresentation 59 F) 2 3) :
    orientH2 59 F zeta hzeta
        (homologyLinearEquiv (rootsTopRepresentation 59 F) 2
          (h2Projection (rootsTopRepresentation 59 F) z)) =
      homologyLinearEquiv (trivialTopLine 59 F) 2
        (h2Projection (trivialTopLine 59 F)
          (orientNominalCycleTwo F zeta hzeta z)) := by
  let phi := (homogeneousCochains (ZMod 59) (AbsoluteGalois F)).map
    (rootsTopRepresentationEquivTrivial 59 F zeta hzeta).hom
  let sourceCycle :=
    (kernelToCategoricalCycles
      ((homogeneousCochains (ZMod 59) (AbsoluteGalois F)).obj
        (rootsTopRepresentation 59 F)) 2 3
      ((ComplexShape.up ℕ).next_eq' (by simp))).hom
        (cycleConcreteLinearEquiv (rootsTopRepresentation 59 F) 2 3 z)
  let targetCycle :=
    (kernelToCategoricalCycles
      ((homogeneousCochains (ZMod 59) (AbsoluteGalois F)).obj
        (trivialTopLine 59 F)) 2 3
      ((ComplexShape.up ℕ).next_eq' (by simp))).hom
        (cycleConcreteLinearEquiv (trivialTopLine 59 F) 2 3
          (orientNominalCycleTwo F zeta hzeta z))
  have hcycles : (HomologicalComplex.cyclesMap phi 2).hom sourceCycle =
      targetCycle := by
    apply Fermat.Conservation.ContinuousKummerTateCup.cyclesInclusion_injective
      ((homogeneousCochains (ZMod 59) (AbsoluteGalois F)).obj
        (trivialTopLine 59 F)) 2
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
      ((((homogeneousCochains (ZMod 59) (AbsoluteGalois F)).obj
        (rootsTopRepresentation 59 F)).homologyπ 2).hom sourceCycle) =
    (((homogeneousCochains (ZMod 59) (AbsoluteGalois F)).obj
      (trivialTopLine 59 F)).homologyπ 2).hom targetCycle
  exact hnat

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The oriented existing Kummer cup is exactly the multiplication cup of
the two genuinely oriented Kummer classes. -/
theorem orientH2_kummerCupH1
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) (a b : Fˣ) :
    orientH2 59 F zeta hzeta
        (kummerCupH1 59 F
          (orientH1 59 F zeta hzeta (continuousClassOfUnit 59 F a))
          (continuousClassOfUnit 59 F b)) =
      Fermat.Conservation.ContinuousKummerTateCup.cupH1
        (multiplicationPairing (G := AbsoluteGalois F))
        (orientH1 59 F zeta hzeta (continuousClassOfUnit 59 F a))
        (orientH1 59 F zeta hzeta (continuousClassOfUnit 59 F b)) := by
  rw [kummerCupH1_representative]
  rw [orientH2_h2Projection]
  rw [orientNominalCycleTwo_kummerCup]
  rw [← characterCycle_actualClass_eq_orientedKummer F zeta hzeta a]
  rw [← characterCycle_actualClass_eq_orientedKummer F zeta hzeta b]
  rw [Fermat.Conservation.ContinuousKummerTateCup.cupH1_projection]
  rfl

end Fermat.Conservation.OrientedKummerRepresentative59
