/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Prime-parametric finite and continuous cyclic H²

For every prime \`p\`, this module builds the standard-representative carry
cocycle on \`C_p = Multiplicative (ZMod p)\`, proves symbolically that one
generator loop reads exactly one, and shows that the loop sum kills every
boundary.  It then transports the carry into genuine homogeneous continuous
cohomology for the discrete topology and proves that the normalized readout
is a linear equivalence

\`H²_cont(C_p, F_p) ≃ₗ[F_p] F_p\`.

The construction is route-neutral: it is finite cyclic group cohomology, not
a local invariant, an inflation theorem, or a Hilbert-symbol comparison.
-/
import Fermat.Conservation.DiscreteToContinuousH2
import Mathlib.Algebra.Field.ZMod
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic

noncomputable section

open CategoryTheory
open ContinuousCohomology
open Fermat.Conservation.ContinuousKummerTateCupRaw
open Fermat.Conservation.ContinuousKummerTateCup.Nominal
open Fermat.Conservation.DiscreteToContinuousH2

namespace Fermat.Conservation.PrimeCyclicH2

variable (p : ℕ) [Fact p.Prime]

abbrev CyclicGroup := Multiplicative (ZMod p)

abbrev coefficients : Rep (ZMod p) (CyclicGroup p) :=
  Rep.trivial (ZMod p) (CyclicGroup p) (ZMod p)

def generator : CyclicGroup p := Multiplicative.ofAdd 1

lemma cyclicGroup_card : Nat.card (CyclicGroup p) = p := by
  simp [CyclicGroup]

lemma generator_ne_one : generator p ≠ 1 := by
  change Multiplicative.ofAdd (1 : ZMod p) ≠ Multiplicative.ofAdd 0
  simp

lemma generator_generates (x : CyclicGroup p) :
    x ∈ Subgroup.zpowers (generator p) :=
  mem_zpowers_of_prime_card (cyclicGroup_card p) (generator_ne_one p)

def invariantOne :
    LinearMap.ker
      ((coefficients p).applyAsHom (generator p) - 𝟙 (coefficients p)).hom.toLinearMap :=
  ⟨1, by
    change (1 : ZMod p) - 1 = 0
    simp⟩

set_option maxRecDepth 10000 in
lemma coefficients_norm_eq_zero :
    (coefficients p).norm.hom.toLinearMap = 0 := by
  apply LinearMap.ext
  intro x
  simp [Rep.norm, Representation.norm, coefficients, Finset.sum_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card, cyclicGroup_card,
    nsmul_eq_mul]

def finiteCyclicH2Class : groupCohomology (coefficients p) 2 :=
  Rep.FiniteCyclicGroup.groupCohomologyπEven
    (coefficients p) (generator p) (generator_generates p) 2
      (by exact ⟨1, rfl⟩) (invariantOne p)

set_option maxRecDepth 10000 in
theorem finiteCyclicH2Class_ne_zero : finiteCyclicH2Class p ≠ 0 := by
  intro hzero
  have hrange :
      (1 : ZMod p) ∈ LinearMap.range (coefficients p).norm.hom.toLinearMap :=
    (Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff
      (coefficients p) (generator p) (generator_generates p) 2
        (by exact ⟨1, rfl⟩) (invariantOne p)).mp hzero
  rw [coefficients_norm_eq_zero] at hrange
  simp at hrange

theorem finiteCyclicH2Class_spans
    (x : groupCohomology (coefficients p) 2) :
    ∃ a : ZMod p, a • finiteCyclicH2Class p = x := by
  have hsurj : Function.Surjective
      (Rep.FiniteCyclicGroup.groupCohomologyπEven
        (coefficients p) (generator p) (generator_generates p) 2
          (by exact ⟨1, rfl⟩)).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨y, rfl⟩ := hsurj x
  refine ⟨y.1, ?_⟩
  change y.1 •
      (Rep.FiniteCyclicGroup.groupCohomologyπEven
        (coefficients p) (generator p) (generator_generates p) 2
          (by exact ⟨1, rfl⟩)).hom (invariantOne p) = _
  rw [← map_smul]
  congr 1
  apply Subtype.ext
  simp [invariantOne]

def finiteCyclicH2GeneratorMap :
    ZMod p →ₗ[ZMod p] groupCohomology (coefficients p) 2 where
  toFun a := a • finiteCyclicH2Class p
  map_add' a b := add_smul a b (finiteCyclicH2Class p)
  map_smul' a b := by simp [mul_smul]

theorem finiteCyclicH2GeneratorMap_bijective :
    Function.Bijective (finiteCyclicH2GeneratorMap p) := by
  constructor
  · intro a b hab
    change a • finiteCyclicH2Class p = b • finiteCyclicH2Class p at hab
    exact smul_left_injective (ZMod p) (finiteCyclicH2Class_ne_zero p) hab
  · intro x
    obtain ⟨a, rfl⟩ := finiteCyclicH2Class_spans p x
    exact ⟨a, rfl⟩

def finiteCyclicH2LinearEquiv :
    ZMod p ≃ₗ[ZMod p] groupCohomology (coefficients p) 2 :=
  LinearEquiv.ofBijective (finiteCyclicH2GeneratorMap p)
    (finiteCyclicH2GeneratorMap_bijective p)

def finiteCyclicH2ReadoutEquiv :
    groupCohomology (coefficients p) 2 ≃ₗ[ZMod p] ZMod p :=
  (finiteCyclicH2LinearEquiv p).symm

@[simp]
theorem finiteCyclicH2ReadoutEquiv_class :
    finiteCyclicH2ReadoutEquiv p (finiteCyclicH2Class p) = 1 := by
  change (finiteCyclicH2LinearEquiv p).symm (finiteCyclicH2Class p) = 1
  rw [← one_smul (ZMod p) (finiteCyclicH2Class p)]
  change (finiteCyclicH2LinearEquiv p).symm
    (finiteCyclicH2LinearEquiv p 1) = 1
  simp

local instance : Fintype (CyclicGroup p) := inferInstanceAs (Fintype (ZMod p))

def carry (a b : ZMod p) : ZMod p :=
  if p ≤ a.val + b.val then 1 else 0

def carryFunction : CyclicGroup p × CyclicGroup p → coefficients p :=
  fun gh ↦ carry p gh.1.toAdd gh.2.toAdd

theorem carryFunction_mem_cocycles₂ :
    carryFunction p ∈ groupCohomology.cocycles₂ (coefficients p) := by
  rw [groupCohomology.mem_cocycles₂_def]
  change ∀ (a b c : ZMod p),
    carry p b c - carry p (a + b) c +
      carry p a (b + c) - carry p a b = 0
  intro a b c
  have ha : a.val < p := a.val_lt
  have hb : b.val < p := b.val_lt
  have hc : c.val < p := c.val_lt
  have hab_val : (a + b).val =
      if p ≤ a.val + b.val then a.val + b.val - p else a.val + b.val := by
    split_ifs with h
    · exact ZMod.val_add_of_le h
    · exact ZMod.val_add_of_lt (lt_of_not_ge h)
  have hbc_val : (b + c).val =
      if p ≤ b.val + c.val then b.val + c.val - p else b.val + c.val := by
    split_ifs with h
    · exact ZMod.val_add_of_le h
    · exact ZMod.val_add_of_lt (lt_of_not_ge h)
  simp only [carry]
  split_ifs with hbc hab_c ha_bc hab <;>
    simp_all <;>
    norm_num <;>
    omega

def carryCocycle : groupCohomology.cocycles₂ (coefficients p) :=
  ⟨carryFunction p, carryFunction_mem_cocycles₂ p⟩

@[simp]
theorem carryCocycle_apply (g h : CyclicGroup p) :
    carryCocycle p (g, h) = carry p g.toAdd h.toAdd := rfl

lemma val_neg_one_prime : (-1 : ZMod p).val = p - 1 := by
  cases p with
  | zero =>
      exact ((Fact.out : Nat.Prime 0).ne_zero rfl).elim
  | succ n =>
      simp [ZMod.val_neg_one]

lemma carry_generator_apply (h : CyclicGroup p) :
    carry p (generator p).toAdd h.toAdd =
      if h = Multiplicative.ofAdd (-1 : ZMod p) then 1 else 0 := by
  have hp_one : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hone : (1 : ZMod p).val = 1 := by
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hp_one]
  have hcriterion :
      p ≤ (1 : ZMod p).val + h.toAdd.val ↔
        h = Multiplicative.ofAdd (-1 : ZMod p) := by
    constructor
    · intro hle
      change h.toAdd = (-1 : ZMod p)
      apply ZMod.val_injective p
      rw [val_neg_one_prime]
      rw [hone] at hle
      have hlt := h.toAdd.val_lt
      omega
    · intro heq
      rw [heq]
      change p ≤ (1 : ZMod p).val + (-1 : ZMod p).val
      rw [hone, val_neg_one_prime]
      omega
  change carry p (1 : ZMod p) h.toAdd = _
  simp only [carry]
  by_cases hc : p ≤ (1 : ZMod p).val + h.toAdd.val
  · rw [if_pos hc, if_pos (hcriterion.mp hc)]
  · rw [if_neg hc, if_neg (mt hcriterion.mpr hc)]

theorem sum_carryCocycle_generator :
    ∑ h : CyclicGroup p, carryCocycle p (generator p, h) = 1 := by
  simp_rw [carryCocycle_apply, carry_generator_apply]
  classical
  rw [Finset.sum_eq_single (Multiplicative.ofAdd (-1 : ZMod p))]
  · simp
  · intro b _ hb
    rw [if_neg]
    change b ≠ Multiplicative.ofAdd (-1 : ZMod p)
    exact hb
  · simp

theorem sum_discreteBoundary_generator
    (b : CyclicGroup p → coefficients p) :
    ∑ h : CyclicGroup p,
      (groupCohomology.d₁₂ (coefficients p)).hom b (generator p, h) = 0 := by
  simp only [groupCohomology.d₁₂_hom_apply]
  change ∑ h : CyclicGroup p,
      (b h - b (generator p * h) + b (generator p)) = 0
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hperm : (∑ h : CyclicGroup p, b (generator p * h)) =
      ∑ h : CyclicGroup p, b h :=
    (Group.mulLeft_bijective (generator p)).sum_comp b
  rw [hperm, sub_self, zero_add, Finset.sum_const, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card, cyclicGroup_card]
  change p • (b (generator p) : ZMod p) = 0
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

theorem carryCocycle_not_mem_coboundaries₂ :
    ⇑(carryCocycle p) ∉ groupCohomology.coboundaries₂ (coefficients p) := by
  intro hboundary
  obtain ⟨b, hb⟩ := hboundary
  have hsum := congrArg
    (fun f : CyclicGroup p × CyclicGroup p → coefficients p ↦
      ∑ h : CyclicGroup p, f (generator p, h)) hb
  rw [sum_discreteBoundary_generator, sum_carryCocycle_generator] at hsum
  exact zero_ne_one hsum

local instance : TopologicalSpace (ZMod p) := ⊥
local instance : DiscreteTopology (ZMod p) := ⟨rfl⟩
local instance : TopologicalSpace (CyclicGroup p) := ⊥
local instance : DiscreteTopology (CyclicGroup p) := ⟨rfl⟩

abbrev continuousCoefficients :=
  trivialAction (R := ZMod p) (G := CyclicGroup p)

def continuousCarryCycle :
    Cycle (continuousCoefficients p) 2 3 :=
  continuousCycleOfDiscrete (carryCocycle p)

theorem continuousCarryCycle_not_boundary :
    ¬ ∃ b : Cochain (continuousCoefficients p) 1,
      differential (continuousCoefficients p) 1 2 b =
        cycleCochain (continuousCoefficients p) 2 3
          (continuousCarryCycle p) :=
  continuousCycleOfDiscrete_not_boundary (carryCocycle p)
    (carryCocycle_not_mem_coboundaries₂ p)

def continuousCarryH2Class :
    (continuousCohomology (ZMod p) (CyclicGroup p) 2).obj
      (continuousCoefficients p) :=
  homologyLinearEquiv (continuousCoefficients p) 2
    (h2Projection (continuousCoefficients p)
      (continuousCarryCycle p))

theorem continuousCarryH2Class_ne_zero :
    continuousCarryH2Class p ≠ 0 := by
  intro hzero
  have hprojection :
      h2Projection (continuousCoefficients p)
        (continuousCarryCycle p) = 0 := by
    let e := homologyLinearEquiv (continuousCoefficients p) 2
    change e (h2Projection (continuousCoefficients p)
      (continuousCarryCycle p)) = 0 at hzero
    exact e.injective (hzero.trans e.map_zero.symm)
  exact continuousCarryCycle_not_boundary p
    ((h2Projection_eq_zero_iff (continuousCoefficients p)
      (continuousCarryCycle p)).mp hprojection)

/-- One summand of the generator-loop evaluation of a homogeneous cycle. -/
def cyclicCycleValue
    (z : Cycle (continuousCoefficients p) 2 3)
    (h : CyclicGroup p) : ZMod p :=
  show ZMod p from
    twoValue z.cochain.val 1 (generator p) (generator p * h)

/-- Sum a continuous homogeneous two-cycle once around the chosen generator. -/
def cyclicCycleSum :
    Cycle (continuousCoefficients p) 2 3 →ₗ[ZMod p] ZMod p where
  toFun z := ∑ h : CyclicGroup p, cyclicCycleValue p z h
  map_add' x y := by
    have hvalue (h : CyclicGroup p) :
        cyclicCycleValue p (x + y) h =
          cyclicCycleValue p x h + cyclicCycleValue p y h := by
      rfl
    simp_rw [hvalue]
    rw [Finset.sum_add_distrib]
  map_smul' a x := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rfl

@[simp]
theorem cyclicCycleSum_continuousCarryCycle :
    cyclicCycleSum p (continuousCarryCycle p) = 1 := by
  change (∑ h : CyclicGroup p,
    cyclicCycleValue p (continuousCarryCycle p) h) = 1
  have hvalue (h : CyclicGroup p) :
      cyclicCycleValue p (continuousCarryCycle p) h =
        carryCocycle p (generator p, h) := by
    change carryCocycle p
      (1⁻¹ * generator p, (generator p)⁻¹ * (generator p * h)) = _
    rw [inv_one, one_mul, inv_mul_cancel_left]
  simp_rw [hvalue]
  exact sum_carryCocycle_generator p

theorem sum_continuousBoundary_generator
    (b : Cochain (continuousCoefficients p) 1) :
    ∑ h : CyclicGroup p,
      twoValue (differential (continuousCoefficients p) 1 2 b).val
        1 (generator p) (generator p * h) = 0 := by
  let b' : CyclicGroup p → coefficients p := fun g ↦ oneValue b.val 1 g
  have hpoint (h : CyclicGroup p) :
      twoValue (differential (continuousCoefficients p) 1 2 b).val
          1 (generator p) (generator p * h) =
        (groupCohomology.d₁₂ (coefficients p)).hom b'
          (generator p, h) := by
    rw [differential_val, continuousOneDifferential_apply]
    change oneValue b.val (generator p) (generator p * h) -
        (oneValue b.val 1 (generator p * h) -
          oneValue b.val 1 (generator p)) = _
    have hinv := oneValue_invariant b.val (generator p)
      (generator p) (generator p * h)
    have hinv' : oneValue b.val 1 h =
        oneValue b.val (generator p) (generator p * h) := by
      simpa using hinv
    rw [← hinv']
    simp only [groupCohomology.d₁₂_hom_apply]
    change oneValue b.val 1 h -
        (oneValue b.val 1 (generator p * h) -
          oneValue b.val 1 (generator p)) =
      oneValue b.val 1 h - oneValue b.val 1 (generator p * h) +
        oneValue b.val 1 (generator p)
    abel
  simp_rw [hpoint]
  exact sum_discreteBoundary_generator p b'

theorem cyclicCycleSum_eq_zero_of_h2Projection_eq_zero
    (z : Cycle (continuousCoefficients p) 2 3)
    (hz : h2Projection (continuousCoefficients p) z = 0) :
    cyclicCycleSum p z = 0 := by
  obtain ⟨b, hb⟩ :=
    (h2Projection_eq_zero_iff (continuousCoefficients p) z).mp hz
  change (∑ h : CyclicGroup p,
    twoValue z.cochain.val 1 (generator p) (generator p * h)) = 0
  have hbval := congrArg Cochain.val hb
  rw [differential_val, cycleCochain_val] at hbval
  rw [← hbval]
  exact sum_continuousBoundary_generator p b

theorem ker_h2Projection_le_ker_cyclicCycleSum :
    LinearMap.ker (h2Projection (continuousCoefficients p)) ≤
      LinearMap.ker (cyclicCycleSum p) := by
  intro z hz
  rw [LinearMap.mem_ker] at hz ⊢
  exact cyclicCycleSum_eq_zero_of_h2Projection_eq_zero p z hz

theorem h2Projection_surjective :
    Function.Surjective (h2Projection (continuousCoefficients p)) :=
  cycleToHomology_surjective (continuousCoefficients p) 2 3
    ((ComplexShape.up ℕ).next_eq' (by simp))

/-- The generator-loop sum descended through actual continuous homology. -/
noncomputable def continuousCyclicH2Readout :
    Homology (continuousCoefficients p) 2 →ₗ[ZMod p] ZMod p :=
  ((LinearMap.ker (h2Projection (continuousCoefficients p))).liftQ
      (cyclicCycleSum p) (ker_h2Projection_le_ker_cyclicCycleSum p)).comp
    ((h2Projection (continuousCoefficients p)).quotKerEquivOfSurjective
      (h2Projection_surjective p)).symm.toLinearMap

@[simp]
theorem continuousCyclicH2Readout_h2Projection
    (z : Cycle (continuousCoefficients p) 2 3) :
    continuousCyclicH2Readout p
        (h2Projection (continuousCoefficients p) z) =
      cyclicCycleSum p z := by
  change ((LinearMap.ker (h2Projection (continuousCoefficients p))).liftQ
      (cyclicCycleSum p) (ker_h2Projection_le_ker_cyclicCycleSum p))
    (((h2Projection (continuousCoefficients p)).quotKerEquivOfSurjective
      (h2Projection_surjective p)).symm
        (h2Projection (continuousCoefficients p) z)) = _
  rw [(h2Projection (continuousCoefficients p)).quotKerEquivOfSurjective_symm_apply]
  exact Submodule.liftQ_apply _ _ _

/-- The normalized readout on Mathlib's exposed continuous cohomology object. -/
noncomputable def actualContinuousCyclicH2Readout :
    (continuousCohomology (ZMod p) (CyclicGroup p) 2).obj
        (continuousCoefficients p) →ₗ[ZMod p] ZMod p :=
  (continuousCyclicH2Readout p).comp
    (homologyLinearEquiv (continuousCoefficients p) 2).symm.toLinearMap

@[simp]
theorem actualContinuousCyclicH2Readout_continuousCarryH2Class :
    actualContinuousCyclicH2Readout p (continuousCarryH2Class p) = 1 := by
  change continuousCyclicH2Readout p
      (h2Projection (continuousCoefficients p) (continuousCarryCycle p)) = 1
  rw [continuousCyclicH2Readout_h2Projection]
  exact cyclicCycleSum_continuousCarryCycle p

/-- The scalar multiples of the continuous carry class. -/
def actualContinuousCyclicH2Generator :
    ZMod p →ₗ[ZMod p]
      (continuousCohomology (ZMod p) (CyclicGroup p) 2).obj
        (continuousCoefficients p) where
  toFun a := a • continuousCarryH2Class p
  map_add' a b := add_smul a b (continuousCarryH2Class p)
  map_smul' a b := by simp [mul_smul]

@[simp]
theorem actualContinuousCyclicH2Readout_generator (a : ZMod p) :
    actualContinuousCyclicH2Readout p
        (actualContinuousCyclicH2Generator p a) = a := by
  simp [actualContinuousCyclicH2Generator]

theorem actualContinuousCyclicH2Readout_surjective :
    Function.Surjective (actualContinuousCyclicH2Readout p) :=
  fun a ↦ ⟨actualContinuousCyclicH2Generator p a, by simp⟩

theorem actualContinuousCyclicH2Generator_injective :
    Function.Injective (actualContinuousCyclicH2Generator p) :=
  Function.LeftInverse.injective
    (actualContinuousCyclicH2Readout_generator p)

private def threeValue
    (f : ((homogeneousCochains (ZMod p) (CyclicGroup p)).obj
      (continuousCoefficients p)).X 3) :
    C(CyclicGroup p, C(CyclicGroup p, C(CyclicGroup p,
      C(CyclicGroup p, ZMod p)))) := by
  change {x : C(CyclicGroup p, C(CyclicGroup p, C(CyclicGroup p,
    C(CyclicGroup p, ZMod p)))) // ∀ g : CyclicGroup p, _} at f
  exact f.1

private theorem continuousTwoCycle_identity
    (f : ((homogeneousCochains (ZMod p) (CyclicGroup p)).obj
      (continuousCoefficients p)).X 2)
    (hf : (((homogeneousCochains (ZMod p) (CyclicGroup p)).obj
      (continuousCoefficients p)).d 2 3).hom f = 0)
    (w x y z : CyclicGroup p) :
    twoValue f x y z -
      (twoValue f w y z -
        (twoValue f w x z - twoValue f w x y)) = 0 := by
  have h := congrArg
    (fun q : ((homogeneousCochains (ZMod p) (CyclicGroup p)).obj
      (continuousCoefficients p)).X 3 ↦ threeValue p q w x y z) hf
  exact h

private theorem twoValue_invariant
    (f : ((homogeneousCochains (ZMod p) (CyclicGroup p)).obj
      (continuousCoefficients p)).X 2)
    (a x y z : CyclicGroup p) :
    ((continuousCoefficients p).ρ a).hom
        (twoValue f (a⁻¹ * x) (a⁻¹ * y) (a⁻¹ * z)) =
      twoValue f x y z := by
  change {q : C(CyclicGroup p, C(CyclicGroup p,
    C(CyclicGroup p, ZMod p))) // ∀ g : CyclicGroup p, _} at f
  exact congrArg
    (fun q : C(CyclicGroup p, C(CyclicGroup p, C(CyclicGroup p, ZMod p))) ↦
      q x y z) (f.2 a)

def discreteTwoOfContinuous
    (z : Cycle (continuousCoefficients p) 2 3) :
    CyclicGroup p × CyclicGroup p → coefficients p :=
  fun gh ↦ twoValue z.cochain.val 1 gh.1 (gh.1 * gh.2)

theorem discreteTwoOfContinuous_mem_cocycles₂
    (z : Cycle (continuousCoefficients p) 2 3) :
    discreteTwoOfContinuous p z ∈
      groupCohomology.cocycles₂ (coefficients p) := by
  rw [groupCohomology.mem_cocycles₂_def]
  intro g h k
  have hzval := congrArg Cochain.val z.isCycle
  rw [differential_val] at hzval
  have hz := continuousTwoCycle_identity p z.cochain.val hzval
    1 g (g * h) ((g * h) * k)
  have hinv := twoValue_invariant p z.cochain.val g g (g * h) ((g * h) * k)
  rw [show g⁻¹ * ((g * h) * k) = h * k by group] at hinv
  have hinv' : twoValue z.cochain.val 1 h (h * k) =
      twoValue z.cochain.val g (g * h) ((g * h) * k) := by
    simpa [trivialAction_action] using hinv
  change
    discreteTwoOfContinuous p z (h, k) -
      discreteTwoOfContinuous p z (g * h, k) +
      discreteTwoOfContinuous p z (g, h * k) -
      discreteTwoOfContinuous p z (g, h) = 0
  change
    twoValue z.cochain.val 1 h (h * k) -
      twoValue z.cochain.val 1 (g * h) ((g * h) * k) +
      twoValue z.cochain.val 1 g (g * (h * k)) -
      twoValue z.cochain.val 1 g (g * h) = 0
  rw [hinv']
  rw [show g * (h * k) = (g * h) * k by group]
  calc
    twoValue z.cochain.val g (g * h) ((g * h) * k) -
          twoValue z.cochain.val 1 (g * h) ((g * h) * k) +
          twoValue z.cochain.val 1 g ((g * h) * k) -
          twoValue z.cochain.val 1 g (g * h) =
        twoValue z.cochain.val g (g * h) ((g * h) * k) -
          (twoValue z.cochain.val 1 (g * h) ((g * h) * k) -
            (twoValue z.cochain.val 1 g ((g * h) * k) -
              twoValue z.cochain.val 1 g (g * h))) := by abel
    _ = 0 := hz

def discreteCocycleOfContinuous
    (z : Cycle (continuousCoefficients p) 2 3) :
    groupCohomology.cocycles₂ (coefficients p) :=
  ⟨discreteTwoOfContinuous p z, discreteTwoOfContinuous_mem_cocycles₂ p z⟩

theorem continuousCycleOfDiscrete_discreteCocycleOfContinuous
    (z : Cycle (continuousCoefficients p) 2 3) :
    continuousCycleOfDiscrete (discreteCocycleOfContinuous p z) = z := by
  apply Cycle.ext
  apply Cochain.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  apply ContinuousMap.ext
  intro w
  change twoValue z.cochain.val 1 (x⁻¹ * y)
      ((x⁻¹ * y) * (y⁻¹ * w)) = twoValue z.cochain.val x y w
  have hinv := twoValue_invariant p z.cochain.val x x y w
  have hinv' : twoValue z.cochain.val 1 (x⁻¹ * y) (x⁻¹ * w) =
      twoValue z.cochain.val x y w := by
    simpa [trivialAction_action] using hinv
  rw [show (x⁻¹ * y) * (y⁻¹ * w) = x⁻¹ * w by group]
  exact hinv'

private def rawHomogeneousOne
    (b : CyclicGroup p → coefficients p) :
    C(CyclicGroup p, C(CyclicGroup p, ZMod p)) :=
  ⟨fun x ↦
    ⟨fun y ↦ b (x⁻¹ * y), continuous_of_discreteTopology⟩,
    continuous_of_discreteTopology⟩

private def homogeneousOneOfDiscrete
    (b : CyclicGroup p → coefficients p) :
    ((homogeneousCochains (ZMod p) (CyclicGroup p)).obj
      (continuousCoefficients p)).X 1 := by
  refine ⟨rawHomogeneousOne p b, ?_⟩
  intro a
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  change b ((a⁻¹ * x)⁻¹ * (a⁻¹ * y)) = b (x⁻¹ * y)
  congr 1
  group

private def continuousOneOfDiscrete
    (b : CyclicGroup p → coefficients p) :
    Cochain (continuousCoefficients p) 1 :=
  ⟨homogeneousOneOfDiscrete p b⟩

private theorem differential_continuousOneOfDiscrete_apply
    (b : CyclicGroup p → coefficients p) (x y z : CyclicGroup p) :
    twoValue (differential (continuousCoefficients p) 1 2
      (continuousOneOfDiscrete p b)).val x y z =
      (groupCohomology.d₁₂ (coefficients p)).hom b
        (x⁻¹ * y, y⁻¹ * z) := by
  rw [differential_val, continuousOneDifferential_apply]
  simp only [groupCohomology.d₁₂_hom_apply]
  change b (y⁻¹ * z) - (b (x⁻¹ * z) - b (x⁻¹ * y)) =
    b (y⁻¹ * z) - b ((x⁻¹ * y) * (y⁻¹ * z)) + b (x⁻¹ * y)
  rw [show (x⁻¹ * y) * (y⁻¹ * z) = x⁻¹ * z by group]
  abel

theorem continuousBoundary_of_mem_discreteCoboundaries
    (c : groupCohomology.cocycles₂ (coefficients p))
    (hc : ⇑c ∈ groupCohomology.coboundaries₂ (coefficients p)) :
    ∃ b : Cochain (continuousCoefficients p) 1,
      differential (continuousCoefficients p) 1 2 b =
        cycleCochain (continuousCoefficients p) 2 3
          (continuousCycleOfDiscrete c) := by
  obtain ⟨b, hb⟩ := hc
  refine ⟨continuousOneOfDiscrete p b, ?_⟩
  apply Cochain.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  apply ContinuousMap.ext
  intro z
  change twoValue (differential (continuousCoefficients p) 1 2
      (continuousOneOfDiscrete p b)).val x y z =
    twoValue (cycleCochain (continuousCoefficients p) 2 3
      (continuousCycleOfDiscrete c)).val x y z
  rw [differential_continuousOneOfDiscrete_apply]
  change (groupCohomology.d₁₂ (coefficients p)).hom b
      (x⁻¹ * y, y⁻¹ * z) = c (x⁻¹ * y, y⁻¹ * z)
  exact congrFun hb (x⁻¹ * y, y⁻¹ * z)

def continuousCycleOfDiscreteLinear :
    groupCohomology.cocycles₂ (coefficients p) →ₗ[ZMod p]
      Cycle (continuousCoefficients p) 2 3 where
  toFun := continuousCycleOfDiscrete
  map_add' c d := by
    apply Cycle.ext
    apply Cochain.ext
    rfl
  map_smul' a c := by
    apply Cycle.ext
    apply Cochain.ext
    rfl

theorem discreteCarryH2Class_ne_zero :
    (groupCohomology.H2π (coefficients p)).hom (carryCocycle p) ≠ 0 := by
  intro hzero
  exact carryCocycle_not_mem_coboundaries₂ p
    ((groupCohomology.H2π_eq_zero_iff (carryCocycle p)).mp hzero)

theorem discreteCarryH2Class_spans
    (x : groupCohomology (coefficients p) 2) :
    ∃ a : ZMod p,
      a • (groupCohomology.H2π (coefficients p)).hom (carryCocycle p) = x := by
  obtain ⟨u, hu⟩ := finiteCyclicH2Class_spans p
    ((groupCohomology.H2π (coefficients p)).hom (carryCocycle p))
  have hu0 : u ≠ 0 := by
    intro hzero
    apply discreteCarryH2Class_ne_zero p
    rw [← hu, hzero, zero_smul]
  obtain ⟨v, hv⟩ := finiteCyclicH2Class_spans p x
  refine ⟨v * u⁻¹, ?_⟩
  rw [← hu, ← hv]
  simp [smul_smul, hu0]

theorem continuousCarryCycle_spans_h2Projection
    (z : Cycle (continuousCoefficients p) 2 3) :
    ∃ a : ZMod p,
      a • h2Projection (continuousCoefficients p) (continuousCarryCycle p) =
        h2Projection (continuousCoefficients p) z := by
  let c := discreteCocycleOfContinuous p z
  obtain ⟨a, ha⟩ := discreteCarryH2Class_spans p
    ((groupCohomology.H2π (coefficients p)).hom c)
  have heq :
      (groupCohomology.H2π (coefficients p)).hom c =
        (groupCohomology.H2π (coefficients p)).hom (a • carryCocycle p) := by
    simpa using ha.symm
  have hcoboundary :
      ⇑(c - a • carryCocycle p) ∈
        groupCohomology.coboundaries₂ (coefficients p) := by
    exact (groupCohomology.H2π_eq_iff c (a • carryCocycle p)).mp heq
  obtain ⟨b, hb⟩ := continuousBoundary_of_mem_discreteCoboundaries p
    (c - a • carryCocycle p) hcoboundary
  have hzero :
      h2Projection (continuousCoefficients p)
        (continuousCycleOfDiscreteLinear p (c - a • carryCocycle p)) = 0 := by
    apply (h2Projection_eq_zero_iff (continuousCoefficients p) _).mpr
    exact ⟨b, hb⟩
  have hrecover : continuousCycleOfDiscreteLinear p c = z :=
    continuousCycleOfDiscrete_discreteCocycleOfContinuous p z
  rw [map_sub, map_smul, hrecover] at hzero
  change h2Projection (continuousCoefficients p)
      (z - a • continuousCarryCycle p) = 0 at hzero
  rw [map_sub, map_smul] at hzero
  exact ⟨a, (sub_eq_zero.mp hzero).symm⟩

theorem continuousCarryH2Class_spans
    (x : (continuousCohomology (ZMod p) (CyclicGroup p) 2).obj
      (continuousCoefficients p)) :
    ∃ a : ZMod p, a • continuousCarryH2Class p = x := by
  let e := homologyLinearEquiv (continuousCoefficients p) 2
  obtain ⟨z, hz⟩ := h2Projection_surjective p (e.symm x)
  obtain ⟨a, ha⟩ := continuousCarryCycle_spans_h2Projection p z
  refine ⟨a, ?_⟩
  change a • e (h2Projection (continuousCoefficients p) (continuousCarryCycle p)) = x
  rw [← e.map_smul, ha, hz]
  exact e.apply_symm_apply x

theorem actualContinuousCyclicH2Readout_injective :
    Function.Injective (actualContinuousCyclicH2Readout p) := by
  intro x y hxy
  obtain ⟨a, ha⟩ := continuousCarryH2Class_spans p x
  obtain ⟨b, hb⟩ := continuousCarryH2Class_spans p y
  have hab : a = b := by
    rw [← ha, ← hb] at hxy
    simpa using hxy
  rw [← ha, ← hb, hab]

theorem actualContinuousCyclicH2Readout_bijective :
    Function.Bijective (actualContinuousCyclicH2Readout p) :=
  ⟨actualContinuousCyclicH2Readout_injective p,
    actualContinuousCyclicH2Readout_surjective p⟩

/-- For every prime `p`, generator-loop normalization identifies the actual
continuous `H²(C_p, F_p)` with its coefficient field. -/
noncomputable def actualContinuousCyclicH2LinearEquiv :
    (continuousCohomology (ZMod p) (CyclicGroup p) 2).obj
        (continuousCoefficients p) ≃ₗ[ZMod p] ZMod p :=
  LinearEquiv.ofBijective (actualContinuousCyclicH2Readout p)
    (actualContinuousCyclicH2Readout_bijective p)

@[simp]
theorem actualContinuousCyclicH2LinearEquiv_apply
    (x : (continuousCohomology (ZMod p) (CyclicGroup p) 2).obj
      (continuousCoefficients p)) :
    actualContinuousCyclicH2LinearEquiv p x =
      actualContinuousCyclicH2Readout p x :=
  rfl

@[simp]
theorem actualContinuousCyclicH2LinearEquiv_symm_apply
    (a : ZMod p) :
    (actualContinuousCyclicH2LinearEquiv p).symm a =
      actualContinuousCyclicH2Generator p a := by
  apply actualContinuousCyclicH2Readout_injective p
  simp [actualContinuousCyclicH2LinearEquiv]
end Fermat.Conservation.PrimeCyclicH2
