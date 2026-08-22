/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# A generator for one discrete finite-cyclic H²

This file computes degree-two *discrete* group cohomology for the cyclic
group `Multiplicative (ZMod 59)` with trivial `ZMod 59` coefficients.  The
finite-cyclic resolution identifies the class of the invariant element `1`;
the norm is zero in characteristic `59`, so this class is nonzero and spans
the cohomology group.  Consequently this particular discrete `H²` is
linearly equivalent to `ZMod 59`.

This is not a continuous-cohomology comparison, an inflation theorem for an
absolute Galois group, a local invariant, or a local fundamental class.
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic

noncomputable section

open CategoryTheory

namespace Fermat.Conservation.FiniteCyclicH2Generator59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

/-- The multiplicative presentation of the cyclic additive group `ZMod 59`. -/
abbrev CyclicGroup59 := Multiplicative (ZMod 59)

/-- The trivial discrete `ZMod 59` representation of `CyclicGroup59`. -/
abbrev coefficients59 : Rep (ZMod 59) CyclicGroup59 :=
  Rep.trivial (ZMod 59) CyclicGroup59 (ZMod 59)

/-- The element corresponding to `1 : ZMod 59`. -/
def generator59 : CyclicGroup59 := Multiplicative.ofAdd 1

lemma cyclicGroup59_card : Nat.card CyclicGroup59 = 59 := by
  simp [CyclicGroup59]

lemma generator59_ne_one : generator59 ≠ 1 := by
  change Multiplicative.ofAdd (1 : ZMod 59) ≠ Multiplicative.ofAdd 0
  simp

/-- `generator59` generates the finite cyclic group. -/
lemma generator59_generates (x : CyclicGroup59) :
    x ∈ Subgroup.zpowers generator59 :=
  mem_zpowers_of_prime_card cyclicGroup59_card generator59_ne_one

/-- The invariant coefficient `1`, seated in the kernel required by the
finite-cyclic even-degree quotient map. -/
def invariantOne59 :
    LinearMap.ker
      (coefficients59.applyAsHom generator59 - 𝟙 coefficients59).hom.toLinearMap :=
  ⟨1, by
    change (1 : ZMod 59) - 1 = 0
    simp⟩

set_option maxRecDepth 10000 in
/-- The norm on the trivial `ZMod 59` line is zero: it is the sum of `59`
copies of its input in characteristic `59`. -/
lemma coefficients59_norm_eq_zero :
    coefficients59.norm.hom.toLinearMap = 0 := by
  apply LinearMap.ext
  intro x
  change (∑ _g : CyclicGroup59, x) = 0
  rw [Finset.sum_const, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card, cyclicGroup59_card]
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

/-- The finite-cyclic quotient class represented by the invariant element
`1`.  Its target is ordinary discrete group cohomology. -/
def finiteCyclicH2Class59 : groupCohomology coefficients59 2 :=
  Rep.FiniteCyclicGroup.groupCohomologyπEven
    coefficients59 generator59 generator59_generates 2
      (by exact ⟨1, rfl⟩) invariantOne59

set_option maxRecDepth 10000 in
/-- The distinguished discrete finite-cyclic `H²` class is nonzero. -/
theorem finiteCyclicH2Class59_ne_zero : finiteCyclicH2Class59 ≠ 0 := by
  intro hzero
  have hrange :
      (1 : ZMod 59) ∈ LinearMap.range coefficients59.norm.hom.toLinearMap :=
    (Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff
      coefficients59 generator59 generator59_generates 2
        (by exact ⟨1, rfl⟩) invariantOne59).mp hzero
  rw [coefficients59_norm_eq_zero] at hrange
  simp at hrange

/-- A concrete existence receipt at the cocycle level: some ordinary
discrete two-cocycle for `CyclicGroup59` is not a two-coboundary.  This is
obtained by lifting the nonzero finite-cyclic `H²` class through the
surjective low-degree quotient map. -/
theorem exists_twoCocycle_not_mem_coboundaries59 :
    ∃ c : groupCohomology.cocycles₂ coefficients59,
      ⇑c ∉ groupCohomology.coboundaries₂ coefficients59 := by
  have hsurj : Function.Surjective
      (groupCohomology.H2π coefficients59).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨c, hc⟩ := hsurj finiteCyclicH2Class59
  refine ⟨c, ?_⟩
  intro hcoboundary
  apply finiteCyclicH2Class59_ne_zero
  rw [← hc]
  exact (groupCohomology.H2π_eq_zero_iff (A := coefficients59) c).mpr
    hcoboundary

/-- Every class in this discrete finite-cyclic `H²` is a scalar multiple
of `finiteCyclicH2Class59`. -/
theorem finiteCyclicH2Class59_spans
    (x : groupCohomology coefficients59 2) :
    ∃ a : ZMod 59, a • finiteCyclicH2Class59 = x := by
  have hsurj : Function.Surjective
      (Rep.FiniteCyclicGroup.groupCohomologyπEven
        coefficients59 generator59 generator59_generates 2
          (by exact ⟨1, rfl⟩)).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨y, rfl⟩ := hsurj x
  refine ⟨y.1, ?_⟩
  change y.1 •
      (Rep.FiniteCyclicGroup.groupCohomologyπEven
        coefficients59 generator59 generator59_generates 2
          (by exact ⟨1, rfl⟩)).hom invariantOne59 = _
  rw [← map_smul]
  congr 1
  apply Subtype.ext
  simp [invariantOne59]

/-- Send a scalar to its multiple of the distinguished discrete class. -/
def finiteCyclicH2GeneratorMap59 :
    ZMod 59 →ₗ[ZMod 59] groupCohomology coefficients59 2 where
  toFun a := a • finiteCyclicH2Class59
  map_add' a b := add_smul a b finiteCyclicH2Class59
  map_smul' a b := by simp [mul_smul]

theorem finiteCyclicH2GeneratorMap59_bijective :
    Function.Bijective finiteCyclicH2GeneratorMap59 := by
  constructor
  · intro a b hab
    change a • finiteCyclicH2Class59 = b • finiteCyclicH2Class59 at hab
    exact smul_left_injective (ZMod 59) finiteCyclicH2Class59_ne_zero hab
  · intro x
    obtain ⟨a, rfl⟩ := finiteCyclicH2Class59_spans x
    exact ⟨a, rfl⟩

/-- The generator coordinates identify `ZMod 59` with this discrete
finite-cyclic degree-two cohomology group. -/
def finiteCyclicH2LinearEquiv59 :
    ZMod 59 ≃ₗ[ZMod 59] groupCohomology coefficients59 2 :=
  LinearEquiv.ofBijective finiteCyclicH2GeneratorMap59
    finiteCyclicH2GeneratorMap59_bijective

/-- The inverse coordinate map, from the discrete finite-cyclic `H²` to
`ZMod 59`. -/
def finiteCyclicH2ReadoutEquiv59 :
    groupCohomology coefficients59 2 ≃ₗ[ZMod 59] ZMod 59 :=
  finiteCyclicH2LinearEquiv59.symm

@[simp]
theorem finiteCyclicH2ReadoutEquiv59_class :
    finiteCyclicH2ReadoutEquiv59 finiteCyclicH2Class59 = 1 := by
  change finiteCyclicH2LinearEquiv59.symm finiteCyclicH2Class59 = 1
  rw [← one_smul (ZMod 59) finiteCyclicH2Class59]
  change finiteCyclicH2LinearEquiv59.symm
    (finiteCyclicH2LinearEquiv59 1) = 1
  simp

end Fermat.Conservation.FiniteCyclicH2Generator59
