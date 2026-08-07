/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable
-/

import Fermat.Conservation.SelmerSequence

/-!
# The principal-ideal two-term complex and its power-root extension

The principal-ideal arrow

`Kˣ → (FractionalIdeal R⁰ K)ˣ`

is presented as a two-term complex.  Its degree-one homotopy is the kernel,
canonically identified with `Rˣ`, and its degree-zero homotopy is the
cokernel, canonically identified with `ClassGroup R`.

At a positive power `n`, the PowerRoot obstruction sequence has unit power
classes on the left, class-group `n`-torsion on the right, and the empty-
support Selmer group as its middle.  The named extension-class record below
retains exactly the two maps and their exactness data.  It intentionally has
no splitting, section, retraction, or equivalence-to-a-product field: the
Selmer middle carries the extension data without a chosen decomposition.
-/

open scoped nonZeroDivisors

noncomputable section

namespace Fermat.Conservation.PowerRootExactSequence

universe uA uB uR uK uU uM uC

/-- A two-term complex in commutative groups, presented by its only arrow. -/
structure TwoTermComplex (A : Type uA) (B : Type uB)
    [CommGroup A] [CommGroup B] where
  arrow : A →* B

namespace TwoTermComplex

/-- Degree-one homotopy of a two-term arrow: retained morphisms. -/
abbrev PiOne {A : Type uA} {B : Type uB} [CommGroup A] [CommGroup B]
    (C : TwoTermComplex A B) := C.arrow.ker

/-- Degree-zero homotopy of a two-term arrow: component classes. -/
abbrev PiZero {A : Type uA} {B : Type uB} [CommGroup A] [CommGroup B]
    (C : TwoTermComplex A B) := B ⧸ C.arrow.range

end TwoTermComplex

section PrincipalIdealArrow

variable {R : Type uR} [CommRing R] [IsDedekindDomain R]
  {K : Type uK} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The actual principal fractional-ideal arrow used by the PowerRoot square. -/
abbrev principalIdealArrow : Kˣ →* (FractionalIdeal R⁰ K)ˣ :=
  toPrincipalIdeal R K

/-- The principal-ideal arrow as a two-term complex. -/
def principalIdealComplex : TwoTermComplex Kˣ (FractionalIdeal R⁰ K)ˣ where
  arrow := principalIdealArrow (R := R) (K := K)

/-- The retained degree-one morphisms of the principal-ideal arrow. -/
abbrev PrincipalIdealPiOne :=
  TwoTermComplex.PiOne (principalIdealComplex (R := R) (K := K))

/-- The degree-zero component shadow of the principal-ideal arrow. -/
abbrev PrincipalIdealPiZero :=
  TwoTermComplex.PiZero (principalIdealComplex (R := R) (K := K))

/-- The exact height-one-prime geometry used by the arithmetic obstruction
map, exposed for naturality squares. -/
abbrev principalIdealFactorization :
    PowerRoot.Factorization (FractionalIdeal R⁰ K)ˣ
      (IsDedekindDomain.HeightOneSpectrum R) :=
  IsDedekindDomain.selmerGroup.fractionalIdealFactorization
    (R := R) (K := K)

/-- Integral units map canonically to the retained morphisms of the
principal-ideal arrow. -/
def unitsToPiOne : Rˣ →* PrincipalIdealPiOne (R := R) (K := K) where
  toFun u := ⟨Units.map (algebraMap R K : R →* K) u, by
    change toPrincipalIdeal R K (Units.map (algebraMap R K : R →* K) u) = 1
    apply Units.ext
    rw [coe_toPrincipalIdeal, Units.val_one, ← FractionalIdeal.spanSingleton_one,
      FractionalIdeal.spanSingleton_eq_spanSingleton]
    exact ⟨u⁻¹, by simp [Units.smul_def, Algebra.smul_def]⟩⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

private theorem unitsToPiOne_surjective :
    Function.Surjective (unitsToPiOne (R := R) (K := K)) := by
  intro x
  have hxproperty := x.property
  change toPrincipalIdeal R K (x : Kˣ) = 1 at hxproperty
  have hspan : FractionalIdeal.spanSingleton R⁰ ((x : Kˣ) : K) =
      FractionalIdeal.spanSingleton R⁰ (1 : K) := by
    rw [FractionalIdeal.spanSingleton_one]
    simpa only [coe_toPrincipalIdeal, Units.val_one] using congr_arg Units.val hxproperty
  obtain ⟨u, hu⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hspan
  refine ⟨u⁻¹, Subtype.ext ?_⟩
  change Units.map (algebraMap R K : R →* K) u⁻¹ = (x : Kˣ)
  rw [show Units.map (algebraMap R K : R →* K) u⁻¹ =
      (Units.map (algebraMap R K : R →* K) u)⁻¹ by simp]
  apply Units.ext
  apply Units.inv_eq_of_mul_eq_one_right
  rw [Units.coe_map]
  change (algebraMap R K) (u : R) * ((x : Kˣ) : K) = 1
  simpa only [Units.smul_def, Algebra.smul_def] using hu

private theorem unitsToPiOne_injective :
    Function.Injective (unitsToPiOne (R := R) (K := K)) := by
  intro u v huv
  apply Units.map_injective (FaithfulSMul.algebraMap_injective R K)
  exact congr_arg Subtype.val huv

/-- Degree-one homotopy is canonically the unit group. -/
def unitsEquivPiOne : Rˣ ≃* PrincipalIdealPiOne (R := R) (K := K) :=
  MulEquiv.ofBijective (unitsToPiOne (R := R) (K := K))
    ⟨unitsToPiOne_injective (R := R) (K := K),
      unitsToPiOne_surjective (R := R) (K := K)⟩

/-- The inverse orientation of `unitsEquivPiOne`. -/
def piOneEquivUnits : PrincipalIdealPiOne (R := R) (K := K) ≃* Rˣ :=
  (unitsEquivPiOne (R := R) (K := K)).symm

/-- Degree-zero homotopy is canonically the ideal class group. -/
def piZeroEquivClassGroup :
    PrincipalIdealPiZero (R := R) (K := K) ≃* ClassGroup R :=
  (ClassGroup.equiv K).symm

end PrincipalIdealArrow

/-! ## The power layer and its unsplit Selmer middle -/

/-- Unit classes modulo `n`-th powers: the power-layer degree-one term. -/
abbrev UnitPowerClasses (R : Type uR) [CommRing R] (n : ℕ) :=
  Rˣ ⧸ PowerRoot.powerSubgroup Rˣ n

/-- The `n`-torsion in the class group: the power-layer degree-zero term. -/
abbrev ClassPowerTorsion (R : Type uR) [CommRing R] [IsDedekindDomain R]
    (n : ℕ) :=
  (powMonoidHom n : ClassGroup R →* ClassGroup R).ker

/-- The empty-support Selmer group, retained as the middle extension object. -/
abbrev SelmerMiddle (R : Type uR) (K : Type uK)
    [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (n : ℕ) :=
  IsDedekindDomain.selmerGroup
    (R := R) (K := K)
    (S := (∅ : Set (IsDedekindDomain.HeightOneSpectrum R))) (n := n)

section PowerLayer

variable {R : Type uR} [CommRing R] [IsDedekindDomain R]
  {K : Type uK} [Field K] [Algebra R K] [IsFractionRing R K]
  {n : ℕ} [Fact (0 < n)]

/-- The retained unit receipt in the Selmer middle. -/
def unitReceipt : UnitPowerClasses R n →* SelmerMiddle R K n :=
  IsDedekindDomain.selmerGroup.fromUnitLift
    (R := R) (K := K) (n := n)

/-- The component shadow of a Selmer class, restricted to class-group
`n`-torsion. -/
def componentShadow : SelmerMiddle R K n →* ClassPowerTorsion R n :=
  (IsDedekindDomain.selmerGroup.toClass
    (R := R) (K := K) (n := n)).codRestrict
      (ClassPowerTorsion R n) fun s => by
        change IsDedekindDomain.selmerGroup.toClass
          (R := R) (K := K) (n := n) s ∈
            (powMonoidHom n : ClassGroup R →* ClassGroup R).ker
        rw [← IsDedekindDomain.selmerGroup.toClass_range
          (R := R) (K := K) (n := n)]
        exact ⟨s, rfl⟩

/-- Exact extension data with no chosen splitting.  In particular this
record cannot silently turn its middle into a product. -/
structure UnsplitExtensionClass (U : Type uU) (M : Type uM) (C : Type uC)
    [CommGroup U] [CommGroup M] [CommGroup C] where
  inclusion : U →* M
  projection : M →* C
  inclusion_injective : Function.Injective inclusion
  exact_middle : projection.ker = inclusion.range
  projection_surjective : Function.Surjective projection

/-- The named extension class carried by the principal-ideal PowerRoot
sequence.  No splitting datum is selected or consumed. -/
def principalIdealExtensionClass :
    UnsplitExtensionClass (UnitPowerClasses R n) (SelmerMiddle R K n)
      (ClassPowerTorsion R n) where
  inclusion := unitReceipt (R := R) (K := K) (n := n)
  projection := componentShadow (R := R) (K := K) (n := n)
  inclusion_injective :=
    IsDedekindDomain.selmerGroup.fromUnitLift_injective
      (R := R) (K := K) (n := n)
  exact_middle := by
    change (componentShadow (R := R) (K := K) (n := n)).ker =
      (IsDedekindDomain.selmerGroup.fromUnitLift
        (R := R) (K := K) (n := n)).range
    rw [← IsDedekindDomain.selmerGroup.toClass_ker
      (R := R) (K := K) (n := n)]
    ext s
    simp [componentShadow]
  projection_surjective := by
    intro c
    have hc : (c : ClassGroup R) ∈
        (powMonoidHom n : ClassGroup R →* ClassGroup R).ker := c.property
    rw [← IsDedekindDomain.selmerGroup.toClass_range
      (R := R) (K := K) (n := n)] at hc
    obtain ⟨s, hs⟩ := hc
    exact ⟨s, Subtype.ext hs⟩

/-- The unit receipt is injective. -/
theorem unitReceipt_injective :
    Function.Injective (unitReceipt (R := R) (K := K) (n := n)) :=
  (principalIdealExtensionClass (R := R) (K := K) (n := n)).inclusion_injective

/-- Exactness at the unsplit Selmer middle. -/
theorem componentShadow_ker :
    (componentShadow (R := R) (K := K) (n := n)).ker =
      (unitReceipt (R := R) (K := K) (n := n)).range :=
  (principalIdealExtensionClass (R := R) (K := K) (n := n)).exact_middle

/-- Every class-group `n`-torsion component is the shadow of a Selmer
class. -/
theorem componentShadow_surjective :
    Function.Surjective (componentShadow (R := R) (K := K) (n := n)) :=
  (principalIdealExtensionClass (R := R) (K := K) (n := n)).projection_surjective

/-- The two exact maps compose trivially, so they form the power-layer
complex. -/
@[simp]
theorem componentShadow_unitReceipt (u : UnitPowerClasses R n) :
    componentShadow (R := R) (K := K) (n := n)
        (unitReceipt (R := R) (K := K) (n := n) u) = 1 := by
  apply MonoidHom.mem_ker.mp
  rw [componentShadow_ker (R := R) (K := K) (n := n)]
  exact ⟨u, rfl⟩

end PowerLayer

end Fermat.Conservation.PowerRootExactSequence
