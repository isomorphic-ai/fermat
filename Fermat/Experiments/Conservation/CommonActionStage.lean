/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# The common arithmetic action stage

This module seats the linking algebra on the paired Selmer carrier as far as
the available arithmetic permits.  The units--Selmer map is Mathlib's actual
Kummer map, and the vendored unit--Selmer--class sequence supplies its class
projection, middle exactness, and surjectivity onto class-group `p`-torsion.
Two supplied filtered exact legs assemble into a genuine product exact
sequence with a decreasing filtration.

The reflected leg is a dual leg, not a second copy identified by swapping.
Route and return maps are therefore distinct.  Only their closed composites
are endomorphisms.  Integral Stickelberger data is retained as conversion
into the units range with its beta receipt; no Selmer-level annihilation is
invented.  The final outcome type admits the unit-ideal, surviving-channel,
and localized-representation-wall results.
-/
import Fermat.Experiments.Conservation.KummerDrain
import Fermat.Experiments.Conservation.LinkingInterfaces
import Fermat.Experiments.Conservation.CommonActionSelmerCore
import Fermat.Experiments.Conservation.SelmerSequence
import Fermat.Experiments.Conservation.SwapQuotient
import Fermat.Experiments.Conservation.TransverseAnnihilator
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.Tactic

open scoped nonZeroDivisors NumberField

noncomputable section

namespace Fermat.Conservation.CommonActionStage

open Fermat.Conservation.LinkingInterfaces

universe uR uK uLambda uUChi uSChi uCChi uUDual uSDual uCDual
  uUStar uSStar uCStar uDelta uBeta uG uO uChi uDual uA uM uGauge

section RealUnitKummerMap

variable {K : Type uK} [Field K] [NumberField K]
  [NumberField.IsCMField K]
  {p : ℕ} [Fact (0 < p)]

/-- The campaign's real-unit subgroup mapped into units modulo `p`th powers.
This is the concrete bridge from the real-units machinery to the Kummer
exact sequence, not a separately postulated unit map. -/
def realUnitClass :
    Additive (NumberField.IsCMField.realUnits K) →+
      UnitModP (NumberField.RingOfIntegers K) p :=
  MonoidHom.toAdditive <|
    (QuotientGroup.mk'
      (powMonoidHom p :
        (NumberField.RingOfIntegers K)ˣ →*
          (NumberField.RingOfIntegers K)ˣ).range).comp
      (NumberField.IsCMField.realUnits K).subtype

/-- Real units enter the actual Selmer group through Mathlib's injective
units leg. -/
def realUnitInclusion :
    Additive (NumberField.IsCMField.realUnits K) →+
      Selmer (NumberField.RingOfIntegers K) K p :=
  (unitInclusion
    (R := NumberField.RingOfIntegers K) (K := K) (p := p)).comp
      (realUnitClass (K := K) (p := p))

end RealUnitKummerMap

/-! ## A filtered exact leg and its paired product -/

/-- One filtered units--Selmer--class leg, with a decreasing filtration. -/
structure ExactFilteredLeg (p : ℕ) (Lambda : Type uLambda)
    (U : Type uUChi) (S : Type uSChi) (ClassP : Type uCChi)
    [CommRing Lambda] [AddCommGroup U] [Module Lambda U]
    [AddCommGroup S] [Module Lambda S]
    [AddCommGroup ClassP] [Module Lambda ClassP] where
  unitInclusion : U →ₗ[Lambda] S
  classProjection : S →ₗ[Lambda] ClassP
  unitInclusion_injective : Function.Injective unitInclusion
  exact_at_carrier :
    LinearMap.range unitInclusion = LinearMap.ker classProjection
  classProjection_surjective : Function.Surjective classProjection
  class_p_torsion : ∀ c : ClassP, p • c = 0
  filtration : ℕ → Submodule Lambda S
  antitone_filtration : Antitone filtration

/-- Arithmetic realization of a reflected leg as an actual character dual.
The three additive equivalences retain the dual objects, while the displayed
action law records the omega/sharp twist explicitly.  The two arrow laws say
that the reflected exact sequence is contravariant: its inclusion is dual to
the primal class projection and its projection is dual to the primal unit
inclusion. -/
structure ReflectedDualRealization (p : ℕ) (Lambda : Type uLambda)
    (UStar : Type uUStar) (SelmerChiStar : Type uSStar)
    (ClassStar : Type uCStar) (UDual : Type uUDual)
    (DOmegaSelmerChiStar : Type uSDual) (ClassDual : Type uCDual)
    [CommRing Lambda]
    [AddCommGroup UStar] [Module Lambda UStar]
    [AddCommGroup SelmerChiStar] [Module Lambda SelmerChiStar]
    [AddCommGroup ClassStar] [Module Lambda ClassStar]
    [AddCommGroup UDual] [Module Lambda UDual]
    [AddCommGroup DOmegaSelmerChiStar]
    [Module Lambda DOmegaSelmerChiStar]
    [AddCommGroup ClassDual] [Module Lambda ClassDual]
    (chiStar : ExactFilteredLeg p Lambda UStar SelmerChiStar ClassStar)
    (reflectedDual : ExactFilteredLeg p Lambda UDual
      DOmegaSelmerChiStar ClassDual)
    (sharp : Lambda ≃+* Lambda) where
  unitDualEquiv : UDual ≃+ SelmerCharacterDual ClassStar
  carrierDualEquiv : DOmegaSelmerChiStar ≃+ SelmerCharacterDual SelmerChiStar
  classDualEquiv : ClassDual ≃+ SelmerCharacterDual UStar
  omegaTwistedAction : ∀ a d,
    carrierDualEquiv (a • d) =
      sharp a • carrierDualEquiv d
  unitInclusion_is_dual : ∀ u,
    carrierDualEquiv (reflectedDual.unitInclusion u) =
      CharacterModule.dual chiStar.classProjection (unitDualEquiv u)
  classProjection_is_dual : ∀ d,
    classDualEquiv (reflectedDual.classProjection d) =
      CharacterModule.dual chiStar.unitInclusion (carrierDualEquiv d)

/-- The requested paired carrier.  Its second component is named and typed
as the reflected dual leg; there is deliberately no swap equivalence field. -/
structure ExactFilteredPair (p : ℕ) (Lambda : Type uLambda)
    (UChi : Type uUChi) (SelmerChi : Type uSChi)
    (ClassChi : Type uCChi) (UDual : Type uUDual)
    (DOmegaSelmerChiStar : Type uSDual) (ClassDual : Type uCDual)
    [CommRing Lambda]
    [AddCommGroup UChi] [Module Lambda UChi]
    [AddCommGroup SelmerChi] [Module Lambda SelmerChi]
    [AddCommGroup ClassChi] [Module Lambda ClassChi]
    [AddCommGroup UDual] [Module Lambda UDual]
    [AddCommGroup DOmegaSelmerChiStar] [Module Lambda DOmegaSelmerChiStar]
    [AddCommGroup ClassDual] [Module Lambda ClassDual] where
  chi : ExactFilteredLeg p Lambda UChi SelmerChi ClassChi
  reflectedDual :
    ExactFilteredLeg p Lambda UDual DOmegaSelmerChiStar ClassDual

/-- The paired carrier together with the separately realized primal
`chi*` sequence and its omega-twisted character dual.  This record, rather
than a swap equivalence, is the route-not-swap realization of the second
leg. -/
structure ReflectedExactFilteredPair (p : ℕ) (Lambda : Type uLambda)
    (UChi : Type uUChi) (SelmerChi : Type uSChi)
    (ClassChi : Type uCChi) (UStar : Type uUStar)
    (SelmerChiStar : Type uSStar) (ClassStar : Type uCStar)
    (UDual : Type uUDual) (DOmegaSelmerChiStar : Type uSDual)
    (ClassDual : Type uCDual)
    [CommRing Lambda]
    [AddCommGroup UChi] [Module Lambda UChi]
    [AddCommGroup SelmerChi] [Module Lambda SelmerChi]
    [AddCommGroup ClassChi] [Module Lambda ClassChi]
    [AddCommGroup UStar] [Module Lambda UStar]
    [AddCommGroup SelmerChiStar] [Module Lambda SelmerChiStar]
    [AddCommGroup ClassStar] [Module Lambda ClassStar]
    [AddCommGroup UDual] [Module Lambda UDual]
    [AddCommGroup DOmegaSelmerChiStar] [Module Lambda DOmegaSelmerChiStar]
    [AddCommGroup ClassDual] [Module Lambda ClassDual]
    (sharp : Lambda ≃+* Lambda) where
  pair : ExactFilteredPair p Lambda UChi SelmerChi ClassChi
    UDual DOmegaSelmerChiStar ClassDual
  chiStar : ExactFilteredLeg p Lambda UStar SelmerChiStar ClassStar
  dualRealization : ReflectedDualRealization p Lambda UStar SelmerChiStar
    ClassStar UDual DOmegaSelmerChiStar ClassDual chiStar
      pair.reflectedDual sharp

namespace ExactFilteredPair

variable {p : ℕ} {Lambda : Type uLambda}
  {UChi : Type uUChi} {SelmerChi : Type uSChi}
  {ClassChi : Type uCChi} {UDual : Type uUDual}
  {DOmegaSelmerChiStar : Type uSDual} {ClassDual : Type uCDual}
  [CommRing Lambda]
  [AddCommGroup UChi] [Module Lambda UChi]
  [AddCommGroup SelmerChi] [Module Lambda SelmerChi]
  [AddCommGroup ClassChi] [Module Lambda ClassChi]
  [AddCommGroup UDual] [Module Lambda UDual]
  [AddCommGroup DOmegaSelmerChiStar] [Module Lambda DOmegaSelmerChiStar]
  [AddCommGroup ClassDual] [Module Lambda ClassDual]

/-- `M = Sel_chi ⊕ D_omega Sel_chi*` in the finite paired realization. -/
abbrev Carrier := SelmerChi × DOmegaSelmerChiStar

/-- The componentwise units inclusion on the paired carrier. -/
def unitInclusion
    (pair : ExactFilteredPair p Lambda UChi SelmerChi ClassChi
      UDual DOmegaSelmerChiStar ClassDual) :
    (UChi × UDual) →ₗ[Lambda] (SelmerChi × DOmegaSelmerChiStar) :=
  pair.chi.unitInclusion.prodMap pair.reflectedDual.unitInclusion

/-- The componentwise class projection on the paired carrier. -/
def classProjection
    (pair : ExactFilteredPair p Lambda UChi SelmerChi ClassChi
      UDual DOmegaSelmerChiStar ClassDual) :
    (SelmerChi × DOmegaSelmerChiStar) →ₗ[Lambda]
      (ClassChi × ClassDual) :=
  pair.chi.classProjection.prodMap pair.reflectedDual.classProjection

/-- The paired units inclusion is injective because each actual leg is. -/
theorem unitInclusion_injective
    (pair : ExactFilteredPair p Lambda UChi SelmerChi ClassChi
      UDual DOmegaSelmerChiStar ClassDual) :
    Function.Injective pair.unitInclusion := by
  intro x y h
  apply Prod.ext
  · apply pair.chi.unitInclusion_injective
    exact congrArg Prod.fst h
  · apply pair.reflectedDual.unitInclusion_injective
    exact congrArg Prod.snd h

/-- Exactness of the paired sequence is derived componentwise. -/
theorem exact_at_carrier
    (pair : ExactFilteredPair p Lambda UChi SelmerChi ClassChi
      UDual DOmegaSelmerChiStar ClassDual) :
    LinearMap.range pair.unitInclusion = LinearMap.ker pair.classProjection := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    change
      (pair.chi.classProjection (pair.chi.unitInclusion u.1),
        pair.reflectedDual.classProjection
          (pair.reflectedDual.unitInclusion u.2)) = 0
    have hchi : pair.chi.unitInclusion u.1 ∈
        LinearMap.ker pair.chi.classProjection := by
      rw [← pair.chi.exact_at_carrier]
      exact ⟨u.1, rfl⟩
    have hdual : pair.reflectedDual.unitInclusion u.2 ∈
        LinearMap.ker pair.reflectedDual.classProjection := by
      rw [← pair.reflectedDual.exact_at_carrier]
      exact ⟨u.2, rfl⟩
    exact Prod.ext hchi hdual
  · intro hx
    change
      (pair.chi.classProjection x.1,
        pair.reflectedDual.classProjection x.2) = 0 at hx
    have hchi : x.1 ∈ LinearMap.ker pair.chi.classProjection :=
      congrArg Prod.fst hx
    have hdual : x.2 ∈ LinearMap.ker
        pair.reflectedDual.classProjection :=
      congrArg Prod.snd hx
    rw [← pair.chi.exact_at_carrier] at hchi
    rw [← pair.reflectedDual.exact_at_carrier] at hdual
    obtain ⟨u, hu⟩ := hchi
    obtain ⟨v, hv⟩ := hdual
    exact ⟨(u, v), Prod.ext hu hv⟩

/-- The paired class projection is surjective. -/
theorem classProjection_surjective
    (pair : ExactFilteredPair p Lambda UChi SelmerChi ClassChi
      UDual DOmegaSelmerChiStar ClassDual) :
    Function.Surjective pair.classProjection := by
  rintro ⟨c, d⟩
  obtain ⟨x, rfl⟩ := pair.chi.classProjection_surjective c
  obtain ⟨y, rfl⟩ := pair.reflectedDual.classProjection_surjective d
  exact ⟨(x, y), rfl⟩

/-- Choose a lift of a pair of class payloads through the actual paired
surjection. -/
noncomputable def liftClassPair
    (pair : ExactFilteredPair p Lambda UChi SelmerChi ClassChi
      UDual DOmegaSelmerChiStar ClassDual)
    (c : ClassChi × ClassDual) : SelmerChi × DOmegaSelmerChiStar :=
  Classical.choose (pair.classProjection_surjective c)

/-- The chosen obstruction lift projects back to the supplied class pair. -/
theorem classProjection_liftClassPair
    (pair : ExactFilteredPair p Lambda UChi SelmerChi ClassChi
      UDual DOmegaSelmerChiStar ClassDual)
    (c : ClassChi × ClassDual) :
    pair.classProjection (pair.liftClassPair c) = c :=
  Classical.choose_spec (pair.classProjection_surjective c)

/-- The paired decreasing filtration, formed componentwise. -/
def filtration
    (pair : ExactFilteredPair p Lambda UChi SelmerChi ClassChi
      UDual DOmegaSelmerChiStar ClassDual) (n : ℕ) :
    Submodule Lambda (SelmerChi × DOmegaSelmerChiStar) :=
  (pair.chi.filtration n).prod (pair.reflectedDual.filtration n)

/-- The product filtration remains decreasing. -/
theorem antitone_filtration
    (pair : ExactFilteredPair p Lambda UChi SelmerChi ClassChi
      UDual DOmegaSelmerChiStar ClassDual) :
    Antitone pair.filtration := by
  intro a b hab x hx
  exact ⟨pair.chi.antitone_filtration hab hx.1,
    pair.reflectedDual.antitone_filtration hab hx.2⟩

/-- Both class legs retain their `p`-torsion law. -/
theorem class_p_torsion
    (pair : ExactFilteredPair p Lambda UChi SelmerChi ClassChi
      UDual DOmegaSelmerChiStar ClassDual)
    (c : ClassChi × ClassDual) :
    p • c = 0 := by
  apply Prod.ext
  · exact pair.chi.class_p_torsion c.1
  · exact pair.reflectedDual.class_p_torsion c.2

end ExactFilteredPair

/-! ## Binding the filtered character legs to the actual Kummer sequence -/

/-- A character leg is not allowed to carry an unrelated map merely named
`unitInclusion`: the two squares below bind it to Mathlib's actual Kummer map
and to the class projection supplied by `SelmerClassSequenceRealization`.
The allocation maps are kept explicit because the campaign does not yet
construct the character projectors on Selmer. -/
structure KummerCharacterLegCompatibility
    {R : Type uR} [CommRing R] [IsDedekindDomain R]
    {K : Type uK} [Field K] [Algebra R K] [IsFractionRing R K]
    {p : ℕ} [Fact (0 < p)]
    {Lambda : Type uLambda} [CommRing Lambda]
    {U : Type uUChi} {S : Type uSChi} {ClassP : Type uCChi}
    [AddCommGroup U] [Module Lambda U]
    [AddCommGroup S] [Module Lambda S]
    [AddCommGroup ClassP] [Module Lambda ClassP]
    (sequence : SelmerClassSequenceRealization (R := R) (K := K) (p := p))
    (leg : ExactFilteredLeg p Lambda U S ClassP) where
  unitAllocation : UnitModP R p →+ U
  selmerAllocation : Selmer R K p →+ S
  classAllocation : ClassPTorsion R p →+ ClassP
  unit_square : ∀ u,
    leg.unitInclusion (unitAllocation u) =
      selmerAllocation
        (unitInclusion (R := R) (K := K) (p := p) u)
  class_square : ∀ s,
    leg.classProjection (selmerAllocation s) =
      classAllocation (sequence.classProjection s)

/-- Both primal character allocations are tied to one actual Kummer exact
sequence, and the second carrier leg is the separately realized reflected
dual of the `chi*` allocation. -/
structure KummerPairedBinding
    {R : Type uR} [CommRing R] [IsDedekindDomain R]
    {K : Type uK} [Field K] [Algebra R K] [IsFractionRing R K]
    {p : ℕ} [Fact (0 < p)]
    {Lambda : Type uLambda} [CommRing Lambda]
    {UChi : Type uUChi} {SelmerChi : Type uSChi}
    {ClassChi : Type uCChi} {UStar : Type uUStar}
    {SelmerChiStar : Type uSStar} {ClassStar : Type uCStar}
    {UDual : Type uUDual} {DOmegaSelmerChiStar : Type uSDual}
    {ClassDual : Type uCDual}
    [AddCommGroup UChi] [Module Lambda UChi]
    [AddCommGroup SelmerChi] [Module Lambda SelmerChi]
    [AddCommGroup ClassChi] [Module Lambda ClassChi]
    [AddCommGroup UStar] [Module Lambda UStar]
    [AddCommGroup SelmerChiStar] [Module Lambda SelmerChiStar]
    [AddCommGroup ClassStar] [Module Lambda ClassStar]
    [AddCommGroup UDual] [Module Lambda UDual]
    [AddCommGroup DOmegaSelmerChiStar] [Module Lambda DOmegaSelmerChiStar]
    [AddCommGroup ClassDual] [Module Lambda ClassDual]
    {sharp : Lambda ≃+* Lambda}
    (sequence : SelmerClassSequenceRealization (R := R) (K := K) (p := p))
    (carrier : ReflectedExactFilteredPair p Lambda UChi SelmerChi ClassChi
      UStar SelmerChiStar ClassStar UDual DOmegaSelmerChiStar ClassDual
      sharp) where
  chi : KummerCharacterLegCompatibility sequence carrier.pair.chi
  chiStar : KummerCharacterLegCompatibility sequence carrier.chiStar

/-! ## Adapter from the campaign's filtered Stickelberger carrier -/

section FilteredAdapter

variable {p : ℕ} [Fact p.Prime]
  {Delta : Type uDelta} [CommGroup Delta]
  {U : Type uUChi} {S : Type uSChi} {ClassP : Type uCChi}
  [AddCommGroup U] [Module (IntegralPadicGroupAlgebra p Delta) U]
  [AddCommGroup S] [Module (IntegralPadicGroupAlgebra p Delta) S]
  [AddCommGroup ClassP]
  [Module (IntegralPadicGroupAlgebra p Delta) ClassP]
  {Beta : Type uBeta} {G : Type uG} [Group Beta] [CommGroup G]
  {principal : Beta →* G}
  {stickelberger : IntegralStickelbergerIdeal p Delta}

/-- Forget only the principal-flow fields while retaining the complete exact
filtered leg.  The beta data remains available on the source carrier. -/
def exactLegOfFilteredStickelbergerCarrier
    (carrier : FilteredStickelbergerCarrier
      (U := U) (S := S) (ClassP := ClassP) principal stickelberger) :
    ExactFilteredLeg p (IntegralPadicGroupAlgebra p Delta) U S ClassP where
  unitInclusion := carrier.unitInclusion
  classProjection := carrier.classProjection
  unitInclusion_injective := carrier.unitInclusion_injective
  exact_at_carrier := carrier.exact_at_carrier
  classProjection_surjective := carrier.classProjection_surjective
  class_p_torsion := carrier.class_p_torsion
  filtration := carrier.filtration
  antitone_filtration := carrier.antitone_filtration

end FilteredAdapter

/-! ## Both integral guards, retained with the paired carrier -/

/-- The integral source ideal, its separately named reflected ideal, and the
mandatory sharp-transformation theorem. -/
structure IntegralReflectionInput
    (p : ℕ) [Fact p.Prime]
    (Delta : Type uDelta) [CommGroup Delta]
    (omega : InvolutiveBase.Character (PadicInt p) Delta) where
  source : IntegralStickelbergerIdeal p Delta
  omegaReflected : IntegralStickelbergerIdeal p Delta
  sharpGuard :
    IntegralStickelbergerIdeal.SharpTransformationGuard
      omega source omegaReflected

namespace IntegralReflectionInput

variable {p : ℕ} [Fact p.Prime]
  {Delta : Type uDelta} [CommGroup Delta]
  {omega : InvolutiveBase.Character (PadicInt p) Delta}

/-- Transport an actual integral source-ideal element through sharp into the
separately named reflected ideal.  This value consumes both linking guards. -/
def sharpTransport
    (input : IntegralReflectionInput p Delta omega)
    (theta : input.source.ideal) : input.omegaReflected.ideal := by
  refine ⟨InvolutiveBase.hash omega theta.1, ?_⟩
  rw [← input.sharpGuard.sharp_image_eq_omega_reflected]
  exact Ideal.mem_map_of_mem
    (InvolutiveBase.hash omega).toRingEquiv.toRingHom theta.2

@[simp]
theorem sharpTransport_coe
    (input : IntegralReflectionInput p Delta omega)
    (theta : input.source.ideal) :
    (input.sharpTransport theta : IntegralPadicGroupAlgebra p Delta) =
      InvolutiveBase.hash omega theta :=
  rfl

end IntegralReflectionInput

/-- The paired exact carrier together with the two integral Stickelberger
legs from which it is constructed.  `chi` and `reflectedDual` remain distinct
objects; no swap law is stored. -/
structure GuardedPairedCarrier
    (p : ℕ) [Fact p.Prime]
    (Delta : Type uDelta) [CommGroup Delta]
    (omega : InvolutiveBase.Character (PadicInt p) Delta)
    (UChi : Type uUChi) (SelmerChi : Type uSChi)
    (ClassChi : Type uCChi) (UDual : Type uUDual)
    (DOmegaSelmerChiStar : Type uSDual) (ClassDual : Type uCDual)
    [AddCommGroup UChi]
    [Module (IntegralPadicGroupAlgebra p Delta) UChi]
    [AddCommGroup SelmerChi]
    [Module (IntegralPadicGroupAlgebra p Delta) SelmerChi]
    [AddCommGroup ClassChi]
    [Module (IntegralPadicGroupAlgebra p Delta) ClassChi]
    [AddCommGroup UDual]
    [Module (IntegralPadicGroupAlgebra p Delta) UDual]
    [AddCommGroup DOmegaSelmerChiStar]
    [Module (IntegralPadicGroupAlgebra p Delta) DOmegaSelmerChiStar]
    [AddCommGroup ClassDual]
    [Module (IntegralPadicGroupAlgebra p Delta) ClassDual]
    (Beta : Type uBeta) (G : Type uG) [Group Beta] [CommGroup G]
    (principal : Beta →* G) where
  integral : IntegralReflectionInput p Delta omega
  chi : FilteredStickelbergerCarrier
    (U := UChi) (S := SelmerChi) (ClassP := ClassChi)
    principal integral.source
  reflectedDual : FilteredStickelbergerCarrier
    (U := UDual) (S := DOmegaSelmerChiStar) (ClassP := ClassDual)
    principal integral.omegaReflected

namespace GuardedPairedCarrier

variable {p : ℕ} [Fact p.Prime]
  {Delta : Type uDelta} [CommGroup Delta]
  {omega : InvolutiveBase.Character (PadicInt p) Delta}
  {UChi : Type uUChi} {SelmerChi : Type uSChi}
  {ClassChi : Type uCChi} {UDual : Type uUDual}
  {DOmegaSelmerChiStar : Type uSDual} {ClassDual : Type uCDual}
  [AddCommGroup UChi]
  [Module (IntegralPadicGroupAlgebra p Delta) UChi]
  [AddCommGroup SelmerChi]
  [Module (IntegralPadicGroupAlgebra p Delta) SelmerChi]
  [AddCommGroup ClassChi]
  [Module (IntegralPadicGroupAlgebra p Delta) ClassChi]
  [AddCommGroup UDual]
  [Module (IntegralPadicGroupAlgebra p Delta) UDual]
  [AddCommGroup DOmegaSelmerChiStar]
  [Module (IntegralPadicGroupAlgebra p Delta) DOmegaSelmerChiStar]
  [AddCommGroup ClassDual]
  [Module (IntegralPadicGroupAlgebra p Delta) ClassDual]
  {Beta : Type uBeta} {G : Type uG} [Group Beta] [CommGroup G]
  {principal : Beta →* G}

/-- Assemble the campaign's two exact filtered legs into the paired carrier. -/
def exactPair
    (carrier : GuardedPairedCarrier p Delta omega UChi SelmerChi ClassChi
      UDual DOmegaSelmerChiStar ClassDual Beta G principal) :
    ExactFilteredPair p (IntegralPadicGroupAlgebra p Delta)
      UChi SelmerChi ClassChi UDual DOmegaSelmerChiStar ClassDual where
  chi := exactLegOfFilteredStickelbergerCarrier carrier.chi
  reflectedDual :=
    exactLegOfFilteredStickelbergerCarrier carrier.reflectedDual

/-- The beta-bearing conversion receipt on the chi leg. -/
def chiConversionReceipt
    (carrier : GuardedPairedCarrier p Delta omega UChi SelmerChi ClassChi
      UDual DOmegaSelmerChiStar ClassDual Beta G principal)
    (theta : carrier.integral.source.ideal) (s : SelmerChi) :=
  carrier.chi.conversionReceipt theta s

/-- The beta-bearing conversion receipt on the reflected dual leg. -/
def reflectedDualConversionReceipt
    (carrier : GuardedPairedCarrier p Delta omega UChi SelmerChi ClassChi
      UDual DOmegaSelmerChiStar ClassDual Beta G principal)
    (theta : carrier.integral.omegaReflected.ideal)
    (s : DOmegaSelmerChiStar) :=
  carrier.reflectedDual.conversionReceipt theta s

/-- One source Stickelberger element produces both beta-bearing conversion
receipts: the chi receipt uses `theta`, and the reflected-dual receipt uses
its sharp transport into the separately guarded reflected ideal.  This is
the paired value at which both integral guards are consumed. -/
def pairedConversionReceipts
    (carrier : GuardedPairedCarrier p Delta omega UChi SelmerChi ClassChi
      UDual DOmegaSelmerChiStar ClassDual Beta G principal)
    (theta : carrier.integral.source.ideal)
    (chiPayload : SelmerChi) (dualPayload : DOmegaSelmerChiStar) :=
  (carrier.chi.conversionReceipt theta chiPayload,
    carrier.reflectedDual.conversionReceipt
      (carrier.integral.sharpTransport theta) dualPayload)

end GuardedPairedCarrier

/-! ## Real coefficient actions and named route interfaces -/

section CoefficientAction

variable {O : Type uO} [CommRing O]
  {Lambda : Type uLambda} [CommRing Lambda]
  {M : Type uM} [AddCommGroup M] [Module O M] [Module Lambda M]
  [SMulCommClass Lambda O M]

/-- The actual coefficient-ring action as `O`-linear endomorphisms. -/
def lambdaAction : Lambda →+* Module.End O M :=
  Module.toModuleEnd O M

@[simp]
theorem lambdaAction_apply (a : Lambda) (m : M) :
    lambdaAction (O := O) (M := M) a m = a • m :=
  rfl

end CoefficientAction

section DeltaAction

variable {O : Type uO} [CommRing O]
  {Delta : Type uDelta} [CommGroup Delta]
  {M : Type uM} [AddCommGroup M] [Module O M]
  [Module (InvolutiveBase.GroupAlgebra O Delta) M]
  [SMulCommClass (InvolutiveBase.GroupAlgebra O Delta) O M]

/-- The genuine `Delta` action obtained by embedding group elements in
`Lambda = O[Delta]` and using the module action. -/
def deltaAction : Delta →* Module.End O M :=
  (lambdaAction
    (O := O) (Lambda := InvolutiveBase.GroupAlgebra O Delta) (M := M)).toMonoidHom.comp
      (MonoidAlgebra.of O Delta)

@[simp]
theorem deltaAction_apply (delta : Delta) (m : M) :
    deltaAction (O := O) (M := M) delta m =
      MonoidAlgebra.of O Delta delta • m :=
  rfl

end DeltaAction

/-- The two Kummer-pairing-shaped directions.  They are intentionally not
inverse fields and do not identify the two carrier legs. -/
structure RouteMaps
    (O : Type uO) [CommRing O]
    (SelmerChi : Type uChi) (DOmegaSelmerChiStar : Type uDual)
    [AddCommGroup SelmerChi] [Module O SelmerChi]
    [AddCommGroup DOmegaSelmerChiStar] [Module O DOmegaSelmerChiStar] where
  r : SelmerChi →ₗ[O] DOmegaSelmerChiStar
  s : DOmegaSelmerChiStar →ₗ[O] SelmerChi

namespace RouteMaps

variable {O : Type uO} [CommRing O]
  {SelmerChi : Type uChi} {DOmegaSelmerChiStar : Type uDual}
  [AddCommGroup SelmerChi] [Module O SelmerChi]
  [AddCommGroup DOmegaSelmerChiStar] [Module O DOmegaSelmerChiStar]

/-- The closed word `C_chi = s r`, now an actual endomorphism. -/
def closedAtChi
    (routes : RouteMaps O SelmerChi DOmegaSelmerChiStar) :
    Module.End O SelmerChi :=
  routes.s.comp routes.r

/-- The other closed word `C_chi* = r s`, on the reflected dual leg. -/
def closedAtReflected
    (routes : RouteMaps O SelmerChi DOmegaSelmerChiStar) :
    Module.End O DOmegaSelmerChiStar :=
  routes.r.comp routes.s

/-- The open route on the pair, constructed from the two distinct arrows. -/
def openRoute
    (routes : RouteMaps O SelmerChi DOmegaSelmerChiStar) :
    Module.End O (SelmerChi × DOmegaSelmerChiStar) where
  toFun x := (routes.s x.2, routes.r x.1)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

@[simp]
theorem openRoute_apply
    (routes : RouteMaps O SelmerChi DOmegaSelmerChiStar)
    (x : SelmerChi) (y : DOmegaSelmerChiStar) :
    routes.openRoute (x, y) = (routes.s y, routes.r x) :=
  rfl

/-- Squaring the open route yields the two closed return words, not the
identity and not a swap equation. -/
theorem openRoute_sq_apply
    (routes : RouteMaps O SelmerChi DOmegaSelmerChiStar)
    (x : SelmerChi) (y : DOmegaSelmerChiStar) :
    (routes.openRoute ^ 2) (x, y) =
      (routes.closedAtChi x, routes.closedAtReflected y) := by
  change routes.openRoute (routes.openRoute (x, y)) = _
  rw [openRoute_apply, openRoute_apply]
  rfl

/-- Extract the named arrows from any eventual full arithmetic
representation.  This is a real construction conditional on that withheld
input; no representation is manufactured here. -/
def ofArithmeticRepresentation
    {R : Type uR} [CommRing R] [IsDedekindDomain R]
    {K : Type uK} [Field K] [Algebra R K] [IsFractionRing R K]
    {Lambda : Type uLambda} [CommRing Lambda]
    {A : Type uA} [Ring A]
    {base : Lambda →+* A} {route chiProjector reflectedProjector : A}
    (representation : LinkingInterfaces.ArithmeticRepresentation
      (R := R) (K := K)
      (O := O) (Lambda := Lambda) (A := A)
      (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar)
      base route chiProjector reflectedProjector) :
    RouteMaps O SelmerChi DOmegaSelmerChiStar where
  r := representation.routeChiToReflected
  s := representation.routeReflectedToChi

/-- The full representation, when supplied, identifies the Selmer action of
`R^2` with the constructible pair of closed endomorphisms. -/
theorem selmerAction_routeSquared_eq_closed
    {R : Type uR} [CommRing R] [IsDedekindDomain R]
    {K : Type uK} [Field K] [Algebra R K] [IsFractionRing R K]
    {Lambda : Type uLambda} [CommRing Lambda]
    {A : Type uA} [Ring A]
    {base : Lambda →+* A} {route chiProjector reflectedProjector : A}
    (representation : LinkingInterfaces.ArithmeticRepresentation
      (R := R) (K := K)
      (O := O) (Lambda := Lambda) (A := A)
      (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar)
      base route chiProjector reflectedProjector)
    (x : SelmerChi) (y : DOmegaSelmerChiStar) :
    representation.selmerAction (route ^ 2) (x, y) =
      ((ofArithmeticRepresentation representation).closedAtChi x,
        (ofArithmeticRepresentation representation).closedAtReflected y) :=
  representation.selmerAction_routeSquared x y

end RouteMaps

/-! ## Constructible words in the strict route corner -/

section CornerWords

variable {Lambda : Type uLambda} [CommRing Lambda]
  [RouteAlgebra.HasSharp Lambda]
  (e : Lambda) (he : IsIdempotentElem e)

/-- The reflection-cycle word `C^r - 1`, constructed in the actual strict
route corner through its earned polynomial service. -/
def reflectionCycleCorner (r : ℕ) : RouteAlgebra.RouteCorner e he :=
  RouteAlgebra.cornerPolynomialMap e he
    (TransverseAnnihilator.cyclePolynomial
      (RouteAlgebra.BaseCorner e he) r)

/-- Evaluation sends the cycle polynomial to the literal closed-route word. -/
theorem reflectionCycleCorner_eq (r : ℕ) :
    reflectionCycleCorner e he r =
      RouteAlgebra.cornerClosedRoute e he ^ r - 1 := by
  simp [reflectionCycleCorner, TransverseAnnihilator.cyclePolynomial,
    RouteAlgebra.cornerPolynomialMap]

/-- Project a coefficient into the `e Lambda e` base corner. -/
def baseCornerProjection (a : Lambda) : RouteAlgebra.BaseCorner e he := by
  refine ⟨e * a * e, ?_⟩
  rw [Subsemigroup.mem_corner_iff he]
  constructor
  · calc
      e * (e * a * e) = (e * e) * a * e := by ac_rfl
      _ = e * a * e := by rw [he.eq]
  · calc
      (e * a * e) * e = e * a * (e * e) := by ac_rfl
      _ = e * a * e := by rw [he.eq]

/-- Embed the integral coefficient `e theta e` as a constant element of the
strict route corner. -/
def stickelbergerCorner (theta : Lambda) : RouteAlgebra.RouteCorner e he :=
  RouteAlgebra.embedBaseCorner e he (baseCornerProjection e he theta)

@[simp]
theorem stickelbergerCorner_val (theta : Lambda) :
    (stickelbergerCorner e he theta).1 =
      SkewPolynomial.C (e * theta * e) :=
  rfl

end CornerWords

/-- A genuine strict reflection-cycle receipt.  Unlike the class-shadow
(7d) receipt below, its operator is definitionally tied to the constructed
corner word `C^r - 1`.  Producing this record on the Selmer obstruction is
the arithmetic transport still withheld with the route representation. -/
structure StrictReflectionCycleReceipt
    {Lambda : Type uLambda} [CommRing Lambda]
    [RouteAlgebra.HasSharp Lambda]
    (e : Lambda) (he : IsIdempotentElem e) (r : ℕ)
    (M : Type uM) [SMul (RouteAlgebra.RouteCorner e he) M] [Zero M]
    (m : M) where
  receipt : ClassCarrier.AnnihilatorReceipt
    (RouteAlgebra.RouteCorner e he) M
  operator_eq : receipt.operator = reflectionCycleCorner e he r
  payload_eq : receipt.payload = m

/-- Named target for transporting a retained class-shadow fold receipt to
the actual strict closed-word corner on a supplied Selmer payload. -/
def StrictReflectionCycleReceiptTarget
    {Lambda : Type uLambda} [CommRing Lambda]
    [RouteAlgebra.HasSharp Lambda]
    (e : Lambda) (he : IsIdempotentElem e) (r : ℕ)
    (M : Type uM) [SMul (RouteAlgebra.RouteCorner e he) M] [Zero M]
    (m : M) : Prop :=
  Nonempty (StrictReflectionCycleReceipt e he r M m)

/-! ## Integral conversion at a character corner -/

section CornerConversion

variable {p : ℕ} [Fact p.Prime]
  {Delta : Type uDelta} [CommGroup Delta]
  [RouteAlgebra.HasSharp (IntegralPadicGroupAlgebra p Delta)]
  {U : Type uUChi} {S : Type uSChi} {ClassP : Type uCChi}
  [AddCommGroup U] [Module (IntegralPadicGroupAlgebra p Delta) U]
  [AddCommGroup S] [Module (IntegralPadicGroupAlgebra p Delta) S]
  [AddCommGroup ClassP]
  [Module (IntegralPadicGroupAlgebra p Delta) ClassP]
  {Beta : Type uBeta} {G : Type uG} [Group Beta] [CommGroup G]
  {principal : Beta →* G}
  {stickelberger : IntegralStickelbergerIdeal p Delta}

variable (e : IntegralPadicGroupAlgebra p Delta)
  (he : IsIdempotentElem e)

omit [RouteAlgebra.HasSharp (IntegralPadicGroupAlgebra p Delta)] in
/-- On the `e`-summand, the corner coefficient `e theta e` acts exactly as
`theta`. -/
theorem cornerCoefficient_smul_eq
    (theta : stickelberger.ideal) (s : S) (hs : e • s = s) :
    (e * (theta : IntegralPadicGroupAlgebra p Delta) * e) • s =
      (theta : IntegralPadicGroupAlgebra p Delta) • s := by
  calc
    (e * (theta : IntegralPadicGroupAlgebra p Delta) * e) • s =
        e • ((theta : IntegralPadicGroupAlgebra p Delta) • (e • s)) := by
      simp only [mul_smul]
    _ = e • ((theta : IntegralPadicGroupAlgebra p Delta) • s) := by
      rw [hs]
    _ = (theta : IntegralPadicGroupAlgebra p Delta) • (e • s) :=
      smul_comm e (theta : IntegralPadicGroupAlgebra p Delta) s
    _ = (theta : IntegralPadicGroupAlgebra p Delta) • s := by rw [hs]

/-- Conversion data at one strict-route corner.  The converted unit and its
beta principalization receipt are retained.  The equation is conversion into
the units range, not an assertion that the Selmer payload is zero. -/
structure CornerConversionReceipt
    (carrier : FilteredStickelbergerCarrier
      (U := U) (S := S) (ClassP := ClassP) principal stickelberger)
    (theta : stickelberger.ideal) (s : S) (hs : e • s = s) where
  cornerElement : RouteAlgebra.RouteCorner e he
  cornerElement_eq :
    cornerElement = stickelbergerCorner e he theta
  convertedUnit : U
  unitInclusion_eq :
    carrier.unitInclusion convertedUnit =
      (e * (theta : IntegralPadicGroupAlgebra p Delta) * e) • s
  principalization :
    ClassCarrier.PrincipalizationReceipt principal
      (carrier.source theta s) (carrier.reduced theta s)

/-- Construct the corner conversion directly from the campaign's filtered
carrier. -/
def cornerConversionReceipt
    (carrier : FilteredStickelbergerCarrier
      (U := U) (S := S) (ClassP := ClassP) principal stickelberger)
    (theta : stickelberger.ideal) (s : S) (hs : e • s = s) :
    CornerConversionReceipt e he carrier theta s hs where
  cornerElement := stickelbergerCorner e he theta
  cornerElement_eq := rfl
  convertedUnit := carrier.convertedUnit theta s
  unitInclusion_eq :=
    (carrier.stickelberger_conversion theta s).trans
      (cornerCoefficient_smul_eq e theta s hs).symm
  principalization := carrier.conversionReceipt theta s

@[simp]
theorem cornerConversionReceipt_beta
    (carrier : FilteredStickelbergerCarrier
      (U := U) (S := S) (ClassP := ClassP) principal stickelberger)
    (theta : stickelberger.ideal) (s : S) (hs : e • s = s) :
    (cornerConversionReceipt e he carrier theta s hs).principalization.beta =
      carrier.betaOfUnit (carrier.convertedUnit theta s) :=
  rfl

omit [RouteAlgebra.HasSharp (IntegralPadicGroupAlgebra p Delta)] in
/-- Annihilation is valid only after projecting the converted multiple to
the class leg. -/
theorem classProjection_cornerCoefficient_smul_eq_zero
    (carrier : FilteredStickelbergerCarrier
      (U := U) (S := S) (ClassP := ClassP) principal stickelberger)
    (theta : stickelberger.ideal) (s : S) (hs : e • s = s) :
    carrier.classProjection
        ((e * (theta : IntegralPadicGroupAlgebra p Delta) * e) • s) = 0 := by
  rw [cornerCoefficient_smul_eq e theta s hs]
  exact carrier.classProjection_smul_eq_zero theta s

end CornerConversion

/-! ## Binding conversion beta to a non-lossy class state -/

/-- Compatibility required before a Stickelberger conversion may be read as
the units leg of a particular `ClassCarrier` state.  The carrier's source,
reduced representative, and beta are all identified with that state; no
coercion of a field element to an integral unit is fabricated. -/
structure StateConversionCompatibility
    {p : ℕ} [Fact p.Prime]
    {Delta : Type uDelta} [CommGroup Delta]
    {U : Type uUChi} {S : Type uSChi} {ClassP : Type uCChi}
    [AddCommGroup U] [Module (IntegralPadicGroupAlgebra p Delta) U]
    [AddCommGroup S] [Module (IntegralPadicGroupAlgebra p Delta) S]
    [AddCommGroup ClassP]
    [Module (IntegralPadicGroupAlgebra p Delta) ClassP]
    {Beta : Type uBeta} {G : Type uG} [Group Beta] [CommGroup G]
    {principal : Beta →* G}
    {stickelberger : IntegralStickelbergerIdeal p Delta}
    {region : ClassCarrier.BoundedRegion G} {stateSource : G}
    {Operator : Type uA} {Payload : Type uGauge}
    [SMul Operator Payload] [Zero Payload]
    (state : ClassCarrier.State region principal stateSource Operator Payload)
    (carrier : FilteredStickelbergerCarrier
      (U := U) (S := S) (ClassP := ClassP) principal stickelberger)
    (theta : stickelberger.ideal) (s : S) where
  source_eq : carrier.source theta s = stateSource
  reduced_eq : carrier.reduced theta s = state.reduced
  beta_eq : carrier.betaOfUnit (carrier.convertedUnit theta s) = state.beta

@[simp]
theorem StateConversionCompatibility.conversionReceipt_beta_eq_state_beta
    {p : ℕ} [Fact p.Prime]
    {Delta : Type uDelta} [CommGroup Delta]
    {U : Type uUChi} {S : Type uSChi} {ClassP : Type uCChi}
    [AddCommGroup U] [Module (IntegralPadicGroupAlgebra p Delta) U]
    [AddCommGroup S] [Module (IntegralPadicGroupAlgebra p Delta) S]
    [AddCommGroup ClassP]
    [Module (IntegralPadicGroupAlgebra p Delta) ClassP]
    {Beta : Type uBeta} {G : Type uG} [Group Beta] [CommGroup G]
    {principal : Beta →* G}
    {stickelberger : IntegralStickelbergerIdeal p Delta}
    {region : ClassCarrier.BoundedRegion G} {stateSource : G}
    {Operator : Type uA} {Payload : Type uGauge}
    [SMul Operator Payload] [Zero Payload]
    {state : ClassCarrier.State region principal stateSource Operator Payload}
    {carrier : FilteredStickelbergerCarrier
      (U := U) (S := S) (ClassP := ClassP) principal stickelberger}
    {theta : stickelberger.ideal} {s : S}
    (compatibility : StateConversionCompatibility state carrier theta s) :
    (carrier.conversionReceipt theta s).beta = state.beta :=
  compatibility.beta_eq

section PairedCornerConversion

variable {p : ℕ} [Fact p.Prime]
  {Delta : Type uDelta} [CommGroup Delta]
  {omega : InvolutiveBase.Character (PadicInt p) Delta}
  [RouteAlgebra.HasSharp (IntegralPadicGroupAlgebra p Delta)]
  {UChi : Type uUChi} {SelmerChi : Type uSChi}
  {ClassChi : Type uCChi} {UDual : Type uUDual}
  {DOmegaSelmerChiStar : Type uSDual} {ClassDual : Type uCDual}
  [AddCommGroup UChi]
  [Module (IntegralPadicGroupAlgebra p Delta) UChi]
  [AddCommGroup SelmerChi]
  [Module (IntegralPadicGroupAlgebra p Delta) SelmerChi]
  [AddCommGroup ClassChi]
  [Module (IntegralPadicGroupAlgebra p Delta) ClassChi]
  [AddCommGroup UDual]
  [Module (IntegralPadicGroupAlgebra p Delta) UDual]
  [AddCommGroup DOmegaSelmerChiStar]
  [Module (IntegralPadicGroupAlgebra p Delta) DOmegaSelmerChiStar]
  [AddCommGroup ClassDual]
  [Module (IntegralPadicGroupAlgebra p Delta) ClassDual]
  {Beta : Type uBeta} {G : Type uG} [Group Beta] [CommGroup G]
  {principal : Beta →* G}

/-- The paired corner conversion from one integral source element.  Its
second corner receipt is formed only after sharp-transporting that element
through the transformation guard. -/
def GuardedPairedCarrier.pairedCornerConversionReceipts
    (carrier : GuardedPairedCarrier p Delta omega UChi SelmerChi ClassChi
      UDual DOmegaSelmerChiStar ClassDual Beta G principal)
    (eChi eDual : IntegralPadicGroupAlgebra p Delta)
    (heChi : IsIdempotentElem eChi) (heDual : IsIdempotentElem eDual)
    (theta : carrier.integral.source.ideal)
    (chiPayload : SelmerChi) (dualPayload : DOmegaSelmerChiStar)
    (hChi : eChi • chiPayload = chiPayload)
    (hDual : eDual • dualPayload = dualPayload) :=
  (cornerConversionReceipt eChi heChi carrier.chi theta chiPayload hChi,
    cornerConversionReceipt eDual heDual carrier.reflectedDual
      (carrier.integral.sharpTransport theta) dualPayload hDual)

end PairedCornerConversion

/-! ## The allocated class obstruction and its receipts -/

/-- The additive ideal-class carrier used by an allocated factor ledger. -/
abbrev AllocatedClass (K : Type uK) [Field K] [NumberField K] :=
  Additive (ClassGroup (NumberField.RingOfIntegers K))

section ClassCorner

variable (Class : Type uM) [AddCommGroup Class]

/-- The real class-level reflection which exchanges the two allocated
accounts.  This is not identified with the strict route action. -/
def classSwap : Module.End ℤ (Class × Class) where
  toFun x := (x.2, x.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The class-shadow relation-(7d) word `1 + swap`. -/
def sevenDClassOperator : Module.End ℤ (Class × Class) :=
  1 + classSwap Class

/-- The identity idempotent used to regard the class-shadow relation as a
literal corner element. -/
def classCornerIdempotent :
    IsIdempotentElem (1 : Module.End ℤ (Class × Class)) := by
  simp [IsIdempotentElem]

/-- The full class endomorphism ring, displayed as its identity corner. -/
abbrev ClassActionCorner := (classCornerIdempotent Class).Corner

/-- Relation (7d)'s common-mode word as a literal element of the class
endomorphism corner. -/
def sevenDClassCornerElement : ClassActionCorner Class := by
  refine ⟨sevenDClassOperator Class, ?_⟩
  rw [Subsemigroup.mem_corner_iff (classCornerIdempotent Class)]
  simp

/-- The unhalved difference gauge.  For an allocated `p`-torsion pair and
positive `p`, relation (7a) rewrites to its zero reading. -/
def differenceGauge : (Class × Class) →+ Class where
  toFun x := x.1 - x.2
  map_zero' := by simp
  map_add' x y := by
    change (x.1 + y.1) - (x.2 + y.2) =
      (x.1 - x.2) + (y.1 - y.2)
    abel

/-- The actual class-valued relation-(7a) gauge has no affine offset: its
vacuum reading is zero.  This is the strongest unconditional linearity
statement available before a scalar `ZMod p` seating is supplied. -/
@[simp]
theorem differenceGauge_vacuum :
    differenceGauge Class (0 : Class × Class) = 0 :=
  map_zero (differenceGauge Class)

/-- The proved (7d) fold as a proof-bearing class-shadow corner receipt.  Its
operator is `1 + classSwap`; it is not mislabeled as the strict closed word
`C^r - 1`, whose action still requires arithmetic transport. -/
def sevenDClassShadowReceipt (x y : Class) (h : x + y = 0) :
    ClassCarrier.AnnihilatorReceipt
      (Module.End ℤ (Class × Class)) (Class × Class) where
  operator := (sevenDClassCornerElement Class).1
  payload := (x, y)
  annihilates := by
    change (x + y, y + x) = 0
    apply Prod.ext
    · change x + y = (0 : Class)
      exact h
    · change y + x = (0 : Class)
      simpa only [add_comm] using h

end ClassCorner

section AllocatedReceipts

variable {p : ℕ} [Fact p.Prime]
  {K : Type uK} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]
  {I : Type uM}

/-- One allocated root ideal as an invertible fractional ideal, with its
nonzeroness proof retained. -/
def allocatedRootSource
    (ledger : KummerDrain.AllocatedFactorLedger (p := p) (K := K) I)
    (i : I) :
    (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ :=
  Units.mk0
    (ledger.rootIdeal i :
      FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)
    (ledger.rootFractionalIdeal_ne_zero i)

variable {Operator : Type uA} {Payload : Type uGauge}
  [SMul Operator Payload] [Zero Payload]

/-- The actual Minkowski-reduced `ClassCarrier` state above an allocated
root, retaining beta and every supplied annihilator receipt. -/
def allocatedRootState
    (ledger : KummerDrain.AllocatedFactorLedger (p := p) (K := K) I)
    (i : I)
    (receipts : List (ClassCarrier.AnnihilatorReceipt Operator Payload)) :
    ClassCarrier.State (ClassCarrier.numberFieldMinkowskiRegion K)
      (toPrincipalIdeal (NumberField.RingOfIntegers K) K)
      (allocatedRootSource ledger i) Operator Payload :=
  (ClassCarrier.numberFieldBoundedRepresentative K).reduce
    (allocatedRootSource ledger i) receipts

omit [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] in
@[simp]
theorem allocatedRootState_receipts
    (ledger : KummerDrain.AllocatedFactorLedger (p := p) (K := K) I)
    (i : I)
    (receipts : List (ClassCarrier.AnnihilatorReceipt Operator Payload)) :
    (allocatedRootState ledger i receipts).annihilatorReceipts = receipts :=
  rfl

omit [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] in
/-- The receipted state projects to exactly the allocated root class. -/
theorem allocatedRootState_class
    (ledger : KummerDrain.AllocatedFactorLedger (p := p) (K := K) I)
    (i : I)
    (receipts : List (ClassCarrier.AnnihilatorReceipt Operator Payload)) :
    Additive.ofMul
        (ClassCarrier.idealClassProjection
          (allocatedRootState ledger i receipts)) =
      ledger.rootClass i := by
  rw [ClassCarrier.idealClassProjection_eq_source_class]
  rfl

omit [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] in
/-- The retained beta reconstructs the allocated source ideal from its
bounded representative. -/
theorem allocatedRootState_source_eq
    (ledger : KummerDrain.AllocatedFactorLedger (p := p) (K := K) I)
    (i : I)
    (receipts : List (ClassCarrier.AnnihilatorReceipt Operator Payload)) :
    allocatedRootSource ledger i =
      toPrincipalIdeal (NumberField.RingOfIntegers K) K
          (allocatedRootState ledger i receipts).beta *
        (allocatedRootState ledger i receipts).reduced :=
  (allocatedRootState ledger i receipts).source_eq_principal_mul_reduced

/-- The statewise Fermat obstruction before character allocation. -/
def allocatedClassObstruction
    (ledger : KummerDrain.AllocatedFactorLedger (p := p) (K := K) I)
    (i j : I) : AllocatedClass K × AllocatedClass K :=
  (ledger.rootClass i, ledger.rootClass j)

/-- The actual fold/(7d) theorem re-expressed as a corner element acting on
the statewise class obstruction. -/
def allocatedSevenDClassReceipt
    (ledger : KummerDrain.AllocatedFactorLedger (p := p) (K := K) I)
    (i j : I) (sevenD : ledger.VandiverSevenD i j) :
    ClassCarrier.AnnihilatorReceipt
      (Module.End ℤ (AllocatedClass K × AllocatedClass K))
      (AllocatedClass K × AllocatedClass K) := by
  apply sevenDClassShadowReceipt
  exact sevenD

/-- One allocated root state with the fold receipt threaded through its
non-lossy `ClassCarrier` history. -/
def allocatedSevenDReceiptedRootState
    (ledger : KummerDrain.AllocatedFactorLedger (p := p) (K := K) I)
    (i j root : I) (sevenD : ledger.VandiverSevenD i j) :=
  allocatedRootState ledger root [allocatedSevenDClassReceipt ledger i j sevenD]

omit [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] in
@[simp]
theorem allocatedSevenDReceiptedRootState_receipt
    (ledger : KummerDrain.AllocatedFactorLedger (p := p) (K := K) I)
    (i j root : I) (sevenD : ledger.VandiverSevenD i j) :
    (allocatedSevenDReceiptedRootState ledger i j root sevenD).annihilatorReceipts =
      [allocatedSevenDClassReceipt ledger i j sevenD] :=
  rfl

omit [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] in
/-- The fold receipt annihilates exactly the retained statewise obstruction. -/
theorem allocatedSevenDClassReceipt_payload
    (ledger : KummerDrain.AllocatedFactorLedger (p := p) (K := K) I)
    (i j : I) (sevenD : ledger.VandiverSevenD i j) :
    (allocatedSevenDClassReceipt ledger i j sevenD).payload =
      allocatedClassObstruction ledger i j :=
  rfl

end AllocatedReceipts

section AllocatedSelmerLift

variable {p : ℕ} [Fact p.Prime]
  {K : Type uK} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]
  {I : Type uM}
  {Lambda : Type uLambda} [CommRing Lambda]
  {UChi : Type uUChi} {SelmerChi : Type uSChi}
  {ClassChi : Type uCChi}
  {UDual : Type uUDual} {DOmegaSelmerChiStar : Type uSDual}
  {ClassDual : Type uCDual}
  [AddCommGroup UChi] [Module Lambda UChi]
  [AddCommGroup SelmerChi] [Module Lambda SelmerChi]
  [AddCommGroup ClassChi] [Module Lambda ClassChi]
  [AddCommGroup UDual] [Module Lambda UDual]
  [AddCommGroup DOmegaSelmerChiStar] [Module Lambda DOmegaSelmerChiStar]
  [AddCommGroup ClassDual] [Module Lambda ClassDual]

/-- One allocated root class, with its earned `p`-torsion proof retained in
the actual quotient type appearing in the Kummer exact sequence. -/
def allocatedRootClassPTorsion
    (ledger : KummerDrain.AllocatedFactorLedger (p := p) (K := K) I)
    (i : I) :
    ClassPTorsion (NumberField.RingOfIntegers K) p :=
  ⟨ledger.rootClass i,
    AddSubgroup.torsionBy.nsmul_iff.mpr (ledger.rootClass_torsion i)⟩

/-- Character allocation is deliberately directional on each class leg.
In particular the reflected-dual class payload is not obtained by swapping
or by silently reusing the chi quotient type. -/
structure CharacterClassAllocation where
  chi : ClassPTorsion (NumberField.RingOfIntegers K) p →+ ClassChi
  reflectedDual :
    ClassPTorsion (NumberField.RingOfIntegers K) p →+ ClassDual

/-- The two allocated `p`-torsion roots after the separately supplied chi
and reflected-dual class allocations. -/
def allocatedCharacterClassObstruction
    (allocation : CharacterClassAllocation
      (p := p) (K := K) (ClassChi := ClassChi) (ClassDual := ClassDual))
    (ledger : KummerDrain.AllocatedFactorLedger (p := p) (K := K) I)
    (i j : I) : ClassChi × ClassDual :=
  (allocation.chi (allocatedRootClassPTorsion ledger i),
    allocation.reflectedDual (allocatedRootClassPTorsion ledger j))

/-- Lift the statewise Fermat class pair into the paired Selmer carrier when
the named exact-sequence and character-allocation data has genuinely supplied
that carrier. -/
noncomputable def allocatedSelmerObstruction
    (pair : ExactFilteredPair p Lambda UChi SelmerChi ClassChi
      UDual DOmegaSelmerChiStar ClassDual)
    (allocation : CharacterClassAllocation
      (p := p) (K := K) (ClassChi := ClassChi) (ClassDual := ClassDual))
    (ledger : KummerDrain.AllocatedFactorLedger (p := p) (K := K) I)
    (i j : I) : SelmerChi × DOmegaSelmerChiStar :=
  pair.liftClassPair
    (allocatedCharacterClassObstruction allocation ledger i j)

omit [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] in
/-- The lifted obstruction projects to exactly the two allocated Fermat
classes. -/
theorem classProjection_allocatedSelmerObstruction
    (pair : ExactFilteredPair p Lambda UChi SelmerChi ClassChi
      UDual DOmegaSelmerChiStar ClassDual)
    (allocation : CharacterClassAllocation
      (p := p) (K := K) (ClassChi := ClassChi) (ClassDual := ClassDual))
    (ledger : KummerDrain.AllocatedFactorLedger (p := p) (K := K) I)
    (i j : I) :
    pair.classProjection
        (allocatedSelmerObstruction pair allocation ledger i j) =
      allocatedCharacterClassObstruction allocation ledger i j :=
  pair.classProjection_liftClassPair _

end AllocatedSelmerLift

/-! ## Unit ideal, surviving channel, or localized wall -/

namespace Outcome

variable {A : Type uA} {M : Type uM} [Ring A]
  [AddCommGroup M] [Module A M]
  {Gauge : Type uGauge} [AddCommGroup Gauge]
  {cycle transverse : A} {m : M}

/-- The successful unit-ideal result.  It includes both action receipts, the
literal Bézout identity, vanishing of the obstruction, and the projected gauge
reading. -/
structure UnitIdealResult (gauge : M →+ Gauge) where
  cycle_annihilates : TransverseAnnihilator.Annihilates cycle m
  transverse_annihilates : TransverseAnnihilator.Annihilates transverse m
  bezout : TransverseAnnihilator.CornerService.BezoutCertificate
    cycle transverse
  obstruction_eq_zero : m = 0
  gauge_reading : gauge m = 0

/-- Construct the successful result through the common corner service. -/
def unitIdealResult
    (gauge : M →+ Gauge)
    (hcycle : TransverseAnnihilator.Annihilates cycle m)
    (htransverse : TransverseAnnihilator.Annihilates transverse m)
    (bezout : TransverseAnnihilator.CornerService.BezoutCertificate
      cycle transverse) :
    UnitIdealResult (cycle := cycle) (transverse := transverse)
      (m := m) gauge := by
  have hm : m = 0 :=
    TransverseAnnihilator.CornerService.eq_zero_of_annihilates_of_bezout
      hcycle htransverse bezout
  exact
    { cycle_annihilates := hcycle
      transverse_annihilates := htransverse
      bezout := bezout
      obstruction_eq_zero := hm
      gauge_reading := by rw [hm, map_zero] }

/-- The non-unit-ideal result.  In the general noncommutative corner the
truthful object is the surviving quotient class; a named common factor is
available only after a commutative polynomial specialization. -/
structure SurvivingChannelResult where
  cycle_annihilates : TransverseAnnihilator.Annihilates cycle m
  transverse_annihilates : TransverseAnnihilator.Annihilates transverse m
  channel :
    TransverseAnnihilator.CornerService.CornerLivelockChannel cycle transverse

/-- Exact addresses at which the arithmetic construction may stop. -/
inductive WallAddress
  | selmerClassExactness
  | characterDualAllocation
  | integralStickelbergerGuards
  | classReceiptToStrictRoute
  | strictRouteRho
  deriving DecidableEq, Repr

/-- A localized wall names the missing target but does not assert its
negation.  Its stored obstruction is indexed by the acted payload, preventing
an unrelated wall from inhabiting a typed outcome. -/
structure LocalizedWall (m : M) where
  obstruction : M
  obstruction_eq : obstruction = m
  address : WallAddress
  target : Prop

/-- The typed three-way result of the common-action attempt. -/
inductive TypedResult (gauge : M →+ Gauge)
  | unitIdeal (result : UnitIdealResult
      (cycle := cycle) (transverse := transverse) (m := m) gauge)
  | survivingChannel (result : SurvivingChannelResult
      (cycle := cycle) (transverse := transverse) (m := m))
  | localizedWall (wall : LocalizedWall m)

/-- Polynomial specialization of the three-way outcome.  Here the middle
branch is literally a named nonunit common factor, with divisibility and
annihilation receipts, rather than merely a noncommutative quotient channel. -/
inductive PolynomialTypedResult
    {F : Type uA} [Field F] [DecidableEq F]
    {PMode : Type uM} [AddCommGroup PMode]
    [Module (Polynomial F) PMode]
    {r : ℕ}
    (data : TransverseAnnihilator.TwoAnnihilatorMode F PMode r)
    {PGauge : Type uGauge} [AddCommGroup PGauge]
    (gauge : PMode →+ PGauge) where
  | unitIdeal (result : UnitIdealResult
      (cycle := TransverseAnnihilator.cyclePolynomial F r)
      (transverse := data.transverse) (m := data.mode) gauge)
  | namedCommonFactor
      (result : TransverseAnnihilator.LivelockChannel data)
  | localizedWall (wall : LocalizedWall data.mode)

end Outcome

/-! ## The exact withheld representation address -/

section RepresentationWall

variable {p : ℕ} [Fact p.Prime]
  {R : Type uR} [CommRing R] [IsDedekindDomain R]
  {K : Type uK} [Field K] [Algebra R K] [IsFractionRing R K]
  {Delta : Type uDelta} [CommGroup Delta] [Fintype Delta]
  [Invertible (Fintype.card Delta : PadicInt p)]
  {SelmerChi : Type uChi} {DOmegaSelmerChiStar : Type uDual}
  [AddCommGroup SelmerChi] [Module (PadicInt p) SelmerChi]
  [AddCommGroup DOmegaSelmerChiStar]
  [Module (PadicInt p) DOmegaSelmerChiStar]

/-- The current summit localized exactly at the missing strict-route
representation.  No proof of nonexistence is claimed. -/
def reflectedSelmerRhoWall
    (omega chi : InvolutiveBase.Character (PadicInt p) Delta)
    (m : LinkingInterfaces.ReflectedSelmerPair
      SelmerChi DOmegaSelmerChiStar) :
    Outcome.LocalizedWall m where
  obstruction := m
  obstruction_eq := rfl
  address := Outcome.WallAddress.strictRouteRho
  target := LinkingInterfaces.ReflectedSelmerArithmeticRepresentationTarget
    (R := R) (K := K)
    (SelmerChi := SelmerChi)
    (DOmegaSelmerChiStar := DOmegaSelmerChiStar) omega chi

theorem reflectedSelmerRhoWall_target
    (omega chi : InvolutiveBase.Character (PadicInt p) Delta)
    (m : LinkingInterfaces.ReflectedSelmerPair
      SelmerChi DOmegaSelmerChiStar) :
    (reflectedSelmerRhoWall (R := R) (K := K) omega chi m).target =
      LinkingInterfaces.ReflectedSelmerArithmeticRepresentationTarget
        (R := R) (K := K)
        (SelmerChi := SelmerChi)
        (DOmegaSelmerChiStar := DOmegaSelmerChiStar) omega chi :=
  rfl

end RepresentationWall

end Fermat.Conservation.CommonActionStage
