/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Interfaces beyond the linking algebra

This file is an earned-theorem ledger, not an arithmetic proof.  It records
the integral Stickelberger input, the exact filtered carrier and its
conversion receipt, and the still-withheld representation of the strict
route algebra on the reflected Selmer pair.

In particular, the Stickelberger action below is a conversion into the unit
range.  It is not packaged as an annihilator.  The route representation is a
`Prop` with no supplied inhabitant, and its closed route remains the square
of the route generator rather than being identified with the identity.
-/
import Fermat.Conservation.ClassCarrier
import Fermat.Conservation.RouteAlgebra
import Mathlib.NumberTheory.Padics.PadicIntegers

noncomputable section

namespace Fermat.Conservation.LinkingInterfaces

universe uDelta uU uS uClass uBeta uG uLambda uA uO uChi uReflected

/-! ## Integral Stickelberger guards -/

/-- The integral coefficient algebra in which the guarded Stickelberger
ideal lives.  The coefficient ring is `PadicInt p`, never its fraction
field or a rational expression containing a denominator at `p`. -/
abbrev IntegralPadicGroupAlgebra (p : ℕ) [Fact p.Prime]
    (Delta : Type uDelta) [CommGroup Delta] :=
  InvolutiveBase.GroupAlgebra (PadicInt p) Delta

/-- Guard one: a Stickelberger input is an ideal of the integral p-adic
group algebra.  Merely providing a rational group-algebra element cannot
inhabit this interface. -/
structure IntegralStickelbergerIdeal
    (p : ℕ) [Fact p.Prime]
    (Delta : Type uDelta) [CommGroup Delta] where
  ideal : Ideal (IntegralPadicGroupAlgebra p Delta)

namespace IntegralStickelbergerIdeal

variable {p : ℕ} [Fact p.Prime]
  {Delta : Type uDelta} [CommGroup Delta]

/-- The image of the integral ideal under the Teichmuller-twisted
involution. -/
noncomputable def sharpImage
    (omega : InvolutiveBase.Character (PadicInt p) Delta)
    (stickelberger : IntegralStickelbergerIdeal p Delta) :
    Ideal (IntegralPadicGroupAlgebra p Delta) :=
  stickelberger.ideal.map
    (InvolutiveBase.hash omega).toRingEquiv.toRingHom

/-- Guard two: reflection of the Stickelberger ideal must be proved as a
transformation into the separately named omega-reflected ideal.  Invariance
of the source ideal is deliberately not assumed. -/
structure SharpTransformationGuard
    (omega : InvolutiveBase.Character (PadicInt p) Delta)
    (source omegaReflected : IntegralStickelbergerIdeal p Delta) : Prop where
  sharp_image_eq_omega_reflected :
    source.sharpImage omega = omegaReflected.ideal

end IntegralStickelbergerIdeal

/-- The projector-level warning behind the ideal transformation guard:
sharp sends the trivial character projector to the omega projector, not in
general back to the trivial projector. -/
theorem sharp_trivialProjector_eq_omegaProjector
    {O : Type uO} {Delta : Type uDelta}
    [CommRing O] [CommGroup Delta] [Fintype Delta]
    [Invertible (Fintype.card Delta : O)]
    (omega : InvolutiveBase.Character O Delta) :
    InvolutiveBase.hash omega
        (InvolutiveBase.characterIdempotent
          (1 : InvolutiveBase.Character O Delta)) =
      InvolutiveBase.characterIdempotent omega :=
  InvolutiveBase.hash_trivialCharacterIdempotent omega

/-! ## Exact filtered carrier and conversion receipt -/

section FilteredCarrier

variable {p : ℕ} [Fact p.Prime]
  {Delta : Type uDelta} [CommGroup Delta]
  {U : Type uU} {S : Type uS} {ClassP : Type uClass}
  [AddCommGroup U] [Module (IntegralPadicGroupAlgebra p Delta) U]
  [AddCommGroup S] [Module (IntegralPadicGroupAlgebra p Delta) S]
  [AddCommGroup ClassP]
  [Module (IntegralPadicGroupAlgebra p Delta) ClassP]
  {Beta : Type uBeta} {G : Type uG} [Group Beta] [CommGroup G]

/-- Interface only: the exact filtered carrier
`0 -> U -> S -> Cl(K)[p] -> 0`, together with integral Stickelberger
conversion and the retained principal-flow data.

The filtration is intentionally just a decreasing filtration.  No stronger
chain-level structure is asserted here. -/
structure FilteredStickelbergerCarrier
    (principal : Beta →* G)
    (stickelberger : IntegralStickelbergerIdeal p Delta) where
  unitInclusion : U →ₗ[IntegralPadicGroupAlgebra p Delta] S
  classProjection : S →ₗ[IntegralPadicGroupAlgebra p Delta] ClassP
  unitInclusion_injective : Function.Injective unitInclusion
  exact_at_carrier :
    LinearMap.range unitInclusion = LinearMap.ker classProjection
  classProjection_surjective : Function.Surjective classProjection
  class_p_torsion : ∀ c : ClassP, p • c = 0
  filtration : ℕ → Submodule (IntegralPadicGroupAlgebra p Delta) S
  antitone_filtration : Antitone filtration
  convertedUnit : stickelberger.ideal → S → U
  stickelberger_conversion : ∀ theta s,
    unitInclusion (convertedUnit theta s) =
      (theta : IntegralPadicGroupAlgebra p Delta) • s
  source : stickelberger.ideal → S → G
  reduced : stickelberger.ideal → S → G
  betaOfUnit : U → Beta
  principal_flow : ∀ theta s,
    source theta s =
      principal (betaOfUnit (convertedUnit theta s)) * reduced theta s

namespace FilteredStickelbergerCarrier

variable {principal : Beta →* G}
  {stickelberger : IntegralStickelbergerIdeal p Delta}
  (carrier : FilteredStickelbergerCarrier
    (U := U) (S := S) (ClassP := ClassP) principal stickelberger)

/-- The conversion law in its submodule form: every integral
Stickelberger multiple lies in the unit range. -/
theorem smul_mem_unitRange (theta : stickelberger.ideal) (s : S) :
    (theta : IntegralPadicGroupAlgebra p Delta) • s ∈
      LinearMap.range carrier.unitInclusion :=
  ⟨carrier.convertedUnit theta s,
    carrier.stickelberger_conversion theta s⟩

/-- The exactness field exposes that a converted Stickelberger multiple
maps to zero in the class carrier. -/
theorem classProjection_smul_eq_zero
    (theta : stickelberger.ideal) (s : S) :
    carrier.classProjection
        ((theta : IntegralPadicGroupAlgebra p Delta) • s) = 0 := by
  rw [← carrier.stickelberger_conversion theta s]
  have hrange : carrier.unitInclusion (carrier.convertedUnit theta s) ∈
      LinearMap.range carrier.unitInclusion :=
    ⟨carrier.convertedUnit theta s, rfl⟩
  rw [carrier.exact_at_carrier] at hrange
  exact hrange

/-- The unit produced by conversion is retained as the beta in a
`ClassCarrier` principalization receipt.  This is deliberately not an
`AnnihilatorReceipt`: conversion and annihilation are different laws. -/
def conversionReceipt (theta : stickelberger.ideal) (s : S) :
    ClassCarrier.PrincipalizationReceipt principal
      (carrier.source theta s) (carrier.reduced theta s) where
  beta := carrier.betaOfUnit (carrier.convertedUnit theta s)
  source_eq := carrier.principal_flow theta s

@[simp]
theorem conversionReceipt_beta (theta : stickelberger.ideal) (s : S) :
    (carrier.conversionReceipt theta s).beta =
      carrier.betaOfUnit (carrier.convertedUnit theta s) :=
  rfl

/-- Reading the receipt recovers exactly the principal-flow equation
supplied by the filtered carrier. -/
theorem conversionReceipt_source_eq
    (theta : stickelberger.ideal) (s : S) :
    carrier.source theta s =
      principal (carrier.conversionReceipt theta s).beta *
        carrier.reduced theta s :=
  (carrier.conversionReceipt theta s).source_eq

end FilteredStickelbergerCarrier

end FilteredCarrier

/-! ## The withheld arithmetic representation target -/

/-- The two summands on which the strict route algebra is expected to act.
For a finite pair, this product is the module realization of the direct-sum
notation `Sel_p(K)_chi + D_omega Sel_p(K)_chi*`. -/
abbrev ReflectedSelmerPair
    (SelmerChi : Type uChi) (DOmegaSelmerChiStar : Type uReflected) :=
  SelmerChi × DOmegaSelmerChiStar

section ArithmeticRepresentation

variable {O : Type uO} [CommRing O]
  {Lambda : Type uLambda} [CommRing Lambda]
  {A : Type uA} [Ring A]
  {SelmerChi : Type uChi} {DOmegaSelmerChiStar : Type uReflected}
  [AddCommGroup SelmerChi] [Module O SelmerChi]
  [AddCommGroup DOmegaSelmerChiStar] [Module O DOmegaSelmerChiStar]

/-- Interface for the campaign's next arithmetic summit.  It lists the
expected diagonal base action, the off-diagonal route action, and the two
character projectors.  Providing a value of this structure is the withheld
arithmetic theorem; this module provides no value.

The map is a ring representation because the current strict route API does
not impose an `O`-algebra structure.  Its target consists of `O`-linear
endomorphisms, so the scalar-linearity demanded by the arithmetic action is
still explicit. -/
structure ArithmeticRepresentation
    (base : Lambda →+* A)
    (route chiProjector reflectedProjector : A) where
  rho : A →+* Module.End O
    (ReflectedSelmerPair SelmerChi DOmegaSelmerChiStar)
  chiBaseAction : Lambda →+* Module.End O SelmerChi
  reflectedBaseAction : Lambda →+* Module.End O DOmegaSelmerChiStar
  rho_base : ∀ a x y,
    rho (base a) (x, y) =
      (chiBaseAction a x, reflectedBaseAction a y)
  routeChiToReflected : SelmerChi →ₗ[O] DOmegaSelmerChiStar
  routeReflectedToChi : DOmegaSelmerChiStar →ₗ[O] SelmerChi
  rho_route : ∀ x y,
    rho route (x, y) =
      (routeReflectedToChi y, routeChiToReflected x)
  rho_chiProjector : ∀ x y,
    rho chiProjector (x, y) = (x, 0)
  rho_reflectedProjector : ∀ x y,
    rho reflectedProjector (x, y) = (0, y)

namespace ArithmeticRepresentation

variable {base : Lambda →+* A}
  {route chiProjector reflectedProjector : A}
  (representation : ArithmeticRepresentation
    (O := O) (Lambda := Lambda) (A := A)
    (SelmerChi := SelmerChi)
    (DOmegaSelmerChiStar := DOmegaSelmerChiStar)
    base route chiProjector reflectedProjector)

/-- The closed-route action forced by the representation laws.  It is the
two route composites; it is not asserted to be the identity. -/
theorem rho_routeSquared (x : SelmerChi) (y : DOmegaSelmerChiStar) :
    representation.rho (route ^ 2) (x, y) =
      (representation.routeReflectedToChi
          (representation.routeChiToReflected x),
        representation.routeChiToReflected
          (representation.routeReflectedToChi y)) := by
  rw [map_pow]
  change representation.rho route
      (representation.rho route (x, y)) = _
  rw [representation.rho_route, representation.rho_route]

end ArithmeticRepresentation

section StrictRoute

variable [RouteAlgebra.HasSharp Lambda]

/-- The arithmetic representation interface specialized to the actual
strict route algebra `Lambda[R; sharp]`. -/
abbrev StrictRouteArithmeticRepresentation
    (chiProjector reflectedProjector : Lambda) :=
  ArithmeticRepresentation
    (O := O) (Lambda := Lambda) (A := RouteAlgebra.Route Lambda)
    (SelmerChi := SelmerChi)
    (DOmegaSelmerChiStar := DOmegaSelmerChiStar)
    (SkewPolynomial.CRingHom :
      Lambda →+* RouteAlgebra.Route Lambda)
    (SkewPolynomial.X : RouteAlgebra.Route Lambda)
    (SkewPolynomial.C chiProjector)
    (SkewPolynomial.C reflectedProjector)

/-- Named, uninhabited proposition for the withheld representation theorem
over the strict route algebra. -/
def WithheldStrictRouteArithmeticRepresentation
    (chiProjector reflectedProjector : Lambda) : Prop :=
  Nonempty
    (StrictRouteArithmeticRepresentation
      (O := O) (Lambda := Lambda)
      (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar)
      chiProjector reflectedProjector)

/-- On any eventual strict-route representation, the named central closed
route acts by the two return composites. -/
theorem StrictRouteArithmeticRepresentation.rho_closedRoute
    {chiProjector reflectedProjector : Lambda}
    (representation : StrictRouteArithmeticRepresentation
      (O := O) (Lambda := Lambda)
      (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar)
      chiProjector reflectedProjector)
    (x : SelmerChi) (y : DOmegaSelmerChiStar) :
    representation.rho (RouteAlgebra.closedRoute (Lambda := Lambda)) (x, y) =
      (representation.routeReflectedToChi
          (representation.routeChiToReflected x),
        representation.routeChiToReflected
          (representation.routeReflectedToChi y)) := by
  simpa only [RouteAlgebra.closedRoute] using
    representation.rho_routeSquared x y

end StrictRoute

end ArithmeticRepresentation

section TeichmullerRepresentationTarget

variable {p : ℕ} [Fact p.Prime]
  {Delta : Type uDelta} [CommGroup Delta] [Fintype Delta]
  [Invertible (Fintype.card Delta : PadicInt p)]
  {SelmerChi : Type uChi} {DOmegaSelmerChiStar : Type uReflected}
  [AddCommGroup SelmerChi] [Module (PadicInt p) SelmerChi]
  [AddCommGroup DOmegaSelmerChiStar]
  [Module (PadicInt p) DOmegaSelmerChiStar]

/-- The campaign's named next summit, with the actual Teichmuller-twisted
strict route algebra and its `chi`/`chi*` projectors substituted into the
generic representation interface.  This proposition is intentionally not
proved here. -/
def ReflectedSelmerArithmeticRepresentationTarget
    (omega chi : InvolutiveBase.Character (PadicInt p) Delta) : Prop := by
  letI : RouteAlgebra.HasSharp (IntegralPadicGroupAlgebra p Delta) :=
    RouteAlgebra.teichmullerSharp omega
  exact WithheldStrictRouteArithmeticRepresentation
    (O := PadicInt p) (Lambda := IntegralPadicGroupAlgebra p Delta)
    (SelmerChi := SelmerChi)
    (DOmegaSelmerChiStar := DOmegaSelmerChiStar)
    (InvolutiveBase.characterIdempotent chi)
    (InvolutiveBase.characterIdempotent
      (InvolutiveBase.reflectedCharacter omega chi))

end TeichmullerRepresentationTarget

end Fermat.Conservation.LinkingInterfaces
