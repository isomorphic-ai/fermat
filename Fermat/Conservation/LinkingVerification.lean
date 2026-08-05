/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Executable audit for the twisted linking stage

This non-imported leaf checks the W1--W5 public surfaces, the intended
proof-value dependency direction, and the standard-axiom boundary.  In
particular, strict-route perfect return is refuted upstream and is obtained
only through the explicit swap quotient map.
-/
import Fermat.Conservation.GuardDependsOn
import Fermat.Conservation.LinkingInterfaces
import Fermat.Conservation.SwapQuotient
import Fermat.Conservation.TransverseAnnihilator

open Fermat.Conservation

/-! ## Public linking surface -/

#check InvolutiveBase.TeichmullerData
#check InvolutiveBase.GroupAlgebra
#check InvolutiveBase.hash
#check InvolutiveBase.hash_apply
#check InvolutiveBase.hash_hash
#check InvolutiveBase.reflectionPairing
#check InvolutiveBase.reflection_conservation_law
#check InvolutiveBase.reflectedCharacter
#check InvolutiveBase.characterIdempotent
#check InvolutiveBase.characterIdempotent_isIdempotent
#check InvolutiveBase.hash_characterIdempotent
#check InvolutiveBase.hash_trivialCharacterIdempotent
#check InvolutiveBase.plusProjector
#check InvolutiveBase.minusProjector
#check InvolutiveBase.plusProjector_isIdempotent
#check InvolutiveBase.minusProjector_isIdempotent
#check InvolutiveBase.hash_conjugationElement
#check InvolutiveBase.plus_minus_projectors_exchanged

#check RouteAlgebra.HasSharp
#check RouteAlgebra.teichmullerSharp
#check RouteAlgebra.mathlibSkewPolynomialRoute
#check RouteAlgebra.Route
#check RouteAlgebra.route_covariance
#check RouteAlgebra.closedRoute
#check RouteAlgebra.closedRoute_central
#check RouteAlgebra.closedRoute_ne_one
#check RouteAlgebra.CanonicalPathPresentation
#check RouteAlgebra.CanonicalPathPresentation.closedAtChi
#check RouteAlgebra.CanonicalPathPresentation.closedAtReflected
#check RouteAlgebra.BaseCorner
#check RouteAlgebra.RouteCorner
#check RouteAlgebra.routeCorner_coeff_odd_eq_zero
#check RouteAlgebra.cornerClosedRoute
#check RouteAlgebra.cornerPolynomialMap
#check RouteAlgebra.cornerToPolynomial
#check RouteAlgebra.cornerPolynomialEquiv
#check RouteAlgebra.cornerPolynomialEquiv_X
#check RouteAlgebra.teichmullerSharp_characterIdempotent
#check RouteAlgebra.characterCornerPolynomialEquiv

#check SwapQuotient.swapIdeal
#check SwapQuotient.Swap
#check SwapQuotient.quotientMap
#check SwapQuotient.generator
#check SwapQuotient.coefficient
#check SwapQuotient.quotientMap_closedRoute
#check SwapQuotient.generator_sq
#check SwapQuotient.generator_coefficient
#check SwapQuotient.flowElement
#check SwapQuotient.flowElement_two
#check SwapQuotient.piCommon
#check SwapQuotient.piDifference
#check SwapQuotient.piCommon_add_piDifference
#check SwapQuotient.piCommon_idempotent
#check SwapQuotient.piDifference_idempotent
#check SwapQuotient.piCommon_piDifference_orthogonal
#check SwapQuotient.swapLinear
#check SwapQuotient.swapLinear_sq
#check SwapQuotient.commonDifference
#check SwapQuotient.commonDifference_swap
#check SwapQuotient.commonProjector_formula
#check SwapQuotient.differenceProjector_formula
#check SwapQuotient.flowOperator
#check SwapQuotient.flowOperator_apply
#check SwapQuotient.flowOperator_two

#check TransverseAnnihilator.CornerService.BezoutCertificate
#check TransverseAnnihilator.CornerService.eq_zero_of_annihilates_of_bezout
#check TransverseAnnihilator.CornerService.bezout_identity_in_ambient
#check TransverseAnnihilator.CornerService.eq_zero_in_idempotentCorner
#check TransverseAnnihilator.CornerService.LivelockCarrier
#check TransverseAnnihilator.CornerService.livelockCarrier_subsingleton_iff
#check TransverseAnnihilator.CornerService.livelockCarrier_nontrivial_iff
#check TransverseAnnihilator.CornerService.CornerLivelockChannel
#check TransverseAnnihilator.CornerService.nonempty_cornerLivelockChannel_iff
#check TransverseAnnihilator.breaksCycle_iff_polynomialGCD_eq_one
#check TransverseAnnihilator.polynomial_livelockCarrier_subsingleton_iff
#check TransverseAnnihilator.nonempty_polynomial_cornerLivelockChannel_iff
#check TransverseAnnihilator.eq_zero_of_cycle_and_transverse_gcd_eq_one

#check LinkingInterfaces.IntegralPadicGroupAlgebra
#check LinkingInterfaces.IntegralStickelbergerIdeal
#check LinkingInterfaces.IntegralStickelbergerIdeal.SharpTransformationGuard
#check LinkingInterfaces.sharp_trivialProjector_eq_omegaProjector
#check LinkingInterfaces.FilteredStickelbergerCarrier
#check LinkingInterfaces.FilteredStickelbergerCarrier.smul_mem_unitRange
#check LinkingInterfaces.FilteredStickelbergerCarrier.classProjection_smul_eq_zero
#check LinkingInterfaces.FilteredStickelbergerCarrier.conversionReceipt
#check LinkingInterfaces.StrictRouteArithmeticRepresentation
#check LinkingInterfaces.WithheldStrictRouteArithmeticRepresentation
#check LinkingInterfaces.ReflectedSelmerArithmeticRepresentationTarget

/-! ## Proof-value wiring -/

#guard_depends_on InvolutiveBase.hash_hash,
  InvolutiveBase.hashHom_comp_self
#guard_depends_on InvolutiveBase.reflection_conservation_law,
  InvolutiveBase.reflectionPairing
#guard_depends_on InvolutiveBase.characterIdempotent_isIdempotent,
  InvolutiveBase.groupAverage_isIdempotent
#guard_depends_on InvolutiveBase.hash_characterIdempotent,
  InvolutiveBase.reflectedCharacter
#guard_depends_on InvolutiveBase.hash_trivialCharacterIdempotent,
  InvolutiveBase.hash_characterIdempotent
#guard_depends_on InvolutiveBase.plus_minus_projectors_exchanged,
  InvolutiveBase.hash_conjugationElement

#guard_depends_on RouteAlgebra.closedRoute_central,
  RouteAlgebra.phi_sq
#guard_depends_on RouteAlgebra.closedRoute_ne_one,
  SkewPolynomial.coeff_monomial
#guard_depends_on RouteAlgebra.routeCorner_coeff_odd_eq_zero,
  RouteAlgebra.odd_smul
#guard_depends_on RouteAlgebra.cornerPolynomialMap_surjective,
  RouteAlgebra.routeCorner_coeff_odd_eq_zero
#guard_depends_on RouteAlgebra.cornerPolynomialEquiv,
  RouteAlgebra.cornerPolynomialMap_surjective
#guard_depends_on RouteAlgebra.cornerPolynomialEquiv_X,
  RouteAlgebra.cornerPolynomialMap
#guard_depends_on RouteAlgebra.characterCornerPolynomialEquiv,
  RouteAlgebra.cornerPolynomialEquiv
#guard_depends_on RouteAlgebra.characterCornerPolynomialEquiv,
  InvolutiveBase.hash_characterIdempotent

#guard_depends_on SwapQuotient.quotientMap_closedRoute,
  TwoSidedIdeal.subset_span
#guard_depends_on SwapQuotient.generator_sq,
  SwapQuotient.quotientMap_closedRoute
#guard_depends_on SwapQuotient.piCommon_idempotent,
  SwapQuotient.generator_sq
#guard_depends_on SwapQuotient.piDifference_idempotent,
  SwapQuotient.generator_sq
#guard_depends_on SwapQuotient.piCommon_piDifference_orthogonal,
  SwapQuotient.generator_sq
#guard_depends_on SwapQuotient.flowElement_two,
  SwapQuotient.flowElement
#guard_depends_on SwapQuotient.commonDifference_swap,
  SwapQuotient.swapLinear
#guard_depends_on SwapQuotient.commonProjector_formula,
  SwapQuotient.commonProjector
#guard_depends_on SwapQuotient.differenceProjector_formula,
  SwapQuotient.differenceProjector
#guard_depends_on SwapQuotient.flowOperator_apply,
  Interaction.TwoAccount.step
#guard_depends_on SwapQuotient.flowOperator_two,
  Interaction.TwoAccount.step_two_eq_swap

#guard_depends_on
  TransverseAnnihilator.eq_zero_of_cycle_and_transverse_gcd_eq_one,
  TransverseAnnihilator.CornerService.eq_zero_of_annihilates_of_bezout
#guard_depends_on
  TransverseAnnihilator.CornerService.eq_zero_in_idempotentCorner,
  TransverseAnnihilator.CornerService.eq_zero_of_annihilates_of_bezout
#guard_depends_on
  TransverseAnnihilator.eq_zero_of_cycle_and_transverse_gcd_eq_one,
  TransverseAnnihilator.breaksCycle_iff_polynomialGCD_eq_one
#guard_depends_on
  TransverseAnnihilator.polynomial_livelockCarrier_subsingleton_iff,
  TransverseAnnihilator.CornerService.livelockCarrier_subsingleton_iff

#guard_depends_on
  LinkingInterfaces.sharp_trivialProjector_eq_omegaProjector,
  InvolutiveBase.hash_trivialCharacterIdempotent
#guard_depends_on
  LinkingInterfaces.FilteredStickelbergerCarrier.smul_mem_unitRange,
  LinkingInterfaces.FilteredStickelbergerCarrier.stickelberger_conversion
#guard_depends_on
  LinkingInterfaces.FilteredStickelbergerCarrier.classProjection_smul_eq_zero,
  LinkingInterfaces.FilteredStickelbergerCarrier.exact_at_carrier
#guard_depends_on
  LinkingInterfaces.FilteredStickelbergerCarrier.conversionReceipt,
  ClassCarrier.PrincipalizationReceipt.mk
#guard_depends_on
  LinkingInterfaces.FilteredStickelbergerCarrier.conversionReceipt_source_eq,
  ClassCarrier.PrincipalizationReceipt.source_eq
#guard_depends_on
  LinkingInterfaces.ArithmeticRepresentation.rho_routeSquared,
  LinkingInterfaces.ArithmeticRepresentation.rho_route
#guard_depends_on
  LinkingInterfaces.StrictRouteArithmeticRepresentation.rho_closedRoute,
  LinkingInterfaces.ArithmeticRepresentation.rho_routeSquared

/-! ## Exhaustive axiom boundary

Every declaration created below each W1--W5 namespace is inspected.  This is
exhaustive rather than a hand-maintained theorem sample, so newly added public
declarations are automatically audited as well. -/

open Lean Elab Command

/-- Fail if any declaration under a namespace prefix uses an axiom beyond
Lean's standard extensionality, choice, and quotient-soundness boundary. -/
elab "#guard_standard_axioms_prefix " p:ident : command => do
  let env ← getEnv
  let auditedPrefix := p.getId
  let allowed : Array Name :=
    #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations :=
    env.constants.toList
      |>.map Prod.fst
      |>.filter auditedPrefix.isPrefixOf
  for declaration in declarations do
    let axioms ← Lean.collectAxioms declaration
    let unexpected := axioms.filter fun ax =>
      !allowed.contains ax
    unless unexpected.isEmpty do
      throwError
        "{declaration} depends on nonstandard axioms: {unexpected}"

#guard_standard_axioms_prefix Fermat.Conservation.InvolutiveBase
#guard_standard_axioms_prefix Fermat.Conservation.RouteAlgebra
#guard_standard_axioms_prefix Fermat.Conservation.SwapQuotient
#guard_standard_axioms_prefix Fermat.Conservation.TransverseAnnihilator.CornerService
#guard_standard_axioms_prefix Fermat.Conservation.LinkingInterfaces
