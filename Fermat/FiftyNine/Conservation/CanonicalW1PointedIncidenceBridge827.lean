/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Comparing the canonical W1 boundary with pointed incidence at 827

The inhabited pointed incidence at `827` uses one selected local coordinate,
whereas W2 uses the complete `827` orbit together with lambda localization.
On the reflected character seat, Fourier equivariance proves that the kernel
of the selected coordinate is exactly the kernel of all 58 orbit coordinates.

Consequently every lawful W2 annihilator test, pulled back along genuine
lambda localization, lands in the one-dimensional obstruction line of the
inhabited pointed incidence.  This is the strongest comparison furnished by
the present exactness package.  It does not say that pullback is injective:
that missing local-global detection statement is precisely why pointed
incidence alone cannot prove that every W2 test is represented by an actual
primal Selmer test.

There is an important type-level diagnostic here.  The repository currently
uses the ambient, unprojected `LambdaRootsContinuousH1` as W2's local
codomain.  The bridge detects all tests on that ambient object exactly when
lambda localization is onto the entire object, a much stronger statement
than the reflected local quotient/character seat requested by
`7A-ARTIN-READ.md`.  The equivalence below records that overlarge-codomain
fact; it is not advertised as the intended Poitou--Tate theorem.  Refining
the local type to the reflected seat is future interface work.

No reciprocity law, Poitou--Tate premise, provider, certificate, or selected
lift is introduced.
-/
import Fermat.FiftyNine.Conservation.AlgebraicPointedIncidence827
import Fermat.FiftyNine.Conservation.CanonicalConjugatePairIncidence827
import Fermat.FiftyNine.Conservation.CanonicalW1PoitouTateReduction827

open scoped BigOperators NumberField

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace Fermat.FiftyNine.Conservation.CanonicalW1PointedIncidenceBridge827

open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.TatePairing
open AlgebraicPointedIncidence827
open ArbitraryUnitRawTameCarrierBridge827
open ArbitraryUnitTameOrbitSilence827
open CanonicalConjugatePairIncidence827
open CanonicalFullOrbitLocalPairing827
open CanonicalGlobalTameLedgerIrregular827
open CanonicalIrregularMode827
open CanonicalW1LambdaBoundary827
open CanonicalW1PoitouTateReduction827
open ContinuousKummerTateLocalization59
open CyclotomicSelmerAction59
open DetectorWitness827
open ExplicitTameOrbitReciprocity827
open FermatFactorArtinFourierBoundary827
open LambdaOrbitAffineKernelCriterion827
open LambdaOrbitLocalizationFiber827
open LocalKummerFrobeniusFactorization827
open KummerFrobeniusRead827
open NormalizedContinuousKummerPairing59
open NormalizedContinuousReadout59
open PointedTateIncidence
open PrimalFourierNonvanishing827
open SplitPrimeFourier827
open StrictTameOrbitClassFactorization827
open UlamReadout827
open VostokovLocalization59
open WildOrbitBoundaryComparison827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
private theorem oldPrimal59_nsmul_eq_zero
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59) :
    59 • x = 0 := by
  apply Subtype.ext
  exact SelmerEigenspace.p_nsmul_eq_zero x.1

noncomputable local instance instOldPrimal59ModuleZMod :
    Module (ZMod 59)
      (OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
        irregularCharacter59) :=
  AddCommGroup.zmodModule oldPrimal59_nsmul_eq_zero

noncomputable local instance instQRelaxedReflectedDual827ModuleZMod :
    Module (ZMod 59)
      (QRelaxedReflectedDual827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59) :=
  AddCommGroup.zmodModule
    (qRelaxedReflectedDual827_nsmul_eq_zero
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59)

/-- Every genuine reflected-character class has a full orbit profile equal
to the inverse-reflected character times its selected coordinate. -/
theorem relaxedOrbitValuation827_eq_character_mul_selected
    (tau : GaloisIndex59)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59) :
    relaxedOrbitValuation827 K tau y.1 =
      (((reducedCharacter59
        (InvolutiveBase.reflectedCharacter
          canonicalTeichmullerCharacter59 irregularCharacter59))⁻¹ tau :
          (ZMod 59)ˣ) : ZMod 59) *
        reflectedPointedLocalization827
          (cyclotomicQRelaxedSelmerRepresentation827 K)
          canonicalTeichmullerCharacter59 irregularCharacter59
          (tameOrbitBasePlace827 (K := K)) y := by
  let rhoQ := cyclotomicQRelaxedSelmerRepresentation827 K
  have hprojector :
      qRelaxedReflectedProjector827 rhoQ
          canonicalTeichmullerCharacter59 irregularCharacter59 y.1 = y := by
    apply Subtype.ext
    exact characterProjectorAt_eq_self_of_mem rhoQ
      (InvolutiveBase.reflectedCharacter
        canonicalTeichmullerCharacter59 irregularCharacter59)
      y.1 y.2
  have horbit :=
    (normalizedQLocalizationEquivariance827 K
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K))).projected_coordinate_orbit tau y.1
  rw [hprojector] at horbit
  have hplace :
      orbitSupportPlace827 K tau =
        indexedPlaceOrbitEquiv827 K
          (tameOrbitBasePlace827 (K := K)) tau := by
    apply Subtype.ext
    rfl
  change supportValuationAt (orbitSupportPlace827 K tau) y.1 = _
  rw [hplace]
  exact horbit

/-- The same covariance in the normalized full-orbit profile notation. -/
theorem relaxedOrbitValuation827_eq_profile_mul_selected
    (tau : GaloisIndex59)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59) :
    relaxedOrbitValuation827 K tau y.1 =
      normalizedFullOrbitEigenprofileCoordinates827
          canonicalTeichmullerCharacter59 irregularCharacter59 tau *
        reflectedPointedLocalization827
          (cyclotomicQRelaxedSelmerRepresentation827 K)
          canonicalTeichmullerCharacter59 irregularCharacter59
          (tameOrbitBasePlace827 (K := K)) y := by
  exact relaxedOrbitValuation827_eq_character_mul_selected tau y

/-- The complete tame-orbit boundary of an arbitrary reflected eigenspace
class is its selected coordinate times the local Frobenius functional on the
actual irregular primal test space.  Unlike the older normalized-profile
theorem, this statement requires no normalization and no chosen fiber point. -/
theorem seatedOrbitBoundaryFunctional827_eq_selected_mul_localFrobenius
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59)
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59) :
    seatedOrbitBoundaryFunctional827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 y x =
      reflectedPointedLocalization827
          (cyclotomicQRelaxedSelmerRepresentation827 K)
          canonicalTeichmullerCharacter59 irregularCharacter59
          (tameOrbitBasePlace827 (K := K)) y *
        localKummerFrobeniusModeFortyFourLinearMap827 K x.1 := by
  rw [seatedOrbitBoundaryFunctional827_eq_strictTameOrbitFunctional827,
    strictTameOrbitFunctional827_apply]
  let selected :=
    reflectedPointedLocalization827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K)) y
  have hFourier :
      (∑ tau : GaloisIndex59,
        strictOrbitResidueWave827 K x.1 tau *
          normalizedFullOrbitEigenprofileCoordinates827
            canonicalTeichmullerCharacter59 irregularCharacter59 tau) =
        -fourierCoefficient (strictOrbitResidueWave827 K x.1)
          (powerCharacter59 44) := by
    calc
      (∑ tau : GaloisIndex59,
          strictOrbitResidueWave827 K x.1 tau *
            normalizedFullOrbitEigenprofileCoordinates827
              canonicalTeichmullerCharacter59 irregularCharacter59 tau) =
          ∑ tau : GaloisIndex59,
            strictOrbitResidueWave827 K x.1 tau *
              characterFunction (powerCharacter59 14) tau := by
        apply Finset.sum_congr rfl
        intro tau _
        change _ * characterFunction
            (inverseReflectedResidueCharacter827
              canonicalTeichmullerCharacter59 irregularCharacter59) tau = _
        rw [inverseReflectedResidueCharacter827_canonical_irregular_eq_powerFourteen]
      _ = -fourierCoefficient (strictOrbitResidueWave827 K x.1)
            (powerCharacter59 44) := by
        rw [← powerCharacter59_fortyFour_inv]
        unfold fourierCoefficient
        rw [show (58 : ZMod 59)⁻¹ = -1 by decide +kernel +revert]
        simp only [neg_mul, one_mul, neg_neg, characterFunction,
          MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
        apply Finset.sum_congr rfl
        intro tau _
        ring
  calc
    (∑ tau : GaloisIndex59, rawTameOrbitReading827 K tau x.1 y.1) =
        ∑ tau : GaloisIndex59,
          strictOrbitResidueWave827 K x.1 tau *
            relaxedOrbitValuation827 K tau y.1 := by
      apply Finset.sum_congr rfl
      intro tau _
      exact rawTameOrbitReading827_eq_strictResidueWave_mul_relaxedValuation
        K tau x.1 y.1
    _ = ∑ tau : GaloisIndex59,
          strictOrbitResidueWave827 K x.1 tau *
            (normalizedFullOrbitEigenprofileCoordinates827
              canonicalTeichmullerCharacter59 irregularCharacter59 tau *
                selected) := by
      apply Finset.sum_congr rfl
      intro tau _
      rw [relaxedOrbitValuation827_eq_profile_mul_selected]
    _ = (∑ tau : GaloisIndex59,
          strictOrbitResidueWave827 K x.1 tau *
            normalizedFullOrbitEigenprofileCoordinates827
              canonicalTeichmullerCharacter59 irregularCharacter59 tau) *
          selected := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro tau _
      ring
    _ = (-fourierCoefficient (strictOrbitResidueWave827 K x.1)
          (powerCharacter59 44)) * selected := by
      exact congrArg (fun z : ZMod 59 ↦ z * selected) hFourier
    _ = selected *
        localKummerFrobeniusModeFortyFourLinearMap827 K x.1 := by
      rw [localKummerFrobeniusModeFortyFourLinearMap827_apply,
        strictOrbitFrobeniusExponentWave827_eq_residueWave]
      ring

/-- On the reflected eigenspace, vanishing of all 58 orbit coordinates is
equivalent to vanishing of the one selected pointed coordinate. -/
theorem fullOrbitValuationLocalization827_eq_zero_iff_selected_eq_zero
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59) :
    fullOrbitValuationLocalization827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 y = 0 ↔
      reflectedPointedLocalization827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59
        (tameOrbitBasePlace827 (K := K)) y = 0 := by
  constructor
  · intro hall
    have hone := congrFun hall (1 : GaloisIndex59)
    rw [fullOrbitValuationLocalization827_apply,
      relaxedOrbitValuation827_eq_character_mul_selected] at hone
    simpa using hone
  · intro hselected
    funext tau
    rw [fullOrbitValuationLocalization827_apply,
      relaxedOrbitValuation827_eq_character_mul_selected,
      hselected, mul_zero]
    rfl

/-- Thus W2's full-orbit-invisible reflected adjustment space is literally
the reflected kernel in the already inhabited pointed incidence. -/
theorem fullOrbitValuationKernel827_eq_reflectedG827 :
    FullOrbitValuationKernel827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 =
      ReflectedG827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59
        (tameOrbitBasePlace827 (K := K)) := by
  ext y
  rw [LinearMap.mem_ker, LinearMap.mem_ker,
    fullOrbitValuationLocalizationLinear827_apply]
  exact fullOrbitValuationLocalization827_eq_zero_iff_selected_eq_zero y

/-- Pull a W2 lambda-local annihilator test back to the actual reflected
q-relaxed global Selmer space. -/
noncomputable def w1BoundaryTestGlobalPullback827 :
    CanonicalW1LambdaBoundaryTestSpace827 (K := K) →ₗ[ZMod 59]
      Module.Dual (ZMod 59)
        (QRelaxedReflectedDual827
          (cyclotomicQRelaxedSelmerRepresentation827 K)
          canonicalTeichmullerCharacter59 irregularCharacter59) :=
  (lambdaReflectedLocalizationLinear827 (K := K)
    canonicalTeichmullerCharacter59 irregularCharacter59).dualMap.comp
      (CanonicalW1LambdaBoundaryTestSpace827 (K := K)).subtype

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
@[simp]
theorem w1BoundaryTestGlobalPullback827_apply
    (phi : CanonicalW1LambdaBoundaryTestSpace827 (K := K))
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59) :
    w1BoundaryTestGlobalPullback827 (K := K) phi y =
      phi.1 (lambdaReflectedLocalization827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 y) :=
  rfl

/-- Every such pullback vanishes on the reflected kernel of the selected
coordinate.  The proof uses the newly identified equality of the pointed
and full-orbit kernels. -/
theorem w1BoundaryTestGlobalPullback827_mem_reflectedRestriction_ker
    (phi : CanonicalW1LambdaBoundaryTestSpace827 (K := K)) :
    w1BoundaryTestGlobalPullback827 (K := K) phi ∈
      LinearMap.ker
        (reflectedGToF827
          (cyclotomicQRelaxedSelmerRepresentation827 K)
          canonicalTeichmullerCharacter59 irregularCharacter59
          (tameOrbitBasePlace827 (K := K))).dualMap := by
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro y
  rw [LinearMap.zero_apply]
  change phi.1
      (lambdaReflectedLocalization827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 y.1) = 0
  have hfull : y.1 ∈
      FullOrbitValuationKernel827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 := by
    rw [fullOrbitValuationKernel827_eq_reflectedG827]
    exact y.2
  exact (Submodule.mem_dualAnnihilator phi.1).mp phi.2 _
    ⟨⟨y.1, hfull⟩, rfl⟩

/-- The one-dimensional obstruction line in the inhabited canonical pointed
incidence. -/
abbrev CanonicalPointedObstructionLine827 :=
  LinearMap.range
    ((canonicalConjugatePairPointedIncidence827 (K := K))
      |>.toPoitouTateFiveTerm.connecting)

/-- Existing exactness now places every pulled-back W2 test in the actual
pointed obstruction line. -/
theorem w1BoundaryTestGlobalPullback827_mem_pointedObstructionLine
    (phi : CanonicalW1LambdaBoundaryTestSpace827 (K := K)) :
    w1BoundaryTestGlobalPullback827 (K := K) phi ∈
      CanonicalPointedObstructionLine827 (K := K) := by
  have hker :=
    w1BoundaryTestGlobalPullback827_mem_reflectedRestriction_ker
      (K := K) phi
  have hexact := LinearMap.exact_iff.mp
    (canonicalConjugatePairPointedIncidence827
      (K := K)).exact_at_reflected
  rw [hexact] at hker
  exact hker

/-- The canonical map from all W2 annihilator tests into the obstruction line
of the already inhabited pointed incidence. -/
noncomputable def w1BoundaryTestsToPointedObstructionLine827 :
    CanonicalW1LambdaBoundaryTestSpace827 (K := K) →ₗ[ZMod 59]
      CanonicalPointedObstructionLine827 (K := K) :=
  (w1BoundaryTestGlobalPullback827 (K := K)).codRestrict
    (CanonicalPointedObstructionLine827 (K := K))
    (w1BoundaryTestGlobalPullback827_mem_pointedObstructionLine (K := K))

@[simp]
theorem w1BoundaryTestsToPointedObstructionLine827_apply_coe
    (phi : CanonicalW1LambdaBoundaryTestSpace827 (K := K)) :
    (w1BoundaryTestsToPointedObstructionLine827 (K := K) phi).1 =
      w1BoundaryTestGlobalPullback827 (K := K) phi :=
  rfl

/-- **Overlarge-codomain diagnostic.**  The pointed-incidence bridge
detects every W2 annihilator test if and only if genuine reflected
q-relaxed lambda localization is onto the current complete ambient local
`H¹` type.  The forward direction works because every element of the kernel of
the dual localization automatically annihilates the smaller
full-orbit-kernel image, hence already lies in the W2 test space.

The inhabited one-coordinate incidence proves neither side of this
equivalence; it only receives the pullback after localization.  This theorem
is an exact description of the current API, not a claim that full ambient
`H¹` surjectivity is the cheapest or mathematically intended PT input. -/
theorem w1BoundaryTestsToPointedObstructionLine827_injective_iff_lambda_surjective :
    Function.Injective
        (w1BoundaryTestsToPointedObstructionLine827 (K := K)) ↔
      Function.Surjective
        (lambdaReflectedLocalizationLinear827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59) := by
  let T := lambdaReflectedLocalizationLinear827 (K := K)
    canonicalTeichmullerCharacter59 irregularCharacter59
  constructor
  · intro hbridge
    apply LinearMap.dualMap_injective_iff.mp
    intro f g hfg
    have hdmap : T.dualMap (f - g) = 0 := by
      rw [map_sub, hfg, sub_self]
    have hdmem : f - g ∈
        (LinearMap.range
          (lambdaOnFullOrbitKernel827 (K := K)
            canonicalTeichmullerCharacter59 irregularCharacter59)).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro r hr
      obtain ⟨z, rfl⟩ := hr
      have hz := LinearMap.congr_fun hdmap z.1
      change (f - g)
        (lambdaReflectedLocalizationLinear827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 z.1) = 0 at hz
      exact hz
    let phi : CanonicalW1LambdaBoundaryTestSpace827 (K := K) :=
      ⟨f - g, hdmem⟩
    have hphiZero :
        w1BoundaryTestsToPointedObstructionLine827 (K := K) phi = 0 := by
      apply Subtype.ext
      exact hdmap
    have hphi : phi = 0 := by
      apply hbridge
      simpa using hphiZero
    have hd : f - g = 0 := congrArg Subtype.val hphi
    exact sub_eq_zero.mp hd
  · intro hlambda
    have hdual : Function.Injective T.dualMap :=
      LinearMap.dualMap_injective_iff.mpr hlambda
    intro phi psi hphi
    apply Subtype.ext
    apply hdual
    exact congrArg Subtype.val hphi

/-- The genuine local Frobenius functional restricted to the actual
irregular primal Selmer test space. -/
noncomputable def irregularPrimalFrobeniusFunctional827 :
    Module.Dual (ZMod 59)
      (OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
        irregularCharacter59) :=
  (localKummerFrobeniusModeFortyFourLinearMap827 K).comp
    (irregularPrimalInclusion59 K)

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
@[simp]
theorem irregularPrimalFrobeniusFunctional827_apply
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59) :
    irregularPrimalFrobeniusFunctional827 (K := K) x =
      localKummerFrobeniusModeFortyFourLinearMap827 K x.1 :=
  rfl

/-! ## The honest wild-plus-827 Poitou--Tate local term -/

/-- Actual simultaneous localization of a reflected q-relaxed global class:
its complete lambda-local `H¹` value and its selected `827` coordinate. -/
noncomputable def lambdaPointedLocalization827 :
    QRelaxedReflectedDual827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59 →ₗ[ZMod 59]
      (LambdaRootsContinuousH1 K × ZMod 59) :=
  (lambdaReflectedLocalizationLinear827 (K := K)
    canonicalTeichmullerCharacter59 irregularCharacter59).prod
      (reflectedPointedLocalization827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59
        (tameOrbitBasePlace827 (K := K)))

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
@[simp]
theorem lambdaPointedLocalization827_apply
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59) :
    lambdaPointedLocalization827 (K := K) y =
      (lambdaReflectedLocalization827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 y,
        reflectedPointedLocalization827
          (cyclotomicQRelaxedSelmerRepresentation827 K)
          canonicalTeichmullerCharacter59 irregularCharacter59
          (tameOrbitBasePlace827 (K := K)) y) :=
  rfl

/-- The compiler-visible ambient two-charge boundary map modeled on
`7A-ARTIN-READ` and evaluated on the actual primal test space.  Its first term
is the lambda-local cup functional; its second is the selected `827` charge
read through local Frobenius.  Its lambda factor is still the repository's
unprojected ambient `H¹`; the final PT interface should restrict this factor
to the reflected local quotient/character seat. -/
noncomputable def lambdaPointedPoitouTateBoundary827 :
    (LambdaRootsContinuousH1 K × ZMod 59) →ₗ[ZMod 59]
      Module.Dual (ZMod 59)
        (OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
          irregularCharacter59) where
  toFun state :=
    (irregularPrimalLambdaTestMap827 (K := K)).flip state.1 +
      state.2 • irregularPrimalFrobeniusFunctional827 (K := K)
  map_add' left right := by
    ext x
    simp
    ring
  map_smul' a state := by
    ext x
    simp
    ring

@[simp]
theorem lambdaPointedPoitouTateBoundary827_apply
    (state : LambdaRootsContinuousH1 K × ZMod 59)
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59) :
    lambdaPointedPoitouTateBoundary827 (K := K) state x =
      irregularPrimalLambdaTestMap827 (K := K) x state.1 +
        state.2 * irregularPrimalFrobeniusFunctional827 (K := K) x :=
  rfl

/-- The already implemented global reciprocity law proves the easy half of
the genuine Poitou--Tate statement: every simultaneous global localization
has zero total boundary on the entire actual primal test space. -/
theorem lambdaPointedLocalization827_range_le_poitouTateBoundary_ker
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59)) :
    LinearMap.range (lambdaPointedLocalization827 (K := K)) ≤
      LinearMap.ker (lambdaPointedPoitouTateBoundary827 (K := K)) := by
  rintro _ ⟨y, rfl⟩
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro x
  rw [lambdaPointedLocalization827_apply,
    lambdaPointedPoitouTateBoundary827_apply]
  change normalizedInflationReadout59 K
      (lambdaContinuousCup59 K
        (lambdaPrimalFactorOfGlobalKummer59 (K := K) (toKummerClass x))
        (lambdaReflectedFactorOfGlobalKummer59 (K := K)
          (toKummerClassAt y))) + _ = 0
  rw [← normalizedLambdaGlobalPairing59_eq_localized_factor_cup,
    ← seatedWildBoundaryFunctional59_apply]
  have hWild := LinearMap.congr_fun
    (seatedWildBoundaryFunctional59_eq_neg_orbit (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59 reciprocity y) x
  rw [hWild, LinearMap.neg_apply,
    seatedOrbitBoundaryFunctional827_eq_selected_mul_localFrobenius,
    irregularPrimalFrobeniusFunctional827_apply]
  ring

/-- Because reciprocity proves `range ≤ ker`, the full PT exactness statement
`range(localization) = ker(boundary)` is now equivalent to just the missing
lifting direction.  This literal reverse inclusion, rather than the old
one-coordinate incidence, is the concrete theorem still required. -/
theorem lambdaPointedLocalization827_range_eq_ker_iff_kernel_lifts
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59)) :
    LinearMap.range (lambdaPointedLocalization827 (K := K)) =
        LinearMap.ker (lambdaPointedPoitouTateBoundary827 (K := K)) ↔
      LinearMap.ker (lambdaPointedPoitouTateBoundary827 (K := K)) ≤
        LinearMap.range (lambdaPointedLocalization827 (K := K)) := by
  constructor
  · intro h
    rw [h]
  · intro h
    exact le_antisymm
      (lambdaPointedLocalization827_range_le_poitouTateBoundary_ker
        reciprocity)
      h

/-- PT exactness produces a prescribed lambda-local lift once an `827`
charge has been shown to cancel its boundary on every primal test.  This is
the direct, non-selected fiber statement from `7A-ARTIN-READ`. -/
theorem exists_reflected_lift_of_pt_kernel_lifts_of_boundary_cancels
    (kernel_lifts :
      LinearMap.ker (lambdaPointedPoitouTateBoundary827 (K := K)) ≤
        LinearMap.range (lambdaPointedLocalization827 (K := K)))
    (r : LambdaRootsContinuousH1 K) (a : ZMod 59)
    (cancels : lambdaPointedPoitouTateBoundary827 (K := K) (r, a) = 0) :
    ∃ y : QRelaxedReflectedDual827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59,
      lambdaReflectedLocalization827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 y = r ∧
        reflectedPointedLocalization827
          (cyclotomicQRelaxedSelmerRepresentation827 K)
          canonicalTeichmullerCharacter59 irregularCharacter59
          (tameOrbitBasePlace827 (K := K)) y = a := by
  have hker : (r, a) ∈
      LinearMap.ker (lambdaPointedPoitouTateBoundary827 (K := K)) :=
    LinearMap.mem_ker.mpr cancels
  obtain ⟨y, hy⟩ := kernel_lifts hker
  refine ⟨y, ?_, ?_⟩
  · exact congrArg Prod.fst hy
  · exact congrArg Prod.snd hy

/-- At the prescribed W1 reflected factor and normalized selected coordinate
`1`, the two-charge PT boundary is literally W1's receipt functional plus
the normalized local Frobenius functional. -/
theorem lambdaPointedPoitouTateBoundary827_receipt_one :
    lambdaPointedPoitouTateBoundary827 (K := K)
        ((twistedLambdaCupReceipt59 K).reflected, 1) =
      w1ReceiptPrimalBoundaryFunctional827 (K := K) +
        irregularPrimalFrobeniusFunctional827 (K := K) := by
  apply LinearMap.ext
  intro x
  simp only [lambdaPointedPoitouTateBoundary827_apply, one_mul,
    LinearMap.add_apply]
  rfl

/-- Hence the prescribed two-charge boundary vanishes exactly when the
existing map-level Kummer--Artin cancellation equality holds on the entire
actual primal test space. -/
theorem lambdaPointedPoitouTateBoundary827_receipt_one_eq_zero_iff :
    lambdaPointedPoitouTateBoundary827 (K := K)
        ((twistedLambdaCupReceipt59 K).reflected, 1) = 0 ↔
      w1ReceiptPrimalBoundaryFunctional827 (K := K) =
        -irregularPrimalFrobeniusFunctional827 (K := K) := by
  rw [lambdaPointedPoitouTateBoundary827_receipt_one]
  constructor
  · exact eq_neg_of_add_eq_zero_left
  · intro h
    rw [h, neg_add_cancel]

/-- **Direct PT consumer for W2.**  The missing reverse exactness inclusion
for the genuine wild-plus-`827` boundary, together with the existing
map-level Kummer--Artin cancellation target, produces a nonempty W1+W3
compatible fiber.  No surjectivity of the oversized abstract dual-test map
and no selected lift are needed. -/
theorem w1w3CompatibleFiber827_nonempty_of_pt_kernel_lifts_of_kummerArtin
    (kernel_lifts :
      LinearMap.ker (lambdaPointedPoitouTateBoundary827 (K := K)) ≤
        LinearMap.range (lambdaPointedLocalization827 (K := K)))
    (kummerArtin_cancels :
      w1ReceiptPrimalBoundaryFunctional827 (K := K) =
        -irregularPrimalFrobeniusFunctional827 (K := K)) :
    Nonempty (W1W3CompatibleFiber827 (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59) := by
  have hcancels :
      lambdaPointedPoitouTateBoundary827 (K := K)
        ((twistedLambdaCupReceipt59 K).reflected, 1) = 0 :=
    (lambdaPointedPoitouTateBoundary827_receipt_one_eq_zero_iff
      (K := K)).2 kummerArtin_cancels
  obtain ⟨y, hlambda, hselected⟩ :=
    exists_reflected_lift_of_pt_kernel_lifts_of_boundary_cancels
      (K := K) kernel_lifts (twistedLambdaCupReceipt59 K).reflected 1 hcancels
  refine ⟨⟨y, ?_⟩⟩
  rw [lambdaOrbitLocalizationLinear827_apply,
    w1w3LocalizationTarget827]
  apply Prod.ext
  · exact hlambda
  · funext tau
    change relaxedOrbitValuation827 K tau y.1 =
      normalizedFullOrbitEigenprofileCoordinates827
        canonicalTeichmullerCharacter59 irregularCharacter59 tau
    rw [relaxedOrbitValuation827_eq_profile_mul_selected, hselected,
      mul_one]

/-- The canonical connecting map, with its codomain restricted to the
actual pointed obstruction line. -/
noncomputable def canonicalPointedConnectingToObstructionLine827 :
    ZMod 59 →ₗ[ZMod 59] CanonicalPointedObstructionLine827 (K := K) :=
  ((canonicalConjugatePairPointedIncidence827 (K := K))
    |>.toPoitouTateFiveTerm.connecting).rangeRestrict

/-- After genuine global reciprocity, pulling an actual primal lambda test
back to the reflected global carrier gives the pointed connecting functional
at the negative local Frobenius reading. -/
theorem w1BoundaryTestGlobalPullback827_primal_eq_connecting_frobenius
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59))
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59) :
    w1BoundaryTestGlobalPullback827 (K := K)
        (irregularPrimalToW1BoundaryTests827 (K := K) reciprocity x) =
      ((canonicalConjugatePairPointedIncidence827 (K := K))
        |>.toPoitouTateFiveTerm.connecting)
          (-irregularPrimalFrobeniusFunctional827 (K := K) x) := by
  apply LinearMap.ext
  intro y
  rw [w1BoundaryTestGlobalPullback827_apply,
    irregularPrimalToW1BoundaryTests827_apply_coe,
    irregularPrimalLambdaTestMap827_apply]
  change normalizedInflationReadout59 K
      (lambdaContinuousCup59 K
        (lambdaPrimalFactorOfGlobalKummer59 (K := K) (toKummerClass x))
        (lambdaReflectedFactorOfGlobalKummer59 (K := K)
          (toKummerClassAt y))) = _
  rw [← normalizedLambdaGlobalPairing59_eq_localized_factor_cup,
    ← seatedWildBoundaryFunctional59_apply]
  have hWild := LinearMap.congr_fun
    (seatedWildBoundaryFunctional59_eq_neg_orbit (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59 reciprocity y) x
  rw [hWild, LinearMap.neg_apply,
    seatedOrbitBoundaryFunctional827_eq_selected_mul_localFrobenius,
    PointedTateIncidence827.connecting_apply,
    irregularPrimalFrobeniusFunctional827_apply]
  ring

/-- Map-level form of the same comparison.  The actual-primal-to-W2 map,
followed by the canonical pointed-incidence bridge, is exactly negative
local Frobenius followed by the canonical connecting map. -/
theorem w1BoundaryTestsToPointedObstructionLine827_comp_primal_eq
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59)) :
    (w1BoundaryTestsToPointedObstructionLine827 (K := K)).comp
        (irregularPrimalToW1BoundaryTests827 (K := K) reciprocity) =
      (canonicalPointedConnectingToObstructionLine827 (K := K)).comp
        (-irregularPrimalFrobeniusFunctional827 (K := K)) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact w1BoundaryTestGlobalPullback827_primal_eq_connecting_frobenius
    reciprocity x

/-- The canonical pointed connecting map is injective.  This is a genuine
consequence of the already inhabited incidence and its proved nonzero
selected reflected localization. -/
theorem canonicalPointedConnectingToObstructionLine827_injective :
    Function.Injective
      (canonicalPointedConnectingToObstructionLine827 (K := K)) := by
  have hloc :
      reflectedPointedLocalization827
          (cyclotomicQRelaxedSelmerRepresentation827 K)
          canonicalTeichmullerCharacter59 irregularCharacter59
          (tameOrbitBasePlace827 (K := K)) ≠ 0 := by
    rw [← reflectedBoundaryFunctional827_eq_reflectedPointedLocalization827]
    exact canonicalConjugatePairBoundaryFunctional827_ne_zero (K := K)
  have hconnecting : Function.Injective
      ((canonicalConjugatePairPointedIncidence827 (K := K))
        |>.toPoitouTateFiveTerm.connecting) := by
    exact reflectedCoordinatePairing827_flip_injective
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K)) hloc
  intro a b hab
  apply hconnecting
  exact congrArg Subtype.val hab

/-- The pointed obstruction line really is one-dimensional; this is derived
from injectivity of its actual connecting map, not assumed by dimension. -/
theorem canonicalPointedObstructionLine827_finrank_eq_one :
    Module.finrank (ZMod 59)
      (CanonicalPointedObstructionLine827 (K := K)) = 1 := by
  let connecting :=
    (canonicalConjugatePairPointedIncidence827 (K := K))
      |>.toPoitouTateFiveTerm.connecting
  have hinjective : Function.Injective connecting := by
    intro a b hab
    apply canonicalPointedConnectingToObstructionLine827_injective (K := K)
    apply Subtype.ext
    exact hab
  calc
    Module.finrank (ZMod 59)
        (CanonicalPointedObstructionLine827 (K := K)) =
      Module.finrank (ZMod 59) (ZMod 59) :=
        LinearMap.finrank_range_of_inj hinjective
    _ = 1 := by simp

/-- Pure linear-algebra reduction: if pointed pullback detects W2 tests and
the actual-primal composite reaches a nonzero point of the one-dimensional
obstruction line, then every W2 test is represented by an actual primal
test. -/
theorem irregularPrimalToW1BoundaryTests827_surjective_of_pointed_bridge
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59))
    (bridge_injective : Function.Injective
      (w1BoundaryTestsToPointedObstructionLine827 (K := K)))
    (composite_ne_zero :
      (w1BoundaryTestsToPointedObstructionLine827 (K := K)).comp
          (irregularPrimalToW1BoundaryTests827 (K := K) reciprocity) ≠ 0) :
    Function.Surjective
      (irregularPrimalToW1BoundaryTests827 (K := K) reciprocity) := by
  have composite_surjective : Function.Surjective
      ((w1BoundaryTestsToPointedObstructionLine827 (K := K)).comp
        (irregularPrimalToW1BoundaryTests827 (K := K) reciprocity)) :=
    surjective_of_nonzero_of_finrank_eq_one
      (canonicalPointedObstructionLine827_finrank_eq_one (K := K))
      composite_ne_zero
  intro phi
  obtain ⟨x, hx⟩ := composite_surjective
    (w1BoundaryTestsToPointedObstructionLine827 (K := K) phi)
  refine ⟨x, ?_⟩
  apply bridge_injective
  exact hx

/-- A sufficient compiler-visible producer reduction for the current
ambient W2 test space.  The desired W2
representation follows from two concrete statements:

* genuine q-relaxed reflected localization is onto the complete current
  ambient lambda-local `H¹` object (the diagnostic faithfulness gap left by
  pointed incidence);
* the actual irregular-primal local Frobenius functional is nonzero (the
  already identified W4/W7 nonvanishing seam).

The canonical incidence, Fourier kernel comparison, and map-level
Kummer--Frobenius identity discharge everything else.  This is deliberately
not presented as the intended cheapest PT hypothesis: the proper reflected
local quotient/seat has not yet been introduced in the current API. -/
theorem irregularPrimalToW1BoundaryTests827_surjective_of_lambda_and_frobenius
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59))
    (lambda_surjective : Function.Surjective
      (lambdaReflectedLocalizationLinear827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59))
    (frobenius_ne_zero :
      irregularPrimalFrobeniusFunctional827 (K := K) ≠ 0) :
    Function.Surjective
      (irregularPrimalToW1BoundaryTests827 (K := K) reciprocity) := by
  have hbridge : Function.Injective
      (w1BoundaryTestsToPointedObstructionLine827 (K := K)) :=
    (w1BoundaryTestsToPointedObstructionLine827_injective_iff_lambda_surjective
      (K := K)).2 lambda_surjective
  apply irregularPrimalToW1BoundaryTests827_surjective_of_pointed_bridge
    reciprocity hbridge
  rw [w1BoundaryTestsToPointedObstructionLine827_comp_primal_eq reciprocity]
  intro hzero
  apply frobenius_ne_zero
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun hzero x
  have hconnecting :=
    canonicalPointedConnectingToObstructionLine827_injective (K := K)
  have hxzero :
      -irregularPrimalFrobeniusFunctional827 (K := K) x = 0 := by
    apply hconnecting
    simpa using hx
  simpa using congrArg Neg.neg hxzero

/-! ## Axiom guards

The kernel comparison, exactness reductions, and both consumers use only
Lean's standard quotient/classical axioms.  In particular this module adds
no provider, certificate, or arithmetic postulate. -/

/--
info: 'Fermat.FiftyNine.Conservation.CanonicalW1PointedIncidenceBridge827.fullOrbitValuationKernel827_eq_reflectedG827' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fullOrbitValuationKernel827_eq_reflectedG827

/--
info: 'Fermat.FiftyNine.Conservation.CanonicalW1PointedIncidenceBridge827.w1BoundaryTestsToPointedObstructionLine827_injective_iff_lambda_surjective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms w1BoundaryTestsToPointedObstructionLine827_injective_iff_lambda_surjective

/--
info: 'Fermat.FiftyNine.Conservation.CanonicalW1PointedIncidenceBridge827.lambdaPointedLocalization827_range_le_poitouTateBoundary_ker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms lambdaPointedLocalization827_range_le_poitouTateBoundary_ker

/--
info: 'Fermat.FiftyNine.Conservation.CanonicalW1PointedIncidenceBridge827.lambdaPointedLocalization827_range_eq_ker_iff_kernel_lifts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms lambdaPointedLocalization827_range_eq_ker_iff_kernel_lifts

/--
info: 'Fermat.FiftyNine.Conservation.CanonicalW1PointedIncidenceBridge827.w1w3CompatibleFiber827_nonempty_of_pt_kernel_lifts_of_kummerArtin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms w1w3CompatibleFiber827_nonempty_of_pt_kernel_lifts_of_kummerArtin

/--
info: 'Fermat.FiftyNine.Conservation.CanonicalW1PointedIncidenceBridge827.irregularPrimalToW1BoundaryTests827_surjective_of_lambda_and_frobenius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms irregularPrimalToW1BoundaryTests827_surjective_of_lambda_and_frobenius

end Fermat.FiftyNine.Conservation.CanonicalW1PointedIncidenceBridge827
