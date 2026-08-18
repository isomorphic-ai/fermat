/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Focused verification of the relation-7A Kummer--Artin route

This non-imported executable audit leaf covers only the newly exposed route:

* W1 retains the complete nonzero normalized twisted-lambda cup receipt;
* W3 constructs the normalized inverse-reflected profile on all 58 places,
  and the normalized reflected fiber realizes that profile on an actual
  global `827`-relaxed carrier;
* the W4 algebra turns same-line nonvanishing into a unique unit scalar;
* W1's two retained degree-one factors are reached exactly by localizing
  explicit global Kummer representatives, including the normalized value-one
  reading of their transported cup;
* W2 is now a concrete `ZMod 59`-linear lambda-plus-827 localization map
  from the actual reflected q-relaxed Selmer carrier to the product of the
  roots-valued lambda `H¹` seat and all 58 supported-valuation coordinates;
  its prescribed W1+W3 fiber is defined without asserting an inhabitant;
* the normalized wild and complete `827` boundaries are literal linear maps
  on one genuine seated primal Selmer space; under `GlobalReciprocityLaw`
  they are exact negatives, have equal kernels, and lie in one explicit
  common line, which has rank one as soon as the orbit map is nonzero;
* the concrete tame-orbit functional factors uniquely through the actual
  class gauge exactly at the global-unit-silence boundary;
* seated global reciprocity balances that orbit against the lambda row;
* the inverse-oriented even-plus-primitive Fourier shape has zero mode 43;
* every actual global-unit raw residue wave has that shape and therefore
  has zero inverse-oriented mode-43 projection;
* the raw wave is identified with the genuine canonical tame context and
  with the actual strict-Selmer `unitInclusion` pairing, including the
  mandatory global-root factor and inverse place orientation;
* the realized profile makes the genuine strict tame functional silent on
  every ring unit and every `UnitModP` class, thereby constructing its
  unique class-level readout;
* W7 identifies orbit silence with relation 7A once that produced readout
  is proved faithful at the single Fermat-selected class; this faithfulness
  is further reduced to seating in the genuine chi=15 class line,
  one-dimensionality of that line, and readout nonvanishing on it.
* independently, every genuine tame row of the Fermat-factor strict class is
  factored through its representative-independent residue wave, so the full
  normalized orbit is exactly the negative mode-44 Fourier coefficient; the
  direction `7A -> coefficient = 0` is unconditional;
* W5 now proves that the normalized 58-row profile determines both the
  complete strict tame functional and any factorizing class readout,
  independently of the chosen point of the normalized reflected fiber;
  moreover the readout/Fourier identity holds for every strict Selmer input,
  so the mode-44 coefficient descends through the genuine class gauge and
  vanishes unconditionally on its kernel.
* the allocated plus root is now unconditionally fixed by the complete odd
  class projector: genuine class-map naturality identifies cyclotomic `-1`
  with the allocated minus root, and relation 7D makes that root the negative
  of the plus root;
* exact chi=15 seating is isolated as vanishing of the derived complement
  between the complete odd projector and the selected irregular projector,
  both on the allocated plus root and directly on the W7 class gauge.

The checks deliberately keep the remaining lanes separate.  The common
Hom-space and common-line comparison now exist on the real seated Selmer
space: for one reflected carrier, `GlobalReciprocityLaw` gives literal map
equality `wild = -orbit`, kernel equality, and common-line membership.
Three inputs are still honest seams: reciprocity itself is not yet produced;
the concrete W1+W3 localization fiber is not yet proved nonempty; and neither
boundary is yet proved nonzero on the actual seated primal test space.  The
W2 boundary is now exact and machine-readable:

`Nonempty W1W3CompatibleFiber827`

is equivalent to existence of a point in the already retained normalized W3
fiber whose actual lambda localization is W1's prescribed reflected class.
The equivalence does not prove that such a point exists.  Thus the rank-one
unit comparison is exact once seated nonvanishing is supplied, but it is not
an unconditional Poitou--Tate lift.

Within W7, pointwise faithfulness of the produced readout is now displayed
as one concrete mode-44 Fourier zero-reflection statement for the actual
Fermat factor.  Its reverse implication is proved unconditionally.  The
missing forward reflection is the exact target of the Kummer--Artin
factorization/comparison.
The odd character seat is proved, but the sharper chi=15 seat is not: its
remaining arithmetic obligation is precisely that the allocated plus root's
odd-minus-chi=15 complement vanishes.  Poitou--Tate alone does not supply
that Kummer--Artin character-support comparison.
This file does not import the monolithic exponent-59 verifier.
-/
import Fermat.Conservation.GuardDependsOn
import Fermat.Conservation.OneDimensionalUnitProportionality
import Fermat.FiftyNine.Conservation.TwistedLambdaCupReceipt59
import Fermat.FiftyNine.Conservation.NormalizedFullOrbitEigenprofile827
import Fermat.FiftyNine.Conservation.StrictTameOrbitClassFactorization827
import Fermat.FiftyNine.Conservation.SeatedTameOrbitReciprocityBalance827
import Fermat.FiftyNine.Conservation.InverseEvenPrimitiveFourierSilence827
import Fermat.FiftyNine.Conservation.ArbitraryUnitOrbitDecomposition827
import Fermat.FiftyNine.Conservation.ArbitraryUnitFourierSilence827
import Fermat.FiftyNine.Conservation.ArbitraryUnitLocalReduction827
import Fermat.FiftyNine.Conservation.ArbitraryUnitRawTameCarrierBridge827
import Fermat.FiftyNine.Conservation.SevenAArtinPartialClosure59
import Fermat.FiftyNine.Conservation.UnitSilenceClassReadout827
import Fermat.FiftyNine.Conservation.ArbitraryUnitTameOrbitSilence827
import Fermat.FiftyNine.Conservation.NormalizedFullOrbitGlobalRealization827
import Fermat.FiftyNine.Conservation.NormalizedFullOrbitUnitSilence827
import Fermat.FiftyNine.Conservation.PointwiseFaithfulSevenAReadout827
import Fermat.FiftyNine.Conservation.FermatFactorClassGaugeCharacterBoundary59
import Fermat.FiftyNine.Conservation.CharacterLinePointwiseFaithfulness59
import Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59
import Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827
import Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827
import Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827

/-! ## Public route inventory -/

/-! W1: the retained local cup and its two oriented degree-one factors. -/

#check Fermat.FiftyNine.Conservation.TwistedLambdaCupReceipt59
#check Fermat.FiftyNine.Conservation.TwistedLambdaCupReceipt59.cup_eq
#check Fermat.FiftyNine.Conservation.TwistedLambdaCupReceipt59.cup_ne_zero
#check Fermat.FiftyNine.Conservation.TwistedLambdaCupReceipt59.normalized_reading
#check Fermat.FiftyNine.Conservation.TwistedLambdaCupReceipt59.reading_ne_zero
#check Fermat.FiftyNine.Conservation.twistedLambdaCupReceipt59

/-! W1's retained factors are reached by exact global-to-local transport.
The future lambda-plus-827 lift must match the same reflected factor, not
merely reproduce its scalar reading. -/

#check Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.lambdaPrimalFactorOfGlobalKummer59
#check Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.lambdaReflectedFactorOfGlobalKummer59
#check Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.lambdaPrimalFactorOfGlobalTwistedLambda59_eq_receipt
#check Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.lambdaReflectedFactorOfGlobalPrimitive59_eq_receipt
#check Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.localizedGlobalTwistedLambdaPrimitiveCup59_eq_receipt
#check Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.localizedGlobalTwistedLambdaPrimitiveReading59_eq_one
#check Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.normalizedLambdaGlobalPairing59_eq_localized_factor_cup

/-! W3: the full physical 827 orbit and frozen inverse-reflected
orientation. -/

#check Fermat.FiftyNine.Conservation.inverseReflectedResidueCharacter827_apply
#check Fermat.FiftyNine.Conservation.normalizedFullOrbitEigenprofileCoordinates827_isPureCharacter
#check Fermat.FiftyNine.Conservation.tameOrbitPlace827_one
#check Fermat.FiftyNine.Conservation.cyclotomicPlaceEquiv59_tameOrbitPlace827
#check Fermat.FiftyNine.Conservation.normalizedFullOrbitEigenprofileLedger827_apply
#check Fermat.FiftyNine.Conservation.normalizedFullOrbitEigenprofileLedger827_base
#check Fermat.FiftyNine.Conservation.normalizedFullOrbitEigenprofileLedger827_support
#check Fermat.FiftyNine.Conservation.normalizedFullOrbitEigenprofileLedger827_support_card
#check Fermat.FiftyNine.Conservation.normalizedFullOrbitEigenprofileLedger827_reflected_eigenlaw
#check Fermat.FiftyNine.Conservation.NormalizedFullOrbitEigenprofile827
#check Fermat.FiftyNine.Conservation.normalizedFullOrbitEigenprofile827

/-! The normalized reflected fiber now realizes W3 on an actual global
relaxed carrier.  This is not yet a simultaneous wild/tame PT lift. -/

#check Fermat.FiftyNine.Conservation.NormalizedFullOrbitGlobalRealization827.normalizedReflectedFiber827_relaxedOrbitValuation_eq_profile
#check Fermat.FiftyNine.Conservation.NormalizedFullOrbitGlobalRealization827.normalizedReflectedFiber827_relaxedOrbitValuation_isPureCharacter
#check Fermat.FiftyNine.Conservation.NormalizedFullOrbitGlobalRealization827.exists_relaxedCarrier827_realizing_normalizedFullOrbitEigenprofile

/-! W2 is now exposed as one actual lambda-plus-827 localization map and
its literal W1+W3 fiber.  The two nonemptiness equivalences state the exact
remaining lift problem; neither one asserts that the fiber is inhabited. -/

#check Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.LambdaOrbitLocalizationTarget827
#check Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.lambdaReflectedLocalization827
#check Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.fullOrbitValuationLocalization827
#check Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.lambdaOrbitLocalization827
#check Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.lambdaOrbitLocalizationLinear827
#check Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.w1w3LocalizationTarget827
#check Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.W1W3CompatibleFiber827
#check Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.w1w3CompatibleFiber827_lambda
#check Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.w1w3CompatibleFiber827_fullOrbit
#check Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.w1w3CompatibleFiber827_orbitCoordinate
#check Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.w1w3CompatibleFiber827_toNormalizedReflectedFiber827
#check Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.w1w3CompatibleFiber827_of_normalizedReflectedFiber827
#check Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.w1w3CompatibleFiber827_wildBoundary_eq_receiptCup
#check Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.w1w3CompatibleFiber827_orbitBoundary_eq_strict
#check Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.w1w3CompatibleFiber827_nonempty_iff
#check Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.w1w3CompatibleFiber827_nonempty_iff_exists_normalized_lambda

/-! W4's completed algebraic implication.  The arithmetic same-line
producer remains intentionally outside this theorem. -/

#check Fermat.Conservation.existsUnique_unit_smul_of_mem_finrank_one
#check Fermat.Conservation.eq_zero_of_mem_finrank_one_of_readout_restrict_ne_zero

/-! W4 now lives on the genuine common seated Selmer space.  Under the
explicit reciprocity hypothesis the two maps are exact negatives, hence
have the same kernel and occupy one concrete line.  Only reciprocity,
lambda-plus-827 localization compatibility, and seated nonvanishing remain
outside these theorems. -/

#check Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.seatedWildBoundaryFunctional59
#check Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.seatedOrbitBoundaryFunctional827
#check Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.seatedWildBoundaryFunctional59_eq_receipt_cup_of_localizes
#check Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.seatedOrbitBoundaryFunctional827_eq_strictTameOrbitFunctional827
#check Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.seatedWildBoundaryFunctional59_add_orbit_eq_zero
#check Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.seatedWildBoundaryFunctional59_eq_neg_orbit
#check Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.seatedWildBoundaryFunctional59_ker_eq_orbit_ker
#check Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.wildOrbitCommonLine827
#check Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.seatedOrbitBoundaryFunctional827_mem_commonLine
#check Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.seatedWildBoundaryFunctional59_mem_commonLine_of_reciprocity
#check Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.wildOrbitCommonLine827_finrank_eq_one
#check Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.existsUnique_unit_wild_eq_smul_orbit_of_reciprocity
#check Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.exists_normalized_wildOrbitBoundaryPair827

/-! The concrete full-orbit class-factorization boundary. -/

#check Fermat.FiftyNine.Conservation.StrictTameOrbitClassFactorization827.strictTameOrbitFunctional827
#check Fermat.FiftyNine.Conservation.StrictTameOrbitClassFactorization827.strictTameOrbitFunctional827_apply
#check Fermat.FiftyNine.Conservation.StrictTameOrbitClassFactorization827.unit_silence_strictTameOrbitFunctional827_iff_existsUnique_classReadout

/-! The exact seated reciprocity balance; this records rather than erases
the normalized lambda term. -/

#check Fermat.FiftyNine.Conservation.SeatedTameOrbitReciprocityBalance827.seatedTameOrbitSum827
#check Fermat.FiftyNine.Conservation.SeatedTameOrbitReciprocityBalance827.seatedTameOrbitSum827_eq_neg_normalizedLambda_of_globalReciprocity
#check Fermat.FiftyNine.Conservation.SeatedTameOrbitReciprocityBalance827.seatedTameOrbitSum827_eq_zero_iff_normalizedLambda_eq_zero

/-! The committed finite Fourier half of arbitrary-unit silence. -/

#check Fermat.FiftyNine.Conservation.InverseEvenPrimitiveFourierSilence827.inverseReindex_powerCharacter59_one_eq_fiftySeven
#check Fermat.FiftyNine.Conservation.InverseEvenPrimitiveFourierSilence827.powerCharacter59_fortyThree_negOne
#check Fermat.FiftyNine.Conservation.InverseEvenPrimitiveFourierSilence827.powerCharacter59_fiftySeven_ne_fortyThree
#check Fermat.FiftyNine.Conservation.InverseEvenPrimitiveFourierSilence827.inverseReindex_negOne_invariant
#check Fermat.FiftyNine.Conservation.InverseEvenPrimitiveFourierSilence827.inverseReindex_even_add_primitiveRootMode_eq
#check Fermat.FiftyNine.Conservation.InverseEvenPrimitiveFourierSilence827.inverseEvenPrimitive_powerFortyThree_fourier_eq_zero

/-! The arithmetic global-unit decomposition and its composed raw-tame
mode-43 silence. -/

#check Fermat.FiftyNine.Conservation.ArbitraryUnitOrbitDecomposition827.orbitReductionHom827_unitsComplexConj
#check Fermat.FiftyNine.Conservation.ArbitraryUnitOrbitDecomposition827.exists_rawGlobalUnitOrbitWave827_rootMode_decomposition
#check Fermat.FiftyNine.Conservation.ArbitraryUnitOrbitDecomposition827.fullOrbitUnitReading827_negOne_even
#check Fermat.FiftyNine.Conservation.ArbitraryUnitFourierSilence827.rawGlobalUnitEvenPart827
#check Fermat.FiftyNine.Conservation.ArbitraryUnitFourierSilence827.exists_rawGlobalUnitOrbitWave827_eq_even_add_primitiveRootMode
#check Fermat.FiftyNine.Conservation.ArbitraryUnitFourierSilence827.inverseReindex_rawGlobalUnitOrbitWave827_powerFortyThree_eq_zero
#check Fermat.FiftyNine.Conservation.ArbitraryUnitFourierSilence827.inverseReindex_rawGlobalUnitOrbitWave827_powerFortyThree_characterComponent_eq_zero
#check Fermat.FiftyNine.Conservation.ArbitraryUnitFourierSilence827.inverseReindex_fullOrbitUnitReading827_powerFortyThree_eq_zero

/-! The exact local and carrier comparisons retain the forced inverse
orientation and the global-root coordinate factor. -/

#check Fermat.FiftyNine.Conservation.ArbitraryUnitLocalReduction827.inverseOrientedRawGlobalUnitOrbitWave827
#check Fermat.FiftyNine.Conservation.ArbitraryUnitLocalReduction827.tameContext827_primalResidue_eq_rawGlobalUnitOrbitWave827
#check Fermat.FiftyNine.Conservation.ArbitraryUnitLocalReduction827.tameContext827_value_globalUnit_at_tameOrbitPlace827
#check Fermat.FiftyNine.Conservation.ArbitraryUnitLocalReduction827.canonicalContext827_value_globalUnit_at_tameOrbitPlace827
#check Fermat.FiftyNine.Conservation.ArbitraryUnitLocalReduction827.tameContext827_value_globalUnit_relaxedRepresentative_eq_raw_product
#check Fermat.FiftyNine.Conservation.ArbitraryUnitRawTameCarrierBridge827.ringUnitClass59
#check Fermat.FiftyNine.Conservation.ArbitraryUnitRawTameCarrierBridge827.strictKummerClass59_unitInclusion_ringUnitClass59
#check Fermat.FiftyNine.Conservation.ArbitraryUnitRawTameCarrierBridge827.relaxedOrbitValuation827
#check Fermat.FiftyNine.Conservation.ArbitraryUnitRawTameCarrierBridge827.rawTameOrbitReading827_unitInclusion_eq_orientedRaw_mul_relaxedValuation

/-! The genuine arbitrary-unit sum and strict functional are now silent for
every carrier in the canonical pure reflected seat. -/

#check Fermat.FiftyNine.Conservation.ArbitraryUnitTameOrbitSilence827.inverseReflectedResidueCharacter827_canonical_irregular_eq_powerFourteen
#check Fermat.FiftyNine.Conservation.ArbitraryUnitTameOrbitSilence827.relaxedOrbitValuation827_isPureCharacter_of_eq_normalizedProfile
#check Fermat.FiftyNine.Conservation.ArbitraryUnitTameOrbitSilence827.weightedRelaxedOrbitValuation827_isPureCharacter
#check Fermat.FiftyNine.Conservation.ArbitraryUnitTameOrbitSilence827.sum_rawTameOrbitReading827_unitInclusion_eq_zero_of_pureMode
#check Fermat.FiftyNine.Conservation.ArbitraryUnitTameOrbitSilence827.strictTameOrbitFunctional827_unitInclusion_ringUnitClass59_eq_zero
#check Fermat.FiftyNine.Conservation.ArbitraryUnitTameOrbitSilence827.existsUnique_classReadout_of_relaxedOrbitValuation_isPureCharacter

/-! Unit silence constructs the readout rather than accepting it as input. -/

#check Fermat.FiftyNine.Conservation.UnitSilenceClassReadout827.ringUnitClass59_surjective
#check Fermat.FiftyNine.Conservation.UnitSilenceClassReadout827.existsUnique_classReadout_of_unit_silence
#check Fermat.FiftyNine.Conservation.UnitSilenceClassReadout827.existsUnique_classReadout_of_ringUnit_silence
#check Fermat.FiftyNine.Conservation.UnitSilenceClassReadout827.existsUnique_classReadout_with_kernel_detection_of_unit_silence
#check Fermat.FiftyNine.Conservation.UnitSilenceClassReadout827.existsUnique_classReadout_with_vandiverSevenA_of_unit_silence

/-! The realized W3 carrier simultaneously retains its eigenseat, exact
profile, ring-unit and quotient-unit silence, and unique class readout. -/

#check Fermat.FiftyNine.Conservation.NormalizedFullOrbitUnitSilence827.strictTameOrbitFunctional827_unitInclusion_eq_zero_of_normalizedProfile
#check Fermat.FiftyNine.Conservation.NormalizedFullOrbitUnitSilence827.exists_normalizedFullOrbitProfile_unitSilence_classReadout827

/-! W7's underlying pointwise algebra. -/

#check Fermat.FiftyNine.Conservation.SevenAArtinPartialClosure59.strictTameOrbitFunctional827_eq_zero_iff_classGauge_eq_zero
#check Fermat.FiftyNine.Conservation.SevenAArtinPartialClosure59.fermatFactorClassGaugeMap59_fermatFactorSelmerDifference59
#check Fermat.FiftyNine.Conservation.SevenAArtinPartialClosure59.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_selectedClassGauge59_eq_zero
#check Fermat.FiftyNine.Conservation.SevenAArtinPartialClosure59.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA

/-! The selected class's character seat is reduced to one exact global-unit
range receipt, without pretending that receipt or Artin faithfulness is
already available. -/

#check Fermat.FiftyNine.Conservation.FermatFactorClassGaugeCharacterBoundary59.cyclotomicClassProjector59_selectedClassGauge59_eq_projectedSelmerClass
#check Fermat.FiftyNine.Conservation.FermatFactorClassGaugeCharacterBoundary59.selectedClassGauge59_projector_fixed_iff_projectedClass_eq_class
#check Fermat.FiftyNine.Conservation.FermatFactorClassGaugeCharacterBoundary59.selectedClassGauge59_projector_fixed_iff_difference_mem_unitRange
#check Fermat.FiftyNine.Conservation.FermatFactorClassGaugeCharacterBoundary59.selectedClassGauge59_eq_plusRoot_add_plusRoot
#check Fermat.FiftyNine.Conservation.FermatFactorClassGaugeCharacterBoundary59.selectedClassGauge59_projector_fixed_iff_plusRoot_projector_fixed

/-! The allocated plus root is now genuinely seated in the complete odd
class space.  The final equivalence records exactly what remains before this
can be sharpened to the selected chi=15 line. -/

#check Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.normalizationCorrectionStrictSelmer59_mem_unitRange
#check Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.strictSelmerClassLinearMap59_normalizationCorrection_eq_zero
#check Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.strictSelmerClassLinearMap59_cyclotomicNegOne
#check Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.cyclotomicNegOne_allocatedPlusRoot_eq_allocatedMinusRoot
#check Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.allocatedMinusRoot_eq_neg_allocatedPlusRoot
#check Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.cyclotomicNegOne_allocatedPlusRoot_eq_neg
#check Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.cyclotomicClassMinusProjector59
#check Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.cyclotomicClassMinusProjector59_allocatedPlusRoot
#check Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.cyclotomicNegOne_selectedClassGauge59_eq_neg
#check Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.cyclotomicClassMinusProjector59_selectedClassGauge59
#check Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.cyclotomicClassIrregularComplement59
#check Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.allocatedPlusRoot_eq_irregularProjection_add_complement
#check Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.allocatedPlusRoot_irregularProjector_fixed_iff_complement_eq_zero
#check Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.selectedClassGauge59_irregularProjector_fixed_iff_complement_eq_zero

/-! The produced-readout W7 boundary.  Full injectivity is unnecessary:
only zero reflection at the one Fermat-selected class remains visible. -/

#check Fermat.FiftyNine.Conservation.PointwiseFaithfulSevenAReadout827.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_selectedClassGauge59_eq_zero_of_pointwiseFaithful
#check Fermat.FiftyNine.Conservation.PointwiseFaithfulSevenAReadout827.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA_of_pointwiseFaithful
#check Fermat.FiftyNine.Conservation.PointwiseFaithfulSevenAReadout827.existsUnique_classReadout_with_pointwiseW7_of_unit_silence
#check Fermat.FiftyNine.Conservation.PointwiseFaithfulSevenAReadout827.existsUnique_classReadout_with_pointwiseW7_of_ringUnit_silence
#check Fermat.FiftyNine.Conservation.PointwiseFaithfulSevenAReadout827.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA_of_unit_silence
#check Fermat.FiftyNine.Conservation.PointwiseFaithfulSevenAReadout827.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA_of_ringUnit_silence

/-! The pointwise Artin seam is now a concrete representative-independent
Fourier statement.  Every genuine tame row factors through the strict
residue wave; the normalized orbit is exactly negative mode 44, and the
easy implication from relation 7A is already unconditional. -/

#check Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.strictKummerRepresentative59
#check Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.strictOrbitResidueWave827
#check Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.strictKummerRepresentative59_mk
#check Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.context59_residueCharacter_angularComponent_eq_of_kummer_mk_eq
#check Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.fiftyNine_dvd_valuation_strictKummerRepresentative59
#check Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.rawTameOrbitReading827_eq_strictResidueWave_mul_relaxedValuation
#check Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.strictTameOrbitFunctional827_eq_neg_fourierCoefficient_powerFortyFour

/-! W5 is now representative-independent at both the normalized reflected
fiber and class-gauge levels.  These are all-input statements: the generic
readout/Fourier identity is not specialized to the Fermat-selected class,
and only the zero-reflection converse remains open. -/

#check Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.strictTameOrbitFunctional827_eq_of_normalizedProfile
#check Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.classReadout_eq_of_normalizedProfile
#check Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.classReadout_classGaugeMap59_eq_neg_fourierCoefficient
#check Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.fourierCoefficient_eq_of_classGaugeMap59_eq
#check Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.fourierCoefficient_eq_zero_of_classGaugeMap59_eq_zero

#check Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.classReadout_selectedClassGauge59_eq_neg_fourierCoefficient
#check Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.classReadout_pointwiseFaithful_iff_fourierCoefficient_zero_implies_selectedClassGauge59_eq_zero
#check Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.fourierCoefficient_fermatFactor_eq_zero_of_selectedClassGauge59_eq_zero
#check Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.fourierCoefficient_fermatFactor_eq_zero_of_vandiverSevenA
#check Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.fourierCoefficient_fermatFactor_eq_zero_iff_vandiverSevenA_of_reflects_zero
#check Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.exists_normalizedFullOrbit_w7_of_fourierCoefficient_faithful

/-! The opaque pointwise premise is now decomposed exactly as in the
Kummer--Artin strategy: character seating, rank one, and a nonzero readout
on that genuine projector image. -/

#check Fermat.FiftyNine.Conservation.CharacterLinePointwiseFaithfulness59.irregularClassProjectorZMod59
#check Fermat.FiftyNine.Conservation.CharacterLinePointwiseFaithfulness59.irregularClassCharacterLine59
#check Fermat.FiftyNine.Conservation.CharacterLinePointwiseFaithfulness59.mem_irregularClassCharacterLine59_of_projector_fixed
#check Fermat.FiftyNine.Conservation.CharacterLinePointwiseFaithfulness59.selectedClassGauge59_eq_zero_of_readout_eq_zero_of_characterLine
#check Fermat.FiftyNine.Conservation.CharacterLinePointwiseFaithfulness59.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA_of_characterLine

/-! ## Main endpoint axiom audit -/

/--
info: 'Fermat.FiftyNine.Conservation.twistedLambdaCupReceipt59' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.twistedLambdaCupReceipt59

/--
info: 'Fermat.FiftyNine.Conservation.normalizedFullOrbitEigenprofile827' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.normalizedFullOrbitEigenprofile827

/--
info: 'Fermat.Conservation.existsUnique_unit_smul_of_mem_finrank_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.existsUnique_unit_smul_of_mem_finrank_one

/--
info: 'Fermat.Conservation.eq_zero_of_mem_finrank_one_of_readout_restrict_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.eq_zero_of_mem_finrank_one_of_readout_restrict_ne_zero

/--
info: 'Fermat.FiftyNine.Conservation.StrictTameOrbitClassFactorization827.unit_silence_strictTameOrbitFunctional827_iff_existsUnique_classReadout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.StrictTameOrbitClassFactorization827.unit_silence_strictTameOrbitFunctional827_iff_existsUnique_classReadout

/--
info: 'Fermat.FiftyNine.Conservation.SeatedTameOrbitReciprocityBalance827.seatedTameOrbitSum827_eq_zero_iff_normalizedLambda_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.SeatedTameOrbitReciprocityBalance827.seatedTameOrbitSum827_eq_zero_iff_normalizedLambda_eq_zero

/--
info: 'Fermat.FiftyNine.Conservation.InverseEvenPrimitiveFourierSilence827.inverseEvenPrimitive_powerFortyThree_fourier_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.InverseEvenPrimitiveFourierSilence827.inverseEvenPrimitive_powerFortyThree_fourier_eq_zero

/--
info: 'Fermat.FiftyNine.Conservation.ArbitraryUnitOrbitDecomposition827.exists_rawGlobalUnitOrbitWave827_rootMode_decomposition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.ArbitraryUnitOrbitDecomposition827.exists_rawGlobalUnitOrbitWave827_rootMode_decomposition

/--
info: 'Fermat.FiftyNine.Conservation.ArbitraryUnitFourierSilence827.inverseReindex_rawGlobalUnitOrbitWave827_powerFortyThree_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.ArbitraryUnitFourierSilence827.inverseReindex_rawGlobalUnitOrbitWave827_powerFortyThree_eq_zero

/--
info: 'Fermat.FiftyNine.Conservation.ArbitraryUnitLocalReduction827.canonicalContext827_value_globalUnit_at_tameOrbitPlace827' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.ArbitraryUnitLocalReduction827.canonicalContext827_value_globalUnit_at_tameOrbitPlace827

/--
info: 'Fermat.FiftyNine.Conservation.ArbitraryUnitRawTameCarrierBridge827.rawTameOrbitReading827_unitInclusion_eq_orientedRaw_mul_relaxedValuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.ArbitraryUnitRawTameCarrierBridge827.rawTameOrbitReading827_unitInclusion_eq_orientedRaw_mul_relaxedValuation

/--
info: 'Fermat.FiftyNine.Conservation.UnitSilenceClassReadout827.existsUnique_classReadout_of_ringUnit_silence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.UnitSilenceClassReadout827.existsUnique_classReadout_of_ringUnit_silence

/--
info: 'Fermat.FiftyNine.Conservation.ArbitraryUnitTameOrbitSilence827.strictTameOrbitFunctional827_unitInclusion_ringUnitClass59_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.ArbitraryUnitTameOrbitSilence827.strictTameOrbitFunctional827_unitInclusion_ringUnitClass59_eq_zero

/--
info: 'Fermat.FiftyNine.Conservation.NormalizedFullOrbitGlobalRealization827.exists_relaxedCarrier827_realizing_normalizedFullOrbitEigenprofile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.NormalizedFullOrbitGlobalRealization827.exists_relaxedCarrier827_realizing_normalizedFullOrbitEigenprofile

/--
info: 'Fermat.FiftyNine.Conservation.NormalizedFullOrbitUnitSilence827.exists_normalizedFullOrbitProfile_unitSilence_classReadout827' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.NormalizedFullOrbitUnitSilence827.exists_normalizedFullOrbitProfile_unitSilence_classReadout827

/--
info: 'Fermat.FiftyNine.Conservation.FermatFactorClassGaugeCharacterBoundary59.selectedClassGauge59_projector_fixed_iff_difference_mem_unitRange' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.FermatFactorClassGaugeCharacterBoundary59.selectedClassGauge59_projector_fixed_iff_difference_mem_unitRange

/--
info: 'Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.cyclotomicClassMinusProjector59_allocatedPlusRoot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.cyclotomicClassMinusProjector59_allocatedPlusRoot

/--
info: 'Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.allocatedPlusRoot_irregularProjector_fixed_iff_complement_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.allocatedPlusRoot_irregularProjector_fixed_iff_complement_eq_zero

/--
info: 'Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.selectedClassGauge59_irregularProjector_fixed_iff_complement_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.selectedClassGauge59_irregularProjector_fixed_iff_complement_eq_zero

/--
info: 'Fermat.FiftyNine.Conservation.PointwiseFaithfulSevenAReadout827.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA_of_ringUnit_silence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.PointwiseFaithfulSevenAReadout827.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA_of_ringUnit_silence

/--
info: 'Fermat.FiftyNine.Conservation.SevenAArtinPartialClosure59.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.SevenAArtinPartialClosure59.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA

/--
info: 'Fermat.FiftyNine.Conservation.CharacterLinePointwiseFaithfulness59.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA_of_characterLine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.CharacterLinePointwiseFaithfulness59.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA_of_characterLine

/-! Exact W1 transport, common-boundary comparison, and the concrete
mode-44 boundary remain within Lean's standard quotient/classical axioms. -/

/--
info: 'Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.localizedGlobalTwistedLambdaPrimitiveReading59_eq_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.localizedGlobalTwistedLambdaPrimitiveReading59_eq_one

/--
info: 'Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.seatedWildBoundaryFunctional59_eq_neg_orbit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.seatedWildBoundaryFunctional59_eq_neg_orbit

/--
info: 'Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.seatedWildBoundaryFunctional59_ker_eq_orbit_ker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.seatedWildBoundaryFunctional59_ker_eq_orbit_ker

/--
info: 'Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.wildOrbitCommonLine827_finrank_eq_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.wildOrbitCommonLine827_finrank_eq_one

/--
info: 'Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.existsUnique_unit_wild_eq_smul_orbit_of_reciprocity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.existsUnique_unit_wild_eq_smul_orbit_of_reciprocity

/-! The concrete W2 map and both exact formulations of its unresolved
nonemptiness boundary use only Lean's standard quotient/classical axioms. -/

/--
info: 'Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.lambdaOrbitLocalizationLinear827' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.lambdaOrbitLocalizationLinear827

/--
info: 'Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.w1w3CompatibleFiber827_nonempty_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.w1w3CompatibleFiber827_nonempty_iff

/--
info: 'Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.w1w3CompatibleFiber827_nonempty_iff_exists_normalized_lambda' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.w1w3CompatibleFiber827_nonempty_iff_exists_normalized_lambda

/--
info: 'Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.context59_residueCharacter_angularComponent_eq_of_kummer_mk_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.context59_residueCharacter_angularComponent_eq_of_kummer_mk_eq

/--
info: 'Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.rawTameOrbitReading827_eq_strictResidueWave_mul_relaxedValuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.rawTameOrbitReading827_eq_strictResidueWave_mul_relaxedValuation

/--
info: 'Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.strictTameOrbitFunctional827_eq_neg_fourierCoefficient_powerFortyFour' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.strictTameOrbitFunctional827_eq_neg_fourierCoefficient_powerFortyFour

/-! The W5 representative-independence, generic readout/Fourier identity,
and descent through the actual class gauge also have standard dependencies. -/

/--
info: 'Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.strictTameOrbitFunctional827_eq_of_normalizedProfile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.strictTameOrbitFunctional827_eq_of_normalizedProfile

/--
info: 'Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.classReadout_eq_of_normalizedProfile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.classReadout_eq_of_normalizedProfile

/--
info: 'Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.classReadout_classGaugeMap59_eq_neg_fourierCoefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.classReadout_classGaugeMap59_eq_neg_fourierCoefficient

/--
info: 'Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.fourierCoefficient_eq_of_classGaugeMap59_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.fourierCoefficient_eq_of_classGaugeMap59_eq

/--
info: 'Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.fourierCoefficient_eq_zero_of_classGaugeMap59_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.fourierCoefficient_eq_zero_of_classGaugeMap59_eq_zero

/--
info: 'Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.fourierCoefficient_fermatFactor_eq_zero_of_vandiverSevenA' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.fourierCoefficient_fermatFactor_eq_zero_of_vandiverSevenA

/-! ## Proof-value dependency gates -/

/-! The W1 receipt consumes both the established nonzero cup and its
normalized value-one theorem. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.twistedLambdaCupReceipt59,
  Fermat.FiftyNine.Conservation.NormImageBridge59.twistedLambdaKummerCupH2Class59_ne_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.twistedLambdaCupReceipt59,
  Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.normalizedInflationReadout59_twistedLambdaCup

/-! The concrete W3 receipt consumes both exact full support and the
literal sigma-inverse reflected eigenlaw. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.normalizedFullOrbitEigenprofile827,
  Fermat.FiftyNine.Conservation.normalizedFullOrbitEigenprofileLedger827_support
#guard_depends_on
  Fermat.FiftyNine.Conservation.normalizedFullOrbitEigenprofile827,
  Fermat.FiftyNine.Conservation.normalizedFullOrbitEigenprofileLedger827_reflected_eigenlaw

/-! W4 is genuine one-dimensional linear algebra. -/

#guard_depends_on
  Fermat.Conservation.existsUnique_unit_smul_of_mem_finrank_one,
  exists_smul_eq_of_finrank_eq_one
#guard_depends_on
  Fermat.Conservation.eq_zero_of_mem_finrank_one_of_readout_restrict_ne_zero,
  exists_smul_eq_of_finrank_eq_one

/-! The scalar orbit map reads the genuine raw tame rows, while its exact
factorization theorem uses the actual class-gauge kernel result. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.StrictTameOrbitClassFactorization827.strictTameOrbitFunctional827_apply,
  Fermat.FiftyNine.Conservation.CanonicalFullOrbitLocalPairing827.rawTameOrbitReading827
#guard_depends_on
  Fermat.FiftyNine.Conservation.StrictTameOrbitClassFactorization827.unit_silence_strictTameOrbitFunctional827_iff_existsUnique_classReadout,
  Fermat.FiftyNine.Conservation.FermatFactorClassGaugeSeating59.existsUnique_classReadout_factorization_iff_unit_silence

/-! The seated balance consumes the complete full-orbit reciprocity
criterion, and its zero equivalence consumes that retained balance. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.SeatedTameOrbitReciprocityBalance827.seatedTameOrbitSum827_eq_neg_normalizedLambda_of_globalReciprocity,
  Fermat.FiftyNine.Conservation.FullOrbitGlobalReciprocityCriterion827.globalReciprocityLaw_canonicalFullOrbitLocalPairing827_iff
#guard_depends_on
  Fermat.FiftyNine.Conservation.SeatedTameOrbitReciprocityBalance827.seatedTameOrbitSum827_eq_zero_iff_normalizedLambda_eq_zero,
  Fermat.FiftyNine.Conservation.SeatedTameOrbitReciprocityBalance827.seatedTameOrbitSum827_eq_neg_normalizedLambda_of_globalReciprocity

/-! The Fourier-silence endpoint consumes the exact inverse orientation,
preserved evenness, odd target mode, and separation of modes 57 and 43. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.InverseEvenPrimitiveFourierSilence827.inverseEvenPrimitive_powerFortyThree_fourier_eq_zero,
  Fermat.FiftyNine.Conservation.InverseEvenPrimitiveFourierSilence827.inverseReindex_even_add_primitiveRootMode_eq
#guard_depends_on
  Fermat.FiftyNine.Conservation.InverseEvenPrimitiveFourierSilence827.inverseEvenPrimitive_powerFortyThree_fourier_eq_zero,
  Fermat.FiftyNine.Conservation.InverseEvenPrimitiveFourierSilence827.inverseReindex_negOne_invariant
#guard_depends_on
  Fermat.FiftyNine.Conservation.InverseEvenPrimitiveFourierSilence827.inverseEvenPrimitive_powerFortyThree_fourier_eq_zero,
  Fermat.FiftyNine.Conservation.InverseEvenPrimitiveFourierSilence827.powerCharacter59_fortyThree_negOne
#guard_depends_on
  Fermat.FiftyNine.Conservation.InverseEvenPrimitiveFourierSilence827.inverseEvenPrimitive_powerFortyThree_fourier_eq_zero,
  Fermat.FiftyNine.Conservation.InverseEvenPrimitiveFourierSilence827.powerCharacter59_fiftySeven_ne_fortyThree

/-! The actual arbitrary-unit endpoint consumes both the CM-unit arithmetic
decomposition and the separately proved inverse-oriented Fourier theorem. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.ArbitraryUnitOrbitDecomposition827.exists_rawGlobalUnitOrbitWave827_rootMode_decomposition,
  unit_inv_conj_is_root_of_unity
#guard_depends_on
  Fermat.FiftyNine.Conservation.ArbitraryUnitFourierSilence827.exists_rawGlobalUnitOrbitWave827_eq_even_add_primitiveRootMode,
  Fermat.FiftyNine.Conservation.ArbitraryUnitOrbitDecomposition827.exists_rawGlobalUnitOrbitWave827_rootMode_decomposition
#guard_depends_on
  Fermat.FiftyNine.Conservation.ArbitraryUnitFourierSilence827.inverseReindex_rawGlobalUnitOrbitWave827_powerFortyThree_eq_zero,
  Fermat.FiftyNine.Conservation.ArbitraryUnitFourierSilence827.exists_rawGlobalUnitOrbitWave827_eq_even_add_primitiveRootMode
#guard_depends_on
  Fermat.FiftyNine.Conservation.ArbitraryUnitFourierSilence827.inverseReindex_rawGlobalUnitOrbitWave827_powerFortyThree_eq_zero,
  Fermat.FiftyNine.Conservation.InverseEvenPrimitiveFourierSilence827.inverseEvenPrimitive_powerFortyThree_fourier_eq_zero

/-! The tame comparison really passes through the fixed-root residue
calculation, the global-root normalization, and the actual Selmer carrier. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.ArbitraryUnitLocalReduction827.canonicalContext827_value_globalUnit_at_tameOrbitPlace827,
  Fermat.FiftyNine.Conservation.ArbitraryUnitLocalReduction827.tameContext827_value_globalUnit_at_tameOrbitPlace827
#guard_depends_on
  Fermat.FiftyNine.Conservation.ArbitraryUnitLocalReduction827.canonicalContext827_value_globalUnit_at_tameOrbitPlace827,
  Fermat.FiftyNine.Conservation.CanonicalTameLedger827.tameContext827_value_eq_sigma_mul_context
#guard_depends_on
  Fermat.FiftyNine.Conservation.ArbitraryUnitRawTameCarrierBridge827.rawTameOrbitReading827_unitInclusion_eq_orientedRaw_mul_relaxedValuation,
  Fermat.FiftyNine.Conservation.ArbitraryUnitRawTameCarrierBridge827.rawTameOrbitReading827_unitInclusion_eq_context_value
#guard_depends_on
  Fermat.FiftyNine.Conservation.ArbitraryUnitRawTameCarrierBridge827.rawTameOrbitReading827_unitInclusion_eq_orientedRaw_mul_relaxedValuation,
  Fermat.FiftyNine.Conservation.ArbitraryUnitLocalReduction827.canonicalContext827_value_globalUnit_at_tameOrbitPlace827

/-! Ring-unit silence reaches the quotient through the actual surjective
representative map and then invokes the exact class-factorization theorem. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.UnitSilenceClassReadout827.existsUnique_classReadout_of_ringUnit_silence,
  Fermat.FiftyNine.Conservation.UnitSilenceClassReadout827.ringUnitClass59_surjective
#guard_depends_on
  Fermat.FiftyNine.Conservation.UnitSilenceClassReadout827.existsUnique_classReadout_of_ringUnit_silence,
  Fermat.FiftyNine.Conservation.UnitSilenceClassReadout827.existsUnique_classReadout_of_unit_silence

/-! The genuine arbitrary-unit endpoint consumes both the concrete raw sum
and the strict functional's definition; its readout is then constructed by
the representative-level quotient adapter. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.ArbitraryUnitTameOrbitSilence827.strictTameOrbitFunctional827_unitInclusion_ringUnitClass59_eq_zero,
  Fermat.FiftyNine.Conservation.ArbitraryUnitTameOrbitSilence827.sum_rawTameOrbitReading827_unitInclusion_eq_zero_of_pureMode
#guard_depends_on
  Fermat.FiftyNine.Conservation.ArbitraryUnitTameOrbitSilence827.strictTameOrbitFunctional827_unitInclusion_ringUnitClass59_eq_zero,
  Fermat.FiftyNine.Conservation.StrictTameOrbitClassFactorization827.strictTameOrbitFunctional827_apply
#guard_depends_on
  Fermat.FiftyNine.Conservation.ArbitraryUnitTameOrbitSilence827.existsUnique_classReadout_of_relaxedOrbitValuation_isPureCharacter,
  Fermat.FiftyNine.Conservation.UnitSilenceClassReadout827.existsUnique_classReadout_of_ringUnit_silence

/-! Global W3 realization consumes the retained normalized fiber and its
exact readback theorem. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedFullOrbitGlobalRealization827.exists_relaxedCarrier827_realizing_normalizedFullOrbitEigenprofile,
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairIncidence827.canonicalConjugatePairNormalizedReflectedFiber827_nonempty
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedFullOrbitGlobalRealization827.exists_relaxedCarrier827_realizing_normalizedFullOrbitEigenprofile,
  Fermat.FiftyNine.Conservation.NormalizedFullOrbitGlobalRealization827.normalizedReflectedFiber827_relaxedOrbitValuation_eq_profile

/-! The concrete W2 product map consumes both actual localization legs.
Its sharp nonemptiness equivalence is built in both directions from the
combined fiber and the retained normalized W3 fiber; it does not construct
either side.  Any hypothetical inhabitant then feeds the genuine common
Hom-space maps. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.lambdaOrbitLocalizationLinear827,
  Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.lambdaReflectedLocalization827
#guard_depends_on
  Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.lambdaOrbitLocalizationLinear827,
  Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.fullOrbitValuationLocalization827
#guard_depends_on
  Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.w1w3CompatibleFiber827_toNormalizedReflectedFiber827,
  Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.w1w3CompatibleFiber827_orbitCoordinate
#guard_depends_on
  Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.w1w3CompatibleFiber827_of_normalizedReflectedFiber827,
  Fermat.FiftyNine.Conservation.NormalizedFullOrbitGlobalRealization827.normalizedReflectedFiber827_relaxedOrbitValuation_eq_profile
#guard_depends_on
  Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.w1w3CompatibleFiber827_nonempty_iff_exists_normalized_lambda,
  Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.w1w3CompatibleFiber827_toNormalizedReflectedFiber827
#guard_depends_on
  Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.w1w3CompatibleFiber827_nonempty_iff_exists_normalized_lambda,
  Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.w1w3CompatibleFiber827_of_normalizedReflectedFiber827
#guard_depends_on
  Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.w1w3CompatibleFiber827_wildBoundary_eq_receiptCup,
  Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.seatedWildBoundaryFunctional59_eq_receipt_cup_of_localizes
#guard_depends_on
  Fermat.FiftyNine.Conservation.LambdaOrbitLocalizationFiber827.w1w3CompatibleFiber827_orbitBoundary_eq_strict,
  Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.seatedOrbitBoundaryFunctional827_eq_strictTameOrbitFunctional827

/-! The combined W3/unit-silence receipt really composes realization,
arbitrary-unit cancellation, and quotient readout construction. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedFullOrbitUnitSilence827.exists_normalizedFullOrbitProfile_unitSilence_classReadout827,
  Fermat.FiftyNine.Conservation.NormalizedFullOrbitGlobalRealization827.exists_relaxedCarrier827_realizing_normalizedFullOrbitEigenprofile
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedFullOrbitUnitSilence827.exists_normalizedFullOrbitProfile_unitSilence_classReadout827,
  Fermat.FiftyNine.Conservation.ArbitraryUnitTameOrbitSilence827.strictTameOrbitFunctional827_unitInclusion_ringUnitClass59_eq_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedFullOrbitUnitSilence827.exists_normalizedFullOrbitProfile_unitSilence_classReadout827,
  Fermat.FiftyNine.Conservation.UnitSilenceClassReadout827.existsUnique_classReadout_of_ringUnit_silence

/-! Character seating uses strong projector naturality and reduces fixedness
to the actual unit-range exactness receipt. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.FermatFactorClassGaugeCharacterBoundary59.cyclotomicClassProjector59_selectedClassGauge59_eq_projectedSelmerClass,
  Fermat.FiftyNine.Conservation.CyclotomicSelmerClassNaturality59.strictSelmerClassLinearMap59_characterProjector
#guard_depends_on
  Fermat.FiftyNine.Conservation.FermatFactorClassGaugeCharacterBoundary59.selectedClassGauge59_projector_fixed_iff_difference_mem_unitRange,
  Fermat.FiftyNine.Conservation.FermatFactorClassGaugeCharacterBoundary59.selectedClassGauge59_projector_fixed_iff_projectedClass_eq_class
#guard_depends_on
  Fermat.FiftyNine.Conservation.FermatFactorClassGaugeCharacterBoundary59.selectedClassGauge59_projector_fixed_iff_difference_mem_unitRange,
  Fermat.FiftyNine.Conservation.FermatFactorClassGaugeSeating59.fermatFactorClassGaugeMap59_eq_zero_iff_mem_unitRange

/-! Complete odd seating consumes the genuine conjugation action, the
proved 7D relation, and the literal unit-kernel removal of the normalization
correction.  The chi=15 equivalence then depends on that proved odd seat. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.strictSelmerClassLinearMap59_normalizationCorrection_eq_zero,
  Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.normalizationCorrectionStrictSelmer59_mem_unitRange
#guard_depends_on
  Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.cyclotomicNegOne_allocatedPlusRoot_eq_allocatedMinusRoot,
  Fermat.FiftyNine.Conservation.FermatFactorConjugation59.fermatMinusStrictSelmer59_eq_correction_add_conj
#guard_depends_on
  Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.cyclotomicNegOne_allocatedPlusRoot_eq_allocatedMinusRoot,
  Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.strictSelmerClassLinearMap59_cyclotomicNegOne
#guard_depends_on
  Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.cyclotomicNegOne_allocatedPlusRoot_eq_neg,
  Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.cyclotomicNegOne_allocatedPlusRoot_eq_allocatedMinusRoot
#guard_depends_on
  Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.cyclotomicNegOne_allocatedPlusRoot_eq_neg,
  Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.allocatedMinusRoot_eq_neg_allocatedPlusRoot
#guard_depends_on
  Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.cyclotomicClassMinusProjector59_allocatedPlusRoot,
  Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.cyclotomicNegOne_allocatedPlusRoot_eq_neg
#guard_depends_on
  Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.allocatedPlusRoot_irregularProjector_fixed_iff_complement_eq_zero,
  Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.cyclotomicClassMinusProjector59_allocatedPlusRoot
#guard_depends_on
  Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.cyclotomicNegOne_selectedClassGauge59_eq_neg,
  Fermat.FiftyNine.Conservation.FermatFactorClassGaugeCharacterBoundary59.selectedClassGauge59_eq_plusRoot_add_plusRoot
#guard_depends_on
  Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.cyclotomicNegOne_selectedClassGauge59_eq_neg,
  Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.cyclotomicNegOne_allocatedPlusRoot_eq_neg
#guard_depends_on
  Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.cyclotomicClassMinusProjector59_selectedClassGauge59,
  Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.cyclotomicNegOne_selectedClassGauge59_eq_neg
#guard_depends_on
  Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.selectedClassGauge59_irregularProjector_fixed_iff_complement_eq_zero,
  Fermat.FiftyNine.Conservation.AllocatedPlusRootOddSupport59.cyclotomicClassMinusProjector59_selectedClassGauge59

/-! W7 consumes the concrete class seating, the generic pointwise kernel
comparison, and the established selected-class characterization of 7A. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.SevenAArtinPartialClosure59.fermatFactorClassGaugeMap59_fermatFactorSelmerDifference59,
  Fermat.FiftyNine.Conservation.FermatFactorClassGaugeSeating59.fermatFactorClassGaugeSeating59
#guard_depends_on
  Fermat.FiftyNine.Conservation.SevenAArtinPartialClosure59.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_selectedClassGauge59_eq_zero,
  Fermat.FiftyNine.Conservation.SevenAArtinPartialClosure59.strictTameOrbitFunctional827_eq_zero_iff_classGauge_eq_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.SevenAArtinPartialClosure59.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_selectedClassGauge59_eq_zero,
  Fermat.FiftyNine.Conservation.SevenAArtinPartialClosure59.fermatFactorClassGaugeMap59_fermatFactorSelmerDifference59
#guard_depends_on
  Fermat.FiftyNine.Conservation.SevenAArtinPartialClosure59.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA,
  Fermat.FiftyNine.Conservation.UlamReadout827.selectedClassGauge59_eq_zero_iff_vandiverSevenA

/-! The readout-free W7 endpoint constructs the unique factorization from
ring-unit silence and leaves only pointwise faithfulness to its sharp
consumer theorem. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.PointwiseFaithfulSevenAReadout827.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA_of_ringUnit_silence,
  Fermat.FiftyNine.Conservation.UnitSilenceClassReadout827.existsUnique_classReadout_of_ringUnit_silence
#guard_depends_on
  Fermat.FiftyNine.Conservation.PointwiseFaithfulSevenAReadout827.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA_of_ringUnit_silence,
  Fermat.FiftyNine.Conservation.PointwiseFaithfulSevenAReadout827.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA_of_pointwiseFaithful

/-! The rank-one W7 adapter consumes the actual class projector, the
generic one-dimensional zero-reflection theorem, and the sharp pointwise
W7 endpoint. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.CharacterLinePointwiseFaithfulness59.selectedClassGauge59_eq_zero_of_readout_eq_zero_of_characterLine,
  Fermat.Conservation.eq_zero_of_mem_finrank_one_of_readout_restrict_ne_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.CharacterLinePointwiseFaithfulness59.selectedClassGauge59_eq_zero_of_readout_eq_zero_of_characterLine,
  Fermat.FiftyNine.Conservation.CharacterLinePointwiseFaithfulness59.mem_irregularClassCharacterLine59_of_projector_fixed
#guard_depends_on
  Fermat.FiftyNine.Conservation.CharacterLinePointwiseFaithfulness59.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA_of_characterLine,
  Fermat.FiftyNine.Conservation.CharacterLinePointwiseFaithfulness59.selectedClassGauge59_eq_zero_of_readout_eq_zero_of_characterLine
#guard_depends_on
  Fermat.FiftyNine.Conservation.CharacterLinePointwiseFaithfulness59.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA_of_characterLine,
  Fermat.FiftyNine.Conservation.PointwiseFaithfulSevenAReadout827.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA_of_pointwiseFaithful

/-! Exact W1 transport uses both global-to-local factor identifications and
then consumes the retained normalized cup reading. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.localizedGlobalTwistedLambdaPrimitiveCup59_eq_receipt,
  Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.lambdaPrimalFactorOfGlobalTwistedLambda59_eq_receipt
#guard_depends_on
  Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.localizedGlobalTwistedLambdaPrimitiveCup59_eq_receipt,
  Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.lambdaReflectedFactorOfGlobalPrimitive59_eq_receipt
#guard_depends_on
  Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.localizedGlobalTwistedLambdaPrimitiveReading59_eq_one,
  Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.localizedGlobalTwistedLambdaPrimitiveCup59_eq_receipt

/-! The real common-space comparison consumes the seated reciprocity law.
Map equality then drives kernel equality and line membership, while the unit
comparison consumes both the concrete rank-one line and generic W4 algebra. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.seatedWildBoundaryFunctional59_add_orbit_eq_zero,
  Fermat.FiftyNine.Conservation.SeatedTameOrbitReciprocityBalance827.seatedTameOrbitSum827_eq_neg_normalizedLambda_of_globalReciprocity
#guard_depends_on
  Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.seatedWildBoundaryFunctional59_eq_neg_orbit,
  Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.seatedWildBoundaryFunctional59_add_orbit_eq_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.seatedWildBoundaryFunctional59_ker_eq_orbit_ker,
  Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.seatedWildBoundaryFunctional59_eq_neg_orbit
#guard_depends_on
  Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.seatedWildBoundaryFunctional59_mem_commonLine_of_reciprocity,
  Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.seatedWildBoundaryFunctional59_eq_neg_orbit
#guard_depends_on
  Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.wildOrbitCommonLine827_finrank_eq_one,
  finrank_span_singleton
#guard_depends_on
  Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.existsUnique_unit_wild_eq_smul_orbit_of_reciprocity,
  Fermat.Conservation.existsUnique_unit_smul_of_mem_finrank_one
#guard_depends_on
  Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.existsUnique_unit_wild_eq_smul_orbit_of_reciprocity,
  Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827.wildOrbitCommonLine827_finrank_eq_one

/-! The concrete W7 boundary really descends through Kummer-representative
independence, factors every tame row, assembles the exact mode-44 formula,
and proves the unconditional `7A -> coefficient = 0` direction. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.context59_residueCharacter_angularComponent_eq_of_kummer_mk_eq,
  QuotientGroup.mk'_eq_mk'
#guard_depends_on
  Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.context59_residueCharacter_angularComponent_eq_of_kummer_mk_eq,
  ZModModule.char_nsmul_eq_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.rawTameOrbitReading827_eq_strictResidueWave_mul_relaxedValuation,
  Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.context59_value_eq_ord_mul_residueCharacter_of_dvd_ord_left
#guard_depends_on
  Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.rawTameOrbitReading827_eq_strictResidueWave_mul_relaxedValuation,
  Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.fiftyNine_dvd_valuation_strictKummerRepresentative59
#guard_depends_on
  Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.rawTameOrbitReading827_eq_strictResidueWave_mul_relaxedValuation,
  Fermat.FiftyNine.Conservation.ArbitraryUnitRawTameCarrierBridge827.relaxedOrbitValuation827_eq_representative
#guard_depends_on
  Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.strictTameOrbitFunctional827_eq_neg_fourierCoefficient_powerFortyFour,
  Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.rawTameOrbitReading827_eq_strictResidueWave_mul_relaxedValuation
#guard_depends_on
  Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.strictTameOrbitFunctional827_eq_neg_fourierCoefficient_powerFortyFour,
  Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827.powerCharacter59_fortyFour_inv

/-! W5 removes dependence on a chosen normalized-fiber representative,
then identifies the produced class readout with the same Fourier coefficient
on every strict input.  The two descent consequences really consume the
internally constructed normalized profile/readout rather than a supplied
class-function certificate. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.strictTameOrbitFunctional827_eq_of_normalizedProfile,
  Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.strictTameOrbitFunctional827_eq_neg_fourierCoefficient_powerFortyFour
#guard_depends_on
  Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.classReadout_eq_of_normalizedProfile,
  Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.strictTameOrbitFunctional827_eq_of_normalizedProfile
#guard_depends_on
  Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.classReadout_eq_of_normalizedProfile,
  Fermat.FiftyNine.Conservation.FermatFactorClassGaugeSeating59.fermatFactorClassGaugeMap59_surjective
#guard_depends_on
  Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.classReadout_classGaugeMap59_eq_neg_fourierCoefficient,
  Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.strictTameOrbitFunctional827_eq_neg_fourierCoefficient_powerFortyFour
#guard_depends_on
  Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.fourierCoefficient_eq_of_classGaugeMap59_eq,
  Fermat.FiftyNine.Conservation.NormalizedFullOrbitUnitSilence827.exists_normalizedFullOrbitProfile_unitSilence_classReadout827
#guard_depends_on
  Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.fourierCoefficient_eq_of_classGaugeMap59_eq,
  Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.classReadout_classGaugeMap59_eq_neg_fourierCoefficient
#guard_depends_on
  Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.fourierCoefficient_eq_zero_of_classGaugeMap59_eq_zero,
  Fermat.FiftyNine.Conservation.NormalizedFullOrbitUnitSilence827.exists_normalizedFullOrbitProfile_unitSilence_classReadout827
#guard_depends_on
  Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.fourierCoefficient_eq_zero_of_classGaugeMap59_eq_zero,
  Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.classReadout_classGaugeMap59_eq_neg_fourierCoefficient

#guard_depends_on
  Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.fourierCoefficient_fermatFactor_eq_zero_of_vandiverSevenA,
  Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.fourierCoefficient_fermatFactor_eq_zero_of_selectedClassGauge59_eq_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827.fourierCoefficient_fermatFactor_eq_zero_of_vandiverSevenA,
  Fermat.FiftyNine.Conservation.UlamReadout827.selectedClassGauge59_eq_zero_iff_vandiverSevenA
