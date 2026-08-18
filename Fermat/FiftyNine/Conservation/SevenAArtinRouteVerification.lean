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

The checks deliberately keep the remaining lanes separate.  W1 is a local
cup receipt; no Poitou--Tate theorem yet produces a single global reflected
class simultaneously carrying its wild coordinate and the realized tame
profile, and no common-Hom-line theorem yet identifies the two boundary
functionals.  Within W7, the only visible input is pointwise faithfulness of
the produced readout, the exact target of the Kummer--Artin comparison.
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

/-! ## Public route inventory -/

/-! W1: the retained local cup and its two oriented degree-one factors. -/

#check Fermat.FiftyNine.Conservation.TwistedLambdaCupReceipt59
#check Fermat.FiftyNine.Conservation.TwistedLambdaCupReceipt59.cup_eq
#check Fermat.FiftyNine.Conservation.TwistedLambdaCupReceipt59.cup_ne_zero
#check Fermat.FiftyNine.Conservation.TwistedLambdaCupReceipt59.normalized_reading
#check Fermat.FiftyNine.Conservation.TwistedLambdaCupReceipt59.reading_ne_zero
#check Fermat.FiftyNine.Conservation.twistedLambdaCupReceipt59

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

/-! W4's completed algebraic implication.  The arithmetic same-line
producer remains intentionally outside this theorem. -/

#check Fermat.Conservation.existsUnique_unit_smul_of_mem_finrank_one
#check Fermat.Conservation.eq_zero_of_mem_finrank_one_of_readout_restrict_ne_zero

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

/-! The produced-readout W7 boundary.  Full injectivity is unnecessary:
only zero reflection at the one Fermat-selected class remains visible. -/

#check Fermat.FiftyNine.Conservation.PointwiseFaithfulSevenAReadout827.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_selectedClassGauge59_eq_zero_of_pointwiseFaithful
#check Fermat.FiftyNine.Conservation.PointwiseFaithfulSevenAReadout827.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA_of_pointwiseFaithful
#check Fermat.FiftyNine.Conservation.PointwiseFaithfulSevenAReadout827.existsUnique_classReadout_with_pointwiseW7_of_unit_silence
#check Fermat.FiftyNine.Conservation.PointwiseFaithfulSevenAReadout827.existsUnique_classReadout_with_pointwiseW7_of_ringUnit_silence
#check Fermat.FiftyNine.Conservation.PointwiseFaithfulSevenAReadout827.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA_of_unit_silence
#check Fermat.FiftyNine.Conservation.PointwiseFaithfulSevenAReadout827.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA_of_ringUnit_silence

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
