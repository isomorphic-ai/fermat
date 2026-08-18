/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Focused verification of the relation-7A Kummer--Artin route

This non-imported executable audit leaf covers only the newly exposed route:

* W1 retains the complete nonzero normalized twisted-lambda cup receipt;
* W3 constructs the normalized inverse-reflected profile on all 58 places;
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
* W7 identifies orbit silence with relation 7A once an explicit injective
  class readout and its exact factorization are supplied.

The checks deliberately do not claim the still-missing arithmetic inputs:
same-Hom-line membership, a global reflected lift realizing the required
pure orbit mode, or the Kummer--Artin comparison.  This file does not import
the monolithic exponent-59 verifier.
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

/-! W4's completed algebraic implication.  The arithmetic same-line
producer remains intentionally outside this theorem. -/

#check Fermat.Conservation.existsUnique_unit_smul_of_mem_finrank_one

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

/-! W7's honest algebraic partial closure.  Readout existence,
factorization, and injectivity remain explicit theorem arguments. -/

#check Fermat.FiftyNine.Conservation.SevenAArtinPartialClosure59.strictTameOrbitFunctional827_eq_zero_iff_classGauge_eq_zero
#check Fermat.FiftyNine.Conservation.SevenAArtinPartialClosure59.fermatFactorClassGaugeMap59_fermatFactorSelmerDifference59
#check Fermat.FiftyNine.Conservation.SevenAArtinPartialClosure59.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_selectedClassGauge59_eq_zero
#check Fermat.FiftyNine.Conservation.SevenAArtinPartialClosure59.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA

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
info: 'Fermat.FiftyNine.Conservation.SevenAArtinPartialClosure59.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.SevenAArtinPartialClosure59.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA

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
