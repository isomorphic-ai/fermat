/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Nonvanishing of the Dwork cup from the 827 Artin read

The complementary-depth local-symbol calculation is not the only honest
way to prove that the seated Dwork cup is nonzero.  The Kummer--Artin route
retains both global coordinates instead:

* a reflected global class whose lambda localization is a unit multiple of
  the depth-44 Dwork meter and whose complete `827` profile is normalized;
* a primal global class localizing to the depth-15 Dwork factor and having
  nonzero canonical class-valued Artin read.

Global reciprocity and the already proved exact 7A factorization then force
the local Dwork cup reading to be nonzero.  This file proves that implication
and composes it with the exact affine/unit-orbit lift criterion.  It chooses
neither global class, assumes no local Hilbert-symbol value, and asserts no
new reciprocity or Poitou--Tate theorem.
-/
import Fermat.Experiments.Conservation.GuardDependsOn
import Fermat.Exponents.FiftyNine.Conservation.DworkComplementaryCupReduction59
import Fermat.Exponents.FiftyNine.Conservation.DworkSevenAAffineObstruction59

open scoped BigOperators MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 300000

namespace Fermat.FiftyNine.Conservation.DworkArtinNonvanishing59

open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.TatePairing
open Fermat.Conservation.WildKummerPairing
open CanonicalFullOrbitLocalPairing827
open CanonicalIrregularMode827
open CanonicalModeFortyFourClassFactorization827
open CanonicalW1PoitouTateReduction827
open ContinuousKummerTateLocalization59
open CyclotomicSelmerAction59
open CyclotomicSelmerClassNaturality59
open DetectorWitness827
open DworkComplementaryCupReduction59
open DworkPrincipalUnitCandidates59
open DworkProjectorUnitRepresentative59
open DworkSeatedLambdaMeter59
open DworkSevenAAffineObstruction59
open DworkSevenAArtinBalance59
open IrregularPrimalClassGaugeBridge827
open LambdaMeterAffineUnitOrbit827
open LambdaMeterPointedPoitouTate827
open LambdaOrbitAffineCokernel827
open LocalCompletion59
open NormalizedContinuousKummerPairing59
open PointedTateIncidence
open SplitPrimeFourier827
open TwistedLambdaKummerCupComparison59
open UlamReadout827
open VostokovLocalization59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

local instance instClassTorsion59ModuleZMod :
    Module (ZMod 59) (ClassTorsion59 K) :=
  AddSubgroup.torsionBy.zmodModule

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
private theorem irregularOldPrimal59_nsmul_eq_zero
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59) :
    59 • x = 0 := by
  apply Subtype.ext
  exact p_nsmul_eq_zero x.1

noncomputable local instance instIrregularOldPrimal59ModuleZMod :
    Module (ZMod 59)
      (OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
        irregularCharacter59) :=
  AddCommGroup.zmodModule irregularOldPrimal59_nsmul_eq_zero

/-! ## The exact Artin-to-wild contradiction -/

/-- A genuine reflected Dwork lift and one Artin-visible primal realization
force the normalized complementary-depth Dwork cup reading to be nonzero.

The proof is purely the already banked conservation equation.  If the local
cup vanished, the wild Dwork boundary would vanish on the retained primal
class; the exact Dwork--Artin balance would then make its nonzero class read
vanish as well. -/
theorem dworkCupReadout_ne_zero_of_reflectedLift_and_primalArtin
    (lift : DworkSeatedNormalizedOrbitScaledLambdaLift827 (K := K))
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59))
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59)
    (localizes :
      irregularPrimalLambdaLocalization827 (K := K) x =
        dworkSeatedLambdaPrimalFifteen59 (K := K))
    (artin_ne_zero :
      canonicalModeFortyFourClassReadout827 K
        (irregularPrimalClassGauge59 K x) ≠ 0) :
    normalizedInflationReadout59 K
        (dworkSeatedLambdaCupClass59 (K := K)) ≠ 0 := by
  have hbalance := LinearMap.congr_fun
    (scaledDworkLambdaBoundary_eq_neg_classGaugeReadout
      (K := K) lift reciprocity) x
  intro hcup
  apply artin_ne_zero
  have hboundary :
      dworkSeatedLambdaPrimalBoundaryFunctional827 (K := K) x = 0 := by
    rw [dworkSeatedLambdaPrimalBoundaryFunctional827_apply, localizes]
    exact hcup
  rw [LinearMap.smul_apply, hboundary, smul_zero, LinearMap.neg_apply,
    LinearMap.comp_apply] at hbalance
  exact neg_eq_zero.mp hbalance.symm

/-- The same conclusion from a nonempty reflected lift fiber.  The exact
unit-orbit theorem in `DworkSevenAAffineObstruction59` is the independent
producer of this existential. -/
theorem dworkCupReadout_ne_zero_of_nonempty_reflectedLift_and_primalArtin
    (lift_nonempty :
      Nonempty (DworkSeatedNormalizedOrbitScaledLambdaLift827 (K := K)))
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59))
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59)
    (localizes :
      irregularPrimalLambdaLocalization827 (K := K) x =
        dworkSeatedLambdaPrimalFifteen59 (K := K))
    (artin_ne_zero :
      canonicalModeFortyFourClassReadout827 K
        (irregularPrimalClassGauge59 K x) ≠ 0) :
    normalizedInflationReadout59 K
        (dworkSeatedLambdaCupClass59 (K := K)) ≠ 0 := by
  rcases lift_nonempty with ⟨lift⟩
  exact dworkCupReadout_ne_zero_of_reflectedLift_and_primalArtin
    lift reciprocity x localizes artin_ne_zero

/-! ## Consequences for the retained H2 receipt -/

/-- The Artin route proves nonvanishing of the retained continuous local
`H²` class itself, without an injectivity assumption on the selected
readout. -/
theorem dworkSeatedLambdaCupClass59_ne_zero_of_reflectedLift_and_primalArtin
    (lift : DworkSeatedNormalizedOrbitScaledLambdaLift827 (K := K))
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59))
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59)
    (localizes :
      irregularPrimalLambdaLocalization827 (K := K) x =
        dworkSeatedLambdaPrimalFifteen59 (K := K))
    (artin_ne_zero :
      canonicalModeFortyFourClassReadout827 K
        (irregularPrimalClassGauge59 K x) ≠ 0) :
    dworkSeatedLambdaCupClass59 (K := K) ≠ 0 := by
  have hreadout := dworkCupReadout_ne_zero_of_reflectedLift_and_primalArtin
    lift reciprocity x localizes artin_ne_zero
  intro hcup
  apply hreadout
  rw [hcup, map_zero]

/-- The very same global receipts prove nonvanishing of the exact finite
complementary Dwork pairing exposed by the tier-(b) reduction. -/
theorem finiteDworkComplementaryPairing59_ne_zero_of_reflectedLift_and_primalArtin
    (lift : DworkSeatedNormalizedOrbitScaledLambdaLift827 (K := K))
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59))
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59)
    (localizes :
      irregularPrimalLambdaLocalization827 (K := K) x =
        dworkSeatedLambdaPrimalFifteen59 (K := K))
    (artin_ne_zero :
      canonicalModeFortyFourClassReadout827 K
        (irregularPrimalClassGauge59 K x) ≠ 0) :
    normalizedLambdaLocalPairing59 K
        (classOfUnit 59 (LambdaLocalField59 K)
          (Additive.ofMul (dworkProjectorUnitRepresentativeFifteen59 K)))
        (classOfUnit 59 (LambdaLocalField59 K)
          (Additive.ofMul
            (dworkProjectorUnitRepresentativeFortyFour59 K))) ≠ 0 := by
  rw [← normalizedInflationReadout59_dworkCup_eq_finiteDworkPairing]
  exact dworkCupReadout_ne_zero_of_reflectedLift_and_primalArtin
    lift reciprocity x localizes artin_ne_zero

/-- If local continuous `H²` is one-dimensional, the Artin proof also
supplies the requested unit-line comparison with the already banked nonzero
twisted-lambda cup. -/
theorem exists_unit_dworkCup_eq_smul_twistedCup_of_reflectedLift_and_primalArtin
    (hH2 : Module.finrank (ZMod 59) (LambdaRootsContinuousH2 K) = 1)
    (lift : DworkSeatedNormalizedOrbitScaledLambdaLift827 (K := K))
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59))
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59)
    (localizes :
      irregularPrimalLambdaLocalization827 (K := K) x =
        dworkSeatedLambdaPrimalFifteen59 (K := K))
    (artin_ne_zero :
      canonicalModeFortyFourClassReadout827 K
        (irregularPrimalClassGauge59 K x) ≠ 0) :
    ∃ u : (ZMod 59)ˣ,
      dworkSeatedLambdaCupClass59 (K := K) =
        (u : ZMod 59) • twistedLambdaKummerCupH2Class59 K := by
  apply exists_unit_dworkCup_eq_smul_twistedCup_of_finrank_one hH2
  exact
    finiteDworkComplementaryPairing59_ne_zero_of_reflectedLift_and_primalArtin
      lift reciprocity x localizes artin_ne_zero

/-! ## Kernel-trust and route audit -/

/--
info: 'Fermat.FiftyNine.Conservation.DworkArtinNonvanishing59.dworkCupReadout_ne_zero_of_reflectedLift_and_primalArtin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms dworkCupReadout_ne_zero_of_reflectedLift_and_primalArtin

/--
info: 'Fermat.FiftyNine.Conservation.DworkArtinNonvanishing59.dworkCupReadout_ne_zero_of_nonempty_reflectedLift_and_primalArtin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  dworkCupReadout_ne_zero_of_nonempty_reflectedLift_and_primalArtin

/--
info: 'Fermat.FiftyNine.Conservation.DworkArtinNonvanishing59.dworkSeatedLambdaCupClass59_ne_zero_of_reflectedLift_and_primalArtin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  dworkSeatedLambdaCupClass59_ne_zero_of_reflectedLift_and_primalArtin

/--
info: 'Fermat.FiftyNine.Conservation.DworkArtinNonvanishing59.exists_unit_dworkCup_eq_smul_twistedCup_of_reflectedLift_and_primalArtin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  exists_unit_dworkCup_eq_smul_twistedCup_of_reflectedLift_and_primalArtin

#guard_depends_on
  dworkCupReadout_ne_zero_of_reflectedLift_and_primalArtin,
  DworkSevenAArtinBalance59.scaledDworkLambdaBoundary_eq_neg_classGaugeReadout

#guard_depends_on
  dworkCupReadout_ne_zero_of_nonempty_reflectedLift_and_primalArtin,
  dworkCupReadout_ne_zero_of_reflectedLift_and_primalArtin

#guard_depends_on
  dworkSeatedLambdaCupClass59_ne_zero_of_reflectedLift_and_primalArtin,
  dworkCupReadout_ne_zero_of_reflectedLift_and_primalArtin

#guard_depends_on
  finiteDworkComplementaryPairing59_ne_zero_of_reflectedLift_and_primalArtin,
  DworkComplementaryCupReduction59.normalizedInflationReadout59_dworkCup_eq_finiteDworkPairing

#guard_depends_on
  exists_unit_dworkCup_eq_smul_twistedCup_of_reflectedLift_and_primalArtin,
  DworkComplementaryCupReduction59.exists_unit_dworkCup_eq_smul_twistedCup_of_finrank_one

/- This Artin proof does not use the unavailable local Hilbert-symbol
evaluation or the former full reverse-PT inclusion. -/
#guard_not_depends_on
  dworkCupReadout_ne_zero_of_nonempty_reflectedLift_and_primalArtin,
  LambdaMeterPointedPoitouTate827.lambdaMeterPointedLocalization827_range_eq_ker_iff_kernel_lifts

#guard_not_depends_on
  dworkCupReadout_ne_zero_of_nonempty_reflectedLift_and_primalArtin,
  DworkComplementaryCupReduction59.normalizedInflationReadout59_dworkCup_eq_doubleOrbitSum

end Fermat.FiftyNine.Conservation.DworkArtinNonvanishing59
