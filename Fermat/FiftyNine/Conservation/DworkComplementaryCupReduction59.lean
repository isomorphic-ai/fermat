/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Finite reduction of the complementary Dwork cup at 59

The seated Dwork meter couples the power-15 and power-44 projectors.  Their
depths are complementary: `15 + 44 = 59`.  This file retains both factors
and rewrites their genuine continuous local `H²` cup through the explicit
finite Dwork products constructed previously.

After scalarization, the remaining arithmetic value is displayed as an
exact `58 × 58` sum of pairings between transported Dwork orbit factors.
Two conditional adapters isolate the independent structural input needed to
turn nonvanishing of that finite value into the requested `H²` line
comparison: injectivity of the selected readout, or one-dimensionality of
the local `H²` space.  No local-symbol value, nonvanishing claim, or
relation-7A conclusion is asserted here.
-/
import Fermat.FiftyNine.Conservation.DworkProjectorUnitRepresentative59
import Fermat.FiftyNine.Conservation.DworkSeatedLambdaMeter59
import Fermat.Conservation.GuardDependsOn

open scoped BigOperators NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.DworkComplementaryCupReduction59

set_option maxRecDepth 100000

open Fermat.Conservation.LocalKummerTransport
open Fermat.Conservation.WildKummerPairing
open Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59
open Fermat.FiftyNine.Conservation.DworkPrincipalUnitCandidates59
open Fermat.FiftyNine.Conservation.DworkProjectorUnitRepresentative59
open Fermat.FiftyNine.Conservation.DworkCyclotomicTransport59
open Fermat.FiftyNine.Conservation.DworkSeatedLambdaMeter59
open Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59
open Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59
open Fermat.FiftyNine.Conservation.LocalIntegralTrace59
open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.LambdaLocalKummerClassAction59
open Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59
open Fermat.FiftyNine.Conservation.NormImageBridge59
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerCupComparison59
open KummerCriterion.CyclotomicUnits.PadicLogSetup.DworkParameter
open KummerCriterion.CyclotomicUnits.PadicLogSetup.DworkParameter.Conjugation

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

/-! ## Literal orbit factors -/

/-- One translated Dwork principal unit, transported all the way to the
concrete lambda-local field. -/
noncomputable def dworkPrincipalUnitOrbitFactor59
    (sigma : GaloisIndex59) (depth : ℕ) (hdepth : depth ≠ 0) :
    (LambdaLocalField59 K)ˣ :=
  Units.map (valuedCompletionEquivLambdaField59 K).toRingHom
    (Units.map (valuedIntegerToLambdaCompletion59 K).toMonoidHom
      (Units.map (dworkValuedAlgEquiv59 K).toRingHom
        (Units.map
          (dworkCompleteCyclotomicEquiv (p := 59) K sigma).toMonoidHom
          (dworkPrincipalUnitAtDepth59 K depth hdepth))))

/-- The local Kummer class of one transported Dwork orbit factor. -/
noncomputable def dworkPrincipalUnitOrbitKummerClass59
    (sigma : GaloisIndex59) (depth : ℕ) (hdepth : depth ≠ 0) :
    LambdaLocalKummerClass59 K :=
  classOfUnit 59 (LambdaLocalField59 K)
    (Additive.ofMul
      (dworkPrincipalUnitOrbitFactor59 (K := K) sigma depth hdepth))

/-- The Kummer class of a finite Dwork projector product is the explicit
sum of the Kummer classes of its orbit factors. -/
theorem classOfUnit_dworkProjectorUnitRepresentativeAtDepth59_eq_sum
    (t : ZMod 58) (depth : ℕ) (hdepth : depth ≠ 0) :
    classOfUnit 59 (LambdaLocalField59 K)
        (Additive.ofMul
          (dworkProjectorUnitRepresentativeAtDepth59 K t depth hdepth)) =
      ∑ sigma : GaloisIndex59,
        projectorExponent59 t sigma •
          dworkPrincipalUnitOrbitKummerClass59 (K := K)
            sigma depth hdepth := by
  unfold dworkProjectorUnitRepresentativeAtDepth59
    dworkPrincipalUnitOrbitKummerClass59 dworkPrincipalUnitOrbitFactor59
  change classOfUnit 59 (LambdaLocalField59 K)
      (∑ sigma : GaloisIndex59,
        projectorExponent59 t sigma •
          Additive.ofMul
            (Units.map (valuedCompletionEquivLambdaField59 K).toRingHom
              (Units.map (valuedIntegerToLambdaCompletion59 K).toMonoidHom
                (Units.map (dworkValuedAlgEquiv59 K).toRingHom
                  (Units.map
                    (dworkCompleteCyclotomicEquiv
                      (p := 59) K sigma).toMonoidHom
                    (dworkPrincipalUnitAtDepth59 K depth hdepth)))))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro sigma hsigma
  rw [map_nsmul]

/-! ## Retained `H²` receipt and finite scalar reduction -/

/-- The genuine seated continuous cup is exactly the cup of the two finite
Dwork projector products.  Both degree-one factors remain visible. -/
theorem dworkSeatedLambdaCupClass59_eq_finiteDworkRepresentatives :
    dworkSeatedLambdaCupClass59 (K := K) =
      lambdaLocalH2Pairing K
        (classOfUnit 59 (LambdaLocalField59 K)
          (Additive.ofMul (dworkProjectorUnitRepresentativeFifteen59 K)))
        (classOfUnit 59 (LambdaLocalField59 K)
          (Additive.ofMul (dworkProjectorUnitRepresentativeFortyFour59 K))) := by
  rw [classOfUnit_dworkProjectorUnitRepresentativeFifteen59]
  rw [classOfUnit_dworkProjectorUnitRepresentativeFortyFour59]
  rfl

/-- Exact `58 × 58` expansion before scalarization.  Each summand remains a
genuine continuous local `H²` cup of two explicit orbit-factor Kummer
classes, so the complete cohomological receipt is retained. -/
theorem dworkSeatedLambdaCupClass59_eq_doubleOrbitCupSum :
    dworkSeatedLambdaCupClass59 (K := K) =
      ∑ tau : GaloisIndex59, ∑ sigma : GaloisIndex59,
        projectorExponent59 44 tau •
          (projectorExponent59 15 sigma •
            lambdaLocalH2Pairing K
              (dworkPrincipalUnitOrbitKummerClass59
                (K := K) sigma 15 (by norm_num))
              (dworkPrincipalUnitOrbitKummerClass59
                (K := K) tau 44 (by norm_num))) := by
  rw [dworkSeatedLambdaCupClass59_eq_finiteDworkRepresentatives]
  unfold dworkProjectorUnitRepresentativeFifteen59
    dworkProjectorUnitRepresentativeFortyFour59
  rw [classOfUnit_dworkProjectorUnitRepresentativeAtDepth59_eq_sum]
  rw [classOfUnit_dworkProjectorUnitRepresentativeAtDepth59_eq_sum]
  simp only [map_sum, map_nsmul, AddMonoidHom.finsetSum_apply,
    AddMonoidHom.nsmul_apply, Finset.smul_sum]

/-- Scalarizing the retained cup leaves exactly the finite complementary
Dwork pairing. -/
theorem normalizedInflationReadout59_dworkCup_eq_finiteDworkPairing :
    normalizedInflationReadout59 K
        (dworkSeatedLambdaCupClass59 (K := K)) =
      normalizedLambdaLocalPairing59 K
        (classOfUnit 59 (LambdaLocalField59 K)
          (Additive.ofMul (dworkProjectorUnitRepresentativeFifteen59 K)))
        (classOfUnit 59 (LambdaLocalField59 K)
          (Additive.ofMul (dworkProjectorUnitRepresentativeFortyFour59 K))) := by
  rw [dworkSeatedLambdaCupClass59_eq_finiteDworkRepresentatives]
  rfl

/-- Exact `58 × 58` orbit expansion of the scalar arithmetic seam.  The
outer sum is the depth-44 orbit and the inner sum the depth-15 orbit. -/
theorem normalizedInflationReadout59_dworkCup_eq_doubleOrbitSum :
    normalizedInflationReadout59 K
        (dworkSeatedLambdaCupClass59 (K := K)) =
      ∑ tau : GaloisIndex59, ∑ sigma : GaloisIndex59,
        projectorExponent59 44 tau •
          (projectorExponent59 15 sigma •
            normalizedLambdaLocalPairing59 K
              (dworkPrincipalUnitOrbitKummerClass59
                (K := K) sigma 15 (by norm_num))
              (dworkPrincipalUnitOrbitKummerClass59
                (K := K) tau 44 (by norm_num))) := by
  rw [dworkSeatedLambdaCupClass59_eq_doubleOrbitCupSum]
  simp only [map_sum, map_nsmul]
  rfl

/-! ## Honest conditional line-comparison adapters -/

/-- If the chosen normalized readout is injective, nonvanishing of the
finite Dwork pairing gives the requested unit line comparison in `H²`. -/
theorem exists_unit_dworkCup_eq_smul_twistedCup_of_injective_readout
    (hinjective : LinearMap.ker (normalizedInflationReadout59 K) = ⊥)
    (hfinite :
      normalizedLambdaLocalPairing59 K
        (classOfUnit 59 (LambdaLocalField59 K)
          (Additive.ofMul (dworkProjectorUnitRepresentativeFifteen59 K)))
        (classOfUnit 59 (LambdaLocalField59 K)
          (Additive.ofMul (dworkProjectorUnitRepresentativeFortyFour59 K))) ≠ 0) :
    ∃ u : (ZMod 59)ˣ,
      dworkSeatedLambdaCupClass59 (K := K) =
        (u : ZMod 59) • twistedLambdaKummerCupH2Class59 K := by
  have ha : normalizedInflationReadout59 K
      (dworkSeatedLambdaCupClass59 (K := K)) ≠ 0 := by
    rw [normalizedInflationReadout59_dworkCup_eq_finiteDworkPairing]
    exact hfinite
  let u : (ZMod 59)ˣ := Units.mk0
    (normalizedInflationReadout59 K
      (dworkSeatedLambdaCupClass59 (K := K))) ha
  refine ⟨u, ?_⟩
  apply LinearMap.ker_eq_bot.mp hinjective
  simp [u, normalizedInflationReadout59_twistedLambdaCup]

/-- Alternatively, one-dimensionality of local continuous `H²`, together
with the same finite nonvanishing statement, gives the unit comparison. -/
theorem exists_unit_dworkCup_eq_smul_twistedCup_of_finrank_one
    (hfinrank : Module.finrank (ZMod 59) (LambdaRootsContinuousH2 K) = 1)
    (hfinite :
      normalizedLambdaLocalPairing59 K
        (classOfUnit 59 (LambdaLocalField59 K)
          (Additive.ofMul (dworkProjectorUnitRepresentativeFifteen59 K)))
        (classOfUnit 59 (LambdaLocalField59 K)
          (Additive.ofMul (dworkProjectorUnitRepresentativeFortyFour59 K))) ≠ 0) :
    ∃ u : (ZMod 59)ˣ,
      dworkSeatedLambdaCupClass59 (K := K) =
        (u : ZMod 59) • twistedLambdaKummerCupH2Class59 K := by
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero'
      (twistedLambdaKummerCupH2Class59 K)
      (twistedLambdaKummerCupH2Class59_ne_zero K)).mp hfinrank
      (dworkSeatedLambdaCupClass59 (K := K))
  have hreadout : normalizedInflationReadout59 K
      (dworkSeatedLambdaCupClass59 (K := K)) ≠ 0 := by
    rw [normalizedInflationReadout59_dworkCup_eq_finiteDworkPairing]
    exact hfinite
  have hc_ne : c ≠ 0 := by
    intro hc_zero
    apply hreadout
    rw [← hc, hc_zero, zero_smul, map_zero]
  exact ⟨Units.mk0 c hc_ne, hc.symm⟩

/-! ## Kernel-trust and dependency audit -/

/--
info: 'Fermat.FiftyNine.Conservation.DworkComplementaryCupReduction59.classOfUnit_dworkProjectorUnitRepresentativeAtDepth59_eq_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms classOfUnit_dworkProjectorUnitRepresentativeAtDepth59_eq_sum

/--
info: 'Fermat.FiftyNine.Conservation.DworkComplementaryCupReduction59.dworkSeatedLambdaCupClass59_eq_finiteDworkRepresentatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms dworkSeatedLambdaCupClass59_eq_finiteDworkRepresentatives

/--
info: 'Fermat.FiftyNine.Conservation.DworkComplementaryCupReduction59.dworkSeatedLambdaCupClass59_eq_doubleOrbitCupSum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms dworkSeatedLambdaCupClass59_eq_doubleOrbitCupSum

/--
info: 'Fermat.FiftyNine.Conservation.DworkComplementaryCupReduction59.normalizedInflationReadout59_dworkCup_eq_finiteDworkPairing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms normalizedInflationReadout59_dworkCup_eq_finiteDworkPairing

/--
info: 'Fermat.FiftyNine.Conservation.DworkComplementaryCupReduction59.normalizedInflationReadout59_dworkCup_eq_doubleOrbitSum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms normalizedInflationReadout59_dworkCup_eq_doubleOrbitSum

/--
info: 'Fermat.FiftyNine.Conservation.DworkComplementaryCupReduction59.exists_unit_dworkCup_eq_smul_twistedCup_of_injective_readout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms exists_unit_dworkCup_eq_smul_twistedCup_of_injective_readout

/--
info: 'Fermat.FiftyNine.Conservation.DworkComplementaryCupReduction59.exists_unit_dworkCup_eq_smul_twistedCup_of_finrank_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms exists_unit_dworkCup_eq_smul_twistedCup_of_finrank_one

/- The orbit sum is the literal additive readback of the finite product. -/
#guard_depends_on
  classOfUnit_dworkProjectorUnitRepresentativeAtDepth59_eq_sum,
  dworkProjectorUnitRepresentativeAtDepth59

/- Both degree-one factors are retained through their exact projector
readbacks. -/
#guard_depends_on
  dworkSeatedLambdaCupClass59_eq_finiteDworkRepresentatives,
  classOfUnit_dworkProjectorUnitRepresentativeFifteen59

#guard_depends_on
  dworkSeatedLambdaCupClass59_eq_finiteDworkRepresentatives,
  classOfUnit_dworkProjectorUnitRepresentativeFortyFour59

/- The cohomological orbit expansion consumes both the retained cup identity
and the literal orbit-factor readback. -/
#guard_depends_on
  dworkSeatedLambdaCupClass59_eq_doubleOrbitCupSum,
  dworkSeatedLambdaCupClass59_eq_finiteDworkRepresentatives

#guard_depends_on
  dworkSeatedLambdaCupClass59_eq_doubleOrbitCupSum,
  classOfUnit_dworkProjectorUnitRepresentativeAtDepth59_eq_sum

/- Scalar reduction consumes the retained `H²` identity. -/
#guard_depends_on
  normalizedInflationReadout59_dworkCup_eq_finiteDworkPairing,
  dworkSeatedLambdaCupClass59_eq_finiteDworkRepresentatives

/- Scalarization of the double sum consumes the retained `H²` expansion. -/
#guard_depends_on
  normalizedInflationReadout59_dworkCup_eq_doubleOrbitSum,
  dworkSeatedLambdaCupClass59_eq_doubleOrbitCupSum

#guard_depends_on
  normalizedInflationReadout59_dworkCup_eq_doubleOrbitSum,
  classOfUnit_dworkProjectorUnitRepresentativeAtDepth59_eq_sum

/- The injective-readout adapter calibrates against the genuine twisted
lambda cup, rather than manufacturing a scalar line by definition. -/
#guard_depends_on
  exists_unit_dworkCup_eq_smul_twistedCup_of_injective_readout,
  normalizedInflationReadout59_dworkCup_eq_finiteDworkPairing

#guard_depends_on
  exists_unit_dworkCup_eq_smul_twistedCup_of_injective_readout,
  normalizedInflationReadout59_twistedLambdaCup

/- The rank-one adapter retains both the finite scalar seam and the banked
nonzero genuine cup. -/
#guard_depends_on
  exists_unit_dworkCup_eq_smul_twistedCup_of_finrank_one,
  normalizedInflationReadout59_dworkCup_eq_finiteDworkPairing

#guard_depends_on
  exists_unit_dworkCup_eq_smul_twistedCup_of_finrank_one,
  twistedLambdaKummerCupH2Class59_ne_zero

end Fermat.FiftyNine.Conservation.DworkComplementaryCupReduction59
