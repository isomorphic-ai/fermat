/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# W4 from canonical class-readout nonvanishing

The irregular-primal class gauge reaches exactly the canonical `chi = 15`
class-projector image.  For a reflected class carrying the normalized full
827-orbit profile, its orbit boundary is therefore nonzero exactly when the
canonical mode-44 class readout is nonzero on that image.

Global reciprocity identifies the wild boundary with the negative orbit
boundary.  This module combines those two proved comparisons so the W4
unique-unit conclusion consumes W7's canonical restricted-readout
nonvanishing directly; no independent orbit-nonvanishing premise remains.
The restricted-readout nonvanishing itself remains the visible arithmetic
seam.
-/
import Fermat.Exponents.FiftyNine.Conservation.IrregularPrimalClassGaugeBridge827

open scoped MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation.CanonicalW4ClassReadoutBridge827

open Fermat.Conservation
open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.TatePairing
open ArbitraryUnitRawTameCarrierBridge827
open CanonicalFullOrbitLocalPairing827
open CanonicalIrregularMode827
open CanonicalModeFortyFourClassFactorization827
open CharacterLinePointwiseFaithfulness59
open CyclotomicSelmerAction59
open CyclotomicSelmerClassNaturality59
open DetectorWitness827
open IrregularPrimalClassGaugeBridge827
open NormalizedFullOrbitEigenprofile827
open SeatedTameOrbitReciprocityBalance827
open SplitPrimeFourier827
open VostokovLocalization59
open WildOrbitBoundaryComparison827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
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
  AddCommGroup.zmodModule (irregularOldPrimal59_nsmul_eq_zero K)

/-- Under genuine global reciprocity and the normalized orbit profile, wild
transversality is exactly nonvanishing of the canonical mode-44 class
readout on the actual irregular class line. -/
theorem seatedWildBoundaryFunctional59_ne_zero_iff_classReadout_restrict_ne_zero
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59))
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59)
    (hprofile : ∀ tau : GaloisIndex59,
      relaxedOrbitValuation827 K tau y.1 =
        normalizedFullOrbitEigenprofileCoordinates827
          canonicalTeichmullerCharacter59 irregularCharacter59 tau) :
    seatedWildBoundaryFunctional59 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 y ≠ 0 ↔
      (canonicalModeFortyFourClassReadout827 K).comp
          (irregularClassCharacterLine59 K).subtype ≠ 0 := by
  rw [seatedWildBoundaryFunctional59_eq_neg_orbit
    canonicalTeichmullerCharacter59 irregularCharacter59 reciprocity y,
    neg_ne_zero]
  exact
    seatedOrbitBoundaryFunctional827_ne_zero_iff_classReadout_restrict_ne_zero
      K y hprofile

/-- The W4 unique-unit comparison with no separate orbit-transversality
input: canonical W7 restricted-readout nonvanishing supplies it through the
proved irregular-primal range equality. -/
theorem existsUnique_unit_wild_eq_smul_orbit_of_classReadout_ne_zero
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59))
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59)
    (hprofile : ∀ tau : GaloisIndex59,
      relaxedOrbitValuation827 K tau y.1 =
        normalizedFullOrbitEigenprofileCoordinates827
          canonicalTeichmullerCharacter59 irregularCharacter59 tau)
    (readout_ne_zero :
      (canonicalModeFortyFourClassReadout827 K).comp
          (irregularClassCharacterLine59 K).subtype ≠ 0) :
    ∃! u : (ZMod 59)ˣ,
      seatedWildBoundaryFunctional59 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 y =
        (u : ZMod 59) •
          seatedOrbitBoundaryFunctional827 (K := K)
            canonicalTeichmullerCharacter59 irregularCharacter59 y := by
  apply existsUnique_unit_wild_eq_smul_orbit_of_reciprocity
    canonicalTeichmullerCharacter59 irregularCharacter59 reciprocity y
  exact
    (seatedOrbitBoundaryFunctional827_ne_zero_iff_classReadout_restrict_ne_zero
      K y hprofile).2 readout_ne_zero

/-! ## Axiom audit -/

/--
info: 'Fermat.FiftyNine.Conservation.CanonicalW4ClassReadoutBridge827.seatedWildBoundaryFunctional59_ne_zero_iff_classReadout_restrict_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  seatedWildBoundaryFunctional59_ne_zero_iff_classReadout_restrict_ne_zero

/--
info: 'Fermat.FiftyNine.Conservation.CanonicalW4ClassReadoutBridge827.existsUnique_unit_wild_eq_smul_orbit_of_classReadout_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  existsUnique_unit_wild_eq_smul_orbit_of_classReadout_ne_zero

end Fermat.FiftyNine.Conservation.CanonicalW4ClassReadoutBridge827
