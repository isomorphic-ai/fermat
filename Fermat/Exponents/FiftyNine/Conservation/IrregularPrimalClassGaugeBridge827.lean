/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The irregular primal class gauge and the W4/W7 seam

The strict Selmer class gauge is surjective onto the complete 59-torsion
class carrier.  Strong naturality of the genuine class map then says that
restricting its source to the canonical `chi = omega^15` Selmer eigenspace
has image exactly the corresponding class-projector image.

Consequently, for every reflected class carrying the normalized full-orbit
profile, nonvanishing of its seated 827 boundary on the genuine irregular
primal test space is equivalent to nonvanishing of the canonical mode-44
class readout on the actual irregular class line.  This identifies W4
transversality and W7 restricted-readout nonvanishing as one literal seam;
neither side is asserted here.
-/
import Fermat.Exponents.FiftyNine.Conservation.CharacterLinePointwiseFaithfulness59
import Fermat.Exponents.FiftyNine.Conservation.LocalKummerFrobeniusFactorization827

open scoped MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation.IrregularPrimalClassGaugeBridge827

open Fermat.Conservation
open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.SelmerEigenspace
open ArbitraryUnitRawTameCarrierBridge827
open CanonicalFullOrbitLocalPairing827
open CanonicalIrregularMode827
open CanonicalModeFortyFourClassFactorization827
open CharacterLinePointwiseFaithfulness59
open CyclotomicSelmerAction59
open CyclotomicSelmerClassNaturality59
open DetectorWitness827
open FermatFactorClassGaugeSeating59
open LocalKummerFrobeniusFactorization827
open NormalizedFullOrbitEigenprofile827
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

local instance instClassTorsion59ModulePadicInt :
    Module (PadicInt 59) (ClassTorsion59 K) :=
  Module.compHom (ClassTorsion59 K) PadicInt.toZMod

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

/-- The actual strict-Selmer class gauge restricted to the canonical
irregular primal eigenspace. -/
noncomputable def irregularPrimalClassGauge59 :
    OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
        irregularCharacter59 →ₗ[ZMod 59] ClassTorsion59 K :=
  (fermatFactorClassGaugeMap59 (K := K)).comp
    (irregularPrimalInclusion59 K)

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
@[simp]
theorem irregularPrimalClassGauge59_apply
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59) :
    irregularPrimalClassGauge59 K x =
      strictSelmerClassLinearMap59 K x.1 :=
  rfl

/-- The genuine irregular primal class gauge reaches exactly the image of
the canonical irregular class projector.  Full class-gauge surjectivity
supplies preimages before projection; strong naturality transports the
projection through the class map. -/
theorem irregularPrimalClassGauge59_range_eq_irregularClassCharacterLine59 :
    LinearMap.range (irregularPrimalClassGauge59 K) =
      irregularClassCharacterLine59 K := by
  apply le_antisymm
  · rintro c ⟨x, rfl⟩
    refine ⟨strictSelmerClassLinearMap59 K x.1, ?_⟩
    rw [irregularClassProjectorZMod59_apply,
      ← strictSelmerClassLinearMap59_characterProjector]
    rw [characterProjectorAt_eq_self_of_mem
      (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59 x.1 x.property]
    rfl
  · rintro c ⟨q, rfl⟩
    obtain ⟨s, hs⟩ :=
      fermatFactorClassGaugeMap59_surjective (K := K) q
    refine ⟨characterProjectorAt
      (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59 s, ?_⟩
    rw [irregularPrimalClassGauge59_apply,
      strictSelmerClassLinearMap59_characterProjector,
      irregularClassProjectorZMod59_apply]
    change strictSelmerClassLinearMap59 K s = q at hs
    rw [hs]

/-- On a normalized reflected profile, the seated orbit boundary is
literally the canonical class readout after the irregular primal class
gauge. -/
theorem seatedOrbitBoundaryFunctional827_eq_classReadout_comp_irregularGauge
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59)
    (hprofile : ∀ tau : GaloisIndex59,
      relaxedOrbitValuation827 K tau y.1 =
        normalizedFullOrbitEigenprofileCoordinates827
          canonicalTeichmullerCharacter59 irregularCharacter59 tau) :
    seatedOrbitBoundaryFunctional827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 y =
      (canonicalModeFortyFourClassReadout827 K).comp
        (irregularPrimalClassGauge59 K) := by
  ext x
  rw [LinearMap.comp_apply, irregularPrimalClassGauge59_apply]
  exact seatedOrbitBoundaryFunctional827_eq_canonicalClassReadout
    K y hprofile x

/-- W4 transversality on the genuine irregular primal test space is exactly
W7 nonvanishing of the canonical mode-44 readout restricted to the actual
irregular class-projector image. -/
theorem seatedOrbitBoundaryFunctional827_ne_zero_iff_classReadout_restrict_ne_zero
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59)
    (hprofile : ∀ tau : GaloisIndex59,
      relaxedOrbitValuation827 K tau y.1 =
        normalizedFullOrbitEigenprofileCoordinates827
          canonicalTeichmullerCharacter59 irregularCharacter59 tau) :
    seatedOrbitBoundaryFunctional827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 y ≠ 0 ↔
      (canonicalModeFortyFourClassReadout827 K).comp
          (irregularClassCharacterLine59 K).subtype ≠ 0 := by
  rw [seatedOrbitBoundaryFunctional827_eq_classReadout_comp_irregularGauge
    K y hprofile]
  constructor
  · intro hcomp hrestrict
    apply hcomp
    ext x
    rw [LinearMap.zero_apply, LinearMap.comp_apply]
    let z : irregularClassCharacterLine59 K :=
      ⟨irregularPrimalClassGauge59 K x,
        by
          rw [←
            irregularPrimalClassGauge59_range_eq_irregularClassCharacterLine59 K]
          exact ⟨x, rfl⟩⟩
    have hz := LinearMap.congr_fun hrestrict z
    simpa [z] using hz
  · intro hrestrict hcomp
    apply hrestrict
    ext z
    rw [LinearMap.zero_apply, LinearMap.comp_apply]
    have hzmem : (z : ClassTorsion59 K) ∈
        LinearMap.range (irregularPrimalClassGauge59 K) := by
      rw [
        irregularPrimalClassGauge59_range_eq_irregularClassCharacterLine59 K]
      exact z.property
    obtain ⟨x, hx⟩ := hzmem
    have hxzero := LinearMap.congr_fun hcomp x
    rw [LinearMap.zero_apply, LinearMap.comp_apply] at hxzero
    change canonicalModeFortyFourClassReadout827 K
      (z : ClassTorsion59 K) = 0
    rw [← hx]
    exact hxzero

/-! ## Axiom audit -/

/--
info: 'Fermat.FiftyNine.Conservation.IrregularPrimalClassGaugeBridge827.irregularPrimalClassGauge59_range_eq_irregularClassCharacterLine59' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  irregularPrimalClassGauge59_range_eq_irregularClassCharacterLine59

/--
info: 'Fermat.FiftyNine.Conservation.IrregularPrimalClassGaugeBridge827.seatedOrbitBoundaryFunctional827_eq_classReadout_comp_irregularGauge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  seatedOrbitBoundaryFunctional827_eq_classReadout_comp_irregularGauge

/--
info: 'Fermat.FiftyNine.Conservation.IrregularPrimalClassGaugeBridge827.seatedOrbitBoundaryFunctional827_ne_zero_iff_classReadout_restrict_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  seatedOrbitBoundaryFunctional827_ne_zero_iff_classReadout_restrict_ne_zero

end Fermat.FiftyNine.Conservation.IrregularPrimalClassGaugeBridge827
