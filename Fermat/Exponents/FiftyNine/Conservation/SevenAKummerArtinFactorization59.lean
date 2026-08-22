/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The relation-7A Kummer--Artin factorization on the PT test space

The normalized full `827` orbit boundary is already known to factor through
the genuine class-valued relation-7A gauge on the actual irregular primal
Poitou--Tate test space.  This file gives that result its campaign-facing W5
name without defining another gauge, readout, local pairing, or lift.

Here `ArtinRead_827` means the existing
`canonicalModeFortyFourClassReadout827`: the unique descent to class-group
`59`-torsion of the complete `58`-place local Kummer--Frobenius reading.  Its
local residue-Frobenius semantics are kernel-checked by
`SevenALocalKummerFrobeniusFactorization827`.  It is not a constructed global
ray-class Artin map, a Hilbert class field, or a global Artin-reciprocity
theorem.

The reflected input remains arbitrary subject to its literal normalized
full-orbit profile.  In particular, this theorem selects no point of a
Poitou--Tate fiber and proves neither PT exactness nor relation `(7a)`.
-/
import Fermat.Experiments.Conservation.GuardDependsOn
import Fermat.Exponents.FiftyNine.Conservation.IrregularPrimalClassGaugeBridge827

open scoped MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation

open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open ArbitraryUnitRawTameCarrierBridge827
open CanonicalModeFortyFourClassFactorization827
open CanonicalIrregularMode827
open CharacterLinePointwiseFaithfulness59
open CyclotomicSelmerAction59
open CyclotomicSelmerClassNaturality59
open DetectorWitness827
open ExplicitTameOrbitReciprocity827
open IrregularPrimalClassGaugeBridge827
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

/-- **W5: the exact relation-7A Kummer--Artin factorization.**

On the genuine `chi = omega^15` strict-Selmer Poitou--Tate test space, the
complete normalized `827` boundary is exactly the uniquely descended local
Kummer--Frobenius readout after the actual class-valued relation-7A gauge.

The equality has no unit ambiguity because the inverse-reflected orbit and
the sign in `canonicalModeFortyFourClassReadout827` use the same committed
orientation. -/
theorem SevenAKummerArtinFactorization59
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
  exact
    seatedOrbitBoundaryFunctional827_eq_classReadout_comp_irregularGauge
      K y hprofile

/-! ## Kernel-trust and route-separation audit -/

/--
info: 'Fermat.FiftyNine.Conservation.SevenAKummerArtinFactorization59' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SevenAKummerArtinFactorization59

/- The public W5 name must consume the previously proved exact map
factorization, rather than rebuilding a parallel readout. -/
#guard_depends_on
  SevenAKummerArtinFactorization59,
  IrregularPrimalClassGaugeBridge827.seatedOrbitBoundaryFunctional827_eq_classReadout_comp_irregularGauge

/- The factorization retains the proved local Kummer--Frobenius semantics
underlying the canonical class readout. -/
#guard_depends_on
  SevenAKummerArtinFactorization59,
  LocalKummerFrobeniusFactorization827.seatedOrbitBoundaryFunctional827_eq_canonicalClassReadout

/- W5 does not obtain its equality from the later Fermat-specific 7A
closure. -/
#guard_not_depends_on
  SevenAKummerArtinFactorization59,
  SevenAArtinPartialClosure59.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA

/- W5 does not call even the earlier selected-class `7A` endpoint. -/
#guard_not_depends_on
  SevenAKummerArtinFactorization59,
  UlamReadout827.selectedClassGauge59_eq_zero_iff_vandiverSevenA

/- The Takagi and historical modules are deliberately not imported into
this cone.  The two value-level guards above separately ensure that W5 does
not close through either available relation-7A endpoint. -/

end Fermat.FiftyNine.Conservation
