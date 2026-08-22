/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The canonical mode-44 readout on the chi=15 class line

The signed mode-44 Fourier functional now descends to a uniquely determined
map on the genuine 59-torsion class group.  This file specializes the
rank-one W7 reduction to that canonical map.  The result no longer carries a
chosen normalized reflected point, an arbitrary class readout, or a separate
factorization premise.

The three remaining arithmetic inputs are kept literal: seating of the
selected class in the chi=15 projector image, dimension one of that image,
and nonvanishing of the canonical readout on it.
-/
import Fermat.Exponents.FiftyNine.Conservation.CanonicalModeFortyFourClassFactorization827
import Fermat.Exponents.FiftyNine.Conservation.CharacterLinePointwiseFaithfulness59

open scoped MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation.CanonicalModeFortyFourCharacterLine827

open Fermat.Conservation
open Fermat.Conservation.CommonActionStage
open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.CanonicalModeFortyFourClassFactorization827
open Fermat.FiftyNine.Conservation.CharacterLinePointwiseFaithfulness59
open Fermat.FiftyNine.Conservation.CyclotomicSelmerClassNaturality59
open Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827
open Fermat.FiftyNine.Conservation.FermatFactorClassGaugeSeating59
open Fermat.FiftyNine.Conservation.FermatFactorSelmerGauge59
open Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827
open Fermat.FiftyNine.Conservation.SevenAArtinPartialClosure59
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.StateFactorPair
open Fermat.FiftyNine.Conservation.UlamReadout827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

local instance instClassTorsion59ModuleZMod :
    Module (ZMod 59) (ClassTorsion59 K) :=
  AddSubgroup.torsionBy.zmodModule

local instance instClassTorsion59ModulePadicInt :
    Module (PadicInt 59) (ClassTorsion59 K) :=
  Module.compHom (ClassTorsion59 K) PadicInt.toZMod

variable {zeta : K} {hZeta : IsPrimitiveRoot zeta 59}
  {S : Fermat.FiftyNine.Conservation.FermatState.PrimitiveSecondCaseSolution}
  {hz : (59 : ℤ) ∣ S.z}

/-- The canonical Fourier readout reflects zero at the selected Fermat class
as soon as the three explicit chi=15 character-line facts are supplied. -/
theorem selectedClassGauge59_eq_zero_of_canonicalModeFortyFourReadout_eq_zero
    (pair : StateLinkedIdealPair hZeta S hz)
    (seated :
      cyclotomicClassProjector59 K irregularCharacter59
          (selectedClassGauge59 pair) = selectedClassGauge59 pair)
    (rank_one : Module.finrank (ZMod 59)
      (irregularClassCharacterLine59 K) = 1)
    (readout_ne_zero :
      (canonicalModeFortyFourClassReadout827 K).comp
          (irregularClassCharacterLine59 K).subtype ≠ 0)
    (readout_zero :
      canonicalModeFortyFourClassReadout827 K
        (selectedClassGauge59 pair) = 0) :
    selectedClassGauge59 pair = 0 := by
  exact
    selectedClassGauge59_eq_zero_of_readout_eq_zero_of_characterLine
      K (canonicalModeFortyFourClassReadout827 K) pair seated rank_one
        readout_ne_zero readout_zero

/-- W7 for the actual canonical mode-44 class readout.  This is the sharp
rank-one closure statement predicted by the Kummer--Artin route. -/
theorem fourierCoefficient_fermatFactor_eq_zero_iff_vandiverSevenA_of_canonicalCharacterLine
    (pair : StateLinkedIdealPair hZeta S hz)
    (seated :
      cyclotomicClassProjector59 K irregularCharacter59
          (selectedClassGauge59 pair) = selectedClassGauge59 pair)
    (rank_one : Module.finrank (ZMod 59)
      (irregularClassCharacterLine59 K) = 1)
    (readout_ne_zero :
      (canonicalModeFortyFourClassReadout827 K).comp
          (irregularClassCharacterLine59 K).subtype ≠ 0) :
    fourierCoefficient
        (strictOrbitResidueWave827 K
          (fermatFactorSelmerDifference59 pair))
        (powerCharacter59 44) = 0 ↔
      pair.ledger.VandiverSevenA 0 1 := by
  constructor
  · intro hzero
    apply (selectedClassGauge59_eq_zero_iff_vandiverSevenA pair).1
    apply
      selectedClassGauge59_eq_zero_of_canonicalModeFortyFourReadout_eq_zero
        K pair seated rank_one readout_ne_zero
    rw [← fermatFactorClassGaugeMap59_fermatFactorSelmerDifference59 K pair,
      canonicalModeFortyFourClassReadout827_classGaugeMap59,
      strictOrbitNegativeModeFortyFourLinearMap827_apply, hzero, neg_zero]
  · exact fourierCoefficient_fermatFactor_eq_zero_of_vandiverSevenA K pair

/--
info: 'Fermat.FiftyNine.Conservation.CanonicalModeFortyFourCharacterLine827.fourierCoefficient_fermatFactor_eq_zero_iff_vandiverSevenA_of_canonicalCharacterLine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  fourierCoefficient_fermatFactor_eq_zero_iff_vandiverSevenA_of_canonicalCharacterLine

end Fermat.FiftyNine.Conservation.CanonicalModeFortyFourCharacterLine827
