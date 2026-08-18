/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Rank-one character-line reduction of W7

The pointwise-faithfulness premise in the 827 class-readout endpoint can be
split into the three arithmetic statements predicted by the Kummer--Artin
route:

* the selected relation-7A class is seated in the canonical chi=15 line;
* that line is one-dimensional;
* the constructed class readout is nonzero on that line.

Everything after those statements is pure linear algebra.  This file builds
the actual `ZMod 59` character line from the genuine class-group projector
and proves the resulting W7 consumer.  It supplies none of the three
arithmetic statements and does not import the Takagi relation-7A proof.
-/
import Fermat.Conservation.OneDimensionalUnitProportionality
import Fermat.FiftyNine.Conservation.FermatFactorClassGaugeCharacterBoundary59
import Fermat.FiftyNine.Conservation.PointwiseFaithfulSevenAReadout827

open scoped MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

namespace Fermat.FiftyNine.Conservation.CharacterLinePointwiseFaithfulness59

open Fermat.Conservation
open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.SelmerEigenspace
open CanonicalFullOrbitLocalPairing827
open CanonicalIrregularMode827
open CyclotomicSelmerClassNaturality59
open FermatFactorClassGaugeCharacterBoundary59
open FermatFactorClassGaugeSeating59
open FermatFactorSelmerGauge59
open PointwiseFaithfulSevenAReadout827
open SplitPrimeFourier827
open StateFactorPair
open StrictTameOrbitClassFactorization827
open UlamReadout827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

set_option maxRecDepth 3000
set_option maxHeartbeats 800000

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

local instance instClassTorsion59ModuleZMod :
    Module (ZMod 59) (ClassTorsion59 K) :=
  AddSubgroup.torsionBy.zmodModule

local instance instClassTorsion59ModulePadicInt :
    Module (PadicInt 59) (ClassTorsion59 K) :=
  Module.compHom (ClassTorsion59 K) PadicInt.toZMod

/-- The genuine chi=15 class projector, regarded over the field `ZMod 59`.
The underlying additive map is unchanged; this merely exposes the scalar
structure already carried by the 59-torsion target. -/
noncomputable def irregularClassProjectorZMod59 :
    ClassTorsion59 K →ₗ[ZMod 59] ClassTorsion59 K :=
  (cyclotomicClassProjector59 K irregularCharacter59).toAddMonoidHom
    |>.toZModLinearMap 59

@[simp]
theorem irregularClassProjectorZMod59_apply (q : ClassTorsion59 K) :
    irregularClassProjectorZMod59 K q =
      cyclotomicClassProjector59 K irregularCharacter59 q :=
  rfl

/-- The actual image of the canonical irregular class projector. -/
noncomputable def irregularClassCharacterLine59 :
    Submodule (ZMod 59) (ClassTorsion59 K) :=
  LinearMap.range (irregularClassProjectorZMod59 K)

/-- A class fixed by the canonical projector lies in its genuine image
line.  No idempotence theorem is needed for this direction. -/
theorem mem_irregularClassCharacterLine59_of_projector_fixed
    {q : ClassTorsion59 K}
    (hq : cyclotomicClassProjector59 K irregularCharacter59 q = q) :
    q ∈ irregularClassCharacterLine59 K := by
  refine ⟨q, ?_⟩
  simpa using hq

variable {zeta : K} {hZeta : IsPrimitiveRoot zeta 59}
  {S : Fermat.FiftyNine.Conservation.FermatState.PrimitiveSecondCaseSolution}
  {hz : (59 : ℤ) ∣ S.z}

/-- The three precise arithmetic inputs from the Kummer--Artin strategy
imply the formerly opaque pointwise-faithfulness premise at the selected
relation-7A class. -/
theorem selectedClassGauge59_eq_zero_of_readout_eq_zero_of_characterLine
    (readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59)
    (pair : StateLinkedIdealPair hZeta S hz)
    (seated :
      cyclotomicClassProjector59 K irregularCharacter59
          (selectedClassGauge59 pair) = selectedClassGauge59 pair)
    (rank_one : Module.finrank (ZMod 59)
      (irregularClassCharacterLine59 K) = 1)
    (readout_ne_zero :
      readout.comp (irregularClassCharacterLine59 K).subtype ≠ 0)
    (readout_zero : readout (selectedClassGauge59 pair) = 0) :
    selectedClassGauge59 pair = 0 := by
  exact eq_zero_of_mem_finrank_one_of_readout_restrict_ne_zero
    (irregularClassCharacterLine59 K) readout rank_one readout_ne_zero
    (mem_irregularClassCharacterLine59_of_projector_fixed K seated)
    readout_zero

/-- W7 with the Kummer--Artin work separated into character seating,
one-dimensionality of the actual projector image, and nonvanishing of the
constructed readout on that image. -/
theorem strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA_of_characterLine
    (y : RelaxedCarrier827 K)
    (readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59)
    (factorization :
      readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
        strictTameOrbitFunctional827 K y)
    (pair : StateLinkedIdealPair hZeta S hz)
    (seated :
      cyclotomicClassProjector59 K irregularCharacter59
          (selectedClassGauge59 pair) = selectedClassGauge59 pair)
    (rank_one : Module.finrank (ZMod 59)
      (irregularClassCharacterLine59 K) = 1)
    (readout_ne_zero :
      readout.comp (irregularClassCharacterLine59 K).subtype ≠ 0) :
    strictTameOrbitFunctional827 K y
        (fermatFactorSelmerDifference59 pair) = 0 ↔
      pair.ledger.VandiverSevenA 0 1 := by
  exact
    strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA_of_pointwiseFaithful
      K y readout factorization pair
      (selectedClassGauge59_eq_zero_of_readout_eq_zero_of_characterLine
        K readout pair seated rank_one readout_ne_zero)

end Fermat.FiftyNine.Conservation.CharacterLinePointwiseFaithfulness59
