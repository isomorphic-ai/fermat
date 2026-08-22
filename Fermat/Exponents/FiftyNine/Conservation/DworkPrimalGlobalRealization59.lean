/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The global-unit boundary for the depth-15 Dwork primal factor

The explicit Dwork principal unit is constructed in the completed local
integer ring.  A tempting globalization route would be to realize it by a
global ring unit, insert that unit through the strict Selmer sequence, and
then project to the irregular character seat.

This file proves that such a route cannot supply the Artin-visible primal
class required by the Dwork nonvanishing argument.  Every projected global
unit remains in the unit leg of the exact unit--Selmer--class sequence, so
its genuine class gauge, and hence its canonical mode-44 class readout, is
zero.  The desired primal realization therefore has to be a non-unit strict
Selmer class with the prescribed lambda localization.
-/
import Fermat.Exponents.FiftyNine.Conservation.CyclotomicUnitSelmerNaturality59
import Fermat.Exponents.FiftyNine.Conservation.DworkSeatedLambdaMeter59
import Fermat.Exponents.FiftyNine.Conservation.IrregularPrimalClassGaugeBridge827
import Fermat.Experiments.Conservation.GuardDependsOn

open scoped MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000

namespace Fermat.FiftyNine.Conservation.DworkPrimalGlobalRealization59

open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.SelmerEigenspace
open CanonicalIrregularMode827
open CanonicalModeFortyFourClassFactorization827
open CanonicalW1PoitouTateReduction827
open CyclotomicSelmerAction59
open CyclotomicSelmerClassNaturality59
open CyclotomicUnitSelmerNaturality59
open DworkSeatedLambdaMeter59
open IrregularPrimalClassGaugeBridge827
open SplitPrimeFourier827
open VostokovLocalization59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

/-- Insert a genuine global unit class into the strict Selmer carrier and
then project it to the canonical irregular character seat. -/
noncomputable def projectedGlobalUnitPrimal59
    (u : UnitModP (NumberField.RingOfIntegers K) 59) :
    OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59 :=
  characterProjectorAt (cyclotomicStrictSelmerRepresentation59 K)
    irregularCharacter59
    (unitInclusion
      (R := NumberField.RingOfIntegers K) (K := K) (p := 59) u)

omit [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- The class gauge kills an unprojected global-unit Selmer class by the
exactness of the genuine unit--Selmer--class sequence. -/
theorem strictSelmerClassLinearMap59_unitInclusion_eq_zero
    (u : UnitModP (NumberField.RingOfIntegers K) 59) :
    strictSelmerClassLinearMap59 K
        (unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59) u) = 0 := by
  have hmem :
      unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59) u ∈
        Set.range
          (unitInclusion
            (R := NumberField.RingOfIntegers K) (K := K) (p := 59)) :=
    ⟨u, rfl⟩
  have hzero :
      selmerClassProjection
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
          (unitInclusion
            (R := NumberField.RingOfIntegers K) (K := K) (p := 59) u) = 0 := by
    have hkernel := hmem
    rw [(selmerClassSequenceRealization
      (R := NumberField.RingOfIntegers K) (K := K)
      (p := 59)).exact_at_selmer] at hkernel
    change selmerClassProjection
        (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
        (unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59) u) = 0 at hkernel
    exact hkernel
  change selmerClassProjection
      (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
      (unitInclusion
        (R := NumberField.RingOfIntegers K) (K := K) (p := 59) u) = 0
  exact hzero

/-- Projecting a global-unit class cannot escape the class-kernel: the
actual irregular primal class gauge is still zero. -/
theorem irregularPrimalClassGauge59_projectedGlobalUnitPrimal59_eq_zero
    (u : UnitModP (NumberField.RingOfIntegers K) 59) :
    irregularPrimalClassGauge59 K (projectedGlobalUnitPrimal59 K u) = 0 := by
  rw [irregularPrimalClassGauge59_apply]
  change strictSelmerClassLinearMap59 K
      ((characterProjectorAt
        (cyclotomicStrictSelmerRepresentation59 K)
        irregularCharacter59
        (unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59) u)).1) = 0
  calc
    strictSelmerClassLinearMap59 K
        ((characterProjectorAt
          (cyclotomicStrictSelmerRepresentation59 K)
          irregularCharacter59
          (unitInclusion
            (R := NumberField.RingOfIntegers K) (K := K) (p := 59) u)).1) =
      cyclotomicClassProjector59 K irregularCharacter59
        (strictSelmerClassLinearMap59 K
          (unitInclusion
            (R := NumberField.RingOfIntegers K) (K := K) (p := 59) u)) :=
      strictSelmerClassLinearMap59_characterProjector K irregularCharacter59 _
    _ = 0 := by
      rw [strictSelmerClassLinearMap59_unitInclusion_eq_zero, map_zero]

/-- Consequently the canonical mode-44 Artin/class-gauge reading of every
projected global unit is zero. -/
theorem canonicalModeFortyFourClassReadout827_projectedGlobalUnitPrimal59_eq_zero
    (u : UnitModP (NumberField.RingOfIntegers K) 59) :
    canonicalModeFortyFourClassReadout827 K
        (irregularPrimalClassGauge59 K
          (projectedGlobalUnitPrimal59 K u)) = 0 := by
  rw [irregularPrimalClassGauge59_projectedGlobalUnitPrimal59_eq_zero,
    map_zero]

/-- **No-go theorem for the global-unit shortcut.**  No projected global
unit can simultaneously realize the depth-15 Dwork lambda factor and carry
the nonzero mode-44 class reading required by the Artin route.  The
localization equation is retained in the statement to make clear that the
contradiction is already forced by the class-gauge half. -/
theorem not_exists_projectedGlobalUnitPrimal59_dwork_localization_and_artin :
    ¬ ∃ u : UnitModP (NumberField.RingOfIntegers K) 59,
      irregularPrimalLambdaLocalization827
          (projectedGlobalUnitPrimal59 K u) =
        dworkSeatedLambdaPrimalFifteen59 (K := K) ∧
      canonicalModeFortyFourClassReadout827 K
          (irregularPrimalClassGauge59 K
            (projectedGlobalUnitPrimal59 K u)) ≠ 0 := by
  rintro ⟨u, _hlocal, hread⟩
  exact hread
    (canonicalModeFortyFourClassReadout827_projectedGlobalUnitPrimal59_eq_zero
      K u)

/-! ## The honest role left for global units -/

/-- A global unit can still serve as an *affine correction* to an already
Artin-visible non-unit Selmer class.  If its projected localization is the
difference between the desired Dwork factor and the base localization, then
adding it fixes the local coordinate while exactness guarantees that the
nonzero class reading is conserved.

This theorem makes the remaining local--global unit problem explicit; it
does not assert that such a correcting unit exists. -/
theorem exists_dworkPrimalArtin_of_projectedGlobalUnit_adjustment
    (x₀ : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59)
    (artin_ne_zero :
      canonicalModeFortyFourClassReadout827 K
        (irregularPrimalClassGauge59 K x₀) ≠ 0)
    (u : UnitModP (NumberField.RingOfIntegers K) 59)
    (adjusts :
      irregularPrimalLambdaLocalization827 (K := K)
          (projectedGlobalUnitPrimal59 K u) =
        dworkSeatedLambdaPrimalFifteen59 (K := K) -
          irregularPrimalLambdaLocalization827 (K := K) x₀) :
    ∃ x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
        irregularCharacter59,
      irregularPrimalLambdaLocalization827 (K := K) x =
          dworkSeatedLambdaPrimalFifteen59 (K := K) ∧
        canonicalModeFortyFourClassReadout827 K
          (irregularPrimalClassGauge59 K x) ≠ 0 := by
  refine ⟨x₀ + projectedGlobalUnitPrimal59 K u, ?_, ?_⟩
  · rw [map_add, adjusts]
    abel
  · rw [map_add,
      irregularPrimalClassGauge59_projectedGlobalUnitPrimal59_eq_zero,
      add_zero]
    exact artin_ne_zero

/-! ## Kernel-trust and dependency audit -/

/--
info: 'Fermat.FiftyNine.Conservation.DworkPrimalGlobalRealization59.irregularPrimalClassGauge59_projectedGlobalUnitPrimal59_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  irregularPrimalClassGauge59_projectedGlobalUnitPrimal59_eq_zero

/--
info: 'Fermat.FiftyNine.Conservation.DworkPrimalGlobalRealization59.not_exists_projectedGlobalUnitPrimal59_dwork_localization_and_artin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  not_exists_projectedGlobalUnitPrimal59_dwork_localization_and_artin

#guard_depends_on
  not_exists_projectedGlobalUnitPrimal59_dwork_localization_and_artin,
  canonicalModeFortyFourClassReadout827_projectedGlobalUnitPrimal59_eq_zero

#guard_depends_on
  exists_dworkPrimalArtin_of_projectedGlobalUnit_adjustment,
  irregularPrimalClassGauge59_projectedGlobalUnitPrimal59_eq_zero

end Fermat.FiftyNine.Conservation.DworkPrimalGlobalRealization59
