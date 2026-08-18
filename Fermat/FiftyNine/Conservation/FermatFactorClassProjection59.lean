/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The conjugate Fermat factors in the actual class-group character seat

The normalized plus and minus Fermat factors already satisfy a clean
conjugation relation after projection to the canonical odd character.  The
strict Selmer class map is now known to intertwine the cyclotomic actions, so
that relation can be transported to the genuine `59`-torsion ideal class
group.

This file records the resulting class-level identities.  In particular, the
projected difference of the two allocated root classes is twice the projected
plus class.  The statewise Takagi theorem then kills both underlying root
classes, so the two projected Fermat modes and their difference have zero
class obstruction as actual consequences rather than supplied premises.
-/
import Fermat.FiftyNine.Conservation.CyclotomicSelmerClassNaturality59
import Fermat.FiftyNine.Conservation.FermatFactorSelmerGauge59
import Fermat.FiftyNine.Conservation.FermatStateTakagiSevenA59
import Fermat.FiftyNine.Conservation.NormalizationCorrectionProjection59

open scoped MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Fermat.FiftyNine.Conservation.FermatFactorClassProjection59

open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.SelmerEigenspace
open CanonicalIrregularMode827
open CyclotomicSelmerAction59
open CyclotomicSelmerClassNaturality59
open FermatFactorSelmerGauge59
open FermatFactorSelmerSource59
open FermatStateTakagiSevenA59
open NormalizationCorrectionProjection59
open SplitPrimeFourier827
open StateFactorPair
open VostokovLocalization59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  {zeta : K} {hZeta : IsPrimitiveRoot zeta 59}
  {S : Fermat.FiftyNine.Conservation.FermatState.PrimitiveSecondCaseSolution}
  {hz : (59 : ℤ) ∣ S.z}

local instance instClassTorsion59ModuleZMod :
    Module (ZMod 59) (ClassTorsion59 K) :=
  AddSubgroup.torsionBy.zmodModule

local instance instClassTorsion59ModulePadicInt :
    Module (PadicInt 59) (ClassTorsion59 K) :=
  Module.compHom (ClassTorsion59 K) PadicInt.toZMod

/-! ## Transport the clean conjugation relation to ideal classes -/

/-- In the actual `59`-torsion class group, the chi-15 projection of the
allocated minus root is the negative of the corresponding plus projection. -/
theorem allocatedRootClassPTorsion_one_projection_eq_neg_zero
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (pair : StateLinkedIdealPair hZeta S hz) :
    cyclotomicClassProjector59 K irregularCharacter59
        (allocatedRootClassPTorsion pair.ledger 1) =
      -cyclotomicClassProjector59 K irregularCharacter59
        (allocatedRootClassPTorsion pair.ledger 0) := by
  have hmode := congrArg Subtype.val
    (fermatMinusPrimalMode59_eq_neg_plus pair)
  have h :
      strictSelmerClassLinearMap59 K (fermatMinusPrimalMode59 pair).1 =
        -strictSelmerClassLinearMap59 K (fermatPlusPrimalMode59 pair).1 := by
    rw [hmode]
    exact map_neg (strictSelmerClassLinearMap59 K)
      (fermatPlusPrimalMode59 pair).1
  rw [fermatMinusPrimalMode59_classProjection,
    fermatPlusPrimalMode59_classProjection] at h
  exact h

/-- Consequently the projected difference of the two allocated classes is
the sum of two copies of the projected plus class. -/
theorem allocatedRootClassPTorsion_difference_projection
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (pair : StateLinkedIdealPair hZeta S hz) :
    cyclotomicClassProjector59 K irregularCharacter59
        (allocatedRootClassPTorsion pair.ledger 0 -
          allocatedRootClassPTorsion pair.ledger 1) =
      cyclotomicClassProjector59 K irregularCharacter59
          (allocatedRootClassPTorsion pair.ledger 0) +
        cyclotomicClassProjector59 K irregularCharacter59
          (allocatedRootClassPTorsion pair.ledger 0) := by
  rw [map_sub,
    allocatedRootClassPTorsion_one_projection_eq_neg_zero]
  abel

/-! ## The same identity on the genuine Fermat Selmer difference -/

/-- Projecting the actual plus-minus Selmer difference and then taking its
class obstruction gives twice the chi-15 projection of the allocated plus
root class. -/
theorem fermatFactorSelmerDifference59_projected_class
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (pair : StateLinkedIdealPair hZeta S hz) :
    strictSelmerClassLinearMap59 K
        ((characterProjectorAt
          (cyclotomicStrictSelmerRepresentation59 K)
          irregularCharacter59
          (fermatFactorSelmerDifference59 pair)).1) =
      cyclotomicClassProjector59 K irregularCharacter59
          (allocatedRootClassPTorsion pair.ledger 0) +
        cyclotomicClassProjector59 K irregularCharacter59
          (allocatedRootClassPTorsion pair.ledger 0) := by
  rw [strictSelmerClassLinearMap59_characterProjector]
  change cyclotomicClassProjector59 K irregularCharacter59
      (strictSelmerClassLinearMap59 K
        (fermatPlusStrictSelmer59 pair - fermatMinusStrictSelmer59 pair)) = _
  rw [map_sub]
  have hplus :
      strictSelmerClassLinearMap59 K (fermatPlusStrictSelmer59 pair) =
        allocatedRootClassPTorsion pair.ledger 0 := by
    apply Subtype.ext
    exact fermatPlusStrictSelmer59_idealClass pair
  have hminus :
      strictSelmerClassLinearMap59 K (fermatMinusStrictSelmer59 pair) =
        allocatedRootClassPTorsion pair.ledger 1 := by
    apply Subtype.ext
    exact fermatMinusStrictSelmer59_idealClass pair
  rw [hplus, hminus]
  exact allocatedRootClassPTorsion_difference_projection pair

/-- Equivalent scalar form: the projected class of the Fermat difference is
`2` times the projected plus class. -/
theorem fermatFactorSelmerDifference59_projected_class_eq_two_smul
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (pair : StateLinkedIdealPair hZeta S hz) :
    strictSelmerClassLinearMap59 K
        ((characterProjectorAt
          (cyclotomicStrictSelmerRepresentation59 K)
          irregularCharacter59
          (fermatFactorSelmerDifference59 pair)).1) =
      (2 : PadicInt 59) •
        cyclotomicClassProjector59 K irregularCharacter59
          (allocatedRootClassPTorsion pair.ledger 0) := by
  rw [fermatFactorSelmerDifference59_projected_class]
  exact (two_smul (PadicInt 59)
    (cyclotomicClassProjector59 K irregularCharacter59
      (allocatedRootClassPTorsion pair.ledger 0))).symm

/-! ## Takagi kills the actual projected obstructions -/

/-- The allocated plus root is zero already in the full class group, hence
also in its genuine 59-torsion subtype. -/
theorem allocatedRootClassPTorsion_zero_eq_zero_takagi
    (pair : StateLinkedIdealPair hZeta S hz) :
    allocatedRootClassPTorsion pair.ledger 0 = 0 := by
  apply Subtype.ext
  exact (rootClasses_eq_zero_takagi pair).1

/-- The same full-class-group vanishing for the allocated minus root. -/
theorem allocatedRootClassPTorsion_one_eq_zero_takagi
    (pair : StateLinkedIdealPair hZeta S hz) :
    allocatedRootClassPTorsion pair.ledger 1 = 0 := by
  apply Subtype.ext
  exact (rootClasses_eq_zero_takagi pair).2

/-- The plus Fermat mode has zero obstruction in the actual projected class
group. -/
theorem fermatPlusPrimalMode59_classProjection_eq_zero_takagi
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (pair : StateLinkedIdealPair hZeta S hz) :
    strictSelmerClassLinearMap59 K (fermatPlusPrimalMode59 pair).1 = 0 := by
  rw [fermatPlusPrimalMode59_classProjection,
    allocatedRootClassPTorsion_zero_eq_zero_takagi, map_zero]

/-- The minus Fermat mode has zero obstruction in the actual projected
class group. -/
theorem fermatMinusPrimalMode59_classProjection_eq_zero_takagi
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (pair : StateLinkedIdealPair hZeta S hz) :
    strictSelmerClassLinearMap59 K (fermatMinusPrimalMode59 pair).1 = 0 := by
  rw [fermatMinusPrimalMode59_classProjection,
    allocatedRootClassPTorsion_one_eq_zero_takagi, map_zero]

/-- The character-projected actual plus/minus Selmer difference has zero
class obstruction. -/
theorem fermatFactorSelmerDifference59_projected_class_eq_zero_takagi
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (pair : StateLinkedIdealPair hZeta S hz) :
    strictSelmerClassLinearMap59 K
        ((characterProjectorAt
          (cyclotomicStrictSelmerRepresentation59 K)
          irregularCharacter59
          (fermatFactorSelmerDifference59 pair)).1) = 0 := by
  rw [fermatFactorSelmerDifference59_projected_class_eq_two_smul,
    allocatedRootClassPTorsion_zero_eq_zero_takagi, map_zero, smul_zero]

end Fermat.FiftyNine.Conservation.FermatFactorClassProjection59
