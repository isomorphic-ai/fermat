/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Dwork principal-unit candidates for the seated local receipt

This file constructs two honest principal units in the completed Dwork
integer ring,

`1 + dworkParameter^15` and `1 + dworkParameter^44`.

They are transported through the proved Dwork-to-valued-integer equivalence,
included in the pinned lambda completion, and cast to the concrete Fermat-side
lambda-local field.  Their actual local Kummer classes are then sent through
the genuine power-15 and power-44 character projectors.

The projected classes land in the requested literal seats by construction.
No nonvanishing statement, cup-product statement, or unproved action
covariance is asserted here.
-/
import Fermat.Exponents.FiftyNine.Conservation.LambdaLocalKummerCharacterSeat59
import Fermat.Exponents.FiftyNine.Conservation.LocalIntegralTrace59
import Fermat.Exponents.FiftyNine.Conservation.CriticalUnitCoefficient59

open scoped NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.DworkPrincipalUnitCandidates59

open KummerCriterion.CyclotomicUnits.PadicLogSetup
open KummerCriterion.CyclotomicUnits.PadicLogSetup.DworkParameter
open Fermat.Conservation.LocalKummerTransport
open Fermat.Conservation.WildKummerPairing
open Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59
open Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59
open Fermat.FiftyNine.Conservation.LambdaLocalKummerCharacterSeat59
open Fermat.FiftyNine.Conservation.LambdaLocalKummerClassAction59
open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.LocalCyclotomicTrace59
open Fermat.FiftyNine.Conservation.LocalIntegralTrace59

set_option maxRecDepth 100000

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

noncomputable local instance instLambdaLocalKummerClass59ModuleZMod :
    Module (ZMod 59) (LambdaLocalKummerClass59 K) :=
  AddCommGroup.zmodModule
    (n := 59) (G := LambdaLocalKummerClass59 K)
    (lambdaLocalKummerClass59_nsmul_eq_zero K)

/-- A power of the corrected Dwork parameter lies in the matching power of
the completed lambda ideal. -/
theorem dworkParameter_pow_mem_lambdaIdeal_pow59 (depth : ℕ) :
    dworkParameter 59 K ^ depth ∈
      (dworkCompleteLambdaIdeal 59 K) ^ depth := by
  rw [dworkCompleteLambdaIdeal_eq_dworkParameterIdeal]
  exact Ideal.pow_mem_pow
    (Ideal.mem_span_singleton_self (dworkParameter 59 K)) depth

/-- The principal-unit candidate `1 + dworkParameter^depth` in the genuine
completed Dwork integer ring.  Positive depth puts its additive coordinate
in the completed lambda ideal, hence Henselianity makes it a unit. -/
noncomputable def dworkPrincipalUnitAtDepth59
    (depth : ℕ) (hdepth : depth ≠ 0) :
    (DworkCompleteIntegerRing 59 K)ˣ :=
  (isUnit_one_add_of_mem_dworkCompleteLambdaIdeal
    (p := 59) (K := K)
    (Ideal.pow_le_self hdepth
      (dworkParameter_pow_mem_lambdaIdeal_pow59 K depth))).unit

@[simp]
theorem dworkPrincipalUnitAtDepth59_val
    (depth : ℕ) (hdepth : depth ≠ 0) :
    (dworkPrincipalUnitAtDepth59 K depth hdepth :
        DworkCompleteIntegerRing 59 K) =
      1 + dworkParameter 59 K ^ depth := by
  exact IsUnit.unit_spec _

/-- The additive coordinate of the candidate is exactly the stated Dwork
power. -/
theorem dworkPrincipalUnitAtDepth59_sub_one
    (depth : ℕ) (hdepth : depth ≠ 0) :
    (dworkPrincipalUnitAtDepth59 K depth hdepth :
        DworkCompleteIntegerRing 59 K) - 1 =
      dworkParameter 59 K ^ depth := by
  rw [dworkPrincipalUnitAtDepth59_val]
  ring

/-- The candidate belongs to the depth-`depth` principal-unit filtration.
This is membership, not a claim that the depth is exact. -/
theorem dworkPrincipalUnitAtDepth59_sub_one_mem
    (depth : ℕ) (hdepth : depth ≠ 0) :
    (dworkPrincipalUnitAtDepth59 K depth hdepth :
        DworkCompleteIntegerRing 59 K) - 1 ∈
      (dworkCompleteLambdaIdeal 59 K) ^ depth := by
  rw [dworkPrincipalUnitAtDepth59_sub_one]
  exact dworkParameter_pow_mem_lambdaIdeal_pow59 K depth

/-- The genuine Dwork principal-unit candidate at depth `15`. -/
noncomputable def dworkPrincipalUnitFifteen59 :
    (DworkCompleteIntegerRing 59 K)ˣ :=
  dworkPrincipalUnitAtDepth59 K 15 (by norm_num)

/-- The genuine Dwork principal-unit candidate at depth `44`. -/
noncomputable def dworkPrincipalUnitFortyFour59 :
    (DworkCompleteIntegerRing 59 K)ˣ :=
  dworkPrincipalUnitAtDepth59 K 44 (by norm_num)

@[simp]
theorem dworkPrincipalUnitFifteen59_val :
    (dworkPrincipalUnitFifteen59 K : DworkCompleteIntegerRing 59 K) =
      1 + dworkParameter 59 K ^ 15 :=
  dworkPrincipalUnitAtDepth59_val K 15 (by norm_num)

@[simp]
theorem dworkPrincipalUnitFortyFour59_val :
    (dworkPrincipalUnitFortyFour59 K : DworkCompleteIntegerRing 59 K) =
      1 + dworkParameter 59 K ^ 44 :=
  dworkPrincipalUnitAtDepth59_val K 44 (by norm_num)

/-! ## Transport to the actual lambda-local field -/

/-- Transport a Dwork principal unit through the proved algebra equivalence
to the actual valuation integer ring. -/
noncomputable def dworkPrincipalUnitValuedInteger59
    (depth : ℕ) (hdepth : depth ≠ 0) :
    (ValuedIntegerRing 59 K)ˣ :=
  Units.map (dworkValuedAlgEquiv59 K).toRingHom
    (dworkPrincipalUnitAtDepth59 K depth hdepth)

/-- Include the transported integer unit in the pinned lambda completion. -/
noncomputable def dworkPrincipalUnitPinnedLambda59
    (depth : ℕ) (hdepth : depth ≠ 0) :
    (LambdaCompletion59 K)ˣ :=
  Units.map (valuedIntegerToLambdaCompletion59 K).toMonoidHom
    (dworkPrincipalUnitValuedInteger59 K depth hdepth)

/-- Cast the pinned completion unit to the concrete Fermat-side lambda-local
field used by the Kummer representation and the wild receipt. -/
noncomputable def dworkPrincipalUnitLocal59
    (depth : ℕ) (hdepth : depth ≠ 0) :
    (LambdaLocalField59 K)ˣ :=
  Units.map (valuedCompletionEquivLambdaField59 K).toRingHom
    (dworkPrincipalUnitPinnedLambda59 K depth hdepth)

/-- The transported depth-15 unit in the actual local field. -/
noncomputable def dworkPrincipalUnitLocalFifteen59 :
    (LambdaLocalField59 K)ˣ :=
  dworkPrincipalUnitLocal59 K 15 (by norm_num)

/-- The transported depth-44 unit in the actual local field. -/
noncomputable def dworkPrincipalUnitLocalFortyFour59 :
    (LambdaLocalField59 K)ˣ :=
  dworkPrincipalUnitLocal59 K 44 (by norm_num)

/-! ## Actual Kummer classes and their honest projections -/

/-- The actual local Kummer class of the transported depth-15 unit. -/
noncomputable def dworkPrincipalKummerClassFifteen59 :
    LambdaLocalKummerClass59 K :=
  classOfUnit 59 (LambdaLocalField59 K)
    (Additive.ofMul (dworkPrincipalUnitLocalFifteen59 K))

/-- The actual local Kummer class of the transported depth-44 unit. -/
noncomputable def dworkPrincipalKummerClassFortyFour59 :
    LambdaLocalKummerClass59 K :=
  classOfUnit 59 (LambdaLocalField59 K)
    (Additive.ofMul (dworkPrincipalUnitLocalFortyFour59 K))

/-- The depth-15 candidate after applying the genuine power-15 group
idempotent.  Its codomain is the literal power-15 local Kummer seat. -/
noncomputable def projectedDworkPrincipalKummerClassFifteen59 :
    lambdaLocalKummerPowerSeat59 K (15 : ZMod 58) :=
  lambdaLocalKummerPowerProjector59 K 15
    (dworkPrincipalKummerClassFifteen59 K)

/-- The depth-44 candidate after applying the genuine power-44 group
idempotent.  Its codomain is the literal power-44 local Kummer seat. -/
noncomputable def projectedDworkPrincipalKummerClassFortyFour59 :
    lambdaLocalKummerPowerSeat59 K (44 : ZMod 58) :=
  lambdaLocalKummerPowerProjector59 K 44
    (dworkPrincipalKummerClassFortyFour59 K)

/-- The projected depth-15 Kummer class satisfies the exact simultaneous
power-15 eigenlaw. -/
theorem projectedDworkPrincipalKummerClassFifteen59_mem_powerSeat :
    (projectedDworkPrincipalKummerClassFifteen59 K :
        LambdaLocalKummerClass59 K) ∈
      lambdaLocalKummerPowerSeat59 K (15 : ZMod 58) :=
  (projectedDworkPrincipalKummerClassFifteen59 K).property

/-- The projected depth-44 Kummer class satisfies the exact simultaneous
power-44 eigenlaw. -/
theorem projectedDworkPrincipalKummerClassFortyFour59_mem_powerSeat :
    (projectedDworkPrincipalKummerClassFortyFour59 K :
        LambdaLocalKummerClass59 K) ∈
      lambdaLocalKummerPowerSeat59 K (44 : ZMod 58) :=
  (projectedDworkPrincipalKummerClassFortyFour59 K).property

/-- Expanded eigenlaw for the projected depth-15 candidate. -/
theorem projectedDworkPrincipalKummerClassFifteen59_eigen
    (sigma : Fermat.FiftyNine.Conservation.SplitPrimeFourier827.GaloisIndex59) :
    lambdaLocalKummerClassRepresentation59 K sigma
        (projectedDworkPrincipalKummerClassFifteen59 K :
          LambdaLocalKummerClass59 K) =
      ((Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.powerCharacter59
          15 sigma : (ZMod 59)ˣ) : ZMod 59) •
        (projectedDworkPrincipalKummerClassFifteen59 K :
          LambdaLocalKummerClass59 K) :=
  (mem_lambdaLocalKummerPowerSeat59_iff K 15 _).mp
    (projectedDworkPrincipalKummerClassFifteen59_mem_powerSeat K) sigma

/-- Expanded eigenlaw for the projected depth-44 candidate. -/
theorem projectedDworkPrincipalKummerClassFortyFour59_eigen
    (sigma : Fermat.FiftyNine.Conservation.SplitPrimeFourier827.GaloisIndex59) :
    lambdaLocalKummerClassRepresentation59 K sigma
        (projectedDworkPrincipalKummerClassFortyFour59 K :
          LambdaLocalKummerClass59 K) =
      ((Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.powerCharacter59
          44 sigma : (ZMod 59)ˣ) : ZMod 59) •
        (projectedDworkPrincipalKummerClassFortyFour59 K :
          LambdaLocalKummerClass59 K) :=
  (mem_lambdaLocalKummerPowerSeat59_iff K 44 _).mp
    (projectedDworkPrincipalKummerClassFortyFour59_mem_powerSeat K) sigma

/-! ## Kernel-trust audit -/

/--
info: 'Fermat.FiftyNine.Conservation.DworkPrincipalUnitCandidates59.dworkPrincipalUnitFifteen59_val' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms dworkPrincipalUnitFifteen59_val

/--
info: 'Fermat.FiftyNine.Conservation.DworkPrincipalUnitCandidates59.projectedDworkPrincipalKummerClassFifteen59_eigen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms projectedDworkPrincipalKummerClassFifteen59_eigen

/--
info: 'Fermat.FiftyNine.Conservation.DworkPrincipalUnitCandidates59.projectedDworkPrincipalKummerClassFortyFour59_eigen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms projectedDworkPrincipalKummerClassFortyFour59_eigen

end Fermat.FiftyNine.Conservation.DworkPrincipalUnitCandidates59
