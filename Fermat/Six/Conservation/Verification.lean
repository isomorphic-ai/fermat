/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# N6 conservation verification

This non-imported executable audit leaf checks the public axiom surface of
the complete native exponent-six conservation cone.  It also checks that
fixed exponent-three and exponent-four theorems, the proposition-level
divisibility fold, and every Ladder fold or transport sentinel remain
unknown after importing only the public N6 rung.
-/
import Fermat.Conservation.GuardDependsOn
import Fermat.Six.Conservation

/-! ## Ledger-literal gate -/

/-! The native factor, cube balance, origin-carrying successor, and public
closure are projections of literal global accounts and Transfers. -/

#guard_depends_on Fermat.Six.Conservation.sixth_ledger,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on Fermat.Six.Conservation.pythagorean_cube_balance,
  Fermat.Conservation.Ledger.conservation_identity

#guard_depends_on Fermat.Six.Conservation.PrimitiveSolution.native_ledger,
  Fermat.Six.Conservation.sixth_ledger
#guard_depends_on Fermat.Six.Conservation.PrimitiveSolution.native_ledger,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on Fermat.Six.Conservation.PrimitiveSolution.cube_balance,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on Fermat.Six.Conservation.OrientedState.accountTransfer,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on Fermat.Six.Conservation.OrientedState.accountTransfer,
  Fermat.Six.Conservation.PrimitiveSolution.native_ledger
#guard_depends_on
  Fermat.Six.Conservation.OrientedState.accountTransfer_factor_ledgers,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Six.Conservation.OrientedState.accountTransfer_factor_ledgers,
  Fermat.Conservation.Transfer.endpoint_conservation
#guard_depends_on
  Fermat.Six.Conservation.OrientedState.accountTransfer_stock_decomposition,
  Fermat.Conservation.Transfer.available_eq
#guard_depends_on
  Fermat.Six.Conservation.OrientedState.charged_descent_transfer,
  Fermat.Six.Conservation.OrientedState.accountTransfer
#guard_depends_on Fermat.Six.Conservation.exists_orientedStateCharge_lt,
  Fermat.Conservation.Transfer.available_eq
#guard_depends_on Fermat.Six.Conservation.exists_orientedStateCharge_lt,
  Fermat.Six.Conservation.OrientedState.charged_descent_transfer
#guard_depends_on
  Fermat.Six.Conservation.PrimitiveSolution.impossible_conservation,
  Fermat.Conservation.Transfer.available_eq
#guard_depends_on
  Fermat.Six.Conservation.PrimitiveSolution.impossible_conservation,
  Fermat.Six.Conservation.OrientedState.charged_descent_transfer
#guard_depends_on Fermat.Six.holdsAt_six_conservation,
  Fermat.Conservation.Transfer.available_eq
#guard_depends_on Fermat.Six.holdsAt_six_conservation,
  Fermat.Six.Conservation.OrientedState.charged_descent_transfer

/--
info: 'Fermat.Conservation.noInfinitePositiveChargeDrain' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.noInfinitePositiveChargeDrain

/--
info: 'Fermat.Conservation.impossible_of_strict_charge_drain' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.impossible_of_strict_charge_drain

/--
info: 'Fermat.Six.Conservation.embeddedCubeRoot_cube' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Six.Conservation.embeddedCubeRoot_cube

/--
info: 'Fermat.Six.Conservation.charge_formula' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Six.Conservation.charge_formula

/--
info: 'Fermat.Six.Conservation.charge_mul' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Six.Conservation.charge_mul

/--
info: 'Fermat.Six.Conservation.cofactor_charge' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Six.Conservation.cofactor_charge

/--
info: 'Fermat.Six.Conservation.sixth_ledger' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Six.Conservation.sixth_ledger

/--
info: 'Fermat.Six.Conservation.pythagorean_cube_balance' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Six.Conservation.pythagorean_cube_balance

/--
info: 'Fermat.Six.Conservation.embeddedCubeRoot_sub_one' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Six.Conservation.embeddedCubeRoot_sub_one

/--
info: 'Fermat.Six.Conservation.embeddedCubeRoot_sub_one_charge' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Six.Conservation.embeddedCubeRoot_sub_one_charge

/--
info: 'Fermat.Six.Conservation.drainUnit_charge' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Six.Conservation.drainUnit_charge

/--
info: 'Fermat.Six.Conservation.charge_pow' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Six.Conservation.charge_pow

/--
info: 'Fermat.Six.Conservation.drainCharge_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Six.Conservation.drainCharge_eq

/--
info: 'Fermat.Six.Conservation.drainCharge_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Six.Conservation.drainCharge_lt

/--
info: 'Fermat.Six.Conservation.PrimitiveSolution.pairwise_isCoprime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Six.Conservation.PrimitiveSolution.pairwise_isCoprime

/--
info: 'Fermat.Six.Conservation.PrimitiveSolution.native_ledger' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Six.Conservation.PrimitiveSolution.native_ledger

/--
info: 'Fermat.Six.Conservation.PrimitiveSolution.cube_balance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Six.Conservation.PrimitiveSolution.cube_balance

/--
info: 'Fermat.Six.Conservation.PrimitiveSolution.three_divisibility_pattern' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Six.Conservation.PrimitiveSolution.three_divisibility_pattern

/--
info: 'Fermat.Conservation.CubicChargedDescent.RawState.exists_oriented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.CubicChargedDescent.RawState.exists_oriented

/--
info: 'Fermat.Conservation.CubicChargedDescent.OrientedState.exists_multiplicity_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.CubicChargedDescent.OrientedState.exists_multiplicity_lt

/--
info: 'Fermat.Six.Conservation.lambda_not_dvd_intCast_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Six.Conservation.lambda_not_dvd_intCast_sq

/--
info: 'Fermat.Six.Conservation.lambda_dvd_intCast_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Six.Conservation.lambda_dvd_intCast_sq

/--
info: 'Fermat.Six.Conservation.PrimitiveSolution.rawState_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Six.Conservation.PrimitiveSolution.rawState_nonempty

/--
info: 'Fermat.Six.Conservation.PrimitiveSolution.orientedState_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Six.Conservation.PrimitiveSolution.orientedState_nonempty

/--
info: 'Fermat.Six.Conservation.orientedStateCharge_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Six.Conservation.orientedStateCharge_pos

/--
info: 'Fermat.Six.Conservation.exists_orientedStateCharge_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Six.Conservation.exists_orientedStateCharge_lt

/--
info: 'Fermat.Six.Conservation.PrimitiveSolution.impossible_conservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Six.Conservation.PrimitiveSolution.impossible_conservation

/--
info: 'Fermat.Six.holdsAt_six_conservation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Six.holdsAt_six_conservation

/--
error: Unknown identifier `fermatLastTheoremThree`
-/
#guard_msgs in
#check fermatLastTheoremThree

/--
error: Unknown identifier `fermatLastTheoremThree_case_1`
-/
#guard_msgs in
#check fermatLastTheoremThree_case_1

/--
error: Unknown identifier `fermatLastTheoremThree_of_dvd_a_of_gcd_eq_one_of_case2`
-/
#guard_msgs in
#check fermatLastTheoremThree_of_dvd_a_of_gcd_eq_one_of_case2

/--
error: Unknown identifier `fermatLastTheoremThree_of_three_dvd_only_c`
-/
#guard_msgs in
#check fermatLastTheoremThree_of_three_dvd_only_c

/--
error: Unknown identifier `FermatLastTheoremForThreeGen`
-/
#guard_msgs in
#check FermatLastTheoremForThreeGen

/--
error: Unknown identifier `FermatLastTheoremForThree_of_FermatLastTheoremThreeGen`
-/
#guard_msgs in
#check FermatLastTheoremForThree_of_FermatLastTheoremThreeGen

/--
error: Unknown identifier `FermatLastTheoremForThreeGen.Solution`
-/
#guard_msgs in
#check FermatLastTheoremForThreeGen.Solution

/--
error: Unknown identifier `Fermat.holdsAt_three`
-/
#guard_msgs in
#check Fermat.holdsAt_three

/--
error: Unknown identifier `Fermat.Three.holdsAt_three_conservation`
-/
#guard_msgs in
#check Fermat.Three.holdsAt_three_conservation

/--
error: Unknown identifier `Fermat.Three.Conservation.ledger_identity`
-/
#guard_msgs in
#check Fermat.Three.Conservation.ledger_identity

/--
error: Unknown identifier `Fermat.Three.Conservation.Euler.GeneralizedStatement`
-/
#guard_msgs in
#check Fermat.Three.Conservation.Euler.GeneralizedStatement

/--
error: Unknown identifier `Fermat.Three.Conservation.Euler.GeneralizedStatement.Solution`
-/
#guard_msgs in
#check Fermat.Three.Conservation.Euler.GeneralizedStatement.Solution

/--
error: Unknown identifier `Fermat.Three.Conservation.Euler.GeneralizedStatement.euler_descent_charge_lt`
-/
#guard_msgs in
#check Fermat.Three.Conservation.Euler.GeneralizedStatement.euler_descent_charge_lt

/--
error: Unknown identifier `Fermat.Ladder.Three.sharpeningClaim_checked`
-/
#guard_msgs in
#check Fermat.Ladder.Three.sharpeningClaim_checked

/--
error: Unknown identifier `fermatLastTheoremFour`
-/
#guard_msgs in
#check fermatLastTheoremFour

/--
error: Unknown identifier `not_fermat_42`
-/
#guard_msgs in
#check not_fermat_42

/--
error: Unknown identifier `Fermat42.not_minimal`
-/
#guard_msgs in
#check Fermat42.not_minimal

/--
error: Unknown constant `FermatLastTheorem.of_odd_primes`
-/
#guard_msgs in
#check FermatLastTheorem.of_odd_primes

/--
error: Unknown identifier `Fermat.holdsAt_four`
-/
#guard_msgs in
#check Fermat.holdsAt_four

/--
error: Unknown constant `Fermat.HoldsAt.mono_of_dvd`
-/
#guard_msgs in
#check Fermat.HoldsAt.mono_of_dvd

/--
error: Unknown identifier `Fermat.Ladder.awarenessFold`
-/
#guard_msgs in
#check Fermat.Ladder.awarenessFold

/--
error: Unknown identifier `Fermat.Ladder.structureFold`
-/
#guard_msgs in
#check Fermat.Ladder.structureFold

/--
error: Unknown identifier `Fermat.Ladder.sharpeningFold`
-/
#guard_msgs in
#check Fermat.Ladder.sharpeningFold

/--
error: Unknown identifier `Fermat.Ladder.presenceFold`
-/
#guard_msgs in
#check Fermat.Ladder.presenceFold

/--
error: Unknown identifier `Fermat.Ladder.alignmentFold`
-/
#guard_msgs in
#check Fermat.Ladder.alignmentFold

/--
error: Unknown identifier `Fermat.Ladder.agencyFold`
-/
#guard_msgs in
#check Fermat.Ladder.agencyFold

/--
error: Unknown identifier `Fermat.Ladder.flexibilityFold`
-/
#guard_msgs in
#check Fermat.Ladder.flexibilityFold

/--
error: Unknown identifier `Fermat.Ladder.sevenFolds`
-/
#guard_msgs in
#check Fermat.Ladder.sevenFolds

/--
error: Unknown identifier `Fermat.Ladder.CaseTrace`
-/
#guard_msgs in
#check Fermat.Ladder.CaseTrace

/--
error: Unknown identifier `Fermat.Ladder.Four.holdsAt_of_presenceClaim`
-/
#guard_msgs in
#check Fermat.Ladder.Four.holdsAt_of_presenceClaim

/--
error: Unknown identifier `Fermat.Ladder.Six.holdsAt_of_awarenessClaim`
-/
#guard_msgs in
#check Fermat.Ladder.Six.holdsAt_of_awarenessClaim

/--
error: Unknown identifier `Fermat.Ladder.Eight.holdsAt_of_awarenessClaim`
-/
#guard_msgs in
#check Fermat.Ladder.Eight.holdsAt_of_awarenessClaim

/--
error: Unknown identifier `Fermat.Ladder.Nine.holdsAt_of_awarenessClaim`
-/
#guard_msgs in
#check Fermat.Ladder.Nine.holdsAt_of_awarenessClaim

/--
error: Unknown identifier `Fermat.Ladder.Ten.holdsAt_of_awarenessClaim`
-/
#guard_msgs in
#check Fermat.Ladder.Ten.holdsAt_of_awarenessClaim

/--
error: Unknown identifier `Fermat.Ladder.Twelve.holdsAt_of_awarenessClaim`
-/
#guard_msgs in
#check Fermat.Ladder.Twelve.holdsAt_of_awarenessClaim

/--
error: Unknown identifier `Fermat.Ladder.Fourteen.holdsAt_of_awarenessClaim`
-/
#guard_msgs in
#check Fermat.Ladder.Fourteen.holdsAt_of_awarenessClaim

/--
error: Unknown identifier `Fermat.Ladder.Six.awarenessClaim`
-/
#guard_msgs in
#check Fermat.Ladder.Six.awarenessClaim

/--
error: Unknown identifier `Fermat.Ladder.Six.awarenessClaim_checked`
-/
#guard_msgs in
#check Fermat.Ladder.Six.awarenessClaim_checked

/--
error: Unknown identifier `Fermat.Ladder.Six.flexibilityClaim_checked`
-/
#guard_msgs in
#check Fermat.Ladder.Six.flexibilityClaim_checked
