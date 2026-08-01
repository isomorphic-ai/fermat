/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# N7 conservation verification

This non-imported executable audit leaf checks every public theorem in the
strict exponent-seven conservation cone.  It also verifies that the earlier
Lebesgue and Lamé routes, the root endpoint, the divisibility shortcut,
every Ladder fold and transport, and fixed-exponent FLT results from Mathlib
or flt-regular remain unknown after importing only the public N7 rung.
-/
import Fermat.Conservation.GuardDependsOn
import Fermat.Seven.Conservation

/-! ## Ledger-literal gate -/

/-! Both terminal case closures and every downstream N7 public assembly
retain the septic ledger through their elaborated proof values. -/

#guard_depends_on
  Fermat.Seven.Conservation.Reconstruction.Lebesgue.seven_dvd_t_branch_impossible,
  Fermat.Seven.Conservation.septic_ledger
#guard_depends_on
  Fermat.Seven.Conservation.Reconstruction.Lebesgue.not_seven_dvd_t_branch_impossible,
  Fermat.Seven.Conservation.septic_ledger
#guard_depends_on
  Fermat.Seven.Conservation.Reconstruction.Lebesgue.ternaryOnlyTrivial_lebesgue,
  Fermat.Seven.Conservation.septic_ledger
#guard_depends_on
  Fermat.Seven.Conservation.Reconstruction.Lebesgue.holdsAt_seven_lebesgue,
  Fermat.Seven.Conservation.septic_ledger
#guard_depends_on Fermat.Seven.holdsAt_seven_conservation,
  Fermat.Seven.Conservation.septic_ledger

/-! ## Shared conservation floor -/

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

/-! ## Class-number-one certificate -/

/--
info: 'Fermat.Seven.Conservation.minkowskiFloor_seven' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.minkowskiFloor_seven

/--
info: 'Fermat.Seven.Conservation.ringOfIntegers_isPrincipalIdealRing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.ringOfIntegers_isPrincipalIdealRing

/--
info: 'Fermat.Seven.Conservation.classNumber_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.classNumber_eq_one

/-! ## Cyclotomic charge, full rank-two gauge, ledger, and drain -/

/--
info: 'Fermat.Seven.Conservation.charge_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.charge_mul

/--
info: 'Fermat.Seven.Conservation.norm_unit_eq_one_or_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.norm_unit_eq_one_or_neg_one

/--
info: 'Fermat.Seven.Conservation.charge_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.charge_unit

/--
info: 'Fermat.Seven.Conservation.charge_unit_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.charge_unit_invariant

/--
info: 'Fermat.Seven.Conservation.gauge_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.gauge_decomposition

/--
info: 'Fermat.Seven.Conservation.unitRank_eq_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.unitRank_eq_two

/--
info: 'Fermat.Seven.Conservation.charge_gauge_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.charge_gauge_invariant

/--
info: 'Fermat.Seven.Conservation.charge_full_gauge_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.charge_full_gauge_invariant

/--
info: 'Fermat.Seven.Conservation.fundSystem_isMaxRank' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.fundSystem_isMaxRank

/--
info: 'Fermat.Seven.Conservation.gaugeRegulator_eq_fundSystem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.gaugeRegulator_eq_fundSystem

/--
info: 'Fermat.Seven.Conservation.gaugeRegulator_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.gaugeRegulator_pos

/--
info: 'Fermat.Seven.Conservation.rankTwoGauge_regulator' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.rankTwoGauge_regulator

/--
info: 'Fermat.Seven.Conservation.psiSeven_compressed' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.psiSeven_compressed

/--
info: 'Fermat.Seven.Conservation.psiSeven_difference' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.psiSeven_difference

/--
info: 'Fermat.Seven.Conservation.psiSeven_neg_compressed' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.psiSeven_neg_compressed

/--
info: 'Fermat.Seven.Conservation.septic_ledger' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.septic_ledger

/--
info: 'Fermat.Seven.Conservation.lambda_eq_neg_zeta_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.lambda_eq_neg_zeta_sub_one

/--
info: 'Fermat.Seven.Conservation.lambda_charge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.lambda_charge

/--
info: 'Fermat.Seven.Conservation.charge_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.charge_pow

/--
info: 'Fermat.Seven.Conservation.drainCharge_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.drainCharge_eq

/--
info: 'Fermat.Seven.Conservation.drainCharge_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.drainCharge_strictMono

/--
info: 'Fermat.Seven.Conservation.drainCharge_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.drainCharge_step

/-! ## Reconstructed symmetric and primitive arithmetic -/

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.u_eq_s_sq_sub' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.u_eq_s_sq_sub

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.v_eq_s_mul_sub_xyz' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.v_eq_s_mul_sub_xyz

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.seventh_power_identity' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.seventh_power_identity

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.s_pow_seven_eq_seven_mul_v_t_of_ternary' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.s_pow_seven_eq_seven_mul_v_t_of_ternary

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.exactly_one_even_of_ternary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.exactly_one_even_of_ternary

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.even_s_of_ternary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.even_s_of_ternary

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.odd_u_of_ternary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.odd_u_of_ternary

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.t_modEq_one_mod_four_of_ternary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.t_modEq_one_mod_four_of_ternary

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.isCoprime_t_xyz_of_ternary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.isCoprime_t_xyz_of_ternary

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.isCoprime_t_v_of_ternary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.isCoprime_t_v_of_ternary

/-! ## Reconstructed power allocation -/

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.t_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.t_nonneg

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.not_seven_dvd_of_lebesgue_power_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.not_seven_dvd_of_lebesgue_power_data

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.exists_power_data_of_lebesgue_of_not_seven_dvd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.exists_power_data_of_lebesgue_of_not_seven_dvd

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.exists_power_data_of_lebesgue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.exists_power_data_of_lebesgue

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.isCoprime_p_r_of_symmetric_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.isCoprime_p_r_of_symmetric_data

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.exists_power_data_of_symmetric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.exists_power_data_of_symmetric

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.exists_pairwise_power_data_of_symmetric_of_not_seven_dvd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.exists_pairwise_power_data_of_symmetric_of_not_seven_dvd

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.exists_pairwise_power_data_of_symmetric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.exists_pairwise_power_data_of_symmetric

/-! ## Reconstructed extraction and charged descent -/

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.exists_even_square_decomposition_nat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.exists_even_square_decomposition_nat

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.exists_even_square_decomposition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.exists_even_square_decomposition

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.exists_even_square_decomposition_coprime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.exists_even_square_decomposition_coprime

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.p_ne_zero_of_ternary_v_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.p_ne_zero_of_ternary_v_data

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.exists_descentEquation_of_power_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.exists_descentEquation_of_power_data

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.ChargedState.stateCharge_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.ChargedState.stateCharge_eq

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.ChargedState.stateCharge_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.ChargedState.stateCharge_pos

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.ChargedState.stateCharge_rankTwoGauge_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.ChargedState.stateCharge_rankTwoGauge_invariant

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.ChargedState.exists_stateCharge_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.ChargedState.exists_stateCharge_lt

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.ChargedState.impossible_conservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.ChargedState.impossible_conservation

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.descentEquation_impossible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.descentEquation_impossible

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.theoremI_r_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.theoremI_r_eq_zero

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.theoremI_impossible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.theoremI_impossible

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.holdsAt_seven_of_ternaryOnlyTrivial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.holdsAt_seven_of_ternaryOnlyTrivial

/-! ## Exact exceptional and ordinary branches -/

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.SevenDvdTBranchState.allocation_contradiction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.SevenDvdTBranchState.allocation_contradiction

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.SevenDvdTBranchState.stateCharge_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.SevenDvdTBranchState.stateCharge_eq

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.SevenDvdTBranchState.stateCharge_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.SevenDvdTBranchState.stateCharge_pos

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.SevenDvdTBranchState.stateCharge_rankTwoGauge_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.SevenDvdTBranchState.stateCharge_rankTwoGauge_invariant

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.SevenDvdTBranchState.exists_stateCharge_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.SevenDvdTBranchState.exists_stateCharge_lt

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.SevenDvdTBranchState.impossible_conservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.SevenDvdTBranchState.impossible_conservation

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.seven_dvd_t_branch_impossible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.seven_dvd_t_branch_impossible

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.not_seven_dvd_t_branch_impossible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.not_seven_dvd_t_branch_impossible

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.ternaryOnlyTrivial_lebesgue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.ternaryOnlyTrivial_lebesgue

/--
info: 'Fermat.Seven.Conservation.Reconstruction.Lebesgue.holdsAt_seven_lebesgue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.Conservation.Reconstruction.Lebesgue.holdsAt_seven_lebesgue

/-! ## Public endpoint -/

/--
info: 'Fermat.Seven.holdsAt_seven_conservation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Seven.holdsAt_seven_conservation

/-! ## Forbidden earlier exponent-seven routes -/

/--
error: Unknown identifier `Fermat.Seven.Lebesgue.DescentEquation`
-/
#guard_msgs in
#check Fermat.Seven.Lebesgue.DescentEquation

/--
error: Unknown identifier `Fermat.Seven.Lebesgue.descentEquation_impossible`
-/
#guard_msgs in
#check Fermat.Seven.Lebesgue.descentEquation_impossible

/--
error: Unknown identifier `Fermat.Seven.Lebesgue.exists_even_square_decomposition`
-/
#guard_msgs in
#check Fermat.Seven.Lebesgue.exists_even_square_decomposition

/--
error: Unknown identifier `Fermat.Seven.Lebesgue.p_ne_zero_of_ternary_v_data`
-/
#guard_msgs in
#check Fermat.Seven.Lebesgue.p_ne_zero_of_ternary_v_data

/--
error: Unknown identifier `Fermat.Seven.Lebesgue.exists_descentEquation_of_power_data`
-/
#guard_msgs in
#check Fermat.Seven.Lebesgue.exists_descentEquation_of_power_data

/--
error: Unknown identifier `Fermat.Seven.Lebesgue.exists_power_data_of_lebesgue`
-/
#guard_msgs in
#check Fermat.Seven.Lebesgue.exists_power_data_of_lebesgue

/--
error: Unknown identifier `Fermat.Seven.Lebesgue.exactly_one_even_of_ternary`
-/
#guard_msgs in
#check Fermat.Seven.Lebesgue.exactly_one_even_of_ternary

/--
error: Unknown identifier `Fermat.Seven.Lebesgue.holdsAt_seven_of_ternaryOnlyTrivial`
-/
#guard_msgs in
#check Fermat.Seven.Lebesgue.holdsAt_seven_of_ternaryOnlyTrivial

/--
error: Unknown identifier `Fermat.Seven.Lebesgue.seventh_power_identity`
-/
#guard_msgs in
#check Fermat.Seven.Lebesgue.seventh_power_identity

/--
error: Unknown identifier `Fermat.Seven.Lebesgue.ternaryOnlyTrivial_lebesgue`
-/
#guard_msgs in
#check Fermat.Seven.Lebesgue.ternaryOnlyTrivial_lebesgue

/--
error: Unknown identifier `Fermat.Seven.Lebesgue.holdsAt_seven_lebesgue`
-/
#guard_msgs in
#check Fermat.Seven.Lebesgue.holdsAt_seven_lebesgue

/--
error: Unknown identifier `Fermat.Seven.Lame.X`
-/
#guard_msgs in
#check Fermat.Seven.Lame.X

/--
error: Unknown identifier `Fermat.Seven.Lame.add_seventhPower_factorization`
-/
#guard_msgs in
#check Fermat.Seven.Lame.add_seventhPower_factorization

/--
error: Unknown identifier `Fermat.Seven.Lame.primitive_entry`
-/
#guard_msgs in
#check Fermat.Seven.Lame.primitive_entry

/--
error: Unknown identifier `Fermat.holdsAt_seven`
-/
#guard_msgs in
#check Fermat.holdsAt_seven

/--
error: Unknown constant `Fermat.HoldsAt.mono_of_dvd`
-/
#guard_msgs in
#check Fermat.HoldsAt.mono_of_dvd

/-! ## Forbidden Ladder folds and transports -/

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
error: Unknown identifier `Fermat.Ladder.Seven.awarenessClaim_checked`
-/
#guard_msgs in
#check Fermat.Ladder.Seven.awarenessClaim_checked

/--
error: Unknown identifier `Fermat.Ladder.Seven.run`
-/
#guard_msgs in
#check Fermat.Ladder.Seven.run

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

/-! ## Forbidden fixed-exponent FLT and flt-regular declarations -/

/--
error: Unknown constant `IsCyclotomicExtension.Rat.seven_pid`
-/
#guard_msgs in
#check IsCyclotomicExtension.Rat.seven_pid

/--
error: Unknown identifier `isRegularPrime_seven`
-/
#guard_msgs in
#check isRegularPrime_seven

/--
error: Unknown identifier `fermatLastTheoremSeven`
-/
#guard_msgs in
#check fermatLastTheoremSeven

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
