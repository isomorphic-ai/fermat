/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# N5 conservation verification

This non-imported executable audit leaf checks the public axiom surface of
the complete golden-ring conservation cone and verifies that declarations
from every layer of the repository's earlier exponent-five route remain
unknown after importing only the public N5 conservation rung.
-/
import Fermat.Conservation.GuardDependsOn
import Fermat.Five.Conservation

/-! ## Ledger-literal gate -/

/-! Every entry and terminal branch in the complete N5 cone retains the
native golden-norm ledger through its elaborated proof value. -/

#guard_depends_on
  Fermat.Five.Conservation.PrimitiveFifthSolution.equation,
  Fermat.Five.Conservation.quintic_ledger
#guard_depends_on Fermat.Five.Conservation.fermatEquation_five_ledger,
  Fermat.Five.Conservation.quintic_ledger
#guard_depends_on Fermat.Five.Conservation.not_five_dvd_c_seed,
  Fermat.Five.Conservation.quintic_ledger
#guard_depends_on Fermat.Five.Conservation.five_dvd_c_seed,
  Fermat.Five.Conservation.quintic_ledger
#guard_depends_on Fermat.Five.Conservation.not_five_dvd_c_impossible,
  Fermat.Five.Conservation.quintic_ledger
#guard_depends_on Fermat.Five.Conservation.five_dvd_c_impossible,
  Fermat.Five.Conservation.quintic_ledger
#guard_depends_on Fermat.Five.holdsAt_five_conservation,
  Fermat.Five.Conservation.quintic_ledger

/-! The formerly scalar gauge and charged-descent claims are now literal
projections of full accounted transactions. -/

#check Fermat.Five.Conservation.chargeLedger
#check Fermat.Five.Conservation.gaugeTransfer
#check Fermat.Five.Conservation.gaugeTransfer_columns
#check Fermat.Five.Conservation.ChargedState.accountLedger
#check Fermat.Five.Conservation.ChargedState.accountTransfer
#check Fermat.Five.Conservation.ChargedState.charged_descent_transfer
#check Fermat.Five.Conservation.not_five_dvd_c_charged_transfer
#check Fermat.Five.Conservation.five_dvd_c_charged_transfer

#guard_depends_on Fermat.Five.Conservation.gaugeTransfer,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on Fermat.Five.Conservation.gaugeTransfer_columns,
  Fermat.Five.Conservation.gaugeTransfer
#guard_depends_on Fermat.Five.Conservation.charge_gauge_invariant,
  Fermat.Five.Conservation.gaugeTransfer
#guard_depends_on Fermat.Five.Conservation.charge_gauge_invariant,
  Fermat.Conservation.Transfer.available_eq
#guard_depends_on
  Fermat.Five.Conservation.ChargedState.charge_gauge_invariant,
  Fermat.Five.Conservation.ChargedState.gaugeTransfer
#guard_depends_on
  Fermat.Five.Conservation.NotFiveDvdCState.charge_gauge_invariant,
  Fermat.Five.Conservation.ChargedState.gaugeTransfer
#guard_depends_on
  Fermat.Five.Conservation.FiveDvdCState.charge_gauge_invariant,
  Fermat.Five.Conservation.ChargedState.gaugeTransfer
#guard_depends_on
  Fermat.Five.Conservation.ChargedState.charged_descent_transfer,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on Fermat.Five.Conservation.not_five_dvd_c_charged_transfer,
  Fermat.Five.Conservation.ChargedState.charged_descent_transfer
#guard_depends_on Fermat.Five.Conservation.five_dvd_c_charged_transfer,
  Fermat.Five.Conservation.ChargedState.charged_descent_transfer
#guard_depends_on Fermat.Five.Conservation.not_five_dvd_c_charged_descent,
  Fermat.Five.Conservation.not_five_dvd_c_charged_transfer
#guard_depends_on Fermat.Five.Conservation.not_five_dvd_c_charged_descent,
  Fermat.Conservation.Transfer.stock_decomposition_of_credit_eq
#guard_depends_on Fermat.Five.Conservation.five_dvd_c_charged_descent,
  Fermat.Five.Conservation.five_dvd_c_charged_transfer
#guard_depends_on Fermat.Five.Conservation.five_dvd_c_charged_descent,
  Fermat.Conservation.Transfer.stock_decomposition_of_credit_eq
#guard_depends_on Fermat.Five.Conservation.not_five_dvd_c_impossible,
  Fermat.Five.Conservation.not_five_dvd_c_charged_transfer
#guard_depends_on Fermat.Five.Conservation.five_dvd_c_impossible,
  Fermat.Five.Conservation.five_dvd_c_charged_transfer
#guard_depends_on Fermat.Five.holdsAt_five_conservation,
  Fermat.Five.Conservation.not_five_dvd_c_charged_transfer
#guard_depends_on Fermat.Five.holdsAt_five_conservation,
  Fermat.Five.Conservation.five_dvd_c_charged_transfer

/--
error: Unknown constant `Fermat.HoldsAt.mono_of_dvd`
-/
#guard_msgs in
#check Fermat.HoldsAt.mono_of_dvd

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
info: 'Fermat.Five.Conservation.PrimitiveFifthSolution.equation' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.PrimitiveFifthSolution.equation

/--
info: 'Fermat.Five.Conservation.ChargedState.coordinate_pos' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.ChargedState.coordinate_pos

/--
info: 'Fermat.Five.Conservation.ChargedState.stateCharge_eq_coordinate_sq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.ChargedState.stateCharge_eq_coordinate_sq

/--
info: 'Fermat.Five.Conservation.ChargedState.stateCharge_pos' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.ChargedState.stateCharge_pos

/--
info: 'Fermat.Five.Conservation.ChargedState.charge_gauge_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.ChargedState.charge_gauge_invariant

/--
info: 'Fermat.Five.Conservation.NotFiveDvdCState.stateCharge_pos' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.NotFiveDvdCState.stateCharge_pos

/--
info: 'Fermat.Five.Conservation.NotFiveDvdCState.charge_gauge_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.NotFiveDvdCState.charge_gauge_invariant

/--
info: 'Fermat.Five.Conservation.FiveDvdCState.stateCharge_pos' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.FiveDvdCState.stateCharge_pos

/--
info: 'Fermat.Five.Conservation.FiveDvdCState.charge_gauge_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.FiveDvdCState.charge_gauge_invariant

/--
info: 'Fermat.Five.Conservation.not_five_dvd_c_seed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.not_five_dvd_c_seed

/--
info: 'Fermat.Five.Conservation.five_dvd_c_seed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.five_dvd_c_seed

/--
info: 'Fermat.Five.Conservation.not_five_dvd_c_charged_descent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.not_five_dvd_c_charged_descent

/--
info: 'Fermat.Five.Conservation.five_dvd_c_charged_descent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.five_dvd_c_charged_descent

/--
info: 'Fermat.Five.Conservation.not_five_dvd_c_impossible' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.not_five_dvd_c_impossible

/--
info: 'Fermat.Five.Conservation.five_dvd_c_impossible' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.five_dvd_c_impossible

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.FifthEquation.oddCore_of_oppositeParity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.FifthEquation.oddCore_of_oppositeParity

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.FifthEquation.evenCore_of_odd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.FifthEquation.evenCore_of_odd

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.FifthEquation.exists_core' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.FifthEquation.exists_core

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.F_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.F_pos

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.five_coprime_F' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.five_coprime_F

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.s_coprime_F' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.s_coprime_F

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.not_five_dvd_F' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.not_five_dvd_F

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.sixteen_dvd_F_of_odd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.sixteen_dvd_F_of_odd

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.odd_F_of_odd_even' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.odd_F_of_odd_even

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.odd_F_of_even_odd' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.odd_F_of_even_odd

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.odd_factor_coprime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.odd_factor_coprime

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.even_factor_coprime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.even_factor_coprime

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.OddState.split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.OddState.split

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.EvenState.split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.EvenState.split

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.norm_identity' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.norm_identity

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.OddState.normData' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.OddState.normData

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.EvenState.normData' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.EvenState.normData

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.EvenCoordinates.ofOppositeParity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.EvenCoordinates.ofOppositeParity

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.OddState.extractCoordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.OddState.extractCoordinates

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.EvenState.extractCoordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.EvenState.extractCoordinates

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.OddCoordinates.five_dvd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.OddCoordinates.five_dvd

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.OddCoordinates.smaller' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.OddCoordinates.smaller

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.EvenCoordinates.five_dvd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.EvenCoordinates.five_dvd

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.EvenCoordinates.smaller' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.EvenCoordinates.smaller

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.OddState.nextOfCoordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.OddState.nextOfCoordinates

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.EvenState.nextOfCoordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.EvenState.nextOfCoordinates

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.OddState.descends' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.OddState.descends

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.EvenState.descends' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.EvenState.descends

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.FifthEquation.ne_zero' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.FifthEquation.ne_zero

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.FifthEquation.neg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.FifthEquation.neg

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.FifthEquation.exists_positive_right' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.FifthEquation.exists_positive_right

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.exists_fifthEquation_of_pairwise_of_five_dvd_right' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.exists_fifthEquation_of_pairwise_of_five_dvd_right

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.exists_fifthEquation_of_pairwise_of_not_five_dvd_right' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.exists_fifthEquation_of_pairwise_of_not_five_dvd_right

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.exists_fifthEquation_of_pairwise' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.exists_fifthEquation_of_pairwise

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.OddCore.initialNormData' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.OddCore.initialNormData

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.EvenCore.initialNormData' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.EvenCore.initialNormData

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.OddCore.oddState_of_coordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.OddCore.oddState_of_coordinates

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.EvenCore.evenState_of_coordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.EvenCore.evenState_of_coordinates

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.OddCore.exists_oddState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.OddCore.exists_oddState

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.EvenCore.exists_evenState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.EvenCore.exists_evenState

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.H_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.H_pos

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.r_coprime_H' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.r_coprime_H

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.five_coprime_H' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.five_coprime_H

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.sixteen_dvd_H_of_odd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.sixteen_dvd_H_of_odd

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.odd_H_of_odd_even' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.odd_H_of_odd_even

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.split_odd_core' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.split_odd_core

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.split_even_core' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.split_even_core

/--
info: 'Fermat.Five.Conservation.Reconstruction.five_dvd_one_of_sum_fifth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.five_dvd_one_of_sum_fifth

/--
info: 'Fermat.Five.Conservation.Reconstruction.five_dvd_one_of_fifth_add_fifth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.five_dvd_one_of_fifth_add_fifth

/--
info: 'Fermat.Five.Conservation.Reconstruction.PowerExtraction.intCast_quarticNat' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.PowerExtraction.intCast_quarticNat

/--
info: 'Fermat.Five.Conservation.Reconstruction.PowerExtraction.quartic_pos_of_ne_zero_left' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.PowerExtraction.quartic_pos_of_ne_zero_left

/--
info: 'Fermat.Five.Conservation.Reconstruction.PowerExtraction.quartic_natAbs' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.PowerExtraction.quartic_natAbs

/--
info: 'Fermat.Five.Conservation.Reconstruction.PowerExtraction.zsqrtd_fifth_re' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.PowerExtraction.zsqrtd_fifth_re

/--
info: 'Fermat.Five.Conservation.Reconstruction.PowerExtraction.zsqrtd_fifth_im' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.PowerExtraction.zsqrtd_fifth_im

/--
info: 'Fermat.Five.Conservation.Reconstruction.PowerExtraction.isCoprime_of_mul_add' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.PowerExtraction.isCoprime_of_mul_add

/--
info: 'Fermat.Five.Conservation.Reconstruction.PowerExtraction.conjugates_isCoprime_of_int' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.PowerExtraction.conjugates_isCoprime_of_int

/--
info: 'Fermat.Five.Conservation.Reconstruction.PowerExtraction.norm_isCoprime_left' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.PowerExtraction.norm_isCoprime_left

/--
info: 'Fermat.Five.Conservation.Reconstruction.PowerExtraction.embedded_conjugates_isCoprime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.PowerExtraction.embedded_conjugates_isCoprime

/--
info: 'Fermat.Five.Conservation.Reconstruction.PowerExtraction.half_conjugates_isCoprime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.PowerExtraction.half_conjugates_isCoprime

/--
info: 'Fermat.Five.Conservation.Reconstruction.PowerExtraction.odd_im_fifth_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.PowerExtraction.odd_im_fifth_iff

/--
info: 'Fermat.Five.Conservation.Reconstruction.PowerExtraction.even_im_fifth_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.PowerExtraction.even_im_fifth_iff

/--
info: 'Fermat.Five.Conservation.Reconstruction.PowerExtraction.five_dvd_im_fifth' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.PowerExtraction.five_dvd_im_fifth

/--
info: 'Fermat.Five.Conservation.Reconstruction.PowerExtraction.phi_remainder_eq_zero' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.PowerExtraction.phi_remainder_eq_zero

/--
info: 'Fermat.Five.Conservation.Reconstruction.PowerExtraction.exists_fifthPower_of_mul_eq_fifth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.PowerExtraction.exists_fifthPower_of_mul_eq_fifth

/--
info: 'Fermat.Five.Conservation.Reconstruction.PowerExtraction.exists_fifthPower_of_coprime_conjugates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.PowerExtraction.exists_fifthPower_of_coprime_conjugates

/--
info: 'Fermat.Five.Conservation.Reconstruction.PowerExtraction.exists_eq_embed_of_even_im' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.PowerExtraction.exists_eq_embed_of_even_im

/--
info: 'Fermat.Five.Conservation.Reconstruction.PowerExtraction.suborder_coordinates_isCoprime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.PowerExtraction.suborder_coordinates_isCoprime

/--
info: 'Fermat.Five.Conservation.Reconstruction.PowerExtraction.half_coordinates_isCoprime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.PowerExtraction.half_coordinates_isCoprime

/--
info: 'Fermat.Five.Conservation.Reconstruction.PowerExtraction.oppositeParity_of_odd_norm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.PowerExtraction.oppositeParity_of_odd_norm

/--
info: 'Fermat.Five.Conservation.Reconstruction.PowerExtraction.half_fifth_coordinate_formulas' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.PowerExtraction.half_fifth_coordinate_formulas

/--
info: 'Fermat.Five.Conservation.Reconstruction.PowerExtraction.exists_oppositeParity_fifthPower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.PowerExtraction.exists_oppositeParity_fifthPower

/--
info: 'Fermat.Five.Conservation.Reconstruction.PowerExtraction.exists_oppositeParity_coordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.PowerExtraction.exists_oppositeParity_coordinates

/--
info: 'Fermat.Five.Conservation.Reconstruction.PowerExtraction.exists_odd_half_fifthPower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.PowerExtraction.exists_odd_half_fifthPower

/--
info: 'Fermat.Five.Conservation.Reconstruction.PowerExtraction.exists_odd_half_coordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.PowerExtraction.exists_odd_half_coordinates

/--
info: 'Fermat.Five.Conservation.Reconstruction.PowerExtraction.exists_odd_coordinates_nat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.PowerExtraction.exists_odd_coordinates_nat

/--
info: 'Fermat.Five.Conservation.Reconstruction.PowerExtraction.exists_oppositeParity_coordinates_nat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.PowerExtraction.exists_oppositeParity_coordinates_nat

/--
info: 'Fermat.Five.Conservation.Reconstruction.exists_pow_eq_of_associated_pow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.exists_pow_eq_of_associated_pow

/--
info: 'Fermat.Five.Conservation.Reconstruction.exists_pow_eq_of_mul_eq_pow_left' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.exists_pow_eq_of_mul_eq_pow_left

/--
info: 'Fermat.Five.Conservation.Reconstruction.exists_pow_eq_of_mul_eq_pow_right' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.exists_pow_eq_of_mul_eq_pow_right

/--
info: 'Fermat.Five.Conservation.Reconstruction.exists_two_pow_eq_of_mul_eq_pow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.exists_two_pow_eq_of_mul_eq_pow

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.pairwise_isCoprime_of_gcd_eq_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.pairwise_isCoprime_of_gcd_eq_one

/--
info: 'Fermat.Five.Conservation.Reconstruction.Dirichlet.holdsAt_five_of_fifthEquationImpossible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.Reconstruction.Dirichlet.holdsAt_five_of_fifthEquationImpossible

/--
info: 'Fermat.Five.Conservation.coe_goldenPhiUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.coe_goldenPhiUnit

/--
info: 'Fermat.Five.Conservation.goldenPhiUnit_pow_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.goldenPhiUnit_pow_injective

/--
info: 'Fermat.Five.Conservation.infinite_goldenUnitGroup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.infinite_goldenUnitGroup

/--
info: 'Fermat.Five.Conservation.goldenNorm_mul' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.goldenNorm_mul

/--
info: 'Fermat.Five.Conservation.goldenCharge_mul' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.goldenCharge_mul

/--
info: 'Fermat.Five.Conservation.goldenNorm_unit_eq_one_or_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.goldenNorm_unit_eq_one_or_neg_one

/--
info: 'Fermat.Five.Conservation.goldenCharge_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.goldenCharge_unit

/--
info: 'Fermat.Five.Conservation.charge_gauge_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.charge_gauge_invariant

/--
info: 'Fermat.Five.Conservation.quinticCofactor_eq_goldenNorm' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.quinticCofactor_eq_goldenNorm

/--
info: 'Fermat.Five.Conservation.quintic_ledger' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.quintic_ledger

/--
info: 'Fermat.Five.Conservation.fermatEquation_five_ledger' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.fermatEquation_five_ledger

/--
info: 'Fermat.Five.Conservation.sqrtFiveDrainQuantum_sq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.sqrtFiveDrainQuantum_sq

/--
info: 'Fermat.Five.Conservation.sqrtFiveDrainQuantum_norm' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.sqrtFiveDrainQuantum_norm

/--
info: 'Fermat.Five.Conservation.sqrtFiveDrainQuantum_charge' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.Conservation.sqrtFiveDrainQuantum_charge

/--
info: 'Fermat.Five.holdsAt_five_conservation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Five.holdsAt_five_conservation

/--
error: Unknown identifier `Fermat.Five.five_dvd_one_of_sum_fifth`
-/
#guard_msgs in
#check Fermat.Five.five_dvd_one_of_sum_fifth

/--
error: Unknown identifier `Fermat.Five.exists_two_pow_eq_of_mul_eq_pow`
-/
#guard_msgs in
#check Fermat.Five.exists_two_pow_eq_of_mul_eq_pow

/--
error: Unknown identifier `Fermat.Five.PowerExtraction.exists_fifthPower_of_coprime_conjugates`
-/
#guard_msgs in
#check Fermat.Five.PowerExtraction.exists_fifthPower_of_coprime_conjugates

/--
error: Unknown identifier `Fermat.Five.Dirichlet.FifthEquation`
-/
#guard_msgs in
#check Fermat.Five.Dirichlet.FifthEquation

/--
error: Unknown identifier `Fermat.Five.Dirichlet.OddState`
-/
#guard_msgs in
#check Fermat.Five.Dirichlet.OddState

/--
error: Unknown identifier `Fermat.Five.Dirichlet.H`
-/
#guard_msgs in
#check Fermat.Five.Dirichlet.H

/--
error: Unknown identifier `Fermat.Five.Dirichlet.OddCore`
-/
#guard_msgs in
#check Fermat.Five.Dirichlet.OddCore

/--
error: Unknown identifier `Fermat.Five.Dirichlet.OddInitialCoordinates`
-/
#guard_msgs in
#check Fermat.Five.Dirichlet.OddInitialCoordinates

/--
error: Unknown identifier `Fermat.Five.Dirichlet.FifthEquationImpossible`
-/
#guard_msgs in
#check Fermat.Five.Dirichlet.FifthEquationImpossible

/--
error: Unknown identifier `Fermat.Five.Dirichlet.holdsAt_five_of_fifthEquationImpossible`
-/
#guard_msgs in
#check Fermat.Five.Dirichlet.holdsAt_five_of_fifthEquationImpossible

/--
error: Unknown identifier `Fermat.Five.Dirichlet.fifthEquationImpossible`
-/
#guard_msgs in
#check Fermat.Five.Dirichlet.fifthEquationImpossible

/--
error: Unknown identifier `Fermat.Five.Dirichlet.holdsAt_five_dirichlet`
-/
#guard_msgs in
#check Fermat.Five.Dirichlet.holdsAt_five_dirichlet

/--
error: Unknown identifier `Fermat.holdsAt_five`
-/
#guard_msgs in
#check Fermat.holdsAt_five
