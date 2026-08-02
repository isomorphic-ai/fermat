/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# N4 conservation verification

This non-imported audit leaf checks the public axiom surface of the complete
balance-inside-drain cone and checks that declarations from the forbidden
fixed-exponent FLT(4) cone remain unknown after importing the public N4 rung.
-/
import Fermat.Conservation.GuardDependsOn
import Fermat.Four.Conservation

/-! ## Accounted-transfer dependency gates -/

#guard_depends_on
  Fermat.Four.Conservation.PrimitiveSolution.accountTransfer,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Four.Conservation.PrimitiveSolution.accountTransfer_stock_decomposition,
  Fermat.Conservation.Transfer.available_eq
#guard_depends_on
  Fermat.Four.Conservation.PrimitiveSolution.charged_descent_transfer,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Four.Conservation.PrimitiveSolution.stateCharge_pos,
  Fermat.Conservation.Transfer.available_lt_of_spent_pos
#guard_depends_on
  Fermat.Four.Conservation.PrimitiveSolution.charged_descent,
  Fermat.Four.Conservation.PrimitiveSolution.charged_descent_transfer
#guard_depends_on
  Fermat.Four.Conservation.PrimitiveSolution.charged_descent,
  Fermat.Conservation.Transfer.available_eq
#guard_depends_on
  Fermat.Four.Conservation.not_stronger_solution_conservation,
  Fermat.Four.Conservation.PrimitiveSolution.charged_descent_transfer
#guard_depends_on
  Fermat.Four.Conservation.not_stronger_solution_conservation,
  Fermat.Conservation.Transfer.available_eq
#guard_depends_on
  Fermat.Four.holdsAt_four_conservation,
  Fermat.Four.Conservation.PrimitiveSolution.charged_descent_transfer

/--
info: 'Fermat.HoldsAt.mono_of_dvd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.HoldsAt.mono_of_dvd

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
info: 'Fermat.Two.charge_conserved' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Two.charge_conserved

/--
info: 'Fermat.Two.charge_ledger' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Two.charge_ledger

/--
info: 'Fermat.Two.pythagoras' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Two.pythagoras

/--
info: 'Fermat.Two.emptyCoupling_of_additive' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Two.emptyCoupling_of_additive

/--
info: 'Fermat.Two.pythagoras_conserved' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Two.pythagoras_conserved

/--
info: 'Fermat.Four.Conservation.pythagorean_balance_engine' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Four.Conservation.pythagorean_balance_engine

/--
info: 'Fermat.Four.Conservation.StrongerSolution.charge_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Four.Conservation.StrongerSolution.charge_pos

/--
info: 'Fermat.Four.Conservation.PrimitiveSolution.stateCharge_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Four.Conservation.PrimitiveSolution.stateCharge_pos

/--
info: 'Fermat.Four.Conservation.PrimitiveSolution.charged_descent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Four.Conservation.PrimitiveSolution.charged_descent

/--
info: 'Fermat.Four.Conservation.not_stronger_solution_conservation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Four.Conservation.not_stronger_solution_conservation

/--
info: 'Fermat.Four.holdsAt_four_conservation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Four.holdsAt_four_conservation

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
error: Unknown identifier `Fermat.holdsAt_four`
-/
#guard_msgs in
#check Fermat.holdsAt_four

/--
error: Unknown identifier `Fermat42.not_minimal`
-/
#guard_msgs in
#check Fermat42.not_minimal
