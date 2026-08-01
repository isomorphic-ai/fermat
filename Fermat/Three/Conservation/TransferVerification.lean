/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Executable audit for the accounted cubic descent

This non-imported leaf verifies that the integer cubic spine and the actual
generalized Euler successor use the route-neutral transfer implementation in
their proof values.  It is deliberately separate from the N59 structural
audit, whose import boundary excludes `Fermat.Statement`.
-/
import Fermat.Conservation.GuardDependsOn
import Fermat.Three.Conservation.Euler

#check Fermat.Three.Conservation.drainTransfer
#check Fermat.Three.Conservation.Euler.GeneralizedStatement.Solution.accountTransfer
#check Fermat.Three.Conservation.Euler.GeneralizedStatement.euler_descent_transfer

#guard_depends_on Fermat.Three.Conservation.ledger_identity,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on Fermat.Three.Conservation.drainCharge_pred_lt,
  Fermat.Three.Conservation.drainTransfer_stock_decomposition
#guard_depends_on Fermat.Three.Conservation.drainCharge_pred_lt,
  Fermat.Conservation.Transfer.available_eq
#guard_depends_on Fermat.Three.Conservation.drainCharge_pred_lt,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Three.Conservation.Euler.GeneralizedStatement.Solution.accountTransfer_projections,
  Fermat.Conservation.Transfer.endpoint_conservation
#guard_depends_on
  Fermat.Three.Conservation.Euler.GeneralizedStatement.Solution.accountTransfer_projections,
  Fermat.Conservation.Transfer.available_eq
#guard_depends_on
  Fermat.Three.Conservation.Euler.GeneralizedStatement.euler_descent_transfer,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Three.Conservation.Euler.GeneralizedStatement.euler_descent_charge_lt,
  Fermat.Three.Conservation.Euler.GeneralizedStatement.euler_descent_transfer
#guard_depends_on
  Fermat.Three.Conservation.Euler.GeneralizedStatement.euler_descent_charge_lt,
  Fermat.Conservation.Transfer.available_eq
#guard_depends_on Fermat.Three.holdsAt_three_conservation,
  Fermat.Three.Conservation.Euler.GeneralizedStatement.euler_descent_transfer

/--
info: 'Fermat.Three.Conservation.Euler.GeneralizedStatement.euler_descent_transfer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Three.Conservation.Euler.GeneralizedStatement.euler_descent_transfer

/--
info: 'Fermat.Three.Conservation.Euler.GeneralizedStatement.euler_descent_charge_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Three.Conservation.Euler.GeneralizedStatement.euler_descent_charge_lt
