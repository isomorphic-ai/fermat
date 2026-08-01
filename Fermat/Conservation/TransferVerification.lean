/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Executable audit for Transfer and the IsoConserve tunnel

This non-imported leaf verifies the route-neutral transaction algebra, its
strict/floor projections, and both compiled directions of the vendored
scheduler correspondence.
-/
import Fermat.Conservation.GuardDependsOn
import Fermat.Conservation.IsoConserveBridge

open Fermat.Conservation

#check Transfer
#check Transfer.comp
#check Transfer.floor_hstep_of_positiveSteps
#check IsoConserveBridge.transfer_L1_conservation
#check IsoConserveBridge.ofBalancedStep
#check IsoConserveBridge.KummerNoether.schedulerStep_instantiates_transfer

/-! Core transactions retain the named endpoint identity, and the legacy
strict/floor vocabulary is downstream of their exact available equation. -/

#guard_depends_on Fermat.Conservation.Transfer.refl,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on Fermat.Conservation.Transfer.comp,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on Fermat.Conservation.Transfer.ofRepay,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on Fermat.Conservation.Transfer.available_lt_of_spent_pos,
  Fermat.Conservation.Transfer.available_eq
#guard_depends_on Fermat.Conservation.Transfer.floor_hstep_of_positiveSteps,
  Fermat.Conservation.Transfer.available_lt_of_spent_pos
#guard_depends_on
  Fermat.Conservation.Transfer.impossible_of_positive_transfer_drain,
  Fermat.Conservation.Transfer.floor_hstep_of_positiveSteps
#guard_depends_on
  Fermat.Conservation.Transfer.impossible_of_positive_transfer_drain,
  Fermat.Conservation.impossible_of_strict_charge_drain

/-! Both general tunnel directions and the concrete Kummer converse are
implementation dependencies, not merely matching theorem signatures. -/

#guard_depends_on
  Fermat.Conservation.IsoConserveBridge.transfer_L1_conservation,
  Fermat.Conservation.IsoConserveStatements.BalancedStep.L1_conservation
#guard_depends_on
  Fermat.Conservation.IsoConserveBridge.ofBalancedStep,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Conservation.IsoConserveBridge.ofBalancedStep_toBalancedStep,
  Fermat.Conservation.IsoConserveBridge.ofBalancedStep
#guard_depends_on
  Fermat.Conservation.IsoConserveBridge.KummerNoether.schedulerStep_instantiates_transfer,
  Fermat.Conservation.IsoConserveBridge.KummerNoether.principalizeTransfer
#guard_depends_on
  Fermat.Conservation.IsoConserveBridge.KummerNoether.schedulerStep_instantiates_transfer,
  Fermat.Conservation.IsoConserveBridge.KummerNoether.evidenceTransfer
#guard_depends_on
  Fermat.Conservation.IsoConserveBridge.KummerNoether.schedulerStep_charge_conserved_via_transfer,
  Fermat.Conservation.IsoConserveBridge.KummerNoether.schedulerStep_instantiates_transfer
#guard_depends_on
  Fermat.Conservation.IsoConserveBridge.KummerNoether.schedulerStep_charge_conserved_via_transfer,
  Fermat.Conservation.IsoConserveBridge.KummerNoether.transfer_schedulerCharge_conserved

/--
info: 'Fermat.Conservation.Transfer.comp' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Transfer.comp

/--
info: 'Fermat.Conservation.IsoConserveBridge.KummerNoether.schedulerStep_charge_conserved_via_transfer' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.IsoConserveBridge.KummerNoether.schedulerStep_charge_conserved_via_transfer
