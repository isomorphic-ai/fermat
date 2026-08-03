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
#check Heis.groupLaws
#check Heis.abelianizationHom
#check Heis.commutator_eq_area_center
#check AreaTransfer
#check AreaTransfer.comp
#check AreaTransfer.chain_projects
#check AreaTransfer.word_abelianization_of_hasLedgerShadow
#check AreaTransfer.no_erasure
#check AreaTransfer.central_coordinate_eq_zero_iff_exact_cancellation
#check IsoConserveBridge.transfer_L1_conservation
#check IsoConserveBridge.ofBalancedStep
#check IsoConserveBridge.PayloadDictionary
#check IsoConserveBridge.toPayloadBalancedStep
#check IsoConserveBridge.ofPayloadBalancedStep
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

/-! The vendored D=2 carrier retains each advertised structural law. -/

#guard_depends_on Fermat.Conservation.Heis.groupLaws,
  Fermat.Conservation.Heis.mul_assoc
#guard_depends_on Fermat.Conservation.Heis.groupLaws,
  Fermat.Conservation.Heis.one_mul
#guard_depends_on Fermat.Conservation.Heis.groupLaws,
  Fermat.Conservation.Heis.mul_one
#guard_depends_on Fermat.Conservation.Heis.groupLaws,
  Fermat.Conservation.Heis.inv_mul
#guard_depends_on Fermat.Conservation.Heis.groupLaws,
  Fermat.Conservation.Heis.mul_inv
#guard_depends_on Fermat.Conservation.Heis.eq_center_iff,
  Fermat.Conservation.Heis.central_iff
#guard_depends_on Fermat.Conservation.Heis.abelianizationHom,
  Fermat.Conservation.Heis.abelianization_one
#guard_depends_on Fermat.Conservation.Heis.abelianizationHom,
  Fermat.Conservation.Heis.abelianization_mul
#guard_depends_on Fermat.Conservation.Heis.abelianization_kernel_eq_center,
  Fermat.Conservation.Heis.abelianization_eq_one_iff
#guard_depends_on Fermat.Conservation.Heis.commutator_eq_area_center,
  Fermat.Conservation.Heis.commutator_formula

/-! AreaTransfer is a real refinement: composition and chains project to the
old transaction algebra, while its Ledger shadow and payload jewels retain
their named D=1/D=2 anchors. -/

#guard_depends_on Fermat.Conservation.AreaTransfer.comp,
  Fermat.Conservation.Transfer.comp
#guard_depends_on Fermat.Conservation.AreaTransfer.comp,
  Fermat.Conservation.Heis.mul_assoc
#guard_depends_on Fermat.Conservation.AreaTransfer.chain_projects,
  Fermat.Conservation.Transfer.Chain.cons
#guard_depends_on
  Fermat.Conservation.AreaTransfer.ledgerPayload_abelianization,
  Fermat.Conservation.Heis.abelianization_mk
#guard_depends_on Fermat.Conservation.AreaTransfer.ledgerAbelian_sum_eq_total,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on Fermat.Conservation.AreaTransfer.ofTransfer,
  Fermat.Conservation.Transfer.available_eq
#guard_depends_on Fermat.Conservation.AreaTransfer.ofTransfer,
  Fermat.Conservation.Transfer.converted_decomposition
#guard_depends_on
  Fermat.Conservation.AreaTransfer.ofTransfer_hasLedgerShadow,
  Fermat.Conservation.AreaTransfer.ledgerPayload_abelianization
#guard_depends_on
  Fermat.Conservation.AreaTransfer.word_abelianization_of_hasLedgerShadow,
  Fermat.Conservation.Transfer.available_eq
#guard_depends_on
  Fermat.Conservation.AreaTransfer.word_abelianization_of_hasLedgerShadow,
  Fermat.Conservation.Transfer.converted_decomposition
#guard_depends_on Fermat.Conservation.AreaTransfer.no_erasure,
  Fermat.Conservation.Heis.no_private_drain
#guard_depends_on Fermat.Conservation.AreaTransfer.nonzero_center_not_erased,
  Fermat.Conservation.AreaTransfer.no_erasure
#guard_depends_on
  Fermat.Conservation.AreaTransfer.central_coordinate_eq_zero_iff_exact_cancellation,
  Fermat.Conservation.Heis.central_coordinate_eq_zero_iff_exact_cancellation

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

/-! The tunnel now carries the payload dictionary and both exact lifted-step
directions without bypassing its existing balanced-step maps. -/

#guard_depends_on
  Fermat.Conservation.IsoConserveBridge.abelianization_columnsPayload,
  Fermat.Conservation.AreaTransfer.ledgerPayload_abelianization
#guard_depends_on
  Fermat.Conservation.IsoConserveBridge.columnsPayload_dictionary,
  Fermat.Conservation.IsoConserveBridge.abelianization_columnsPayload
#guard_depends_on
  Fermat.Conservation.IsoConserveBridge.columnsOfPayload_dictionary,
  Fermat.Conservation.IsoConserveBridge.columnsAbelian_columnsOfPayload
#guard_depends_on
  Fermat.Conservation.IsoConserveBridge.toPayloadBalancedStep,
  Fermat.Conservation.IsoConserveBridge.toBalancedStep
#guard_depends_on
  Fermat.Conservation.IsoConserveBridge.ofPayloadBalancedStep,
  Fermat.Conservation.IsoConserveBridge.ofBalancedStep
#guard_depends_on
  Fermat.Conservation.IsoConserveBridge.areaTransfer_L1_conservation,
  Fermat.Conservation.IsoConserveBridge.transfer_L1_conservation
#guard_depends_on
  Fermat.Conservation.IsoConserveBridge.toPayloadBalancedStep_ofPayloadBalancedStep,
  Fermat.Conservation.IsoConserveBridge.toPayloadBalancedStep
#guard_depends_on
  Fermat.Conservation.IsoConserveBridge.toPayloadBalancedStep_ofPayloadBalancedStep,
  Fermat.Conservation.IsoConserveBridge.ofPayloadBalancedStep
#guard_depends_on
  Fermat.Conservation.IsoConserveBridge.ofPayloadBalancedStep_toPayloadBalancedStep,
  Fermat.Conservation.IsoConserveBridge.toPayloadBalancedStep
#guard_depends_on
  Fermat.Conservation.IsoConserveBridge.ofPayloadBalancedStep_toPayloadBalancedStep,
  Fermat.Conservation.IsoConserveBridge.ofPayloadBalancedStep

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

/-! The public D=2 anchors remain within the repository's standard axiom
baseline. -/

/--
info: 'Fermat.Conservation.Heis.groupLaws' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Heis.groupLaws

/--
info: 'Fermat.Conservation.Heis.central_iff' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Heis.central_iff

/--
info: 'Fermat.Conservation.Heis.abelianization_kernel_eq_center' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Heis.abelianization_kernel_eq_center

/--
info: 'Fermat.Conservation.Heis.commutator_eq_area_center' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Heis.commutator_eq_area_center

/--
info: 'Fermat.Conservation.Heis.no_private_drain' does not depend on any axioms
-/
#guard_msgs in
#print axioms Fermat.Conservation.Heis.no_private_drain

/--
info: 'Fermat.Conservation.Heis.central_coordinate_eq_zero_iff_exact_cancellation' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Heis.central_coordinate_eq_zero_iff_exact_cancellation

/--
info: 'Fermat.Conservation.AreaTransfer.comp' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.AreaTransfer.comp

/--
info: 'Fermat.Conservation.AreaTransfer.chain_projects' does not depend on any axioms
-/
#guard_msgs in
#print axioms Fermat.Conservation.AreaTransfer.chain_projects

/--
info: 'Fermat.Conservation.AreaTransfer.ledgerPayload_abelianization' does not depend on any axioms
-/
#guard_msgs in
#print axioms Fermat.Conservation.AreaTransfer.ledgerPayload_abelianization

/--
info: 'Fermat.Conservation.AreaTransfer.ledgerAbelian_sum_eq_total' does not depend on any axioms
-/
#guard_msgs in
#print axioms Fermat.Conservation.AreaTransfer.ledgerAbelian_sum_eq_total

/--
info: 'Fermat.Conservation.AreaTransfer.ofTransfer_hasLedgerShadow' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Conservation.AreaTransfer.ofTransfer_hasLedgerShadow

/--
info: 'Fermat.Conservation.AreaTransfer.word_abelianization_of_hasLedgerShadow' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Conservation.AreaTransfer.word_abelianization_of_hasLedgerShadow

/--
info: 'Fermat.Conservation.AreaTransfer.no_erasure' does not depend on any axioms
-/
#guard_msgs in
#print axioms Fermat.Conservation.AreaTransfer.no_erasure

/--
info: 'Fermat.Conservation.AreaTransfer.central_coordinate_eq_zero_iff_exact_cancellation' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Conservation.AreaTransfer.central_coordinate_eq_zero_iff_exact_cancellation

/--
info: 'Fermat.Conservation.IsoConserveBridge.abelianization_columnsPayload' does not depend on any axioms
-/
#guard_msgs in
#print axioms Fermat.Conservation.IsoConserveBridge.abelianization_columnsPayload

/--
info: 'Fermat.Conservation.IsoConserveBridge.columnsOfPayload_dictionary' does not depend on any axioms
-/
#guard_msgs in
#print axioms Fermat.Conservation.IsoConserveBridge.columnsOfPayload_dictionary

/--
info: 'Fermat.Conservation.IsoConserveBridge.areaTransfer_L1_conservation' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.IsoConserveBridge.areaTransfer_L1_conservation

/--
info: 'Fermat.Conservation.IsoConserveBridge.toPayloadBalancedStep_ofPayloadBalancedStep' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.IsoConserveBridge.toPayloadBalancedStep_ofPayloadBalancedStep

/--
info: 'Fermat.Conservation.IsoConserveBridge.ofPayloadBalancedStep_toPayloadBalancedStep' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.IsoConserveBridge.ofPayloadBalancedStep_toPayloadBalancedStep
