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
import Fermat.Conservation.Interaction
import Fermat.Conservation.ClassCarrier
import Fermat.Conservation.TransverseAnnihilator
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

/-! The interaction layer exposes the complete two-account flow bound, the
class carrier retains every receipt above its deliberately lossy projection,
and the transverse layer retains both the Bezout kill law and every surviving
gcd channel. -/

#check Interaction.TwoAccount
#check Interaction.TwoAccount.sum_step
#check Interaction.TwoAccount.difference_step
#check Interaction.TwoAccount.energy_step
#check Interaction.TwoAccount.sum_orbit
#check Interaction.TwoAccount.difference_orbit
#check Interaction.TwoAccount.energy_orbit
#check Interaction.TwoAccount.positive_difference_abs_le_sum
#check Interaction.TwoAccount.positive_energy_le_sum_sq
#check Interaction.TwoAccount.damped_energy_strict
#check Interaction.TwoAccount.critical_livelock
#check Interaction.TwoAccount.supercritical_eventually_exceeds_bound
#check Interaction.TwoAccount.supercritical_impossible_forever_in_bounded_orbit
#check Interaction.TwoAccount.supercritical_eventually_leaves_positive_ledger
#check Interaction.TwoAccount.flow_bound_trichotomy
#check Interaction.TwoAccount.exit_trilemma
#check Interaction.TwoAccount.critical_swap_is_closed_area_word
#check Interaction.TwoAccount.gain_three_integer_energy_strict
#check Interaction.TwoAccount.quotient_erases_energy_mod_three
#check Interaction.TwoAccount.quotient_erases_energy_warning
#check ClassCarrier.AnnihilatorReceipt
#check ClassCarrier.PrincipalizationReceipt
#check ClassCarrier.State
#check ClassCarrier.BoundedRepresentativeInterface
#check ClassCarrier.State.source_eq_principal_mul_reduced
#check ClassCarrier.State.lossyProjection_eq_source
#check ClassCarrier.State.lossyProjection_forgets_beta_and_annihilators
#check ClassCarrier.BoundedRepresentativeInterface.reduction_emits_all_annihilator_receipts
#check ClassCarrier.BoundedRepresentativeInterface.reduction_no_silent_discard
#check ClassCarrier.exists_principalizationReceipt_of_same_quotient
#check ClassCarrier.exists_principalizationReceipt_of_same_class
#check ClassCarrier.idealClassProjection_eq_source_class
#check ClassCarrier.idealClassProjection_forgets_beta_and_annihilators
#check ClassCarrier.classGroup_is_lossy_projection
#check ClassCarrier.minkowskiIdealRepresentative_class
#check ClassCarrier.minkowskiIdealRepresentative_norm_le
#check ClassCarrier.numberFieldReduced_mem
#check ClassCarrier.numberFieldReduced_same_class
#check ClassCarrier.numberField_source_eq_principal_mul_reduced
#check ClassCarrier.numberFieldBoundedRepresentative
#check TransverseAnnihilator.TwoAnnihilatorMode
#check TransverseAnnihilator.LivelockChannel
#check TransverseAnnihilator.StickelbergerTransverse
#check TransverseAnnihilator.LampTransverse
#check TransverseAnnihilator.SophieGermainGCDLaw
#check TransverseAnnihilator.SixfoldWendtLaw
#check TransverseAnnihilator.CornerService.BezoutCertificate
#check TransverseAnnihilator.CornerService.BreaksCycle
#check TransverseAnnihilator.CornerService.eq_zero_of_annihilates_of_bezout
#check TransverseAnnihilator.CornerService.relationSubmodule
#check TransverseAnnihilator.CornerService.LivelockCarrier
#check TransverseAnnihilator.CornerService.one_mem_relationSubmodule_iff
#check TransverseAnnihilator.CornerService.relationSubmodule_eq_top_iff
#check TransverseAnnihilator.CornerService.livelockCarrier_subsingleton_iff
#check TransverseAnnihilator.CornerService.livelockCarrier_nontrivial_iff
#check TransverseAnnihilator.CornerService.CornerLivelockChannel
#check TransverseAnnihilator.CornerService.nonempty_cornerLivelockChannel_iff
#check TransverseAnnihilator.breaksCycle_iff_polynomialGCD_eq_one
#check TransverseAnnihilator.polynomial_livelockCarrier_subsingleton_iff
#check TransverseAnnihilator.nonempty_polynomial_cornerLivelockChannel_iff
#check TransverseAnnihilator.eq_zero_of_cycle_and_transverse_gcd_eq_one
#check TransverseAnnihilator.TwoAnnihilatorMode.livelockChannel
#check TransverseAnnihilator.StickelbergerTransverse.mode_eq_zero_of_gcd_eq_one
#check TransverseAnnihilator.SophieGermainGCDLaw.mode_eq_zero_of_certificate
#check TransverseAnnihilator.SophieGermainGCDLaw.channel_of_conditionA_failure
#check TransverseAnnihilator.SixfoldWendtLaw.livelockChannel
#check TransverseAnnihilator.SixfoldWendtLaw.conditionA_fails_of_three_dvd

/-! ## Interaction, non-lossy-carrier, and transverse dependency audit -/

/-! The algebraic flow laws use the actual interaction definitions; orbit,
critical, ordered, and operational claims retain their advertised upstream
laws in proof values. -/

#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.sum_step,
  Fermat.Conservation.Interaction.TwoAccount.step
#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.difference_step,
  Fermat.Conservation.Interaction.TwoAccount.flow
#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.energy_step,
  Fermat.Conservation.Interaction.TwoAccount.difference_step
#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.sum_orbit,
  Fermat.Conservation.Interaction.TwoAccount.sum_step
#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.difference_orbit,
  Fermat.Conservation.Interaction.TwoAccount.difference_step
#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.energy_orbit,
  Fermat.Conservation.Interaction.TwoAccount.difference_orbit
#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.step_two_eq_swap,
  Fermat.Conservation.Interaction.TwoAccount.step
#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.critical_period_two,
  Fermat.Conservation.Interaction.TwoAccount.step_two_eq_swap
#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.critical_energy_invariant,
  Fermat.Conservation.Interaction.TwoAccount.energy_step
#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.critical_livelock,
  Fermat.Conservation.Interaction.TwoAccount.critical_period_two
#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.critical_livelock,
  Fermat.Conservation.Interaction.TwoAccount.critical_energy_invariant
#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.positive_difference_abs_le_sum,
  Fermat.Conservation.Interaction.TwoAccount.PositiveLedger
#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.positive_energy_le_sum_sq,
  Fermat.Conservation.Interaction.TwoAccount.energy
#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.damped_energy_strict,
  Fermat.Conservation.Interaction.TwoAccount.energy_step
#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.damped_energy_strict,
  Fermat.Conservation.Interaction.TwoAccount.damped_multiplier_abs_lt_one
#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.supercritical_eventually_exceeds_bound,
  Fermat.Conservation.Interaction.TwoAccount.difference_orbit
#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.supercritical_impossible_forever_in_bounded_orbit,
  Fermat.Conservation.Interaction.TwoAccount.supercritical_eventually_exceeds_bound
#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.supercritical_eventually_leaves_positive_ledger,
  Fermat.Conservation.Interaction.TwoAccount.supercritical_eventually_exceeds_bound
#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.supercritical_eventually_leaves_positive_ledger,
  Fermat.Conservation.Interaction.TwoAccount.positive_difference_abs_le_sum
#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.flow_bound_trichotomy,
  Fermat.Conservation.Interaction.TwoAccount.damped_energy_strict
#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.flow_bound_trichotomy,
  Fermat.Conservation.Interaction.TwoAccount.critical_livelock
#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.flow_bound_trichotomy,
  Fermat.Conservation.Interaction.TwoAccount.supercritical_eventually_leaves_positive_ledger
#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.exit_trilemma,
  Fermat.Conservation.Interaction.TwoAccount.supercritical_eventually_leaves_positive_ledger

/-! The `AreaTransfer` wiring is a value-level payload statement, not merely
an equality with a matching type. -/

#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.swapTransfer,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.criticalSwapAreaTransfer,
  Fermat.Conservation.AreaTransfer.ofTransfer
#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.criticalSwapAreaTransfer_word,
  Fermat.Conservation.Interaction.TwoAccount.criticalSwapAreaTransfer
#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.criticalSwapAreaTransfer_payload_invariant,
  Fermat.Conservation.AreaTransfer.payload_decomposition
#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.criticalSwapAreaTransfer_payload_invariant,
  Fermat.Conservation.Interaction.TwoAccount.criticalSwapAreaTransfer_word
#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.critical_swap_is_closed_area_word,
  Fermat.Conservation.Interaction.TwoAccount.step_two_eq_swap
#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.critical_swap_is_closed_area_word,
  Fermat.Conservation.Interaction.TwoAccount.criticalSwapAreaTransfer_payload_invariant
#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.quotient_erases_energy_warning,
  Fermat.Conservation.Interaction.TwoAccount.gain_three_integer_energy_strict
#guard_depends_on
  Fermat.Conservation.Interaction.TwoAccount.quotient_erases_energy_warning,
  Fermat.Conservation.Interaction.TwoAccount.quotient_erases_energy_mod_three

/-! Reduction preserves both kinds of receipt; the quotient and class-group
claims depend on the retained principalization equation, and the concrete
number-field implementation depends on Mathlib's Minkowski representative. -/

#guard_depends_on
  Fermat.Conservation.ClassCarrier.State.source_eq_principal_mul_reduced,
  Fermat.Conservation.ClassCarrier.PrincipalizationReceipt.source_eq
#guard_depends_on
  Fermat.Conservation.ClassCarrier.State.lossyProjection_eq_source,
  Fermat.Conservation.ClassCarrier.State.source_eq_principal_mul_reduced
#guard_depends_on
  Fermat.Conservation.ClassCarrier.State.lossyProjection_ignores_receipts,
  Fermat.Conservation.ClassCarrier.State.lossyProjection
#guard_depends_on
  Fermat.Conservation.ClassCarrier.State.lossyProjection_forgets_beta_and_annihilators,
  Fermat.Conservation.ClassCarrier.State.lossyProjection_ignores_receipts
#guard_depends_on
  Fermat.Conservation.ClassCarrier.BoundedRepresentativeInterface.reduction_emits_all_annihilator_receipts,
  Fermat.Conservation.ClassCarrier.BoundedRepresentativeInterface.reduce
#guard_depends_on
  Fermat.Conservation.ClassCarrier.BoundedRepresentativeInterface.reduction_no_silent_discard,
  Fermat.Conservation.ClassCarrier.State.source_eq_principal_mul_reduced
#guard_depends_on
  Fermat.Conservation.ClassCarrier.exists_principalizationReceipt_of_same_quotient,
  QuotientGroup.mk'_eq_mk'
#guard_depends_on
  Fermat.Conservation.ClassCarrier.exists_principalizationReceipt_of_same_class,
  Fermat.Conservation.ClassCarrier.exists_principalizationReceipt_of_same_quotient
#guard_depends_on
  Fermat.Conservation.ClassCarrier.idealClassProjection_eq_source_class,
  Fermat.Conservation.ClassCarrier.State.source_eq_principal_mul_reduced
#guard_depends_on
  Fermat.Conservation.ClassCarrier.idealClassProjection_forgets_beta_and_annihilators,
  Fermat.Conservation.ClassCarrier.idealClassProjection
#guard_depends_on
  Fermat.Conservation.ClassCarrier.classGroup_is_lossy_projection,
  Fermat.Conservation.ClassCarrier.idealClassProjection
#guard_depends_on
  Fermat.Conservation.ClassCarrier.classGroup_is_lossy_projection,
  Fermat.Conservation.ClassCarrier.State.lossyProjection
#guard_depends_on
  Fermat.Conservation.ClassCarrier.minkowskiIdealRepresentative_class,
  NumberField.exists_ideal_in_class_of_norm_le
#guard_depends_on
  Fermat.Conservation.ClassCarrier.minkowskiIdealRepresentative_norm_le,
  NumberField.exists_ideal_in_class_of_norm_le
#guard_depends_on
  Fermat.Conservation.ClassCarrier.minkowskiIdealRepresentative_norm_le,
  Fermat.Conservation.ClassCarrier.minkowskiClassBound
#guard_depends_on
  Fermat.Conservation.ClassCarrier.numberFieldReduced_mem,
  Fermat.Conservation.ClassCarrier.minkowskiIdealRepresentative_norm_le
#guard_depends_on
  Fermat.Conservation.ClassCarrier.numberFieldReduced_same_class,
  Fermat.Conservation.ClassCarrier.minkowskiIdealRepresentative_class
#guard_depends_on
  Fermat.Conservation.ClassCarrier.numberField_source_eq_principal_mul_reduced,
  Fermat.Conservation.ClassCarrier.numberFieldPrincipalizationReceipt

/-! The core Bezout theorem uses the derived gcd annihilator.  A failed lamp
condition retains the exact nonunit gcd, while the sixfold law routes through
the explicit Wendt shared-factor witness. -/

#guard_depends_on
  Fermat.Conservation.TransverseAnnihilator.annihilates_polynomialGCD,
  Fermat.Conservation.TransverseAnnihilator.annihilates_euclideanGCD
#guard_depends_on
  Fermat.Conservation.TransverseAnnihilator.eq_zero_of_cycle_and_transverse_gcd_eq_one,
  Fermat.Conservation.TransverseAnnihilator.breaksCycle_iff_polynomialGCD_eq_one
#guard_depends_on
  Fermat.Conservation.TransverseAnnihilator.eq_zero_of_cycle_and_transverse_gcd_eq_one,
  Fermat.Conservation.TransverseAnnihilator.CornerService.eq_zero_of_annihilates_of_bezout
#guard_depends_on
  Fermat.Conservation.TransverseAnnihilator.TwoAnnihilatorMode.mode_eq_zero,
  Fermat.Conservation.TransverseAnnihilator.eq_zero_of_cycle_and_transverse_gcd_eq_one
#guard_depends_on
  Fermat.Conservation.TransverseAnnihilator.TwoAnnihilatorMode.livelockChannel,
  Fermat.Conservation.TransverseAnnihilator.polynomialGCD_not_isUnit_of_ne_one
#guard_depends_on
  Fermat.Conservation.TransverseAnnihilator.TwoAnnihilatorMode.livelockChannel,
  Fermat.Conservation.TransverseAnnihilator.TwoAnnihilatorMode.gcd_annihilates
#guard_depends_on
  Fermat.Conservation.TransverseAnnihilator.StickelbergerTransverse.mode_eq_zero_of_gcd_eq_one,
  Fermat.Conservation.TransverseAnnihilator.TwoAnnihilatorMode.mode_eq_zero
#guard_depends_on
  Fermat.Conservation.TransverseAnnihilator.SophieGermainGCDLaw.mode_eq_zero_of_certificate,
  Fermat.Conservation.TransverseAnnihilator.SophieGermainGCDLaw.gcd_eq_one_of_certificate
#guard_depends_on
  Fermat.Conservation.TransverseAnnihilator.SophieGermainGCDLaw.channel_of_conditionA_failure,
  Fermat.Conservation.TransverseAnnihilator.SophieGermainGCDLaw.conditionA_iff_gcd_eq_one
#guard_depends_on
  Fermat.Conservation.TransverseAnnihilator.SophieGermainGCDLaw.channel_of_conditionA_failure,
  Fermat.Conservation.TransverseAnnihilator.TwoAnnihilatorMode.livelockChannel
#guard_depends_on
  Fermat.Conservation.TransverseAnnihilator.polynomialGCD_ne_one_of_sharedFactor,
  Fermat.Conservation.TransverseAnnihilator.dvd_polynomialGCD
#guard_depends_on
  Fermat.Conservation.TransverseAnnihilator.SixfoldWendtLaw.sharedFactor,
  Fermat.Conservation.TransverseAnnihilator.wendtPolynomial_not_isUnit
#guard_depends_on
  Fermat.Conservation.TransverseAnnihilator.SixfoldWendtLaw.sharedFactor,
  Fermat.Conservation.TransverseAnnihilator.SixfoldWendtLaw.wendt_shared_of_three_dvd
#guard_depends_on
  Fermat.Conservation.TransverseAnnihilator.SixfoldWendtLaw.livelockChannel,
  Fermat.Conservation.TransverseAnnihilator.polynomialGCD_ne_one_of_sharedFactor
#guard_depends_on
  Fermat.Conservation.TransverseAnnihilator.SixfoldWendtLaw.conditionA_fails_of_three_dvd,
  Fermat.Conservation.TransverseAnnihilator.SixfoldWendtLaw.sharedFactor

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

/-! Every public interaction theorem stays within the standard axiom trio. -/

/--
info: 'Fermat.Conservation.Interaction.TwoAccount.swap_left' does not depend on any axioms
-/
#guard_msgs in
#print axioms Fermat.Conservation.Interaction.TwoAccount.swap_left

/--
info: 'Fermat.Conservation.Interaction.TwoAccount.swap_right' does not depend on any axioms
-/
#guard_msgs in
#print axioms Fermat.Conservation.Interaction.TwoAccount.swap_right

/--
info: 'Fermat.Conservation.Interaction.TwoAccount.swap_swap' does not depend on any axioms
-/
#guard_msgs in
#print axioms Fermat.Conservation.Interaction.TwoAccount.swap_swap

/--
info: 'Fermat.Conservation.Interaction.TwoAccount.sum_step' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Interaction.TwoAccount.sum_step

/--
info: 'Fermat.Conservation.Interaction.TwoAccount.difference_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Interaction.TwoAccount.difference_step

/--
info: 'Fermat.Conservation.Interaction.TwoAccount.energy_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Interaction.TwoAccount.energy_step

/--
info: 'Fermat.Conservation.Interaction.TwoAccount.orbit_zero' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Interaction.TwoAccount.orbit_zero

/--
info: 'Fermat.Conservation.Interaction.TwoAccount.orbit_succ' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Interaction.TwoAccount.orbit_succ

/--
info: 'Fermat.Conservation.Interaction.TwoAccount.sum_orbit' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Interaction.TwoAccount.sum_orbit

/--
info: 'Fermat.Conservation.Interaction.TwoAccount.difference_orbit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Interaction.TwoAccount.difference_orbit

/--
info: 'Fermat.Conservation.Interaction.TwoAccount.energy_orbit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Interaction.TwoAccount.energy_orbit

/--
info: 'Fermat.Conservation.Interaction.TwoAccount.step_two_eq_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Interaction.TwoAccount.step_two_eq_swap

/--
info: 'Fermat.Conservation.Interaction.TwoAccount.critical_period_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Interaction.TwoAccount.critical_period_two

/--
info: 'Fermat.Conservation.Interaction.TwoAccount.critical_energy_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Interaction.TwoAccount.critical_energy_invariant

/--
info: 'Fermat.Conservation.Interaction.TwoAccount.critical_livelock' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Interaction.TwoAccount.critical_livelock

/--
info: 'Fermat.Conservation.Interaction.TwoAccount.positive_difference_abs_le_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Interaction.TwoAccount.positive_difference_abs_le_sum

/--
info: 'Fermat.Conservation.Interaction.TwoAccount.positive_energy_le_sum_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Interaction.TwoAccount.positive_energy_le_sum_sq

/--
info: 'Fermat.Conservation.Interaction.TwoAccount.damped_multiplier_abs_lt_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Interaction.TwoAccount.damped_multiplier_abs_lt_one

/--
info: 'Fermat.Conservation.Interaction.TwoAccount.damped_energy_strict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Interaction.TwoAccount.damped_energy_strict

/--
info: 'Fermat.Conservation.Interaction.TwoAccount.supercritical_eventually_exceeds_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Interaction.TwoAccount.supercritical_eventually_exceeds_bound

/--
info: 'Fermat.Conservation.Interaction.TwoAccount.supercritical_impossible_forever_in_bounded_orbit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Interaction.TwoAccount.supercritical_impossible_forever_in_bounded_orbit

/--
info: 'Fermat.Conservation.Interaction.TwoAccount.supercritical_eventually_leaves_positive_ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Interaction.TwoAccount.supercritical_eventually_leaves_positive_ledger

/--
info: 'Fermat.Conservation.Interaction.TwoAccount.flow_bound_trichotomy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Interaction.TwoAccount.flow_bound_trichotomy

/--
info: 'Fermat.Conservation.Interaction.TwoAccount.exit_trilemma' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Interaction.TwoAccount.exit_trilemma

/--
info: 'Fermat.Conservation.Interaction.TwoAccount.criticalSwapAreaTransfer_word' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Interaction.TwoAccount.criticalSwapAreaTransfer_word

/--
info: 'Fermat.Conservation.Interaction.TwoAccount.criticalSwapAreaTransfer_payload_invariant' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Interaction.TwoAccount.criticalSwapAreaTransfer_payload_invariant

/--
info: 'Fermat.Conservation.Interaction.TwoAccount.critical_swap_is_closed_area_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Interaction.TwoAccount.critical_swap_is_closed_area_word

/--
info: 'Fermat.Conservation.Interaction.TwoAccount.gain_three_integer_energy_strict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Interaction.TwoAccount.gain_three_integer_energy_strict

/--
info: 'Fermat.Conservation.Interaction.TwoAccount.quotient_erases_energy_mod_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Interaction.TwoAccount.quotient_erases_energy_mod_three

/--
info: 'Fermat.Conservation.Interaction.TwoAccount.quotient_erases_energy_warning' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Interaction.TwoAccount.quotient_erases_energy_warning

/-! Every public class-carrier theorem stays within the standard axiom trio. -/

/--
info: 'Fermat.Conservation.ClassCarrier.State.source_eq_principal_mul_reduced' does not depend on any axioms
-/
#guard_msgs in
#print axioms Fermat.Conservation.ClassCarrier.State.source_eq_principal_mul_reduced

/--
info: 'Fermat.Conservation.ClassCarrier.State.lossyProjection_eq_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ClassCarrier.State.lossyProjection_eq_source

/--
info: 'Fermat.Conservation.ClassCarrier.State.lossyProjection_ignores_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ClassCarrier.State.lossyProjection_ignores_receipts

/--
info: 'Fermat.Conservation.ClassCarrier.State.lossyProjection_forgets_beta_and_annihilators' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ClassCarrier.State.lossyProjection_forgets_beta_and_annihilators

/--
info: 'Fermat.Conservation.ClassCarrier.BoundedRepresentativeInterface.reduction_emits_all_annihilator_receipts' does not depend on any axioms
-/
#guard_msgs in
#print axioms Fermat.Conservation.ClassCarrier.BoundedRepresentativeInterface.reduction_emits_all_annihilator_receipts

/--
info: 'Fermat.Conservation.ClassCarrier.BoundedRepresentativeInterface.reduction_no_silent_discard' does not depend on any axioms
-/
#guard_msgs in
#print axioms Fermat.Conservation.ClassCarrier.BoundedRepresentativeInterface.reduction_no_silent_discard

/--
info: 'Fermat.Conservation.ClassCarrier.exists_principalizationReceipt_of_same_quotient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ClassCarrier.exists_principalizationReceipt_of_same_quotient

/--
info: 'Fermat.Conservation.ClassCarrier.exists_principalizationReceipt_of_same_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ClassCarrier.exists_principalizationReceipt_of_same_class

/--
info: 'Fermat.Conservation.ClassCarrier.idealClassProjection_eq_source_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ClassCarrier.idealClassProjection_eq_source_class

/--
info: 'Fermat.Conservation.ClassCarrier.idealClassProjection_forgets_beta_and_annihilators' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ClassCarrier.idealClassProjection_forgets_beta_and_annihilators

/--
info: 'Fermat.Conservation.ClassCarrier.classGroup_is_lossy_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ClassCarrier.classGroup_is_lossy_projection

/--
info: 'Fermat.Conservation.ClassCarrier.minkowskiIdealRepresentative_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ClassCarrier.minkowskiIdealRepresentative_class

/--
info: 'Fermat.Conservation.ClassCarrier.minkowskiIdealRepresentative_norm_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ClassCarrier.minkowskiIdealRepresentative_norm_le

/--
info: 'Fermat.Conservation.ClassCarrier.numberFieldReduced_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ClassCarrier.numberFieldReduced_mem

/--
info: 'Fermat.Conservation.ClassCarrier.numberFieldReduced_same_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ClassCarrier.numberFieldReduced_same_class

/--
info: 'Fermat.Conservation.ClassCarrier.numberField_source_eq_principal_mul_reduced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ClassCarrier.numberField_source_eq_principal_mul_reduced

/-! Every public transverse-annihilator theorem stays within the standard
axiom trio. -/

/--
info: 'Fermat.Conservation.TransverseAnnihilator.CornerService.eq_zero_of_annihilates_of_bezout' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Conservation.TransverseAnnihilator.CornerService.eq_zero_of_annihilates_of_bezout

/--
info: 'Fermat.Conservation.TransverseAnnihilator.CornerService.one_mem_relationSubmodule_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.TransverseAnnihilator.CornerService.one_mem_relationSubmodule_iff

/--
info: 'Fermat.Conservation.TransverseAnnihilator.CornerService.relationSubmodule_eq_top_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.TransverseAnnihilator.CornerService.relationSubmodule_eq_top_iff

/--
info: 'Fermat.Conservation.TransverseAnnihilator.CornerService.livelockCarrier_subsingleton_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.TransverseAnnihilator.CornerService.livelockCarrier_subsingleton_iff

/--
info: 'Fermat.Conservation.TransverseAnnihilator.CornerService.livelockCarrier_nontrivial_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.TransverseAnnihilator.CornerService.livelockCarrier_nontrivial_iff

/--
info: 'Fermat.Conservation.TransverseAnnihilator.CornerService.nonempty_cornerLivelockChannel_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.TransverseAnnihilator.CornerService.nonempty_cornerLivelockChannel_iff

/--
info: 'Fermat.Conservation.TransverseAnnihilator.breaksCycle_iff_polynomialGCD_eq_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.TransverseAnnihilator.breaksCycle_iff_polynomialGCD_eq_one

/--
info: 'Fermat.Conservation.TransverseAnnihilator.polynomial_livelockCarrier_subsingleton_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.TransverseAnnihilator.polynomial_livelockCarrier_subsingleton_iff

/--
info: 'Fermat.Conservation.TransverseAnnihilator.nonempty_polynomial_cornerLivelockChannel_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.TransverseAnnihilator.nonempty_polynomial_cornerLivelockChannel_iff

/--
info: 'Fermat.Conservation.TransverseAnnihilator.normalize_polynomialGCD' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.TransverseAnnihilator.normalize_polynomialGCD

/--
info: 'Fermat.Conservation.TransverseAnnihilator.polynomialGCD_dvd_left' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.TransverseAnnihilator.polynomialGCD_dvd_left

/--
info: 'Fermat.Conservation.TransverseAnnihilator.polynomialGCD_dvd_right' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.TransverseAnnihilator.polynomialGCD_dvd_right

/--
info: 'Fermat.Conservation.TransverseAnnihilator.dvd_polynomialGCD' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.TransverseAnnihilator.dvd_polynomialGCD

/--
info: 'Fermat.Conservation.TransverseAnnihilator.annihilates_euclideanGCD' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.TransverseAnnihilator.annihilates_euclideanGCD

/--
info: 'Fermat.Conservation.TransverseAnnihilator.annihilates_polynomialGCD' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.TransverseAnnihilator.annihilates_polynomialGCD

/--
info: 'Fermat.Conservation.TransverseAnnihilator.eq_zero_of_cycle_and_transverse_gcd_eq_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.TransverseAnnihilator.eq_zero_of_cycle_and_transverse_gcd_eq_one

/--
info: 'Fermat.Conservation.TransverseAnnihilator.polynomialGCD_not_isUnit_of_ne_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.TransverseAnnihilator.polynomialGCD_not_isUnit_of_ne_one

/--
info: 'Fermat.Conservation.TransverseAnnihilator.TwoAnnihilatorMode.gcd_annihilates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.TransverseAnnihilator.TwoAnnihilatorMode.gcd_annihilates

/--
info: 'Fermat.Conservation.TransverseAnnihilator.TwoAnnihilatorMode.mode_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.TransverseAnnihilator.TwoAnnihilatorMode.mode_eq_zero

/--
info: 'Fermat.Conservation.TransverseAnnihilator.StickelbergerTransverse.mode_eq_zero_of_gcd_eq_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.TransverseAnnihilator.StickelbergerTransverse.mode_eq_zero_of_gcd_eq_one

/--
info: 'Fermat.Conservation.TransverseAnnihilator.SophieGermainGCDLaw.gcd_eq_one_of_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.TransverseAnnihilator.SophieGermainGCDLaw.gcd_eq_one_of_certificate

/--
info: 'Fermat.Conservation.TransverseAnnihilator.SophieGermainGCDLaw.mode_eq_zero_of_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.TransverseAnnihilator.SophieGermainGCDLaw.mode_eq_zero_of_certificate

/--
info: 'Fermat.Conservation.TransverseAnnihilator.wendtPolynomial_not_isUnit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.TransverseAnnihilator.wendtPolynomial_not_isUnit

/--
info: 'Fermat.Conservation.TransverseAnnihilator.polynomialGCD_ne_one_of_sharedFactor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.TransverseAnnihilator.polynomialGCD_ne_one_of_sharedFactor

/--
info: 'Fermat.Conservation.TransverseAnnihilator.SixfoldWendtLaw.conditionA_fails_of_three_dvd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.TransverseAnnihilator.SixfoldWendtLaw.conditionA_fails_of_three_dvd
