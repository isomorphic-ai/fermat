/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Executable audit for the route-neutral credit ladder

This non-imported leaf audits the public C1--C3 and W1--W3 surfaces and
checks that no forbidden endpoint, generic-irregular, or ladder declaration
or module enters the credit cone.
-/
import Fermat.Conservation.GuardDependsOn
import Fermat.Conservation.Ledger
import Fermat.Conservation.Transfer
import Fermat.Conservation.Credit.Vacuum
import Fermat.Conservation.Credit.Capacity
import Fermat.Conservation.Credit.Repayment
import Fermat.Conservation.Credit.Flow
import Fermat.Conservation.Credit.LogRateFlow
import Fermat.Conservation.Credit.HighFlowClosure
import Fermat.Conservation.Credit.CompletedFlow
import Fermat.Conservation.Credit.Bernoulli
import Fermat.Conservation.Credit.Gauge
import Fermat.Conservation.Credit.HighFlow
import Fermat.Conservation.Credit.Forcing
import Fermat.Conservation.Credit.DepthFlow
import Fermat.Conservation.Credit.CyclotomicFlow
import Fermat.Conservation.Credit.MomentFlow
import Fermat.Conservation.Credit.NonlinearFlow
import Fermat.Conservation.Credit.RationalReduction
import Fermat.Conservation.Credit.RealGauge
import Fermat.Conservation.Credit.RealHighFlow
import Fermat.Conservation.Credit.RelationDepthFlow
import Fermat.Conservation.Credit.RelationEvaluationFlow
import Fermat.Conservation.Credit.RealForcing
import Fermat.Conservation.Credit.DepthCertificate
import Fermat.Conservation.Credit.GaugeQuotient
import Fermat.Conservation.Credit.Fold
import Fermat.Conservation.CyclotomicDrain
import Fermat.Conservation.KummerDrain

/-! ## Ledger-literal gate -/

/-! The three named identities and the deliberately open layer-transport
interface must remain present in the generic conservation environment. -/

#check Fermat.Conservation.Ledger.conservation_identity
#check Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.depth_conservation
#check Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.depthTransfer
#check Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.depthTransfer_credit_decomposition
#check Fermat.Conservation.Credit.Repayment.repay_layer_conservation
#check Fermat.Conservation.Credit.Repayment.C.accountCredit
#check Fermat.Conservation.Credit.Repayment.C.accountLedger
#check Fermat.Conservation.Credit.Repayment.repay_layer_transfer
#check Fermat.Conservation.Credit.Repayment.LayerTransport
#check Fermat.Conservation.Credit.Flow.GeneratorOrbit.accountFlow
#check Fermat.Conservation.Credit.Flow.GeneratorOrbit.productTransfer
#check Fermat.Conservation.Credit.Flow.GeneratorOrbit.sumTransfer
#check Fermat.Conservation.Credit.MatrixAccount
#check Fermat.Conservation.Credit.accountMatrix
#check Fermat.Conservation.Credit.accountLedger
#check Fermat.Conservation.Credit.kummer_credit_accounted_vacuum
#check Fermat.Conservation.Credit.Cycle.CapacityData.Account
#check Fermat.Conservation.Credit.Cycle.CapacityData.Account.spendingTransfer
#check Fermat.Conservation.Credit.Cycle.CapacityData.Account.spendOneTransfer

/-! Global three-column accounting is load-bearing in each claimed literal
ledger transfer. -/

#guard_depends_on Fermat.Conservation.Ledger.vacuum_conservation,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on Fermat.Conservation.Ledger.repay_conservation,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on Fermat.Conservation.Ledger.repayNat_conservation,
  Fermat.Conservation.Ledger.conservation_identity

/-! The compatibility readings retain the non-lossy Bernoulli channel
identity through their elaborated proof values. -/

#guard_depends_on
  Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.depthTransfer,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.depthTransfer_credit_decomposition,
  Fermat.Conservation.Transfer.credit_decomposition_of_stock_eq
#guard_depends_on
  Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.depth_conservation,
  Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.depthTransfer
#guard_depends_on
  Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.depth_conservation,
  Fermat.Conservation.Ledger.conservation_identity

#guard_depends_on
  Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.depth_eq_min_two_add_depth_sub_two,
  Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.depth_conservation
#guard_depends_on
  Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.cubeFree_of_surplus_eq_zero,
  Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.depth_conservation
#guard_depends_on
  Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.depth_eq_min_two_add_depth_sub_two,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.cubeFree_of_surplus_eq_zero,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Conservation.Credit.Flow.FlowCertificate.eigenvalue_cubeFree,
  Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.depth_conservation
#guard_depends_on
  Fermat.Conservation.Credit.Flow.FlowCertificate.eigenvalue_cubeFree,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Conservation.Credit.RealFlow.FlowCertificate.eigenvalue_cubeFree,
  Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.depth_conservation
#guard_depends_on
  Fermat.Conservation.Credit.RealFlow.FlowCertificate.eigenvalue_cubeFree,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Conservation.Credit.RealFlow.FlowCertificate.depthAtMostTwo,
  Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.depth_conservation
#guard_depends_on
  Fermat.Conservation.Credit.RealFlow.FlowCertificate.depthAtMostTwo,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Conservation.Credit.RealFlow.DepthTwoCertificate.atMostTwo,
  Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.depth_conservation
#guard_depends_on
  Fermat.Conservation.Credit.RealFlow.DepthTwoCertificate.atMostTwo,
  Fermat.Conservation.Ledger.conservation_identity

/-! A repayment spends exactly one typed layer.  The final guard checks only
the shape of the named open interface: it does not assert that layer
transport is inhabited. -/

#guard_depends_on Fermat.Conservation.Credit.Repayment.repay_totalLayers,
  Fermat.Conservation.Credit.Repayment.repay_layer_conservation
#guard_depends_on
  Fermat.Conservation.Credit.Repayment.repay_layer_transfer,
  Fermat.Conservation.Credit.Repayment.repay_layer_conservation
#guard_depends_on
  Fermat.Conservation.Credit.Repayment.repay_layer_transfer,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Conservation.Credit.Repayment.repay_layer_credit_decomposition,
  Fermat.Conservation.Transfer.credit_decomposition_of_stock_eq
#guard_depends_on
  Fermat.Conservation.Credit.Repayment.repay_layer_converted_decomposition,
  Fermat.Conservation.Transfer.converted_decomposition
#guard_depends_on
  Fermat.Conservation.Credit.Repayment.repay_layer_total_preserved,
  Fermat.Conservation.Transfer.total_preserved
#guard_depends_on Fermat.Conservation.Credit.Repayment.repay_totalLayers,
  Fermat.Conservation.Credit.Repayment.repay_layer_transfer
#guard_depends_on Fermat.Conservation.Credit.Repayment.repay_totalLayers,
  Fermat.Conservation.Transfer.credit_decomposition_of_stock_eq
#guard_depends_on Fermat.Conservation.Credit.Repayment.repay_one_accounted,
  Fermat.Conservation.Credit.Repayment.repay_layer_transfer
#guard_depends_on Fermat.Conservation.Credit.Repayment.nonempty_repay_one_iff,
  Fermat.Conservation.Credit.Repayment.repay_layer_conservation
#guard_depends_on Fermat.Conservation.Credit.Repayment.nonempty_repay_one_iff,
  Fermat.Conservation.Credit.Repayment.repay_layer_transfer
#guard_depends_on
  Fermat.Conservation.Credit.Repayment.repay_of_deep_generated_cycle,
  Fermat.Conservation.Credit.Repayment.repay_layer_transfer
#guard_depends_on Fermat.Conservation.Credit.Repayment.LayerTransport,
  Fermat.Conservation.Credit.Repayment.LayerConservation
#guard_depends_on Fermat.Conservation.Credit.Repayment.Repay.ofLayerTransport,
  Fermat.Conservation.Credit.Repayment.LayerTransport
#guard_depends_on Fermat.Conservation.Credit.Repayment.Repay.ofLayerTransport,
  Fermat.Conservation.Credit.Repayment.LayerConservation

/-! Generated products and finite sums are now zero-spent global transfers.
The legacy additive equalities are projections of their available columns. -/

#guard_depends_on
  Fermat.Conservation.Credit.Flow.GeneratorOrbit.productTransfer,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Conservation.Credit.Flow.GeneratorOrbit.productTransfer,
  Fermat.Conservation.Credit.Flow.GeneratorOrbit.accountFlow
#guard_depends_on
  Fermat.Conservation.Credit.Flow.GeneratorOrbit.sumTransfer,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Conservation.Credit.Flow.GeneratorOrbit.sumTransfer,
  Fermat.Conservation.Credit.Flow.GeneratorOrbit.accountFlow
#guard_depends_on
  Fermat.Conservation.Credit.Flow.GeneratorOrbit.product_conservation,
  Fermat.Conservation.Credit.Flow.GeneratorOrbit.productTransfer
#guard_depends_on
  Fermat.Conservation.Credit.Flow.GeneratorOrbit.product_conservation,
  Fermat.Conservation.Transfer.available_eq
#guard_depends_on
  Fermat.Conservation.Credit.Flow.GeneratorOrbit.product_conservation,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Conservation.Credit.Flow.GeneratorOrbit.sum_conservation,
  Fermat.Conservation.Credit.Flow.GeneratorOrbit.sumTransfer
#guard_depends_on
  Fermat.Conservation.Credit.Flow.GeneratorOrbit.sum_conservation,
  Fermat.Conservation.Transfer.available_eq
#guard_depends_on
  Fermat.Conservation.Credit.Flow.GeneratorOrbit.sum_conservation,
  Fermat.Conservation.Ledger.conservation_identity

/-! C1 now has a faithful union-additive matrix account and a global vacuum;
the legacy native equality is projected from that accounted theorem. -/

#guard_depends_on Fermat.Conservation.Credit.accountMatrix_merge,
  Fermat.Conservation.Credit.merge
#guard_depends_on Fermat.Conservation.Credit.accountLedger_conservation,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on Fermat.Conservation.Credit.kummer_credit_accounted_vacuum,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on Fermat.Conservation.Credit.kummer_credit_accounted_vacuum,
  Fermat.Conservation.Credit.generated_eq_bot_of_no_generator
#guard_depends_on Fermat.Conservation.Credit.kummer_credit_vacuum,
  Fermat.Conservation.Credit.kummer_credit_accounted_vacuum
#guard_depends_on Fermat.Conservation.Credit.kummer_credit_vacuum,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on Fermat.Conservation.Credit.kummer_credit_vacuum,
  Fermat.Conservation.Credit.accountLedger_eq_vacuum_iff

#guard_depends_on Fermat.Conservation.Credit.kummer_credit_vacuum,
  Fermat.Conservation.Credit.generated_eq_bot_of_no_generator

/-! C2's native relative index is now the fixed total of a credit account.
Finite capacity funds a positive one-unit Transfer, and all legacy capacity
equalities are projections of the corresponding global ledgers. -/

#guard_depends_on
  Fermat.Conservation.Credit.Cycle.capacityIndex_eq_relIndex,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Conservation.Credit.Cycle.capacityIndex_eq_relIndex,
  Fermat.Conservation.Credit.Cycle.capacityIndexLedger
#guard_depends_on
  Fermat.Conservation.Credit.Cycle.CapacityData.Account.spendingTransfer,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Conservation.Credit.Cycle.CapacityData.Account.spending_credit_decomposition,
  Fermat.Conservation.Transfer.credit_decomposition_of_stock_eq
#guard_depends_on
  Fermat.Conservation.Credit.Cycle.CapacityData.Account.spending_converted_decomposition,
  Fermat.Conservation.Transfer.converted_decomposition
#guard_depends_on
  Fermat.Conservation.Credit.Cycle.CapacityData.Account.spending_total_preserved,
  Fermat.Conservation.Transfer.total_preserved
#guard_depends_on
  Fermat.Conservation.Credit.Cycle.CapacityData.Account.spendOne_credit_lt,
  Fermat.Conservation.Transfer.credit_lt_of_stock_eq
#guard_depends_on
  Fermat.Conservation.Credit.Cycle.CapacityData.Account.full_credit_eq_relIndex,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Conservation.Credit.Cycle.CapacityData.capacity_eq_relIndex,
  Fermat.Conservation.Credit.Cycle.CapacityData.Account.full_credit_eq_relIndex
#guard_depends_on
  Fermat.Conservation.Credit.Cycle.CapacityData.capacity_eq_relIndex,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Conservation.Credit.Cycle.CapacityData.capacity_pos,
  Fermat.Conservation.Credit.Cycle.CapacityData.Account.spendOneTransfer
#guard_depends_on
  Fermat.Conservation.Credit.Cycle.CapacityData.capacity_pos,
  Fermat.Conservation.Transfer.credit_lt_of_stock_eq
#guard_depends_on
  Fermat.Conservation.Credit.Cycle.CapacityData.capacity_pos,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Conservation.Credit.Cycle.CapacityCertificate.sound,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Conservation.Credit.Cycle.IndexCertificate.sound,
  Fermat.Conservation.Ledger.conservation_identity

/-! Gauge quotienting moves the faithful generated matrix account from credit
to conversion while preserving the stock charge in a product carrier. -/

#guard_depends_on
  Fermat.Conservation.Credit.GaugeQuotient.PrimeData.quotientLedger_eq_bot,
  Fermat.Conservation.Credit.kummer_credit_vacuum
#guard_depends_on
  Fermat.Conservation.Credit.GaugeQuotient.PrimeData.quotientLedger_eq_bot,
  Fermat.Conservation.Credit.generated_eq_bot_of_no_generator
#guard_depends_on
  Fermat.Conservation.Credit.GaugeQuotient.PrimeData.quotientLedger_eq_bot,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Conservation.Credit.GaugeQuotient.PrimeData.sourceToQuotientTransfer,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Conservation.Credit.GaugeQuotient.PrimeData.sourceToQuotient_credit_decomposition,
  Fermat.Conservation.Transfer.available_eq
#guard_depends_on
  Fermat.Conservation.Credit.GaugeQuotient.PrimeData.quotientCharge_quotientState,
  Fermat.Conservation.Credit.GaugeQuotient.PrimeData.sourceToQuotientTransfer
#guard_depends_on
  Fermat.Conservation.Credit.GaugeQuotient.PrimeData.quotientCharge_quotientState,
  Fermat.Conservation.Transfer.total_preserved
#guard_depends_on
  Fermat.Conservation.Credit.GaugeQuotient.PrimeData.quotient_vacuum_and_charge_eq,
  Fermat.Conservation.Credit.GaugeQuotient.PrimeData.quotientLedger_eq_bot
#guard_depends_on
  Fermat.Conservation.Credit.GaugeQuotient.PrimeData.quotient_vacuum_and_charge_eq,
  Fermat.Conservation.Credit.GaugeQuotient.PrimeData.quotientCharge_quotientState
#guard_depends_on
  Fermat.Conservation.Credit.GaugeQuotient.PrimeData.quotient_vacuum_and_charge_eq,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Conservation.Credit.GaugeQuotient.PrimeData.quotient_vacuum_and_charge_eq,
  Fermat.Conservation.Credit.GaugeQuotient.PrimeData.sourceToQuotientTransfer
#guard_depends_on
  Fermat.Conservation.Credit.Fold.relativeNormFold_apply_of_conjugation,
  Fermat.Conservation.Credit.Fold.relativeNormFold_apply
#guard_depends_on
  Fermat.Conservation.Credit.Fold.relativeNormFold_apply,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Conservation.Credit.Fold.relativeNormFold_apply_of_conjugation,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Conservation.Credit.Fold.relativeNormFold_class_eq_zero_of_coprime_card,
  Fermat.Conservation.Credit.Fold.relativeNormFoldClassTransfer_of_coprime_card
#guard_depends_on
  Fermat.Conservation.Credit.Fold.relativeNormFold_class_eq_zero_of_coprime_card,
  Fermat.Conservation.Transfer.converted_decomposition
#guard_depends_on
  Fermat.Conservation.Credit.Fold.conjugate_class_fold_eq_zero_of_coprime_card,
  Fermat.Conservation.Credit.Fold.conjugateClassFoldTransfer_of_coprime_card
#guard_depends_on
  Fermat.Conservation.Credit.Fold.odd_torsion_netting,
  Fermat.Conservation.Credit.Fold.oddTorsionNettingTransfer
#guard_depends_on
  Fermat.Conservation.KummerDrain.AllocatedFactorLedger.vandiverSevenD_of_relativeNormFold,
  Fermat.Conservation.KummerDrain.AllocatedFactorLedger.vandiverSevenDFoldToVacuumTransfer
#guard_depends_on
  Fermat.Conservation.KummerDrain.AllocatedFactorLedger.vandiverSevenD_of_conjugationTranspose,
  Fermat.Conservation.KummerDrain.AllocatedFactorLedger.conjugationFoldToVacuumTransfer
#guard_depends_on
  Fermat.Conservation.KummerDrain.factorPrincipalizationPermit_of_vandiver_relations,
  Fermat.Conservation.Credit.Fold.oddTorsionNettingTransfer
#guard_depends_on
  Fermat.Conservation.KummerDrain.factorPrincipalizationPermit_finTwo_of_vandiver_relations,
  Fermat.Conservation.Credit.Fold.oddTorsionNettingTransfer

/-! ## C1: generated vacuum and two-sided semilattice -/

/--
info: 'Fermat.Conservation.Credit.mem_generated' does not depend on any axioms
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.mem_generated

/--
info: 'Fermat.Conservation.Credit.mem_merge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.mem_merge

/--
info: 'Fermat.Conservation.Credit.merge_self' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.merge_self

/--
info: 'Fermat.Conservation.Credit.merge_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.merge_comm

/--
info: 'Fermat.Conservation.Credit.merge_assoc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.merge_assoc

/--
info: 'Fermat.Conservation.Credit.merge_bot_left' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.merge_bot_left

/--
info: 'Fermat.Conservation.Credit.merge_bot_right' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.merge_bot_right

/--
info: 'Fermat.Conservation.Credit.generated_union' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.generated_union

/--
info: 'Fermat.Conservation.Credit.opposite_apply' depends on axioms: [Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.opposite_apply

/--
info: 'Fermat.Conservation.Credit.opposite_opposite' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.opposite_opposite

/--
info: 'Fermat.Conservation.Credit.opposite_merge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.opposite_merge

/--
info: 'Fermat.Conservation.Credit.reverseRoute_reverseRoute' depends on axioms: [Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.reverseRoute_reverseRoute

/--
info: 'Fermat.Conservation.Credit.opposite_generated' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.opposite_generated

/--
info: 'Fermat.Conservation.Credit.generated_eq_bot_of_no_generator' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.generated_eq_bot_of_no_generator

/--
info: 'Fermat.Conservation.Credit.kummer_credit_vacuum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.kummer_credit_vacuum

/-! ## C2: one cycle, generated edge family, and capacity index -/

/--
info: 'Fermat.Conservation.Credit.Cycle.point_zero' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Cycle.point_zero

/--
info: 'Fermat.Conservation.Credit.Cycle.point_succ' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Cycle.point_succ

/--
info: 'Fermat.Conservation.Credit.Cycle.point_closes' does not depend on any axioms
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Cycle.point_closes

/--
info: 'Fermat.Conservation.Credit.Cycle.edge_mem_generatedSubledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Cycle.edge_mem_generatedSubledger

/--
info: 'Fermat.Conservation.Credit.Cycle.capacityIndex_eq_relIndex' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Cycle.capacityIndex_eq_relIndex

/--
info: 'Fermat.Conservation.Credit.Cycle.transfer_self' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Cycle.transfer_self

/--
info: 'Fermat.Conservation.Credit.Cycle.transfer_opposite' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Cycle.transfer_opposite

/--
info: 'Fermat.Conservation.Credit.Cycle.CapacityData.capacity_eq_relIndex' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Cycle.CapacityData.capacity_eq_relIndex

/--
info: 'Fermat.Conservation.Credit.Cycle.CapacityData.capacity_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Cycle.CapacityData.capacity_pos

/--
info: 'Fermat.Conservation.Credit.Cycle.CapacityCertificate.sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Cycle.CapacityCertificate.sound

/--
info: 'Fermat.Conservation.Credit.Cycle.IndexCertificate.sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Cycle.IndexCertificate.sound

/--
info: 'Fermat.Conservation.Credit.Cycle.iterate_mul_left' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Cycle.iterate_mul_left

/--
info: 'Fermat.Conservation.Credit.Cycle.ofMul_point' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Cycle.ofMul_point

/-! ## C3: Vandiver repayment on the generated edge family -/

/--
info: 'Fermat.Conservation.Credit.Repayment.realUnits_odd_pow_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Repayment.realUnits_odd_pow_injective

/--
info: 'Fermat.Conservation.Credit.Repayment.repay_of_deep_generated_cycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Repayment.repay_of_deep_generated_cycle

/-! ## C6: class-ledger transpose, relative norm, and statewise netting -/

/--
info: 'Fermat.Conservation.Credit.Fold.conjugateTranspose_apply' depends on axioms: [Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Fold.conjugateTranspose_apply

/--
info: 'Fermat.Conservation.Credit.Fold.conjugateTranspose_conjugateTranspose' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Fold.conjugateTranspose_conjugateTranspose

/--
info: 'Fermat.Conservation.Credit.Fold.relativeNormFold_apply' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Fold.relativeNormFold_apply

/--
info: 'Fermat.Conservation.Credit.Fold.relativeNormFold_apply_of_conjugation' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Fold.relativeNormFold_apply_of_conjugation

/--
info: 'Fermat.Conservation.Credit.Fold.fractionalIdealClass_eq_zero_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Fold.fractionalIdealClass_eq_zero_iff

/--
info: 'Fermat.Conservation.Credit.Fold.nsmul_fractionalIdealClass_eq_zero_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Fold.nsmul_fractionalIdealClass_eq_zero_iff

/--
info: 'Fermat.Conservation.Credit.Fold.fractionalIdealClass_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Fold.fractionalIdealClass_mul

/--
info: 'Fermat.Conservation.Credit.Fold.relativeNorm_isPrincipal_of_coprime_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Fold.relativeNorm_isPrincipal_of_coprime_card

/--
info: 'Fermat.Conservation.Credit.Fold.relativeNormFold_class_eq_zero_of_coprime_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Fold.relativeNormFold_class_eq_zero_of_coprime_card

/--
info: 'Fermat.Conservation.Credit.Fold.map_relativeNorm_eq_mul_conjugate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Fold.map_relativeNorm_eq_mul_conjugate

/--
info: 'Fermat.Conservation.Credit.Fold.conjugate_class_fold_eq_zero_of_coprime_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Fold.conjugate_class_fold_eq_zero_of_coprime_card

/--
info: 'Fermat.Conservation.Credit.Fold.odd_torsion_netting' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Fold.odd_torsion_netting

/-! ## W1--W2: generated flow and gauge diagonalization -/

open Lean Elab Command

/-- Fail if any declaration below a prefix uses an axiom beyond Lean's
standard extensionality, choice, and quotient-soundness boundary.  The
prefix form keeps this audit exhaustive when a generated API gains another
public theorem. -/
elab "#guard_standard_axioms_prefix " p:ident : command => do
  let env ← getEnv
  let auditedPrefix := p.getId
  let allowed : Array Name :=
    #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations :=
    env.constants.toList
      |>.map Prod.fst
      |>.filter auditedPrefix.isPrefixOf
  for declaration in declarations do
    let axioms ← Lean.collectAxioms declaration
    let unexpected := axioms.filter fun ax =>
      !allowed.contains ax
    unless unexpected.isEmpty do
      throwError
        "{declaration} depends on nonstandard axioms: {unexpected}"

-- This prefix exhaustively covers `Flow`, `DepthFlow`, `CyclotomicFlow`,
-- `MomentFlow`, and `NonlinearFlow`.
#guard_standard_axioms_prefix Fermat.Conservation.Credit.Flow
#guard_standard_axioms_prefix Fermat.Conservation.Credit.Gauge
#guard_standard_axioms_prefix Fermat.Conservation.Credit.Bernoulli
-- `RealGauge` has its own namespace.
#guard_standard_axioms_prefix Fermat.Conservation.Credit.RealGauge
-- This prefix exhaustively covers `RealHighFlow`, `RelationDepthFlow`, and
-- `RealForcing`.
#guard_standard_axioms_prefix Fermat.Conservation.Credit.RealFlow
#guard_standard_axioms_prefix Fermat.Conservation.Credit.GaugeQuotient
#guard_standard_axioms_prefix Fermat.Conservation.Credit.Fold
#guard_standard_axioms_prefix Fermat.Conservation.CyclotomicDrain
#guard_standard_axioms_prefix Fermat.Conservation.KummerDrain

/--
info: 'Fermat.Conservation.Credit.Gauge.GaugeData.orbitGenerator_pow_rank_add_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Gauge.GaugeData.orbitGenerator_pow_rank_add_one

/--
info: 'Fermat.Conservation.Credit.Gauge.GaugeData.cycle_rank' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Gauge.GaugeData.cycle_rank

/--
info: 'Fermat.Conservation.Credit.Gauge.GaugeData.cycle_point' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Gauge.GaugeData.cycle_point

/--
info: 'Fermat.Conservation.Credit.Gauge.GaugeData.realCycleOrder_odd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Gauge.GaugeData.realCycleOrder_odd

/--
info: 'Fermat.Conservation.Credit.Gauge.GaugeData.prime_mod_four_eq_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Gauge.GaugeData.prime_mod_four_eq_three

/--
info: 'Fermat.Conservation.Credit.Gauge.GaugeData.orbitNode_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Gauge.GaugeData.orbitNode_injective

/--
info: 'Fermat.Conservation.Credit.Gauge.GaugeData.orbitGenerator_square_pow_succ_ne_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Gauge.GaugeData.orbitGenerator_square_pow_succ_ne_one

/--
info: 'Fermat.Conservation.Credit.Gauge.GaugeData.rowScale_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Gauge.GaugeData.rowScale_ne_zero

/--
info: 'Fermat.Conservation.Credit.Gauge.GaugeData.columnScale_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Gauge.GaugeData.columnScale_ne_zero

/--
info: 'Fermat.Conservation.Credit.Gauge.GaugeData.characterMatrix_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Gauge.GaugeData.characterMatrix_apply

/--
info: 'Fermat.Conservation.Credit.Gauge.GaugeData.characterMatrix_eq_high_edge_difference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Gauge.GaugeData.characterMatrix_eq_high_edge_difference

/--
info: 'Fermat.Conservation.Credit.Gauge.GaugeData.characterMatrix_det_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Gauge.GaugeData.characterMatrix_det_ne_zero

/--
info: 'Fermat.Conservation.Credit.Gauge.GaugeData.raw_eq_zero_of_character_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Gauge.GaugeData.raw_eq_zero_of_character_eq_zero

/--
info: 'Fermat.Conservation.Credit.Gauge.GaugeData.characterCoordinates_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Gauge.GaugeData.characterCoordinates_injective

/-! ## W1 completed flow, exact lift, and generic W3 forcing -/

/--
info: 'Fermat.Conservation.Credit.Flow.completedLogFlow_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Flow.completedLogFlow_mul

/--
info: 'Fermat.Conservation.Credit.Flow.dworkParameterPowerBasis_coeff_sub_mem_primeIdeal_sq_of_mem_parameterIdeal_two_mul_prime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Flow.dworkParameterPowerBasis_coeff_sub_mem_primeIdeal_sq_of_mem_parameterIdeal_two_mul_prime

/--
info: 'Fermat.Conservation.Credit.Flow.dworkCompleteCyclotomicEquiv_completedLog' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Flow.dworkCompleteCyclotomicEquiv_completedLog

/--
info: 'Fermat.Conservation.Credit.Bernoulli.exceptional_bernoulli_numerator_not_dvd_cube_of_faulhaber' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Bernoulli.exceptional_bernoulli_numerator_not_dvd_cube_of_faulhaber

/--
info: 'Fermat.Conservation.Credit.Flow.intCast_teichNodeValue' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Flow.intCast_teichNodeValue

/--
info: 'Fermat.Conservation.Credit.Flow.gaugeGeneratorOrbit_exponentFlow_eq_exactHighEdgeCoefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Flow.gaugeGeneratorOrbit_exponentFlow_eq_exactHighEdgeCoefficient

/--
info: 'Fermat.Conservation.Credit.Flow.intCast_exactHighEdgeCoefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Flow.intCast_exactHighEdgeCoefficient

/--
info: 'Fermat.Conservation.Credit.Flow.exponent_dvd_of_highFlowVanishes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Flow.exponent_dvd_of_highFlowVanishes

/--
info: 'Fermat.Conservation.Credit.Flow.deepExponentForcing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.Flow.deepExponentForcing

/--
info: 'Fermat.Conservation.Credit.RealFlow.relation_polynomial_depth_of_deep_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.RealFlow.relation_polynomial_depth_of_deep_witness

/--
info: 'Fermat.Conservation.Credit.RealFlow.exists_moment_ready_relation_of_vandiverDeep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.RealFlow.exists_moment_ready_relation_of_vandiverDeep

/--
info: 'Fermat.Conservation.Credit.RationalFlow.reduce_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.RationalFlow.reduce_eq_zero_iff

/--
info: 'Fermat.Conservation.Credit.RationalFlow.denominatorPrimeTo_quotient_of_recurrence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.RationalFlow.denominatorPrimeTo_quotient_of_recurrence

/--
info: 'Fermat.Conservation.Credit.RationalFlow.denominatorPrimeTo_logDerivative_of_recurrence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.RationalFlow.denominatorPrimeTo_logDerivative_of_recurrence

/--
info: 'Fermat.Conservation.Credit.LogRate.Relation.formalDerivativeAtZero_generatedRelationRate_high' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.LogRate.Relation.formalDerivativeAtZero_generatedRelationRate_high

/--
info: 'Fermat.Conservation.Credit.LogRate.Arithmetic.prime_cube_dvd_exact_of_rate_numerator_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.LogRate.Arithmetic.prime_cube_dvd_exact_of_rate_numerator_sq

/--
info: 'Fermat.Conservation.Credit.RateFlow.Composition.rateJet_selected_prime_integral_and_num_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.RateFlow.Composition.rateJet_selected_prime_integral_and_num_sq

/--
info: 'Fermat.Conservation.Credit.HighFlowClosure.GeneratedRelation.highFlowVanishes_of_moment_ready_generated_relation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.HighFlowClosure.GeneratedRelation.highFlowVanishes_of_moment_ready_generated_relation

/--
info: 'Fermat.Conservation.Credit.RealFlow.highFlowVanishes_of_deepRelation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.RealFlow.highFlowVanishes_of_deepRelation

/--
info: 'Fermat.Conservation.Credit.RealFlow.deepFlowLaw_realCyclotomicOrbitNodeQuotient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.RealFlow.deepFlowLaw_realCyclotomicOrbitNodeQuotient

/-! ## Transformer quotient, drain, and factor-ledger receipts -/

/--
info: 'Fermat.Conservation.Credit.RealFlow.FlowCertificate.depthAtMostTwo' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.RealFlow.FlowCertificate.depthAtMostTwo

/--
info: 'Fermat.Conservation.Credit.GaugeQuotient.PrimeData.quotientTransfer_eq_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.GaugeQuotient.PrimeData.quotientTransfer_eq_one

/--
info: 'Fermat.Conservation.Credit.GaugeQuotient.PrimeData.quotientLedger_eq_morphism' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.GaugeQuotient.PrimeData.quotientLedger_eq_morphism

/--
info: 'Fermat.Conservation.Credit.GaugeQuotient.PrimeData.quotientLedger_eq_bot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.GaugeQuotient.PrimeData.quotientLedger_eq_bot

/--
info: 'Fermat.Conservation.Credit.GaugeQuotient.PrimeData.debt_eq_repaymentRoot_pow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.GaugeQuotient.PrimeData.debt_eq_repaymentRoot_pow

/--
info: 'Fermat.Conservation.Credit.GaugeQuotient.PrimeData.quotientCharge_quotientState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.GaugeQuotient.PrimeData.quotientCharge_quotientState

/--
info: 'Fermat.Conservation.Credit.GaugeQuotient.PrimeData.quotient_vacuum_and_charge_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.Credit.GaugeQuotient.PrimeData.quotient_vacuum_and_charge_eq

/--
info: 'Fermat.Conservation.CyclotomicDrain.lambda_eq_neg_zeta_sub_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.CyclotomicDrain.lambda_eq_neg_zeta_sub_one

/--
info: 'Fermat.Conservation.CyclotomicDrain.charge_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.CyclotomicDrain.charge_pow

/--
info: 'Fermat.Conservation.CyclotomicDrain.lambda_charge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.CyclotomicDrain.lambda_charge

/--
info: 'Fermat.Conservation.CyclotomicDrain.drainCharge_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.CyclotomicDrain.drainCharge_eq

/--
info: 'Fermat.Conservation.CyclotomicDrain.drainCharge_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.CyclotomicDrain.drainCharge_strictMono

/--
info: 'Fermat.Conservation.CyclotomicDrain.drainCharge_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.CyclotomicDrain.drainCharge_step

/--
info: 'Fermat.Conservation.KummerDrain.factorNode_product' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.KummerDrain.factorNode_product

/--
info: 'Fermat.Conservation.KummerDrain.factorIdeal_product' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.KummerDrain.factorIdeal_product

/--
info: 'Fermat.Conservation.KummerDrain.factorNode_charge_product' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.KummerDrain.factorNode_charge_product

/--
info: 'Fermat.Conservation.KummerDrain.factorNode_charge_gauge_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.KummerDrain.factorNode_charge_gauge_invariant

/--
info: 'Fermat.Conservation.KummerDrain.AllocatedFactorLedger.rootFractionalIdeal_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.KummerDrain.AllocatedFactorLedger.rootFractionalIdeal_ne_zero

/--
info: 'Fermat.Conservation.KummerDrain.AllocatedFactorLedger.rootClass_torsion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.KummerDrain.AllocatedFactorLedger.rootClass_torsion

/--
info: 'Fermat.Conservation.KummerDrain.AllocatedFactorLedger.rootQuotient_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.KummerDrain.AllocatedFactorLedger.rootQuotient_ne_zero

/--
info: 'Fermat.Conservation.KummerDrain.AllocatedFactorLedger.rootQuotient_pow_isPrincipal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.KummerDrain.AllocatedFactorLedger.rootQuotient_pow_isPrincipal

/--
info: 'Fermat.Conservation.KummerDrain.AllocatedFactorLedger.vandiverSevenD_of_relativeNormFold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.KummerDrain.AllocatedFactorLedger.vandiverSevenD_of_relativeNormFold

/--
info: 'Fermat.Conservation.KummerDrain.AllocatedFactorLedger.vandiverSevenD_of_conjugationTranspose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.KummerDrain.AllocatedFactorLedger.vandiverSevenD_of_conjugationTranspose

/--
info: 'Fermat.Conservation.KummerDrain.AllocatedFactorLedger.rootQuotient_isPrincipal_of_vandiver_relations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.KummerDrain.AllocatedFactorLedger.rootQuotient_isPrincipal_of_vandiver_relations

/--
info: 'Fermat.Conservation.KummerDrain.factorPrincipalizationPermit_of_vandiver_relations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.KummerDrain.factorPrincipalizationPermit_of_vandiver_relations

/--
info: 'Fermat.Conservation.KummerDrain.factorPrincipalizationPermit_finTwo_of_vandiver_relations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.KummerDrain.factorPrincipalizationPermit_finTwo_of_vandiver_relations

/-! ## Exhaustive forbidden-prefix guards -/

/-- Fail if the imported environment contains any declaration below a
forbidden namespace prefix. -/
elab "#guard_no_decl_prefix " p:ident : command => do
  let env ← getEnv
  let forbiddenPrefix := p.getId
  let offenders :=
    env.constants.toList.filter fun entry =>
      forbiddenPrefix.isPrefixOf entry.1
  unless offenders.isEmpty do
    throwError
      "declarations with forbidden prefix {forbiddenPrefix}: {offenders.map Prod.fst}"

/-- Fail if the transitive import graph contains a module below a forbidden
prefix.  Declaration checks alone cannot detect modules which declare into
a shorter namespace. -/
elab "#guard_no_module_prefix " p:ident : command => do
  let env ← getEnv
  let forbiddenPrefix := p.getId
  let offenders :=
    env.header.moduleNames.filter forbiddenPrefix.isPrefixOf
  unless offenders.isEmpty do
    throwError
      "modules with forbidden prefix {forbiddenPrefix}: {offenders}"

/-- Fail if one exact module occurs in the transitive import graph.  This is
used when a permitted sibling module shares its name prefix. -/
elab "#guard_no_module " p:ident : command => do
  let env ← getEnv
  let forbiddenModule := p.getId
  if env.header.moduleNames.contains forbiddenModule then
    throwError "forbidden module {forbiddenModule} is imported"

#guard_no_decl_prefix Fermat.FiftyNine
#guard_no_decl_prefix Fermat.FiftyNine.GenericProof
#guard_no_decl_prefix Fermat.FiftyNine.FirstCase
#guard_no_decl_prefix Fermat.FiftyNine.GenericSecondCase
#guard_no_decl_prefix Fermat.FiftyNine.Folding
#guard_no_decl_prefix Fermat.FiftyNine.GenericChannels
#guard_no_decl_prefix Fermat.FiftyNine.GenericLemmaTwo
#guard_no_decl_prefix Fermat.GenericIrregular
#guard_no_decl_prefix Fermat.Irregular
#guard_no_decl_prefix Fermat.Regular
#guard_no_decl_prefix Fermat.KummerIso
#guard_no_decl_prefix Fermat.Ladder

#guard_no_module_prefix Fermat.FiftyNine
#guard_no_module_prefix Fermat.GenericIrregular
#guard_no_module_prefix Fermat.Irregular
#guard_no_module_prefix Fermat.Regular
#guard_no_module_prefix Fermat.KummerIso
#guard_no_module_prefix Fermat.Ladder
#guard_no_module Fermat.Statement

/-! ## Mechanical selected-prime source-literal gate -/

/-- An identifier character on either side makes the two selected digits part
of a larger token rather than the load-bearing numeral under audit. -/
private def isLeanIdentifierChar (character : Char) : Bool :=
  character.isAlphanum || character == '_'

/-- Source lines containing a standalone selected-prime numeral outside Lean
comments and string literals.  Block-comment depth is tracked across lines,
including nested `/- ... -/` comments. -/
private partial def selectedPrimeTokenLines
    (characters : List Char) (line : Nat := 1)
    (blockCommentDepth : Nat := 0) (inLineComment : Bool := false)
    (inString : Bool := false) (stringEscape : Bool := false)
    (previousIsIdentifier : Bool := false)
    (offenders : Array Nat := #[]) : Array Nat :=
  match characters with
  | [] => offenders
  | '\n' :: rest =>
      selectedPrimeTokenLines rest (line + 1) blockCommentDepth false
        inString false false offenders
  | character :: rest =>
      if inLineComment then
        selectedPrimeTokenLines rest line blockCommentDepth true
          inString false false offenders
      else if blockCommentDepth > 0 then
        match character, rest with
        | '/', '-' :: tail =>
            selectedPrimeTokenLines tail line (blockCommentDepth + 1) false
              false false false offenders
        | '-', '/' :: tail =>
            selectedPrimeTokenLines tail line (blockCommentDepth - 1) false
              false false false offenders
        | _, _ =>
            selectedPrimeTokenLines rest line blockCommentDepth false
              false false false offenders
      else if inString then
        if stringEscape then
          selectedPrimeTokenLines rest line 0 false true false false offenders
        else if character == '\\' then
          selectedPrimeTokenLines rest line 0 false true true false offenders
        else if character == '"' then
          selectedPrimeTokenLines rest line 0 false false false false offenders
        else
          selectedPrimeTokenLines rest line 0 false true false false offenders
      else
        match character, rest with
        | '\'', '\\' :: _ :: '\'' :: tail =>
            selectedPrimeTokenLines tail line 0 false false false false offenders
        | '\'', _ :: '\'' :: tail =>
            selectedPrimeTokenLines tail line 0 false false false false offenders
        | '-', '-' :: tail =>
            selectedPrimeTokenLines tail line 0 true false false false offenders
        | '/', '-' :: tail =>
            selectedPrimeTokenLines tail line 1 false false false false offenders
        | '5', '9' :: tail =>
            let nextIsIdentifier :=
              match tail with
              | next :: _ => isLeanIdentifierChar next
              | [] => false
            let offenders :=
              if previousIsIdentifier || nextIsIdentifier then
                offenders
              else
                offenders.push line
            selectedPrimeTokenLines tail line 0 false false false true offenders
        | _, _ =>
            if character == '"' then
              selectedPrimeTokenLines rest line 0 false true false false offenders
            else
              selectedPrimeTokenLines rest line 0 false false false
                (isLeanIdentifierChar character) offenders

#guard selectedPrimeTokenLines "59".toList == #[1]
#guard selectedPrimeTokenLines "\n59".toList == #[2]
#guard selectedPrimeTokenLines "x59 590 159 59x".toList == #[]
#guard selectedPrimeTokenLines
  "/- outer /- 59 -/ -/\n-- 59\n\"59\"".toList == #[]

/-- Scan every generic credit Lean source together with the route-neutral
drain, Kummer factor-ledger, Transfer, Heisenberg payload, interaction,
receipted class-carrier, transverse-annihilator, involutive-base,
route-algebra, swap-quotient, linking-interface, common-action-stage, and
final linking-verification modules, rejecting the campaign's selected prime
numeral `59` when it occurs as a standalone code token.  Campaign prose in
comments and strings is deliberately ignored. -/
elab "#guard_no_selected_prime_literal" : command => do
  let currentPath := System.FilePath.mk (← getFileName)
  let some sourceDirectory := currentPath.parent
    | throwError "cannot locate the generic credit source directory"
  let some conservationDirectory := sourceDirectory.parent
    | throwError "cannot locate the generic conservation source directory"
  let entries ← liftIO <| System.FilePath.readDir sourceDirectory
  let mut offenders : Array String := #[]
  for entry in entries do
    if entry.path.extension == some "lean" then
      let source ← liftIO <| IO.FS.readFile entry.path
      for line in selectedPrimeTokenLines source.toList do
        offenders := offenders.push s!"{entry.path}:{line}"
  for filename in
      #["CyclotomicDrain.lean", "KummerDrain.lean", "Transfer.lean",
        "Heis.lean", "AreaTransfer.lean", "Interaction.lean",
        "ClassCarrier.lean", "TransverseAnnihilator.lean",
        "InvolutiveBase.lean", "RouteAlgebra.lean", "SwapQuotient.lean",
        "LinkingInterfaces.lean", "SelmerSequence.lean",
        "CommonActionStage.lean", "TameSymbol.lean",
        "SelmerEigenspace.lean", "TamePlacePairing.lean",
        "LinkingVerification.lean"] do
    let path := conservationDirectory / System.FilePath.mk filename
    let source ← liftIO <| IO.FS.readFile path
    for line in selectedPrimeTokenLines source.toList do
      offenders := offenders.push s!"{path}:{line}"
  unless offenders.isEmpty do
    throwError
      "selected-prime source literal occurs at {offenders}"

#guard_no_selected_prime_literal

/-! The forbidden repository transport is a declaration, not a namespace. -/

/--
error: Unknown identifier `Fermat.HoldsAt.mono_of_dvd`
-/
#guard_msgs in
#check Fermat.HoldsAt.mono_of_dvd
