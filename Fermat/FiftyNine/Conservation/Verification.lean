/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# N59 conservation structural verification

This non-imported executable audit leaf checks every theorem currently
exposed by the clean exponent-59 structural spine and the selected
credit-flow instance.  It also checks declarations and the transitive module
graph, rather than relying only on representative unused-name tests.

The final `Fermat.HoldsAt 59` theorem is not present here.  The selected
gauge quotient is complete, while the common-action stage retains the
statewise class receipts and, at one supplied reflected pair, localizes the
first character-allocation wall.  It reaches the strict-route representation
wall only behind evidence for every earlier seam.
-/
import Fermat.Conservation.GuardDependsOn
import Fermat.Conservation.Ledger
import Fermat.Conservation.Transfer
import Fermat.Conservation.ExteriorTransfer
import Fermat.FiftyNine.Conservation.Spine
import Fermat.FiftyNine.Conservation.CapacityCertificate
import Fermat.FiftyNine.Conservation.BoundedSinnott
import Fermat.FiftyNine.Conservation.Instance
import Fermat.FiftyNine.Conservation.DepthCertificate
import Fermat.FiftyNine.Conservation.GaugeQuotient
import Fermat.FiftyNine.Conservation.Fold
import Fermat.FiftyNine.Conservation.StateFactorPair
import Fermat.FiftyNine.Conservation.StateFactorConjugation
import Fermat.FiftyNine.Conservation.CommonActionStage
import Fermat.FiftyNine.Conservation.TateBridge
import Fermat.FiftyNine.Conservation.DetectorWitness827
import Fermat.FiftyNine.Conservation.GaugeSteering827
import Fermat.FiftyNine.Conservation.SplitPrimeFourier827
import Fermat.FiftyNine.Conservation.PointedTateIncidence
import Fermat.FiftyNine.Conservation.ArtinHasseInventory
import Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59
import Fermat.FiftyNine.Conservation.TransformerProbe

/-! ## Ledger-literal gate -/

#check Fermat.Conservation.Ledger.conservation_identity
#check Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.depth_conservation
#check Fermat.Conservation.Credit.Repayment.repay_layer_conservation
#check Fermat.Conservation.Credit.Repayment.LayerTransport

/-! The seven selected native stock laws remain named.  N3 and N5 are now
globally accounted on their selected paths; the checks alone make no such
claim for the other five fields. -/

#check Fermat.One.charge_ledger
#check Fermat.Two.charge_ledger
#check Fermat.Three.Conservation.ledger_identity
#check Fermat.Four.Conservation.pythagorean_balance_engine
#check Fermat.Five.Conservation.quintic_ledger
#check Fermat.Six.Conservation.sixth_ledger
#check Fermat.Seven.Conservation.septic_ledger

/-! The selected Bernoulli table retains the non-lossy depth identity all
the way through the legacy cube-free compatibility theorem. -/

#guard_depends_on
  Fermat.Conservation.Credit.RealFlow.BernoulliChannelCertificate.accountedChannelTransfer,
  Fermat.Conservation.Credit.Flow.GeneratorOrbit.accountFlow
#guard_depends_on
  Fermat.Conservation.Credit.RealFlow.BernoulliChannelCertificate.accountedChannelTransfer,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Conservation.Credit.RealFlow.BernoulliChannelCertificate.accountedChannel_credit_decomposition,
  Fermat.Conservation.Transfer.available_eq
#guard_depends_on
  Fermat.Conservation.Credit.RealFlow.BernoulliChannelCertificate.accountedChannel_flow_stock,
  Fermat.Conservation.Credit.Flow.GeneratorOrbit.accountFlow
#guard_depends_on
  Fermat.FiftyNine.Conservation.Instance.BernoulliCertificate.accountedFlowTransfer,
  Fermat.Conservation.Credit.Flow.GeneratorOrbit.accountFlow
#guard_depends_on
  Fermat.FiftyNine.Conservation.Instance.BernoulliCertificate.accountedFlow_stock,
  Fermat.Conservation.Credit.Flow.GeneratorOrbit.accountFlow
#guard_depends_on
  Fermat.FiftyNine.Conservation.Instance.BernoulliCertificate.accountedFlow_credit_decomposition,
  Fermat.Conservation.Transfer.available_eq
#guard_depends_on
  Fermat.FiftyNine.Conservation.Instance.BernoulliCertificate.channelCertificate_surplus_eq_zero,
  Fermat.FiftyNine.Conservation.Instance.BernoulliCertificate.accountedFlowTransfer
#guard_depends_on
  Fermat.FiftyNine.Conservation.Instance.BernoulliCertificate.highBernoulliNumerator_cubeFree,
  Fermat.FiftyNine.Conservation.Instance.BernoulliCertificate.accountedFlowTransfer

#guard_depends_on
  Fermat.FiftyNine.Conservation.Instance.BernoulliCertificate.highBernoulliNumerator_cubeFree,
  Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.depth_conservation
#guard_depends_on
  Fermat.FiftyNine.Conservation.Instance.BernoulliCertificate.highBernoulliNumerator_cubeFree,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.FiftyNine.Conservation.Instance.noBernoulliCubeObstruction59,
  Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.depth_conservation
#guard_depends_on
  Fermat.FiftyNine.Conservation.Instance.noBernoulliCubeObstruction59,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.FiftyNine.Conservation.Instance.noBernoulliCubeObstruction59,
  Fermat.Conservation.Credit.Flow.GeneratorOrbit.accountFlow
#guard_depends_on
  Fermat.FiftyNine.Conservation.Instance.deepExponentForcing_of_flow,
  Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.depth_conservation
#guard_depends_on
  Fermat.FiftyNine.Conservation.Instance.deepExponentForcing_of_flow,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.FiftyNine.Conservation.Instance.deepExponentForcing_of_flow,
  Fermat.Conservation.Credit.Flow.GeneratorOrbit.accountFlow
#guard_depends_on
  Fermat.FiftyNine.Conservation.Instance.deepExponentForcing_on_exponentCycle_of_flow,
  Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.depth_conservation
#guard_depends_on
  Fermat.FiftyNine.Conservation.Instance.deepExponentForcing_on_exponentCycle_of_flow,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.FiftyNine.Conservation.Instance.deepExponentForcing_on_exponentCycle_of_flow,
  Fermat.Conservation.Credit.Flow.GeneratorOrbit.accountFlow

/-! The unique square-depth row is the natural-coordinate projection of the
selected funded grade-one repayment transaction. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.DepthCertificate.highEigenvalue_square_attained,
  Fermat.FiftyNine.Conservation.Instance.BernoulliCertificate.accountedFlowTransfer
#guard_depends_on
  Fermat.FiftyNine.Conservation.DepthCertificate.fundedRow_accountedFlow_spends_one,
  Fermat.FiftyNine.Conservation.Instance.BernoulliCertificate.accountedFlowTransfer
#guard_depends_on
  Fermat.FiftyNine.Conservation.DepthCertificate.depthTwoCertificate,
  Fermat.FiftyNine.Conservation.Instance.BernoulliCertificate.accountedFlowTransfer
#guard_depends_on
  Fermat.FiftyNine.Conservation.DepthCertificate.fundedRow_maps_to_repayLayer,
  Fermat.FiftyNine.Conservation.Instance.BernoulliCertificate.accountedFlowTransfer
#guard_depends_on
  Fermat.FiftyNine.Conservation.DepthCertificate.fundedRow_maps_to_repayLayer,
  Fermat.Conservation.Credit.Repayment.repay_layer_transfer
#guard_depends_on
  Fermat.FiftyNine.Conservation.DepthCertificate.fundedRow_maps_to_repayLayer,
  Fermat.Conservation.Ledger.conservation_identity

/-! The selected `d = 1` equivalence and its legacy repayment corollary
retain the named one-layer conservation identity transitively. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.Instance.nonempty_repayOne_iff_deep_repayment59,
  Fermat.Conservation.Credit.Repayment.repay_layer_conservation
#guard_depends_on
  Fermat.FiftyNine.Conservation.Instance.nonempty_repayOne_iff_deep_repayment59,
  Fermat.Conservation.Credit.Repayment.repay_layer_transfer
#guard_depends_on
  Fermat.FiftyNine.Conservation.Instance.repayment_of_capacity_and_flow,
  Fermat.Conservation.Credit.Repayment.repay_layer_conservation
#guard_depends_on
  Fermat.FiftyNine.Conservation.Instance.repayment_of_capacity_and_flow,
  Fermat.Conservation.Credit.Repayment.repay_layer_transfer

/-! The selected grade-zero state is literally funded by both halves named
in its definition: the stock receipt and a generated C1 vacuum. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.Instance.regularClosure59,
  Fermat.FiftyNine.Conservation.stockSpineReceipt
#guard_depends_on
  Fermat.FiftyNine.Conservation.Instance.regularClosure59,
  Fermat.Conservation.Credit.kummer_credit_vacuum
#guard_depends_on
  Fermat.FiftyNine.Conservation.Instance.regularClosure59,
  Fermat.Conservation.Ledger.conservation_identity

/-! The mixed stock receipt remains heterogeneous, but each selected field is
now routed through its own literal account. -/

#guard_depends_on Fermat.One.coupling_empty,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on Fermat.One.charge_ledger,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on Fermat.One.solvable,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on Fermat.One.always_balances,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on Fermat.One.not_holdsAt_one,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on Fermat.FiftyNine.Conservation.stockSpineReceipt,
  Fermat.One.coupling_empty
#guard_depends_on Fermat.FiftyNine.Conservation.stockSpineReceipt,
  Fermat.Conservation.Ledger.conservation_identity

#guard_depends_on Fermat.FiftyNine.Conservation.stockSpineReceipt,
  Fermat.Two.charge_ledger
#guard_depends_on Fermat.Two.charge_ledger,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on Fermat.FiftyNine.Conservation.stockSpineReceipt,
  Fermat.Four.Conservation.PrimitiveSolution.stateCharge_pos
#guard_depends_on Fermat.FiftyNine.Conservation.stockSpineReceipt,
  Fermat.Six.Conservation.sixth_ledger
#guard_depends_on Fermat.FiftyNine.Conservation.stockSpineReceipt,
  Fermat.Seven.Conservation.gauge_decomposition
#guard_depends_on Fermat.Seven.Conservation.gauge_decomposition,
  Fermat.Conservation.Ledger.conservation_identity

/-! N2's Pythagorean balance theorems now reach the global ledger through
the source-inverted public expansion. -/

#guard_depends_on Fermat.Two.pythagoras,
  Fermat.Two.charge_ledger
#guard_depends_on Fermat.Two.pythagoras,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on Fermat.Two.emptyCoupling_of_additive,
  Fermat.Two.charge_ledger
#guard_depends_on Fermat.Two.emptyCoupling_of_additive,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on Fermat.Two.pythagoras_conserved,
  Fermat.Two.charge_ledger
#guard_depends_on Fermat.Two.pythagoras_conserved,
  Fermat.Conservation.Ledger.conservation_identity

/-! The selected N4 positivity receipt is now the positive-transaction
projection used by the complete descent cone. -/

#guard_depends_on
  Fermat.Four.Conservation.PrimitiveSolution.stateCharge_pos,
  Fermat.Conservation.Transfer.available_lt_of_spent_pos
#guard_depends_on Fermat.FiftyNine.Conservation.stockSpineReceipt,
  Fermat.Conservation.Transfer.available_lt_of_spent_pos

/-! The scalar Noether invariant is now the total-column projection of a
zero-spent global transfer.  The transfer itself consumes all four named
column-functoriality laws and both endpoint conservation identities. -/

#guard_depends_on Fermat.Two.isometryTransfer,
  Fermat.Two.chargeLedger_stock_isometry
#guard_depends_on Fermat.Two.isometryTransfer,
  Fermat.Two.chargeLedger_credit_isometry
#guard_depends_on Fermat.Two.isometryTransfer,
  Fermat.Two.chargeLedger_converted_isometry
#guard_depends_on Fermat.Two.isometryTransfer,
  Fermat.Two.chargeLedger_total_isometry
#guard_depends_on Fermat.Two.charge_conserved,
  Fermat.Two.isometryTransfer
#guard_depends_on Fermat.Two.charge_conserved,
  Fermat.Conservation.Ledger.conservation_identity

/-! N3's integer spine and generalized Euler successor now expose one
state-linked accounted transaction.  The factor ledger and ramified stock
drop are projections of that transaction; the former strict theorem and its
downstream floor path retain these dependencies transitively. -/

#guard_depends_on Fermat.Three.Conservation.ledger_identity,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on Fermat.Three.Conservation.drainCharge_pred_lt,
  Fermat.Three.Conservation.drainTransfer_stock_decomposition
#guard_depends_on Fermat.Three.Conservation.drainCharge_pred_lt,
  Fermat.Conservation.Transfer.available_eq
#guard_depends_on Fermat.Three.Conservation.drainCharge_pred_lt,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on Fermat.FiftyNine.Conservation.stockSpineReceipt,
  Fermat.Conservation.Transfer.available_eq
#guard_depends_on Fermat.FiftyNine.Conservation.stockSpineReceipt,
  Fermat.Five.Conservation.gaugeTransfer

/-! The selected gauge quotient joins its stock and faithful matrix-credit
projections in the specialized source-to-quotient transaction. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeQuotient.debitLedger_quotient_eq_bot,
  Fermat.Conservation.Credit.GaugeQuotient.PrimeData.quotientLedger_eq_bot
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeQuotient.debitLedger_quotient_eq_bot,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeQuotient.sourceToQuotientTransfer,
  Fermat.Conservation.Credit.GaugeQuotient.PrimeData.sourceToQuotientTransfer
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeQuotient.sourceToQuotient_credit_decomposition,
  Fermat.Conservation.Transfer.available_eq
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeQuotient.sourceToQuotient_charge_eq,
  Fermat.Conservation.Transfer.total_preserved
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeQuotient.quotient_vacuum_and_charge_eq,
  Fermat.FiftyNine.Conservation.GaugeQuotient.debitLedger_quotient_eq_bot
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeQuotient.quotient_vacuum_and_charge_eq,
  Fermat.Conservation.Credit.GaugeQuotient.PrimeData.quotientCharge_quotientState
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeQuotient.quotient_vacuum_and_charge_eq,
  Fermat.FiftyNine.Conservation.GaugeQuotient.sourceToQuotient_charge_eq
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeQuotient.quotient_vacuum_and_charge_eq,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeQuotient.quotient_vacuum_and_charge_eq,
  Fermat.Conservation.Credit.GaugeQuotient.PrimeData.sourceToQuotientTransfer

/-! Relative-norm (7d) and every consumer conditional on supplied (7a) now
project the selected fold/netting transactions.  The new obstruction theorem
checks that a wanted area transfer projects to (7a); no guard asserts a
producer for that still-open statewise premise. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.Fold.vandiverSevenD_of_relativeNormFold,
  Fermat.FiftyNine.Conservation.Fold.vandiverSevenDFoldToVacuumTransfer
#guard_depends_on
  Fermat.FiftyNine.Conservation.Fold.vandiverSevenD_of_conjugationTranspose,
  Fermat.FiftyNine.Conservation.Fold.conjugationFoldToVacuumTransfer
#guard_depends_on
  Fermat.FiftyNine.Conservation.Fold.factorPrincipalizationPermit_of_sevenA_and_conjugationTranspose,
  Fermat.Conservation.Credit.Fold.oddTorsionNettingTransfer
#guard_depends_on
  Fermat.FiftyNine.Conservation.StateFactorConjugation.StateLinkedIdealPair.vandiverSevenD,
  Fermat.FiftyNine.Conservation.StateFactorConjugation.StateLinkedIdealPair.vandiverSevenDFoldToVacuumTransfer
#guard_depends_on
  Fermat.FiftyNine.Conservation.StateFactorConjugation.StateLinkedIdealPair.vandiverSevenA_of_areaTransfer_to_vacuum,
  Fermat.Conservation.AreaTransfer.abelianProjection
#guard_depends_on
  Fermat.FiftyNine.Conservation.StateFactorConjugation.StateLinkedIdealPair.vandiverSevenA_of_areaTransfer_to_vacuum,
  Fermat.Conservation.Transfer.available_eq
#guard_depends_on
  Fermat.FiftyNine.Conservation.StateFactorConjugation.StateLinkedIdealPair.factorPrincipalizationPermit_of_sevenA,
  Fermat.Conservation.Credit.Fold.oddTorsionNettingTransfer

/-! ## Selected common-action carrier, receipts, and localized walls -/

#check Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.classObstruction
#check Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.reflectionFoldTransfer
#check Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.sevenDClassReceipt
#check Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.plusClassCarrierState
#check Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.minusClassCarrierState
#check Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.plusClassCarrierState_receipt
#check Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.minusClassCarrierState_receipt
#check Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.plusClassCarrierState_class
#check Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.minusClassCarrierState_class
#check Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.plusClassCarrierState_source_eq
#check Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.minusClassCarrierState_source_eq
#check Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.sevenDClassReceipt_payload
#check Fermat.FiftyNine.Conservation.CommonActionStage.canonicalClassObstruction
#check Fermat.FiftyNine.Conservation.CommonActionStage.canonicalSevenDClassReceipt
#check Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.differenceGauge_reading
#check Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.differenceGauge_eq_zero_iff_vandiverSevenA
#check Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.CharacterDualAllocationTarget
#check Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.characterDualAllocationWall
#check Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.StrictRouteBoundary
#check Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.StrictRouteBoundary.selmerObstruction
#check Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.strictRouteRhoWall
#check Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.strictRouteRhoWall_target
#check Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.typedLocalizedResult

#guard_depends_on
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.classObstruction,
  Fermat.Conservation.CommonActionStage.allocatedClassObstruction
#guard_depends_on
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.reflectionFoldTransfer,
  Fermat.FiftyNine.Conservation.StateFactorConjugation.StateLinkedIdealPair.vandiverSevenDFoldToVacuumTransfer
#guard_depends_on
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.sevenDClassReceipt,
  Fermat.FiftyNine.Conservation.StateFactorConjugation.StateLinkedIdealPair.vandiverSevenD
#guard_depends_on
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.sevenDClassReceipt,
  Fermat.Conservation.CommonActionStage.allocatedSevenDClassReceipt
#guard_depends_on
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.plusClassCarrierState,
  Fermat.Conservation.CommonActionStage.allocatedSevenDReceiptedRootState
#guard_depends_on
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.minusClassCarrierState,
  Fermat.Conservation.CommonActionStage.allocatedSevenDReceiptedRootState
#guard_depends_on
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.plusClassCarrierState_receipt,
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.plusClassCarrierState
#guard_depends_on
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.minusClassCarrierState_receipt,
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.minusClassCarrierState
#guard_depends_on
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.plusClassCarrierState_class,
  Fermat.Conservation.CommonActionStage.allocatedRootState_class
#guard_depends_on
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.minusClassCarrierState_class,
  Fermat.Conservation.CommonActionStage.allocatedRootState_class
#guard_depends_on
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.plusClassCarrierState_source_eq,
  Fermat.Conservation.CommonActionStage.allocatedRootState_source_eq
#guard_depends_on
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.minusClassCarrierState_source_eq,
  Fermat.Conservation.CommonActionStage.allocatedRootState_source_eq
#guard_depends_on
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.sevenDClassReceipt_payload,
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.sevenDClassReceipt
#guard_depends_on
  Fermat.FiftyNine.Conservation.CommonActionStage.canonicalClassObstruction,
  Fermat.FiftyNine.Conservation.StateFactorPair.allocatedPair
#guard_depends_on
  Fermat.FiftyNine.Conservation.CommonActionStage.canonicalSevenDClassReceipt,
  Fermat.FiftyNine.Conservation.StateFactorPair.allocatedPair
#guard_depends_on
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.differenceGauge_reading,
  Fermat.Conservation.CommonActionStage.differenceGauge
#guard_depends_on
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.differenceGauge_reading,
  Fermat.Conservation.KummerDrain.AllocatedFactorLedger.rootClass_torsion
#guard_depends_on
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.differenceGauge_eq_zero_iff_vandiverSevenA,
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.differenceGauge_reading
#guard_depends_on
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.differenceGauge_eq_zero_iff_vandiverSevenA,
  Fermat.Conservation.KummerDrain.AllocatedFactorLedger.VandiverSevenA
#guard_depends_on
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.CharacterDualAllocationTarget,
  Fermat.Conservation.CommonActionStage.KummerPairedBinding
#guard_depends_on
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.CharacterDualAllocationTarget,
  Fermat.Conservation.CommonActionStage.selmerClassSequenceRealization
#guard_depends_on
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.CharacterDualAllocationTarget,
  Fermat.Conservation.CommonActionStage.CharacterClassAllocation
#guard_depends_on
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.CharacterDualAllocationTarget,
  Fermat.Conservation.CommonActionStage.allocatedRootClassPTorsion
#guard_depends_on
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.characterDualAllocationWall,
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.CharacterDualAllocationTarget
#guard_depends_on
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.StrictRouteBoundary.selmerObstruction,
  Fermat.Conservation.CommonActionStage.allocatedSelmerObstruction
#guard_depends_on
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.strictRouteRhoWall,
  Fermat.Conservation.LinkingInterfaces.ReflectedSelmerArithmeticRepresentationTarget
#guard_depends_on
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.strictRouteRhoWall,
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.StrictRouteBoundary.selmerObstruction
#guard_depends_on
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.strictRouteRhoWall_target,
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.strictRouteRhoWall
#guard_depends_on
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.typedLocalizedResult,
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.characterDualAllocationWall

/-! ## Place-indexed Tate pairing and conditional relation-(7a) bridge -/

/-! W1 exposes local readings with finite support, makes the `#`-adjoint law
proof-relevant, and routes global reciprocity through the existing
`Ledger`/`Transfer`/`IsoConserveBridge` vocabulary. -/

#check Fermat.Conservation.TatePairing.character_mul_reflectedCharacter
#check Fermat.Conservation.TatePairing.PlaceIndexedLocalPairing
#check Fermat.Conservation.TatePairing.PlaceIndexedLocalPairing.pairAt
#check Fermat.Conservation.TatePairing.PlaceIndexedLocalPairing.pairAt_smul_adjoint
#check Fermat.Conservation.TatePairing.PlaceIndexedLocalPairing.pairAt_hash_smul_adjoint
#check Fermat.Conservation.TatePairing.PlaceIndexedLocalPairing.finite_support
#check Fermat.Conservation.TatePairing.PlaceLedger
#check Fermat.Conservation.TatePairing.PlaceLedger.toLedger
#check Fermat.Conservation.TatePairing.PlaceLedger.toVacuumTransfer
#check Fermat.Conservation.TatePairing.PlaceLedger.toVacuumTransfer_L1
#check Fermat.Conservation.TatePairing.GlobalReciprocityLaw
#check Fermat.Conservation.TatePairing.GlobalReciprocityLaw.placeLedger
#check Fermat.Conservation.TatePairing.GlobalReciprocityLaw.ledger_conservation_identity
#check Fermat.Conservation.TatePairing.GlobalReciprocityLaw.reciprocityTransfer
#check Fermat.Conservation.TatePairing.GlobalReciprocityLaw.reciprocity_L1_conservation
#check Fermat.Conservation.TatePairing.GlobalReciprocityLaw.pairAt_eq_zero_of_other_places
#check Fermat.Conservation.TatePairing.LocalOrthogonalityGuard
#check Fermat.Conservation.TatePairing.LocalOrthogonalityGuard.pairAt_eq_zero

#guard_depends_on
  Fermat.Conservation.TatePairing.PlaceIndexedLocalPairing.pairAt_smul_adjoint,
  Fermat.Conservation.TatePairing.PlaceIndexedLocalPairing.adjoint_law
#guard_depends_on
  Fermat.Conservation.TatePairing.PlaceIndexedLocalPairing.pairAt_hash_smul_adjoint,
  Fermat.Conservation.TatePairing.PlaceIndexedLocalPairing.pairAt_smul_adjoint
#guard_depends_on
  Fermat.Conservation.TatePairing.PlaceIndexedLocalPairing.pairAt_hash_smul_adjoint,
  Fermat.Conservation.InvolutiveBase.hash_hash
#guard_depends_on
  Fermat.Conservation.TatePairing.PlaceLedger.toVacuumTransfer,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Conservation.TatePairing.PlaceLedger.toVacuumTransfer_L1,
  Fermat.Conservation.IsoConserveBridge.transfer_L1_conservation
#guard_depends_on
  Fermat.Conservation.TatePairing.GlobalReciprocityLaw.placeLedger,
  Fermat.Conservation.TatePairing.GlobalReciprocityLaw.sum_eq_zero
#guard_depends_on
  Fermat.Conservation.TatePairing.GlobalReciprocityLaw.ledger_conservation_identity,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.Conservation.TatePairing.GlobalReciprocityLaw.reciprocity_L1_conservation,
  Fermat.Conservation.IsoConserveBridge.transfer_L1_conservation
#guard_depends_on
  Fermat.Conservation.TatePairing.GlobalReciprocityLaw.pairAt_eq_zero_of_other_places,
  Fermat.Conservation.TatePairing.GlobalReciprocityLaw.sum_eq_zero
#guard_depends_on
  Fermat.Conservation.TatePairing.LocalOrthogonalityGuard.pairAt_eq_zero,
  Fermat.Conservation.TatePairing.LocalOrthogonalityGuard.orthogonal

/-! The tame layer constructs the complete finite-support pairing from one
wild local interface.  Detector existence and the selected gauge comparison
remain interfaces; the bank audit and every away row are now proved. -/

#check Fermat.FiftyNine.Conservation.TateBridge.LocalPairing
#check Fermat.FiftyNine.Conservation.TateBridge.WildLocalInterface
#check Fermat.FiftyNine.Conservation.TateBridge.H_FLT
#check Fermat.FiftyNine.Conservation.TateBridge.WildDetectorDual
#check Fermat.FiftyNine.Conservation.TateBridge.pair_59
#check Fermat.FiftyNine.Conservation.TateBridge.Lambda
#check Fermat.FiftyNine.Conservation.TateBridge.Lambda_apply
#check Fermat.FiftyNine.Conservation.TateBridge.Lambda_apply_eq_zero_of_reciprocity
#check Fermat.FiftyNine.Conservation.TateBridge.wild_detector_faithful
#check Fermat.FiftyNine.Conservation.TateBridge.eq_zero_of_wild_detector_faithful
#check Fermat.FiftyNine.Conservation.TateBridge.potential_eq_zero_of_stokes_and_faithful
#check Fermat.FiftyNine.Conservation.TateBridge.wild_detector_faithful_of_finrank_one
#check Fermat.FiftyNine.Conservation.TateBridge.SelectedLampAction
#check Fermat.FiftyNine.Conservation.TateBridge.SelectedLampAction.toLampTransverse
#check Fermat.FiftyNine.Conservation.TateBridge.TransverseDetector
#check Fermat.FiftyNine.Conservation.TateBridge.TransverseDetector.lamp
#check Fermat.FiftyNine.Conservation.TateBridge.TransverseDetector.lamp_annihilates_detector
#check Fermat.FiftyNine.Conservation.TateBridge.TransverseDetector.outside_reading_eq_zero
#check Fermat.FiftyNine.Conservation.TateBridge.transverse_detector_exists
#check Fermat.FiftyNine.Conservation.TateBridge.chosenTransverseDetector
#check Fermat.FiftyNine.Conservation.TateBridge.GaugeComparison
#check Fermat.FiftyNine.Conservation.TateBridge.GaugeComparison.scalarGauge_eq_zero_of_local_reading_eq_zero
#check Fermat.FiftyNine.Conservation.TateBridge.GaugeComparison.gauge_eq_zero_of_local_reading_eq_zero
#check Fermat.FiftyNine.Conservation.TateBridge.gauge_eq_local_tate_pairing
#check Fermat.FiftyNine.Conservation.TateBridge.N59BankReceipts
#check Fermat.FiftyNine.Conservation.TateBridge.n59BankReceipts
#check Fermat.FiftyNine.Conservation.TateBridge.BankSilenceAudit
#check Fermat.FiftyNine.Conservation.TateBridge.BankSilenceAudit.auxiliary_reading_eq_zero
#check Fermat.FiftyNine.Conservation.TateBridge.BankSilenceAudit.other_reading_eq_zero
#check Fermat.FiftyNine.Conservation.TateBridge.BankSilenceAudit.away_reading_eq_zero
#check Fermat.FiftyNine.Conservation.TateBridge.bank_silences_other_places

#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.pair_59,
  Fermat.Conservation.TamePlacePairing.WildLocalInterface.reading
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.Lambda,
  Fermat.FiftyNine.Conservation.TateBridge.pair_59
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.Lambda_apply,
  Fermat.Conservation.TamePlacePairing.WildLocalInterface.pairAt_distinguished
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.Lambda_apply_eq_zero_of_reciprocity,
  Fermat.Conservation.TatePairing.GlobalReciprocityLaw.pairAt_eq_zero_of_other_places
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.Lambda_apply_eq_zero_of_reciprocity,
  Fermat.Conservation.TamePlacePairing.WildLocalInterface.pairAt_eq_zero_of_ne
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.wild_detector_faithful,
  Fermat.FiftyNine.Conservation.TateBridge.Lambda
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.eq_zero_of_wild_detector_faithful,
  Fermat.FiftyNine.Conservation.TateBridge.wild_detector_faithful
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.potential_eq_zero_of_stokes_and_faithful,
  Fermat.FiftyNine.Conservation.TateBridge.Lambda_apply_eq_zero_of_reciprocity
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.potential_eq_zero_of_stokes_and_faithful,
  Fermat.FiftyNine.Conservation.TateBridge.eq_zero_of_wild_detector_faithful
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.wild_detector_faithful_of_finrank_one,
  exists_smul_eq_of_finrank_eq_one
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.SelectedLampAction.toLampTransverse,
  Fermat.FiftyNine.Conservation.Credit.attestationPrime_isPrime
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.TransverseDetector.lamp,
  Fermat.FiftyNine.Conservation.TateBridge.SelectedLampAction.toLampTransverse
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.TransverseDetector.lamp_annihilates_detector,
  Fermat.FiftyNine.Conservation.TateBridge.TransverseDetector.lamp_realizes_detector
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.TransverseDetector.lamp_annihilates_detector,
  Fermat.FiftyNine.Conservation.TateBridge.SelectedLampAction.annihilates
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.TransverseDetector.outside_reading_eq_zero,
  Fermat.Conservation.TamePlacePairing.WildLocalInterface.pairAt_eq_zero_of_ne
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.gauge_eq_local_tate_pairing,
  Fermat.FiftyNine.Conservation.TateBridge.chosenTransverseDetector
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.bank_silences_other_places,
  Fermat.FiftyNine.Conservation.TateBridge.chosenTransverseDetector
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.bank_silences_other_places,
  Fermat.FiftyNine.Conservation.TateBridge.n59BankReceipts
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.chosenTransverseDetector,
  Classical.choice
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.GaugeComparison.scalarGauge_eq_zero_of_local_reading_eq_zero,
  Fermat.FiftyNine.Conservation.TateBridge.GaugeComparison.pairing_eq_gauge
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.GaugeComparison.gauge_eq_zero_of_local_reading_eq_zero,
  Fermat.FiftyNine.Conservation.TateBridge.GaugeComparison.reflects_selected_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.GaugeComparison.gauge_eq_zero_of_local_reading_eq_zero,
  Fermat.FiftyNine.Conservation.TateBridge.GaugeComparison.scalarGauge_eq_zero_of_local_reading_eq_zero

#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.n59BankReceipts,
  Fermat.FiftyNine.Conservation.CapacityCertificate.capacityCertificate
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.n59BankReceipts,
  Fermat.FiftyNine.Conservation.Credit.boundedSinnottBridge
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.n59BankReceipts,
  Fermat.FiftyNine.Conservation.Fold.not_dvd_plusClassNumber
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.n59BankReceipts,
  Fermat.FiftyNine.Conservation.Instance.deepFlowLaw59
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.n59BankReceipts,
  Fermat.FiftyNine.Conservation.Instance.repayment_of_capacity_and_flow
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.n59BankReceipts,
  Fermat.FiftyNine.Conservation.StateFactorConjugation.StateLinkedIdealPair.vandiverSevenD
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.BankSilenceAudit.auxiliary_reading_eq_zero,
  Fermat.Conservation.TamePlacePairing.WildLocalInterface.pairAt_eq_zero_of_ne
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.BankSilenceAudit.other_reading_eq_zero,
  Fermat.Conservation.TamePlacePairing.WildLocalInterface.pairAt_eq_zero_of_ne
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.BankSilenceAudit.away_reading_eq_zero,
  Fermat.Conservation.TamePlacePairing.WildLocalInterface.pairAt_eq_zero_of_ne

/-! The nominated 827 lamp has a checked nonzero finite readout.  The old
empty-support no-go remains audited as a regression, while the repaired
surface now exposes Mathlib's literal q-relaxed carrier, its genuine
character projector, the capacity-functional comparison, and the exact
localization-lift interface still awaiting an arithmetic inhabitant. -/

#check Fermat.FiftyNine.Conservation.DetectorWitness827.firstLedgerNode
#check Fermat.FiftyNine.Conservation.DetectorWitness827.firstLampReading827
#check Fermat.FiftyNine.Conservation.DetectorWitness827.firstLampReading827_eq
#check Fermat.FiftyNine.Conservation.DetectorWitness827.firstLampReading827_ne_zero
#check Fermat.FiftyNine.Conservation.DetectorWitness827.firstEdgeResidue827_eq
#check Fermat.FiftyNine.Conservation.DetectorWitness827.firstEdgeSymbol827_eq
#check Fermat.FiftyNine.Conservation.DetectorWitness827.firstEdgeSymbol827_eq_root_pow_reading
#check Fermat.FiftyNine.Conservation.CapacityCertificate.reductionHom_generatedUnit_eq_edgeResidue
#check Fermat.FiftyNine.Conservation.CapacityCertificate.residueFunctional_generatedUnit_eq
#check Fermat.FiftyNine.Conservation.DetectorWitness827.placesOver827
#check Fermat.FiftyNine.Conservation.DetectorWitness827.placesOver59
#check Fermat.FiftyNine.Conservation.DetectorWitness827.mem_placesOver827_iff
#check Fermat.FiftyNine.Conservation.DetectorWitness827.placesOver827_finite
#check Fermat.FiftyNine.Conservation.DetectorWitness827.detectorSupport827
#check Fermat.FiftyNine.Conservation.DetectorWitness827.QRelaxedSelmerCarrier827
#check Fermat.FiftyNine.Conservation.DetectorWitness827.QRelaxedSClassTarget827
#check Fermat.FiftyNine.Conservation.DetectorWitness827.exists_qRelaxedSource_of_sClass_torsion
#check Fermat.FiftyNine.Conservation.DetectorWitness827.qRelaxedSourceOfSClassTorsion827
#check Fermat.FiftyNine.Conservation.DetectorWitness827.toSClass_qRelaxedSourceOfSClassTorsion827
#check Fermat.FiftyNine.Conservation.DetectorWitness827.QRelaxedSelmerDeltaRepresentation827
#check Fermat.FiftyNine.Conservation.DetectorWitness827.QRelaxedReflectedDual827
#check Fermat.FiftyNine.Conservation.DetectorWitness827.firstResidueFunctional827
#check Fermat.FiftyNine.Conservation.DetectorWitness827.firstResidueFunctional827_generatedUnit
#check Fermat.FiftyNine.Conservation.DetectorWitness827.qRelaxedReflectedProjector827
#check Fermat.FiftyNine.Conservation.DetectorWitness827.qLocalizationCoordinate827
#check Fermat.FiftyNine.Conservation.DetectorWitness827.firstLampScale827
#check Fermat.FiftyNine.Conservation.DetectorWitness827.localizationResidueReadout827
#check Fermat.FiftyNine.Conservation.DetectorWitness827.localizationResidueReadout827_apply
#check Fermat.FiftyNine.Conservation.DetectorWitness827.localizationResidueReadout827_eq_mul_residueFunctional
#check Fermat.FiftyNine.Conservation.DetectorWitness827.localizationResidueReadout827_ne_zero
#check Fermat.FiftyNine.Conservation.DetectorWitness827.projectedCandidateAtDetectorSupport827
#check Fermat.FiftyNine.Conservation.DetectorWitness827.projectedCandidateSClassObstruction827
#check Fermat.FiftyNine.Conservation.DetectorWitness827.projectedCandidateSClassObstruction827_pow_eq_one
#check Fermat.FiftyNine.Conservation.DetectorWitness827.ReflectedQRelaxedLocalizationLift827
#check Fermat.FiftyNine.Conservation.DetectorWitness827.ReflectedQRelaxedLocalizationLift827.ofSource_of_sClassObstruction_eq_one
#check Fermat.FiftyNine.Conservation.DetectorWitness827.ReflectedQRelaxedLocalizationLift827.ofSClassTorsion_of_projected_obstruction_eq_one
#check Fermat.FiftyNine.Conservation.DetectorWitness827.ReflectedQRelaxedLocalizationLift827.candidate
#check Fermat.FiftyNine.Conservation.DetectorWitness827.ReflectedQRelaxedLocalizationLift827.candidate_eigenlaw
#check Fermat.FiftyNine.Conservation.DetectorWitness827.ReflectedQRelaxedLocalizationLift827.computedQReading
#check Fermat.FiftyNine.Conservation.DetectorWitness827.ReflectedQRelaxedLocalizationLift827.computedQReading_ne_zero
#check Fermat.FiftyNine.Conservation.DetectorWitness827.ReflectedQRelaxedLocalizationLift827.primalRepresentative
#check Fermat.FiftyNine.Conservation.DetectorWitness827.ReflectedQRelaxedLocalizationLift827.outside_reading_eq_zero_of_both_units
#check Fermat.FiftyNine.Conservation.DetectorWitness827.ReflectedQRelaxedLocalizationLift827.SelectedTameComparison
#check Fermat.FiftyNine.Conservation.DetectorWitness827.ReflectedQRelaxedLocalizationLift827.selected_tame_reading_ne_zero
#check Fermat.FiftyNine.Conservation.DetectorWitness827.TransverseDetectorWitness
#check Fermat.FiftyNine.Conservation.DetectorWitness827.TransverseDetectorWitness.outside_tame_reading_eq_zero
#check Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.Place
#check Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.Primal
#check Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.ReflectedDual
#check Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.Pairing
#check Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.EmptySupportTransverseDetectorWitness
#check Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.EmptySupportTransverseDetectorWitness.candidate_eigenlaw
#check Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.EmptySupportTransverseDetectorWitness.candidate_valuation_dvd
#check Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.EmptySupportTransverseDetectorWitness.reading_eq_zero_at_every_tame_auxiliary
#check Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.EmptySupportTransverseDetectorWitness.auxiliaryReading_eq_zero
#check Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.EmptySupportTransverseDetectorWitness.not_nonempty
#check Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.firstLampReading827_not_realized_by_seated_pairing

#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.firstLampReading827_eq,
  Fermat.FiftyNine.Conservation.DetectorWitness827.firstLampReading827
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.firstLampReading827_ne_zero,
  Fermat.FiftyNine.Conservation.DetectorWitness827.firstLampReading827_eq
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.firstEdgeResidue827_eq,
  Fermat.FiftyNine.Conservation.CapacityCertificate.edgeResidue
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.firstEdgeSymbol827_eq,
  Fermat.FiftyNine.Conservation.CapacityCertificate.edgeResidue
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.firstEdgeSymbol827_eq_root_pow_reading,
  Fermat.FiftyNine.Conservation.DetectorWitness827.firstLampReading827
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.placesOver827_finite,
  IsDedekindDomain.primesOver_finite
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.detectorSupport827,
  Fermat.FiftyNine.Conservation.DetectorWitness827.placesOver59
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.detectorSupport827,
  Fermat.FiftyNine.Conservation.DetectorWitness827.placesOver827
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.QRelaxedSClassTarget827,
  IsDedekindDomain.selmerGroup.obstructionTarget
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.exists_qRelaxedSource_of_sClass_torsion,
  IsDedekindDomain.selmerGroup.toSClass_range
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.qRelaxedSourceOfSClassTorsion827,
  Fermat.FiftyNine.Conservation.DetectorWitness827.exists_qRelaxedSource_of_sClass_torsion
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.toSClass_qRelaxedSourceOfSClassTorsion827,
  Fermat.FiftyNine.Conservation.DetectorWitness827.exists_qRelaxedSource_of_sClass_torsion
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.firstResidueFunctional827_generatedUnit,
  Fermat.FiftyNine.Conservation.CapacityCertificate.residueFunctional_generatedUnit_eq
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.qRelaxedReflectedProjector827,
  Fermat.Conservation.SelmerEigenspace.characterProjectorAt
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.qLocalizationCoordinate827,
  Fermat.Conservation.SelmerEigenspace.eigenspaceSupportValuationAt
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.localizationResidueReadout827_apply,
  Fermat.FiftyNine.Conservation.DetectorWitness827.localizationResidueReadout827
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.localizationResidueReadout827_eq_mul_residueFunctional,
  Fermat.FiftyNine.Conservation.DetectorWitness827.firstResidueFunctional827_generatedUnit
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.localizationResidueReadout827_ne_zero,
  Fermat.FiftyNine.Conservation.DetectorWitness827.firstLampReading827_ne_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.projectedCandidateAtDetectorSupport827,
  Fermat.FiftyNine.Conservation.DetectorWitness827.qRelaxedReflectedProjector827
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.projectedCandidateAtDetectorSupport827,
  IsDedekindDomain.selmerGroup.monotone
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.projectedCandidateSClassObstruction827,
  IsDedekindDomain.selmerGroup.toSClass
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.projectedCandidateSClassObstruction827_pow_eq_one,
  IsDedekindDomain.selmerGroup.toSClass_range
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.ReflectedQRelaxedLocalizationLift827.ofSource_of_sClassObstruction_eq_one,
  IsDedekindDomain.selmerGroup.toSClass_ker
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.ReflectedQRelaxedLocalizationLift827.ofSource_of_sClassObstruction_eq_one,
  IsDedekindDomain.selmerGroup.fromSUnitLift
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.ReflectedQRelaxedLocalizationLift827.ofSource_of_sClassObstruction_eq_one,
  Set.unit_valuation_eq_one
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.ReflectedQRelaxedLocalizationLift827.ofSClassTorsion_of_projected_obstruction_eq_one,
  Fermat.FiftyNine.Conservation.DetectorWitness827.qRelaxedSourceOfSClassTorsion827
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.ReflectedQRelaxedLocalizationLift827.ofSClassTorsion_of_projected_obstruction_eq_one,
  Fermat.FiftyNine.Conservation.DetectorWitness827.ReflectedQRelaxedLocalizationLift827.ofSource_of_sClassObstruction_eq_one
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.ReflectedQRelaxedLocalizationLift827.candidate,
  Fermat.FiftyNine.Conservation.DetectorWitness827.qRelaxedReflectedProjector827
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.ReflectedQRelaxedLocalizationLift827.candidate_eigenlaw,
  Fermat.Conservation.SelmerEigenspace.mem_characterEigenspaceAt_iff
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.ReflectedQRelaxedLocalizationLift827.computedQReading,
  Fermat.FiftyNine.Conservation.DetectorWitness827.localizationResidueReadout827
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.ReflectedQRelaxedLocalizationLift827.computedQReading_ne_zero,
  Fermat.FiftyNine.Conservation.DetectorWitness827.localizationResidueReadout827_ne_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.ReflectedQRelaxedLocalizationLift827.outside_reading_eq_zero_of_both_units,
  Fermat.Conservation.TameSymbol.Context.both_units_silence
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.ReflectedQRelaxedLocalizationLift827.selected_tame_reading_ne_zero,
  Fermat.FiftyNine.Conservation.DetectorWitness827.ReflectedQRelaxedLocalizationLift827.computedQReading_ne_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.TransverseDetectorWitness.outside_tame_reading_eq_zero,
  Fermat.Conservation.TameSymbol.Context.both_units_silence
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.EmptySupportTransverseDetectorWitness.candidate_eigenlaw,
  Fermat.Conservation.SelmerEigenspace.mem_characterEigenspace_iff
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.EmptySupportTransverseDetectorWitness.candidate_valuation_dvd,
  Fermat.Conservation.SelmerEigenspace.quotientRepresentative_valuation_dvd
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.EmptySupportTransverseDetectorWitness.reading_eq_zero_at_every_tame_auxiliary,
  Fermat.Conservation.TamePlacePairing.Seated.Realization.pairAt_eq_zero_at_tame_place
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.EmptySupportTransverseDetectorWitness.auxiliaryReading_eq_zero,
  Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.EmptySupportTransverseDetectorWitness.reading_eq_zero_at_every_tame_auxiliary
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.EmptySupportTransverseDetectorWitness.not_nonempty,
  Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.EmptySupportTransverseDetectorWitness.auxiliaryReading_eq_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.firstLampReading827_not_realized_by_seated_pairing,
  Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.EmptySupportTransverseDetectorWitness.reading_eq_zero_at_every_tame_auxiliary
#guard_depends_on
  Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.firstLampReading827_not_realized_by_seated_pairing,
  Fermat.FiftyNine.Conservation.DetectorWitness827.firstLampReading827_ne_zero

/-! The FOCUS invariant is instantiated on the post-projector finite-`S`
class fiber.  Its selected outcome is a typed missing kernel computation,
not an invented fixed or transverse receipt. -/

#check Fermat.FiftyNine.Conservation.GaugeSteering827.projectedClassObstructionAddHom827
#check Fermat.FiftyNine.Conservation.GaugeSteering827.ProjectedClassRange827
#check Fermat.FiftyNine.Conservation.GaugeSteering827.projectedClassRange827_nsmul_eq_zero
#check Fermat.FiftyNine.Conservation.GaugeSteering827.relaxedClassProjection827
#check Fermat.FiftyNine.Conservation.GaugeSteering827.NonpointedPlace827
#check Fermat.FiftyNine.Conservation.GaugeSteering827.NonpointedReadings827
#check Fermat.FiftyNine.Conservation.GaugeSteering827.pointedCoordinate827
#check Fermat.FiftyNine.Conservation.GaugeSteering827.tameSilence827
#check Fermat.FiftyNine.Conservation.GaugeSteering827.gaugeReading827
#check Fermat.FiftyNine.Conservation.GaugeSteering827.gaugeReading827_ne_zero_iff
#check Fermat.FiftyNine.Conservation.GaugeSteering827.relaxedClassProjection827_eq_zero_iff
#check Fermat.FiftyNine.Conservation.GaugeSteering827.tameSilence827_eq_zero_iff
#check Fermat.FiftyNine.Conservation.GaugeSteering827.PointedConormalCokernel827
#check Fermat.FiftyNine.Conservation.GaugeSteering827.pointedConormalClass827
#check Fermat.FiftyNine.Conservation.GaugeSteering827.pointedConormalRestriction827
#check Fermat.FiftyNine.Conservation.GaugeSteering827.pointedConormalClass827_eq_zero_iff_fixed
#check Fermat.FiftyNine.Conservation.GaugeSteering827.pointedConormalClass827_ne_zero_iff_transverse
#check Fermat.FiftyNine.Conservation.GaugeSteering827.transverseDirection_iff_exists_pointedKernel
#check Fermat.FiftyNine.Conservation.GaugeSteering827.pointedKernel_logical_dichotomy
#check Fermat.FiftyNine.Conservation.GaugeSteering827.zeroCompatibleLift827
#check Fermat.FiftyNine.Conservation.GaugeSteering827.focusedUnitLift827
#check Fermat.FiftyNine.Conservation.GaugeSteering827.localizationLiftOfTransverse827
#check Fermat.FiftyNine.Conservation.GaugeSteering827.SteerableGaugeReceipt827
#check Fermat.FiftyNine.Conservation.GaugeSteering827.steerableGaugeReceipt827
#check Fermat.FiftyNine.Conservation.GaugeSteering827.fixedPointedClassReadout827
#check Fermat.FiftyNine.Conservation.GaugeSteering827.fixedPointedReadout_pullback
#check Fermat.FiftyNine.Conservation.GaugeSteering827.fixedGauge_preimage_independent
#check Fermat.FiftyNine.Conservation.GaugeSteering827.KernelComputationKind
#check Fermat.FiftyNine.Conservation.GaugeSteering827.hasKernelComputation
#check Fermat.FiftyNine.Conservation.GaugeSteering827.Pointed827BranchStatus
#check Fermat.FiftyNine.Conservation.GaugeSteering827.currentKernelInventory
#check Fermat.FiftyNine.Conservation.GaugeSteering827.kernelInventoryComplete
#check Fermat.FiftyNine.Conservation.GaugeSteering827.current_kernelInventory_incomplete
#check Fermat.FiftyNine.Conservation.GaugeSteering827.current_branchStatus_eq_undecidable

#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeSteering827.projectedClassObstructionAddHom827,
  Fermat.FiftyNine.Conservation.DetectorWitness827.projectedCandidateSClassObstruction827
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeSteering827.relaxedClassProjection827,
  AddMonoidHom.rangeRestrict
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeSteering827.pointedCoordinate827,
  Fermat.FiftyNine.Conservation.DetectorWitness827.qLocalizationCoordinate827
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeSteering827.gaugeReading827,
  Fermat.FiftyNine.Conservation.DetectorWitness827.firstLampScale827
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeSteering827.pointedConormalClass827,
  Fermat.Conservation.SteeringFiber.focusConormalClass
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeSteering827.pointedConormalClass827_eq_zero_iff_fixed,
  Fermat.Conservation.SteeringFiber.focusConormalClass_eq_zero_iff_fixed
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeSteering827.pointedConormalClass827_ne_zero_iff_transverse,
  Fermat.Conservation.SteeringFiber.focusConormalClass_ne_zero_iff_transverse
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeSteering827.transverseDirection_iff_exists_pointedKernel,
  Fermat.FiftyNine.Conservation.GaugeSteering827.relaxedClassProjection827_eq_zero_iff
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeSteering827.transverseDirection_iff_exists_pointedKernel,
  Fermat.FiftyNine.Conservation.GaugeSteering827.tameSilence827_eq_zero_iff
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeSteering827.focusedUnitLift827,
  Fermat.Conservation.SteeringFiber.focusedLift
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeSteering827.localizationLiftOfTransverse827,
  Fermat.FiftyNine.Conservation.DetectorWitness827.ReflectedQRelaxedLocalizationLift827.ofSource_of_sClassObstruction_eq_one
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeSteering827.steerableGaugeReceipt827,
  Fermat.FiftyNine.Conservation.GaugeSteering827.localizationLiftOfTransverse827
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeSteering827.fixedPointedReadout_pullback,
  Fermat.Conservation.SteeringFiber.rhoDual_pullback_of_silence

/-! The TRANSVERSALITY W1 audit proves that the 827 places are one regular
58-element orbit and checks the complete position/character Fourier
dictionary.  The final `FIXED` implication is intentionally conditional on
the named action/localization seating law: the abstract supplied
representation does not currently produce an inhabitant. -/

#check Fermat.FiftyNine.Conservation.SplitPrimeFourier827.attestationPrime_mod_fiftyNine
#check Fermat.FiftyNine.Conservation.SplitPrimeFourier827.primesOver827_ncard_eq_fiftyEight
#check Fermat.FiftyNine.Conservation.SplitPrimeFourier827.placesOver827_ncard_eq_fiftyEight
#check Fermat.FiftyNine.Conservation.SplitPrimeFourier827.placeOrbitEquiv827
#check Fermat.FiftyNine.Conservation.SplitPrimeFourier827.indexedPlaceOrbitEquiv827
#check Fermat.FiftyNine.Conservation.SplitPrimeFourier827.characterBasis
#check Fermat.FiftyNine.Conservation.SplitPrimeFourier827.characterBasis_fourier_sum
#check Fermat.FiftyNine.Conservation.SplitPrimeFourier827.fourierCoefficient_positionBasis
#check Fermat.FiftyNine.Conservation.SplitPrimeFourier827.fourierCoefficient_positionBasis_ne_zero
#check Fermat.FiftyNine.Conservation.SplitPrimeFourier827.pureCharacter_support_eq_univ
#check Fermat.FiftyNine.Conservation.SplitPrimeFourier827.pureCharacter_not_support_singleton
#check Fermat.FiftyNine.Conservation.SplitPrimeFourier827.pureCharacter_pointed_silence
#check Fermat.FiftyNine.Conservation.SplitPrimeFourier827.QLocalizationEquivariance827
#check Fermat.FiftyNine.Conservation.SplitPrimeFourier827.projectedLocalization_isPureCharacter
#check Fermat.FiftyNine.Conservation.SplitPrimeFourier827.pointedCoordinate827_eq_selectedCharacterComponent
#check Fermat.FiftyNine.Conservation.SplitPrimeFourier827.fixedAttention_of_fourierSeating
#check Fermat.FiftyNine.Conservation.SplitPrimeFourier827.no_transverseDirection_of_fourierSeating

#guard_depends_on
  Fermat.FiftyNine.Conservation.SplitPrimeFourier827.primesOver827_ncard_eq_fiftyEight,
  Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
#guard_depends_on
  Fermat.FiftyNine.Conservation.SplitPrimeFourier827.placeOrbitEquiv827,
  Fermat.FiftyNine.Conservation.SplitPrimeFourier827.galEquivPrimesOver827
#guard_depends_on
  Fermat.FiftyNine.Conservation.SplitPrimeFourier827.characterBasis_fourier_sum,
  Fermat.FiftyNine.Conservation.SplitPrimeFourier827.fourier_reconstruction
#guard_depends_on
  Fermat.FiftyNine.Conservation.SplitPrimeFourier827.fourierCoefficient_positionBasis_ne_zero,
  Fermat.FiftyNine.Conservation.SplitPrimeFourier827.fourierCoefficient_positionBasis
#guard_depends_on
  Fermat.FiftyNine.Conservation.SplitPrimeFourier827.fixedAttention_of_fourierSeating,
  Fermat.FiftyNine.Conservation.SplitPrimeFourier827.pureCharacter_pointed_silence
#guard_depends_on
  Fermat.FiftyNine.Conservation.SplitPrimeFourier827.no_transverseDirection_of_fourierSeating,
  Fermat.FiftyNine.Conservation.SplitPrimeFourier827.fixedAttention_of_fourierSeating

/-! TRANSVERSALITY W3 keeps the strict and relaxed conditions on the same
module, names the class-field-theory five-term continuation, and derives the
one-dimensional conserved-bit balance.  The 827 boundary is literally the
transpose of the seated reflected localization coordinate. -/

#check Fermat.FiftyNine.Conservation.PointedTateIncidence.strictObservation
#check Fermat.FiftyNine.Conservation.PointedTateIncidence.PointedConditions
#check Fermat.FiftyNine.Conservation.PointedTateIncidence.focusConditions
#check Fermat.FiftyNine.Conservation.PointedTateIncidence.PoitouTateFiveTerm
#check Fermat.FiftyNine.Conservation.PointedTateIncidence.PoitouTateFiveTerm.connecting
#check Fermat.FiftyNine.Conservation.PointedTateIncidence.PoitouTateFiveTerm.fiveTerm_exact
#check Fermat.FiftyNine.Conservation.PointedTateIncidence.PoitouTateFiveTerm.dimension_balance
#check Fermat.FiftyNine.Conservation.PointedTateIncidence.PoitouTateFiveTerm.conserved_bit
#check Fermat.FiftyNine.Conservation.PointedTateIncidence.PoitouTateFiveTerm.landing_alternatives
#check Fermat.FiftyNine.Conservation.PointedTateIncidence.relaxedObservation827
#check Fermat.FiftyNine.Conservation.PointedTateIncidence.strictObservation827
#check Fermat.FiftyNine.Conservation.PointedTateIncidence.pointedConditions827
#check Fermat.FiftyNine.Conservation.PointedTateIncidence.reflectedPointedLocalization827
#check Fermat.FiftyNine.Conservation.PointedTateIncidence.ReflectedG827
#check Fermat.FiftyNine.Conservation.PointedTateIncidence.reflectedGToF827
#check Fermat.FiftyNine.Conservation.PointedTateIncidence.reflectedCoordinatePairing827
#check Fermat.FiftyNine.Conservation.PointedTateIncidence.PointedTateIncidence827
#check Fermat.FiftyNine.Conservation.PointedTateIncidence.PointedTateIncidence827.connecting_apply
#check Fermat.FiftyNine.Conservation.PointedTateIncidence.PointedTateIncidence827.conserved_bit
#check Fermat.FiftyNine.Conservation.PointedTateIncidence.PointedTateIncidence827.conormalClass_eq_zero_iff_primalGain_eq_zero
#check Fermat.FiftyNine.Conservation.PointedTateIncidence.PointedTateIncidence827.reflectedGain_eq_one_iff_fixed
#check Fermat.FiftyNine.Conservation.PointedTateIncidence.PointedTateIncidence827.primalGain_eq_one_iff_transverse
#check Fermat.FiftyNine.Conservation.PointedTateIncidence.PointedTateIncidence827.compiled_future_alternatives
#check Fermat.FiftyNine.Conservation.PointedTateIncidence.reflectedGain_eq_one_of_fourierSeating

#guard_depends_on
  Fermat.FiftyNine.Conservation.PointedTateIncidence.focusConditions,
  Fermat.Conservation.FocusConormal.conormalRestriction
#guard_depends_on
  Fermat.FiftyNine.Conservation.PointedTateIncidence.PoitouTateFiveTerm.dimension_balance,
  LinearMap.finrank_range_add_finrank_ker
#guard_depends_on
  Fermat.FiftyNine.Conservation.PointedTateIncidence.pointedConditions827,
  Fermat.FiftyNine.Conservation.GaugeSteering827.pointedConormalRestriction827
#guard_depends_on
  Fermat.FiftyNine.Conservation.PointedTateIncidence.reflectedPointedLocalization827,
  Fermat.FiftyNine.Conservation.DetectorWitness827.qLocalizationCoordinate827
#guard_depends_on
  Fermat.FiftyNine.Conservation.PointedTateIncidence.PointedTateIncidence827.conserved_bit,
  Fermat.FiftyNine.Conservation.PointedTateIncidence.PoitouTateFiveTerm.conserved_bit
#guard_depends_on
  Fermat.FiftyNine.Conservation.PointedTateIncidence.PointedTateIncidence827.conormalClass_eq_zero_iff_primalGain_eq_zero,
  Fermat.FiftyNine.Conservation.GaugeSteering827.pointedConormalClass827_eq_zero_iff_fixed
#guard_depends_on
  Fermat.FiftyNine.Conservation.PointedTateIncidence.PointedTateIncidence827.compiled_future_alternatives,
  Fermat.FiftyNine.Conservation.PointedTateIncidence.PoitouTateFiveTerm.landing_alternatives
#guard_depends_on
  Fermat.FiftyNine.Conservation.PointedTateIncidence.reflectedGain_eq_one_of_fourierSeating,
  Fermat.FiftyNine.Conservation.SplitPrimeFourier827.fixedAttention_of_fourierSeating

/-! The wild-place inventory records exactly which campaign inputs have an
exposed cyclotomic-generator decomposition.  The two actual pairing inputs
do not, so the conservative formula budget is `NEEDS-VOSTOKOV`.  The named
discharge interface asks for explicit Kummer-class coefficient expansions
of both normalized state factors without asserting that they exist. -/

#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.fieldKummerClass
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.integralUnitKummerClass
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.integralNonzeroKummerClass
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.zetaKummerClass
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.fixedDenominatorKummerClass
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.generatedUnitKummerClass
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.artinHasseKummerSubgroup
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.normalizedPlusKummerClass
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.normalizedMinusKummerClass
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.ArtinHasseKummerDecomposition
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.ArtinHasseKummerDecomposition.mem
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.NormalizedStateFactorArtinHasseDecomposition
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.NormalizedStateFactorArtinHasseDecomposition.plus_mem
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.NormalizedStateFactorArtinHasseDecomposition.minus_mem
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.WildClassKind
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.hasArtinHasseDecomposition
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.WildFormulaBudget
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.formulaBudget
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.campaignInventory
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.campaign_formulaBudget_eq_needsVostokov

#guard_depends_on
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.ArtinHasseKummerDecomposition.mem,
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.artinHasseKummerSubgroup
#guard_depends_on
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.NormalizedStateFactorArtinHasseDecomposition.plus_mem,
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.ArtinHasseKummerDecomposition.mem
#guard_depends_on
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.NormalizedStateFactorArtinHasseDecomposition.minus_mem,
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.ArtinHasseKummerDecomposition.mem
#guard_depends_on
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.campaign_formulaBudget_eq_needsVostokov,
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.formulaBudget
#guard_depends_on
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.campaign_formulaBudget_eq_needsVostokov,
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.campaignInventory

/--
info: 'Fermat.FiftyNine.Conservation.DetectorWitness827.firstLampReading827_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.DetectorWitness827.firstLampReading827_eq

/--
info: 'Fermat.FiftyNine.Conservation.DetectorWitness827.firstLampReading827_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.DetectorWitness827.firstLampReading827_ne_zero

/--
info: 'Fermat.FiftyNine.Conservation.DetectorWitness827.firstEdgeResidue827_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.DetectorWitness827.firstEdgeResidue827_eq

/--
info: 'Fermat.FiftyNine.Conservation.DetectorWitness827.firstEdgeSymbol827_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.DetectorWitness827.firstEdgeSymbol827_eq

/--
info: 'Fermat.FiftyNine.Conservation.DetectorWitness827.firstEdgeSymbol827_eq_root_pow_reading' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.DetectorWitness827.firstEdgeSymbol827_eq_root_pow_reading

/--
info: 'Fermat.FiftyNine.Conservation.DetectorWitness827.TransverseDetectorWitness.outside_tame_reading_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.DetectorWitness827.TransverseDetectorWitness.outside_tame_reading_eq_zero

/--
info: 'Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.EmptySupportTransverseDetectorWitness.candidate_eigenlaw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.EmptySupportTransverseDetectorWitness.candidate_eigenlaw

/--
info: 'Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.EmptySupportTransverseDetectorWitness.candidate_valuation_dvd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.EmptySupportTransverseDetectorWitness.candidate_valuation_dvd

/--
info: 'Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.EmptySupportTransverseDetectorWitness.reading_eq_zero_at_every_tame_auxiliary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.EmptySupportTransverseDetectorWitness.reading_eq_zero_at_every_tame_auxiliary

/--
info: 'Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.EmptySupportTransverseDetectorWitness.auxiliaryReading_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.EmptySupportTransverseDetectorWitness.auxiliaryReading_eq_zero

/--
info: 'Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.EmptySupportTransverseDetectorWitness.not_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.EmptySupportTransverseDetectorWitness.not_nonempty

/--
info: 'Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.firstLampReading827_not_realized_by_seated_pairing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.DetectorWitness827.Seated.firstLampReading827_not_realized_by_seated_pairing

/--
info: 'Fermat.FiftyNine.Conservation.ArtinHasseInventory.campaign_formulaBudget_eq_needsVostokov' does not depend on any axioms
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.ArtinHasseInventory.campaign_formulaBudget_eq_needsVostokov

/-! W3 is a compiled conditional theorem, not an unconditional producer.
Its proof consumes reciprocity, the chosen detector, and the gauge
zero-reflection law.  Its local-vanishing step now factors through the
functional Stokes theorem `Lambda x = 0`, then uses the existing exact
relation-(7a) vanishing theorem. -/

#check Fermat.FiftyNine.Conservation.TateBridge.StateLinkedIdealPair.vandiverSevenA_of_tate_bridge
#check Fermat.FiftyNine.Conservation.TateBridge.Mu59ToTheNRisk
#check Fermat.FiftyNine.Conservation.TateBridge.mu_59_to_the_n_risk

#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.StateLinkedIdealPair.vandiverSevenA_of_tate_bridge,
  Fermat.Conservation.TatePairing.GlobalReciprocityLaw.pairAt_eq_zero_of_other_places
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.StateLinkedIdealPair.vandiverSevenA_of_tate_bridge,
  Fermat.FiftyNine.Conservation.TateBridge.chosenTransverseDetector
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.StateLinkedIdealPair.vandiverSevenA_of_tate_bridge,
  Fermat.FiftyNine.Conservation.TateBridge.Lambda_apply_eq_zero_of_reciprocity
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.StateLinkedIdealPair.vandiverSevenA_of_tate_bridge,
  Fermat.FiftyNine.Conservation.TateBridge.GaugeComparison.reflects_selected_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.StateLinkedIdealPair.vandiverSevenA_of_tate_bridge,
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.differenceGauge_eq_zero_iff_vandiverSevenA
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.mu_59_to_the_n_risk,
  Fermat.FiftyNine.Conservation.TateBridge.Mu59ToTheNRisk.mk

/-! ## Decisive PowerRoot-localization test and retained depth observation -/

/-! The selected readings expose their two allocated sources, while the
generic candidate face keeps both orders of localization on one input.  The
four-constructor result selects the genuinely implemented fourth route. -/

#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.r0
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.r1
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.selectedGauge
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.SelectedAllocatedReadings
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.selectedAllocatedReadings
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.selectedAllocatedReadings_sources_ne
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.PowerRootLocalizationSide
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.ReadingProvenance
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.powerRootR0Candidate
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.powerRootR1Candidate
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.powerRootLocalizationDefect
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.SameInputPowerRootLocalizationFace
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.sameInputPowerRootLocalizationFace
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.LocalPowerRootClassShadowTrivialization
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.r0Provenance
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.r1Provenance
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.gaugeComparisonProvenance
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.SameInputPowerRootIdentification
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.noSameInputPowerRootIdentification
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.DirectPowerRootNaturalityOutcome
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.GlobalReciprocityTwoCell
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.ReciprocityNaturalityOutcome
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.ReflectedDualLocalizationCarrier
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.ReflectedDualCarrierOutcome
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.DifferentObstructionOutcome
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.GaugeNaturalityOutcome
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.gaugeNaturalityOutcome59
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.selectedGauge_eq_difference
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.globalReciprocityTwoCellOfLaw
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.GaugeComparisonRoute
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.gaugeComparisonRoute
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.routeOfGaugeComparison
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.gaugeComparisonNotLocalAfterLocalize
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.gaugeComparisonNotLocalizeAfterGlobal
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.IntegralGaugeLift
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.integralR0
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.integralR1
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.bocksteinPowerRootReceipt
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.TwoTwosCorrespondenceStatus
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.BocksteinPowerRootReceiptObservation
#check Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.bocksteinPowerRootReceiptObservation

#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.selectedAllocatedReadings,
  Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.r0
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.selectedAllocatedReadings,
  Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.r1
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.selectedAllocatedReadings_sources_ne,
  zero_ne_one
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.sameInputPowerRootLocalizationFace,
  Fermat.Conservation.PowerRootNaturality.LocalizationInterface.obstruction_square
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.noSameInputPowerRootIdentification,
  Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.SameInputPowerRootIdentification.shared_selected_input
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.gaugeNaturalityOutcome59,
  Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.selectedAllocatedReadings_sources_ne
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.gaugeNaturalityOutcome59,
  Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.noSameInputPowerRootIdentification
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.selectedGauge_eq_difference,
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.differenceGauge_reading
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.globalReciprocityTwoCellOfLaw,
  Fermat.Conservation.TatePairing.GlobalReciprocityLaw.sum_eq_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.gaugeComparisonRoute,
  Fermat.FiftyNine.Conservation.TateBridge.GaugeComparison.pairing_eq_gauge
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.routeOfGaugeComparison,
  Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.gaugeComparisonRoute
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.gaugeComparisonNotLocalAfterLocalize,
  Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.routeOfGaugeComparison
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.gaugeComparisonNotLocalizeAfterGlobal,
  Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.routeOfGaugeComparison
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.bocksteinPowerRootReceiptObservation,
  Fermat.Conservation.KummerDrain.AllocatedFactorLedger.rootClass_torsion
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.bocksteinPowerRootReceiptObservation,
  Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.selectedGauge_eq_difference
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.bocksteinPowerRootReceiptObservation,
  Fermat.Conservation.CommonActionStage.differenceGauge
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.bocksteinPowerRootReceiptObservation,
  Fermat.FiftyNine.Conservation.TateBridge.mu_59_to_the_n_risk

/--
info: 'Fermat.FiftyNine.Conservation.TateBridge.StateLinkedIdealPair.vandiverSevenA_of_tate_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.TateBridge.StateLinkedIdealPair.vandiverSevenA_of_tate_bridge

/-! ## Generated N59 credit: tower, orbit, matrix, capacity, repayment -/

/--
info: 'Fermat.FiftyNine.Conservation.Credit.stockRank_eq_twentyEight' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.stockRank_eq_twentyEight

/--
info: 'Fermat.FiftyNine.Conservation.Credit.realCycleOrder_eq_twentyNine' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.realCycleOrder_eq_twentyNine

/--
info: 'Fermat.FiftyNine.Conservation.Credit.conductor_eq_fiftyNine' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.conductor_eq_fiftyNine

/--
info: 'Fermat.FiftyNine.Conservation.Credit.generationTower' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.generationTower

/--
info: 'Fermat.FiftyNine.Conservation.Credit.attestationPrime_eq_eightHundredTwentySeven' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.attestationPrime_eq_eightHundredTwentySeven

/--
info: 'Fermat.FiftyNine.Conservation.Credit.attestationPrime_isPrime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.attestationPrime_isPrime

/--
info: 'Fermat.FiftyNine.Conservation.Credit.attestationRoot_eq_sixHundredSeventyOne' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.attestationRoot_eq_sixHundredSeventyOne

/--
info: 'Fermat.FiftyNine.Conservation.Credit.attestationRoot_order' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.attestationRoot_order

/--
info: 'Fermat.FiftyNine.Conservation.Credit.exponentGenerator_val' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.exponentGenerator_val

/--
info: 'Fermat.FiftyNine.Conservation.Credit.exponentGenerator_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.exponentGenerator_order

/--
info: 'Fermat.FiftyNine.Conservation.Credit.exponentGenerator_pow_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.exponentGenerator_pow_order

/--
info: 'Fermat.FiftyNine.Conservation.Credit.exponentCycle_rank' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.exponentCycle_rank

/--
info: 'Fermat.FiftyNine.Conservation.Credit.exponentCycle_exactPeriod' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.exponentCycle_exactPeriod

/--
info: 'Fermat.FiftyNine.Conservation.Credit.exponentCycle_point' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.exponentCycle_point

/--
info: 'Fermat.FiftyNine.Conservation.Credit.generatedUnit_eq_orbit_ratio' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.generatedUnit_eq_orbit_ratio

/--
info: 'Fermat.FiftyNine.Conservation.Credit.generatedUnit_mem_subledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.generatedUnit_mem_subledger

/--
info: 'Fermat.FiftyNine.Conservation.Credit.fundingTransfer_opposite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.fundingTransfer_opposite

/--
info: 'Fermat.FiftyNine.Conservation.Credit.everyTransfer_isFunded' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.everyTransfer_isFunded

/--
info: 'Fermat.FiftyNine.Conservation.Credit.fundedGenerators_eq_univ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.fundedGenerators_eq_univ

/--
info: 'Fermat.FiftyNine.Conservation.Credit.receivableLedger_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.receivableLedger_apply

/--
info: 'Fermat.FiftyNine.Conservation.Credit.receivableLedger_opposite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.receivableLedger_opposite

/--
info: 'Fermat.FiftyNine.Conservation.Credit.ledger_cardinality' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.ledger_cardinality

/--
info: 'Fermat.FiftyNine.Conservation.Credit.capacityIndex_eq_relIndex' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.capacityIndex_eq_relIndex

/-! ## Filled C2 and bounded C4 seams -/

/--
info: 'Fermat.FiftyNine.Conservation.CapacityCertificate.capacityCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.CapacityCertificate.capacityCertificate

/--
info: 'Fermat.FiftyNine.Conservation.Credit.boundedSinnottBridge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Credit.boundedSinnottBridge

/--
info: 'Fermat.FiftyNine.Conservation.Fold.not_dvd_plusClassNumber' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Fold.not_dvd_plusClassNumber

/--
info: 'Fermat.FiftyNine.Conservation.Fold.vandiverSevenD_of_relativeNormFold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Fold.vandiverSevenD_of_relativeNormFold

/--
info: 'Fermat.FiftyNine.Conservation.Fold.vandiverSevenD_of_conjugationTranspose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Fold.vandiverSevenD_of_conjugationTranspose

/--
info: 'Fermat.FiftyNine.Conservation.Fold.factorPrincipalizationPermit_of_sevenA_and_conjugationTranspose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Fold.factorPrincipalizationPermit_of_sevenA_and_conjugationTranspose

/-! ## Selected C5 gauge, cube certificate, and closed W3 -/

open Lean Elab Command

/-- Exhaustively audit every declaration in a selected implementation
namespace against Lean's standard extensionality, choice, and quotient
boundary. -/
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

#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.Instance
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.DepthCertificate
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.GaugeQuotient
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.Fold
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.FermatState
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.StateFactorPair
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.StateFactorConjugation
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.CommonActionStage
#guard_standard_axioms_prefix Fermat.Conservation.TatePairing
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.TateBridge
#guard_standard_axioms_prefix Fermat.Conservation.FocusConormal
#guard_standard_axioms_prefix Fermat.Conservation.SteeringFiber
#guard_standard_axioms_prefix Fermat.Conservation.ExteriorTransfer
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.DetectorWitness827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.GaugeSteering827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.SplitPrimeFourier827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.PointedTateIncidence
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.ArtinHasseInventory
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.TransformerProbe

#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.GaugeSteering827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.SplitPrimeFourier827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.PointedTateIncidence
#audit_no_product_equiv_types_prefix Fermat.Conservation.FocusConormal
#audit_no_product_equiv_types_prefix Fermat.Conservation.SteeringFiber
#audit_no_product_equiv_types_prefix Fermat.Conservation.ExteriorTransfer

/--
info: 'Fermat.FiftyNine.Conservation.Instance.gauge_cycle_eq_exponentCycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Instance.gauge_cycle_eq_exponentCycle

/--
info: 'Fermat.FiftyNine.Conservation.Instance.BernoulliCertificate.raw_power_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Instance.BernoulliCertificate.raw_power_sum

/--
info: 'Fermat.FiftyNine.Conservation.Instance.BernoulliCertificate.highBernoulliNumerator_cubeFree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Instance.BernoulliCertificate.highBernoulliNumerator_cubeFree

/--
info: 'Fermat.FiftyNine.Conservation.Instance.noBernoulliCubeObstruction59' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Instance.noBernoulliCubeObstruction59

/--
info: 'Fermat.FiftyNine.Conservation.Instance.flowCertificate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Instance.flowCertificate

/--
info: 'Fermat.FiftyNine.Conservation.Instance.deepFlowLaw59' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Instance.deepFlowLaw59

/--
info: 'Fermat.FiftyNine.Conservation.Instance.deepExponentForcing_of_flow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Instance.deepExponentForcing_of_flow

/--
info: 'Fermat.FiftyNine.Conservation.Instance.repayment_of_capacity_and_flow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.Instance.repayment_of_capacity_and_flow

/-! ## Selected exact-depth and gauge-quotient receipts -/

/--
info: 'Fermat.FiftyNine.Conservation.DepthCertificate.highEigenvalue_square_attained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.DepthCertificate.highEigenvalue_square_attained

/--
info: 'Fermat.FiftyNine.Conservation.DepthCertificate.depthTwoCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.DepthCertificate.depthTwoCertificate

/--
info: 'Fermat.FiftyNine.Conservation.GaugeQuotient.generatedGauge_chargeInvariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.GaugeQuotient.generatedGauge_chargeInvariant

/--
info: 'Fermat.FiftyNine.Conservation.GaugeQuotient.debitLedger_quotient_eq_bot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.GaugeQuotient.debitLedger_quotient_eq_bot

/--
info: 'Fermat.FiftyNine.Conservation.GaugeQuotient.quotient_vacuum_and_charge_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.GaugeQuotient.quotient_vacuum_and_charge_eq

/-! ## Fermat-state and normalized factor-pair receipts -/

/--
info: 'Fermat.FiftyNine.Conservation.FermatState.PrimitiveSecondCaseSolution.charge_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.FermatState.PrimitiveSecondCaseSolution.charge_pos

/--
info: 'Fermat.FiftyNine.Conservation.FermatState.false_of_stockCreditTransformer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.FermatState.false_of_stockCreditTransformer

/--
info: 'Fermat.FiftyNine.Conservation.FermatState.PrimitiveSecondCaseSolution.exists_oriented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.FermatState.PrimitiveSecondCaseSolution.exists_oriented

/--
info: 'Fermat.FiftyNine.Conservation.StateFactorPair.stateEquation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.StateFactorPair.stateEquation

/--
info: 'Fermat.FiftyNine.Conservation.StateFactorPair.prime_dvd_x_add_y' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.StateFactorPair.prime_dvd_x_add_y

/--
info: 'Fermat.FiftyNine.Conservation.StateFactorPair.state_isCoprime_x_y' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.StateFactorPair.state_isCoprime_x_y

/--
info: 'Fermat.FiftyNine.Conservation.StateFactorPair.zetaUnit_val' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.StateFactorPair.zetaUnit_val

/--
info: 'Fermat.FiftyNine.Conservation.StateFactorPair.zetaUnit_isPrimitiveRoot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.StateFactorPair.zetaUnit_isPrimitiveRoot

/--
info: 'Fermat.FiftyNine.Conservation.StateFactorPair.rawFactorIdeal_product' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.StateFactorPair.rawFactorIdeal_product

/--
info: 'Fermat.FiftyNine.Conservation.StateFactorPair.stateFactor_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.StateFactorPair.stateFactor_ne_zero

/--
info: 'Fermat.FiftyNine.Conservation.StateFactorPair.normalizedFactor_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.StateFactorPair.normalizedFactor_spec

/--
info: 'Fermat.FiftyNine.Conservation.StateFactorPair.normalizedFactor_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.StateFactorPair.normalizedFactor_ne_zero

/--
info: 'Fermat.FiftyNine.Conservation.StateFactorPair.fixedDenominator_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.StateFactorPair.fixedDenominator_ne_zero

/--
info: 'Fermat.FiftyNine.Conservation.StateFactorPair.normalizedPlusFactor_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.StateFactorPair.normalizedPlusFactor_spec

/--
info: 'Fermat.FiftyNine.Conservation.StateFactorPair.normalizedMinusFactor_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.StateFactorPair.normalizedMinusFactor_spec

/--
info: 'Fermat.FiftyNine.Conservation.StateFactorPair.normalizedPlusFactor_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.StateFactorPair.normalizedPlusFactor_ne_zero

/--
info: 'Fermat.FiftyNine.Conservation.StateFactorPair.normalizedMinusFactor_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.StateFactorPair.normalizedMinusFactor_ne_zero

/--
info: 'Fermat.FiftyNine.Conservation.StateFactorPair.stateLinkedIdealPair_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.StateFactorPair.stateLinkedIdealPair_exists

/--
info: 'Fermat.FiftyNine.Conservation.StateFactorPair.allocatedPair' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.StateFactorPair.allocatedPair

/--
info: 'Fermat.FiftyNine.Conservation.StateFactorPair.StateLinkedIdealPair.plusIdeal_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.StateFactorPair.StateLinkedIdealPair.plusIdeal_ne_zero

/--
info: 'Fermat.FiftyNine.Conservation.StateFactorPair.StateLinkedIdealPair.minusIdeal_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.StateFactorPair.StateLinkedIdealPair.minusIdeal_ne_zero

/--
info: 'Fermat.FiftyNine.Conservation.StateFactorPair.StateLinkedIdealPair.ledger_rootIdeal_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.StateFactorPair.StateLinkedIdealPair.ledger_rootIdeal_zero

/--
info: 'Fermat.FiftyNine.Conservation.StateFactorPair.StateLinkedIdealPair.ledger_rootIdeal_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.StateFactorPair.StateLinkedIdealPair.ledger_rootIdeal_one

/-! ## Conjugate state-fold receipts -/

/--
info: 'Fermat.FiftyNine.Conservation.StateFactorConjugation.normalizedMinusFactor_eq_unit_mul_conj' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.StateFactorConjugation.normalizedMinusFactor_eq_unit_mul_conj

/--
info: 'Fermat.FiftyNine.Conservation.StateFactorConjugation.span_normalizedMinusFactor_eq_map_conj' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.StateFactorConjugation.span_normalizedMinusFactor_eq_map_conj

/--
info: 'Fermat.FiftyNine.Conservation.StateFactorConjugation.StateLinkedIdealPair.minusIdeal_eq_map_conj_plusIdeal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.StateFactorConjugation.StateLinkedIdealPair.minusIdeal_eq_map_conj_plusIdeal

/--
info: 'Fermat.FiftyNine.Conservation.StateFactorConjugation.StateLinkedIdealPair.ledger_conjugationTranspose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.StateFactorConjugation.StateLinkedIdealPair.ledger_conjugationTranspose

/--
info: 'Fermat.FiftyNine.Conservation.StateFactorConjugation.StateLinkedIdealPair.vandiverSevenD' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.StateFactorConjugation.StateLinkedIdealPair.vandiverSevenD

/--
info: 'Fermat.FiftyNine.Conservation.StateFactorConjugation.StateLinkedIdealPair.vandiverSevenA_of_areaTransfer_to_vacuum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.StateFactorConjugation.StateLinkedIdealPair.vandiverSevenA_of_areaTransfer_to_vacuum

/--
info: 'Fermat.FiftyNine.Conservation.StateFactorConjugation.StateLinkedIdealPair.factorPrincipalizationPermit_of_sevenA' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.StateFactorConjugation.StateLinkedIdealPair.factorPrincipalizationPermit_of_sevenA

/-! ## Seven-stock receipt -/

/--
info: 'Fermat.FiftyNine.Conservation.stockSpineReceipt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.stockSpineReceipt

/-! ## Rank-28 gauge and ramified drain -/

/--
info: 'Fermat.FiftyNine.Conservation.charge_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.charge_mul

/--
info: 'Fermat.FiftyNine.Conservation.gauge_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.gauge_decomposition

/--
info: 'Fermat.FiftyNine.Conservation.charge_gauge_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.charge_gauge_invariant

/--
info: 'Fermat.FiftyNine.Conservation.charge_full_gauge_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.charge_full_gauge_invariant

/--
info: 'Fermat.FiftyNine.Conservation.unitRank_eq_twentyEight' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.unitRank_eq_twentyEight

/--
info: 'Fermat.FiftyNine.Conservation.rankTwentyEightGauge_regulator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.rankTwentyEightGauge_regulator

/--
info: 'Fermat.FiftyNine.Conservation.lambda_eq_neg_zeta_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.lambda_eq_neg_zeta_sub_one

/--
info: 'Fermat.FiftyNine.Conservation.lambda_charge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.lambda_charge

/--
info: 'Fermat.FiftyNine.Conservation.charge_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.charge_pow

/--
info: 'Fermat.FiftyNine.Conservation.drainCharge_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.drainCharge_eq

/--
info: 'Fermat.FiftyNine.Conservation.drainCharge_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.drainCharge_strictMono

/--
info: 'Fermat.FiftyNine.Conservation.drainCharge_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.drainCharge_step

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

/-! ## Exhaustive forbidden declaration and transitive-module guards -/

/-- Fail if the imported environment contains any declaration below a
forbidden namespace or module prefix. -/
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
prefix.  This catches files such as `FirstCase` whose declarations live in a
shorter namespace. -/
elab "#guard_no_module_prefix " p:ident : command => do
  let env ← getEnv
  let forbiddenPrefix := p.getId
  let offenders :=
    env.header.moduleNames.filter forbiddenPrefix.isPrefixOf
  unless offenders.isEmpty do
    throwError
      "modules with forbidden prefix {forbiddenPrefix}: {offenders}"

/-- Fail if one exact module occurs in the transitive import graph.  This is
needed for the forbidden `Fermat.Statement` transport while still permitting
the narrow `Fermat.Statement.Basic` definitions. -/
elab "#guard_no_module " p:ident : command => do
  let env ← getEnv
  let forbiddenModule := p.getId
  if env.header.moduleNames.contains forbiddenModule then
    throwError "forbidden module {forbiddenModule} is imported"

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

/-! The six classical exponent-specific routes remain absent as modules,
including routes which declare into the shorter `Fermat.FiftyNine`
namespace. -/

#guard_no_module_prefix Fermat.FiftyNine.GenericProof
#guard_no_module_prefix Fermat.FiftyNine.FirstCase
#guard_no_module_prefix Fermat.FiftyNine.GenericSecondCase
#guard_no_module_prefix Fermat.FiftyNine.Folding
#guard_no_module_prefix Fermat.FiftyNine.GenericChannels
#guard_no_module_prefix Fermat.FiftyNine.GenericLemmaTwo

/-! The exact five-file Vandiver seam superseded by CREDIT-FLOW is forbidden
transitively, not merely checked for representative declarations. -/

#guard_no_module Fermat.FiftyNine.VandiverPolynomialUnits
#guard_no_module Fermat.FiftyNine.VandiverDeepPolynomial
#guard_no_module Fermat.FiftyNine.VandiverPositiveRelationDerivative
#guard_no_module Fermat.FiftyNine.VandiverRelationNormalization
#guard_no_module Fermat.FiftyNine.VandiverNormalizedRelationDerivative

#guard_no_module_prefix Fermat.GenericIrregular
#guard_no_module_prefix Fermat.Irregular
#guard_no_module_prefix Fermat.Regular
#guard_no_module_prefix Fermat.KummerIso
#guard_no_module_prefix Fermat.Ladder
#guard_no_module Fermat.Statement

/-! Representative declaration guards cover module boundaries whose source
file does not declare into a same-named namespace (notably `FirstCase`). -/

/--
error: Unknown identifier `Fermat.FiftyNine.GenericProof.holdsAt_fiftyNine_generic`
-/
#guard_msgs in
#check Fermat.FiftyNine.GenericProof.holdsAt_fiftyNine_generic

/--
error: Unknown identifier `Fermat.FiftyNine.firstCase_of_pairwise_coprime`
-/
#guard_msgs in
#check Fermat.FiftyNine.firstCase_of_pairwise_coprime

/--
error: Unknown identifier `Fermat.FiftyNine.GenericSecondCase.secondCaseExcluded_fiftyNine_generic`
-/
#guard_msgs in
#check Fermat.FiftyNine.GenericSecondCase.secondCaseExcluded_fiftyNine_generic

/--
error: Unknown identifier `Fermat.FiftyNine.Folding.safePrimeLadder`
-/
#guard_msgs in
#check Fermat.FiftyNine.Folding.safePrimeLadder

/--
error: Unknown identifier `Fermat.FiftyNine.GenericChannels.bernoulliCubeCondition_fiftyNine_generic`
-/
#guard_msgs in
#check Fermat.FiftyNine.GenericChannels.bernoulliCubeCondition_fiftyNine_generic

/--
error: Unknown identifier `Fermat.FiftyNine.GenericLemmaTwo.vandiverLemmaTwo_fiftyNine_generic`
-/
#guard_msgs in
#check Fermat.FiftyNine.GenericLemmaTwo.vandiverLemmaTwo_fiftyNine_generic

/-! The forbidden repository transport is a declaration rather than a
namespace, so it receives a direct unknown-constant guard. -/

/--
error: Unknown constant `Fermat.HoldsAt.mono_of_dvd`
-/
#guard_msgs in
#check Fermat.HoldsAt.mono_of_dvd

/-! Additional classical endpoints remain outside the cone as well. -/

/--
error: Unknown identifier `Fermat.FiftyNine.holdsAt_fiftyNine_conservation`
-/
#guard_msgs in
#check Fermat.FiftyNine.holdsAt_fiftyNine_conservation

/--
error: Unknown identifier `Fermat.FiftyNine.holdsAt_fiftyNine`
-/
#guard_msgs in
#check Fermat.FiftyNine.holdsAt_fiftyNine

/--
error: Unknown identifier `Fermat.KummerIso.ResidueRegressions.holdsAt_fiftyNine`
-/
#guard_msgs in
#check Fermat.KummerIso.ResidueRegressions.holdsAt_fiftyNine
