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
gauge quotient is complete, while the guarded transformer probe records the
statewise relation-production and pullback obligations that stop W2 and W3.
-/
import Fermat.Conservation.GuardDependsOn
import Fermat.Conservation.Ledger
import Fermat.Conservation.Transfer
import Fermat.FiftyNine.Conservation.Spine
import Fermat.FiftyNine.Conservation.CapacityCertificate
import Fermat.FiftyNine.Conservation.BoundedSinnott
import Fermat.FiftyNine.Conservation.Instance
import Fermat.FiftyNine.Conservation.DepthCertificate
import Fermat.FiftyNine.Conservation.GaugeQuotient
import Fermat.FiftyNine.Conservation.Fold
import Fermat.FiftyNine.Conservation.StateFactorPair
import Fermat.FiftyNine.Conservation.StateFactorConjugation
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
  Fermat.FiftyNine.Conservation.Instance.deepExponentForcing_of_flow,
  Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.depth_conservation
#guard_depends_on
  Fermat.FiftyNine.Conservation.Instance.deepExponentForcing_of_flow,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.FiftyNine.Conservation.Instance.deepExponentForcing_on_exponentCycle_of_flow,
  Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.depth_conservation
#guard_depends_on
  Fermat.FiftyNine.Conservation.Instance.deepExponentForcing_on_exponentCycle_of_flow,
  Fermat.Conservation.Ledger.conservation_identity

/-! The selected `d = 1` equivalence and its legacy repayment corollary
retain the named one-layer conservation identity transitively. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.Instance.nonempty_repayOne_iff_deep_repayment59,
  Fermat.Conservation.Credit.Repayment.repay_layer_conservation
#guard_depends_on
  Fermat.FiftyNine.Conservation.Instance.repayment_of_capacity_and_flow,
  Fermat.Conservation.Credit.Repayment.repay_layer_conservation

/-! The selected grade-zero state is literally funded by both halves named
in its definition: the stock receipt and a generated C1 vacuum. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.Instance.regularClosure59,
  Fermat.FiftyNine.Conservation.stockSpineReceipt
#guard_depends_on
  Fermat.FiftyNine.Conservation.Instance.regularClosure59,
  Fermat.Conservation.Credit.kummer_credit_vacuum

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
#guard_depends_on Fermat.FiftyNine.Conservation.stockSpineReceipt,
  Fermat.Six.Conservation.sixth_ledger

/-! N2's Pythagorean balance theorems remain locally literal.  These guards
do not conflate them with the separately repaired isometry/Noether path. -/

#guard_depends_on Fermat.Two.pythagoras,
  Fermat.Two.charge_ledger
#guard_depends_on Fermat.Two.emptyCoupling_of_additive,
  Fermat.Two.charge_ledger
#guard_depends_on Fermat.Two.pythagoras_conserved,
  Fermat.Two.charge_ledger

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

/-! The selected gauge quotient keeps both of its native projection
identities load-bearing, without pretending they have already been joined
by a global accounting morphism. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeQuotient.debitLedger_quotient_eq_bot,
  Fermat.Conservation.Credit.GaugeQuotient.PrimeData.quotientLedger_eq_bot
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeQuotient.debitLedger_quotient_eq_bot,
  Fermat.Conservation.Ledger.conservation_identity
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeQuotient.quotient_vacuum_and_charge_eq,
  Fermat.FiftyNine.Conservation.GaugeQuotient.debitLedger_quotient_eq_bot
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeQuotient.quotient_vacuum_and_charge_eq,
  Fermat.Conservation.Credit.GaugeQuotient.PrimeData.quotientCharge_quotientState
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeQuotient.quotient_vacuum_and_charge_eq,
  Fermat.Conservation.Ledger.conservation_identity

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
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.TransformerProbe

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
