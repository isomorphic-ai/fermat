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
import Fermat.Conservation.SelmerEigenspace
import Fermat.Conservation.TatePairing
import Fermat.Conservation.TamePlacePairing
import Fermat.Conservation.TameSymbolTransport
import Fermat.Conservation.WildKummerPairing
import Fermat.Conservation.IwasawaTracePairing
import Fermat.Conservation.KummerTateCup
import Fermat.Conservation.KummerTateReadout
import Fermat.Conservation.LocalKummerH1
import Fermat.Conservation.KummerOrientation
import Fermat.Conservation.DiscreteKummerTatePairing
import Fermat.Conservation.KummerCupSpanReadout
import Fermat.Conservation.LocalKummerTransport
import Fermat.Conservation.CohomologicalKummerPairing
import Fermat.Conservation.AlbertDescentDatum59
import Fermat.Conservation.AlbertExtension59
import Fermat.Conservation.AlbertOrder59
import Fermat.Conservation.AlbertGalois59
import Fermat.Conservation.ContinuousCyclicQuotient
import Fermat.Conservation.AlbertCyclicQuotient59
import Fermat.Conservation.AlbertCyclicCompatibility59
import Fermat.Conservation.AlbertCyclicConverse59
import Fermat.Conservation.OrientedKummerRepresentative59
import Fermat.Conservation.KummerCharacterComparison59
import Fermat.Conservation.ConcreteTwistedLiftCupBridge59
import Fermat.Conservation.IntegratedTwistedKummerCup59
import Fermat.Conservation.CompatibleKummerLift59
import Fermat.Conservation.CyclicLiftNaturality59
import Fermat.Conservation.ContinuousCarryH2LiftCriterion59
import Fermat.Conservation.ContinuousCyclicH2Readout59
import Fermat.Conservation.ContinuousCyclicH2Equiv59
import Fermat.Conservation.ContinuousH2Pullback59
import Fermat.Conservation.ContinuousH2PullbackFunctorial59
import Fermat.Conservation.PrimeCyclicH2
import Fermat.Conservation.PrimeCyclicH2At59
import Fermat.Conservation.PrimeCyclicExtension
import Fermat.Conservation.PrimeContinuousHomogeneousPullback
import Fermat.Conservation.PrimeContinuousCarryLift
import Fermat.Conservation.PrimeContinuousCarryLiftAt59
import Fermat.Conservation.PrimeKummerCyclicQuotient
import Fermat.Conservation.PrimeKummerCyclicQuotientAt59
import Fermat.Conservation.PrimeKummerCarryLiftCriterion
import Fermat.Conservation.PrimeKummerCharacterComparison
import Fermat.Conservation.PrimeKummerCharacterComparisonAt59
import Fermat.Conservation.PrimeOrientedCarryH2Class
import Fermat.Conservation.PrimeOrientedCarryH2ClassAt59
import Fermat.Conservation.PrimeConcreteTwistedLiftCupBridge
import Fermat.Conservation.PrimeIntegratedTwistedKummerCup
import Fermat.Conservation.PrimeCompatibleKummerLift
import Fermat.Conservation.PrimeCompatibleKummerLiftAt59
import Fermat.Conservation.PrimeKummerNormLiftH2Criterion
import Fermat.FiftyNine.Conservation.PrimeKummerNormLiftH2CriterionAt59
import Fermat.Conservation.PrimeAlbertDescentDatum
import Fermat.Conservation.PrimeAlbertExtension
import Fermat.Conservation.PrimeAlbertOrder
import Fermat.Conservation.PrimeAlbertGalois
import Fermat.Conservation.PrimeAlbertCyclicQuotient
import Fermat.Conservation.PrimeAlbertCyclicCompatibility
import Fermat.Conservation.PrimeAlbertCyclicConverse
import Fermat.Conservation.PrimeAlbertCyclicConverseAt59
import Fermat.Conservation.KummerOnePlusRootNormPrime
import Fermat.Conservation.KummerOnePlusRootNorm59
import Fermat.Conservation.PrimeKummerExplicitNorm
import Fermat.Conservation.PrimeKummerTrace
import Fermat.Conservation.PrimeTriangularUnitFactorization
import Fermat.Conservation.PrimeTriangularNormBounds
import Fermat.Conservation.PrimeTriangularValuationDepth
import Fermat.Conservation.NonarchimedeanProductRemainder
import Fermat.Conservation.SpectralNormProductRemainder
import Fermat.Conservation.PolynomialSpectralNormBound
import Fermat.Conservation.PrimeTriangularSpectralContraction
import Fermat.Conservation.PrimeTriangularExplicitNorm
import Fermat.Conservation.ValuationProductDominant
import Fermat.Conservation.PrimeTriangularSpectralAbsorption
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
import Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827
import Fermat.FiftyNine.Conservation.FourierPairingProjection827
import Fermat.FiftyNine.Conservation.PrimalOrbitResidue827
import Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827
import Fermat.FiftyNine.Conservation.ExplicitResiduePlaceOrbit827
import Fermat.FiftyNine.Conservation.LocalReduction827
import Fermat.FiftyNine.Conservation.CyclotomicTameContext59
import Fermat.FiftyNine.Conservation.FullOrbitReciprocity827
import Fermat.FiftyNine.Conservation.RawOrbitReciprocity827
import Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827
import Fermat.FiftyNine.Conservation.ExplicitTameOrbitNonvanishing827
import Fermat.FiftyNine.Conservation.ActualTameLedger827
import Fermat.FiftyNine.Conservation.ActualTameLedgerNonvanishing827
import Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
import Fermat.FiftyNine.Conservation.ConjugationFixedClassDivisibility59
import Fermat.FiftyNine.Conservation.ConjugationFixedPrincipalDivisor59
import Fermat.FiftyNine.Conservation.ConjugatePairSource827
import Fermat.FiftyNine.Conservation.ConjugatePlaceOrbit827
import Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827
import Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827
import Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827
import Fermat.FiftyNine.Conservation.CanonicalConjugatePairIncidence827
import Fermat.FiftyNine.Conservation.CanonicalConjugatePairNormalizedEndpoint59
import Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedger827
import Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827
import Fermat.FiftyNine.Conservation.CanonicalGlobalReciprocity827
import Fermat.FiftyNine.Conservation.CanonicalConjugatePairGlobalLedger827
import Fermat.FiftyNine.Conservation.PointedTateIncidence
import Fermat.FiftyNine.Conservation.AlgebraicPointedIncidence827
import Fermat.FiftyNine.Conservation.TransversalityVerdict827
import Fermat.FiftyNine.Conservation.UlamTypeFreeze
import Fermat.FiftyNine.Conservation.UlamReadout827
import Fermat.FiftyNine.Conservation.ArtinHasseInventory
import Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827
import Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
import Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827
import Fermat.FiftyNine.Conservation.CyclotomicLocalizationEquivariance827
import Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827
import Fermat.FiftyNine.Conservation.TrivialReflectedAttestationPrimeLift827
import Fermat.FiftyNine.Conservation.LocalCompletion59
import Fermat.FiftyNine.Conservation.VostokovLocalization59
import Fermat.FiftyNine.Conservation.VostokovShapeAudit59
import Fermat.FiftyNine.Conservation.IwasawaLocalization59
import Fermat.FiftyNine.Conservation.KummerTateLocalization59
import Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59
import Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59
import Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59
import Fermat.FiftyNine.Conservation.NormalizedContinuousWildLocalization59
import Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59
import Fermat.FiftyNine.Conservation.StatewiseTwistedLambdaBridge59
import Fermat.FiftyNine.Conservation.TwistedLambdaCarryH2Class59
import Fermat.FiftyNine.Conservation.TwistedLambdaKummerCupComparison59
import Fermat.FiftyNine.Conservation.TwistedLambdaKummerLiftCriterion59
import Fermat.FiftyNine.Conservation.TwistedLambdaKummerNormCriterion59
import Fermat.FiftyNine.Conservation.TwistedLambdaH2Inflation59
import Fermat.FiftyNine.Conservation.TwistedLambdaAlbertCriterion59
import Fermat.FiftyNine.Conservation.TwistedArtinHasse59
import Fermat.FiftyNine.Conservation.LocalCyclotomicTrace59
import Fermat.FiftyNine.Conservation.TwistedArtinHasseLocalTrace59
import Fermat.FiftyNine.Conservation.TwistedFiniteLogLocalTrace59
import Fermat.FiftyNine.Conservation.AdicCompleteValuedInteger59
import Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59
import Fermat.FiftyNine.Conservation.CompletedLogTail59
import Fermat.FiftyNine.Conservation.LocalIntegralTrace59
import Fermat.FiftyNine.Conservation.CompletedLogTraceNonzero59
import Fermat.FiftyNine.Conservation.CompletedLogResidue59
import Fermat.FiftyNine.Conservation.CompletedLogPowerObstruction59
import Fermat.FiftyNine.Conservation.CompletedLogLocalPowerObstruction59
import Fermat.FiftyNine.Conservation.TwistedLambdaNormalizationSign59
import Fermat.FiftyNine.Conservation.TwistedLambdaNormalizedEndpoint59
import Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59
import Fermat.FiftyNine.Conservation.BareLambdaNorm59
import Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59
import Fermat.FiftyNine.Conservation.CriticalUnitQuotient59
import Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59
import Fermat.FiftyNine.Conservation.CriticalUnitPowerSurjectivity59
import Fermat.FiftyNine.Conservation.CriticalUnitPowerKernel59
import Fermat.FiftyNine.Conservation.ExplicitNormResidue59
import Fermat.FiftyNine.Conservation.TwistedLambdaEisensteinIntegrality59
import Fermat.FiftyNine.Conservation.TriangularSpectralDepth59
import Fermat.FiftyNine.Conservation.TriangularNormSeparation59
import Fermat.FiftyNine.Conservation.TriangularResidualNormalization59
import Fermat.FiftyNine.Conservation.TriangularResidualStep59
import Fermat.FiftyNine.Conservation.TriangularTerminalResidual59
import Fermat.FiftyNine.Conservation.FiveStepResidual59
import Fermat.FiftyNine.Conservation.InitialIntegralDecomposition59
import Fermat.FiftyNine.Conservation.PowerU1Reflection59
import Fermat.FiftyNine.Conservation.NormImageBridge59
import Fermat.FiftyNine.Conservation.ExactNormIntersection59
import Fermat.FiftyNine.Conservation.NormImageConsequences59
import Fermat.FiftyNine.Conservation.Unit60KummerNormObstruction59
import Fermat.FiftyNine.Conservation.TwistedLambdaCupUnitReduction59
import Fermat.FiftyNine.Conservation.KummerCupSpanLocalization59
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
#check Fermat.Conservation.TatePairing.PlaceIndexedLocalPairing.awayReadingTotal
#check Fermat.Conservation.TatePairing.PlaceIndexedLocalPairing.readingTotalOn
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
#check Fermat.Conservation.TatePairing.GlobalReciprocityLaw.pairAt_eq_neg_awayReadingTotal
#check Fermat.Conservation.TatePairing.GlobalReciprocityLaw.pairAt_eq_neg_readingTotalOn
#check Fermat.Conservation.TatePairing.GlobalReciprocityLaw.pairAt_eq_zero_of_other_places
#check Fermat.Conservation.TatePairing.GlobalReciprocityLaw.pairAt_add_pairAt_eq_zero_of_outside_two
#check Fermat.Conservation.TatePairing.GlobalReciprocityLaw.pairAt_eq_neg_pairAt_of_outside_two
#check Fermat.Conservation.TatePairing.LocalOrthogonalityGuard
#check Fermat.Conservation.TatePairing.LocalOrthogonalityGuard.pairAt_eq_zero

#guard_depends_on
  Fermat.Conservation.TatePairing.PlaceIndexedLocalPairing.awayReadingTotal,
  Fermat.Conservation.TatePairing.PlaceIndexedLocalPairing.readings
#guard_depends_on
  Fermat.Conservation.TatePairing.PlaceIndexedLocalPairing.readingTotalOn,
  Fermat.Conservation.TatePairing.PlaceIndexedLocalPairing.pairAt
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
  Fermat.Conservation.TatePairing.GlobalReciprocityLaw.pairAt_eq_neg_awayReadingTotal,
  Fermat.Conservation.TatePairing.GlobalReciprocityLaw.sum_eq_zero
#guard_depends_on
  Fermat.Conservation.TatePairing.GlobalReciprocityLaw.pairAt_eq_neg_awayReadingTotal,
  Fermat.Conservation.TatePairing.PlaceIndexedLocalPairing.awayReadingTotal
#guard_depends_on
  Fermat.Conservation.TatePairing.GlobalReciprocityLaw.pairAt_eq_neg_readingTotalOn,
  Fermat.Conservation.TatePairing.GlobalReciprocityLaw.sum_eq_zero
#guard_depends_on
  Fermat.Conservation.TatePairing.GlobalReciprocityLaw.pairAt_eq_neg_readingTotalOn,
  Fermat.Conservation.TatePairing.PlaceIndexedLocalPairing.readingTotalOn
#guard_depends_on
  Fermat.Conservation.TatePairing.GlobalReciprocityLaw.pairAt_eq_zero_of_other_places,
  Fermat.Conservation.TatePairing.GlobalReciprocityLaw.sum_eq_zero
#guard_depends_on
  Fermat.Conservation.TatePairing.GlobalReciprocityLaw.pairAt_add_pairAt_eq_zero_of_outside_two,
  Fermat.Conservation.TatePairing.GlobalReciprocityLaw.sum_eq_zero
#guard_depends_on
  Fermat.Conservation.TatePairing.GlobalReciprocityLaw.pairAt_eq_neg_pairAt_of_outside_two,
  Fermat.Conservation.TatePairing.GlobalReciprocityLaw.pairAt_add_pairAt_eq_zero_of_outside_two
#guard_depends_on
  Fermat.Conservation.TatePairing.LocalOrthogonalityGuard.pairAt_eq_zero,
  Fermat.Conservation.TatePairing.LocalOrthogonalityGuard.orthogonal

/-! The two-place tame bookkeeping retains an auxiliary reciprocity receipt:
all tame rows outside the distinguished and auxiliary places are constructed
from the seated Selmer valuations, leaving only explicitly non-tame rows. -/

#check Fermat.Conservation.TamePlacePairing.PlaceIndexedTameRealization.OutsideTwoTameBookkeeping
#check Fermat.Conservation.TamePlacePairing.PlaceIndexedTameRealization.OutsideTwoTameBookkeeping.outside_two_readings_at_tame_places
#check Fermat.Conservation.TamePlacePairing.PlaceIndexedTameRealization.OutsideTwoTameBookkeeping.outside_two_readings_of_tame_and_residual
#check Fermat.Conservation.TamePlacePairing.PlaceIndexedTameRealization.OutsideTwoTameBookkeeping.distinguished_eq_neg_auxiliary_of_reciprocity
#check Fermat.Conservation.TamePlacePairing.Seated.Realization.outsideTwoTameBookkeeping
#check Fermat.Conservation.TamePlacePairing.Seated.Realization.outside_two_readings_at_tame_places
#check Fermat.Conservation.TamePlacePairing.Seated.Realization.outside_two_readings_of_residual
#check Fermat.Conservation.TamePlacePairing.Seated.Realization.distinguished_eq_neg_auxiliary_of_reciprocity

#guard_depends_on
  Fermat.Conservation.TamePlacePairing.PlaceIndexedTameRealization.OutsideTwoTameBookkeeping.outside_two_readings_at_tame_places,
  Fermat.Conservation.TamePlacePairing.PlaceIndexedTameRealization.pairAt_eq_zero_of_p_dvd_ord
#guard_depends_on
  Fermat.Conservation.TamePlacePairing.PlaceIndexedTameRealization.OutsideTwoTameBookkeeping.outside_two_readings_of_tame_and_residual,
  Fermat.Conservation.TamePlacePairing.PlaceIndexedTameRealization.OutsideTwoTameBookkeeping.outside_two_readings_at_tame_places
#guard_depends_on
  Fermat.Conservation.TamePlacePairing.PlaceIndexedTameRealization.OutsideTwoTameBookkeeping.distinguished_eq_neg_auxiliary_of_reciprocity,
  Fermat.Conservation.TatePairing.GlobalReciprocityLaw.pairAt_eq_neg_pairAt_of_outside_two
#guard_depends_on
  Fermat.Conservation.TamePlacePairing.PlaceIndexedTameRealization.OutsideTwoTameBookkeeping.distinguished_eq_neg_auxiliary_of_reciprocity,
  Fermat.Conservation.TamePlacePairing.PlaceIndexedTameRealization.OutsideTwoTameBookkeeping.outside_two_readings_of_tame_and_residual
#guard_depends_on
  Fermat.Conservation.TamePlacePairing.Seated.Realization.outsideTwoTameBookkeeping,
  Fermat.Conservation.TamePlacePairing.Seated.Realization.selectedValuationsZeroAt
#guard_depends_on
  Fermat.Conservation.TamePlacePairing.Seated.Realization.outside_two_readings_at_tame_places,
  Fermat.Conservation.TamePlacePairing.PlaceIndexedTameRealization.OutsideTwoTameBookkeeping.outside_two_readings_at_tame_places
#guard_depends_on
  Fermat.Conservation.TamePlacePairing.Seated.Realization.outside_two_readings_of_residual,
  Fermat.Conservation.TamePlacePairing.PlaceIndexedTameRealization.OutsideTwoTameBookkeeping.outside_two_readings_of_tame_and_residual
#guard_depends_on
  Fermat.Conservation.TamePlacePairing.Seated.Realization.distinguished_eq_neg_auxiliary_of_reciprocity,
  Fermat.Conservation.TatePairing.GlobalReciprocityLaw.pairAt_eq_neg_pairAt_of_outside_two
#guard_depends_on
  Fermat.Conservation.TamePlacePairing.Seated.Realization.distinguished_eq_neg_auxiliary_of_reciprocity,
  Fermat.Conservation.TamePlacePairing.Seated.Realization.outside_two_readings_of_residual

/-! The tame layer constructs the complete finite-support pairing from one
wild local interface.  Detector existence and the selected gauge comparison
remain interfaces; the bank audit and every away row are now proved. -/

#check Fermat.FiftyNine.Conservation.TateBridge.LocalPairing
#check Fermat.FiftyNine.Conservation.TateBridge.WildLocalInterface
#check Fermat.FiftyNine.Conservation.TateBridge.H_FLT
#check Fermat.FiftyNine.Conservation.TateBridge.WildDetectorDual
#check Fermat.FiftyNine.Conservation.TateBridge.pair_59
#check Fermat.FiftyNine.Conservation.TateBridge.Lambda
#check Fermat.FiftyNine.Conservation.TateBridge.Q_7a
#check Fermat.FiftyNine.Conservation.TateBridge.sevenAGauge_vacuum
#check Fermat.FiftyNine.Conservation.TateBridge.Q_7a_finrank_le_one
#check Fermat.FiftyNine.Conservation.TateBridge.descendedFunctionalOnQ_7a
#check Fermat.FiftyNine.Conservation.TateBridge.descendedFunctionalOnQ_7a_pullback
#check Fermat.FiftyNine.Conservation.TateBridge.descendedFunctionalOnQ_7a_preimage_independent
#check Fermat.FiftyNine.Conservation.TateBridge.Lambda_apply
#check Fermat.FiftyNine.Conservation.TateBridge.Lambda_apply_eq_zero_of_reciprocity
#check Fermat.FiftyNine.Conservation.TateBridge.wild_detector_faithful
#check Fermat.FiftyNine.Conservation.TateBridge.wild_detector_faithful_on_Q_7a
#check Fermat.FiftyNine.Conservation.TateBridge.eq_zero_of_wild_detector_faithful
#check Fermat.FiftyNine.Conservation.TateBridge.wild_detector_faithful_on_Q_7a_of_global
#check Fermat.FiftyNine.Conservation.TateBridge.gauge_eq_zero_of_wild_detector_faithful_on_Q_7a
#check Fermat.FiftyNine.Conservation.TateBridge.potential_eq_zero_of_stokes_and_faithful
#check Fermat.FiftyNine.Conservation.TateBridge.gauge_eq_zero_of_stokes_and_faithful_on_Q_7a
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
#check Fermat.FiftyNine.Conservation.TateBridge.GaugeComparison.scalarGauge_eq_zero_iff_vandiverSevenA
#check Fermat.FiftyNine.Conservation.TateBridge.GaugeComparison.local_reading_eq_zero_iff_vandiverSevenA
#check Fermat.FiftyNine.Conservation.TateBridge.SevenAGaugeSeating
#check Fermat.FiftyNine.Conservation.TateBridge.SevenAGaugeSeating.gauge_eq_zero_iff_vandiverSevenA
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
  Fermat.FiftyNine.Conservation.TateBridge.sevenAGauge_vacuum,
  map_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.Q_7a_finrank_le_one,
  Fermat.Conservation.SteeringFiber.scalarQuestionQuotient_finrank_le_one
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.descendedFunctionalOnQ_7a_pullback,
  Fermat.Conservation.SteeringFiber.scalarQuestionDual_pullback
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.descendedFunctionalOnQ_7a_preimage_independent,
  Fermat.Conservation.SteeringFiber.scalarQuestionDual_preimage_independent
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
  Fermat.FiftyNine.Conservation.TateBridge.wild_detector_faithful_on_Q_7a_of_global,
  Fermat.FiftyNine.Conservation.TateBridge.eq_zero_of_wild_detector_faithful
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.gauge_eq_zero_of_wild_detector_faithful_on_Q_7a,
  Fermat.FiftyNine.Conservation.TateBridge.wild_detector_faithful_on_Q_7a
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.potential_eq_zero_of_stokes_and_faithful,
  Fermat.FiftyNine.Conservation.TateBridge.Lambda_apply_eq_zero_of_reciprocity
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.potential_eq_zero_of_stokes_and_faithful,
  Fermat.FiftyNine.Conservation.TateBridge.eq_zero_of_wild_detector_faithful
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.gauge_eq_zero_of_stokes_and_faithful_on_Q_7a,
  Fermat.FiftyNine.Conservation.TateBridge.Lambda_apply_eq_zero_of_reciprocity
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.gauge_eq_zero_of_stokes_and_faithful_on_Q_7a,
  Fermat.FiftyNine.Conservation.TateBridge.gauge_eq_zero_of_wild_detector_faithful_on_Q_7a
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
  Fermat.FiftyNine.Conservation.TateBridge.GaugeComparison.scalarGauge_eq_zero_iff_vandiverSevenA,
  Fermat.FiftyNine.Conservation.TateBridge.GaugeComparison.reflects_selected_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.GaugeComparison.scalarGauge_eq_zero_iff_vandiverSevenA,
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.differenceGauge_eq_zero_iff_vandiverSevenA
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.GaugeComparison.local_reading_eq_zero_iff_vandiverSevenA,
  Fermat.FiftyNine.Conservation.TateBridge.GaugeComparison.pairing_eq_gauge
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.GaugeComparison.local_reading_eq_zero_iff_vandiverSevenA,
  Fermat.FiftyNine.Conservation.TateBridge.GaugeComparison.scalarGauge_eq_zero_iff_vandiverSevenA
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.SevenAGaugeSeating.gauge_eq_zero_iff_vandiverSevenA,
  Fermat.FiftyNine.Conservation.TateBridge.SevenAGaugeSeating.gauge_at_fermat
#guard_depends_on
  Fermat.FiftyNine.Conservation.TateBridge.SevenAGaugeSeating.gauge_eq_zero_iff_vandiverSevenA,
  Fermat.FiftyNine.Conservation.TateBridge.GaugeComparison.scalarGauge_eq_zero_iff_vandiverSevenA

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
#check Fermat.Conservation.SelmerEigenspace.characterProjectorAt_eq_self_of_mem
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
  Fermat.Conservation.SelmerEigenspace.characterProjectorAt_eq_self_of_mem,
  Fermat.Conservation.SelmerEigenspace.mem_characterEigenspaceAt_iff
#guard_depends_on
  Fermat.Conservation.SelmerEigenspace.characterProjectorAt_eq_self_of_mem,
  Fermat.Conservation.InvolutiveBase.characterIdempotent
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
#guard_depends_on
  Fermat.FiftyNine.Conservation.GaugeSteering827.fixedGauge_preimage_independent,
  Fermat.Conservation.SteeringFiber.reading_preimage_independent

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

/-! The complete 58-place orbit is retained until complementary character
waves are multiplied.  Their product is constant, so the full orbit sum is
the negative of any selected product in `ZMod 59`; global reciprocity then
turns the distinguished reading into that selected product. -/

#check Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827.pointwiseProduct_complementaryCharacters
#check Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827.pointwiseProduct_eq_selected_of_complementaryPureCharacters
#check Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827.sum_pointwiseProduct_eq_card_mul_selected
#check Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827.sum_pointwiseProduct_eq_fiftyEight_mul_selected
#check Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827.sum_pointwiseProduct_eq_neg_selected
#check Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827.galoisIndex59_sum_pointwiseProduct_eq_neg_selected
#check Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827.cyclotomic_projectedLocalization_product_sum_eq_neg_selected

#guard_depends_on
  Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827.pointwiseProduct_complementaryCharacters,
  Fermat.FiftyNine.Conservation.SplitPrimeFourier827.characterFunction
#guard_depends_on
  Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827.pointwiseProduct_eq_selected_of_complementaryPureCharacters,
  Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827.pointwiseProduct_complementaryCharacters
#guard_depends_on
  Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827.sum_pointwiseProduct_eq_card_mul_selected,
  Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827.pointwiseProduct_eq_selected_of_complementaryPureCharacters
#guard_depends_on
  Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827.sum_pointwiseProduct_eq_fiftyEight_mul_selected,
  Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827.sum_pointwiseProduct_eq_card_mul_selected
#guard_depends_on
  Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827.sum_pointwiseProduct_eq_neg_selected,
  Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827.sum_pointwiseProduct_eq_fiftyEight_mul_selected
#guard_depends_on
  Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827.galoisIndex59_sum_pointwiseProduct_eq_neg_selected,
  Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827.sum_pointwiseProduct_eq_neg_selected
#guard_depends_on
  Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827.cyclotomic_projectedLocalization_product_sum_eq_neg_selected,
  Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827.galoisIndex59_sum_pointwiseProduct_eq_neg_selected
#guard_depends_on
  Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827.cyclotomic_projectedLocalization_product_sum_eq_neg_selected,
  Fermat.FiftyNine.Conservation.SplitPrimeFourier827.projectedLocalization_isPureCharacter

/-! The primal wave is now the Fourier projection of the explicit full
residue orbit of the first generated circular unit.  The corresponding
height-one primes give an explicit 58-place orbit, rather than an abstract
enumeration of the support. -/

#check Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.orbitRoot827
#check Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.orbitRoot827_isPrimitive
#check Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.orbitReductionHom827
#check Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.orbitReductionHom827_zeta
#check Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.orbitRoot827_one_eq_firstRowRoot
#check Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.orbitReductionHom827_one_eq_firstReductionHom
#check Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.fullOrbitUnitReading827
#check Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.fullOrbitUnitReading827_firstGenerated_one
#check Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.unitCharacterWave827
#check Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.unitCharacterWave827_isPureCharacter
#check Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.unitCharacterWave827_mul_apply
#check Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.complementaryPrimalUnitWave827
#check Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.complementaryPrimalUnitWave827_isPureCharacter
#check Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.complementaryPrimalUnitWave827_product_sum_eq_neg_selected

#guard_depends_on
  Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.orbitRoot827_isPrimitive,
  Fermat.FiftyNine.Conservation.Credit.attestationRoot_order
#guard_depends_on
  Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.orbitReductionHom827,
  Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.orbitRoot827_isPrimitive
#guard_depends_on
  Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.orbitReductionHom827_zeta,
  Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.orbitReductionHom827
#guard_depends_on
  Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.orbitRoot827_one_eq_firstRowRoot,
  Fermat.FiftyNine.Conservation.CapacityCertificate.rowRoot
#guard_depends_on
  Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.orbitReductionHom827_one_eq_firstReductionHom,
  Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.orbitRoot827_one_eq_firstRowRoot
#guard_depends_on
  Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.fullOrbitUnitReading827,
  Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.orbitReductionHom827
#guard_depends_on
  Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.fullOrbitUnitReading827_firstGenerated_one,
  Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.orbitReductionHom827_one_eq_firstReductionHom
#guard_depends_on
  Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.fullOrbitUnitReading827_firstGenerated_one,
  Fermat.FiftyNine.Conservation.CapacityCertificate.residueFunctional_generatedUnit_eq
#guard_depends_on
  Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.unitCharacterWave827,
  Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.fullOrbitUnitReading827
#guard_depends_on
  Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.unitCharacterWave827_isPureCharacter,
  Fermat.FiftyNine.Conservation.SplitPrimeFourier827.fourierCoefficient
#guard_depends_on
  Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.unitCharacterWave827_mul_apply,
  Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.unitCharacterWave827
#guard_depends_on
  Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.complementaryPrimalUnitWave827,
  Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.unitCharacterWave827
#guard_depends_on
  Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.complementaryPrimalUnitWave827_isPureCharacter,
  Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.unitCharacterWave827_isPureCharacter
#guard_depends_on
  Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.complementaryPrimalUnitWave827_product_sum_eq_neg_selected,
  Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827.cyclotomic_projectedLocalization_product_sum_eq_neg_selected
#guard_depends_on
  Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.complementaryPrimalUnitWave827_product_sum_eq_neg_selected,
  Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.complementaryPrimalUnitWave827_isPureCharacter

#check Fermat.FiftyNine.Conservation.OrbitPlace827.orbitReductionHom827_surjective
#check Fermat.FiftyNine.Conservation.OrbitPlace827.orbitRoot827_injective
#check Fermat.FiftyNine.Conservation.OrbitPlace827.orbitReductionHom827_ker_ne_bot
#check Fermat.FiftyNine.Conservation.OrbitPlace827.orbitPlace827
#check Fermat.FiftyNine.Conservation.OrbitPlace827.orbitReductionHom827_comp_algebraMap
#check Fermat.FiftyNine.Conservation.OrbitPlace827.orbitPlace827_under_int
#check Fermat.FiftyNine.Conservation.OrbitPlace827.orbitPlace827_mem_placesOver827
#check Fermat.FiftyNine.Conservation.OrbitPlace827.orbitPlace827Subtype
#check Fermat.FiftyNine.Conservation.OrbitPlace827.orbitPlace827Subtype_injective
#check Fermat.FiftyNine.Conservation.OrbitPlace827.orbitPlaceEquiv827
#check Fermat.FiftyNine.Conservation.OrbitPlace827.orbitRoot827_mul
#check Fermat.FiftyNine.Conservation.OrbitPlace827.orbitReductionHom827_comp_cyclotomicRingEquiv
#check Fermat.FiftyNine.Conservation.OrbitPlace827.cyclotomicRingOfIntegersEquiv59_symm_local
#check Fermat.FiftyNine.Conservation.OrbitPlace827.cyclotomicPlaceEquiv59_orbitPlace
#check Fermat.FiftyNine.Conservation.OrbitPlace827.indexedPlaceOrbitEquiv827_eq_orbitPlace827Subtype_inv

#guard_depends_on
  Fermat.FiftyNine.Conservation.OrbitPlace827.orbitReductionHom827_surjective,
  ZMod.ringHom_surjective
#guard_depends_on
  Fermat.FiftyNine.Conservation.OrbitPlace827.orbitRoot827_injective,
  Fermat.FiftyNine.Conservation.Credit.attestationRoot_order
#guard_depends_on
  Fermat.FiftyNine.Conservation.OrbitPlace827.orbitReductionHom827_ker_ne_bot,
  Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.orbitReductionHom827
#guard_depends_on
  Fermat.FiftyNine.Conservation.OrbitPlace827.orbitPlace827,
  Fermat.FiftyNine.Conservation.OrbitPlace827.orbitReductionHom827_ker_ne_bot
#guard_depends_on
  Fermat.FiftyNine.Conservation.OrbitPlace827.orbitPlace827_under_int,
  Fermat.FiftyNine.Conservation.OrbitPlace827.orbitReductionHom827_comp_algebraMap
#guard_depends_on
  Fermat.FiftyNine.Conservation.OrbitPlace827.orbitPlace827_mem_placesOver827,
  Fermat.FiftyNine.Conservation.OrbitPlace827.orbitPlace827_under_int
#guard_depends_on
  Fermat.FiftyNine.Conservation.OrbitPlace827.orbitPlace827Subtype,
  Fermat.FiftyNine.Conservation.OrbitPlace827.orbitPlace827_mem_placesOver827
#guard_depends_on
  Fermat.FiftyNine.Conservation.OrbitPlace827.orbitPlace827Subtype_injective,
  Fermat.FiftyNine.Conservation.OrbitPlace827.orbitRoot827_injective
#guard_depends_on
  Fermat.FiftyNine.Conservation.OrbitPlace827.orbitPlace827Subtype_injective,
  Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.orbitReductionHom827_zeta
#guard_depends_on
  Fermat.FiftyNine.Conservation.OrbitPlace827.orbitPlaceEquiv827,
  Fermat.FiftyNine.Conservation.OrbitPlace827.orbitPlace827Subtype_injective
#guard_depends_on
  Fermat.FiftyNine.Conservation.OrbitPlace827.orbitPlaceEquiv827,
  Fermat.FiftyNine.Conservation.SplitPrimeFourier827.placesOver827_ncard_eq_fiftyEight
#guard_depends_on
  Fermat.FiftyNine.Conservation.OrbitPlace827.orbitRoot827_mul,
  Fermat.FiftyNine.Conservation.Credit.attestationRoot_order
#guard_depends_on
  Fermat.FiftyNine.Conservation.OrbitPlace827.orbitReductionHom827_comp_cyclotomicRingEquiv,
  Fermat.FiftyNine.Conservation.OrbitPlace827.orbitRoot827_mul
#guard_depends_on
  Fermat.FiftyNine.Conservation.OrbitPlace827.orbitReductionHom827_comp_cyclotomicRingEquiv,
  Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.orbitReductionHom827_zeta
#guard_depends_on
  Fermat.FiftyNine.Conservation.OrbitPlace827.cyclotomicRingOfIntegersEquiv59_symm_local,
  KummerCriterion.cyclotomicRingOfIntegersEquiv_mul_apply
#guard_depends_on
  Fermat.FiftyNine.Conservation.OrbitPlace827.cyclotomicPlaceEquiv59_orbitPlace,
  Fermat.FiftyNine.Conservation.OrbitPlace827.cyclotomicRingOfIntegersEquiv59_symm_local
#guard_depends_on
  Fermat.FiftyNine.Conservation.OrbitPlace827.cyclotomicPlaceEquiv59_orbitPlace,
  Fermat.FiftyNine.Conservation.OrbitPlace827.orbitReductionHom827_comp_cyclotomicRingEquiv
#guard_depends_on
  Fermat.FiftyNine.Conservation.OrbitPlace827.indexedPlaceOrbitEquiv827_eq_orbitPlace827Subtype_inv,
  Fermat.FiftyNine.Conservation.CyclotomicLocalizationEquivariance827.indexedPlaceOrbitEquiv827_eq_cyclotomicPlaceEquiv59
#guard_depends_on
  Fermat.FiftyNine.Conservation.OrbitPlace827.indexedPlaceOrbitEquiv827_eq_orbitPlace827Subtype_inv,
  Fermat.FiftyNine.Conservation.OrbitPlace827.cyclotomicPlaceEquiv59_orbitPlace

#check Fermat.FiftyNine.Conservation.FullOrbitReciprocity827.orbitReading
#check Fermat.FiftyNine.Conservation.FullOrbitReciprocity827.GlobalReciprocityLaw.pairAt_eq_neg_sum_orbitReading
#check Fermat.FiftyNine.Conservation.FullOrbitReciprocity827.GlobalReciprocityLaw.pairAt_eq_selectedProduct_of_complementaryOrbit
#check Fermat.FiftyNine.Conservation.FullOrbitReciprocity827.GlobalReciprocityLaw.pairAt_eq_selectedProduct_of_cyclotomicReflectedOrbit
#check Fermat.FiftyNine.Conservation.FullOrbitReciprocity827.GlobalReciprocityLaw.pairAt_eq_selectedCircularUnitProduct_of_cyclotomicReflectedOrbit

#guard_depends_on
  Fermat.FiftyNine.Conservation.FullOrbitReciprocity827.orbitReading,
  Fermat.Conservation.TatePairing.PlaceIndexedLocalPairing.pairAt
#guard_depends_on
  Fermat.FiftyNine.Conservation.FullOrbitReciprocity827.GlobalReciprocityLaw.pairAt_eq_neg_sum_orbitReading,
  Fermat.FiftyNine.Conservation.FullOrbitReciprocity827.orbitReading
#guard_depends_on
  Fermat.FiftyNine.Conservation.FullOrbitReciprocity827.GlobalReciprocityLaw.pairAt_eq_neg_sum_orbitReading,
  Fermat.Conservation.TatePairing.GlobalReciprocityLaw.pairAt_eq_neg_readingTotalOn
#guard_depends_on
  Fermat.FiftyNine.Conservation.FullOrbitReciprocity827.GlobalReciprocityLaw.pairAt_eq_selectedProduct_of_complementaryOrbit,
  Fermat.FiftyNine.Conservation.FullOrbitReciprocity827.GlobalReciprocityLaw.pairAt_eq_neg_sum_orbitReading
#guard_depends_on
  Fermat.FiftyNine.Conservation.FullOrbitReciprocity827.GlobalReciprocityLaw.pairAt_eq_selectedProduct_of_complementaryOrbit,
  Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827.sum_pointwiseProduct_eq_neg_selected
#guard_depends_on
  Fermat.FiftyNine.Conservation.FullOrbitReciprocity827.GlobalReciprocityLaw.pairAt_eq_selectedProduct_of_cyclotomicReflectedOrbit,
  Fermat.FiftyNine.Conservation.FullOrbitReciprocity827.GlobalReciprocityLaw.pairAt_eq_neg_sum_orbitReading
#guard_depends_on
  Fermat.FiftyNine.Conservation.FullOrbitReciprocity827.GlobalReciprocityLaw.pairAt_eq_selectedProduct_of_cyclotomicReflectedOrbit,
  Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827.cyclotomic_projectedLocalization_product_sum_eq_neg_selected
#guard_depends_on
  Fermat.FiftyNine.Conservation.FullOrbitReciprocity827.GlobalReciprocityLaw.pairAt_eq_selectedCircularUnitProduct_of_cyclotomicReflectedOrbit,
  Fermat.FiftyNine.Conservation.FullOrbitReciprocity827.GlobalReciprocityLaw.pairAt_eq_selectedProduct_of_cyclotomicReflectedOrbit
#guard_depends_on
  Fermat.FiftyNine.Conservation.FullOrbitReciprocity827.GlobalReciprocityLaw.pairAt_eq_selectedCircularUnitProduct_of_cyclotomicReflectedOrbit,
  Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.complementaryPrimalUnitWave827_isPureCharacter

/-! The physical 827 orbit is now connected end to end at the scalar level.
`LocalReduction827` builds each actual valuation-ring reduction and tame
context; `FourierPairingProjection827` projects only under the complete
58-place sum; `RawOrbitReciprocity827` transports that honest raw sum through
global reciprocity; and `ExplicitTameOrbitReciprocity827` specializes the
chain to the first circular unit and a genuine q-relaxed representative.

The inverse place orientation remains explicit throughout.  In particular,
these checks do not install the false pointwise identification of a raw
residue coordinate with its selected Fourier component. -/

#check Fermat.FiftyNine.Conservation.LocalReduction827.LocalRing827
#check Fermat.FiftyNine.Conservation.LocalReduction827.localReductionHom827
#check Fermat.FiftyNine.Conservation.LocalReduction827.localReductionHom827_algebraMap
#check Fermat.FiftyNine.Conservation.LocalReduction827.chosenUniformizer827
#check Fermat.FiftyNine.Conservation.LocalReduction827.chosenUniformizer827_spec
#check Fermat.FiftyNine.Conservation.LocalReduction827.chosenUniformizer827_ne_zero
#check Fermat.FiftyNine.Conservation.LocalReduction827.chosenUniformizerUnit827
#check Fermat.FiftyNine.Conservation.LocalReduction827.valuationOfNeZero_chosenUniformizerUnit827
#check Fermat.FiftyNine.Conservation.LocalReduction827.localUnitPart827
#check Fermat.FiftyNine.Conservation.LocalReduction827.angularComponent827
#check Fermat.FiftyNine.Conservation.LocalReduction827.angularComponent827_globalUnit
#check Fermat.FiftyNine.Conservation.LocalReduction827.attestationRootUnit_isPrimitive_public
#check Fermat.FiftyNine.Conservation.LocalReduction827.tameContext827
#check Fermat.FiftyNine.Conservation.LocalReduction827.tameContext827_ord
#check Fermat.FiftyNine.Conservation.LocalReduction827.tameContext827_angularComponent_globalUnit
#check Fermat.FiftyNine.Conservation.LocalReduction827.tameContext827_residueCharacter_eq_residueLog
#check Fermat.FiftyNine.Conservation.LocalReduction827.realNorm_firstGeneratedUnit_eq_sq
#check Fermat.FiftyNine.Conservation.LocalReduction827.tameContext827_primalResidue_eq_fullOrbitUnitReading
#check Fermat.FiftyNine.Conservation.LocalReduction827.tameContext827_value_globalUnit
#check Fermat.FiftyNine.Conservation.LocalReduction827.canonicalZeta59
#check Fermat.FiftyNine.Conservation.LocalReduction827.canonicalZeta59_isPrimitive
#check Fermat.FiftyNine.Conservation.LocalReduction827.inverseOrientedFullOrbitUnitReading827
#check Fermat.FiftyNine.Conservation.LocalReduction827.rhoQ827
#check Fermat.FiftyNine.Conservation.LocalReduction827.qLocalizationCoordinate827_eq_candidateRepresentative
#check Fermat.FiftyNine.Conservation.LocalReduction827.actualTameReadingAtOrbitPlace827_eq_raw_product
#check Fermat.FiftyNine.Conservation.LocalReduction827.actualTameReading827_eq_inverseOriented_raw_product

#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalReduction827.localReductionHom827,
  IsLocalization.lift
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalReduction827.localReductionHom827_algebraMap,
  IsLocalization.lift_eq
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalReduction827.angularComponent827_globalUnit,
  Fermat.FiftyNine.Conservation.LocalReduction827.localReductionHom827_algebraMap
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalReduction827.tameContext827,
  Fermat.FiftyNine.Conservation.LocalReduction827.angularComponent827
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalReduction827.tameContext827_residueCharacter_eq_residueLog,
  Fermat.FiftyNine.Conservation.CapacityCertificate.symbolPower
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalReduction827.tameContext827_primalResidue_eq_fullOrbitUnitReading,
  Fermat.FiftyNine.Conservation.LocalReduction827.realNorm_firstGeneratedUnit_eq_sq
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalReduction827.tameContext827_primalResidue_eq_fullOrbitUnitReading,
  Fermat.FiftyNine.Conservation.PrimalOrbitResidue827.fullOrbitUnitReading827
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalReduction827.tameContext827_value_globalUnit,
  Fermat.Conservation.TameSymbol.Context.value
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalReduction827.qLocalizationCoordinate827_eq_candidateRepresentative,
  Fermat.FiftyNine.Conservation.DetectorWitness827.ReflectedQRelaxedLocalizationLift827.candidate_represents
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalReduction827.actualTameReadingAtOrbitPlace827_eq_raw_product,
  Fermat.FiftyNine.Conservation.LocalReduction827.tameContext827_value_globalUnit
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalReduction827.actualTameReadingAtOrbitPlace827_eq_raw_product,
  Fermat.FiftyNine.Conservation.LocalReduction827.qLocalizationCoordinate827_eq_candidateRepresentative
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalReduction827.actualTameReading827_eq_inverseOriented_raw_product,
  Fermat.FiftyNine.Conservation.LocalReduction827.actualTameReadingAtOrbitPlace827_eq_raw_product
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalReduction827.actualTameReading827_eq_inverseOriented_raw_product,
  Fermat.FiftyNine.Conservation.OrbitPlace827.indexedPlaceOrbitEquiv827_eq_orbitPlace827Subtype_inv

#check Fermat.FiftyNine.Conservation.FourierPairingProjection827.sum_mul_pureInverse_eq_sum_characterComponent_mul
#check Fermat.FiftyNine.Conservation.FourierPairingProjection827.inverseReindex
#check Fermat.FiftyNine.Conservation.FourierPairingProjection827.fourierCoefficient_inverseReindex
#check Fermat.FiftyNine.Conservation.FourierPairingProjection827.sum_inverseReindex_mul_pureInverse_eq_neg_selectedComponent

#guard_depends_on
  Fermat.FiftyNine.Conservation.FourierPairingProjection827.sum_mul_pureInverse_eq_sum_characterComponent_mul,
  Fermat.FiftyNine.Conservation.SplitPrimeFourier827.fourierCoefficient
#guard_depends_on
  Fermat.FiftyNine.Conservation.FourierPairingProjection827.fourierCoefficient_inverseReindex,
  Fermat.FiftyNine.Conservation.FourierPairingProjection827.inverseReindex
#guard_depends_on
  Fermat.FiftyNine.Conservation.FourierPairingProjection827.fourierCoefficient_inverseReindex,
  Fermat.FiftyNine.Conservation.SplitPrimeFourier827.fourierCoefficient
#guard_depends_on
  Fermat.FiftyNine.Conservation.FourierPairingProjection827.sum_inverseReindex_mul_pureInverse_eq_neg_selectedComponent,
  Fermat.FiftyNine.Conservation.FourierPairingProjection827.sum_mul_pureInverse_eq_sum_characterComponent_mul
#guard_depends_on
  Fermat.FiftyNine.Conservation.FourierPairingProjection827.sum_inverseReindex_mul_pureInverse_eq_neg_selectedComponent,
  Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827.sum_pointwiseProduct_eq_neg_selected

/-! The full 58-by-28 residue table now certifies every nontrivial even
Fourier coefficient of every generated circular unit.  The terminal theorem
transports that nonvanishing through the physically forced inverse place
orientation. -/

#check Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.residueLog_eq_of_symbol
#check Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.orbitGeometricResidue827
#check Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.orbitRealNodeResidue827
#check Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.orbitEdgeResidue827
#check Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.fullGeneratedMatrix827
#check Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.fullGeneratedMatrix827_entry_certificate
#check Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.orbitReductionHom827_generatedUnit_eq
#check Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.fullOrbitUnitReading827_generatedUnit_eq
#check Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.powerCharacter59
#check Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.powerCharacter59_apply
#check Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.firstGenerated_powerTwo_fourierCoefficient_eq
#check Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.fullGeneratedMatrix827_powerFourier_ne_zero
#check Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.exists_powerCharacter59
#check Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.fullOrbitUnitReading827_generatedUnit_fourier_ne_zero_of_even_nontrivial
#check Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.inverseReindex_fullOrbitUnitReading827_generatedUnit_fourier_ne_zero

#guard_depends_on
  Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.residueLog_eq_of_symbol,
  Fermat.FiftyNine.Conservation.CapacityCertificate.residueLog
#guard_depends_on
  Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.orbitReductionHom827_generatedUnit_eq,
  Fermat.FiftyNine.Conservation.Credit.generatedUnit_eq_orbit_ratio
#guard_depends_on
  Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.fullOrbitUnitReading827_generatedUnit_eq,
  Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.orbitReductionHom827_generatedUnit_eq
#guard_depends_on
  Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.fullOrbitUnitReading827_generatedUnit_eq,
  Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.residueLog_eq_of_symbol
#guard_depends_on
  Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.exists_powerCharacter59,
  MonoidHom.map_cyclic
#guard_depends_on
  Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.fullOrbitUnitReading827_generatedUnit_fourier_ne_zero_of_even_nontrivial,
  Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.exists_powerCharacter59
#guard_depends_on
  Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.fullOrbitUnitReading827_generatedUnit_fourier_ne_zero_of_even_nontrivial,
  Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.fullGeneratedMatrix827_powerFourier_ne_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.inverseReindex_fullOrbitUnitReading827_generatedUnit_fourier_ne_zero,
  Fermat.FiftyNine.Conservation.FourierPairingProjection827.fourierCoefficient_inverseReindex
#guard_depends_on
  Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.inverseReindex_fullOrbitUnitReading827_generatedUnit_fourier_ne_zero,
  Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.fullOrbitUnitReading827_generatedUnit_fourier_ne_zero_of_even_nontrivial

#check Fermat.FiftyNine.Conservation.RawOrbitReciprocity827.GlobalReciprocityLaw.pairAt_eq_selectedComponent_of_rawOrbit
#check Fermat.FiftyNine.Conservation.RawOrbitReciprocity827.wild_eq_selectedComponent_of_raw_reciprocity
#check Fermat.FiftyNine.Conservation.RawOrbitReciprocity827.GlobalReciprocityLaw.pairAt_eq_inverseOrientedComponent_of_rawOrbit

#guard_depends_on
  Fermat.FiftyNine.Conservation.RawOrbitReciprocity827.GlobalReciprocityLaw.pairAt_eq_selectedComponent_of_rawOrbit,
  Fermat.FiftyNine.Conservation.FullOrbitReciprocity827.GlobalReciprocityLaw.pairAt_eq_neg_sum_orbitReading
#guard_depends_on
  Fermat.FiftyNine.Conservation.RawOrbitReciprocity827.GlobalReciprocityLaw.pairAt_eq_selectedComponent_of_rawOrbit,
  Fermat.FiftyNine.Conservation.FourierPairingProjection827.sum_mul_pureInverse_eq_sum_characterComponent_mul
#guard_depends_on
  Fermat.FiftyNine.Conservation.RawOrbitReciprocity827.wild_eq_selectedComponent_of_raw_reciprocity,
  Fermat.FiftyNine.Conservation.FourierPairingProjection827.sum_mul_pureInverse_eq_sum_characterComponent_mul
#guard_depends_on
  Fermat.FiftyNine.Conservation.RawOrbitReciprocity827.GlobalReciprocityLaw.pairAt_eq_inverseOrientedComponent_of_rawOrbit,
  Fermat.FiftyNine.Conservation.RawOrbitReciprocity827.GlobalReciprocityLaw.pairAt_eq_selectedComponent_of_rawOrbit
#guard_depends_on
  Fermat.FiftyNine.Conservation.RawOrbitReciprocity827.GlobalReciprocityLaw.pairAt_eq_inverseOrientedComponent_of_rawOrbit,
  Fermat.FiftyNine.Conservation.FourierPairingProjection827.inverseReindex

#check Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827.orientedPrimalMode827
#check Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827.inverseOrientedPrimalUnitWave827
#check Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827.inverseOrientedPrimalUnitWave827_isPureCharacter
#check Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827.tameOrbitBasePlace827
#check Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827.actualTameOrbitValue827
#check Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827.actualTameOrbitValue827_eq_raw_product
#check Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827.actualReflectedLocalizationWave827_isPureCharacter
#check Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827.sum_actualTameOrbitValue827_eq_neg_selectedProduct
#check Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827.wild_eq_selectedProduct_of_actualTameOrbitReciprocity827

#guard_depends_on
  Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827.inverseOrientedPrimalUnitWave827,
  Fermat.FiftyNine.Conservation.LocalReduction827.inverseOrientedFullOrbitUnitReading827
#guard_depends_on
  Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827.actualTameOrbitValue827,
  Fermat.FiftyNine.Conservation.LocalReduction827.tameContext827
#guard_depends_on
  Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827.actualTameOrbitValue827_eq_raw_product,
  Fermat.FiftyNine.Conservation.LocalReduction827.actualTameReading827_eq_inverseOriented_raw_product
#guard_depends_on
  Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827.actualReflectedLocalizationWave827_isPureCharacter,
  Fermat.FiftyNine.Conservation.SplitPrimeFourier827.projectedLocalization_isPureCharacter
#guard_depends_on
  Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827.sum_actualTameOrbitValue827_eq_neg_selectedProduct,
  Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827.actualTameOrbitValue827_eq_raw_product
#guard_depends_on
  Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827.sum_actualTameOrbitValue827_eq_neg_selectedProduct,
  Fermat.FiftyNine.Conservation.FourierPairingProjection827.sum_mul_pureInverse_eq_sum_characterComponent_mul
#guard_depends_on
  Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827.wild_eq_selectedProduct_of_actualTameOrbitReciprocity827,
  Fermat.FiftyNine.Conservation.RawOrbitReciprocity827.wild_eq_selectedComponent_of_raw_reciprocity

/-! The nonvanishing composition keeps the reciprocity equation visible and
joins the two independently certified local factors.  It proves that the
complete actual tame sum, and hence any wild reading satisfying that exact
equation, cannot vanish in a nontrivial even mode. -/

#check Fermat.FiftyNine.Conservation.ExplicitTameOrbitNonvanishing827.inverseOrientedPrimalUnitWave827_ne_zero_of_even_nontrivial
#check Fermat.FiftyNine.Conservation.ExplicitTameOrbitNonvanishing827.actualReflectedLocalizationWave827_ne_zero_of_lift
#check Fermat.FiftyNine.Conservation.ExplicitTameOrbitNonvanishing827.selectedProduct_actualTameOrbit827_ne_zero
#check Fermat.FiftyNine.Conservation.ExplicitTameOrbitNonvanishing827.sum_actualTameOrbitValue827_ne_zero
#check Fermat.FiftyNine.Conservation.ExplicitTameOrbitNonvanishing827.wild_ne_zero_of_actualTameOrbitReciprocity827

#guard_depends_on
  Fermat.FiftyNine.Conservation.ExplicitTameOrbitNonvanishing827.inverseOrientedPrimalUnitWave827_ne_zero_of_even_nontrivial,
  Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827.inverseReindex_fullOrbitUnitReading827_generatedUnit_fourier_ne_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.ExplicitTameOrbitNonvanishing827.actualReflectedLocalizationWave827_ne_zero_of_lift,
  Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827.qLocalizationCoordinate_ne_zero_at_every_place_of_lift
#guard_depends_on
  Fermat.FiftyNine.Conservation.ExplicitTameOrbitNonvanishing827.selectedProduct_actualTameOrbit827_ne_zero,
  Fermat.FiftyNine.Conservation.ExplicitTameOrbitNonvanishing827.inverseOrientedPrimalUnitWave827_ne_zero_of_even_nontrivial
#guard_depends_on
  Fermat.FiftyNine.Conservation.ExplicitTameOrbitNonvanishing827.selectedProduct_actualTameOrbit827_ne_zero,
  Fermat.FiftyNine.Conservation.ExplicitTameOrbitNonvanishing827.actualReflectedLocalizationWave827_ne_zero_of_lift
#guard_depends_on
  Fermat.FiftyNine.Conservation.ExplicitTameOrbitNonvanishing827.sum_actualTameOrbitValue827_ne_zero,
  Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827.sum_actualTameOrbitValue827_eq_neg_selectedProduct
#guard_depends_on
  Fermat.FiftyNine.Conservation.ExplicitTameOrbitNonvanishing827.sum_actualTameOrbitValue827_ne_zero,
  Fermat.FiftyNine.Conservation.ExplicitTameOrbitNonvanishing827.selectedProduct_actualTameOrbit827_ne_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.ExplicitTameOrbitNonvanishing827.wild_ne_zero_of_actualTameOrbitReciprocity827,
  Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827.wild_eq_selectedProduct_of_actualTameOrbitReciprocity827
#guard_depends_on
  Fermat.FiftyNine.Conservation.ExplicitTameOrbitNonvanishing827.wild_ne_zero_of_actualTameOrbitReciprocity827,
  Fermat.FiftyNine.Conservation.ExplicitTameOrbitNonvanishing827.selectedProduct_actualTameOrbit827_ne_zero

/-! The complementary tame-context construction covers every height-one
place away from 59 using its literal ideal-quotient residue field.  Applied
to the same circular unit and retained q-relaxed representative, its final
theorem proves actual local-symbol silence outside the 59/827 support. -/

#check Fermat.FiftyNine.Conservation.CyclotomicTameContext59.Place
#check Fermat.FiftyNine.Conservation.CyclotomicTameContext59.Residue
#check Fermat.FiftyNine.Conservation.CyclotomicTameContext59.LocalRing
#check Fermat.FiftyNine.Conservation.CyclotomicTameContext59.localReductionHom
#check Fermat.FiftyNine.Conservation.CyclotomicTameContext59.localReductionHom_algebraMap
#check Fermat.FiftyNine.Conservation.CyclotomicTameContext59.chosenUniformizer
#check Fermat.FiftyNine.Conservation.CyclotomicTameContext59.chosenUniformizer_spec
#check Fermat.FiftyNine.Conservation.CyclotomicTameContext59.chosenUniformizer_ne_zero
#check Fermat.FiftyNine.Conservation.CyclotomicTameContext59.chosenUniformizerUnit
#check Fermat.FiftyNine.Conservation.CyclotomicTameContext59.valuationOfNeZero_chosenUniformizerUnit
#check Fermat.FiftyNine.Conservation.CyclotomicTameContext59.localUnitPart
#check Fermat.FiftyNine.Conservation.CyclotomicTameContext59.angularComponent
#check Fermat.FiftyNine.Conservation.CyclotomicTameContext59.absNorm_coprime_59_of_not_over59
#check Fermat.FiftyNine.Conservation.CyclotomicTameContext59.residueChar_ne_59
#check Fermat.FiftyNine.Conservation.CyclotomicTameContext59.residueRoot_isPrimitive
#check Fermat.FiftyNine.Conservation.CyclotomicTameContext59.residueRootUnit
#check Fermat.FiftyNine.Conservation.CyclotomicTameContext59.residueRootUnit_isPrimitive
#check Fermat.FiftyNine.Conservation.CyclotomicTameContext59.card_sub_one_dvd_59
#check Fermat.FiftyNine.Conservation.CyclotomicTameContext59.context
#check Fermat.FiftyNine.Conservation.CyclotomicTameContext59.context_ord
#check Fermat.FiftyNine.Conservation.CyclotomicTameContext59.rhoQ827
#check Fermat.FiftyNine.Conservation.CyclotomicTameContext59.value_firstGenerated_candidate_eq_zero_outside_support

#guard_depends_on
  Fermat.FiftyNine.Conservation.CyclotomicTameContext59.localReductionHom,
  IsLocalization.lift
#guard_depends_on
  Fermat.FiftyNine.Conservation.CyclotomicTameContext59.localReductionHom_algebraMap,
  IsLocalization.lift_eq
#guard_depends_on
  Fermat.FiftyNine.Conservation.CyclotomicTameContext59.localUnitPart,
  Fermat.FiftyNine.Conservation.CyclotomicTameContext59.valuationOfNeZero_chosenUniformizerUnit
#guard_depends_on
  Fermat.FiftyNine.Conservation.CyclotomicTameContext59.angularComponent,
  Fermat.FiftyNine.Conservation.CyclotomicTameContext59.localReductionHom
#guard_depends_on
  Fermat.FiftyNine.Conservation.CyclotomicTameContext59.angularComponent,
  Fermat.FiftyNine.Conservation.CyclotomicTameContext59.localUnitPart
#guard_depends_on
  Fermat.FiftyNine.Conservation.CyclotomicTameContext59.absNorm_coprime_59_of_not_over59,
  Ideal.exists_isMaximal_dvd_of_dvd_absNorm
#guard_depends_on
  Fermat.FiftyNine.Conservation.CyclotomicTameContext59.residueChar_ne_59,
  Ideal.ringChar_quot
#guard_depends_on
  Fermat.FiftyNine.Conservation.CyclotomicTameContext59.residueRoot_isPrimitive,
  IsPrimitiveRoot.idealQuotient_mk
#guard_depends_on
  Fermat.FiftyNine.Conservation.CyclotomicTameContext59.card_sub_one_dvd_59,
  orderOf_dvd_card
#guard_depends_on
  Fermat.FiftyNine.Conservation.CyclotomicTameContext59.context,
  Fermat.FiftyNine.Conservation.CyclotomicTameContext59.residueRootUnit_isPrimitive
#guard_depends_on
  Fermat.FiftyNine.Conservation.CyclotomicTameContext59.value_firstGenerated_candidate_eq_zero_outside_support,
  Fermat.FiftyNine.Conservation.DetectorWitness827.ReflectedQRelaxedLocalizationLift827.outside_reading_eq_zero_of_both_units

/-! The actual tame ledger retains those orbit values on their genuine
height-one places.  Its support is proved to lie over 827, its aggregate is
the complete orbit sum, and omitted nonwild places agree with the canonical
local tame symbol rather than being silenced by representation alone. -/

#check Fermat.FiftyNine.Conservation.ActualTameLedger827.tameOrbitPlace827
#check Fermat.FiftyNine.Conservation.ActualTameLedger827.actualTameLedger827
#check Fermat.FiftyNine.Conservation.ActualTameLedger827.actualTameLedger827_apply_orbit
#check Fermat.FiftyNine.Conservation.ActualTameLedger827.actualTameLedger827_apply_eq_zero_of_not_over827
#check Fermat.FiftyNine.Conservation.ActualTameLedger827.actualTameLedger827_support_subset_placesOver827
#check Fermat.FiftyNine.Conservation.ActualTameLedger827.actualTameLedger827_sum_eq_orbit_sum
#check Fermat.FiftyNine.Conservation.ActualTameLedger827.wild_add_actualTameLedger827_sum_eq_zero_iff
#check Fermat.FiftyNine.Conservation.ActualTameLedger827.canonicalTameValue_eq_actualTameLedger827_of_outside_support

#guard_depends_on
  Fermat.FiftyNine.Conservation.ActualTameLedger827.actualTameLedger827,
  Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827.actualTameOrbitValue827
#guard_depends_on
  Fermat.FiftyNine.Conservation.ActualTameLedger827.actualTameLedger827_apply_orbit,
  Fermat.FiftyNine.Conservation.ActualTameLedger827.actualTameLedger827
#guard_depends_on
  Fermat.FiftyNine.Conservation.ActualTameLedger827.actualTameLedger827_apply_orbit,
  Fermat.FiftyNine.Conservation.SplitPrimeFourier827.indexedPlaceOrbitEquiv827
#guard_depends_on
  Fermat.FiftyNine.Conservation.ActualTameLedger827.actualTameLedger827_apply_eq_zero_of_not_over827,
  Fermat.FiftyNine.Conservation.ActualTameLedger827.actualTameLedger827
#guard_depends_on
  Fermat.FiftyNine.Conservation.ActualTameLedger827.actualTameLedger827_support_subset_placesOver827,
  Fermat.FiftyNine.Conservation.ActualTameLedger827.actualTameLedger827_apply_eq_zero_of_not_over827
#guard_depends_on
  Fermat.FiftyNine.Conservation.ActualTameLedger827.actualTameLedger827_sum_eq_orbit_sum,
  Fermat.FiftyNine.Conservation.ActualTameLedger827.actualTameLedger827
#guard_depends_on
  Fermat.FiftyNine.Conservation.ActualTameLedger827.wild_add_actualTameLedger827_sum_eq_zero_iff,
  Fermat.FiftyNine.Conservation.ActualTameLedger827.actualTameLedger827_sum_eq_orbit_sum
#guard_depends_on
  Fermat.FiftyNine.Conservation.ActualTameLedger827.canonicalTameValue_eq_actualTameLedger827_of_outside_support,
  Fermat.FiftyNine.Conservation.CyclotomicTameContext59.value_firstGenerated_candidate_eq_zero_outside_support
#guard_depends_on
  Fermat.FiftyNine.Conservation.ActualTameLedger827.canonicalTameValue_eq_actualTameLedger827_of_outside_support,
  Fermat.FiftyNine.Conservation.ActualTameLedger827.actualTameLedger827_apply_eq_zero_of_not_over827

/-! Nonvanishing now reaches the honest finite-support ledger itself.  The
final theorem consumes a visible reciprocity equation on that ledger and
forces its wild contribution to be nonzero. -/

#check Fermat.FiftyNine.Conservation.ActualTameLedgerNonvanishing827.actualTameLedger827_sum_ne_zero
#check Fermat.FiftyNine.Conservation.ActualTameLedgerNonvanishing827.actualTameLedger827_ne_zero
#check Fermat.FiftyNine.Conservation.ActualTameLedgerNonvanishing827.wild_ne_zero_of_actualTameLedgerReciprocity827

#guard_depends_on
  Fermat.FiftyNine.Conservation.ActualTameLedgerNonvanishing827.actualTameLedger827_sum_ne_zero,
  Fermat.FiftyNine.Conservation.ActualTameLedger827.actualTameLedger827_sum_eq_orbit_sum
#guard_depends_on
  Fermat.FiftyNine.Conservation.ActualTameLedgerNonvanishing827.actualTameLedger827_sum_ne_zero,
  Fermat.FiftyNine.Conservation.ExplicitTameOrbitNonvanishing827.sum_actualTameOrbitValue827_ne_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.ActualTameLedgerNonvanishing827.actualTameLedger827_ne_zero,
  Fermat.FiftyNine.Conservation.ActualTameLedgerNonvanishing827.actualTameLedger827_sum_ne_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.ActualTameLedgerNonvanishing827.wild_ne_zero_of_actualTameLedgerReciprocity827,
  Fermat.FiftyNine.Conservation.ExplicitTameOrbitNonvanishing827.wild_ne_zero_of_actualTameOrbitReciprocity827
#guard_depends_on
  Fermat.FiftyNine.Conservation.ActualTameLedgerNonvanishing827.wild_ne_zero_of_actualTameLedgerReciprocity827,
  Fermat.FiftyNine.Conservation.ActualTameLedger827.wild_add_actualTameLedger827_sum_eq_zero_iff

/-! The unique irregular `(59, 44)` channel now has an honest p-adic
Teichmuller character.  Reduction seats its reflected primal wave in power
mode `44`, so parity, nontriviality, and the fixed-root nonvanishing chain no
longer require separate character hypotheses. -/

#check Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.canonicalTeichmullerCharacter59
#check Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.canonicalTeichmullerCharacter59_reduction_apply
#check Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.reducedCharacter59_canonicalTeichmullerCharacter59
#check Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.reducedCharacter59_pow
#check Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.reducedCharacter59_reflectedCharacter
#check Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.irregularCharacter59
#check Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.reducedCharacter59_irregularCharacter59
#check Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.orientedPrimalMode827_canonical_irregular
#check Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.orientedPrimalMode827_canonical_irregular_even
#check Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.orientedPrimalMode827_canonical_irregular_ne_one
#check Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.inverseOrientedPrimalUnitWave827_canonical_irregular_ne_zero
#check Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.selectedProduct_actualTameOrbit827_canonical_irregular_ne_zero
#check Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.sum_actualTameOrbitValue827_canonical_irregular_ne_zero
#check Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.wild_ne_zero_of_actualTameOrbitReciprocity827_canonical_irregular
#check Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.actualTameLedger827_canonical_irregular_sum_ne_zero
#check Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.actualTameLedger827_canonical_irregular_ne_zero
#check Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.wild_ne_zero_of_actualTameLedgerReciprocity827_canonical_irregular

#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.canonicalTeichmullerCharacter59,
  WittVector.teichmuller
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.canonicalTeichmullerCharacter59_reduction_apply,
  WittVector.toPadicInt
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.reducedCharacter59_canonicalTeichmullerCharacter59,
  Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.canonicalTeichmullerCharacter59_reduction_apply
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.reducedCharacter59_irregularCharacter59,
  Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.reducedCharacter59_pow
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.orientedPrimalMode827_canonical_irregular,
  Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.reducedCharacter59_reflectedCharacter
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.orientedPrimalMode827_canonical_irregular_even,
  Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.orientedPrimalMode827_canonical_irregular
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.orientedPrimalMode827_canonical_irregular_ne_one,
  Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.orientedPrimalMode827_canonical_irregular
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.inverseOrientedPrimalUnitWave827_canonical_irregular_ne_zero,
  Fermat.FiftyNine.Conservation.ExplicitTameOrbitNonvanishing827.inverseOrientedPrimalUnitWave827_ne_zero_of_even_nontrivial
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.selectedProduct_actualTameOrbit827_canonical_irregular_ne_zero,
  Fermat.FiftyNine.Conservation.ExplicitTameOrbitNonvanishing827.selectedProduct_actualTameOrbit827_ne_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.sum_actualTameOrbitValue827_canonical_irregular_ne_zero,
  Fermat.FiftyNine.Conservation.ExplicitTameOrbitNonvanishing827.sum_actualTameOrbitValue827_ne_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.actualTameLedger827_canonical_irregular_sum_ne_zero,
  Fermat.FiftyNine.Conservation.ActualTameLedgerNonvanishing827.actualTameLedger827_sum_ne_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.actualTameLedger827_canonical_irregular_ne_zero,
  Fermat.FiftyNine.Conservation.ActualTameLedgerNonvanishing827.actualTameLedger827_ne_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.wild_ne_zero_of_actualTameLedgerReciprocity827_canonical_irregular,
  Fermat.FiftyNine.Conservation.ActualTameLedgerNonvanishing827.wild_ne_zero_of_actualTameLedgerReciprocity827

/-! Conjugation-fixed divisor classes are 59-divisible through the checked
maximal-real class-number certificate.  Principalization then yields an
honest field unit whose valuation vector is the negative divisor modulo 59;
the conjugate pair above 827 seats that unit in Mathlib's literal relaxed
Selmer carrier with a nonzero selected localization. -/

#check Fermat.FiftyNine.Conservation.ConjugationFixedClassDivisibility59.exists_class_pow_fiftyNine_eq_of_conjugation_fixed
#check Fermat.FiftyNine.Conservation.ConjugationFixedPrincipalDivisor59.IntegerIdeal59
#check Fermat.FiftyNine.Conservation.ConjugationFixedPrincipalDivisor59.exists_principal_times_ideal_pow_fiftyNine_eq
#check Fermat.FiftyNine.Conservation.ConjugationFixedPrincipalDivisor59.count_spanSingleton_eq_neg_valuation
#check Fermat.FiftyNine.Conservation.ConjugationFixedPrincipalDivisor59.exists_unit_valuation_mod_fiftyNine_eq_neg_count
#check Fermat.FiftyNine.Conservation.ConjugatePairSource827.cmConjugateIdeal827
#check Fermat.FiftyNine.Conservation.ConjugatePairSource827.cmConjugateIdeal827_involutive
#check Fermat.FiftyNine.Conservation.ConjugatePairSource827.cmConjugateIdeal827_under_int
#check Fermat.FiftyNine.Conservation.ConjugatePairSource827.cmConjugatePlace827
#check Fermat.FiftyNine.Conservation.ConjugatePairSource827.conjugatePairIdeal827
#check Fermat.FiftyNine.Conservation.ConjugatePairSource827.conjugatePairIdeal827_fixed
#check Fermat.FiftyNine.Conservation.ConjugatePairSource827.conjugatePairIdeal827_count
#check Fermat.FiftyNine.Conservation.ConjugatePairSource827.conjugatePairIdeal827_count_eq_zero_of_not_mem
#check Fermat.FiftyNine.Conservation.ConjugatePairSource827.neg_conjugatePairIdeal827_count_selected_ne_zero
#check Fermat.FiftyNine.Conservation.ConjugatePairSource827.exists_plus_principal_data827
#check Fermat.FiftyNine.Conservation.ConjugatePairSource827.conjugatePairIdeal827_class_eq_one
#check Fermat.FiftyNine.Conservation.ConjugatePairSource827.extendedRealRoot827_class_eq_one
#check Fermat.FiftyNine.Conservation.ConjugatePairSource827.exists_sUnit_eq_kummerClass_of_plus_principal_data827
#check Fermat.FiftyNine.Conservation.ConjugatePairSource827.exists_classSilent_conjugatePairUnit827
#check Fermat.FiftyNine.Conservation.ConjugatePairSource827.conjugatePairUnit827
#check Fermat.FiftyNine.Conservation.ConjugatePairSource827.conjugatePairUnit827_valuation_mod
#check Fermat.FiftyNine.Conservation.ConjugatePairSource827.conjugatePairSUnit827
#check Fermat.FiftyNine.Conservation.ConjugatePairSource827.conjugatePairSUnit827_kummerClass
#check Fermat.FiftyNine.Conservation.ConjugatePairSource827.conjugatePairSource827
#check Fermat.FiftyNine.Conservation.ConjugatePairSource827.fromSUnitLift_conjugatePairSUnit827
#check Fermat.FiftyNine.Conservation.ConjugatePairSource827.supportValuationAt_conjugatePairSource827_ne_zero
#check Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.valuationOfNeZero_cyclotomic59

#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugationFixedClassDivisibility59.exists_class_pow_fiftyNine_eq_of_conjugation_fixed,
  Fermat.FiftyNine.Conservation.Fold.not_dvd_plusClassNumber
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugationFixedClassDivisibility59.exists_class_pow_fiftyNine_eq_of_conjugation_fixed,
  Fermat.Conservation.Credit.Fold.map_relativeNorm_eq_mul_conjugate
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugationFixedPrincipalDivisor59.exists_principal_times_ideal_pow_fiftyNine_eq,
  Fermat.FiftyNine.Conservation.ConjugationFixedClassDivisibility59.exists_class_pow_fiftyNine_eq_of_conjugation_fixed
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugationFixedPrincipalDivisor59.count_spanSingleton_eq_neg_valuation,
  FractionalIdeal.count_well_defined
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugationFixedPrincipalDivisor59.exists_unit_valuation_mod_fiftyNine_eq_neg_count,
  Fermat.FiftyNine.Conservation.ConjugationFixedPrincipalDivisor59.exists_principal_times_ideal_pow_fiftyNine_eq
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugationFixedPrincipalDivisor59.exists_unit_valuation_mod_fiftyNine_eq_neg_count,
  Fermat.FiftyNine.Conservation.ConjugationFixedPrincipalDivisor59.count_spanSingleton_eq_neg_valuation
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.cmConjugateIdeal827_involutive,
  NumberField.IsCMField.complexConj_apply_apply
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.conjugatePairIdeal827_fixed,
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.cmConjugateIdeal827
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.conjugatePairIdeal827_count,
  FractionalIdeal.count_mul
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.neg_conjugatePairIdeal827_count_selected_ne_zero,
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.conjugatePairIdeal827_count
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.exists_plus_principal_data827,
  Fermat.FiftyNine.Conservation.Fold.not_dvd_plusClassNumber
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.exists_plus_principal_data827,
  Fermat.Conservation.Credit.Fold.map_relativeNorm_eq_mul_conjugate
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.conjugatePairIdeal827_class_eq_one,
  IsDedekindDomain.selmerGroup.classGroupToObstructionTarget_primeClass
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.extendedRealRoot827_class_eq_one,
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.conjugatePairIdeal827_class_eq_one
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.exists_sUnit_eq_kummerClass_of_plus_principal_data827,
  IsDedekindDomain.selmerGroup.principalDivisorAway_ker
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.exists_classSilent_conjugatePairUnit827,
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.exists_plus_principal_data827
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.exists_classSilent_conjugatePairUnit827,
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.exists_sUnit_eq_kummerClass_of_plus_principal_data827
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.conjugatePairUnit827,
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.exists_classSilent_conjugatePairUnit827
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.conjugatePairSUnit827,
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.exists_classSilent_conjugatePairUnit827
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.conjugatePairSUnit827_kummerClass,
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.exists_classSilent_conjugatePairUnit827
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.conjugatePairSource827,
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.conjugatePairUnit827_valuation_mod
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.fromSUnitLift_conjugatePairSUnit827,
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.conjugatePairSUnit827_kummerClass
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.supportValuationAt_conjugatePairSource827_ne_zero,
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.neg_conjugatePairIdeal827_count_selected_ne_zero

/-! Complex conjugation on the sparse 827 source is not an extra place
permutation: it is the canonical cyclotomic action of `-1`.  The regular
58-place orbit therefore identifies the conjugate place with the explicit
`-1` coordinate and proves that no 827 place is fixed. -/

#check Fermat.FiftyNine.Conservation.ConjugatePlaceOrbit827.ringOfIntegersComplexConj_eq_cyclotomic_negOne59
#check Fermat.FiftyNine.Conservation.ConjugatePlaceOrbit827.cmConjugatePlace827_val_eq_cyclotomic_negOne
#check Fermat.FiftyNine.Conservation.ConjugatePlaceOrbit827.cmConjugatePlace827_eq_cyclotomic_negOne
#check Fermat.FiftyNine.Conservation.ConjugatePlaceOrbit827.cmConjugatePlace827_eq_indexedPlaceOrbit_negOne
#check Fermat.FiftyNine.Conservation.ConjugatePlaceOrbit827.cmConjugatePlace827_ne_self

#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePlaceOrbit827.ringOfIntegersComplexConj_eq_cyclotomic_negOne59,
  NumberField.IsCMField.unitsComplexConj_torsion
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePlaceOrbit827.ringOfIntegersComplexConj_eq_cyclotomic_negOne59,
  KummerCriterion.cyclotomicSigmaOfUnit_apply_zeta
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePlaceOrbit827.cmConjugatePlace827_val_eq_cyclotomic_negOne,
  Fermat.FiftyNine.Conservation.ConjugatePlaceOrbit827.ringOfIntegersComplexConj_eq_cyclotomic_negOne59
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePlaceOrbit827.cmConjugatePlace827_eq_cyclotomic_negOne,
  Fermat.FiftyNine.Conservation.ConjugatePlaceOrbit827.cmConjugatePlace827_val_eq_cyclotomic_negOne
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePlaceOrbit827.cmConjugatePlace827_eq_indexedPlaceOrbit_negOne,
  Fermat.FiftyNine.Conservation.CyclotomicLocalizationEquivariance827.indexedPlaceOrbitEquiv827_eq_cyclotomicPlaceEquiv59
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePlaceOrbit827.cmConjugatePlace827_ne_self,
  Fermat.FiftyNine.Conservation.ConjugatePlaceOrbit827.cmConjugatePlace827_eq_indexedPlaceOrbit_negOne

/-! The sparse source now survives the genuine canonical reflected
idempotent without a supplied mode certificate: its orbit coordinates are
literally `-1` at `1` and `-1`, hence its selected projected coordinate is
the nonzero normalized scalar `-2/58`. -/

#check Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827.supportValuationAt_conjugatePairSource827_eq
#check Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827.supportValuationAt_cyclotomic_apply
#check Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827.cyclotomicPlaceEquiv59_eq_self_iff
#check Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827.cyclotomicPlaceEquiv59_injective_at
#check Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827.conjugatePairSource827_orbit_coordinate
#check Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827.conjugatePairSource827_weighted_sum
#check Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827.supportValuationAt_characterProjectorAt_eq_sum
#check Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827.canonical_projected_conjugatePair_coordinate_eq
#check Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827.projectedNormalization59_ne_zero
#check Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827.canonical_projected_conjugatePair_coordinate_ne_zero

#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827.supportValuationAt_conjugatePairSource827_eq,
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.conjugatePairUnit827_valuation_mod
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827.supportValuationAt_cyclotomic_apply,
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicValuationCovariance59
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827.cyclotomicPlaceEquiv59_eq_self_iff,
  Fermat.FiftyNine.Conservation.CyclotomicLocalizationEquivariance827.indexedPlaceOrbitEquiv827_eq_cyclotomicPlaceEquiv59
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827.cyclotomicPlaceEquiv59_injective_at,
  Fermat.FiftyNine.Conservation.CyclotomicLocalizationEquivariance827.indexedPlaceOrbitEquiv827_eq_cyclotomicPlaceEquiv59
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827.conjugatePairSource827_orbit_coordinate,
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827.supportValuationAt_cyclotomic_apply
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827.conjugatePairSource827_orbit_coordinate,
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.conjugatePairIdeal827_count
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827.conjugatePairSource827_weighted_sum,
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827.conjugatePairSource827_orbit_coordinate
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827.supportValuationAt_characterProjectorAt_eq_sum,
  Fermat.Conservation.InvolutiveBase.characterIdempotent
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827.canonical_projected_conjugatePair_coordinate_eq,
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827.conjugatePairSource827_weighted_sum
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827.canonical_projected_conjugatePair_coordinate_eq,
  Fermat.FiftyNine.Conservation.ConjugatePlaceOrbit827.cmConjugatePlace827_val_eq_cyclotomic_negOne
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827.projectedNormalization59_ne_zero,
  invOf_mul_self
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827.canonical_projected_conjugatePair_coordinate_ne_zero,
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827.canonical_projected_conjugatePair_coordinate_eq
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827.canonical_projected_conjugatePair_coordinate_ne_zero,
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827.projectedNormalization59_ne_zero

/-! Independently, the retained literal S-unit provenance is stable under
the cyclotomic action and p-adic character idempotent.  The projected source
therefore lies in the finite-S kernel, so its canonical class obstruction is
the identity and its additive relaxed class projection is zero. -/

#check Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827.cyclotomicSUnit827
#check Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827.fromSUnitLift_cyclotomicSUnit827
#check Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827.QRelaxedSUnitRange827
#check Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827.conjugatePairSource827_mem_sUnitRange
#check Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827.cyclotomic_conjugatePairSource827_mem_sUnitRange
#check Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827.padicInt_smul_mem_sUnitRange
#check Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827.characterProjector_conjugatePairSource827_mem_sUnitRange
#check Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827.conjugatePairDetectorSUnit827
#check Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827.projectedCandidateSClassObstruction827_conjugatePair_canonical_eq_one
#check Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827.relaxedClassProjection827_conjugatePair_canonical_eq_zero

#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827.cyclotomicSUnit827,
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.valuationOfNeZero_cyclotomic59
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827.fromSUnitLift_cyclotomicSUnit827,
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicKummerHom59_mk
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827.conjugatePairSource827_mem_sUnitRange,
  Fermat.FiftyNine.Conservation.ConjugatePairSource827.fromSUnitLift_conjugatePairSUnit827
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827.cyclotomic_conjugatePairSource827_mem_sUnitRange,
  Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827.fromSUnitLift_cyclotomicSUnit827
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827.characterProjector_conjugatePairSource827_mem_sUnitRange,
  Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827.cyclotomic_conjugatePairSource827_mem_sUnitRange
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827.characterProjector_conjugatePairSource827_mem_sUnitRange,
  Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827.padicInt_smul_mem_sUnitRange
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827.projectedCandidateSClassObstruction827_conjugatePair_canonical_eq_one,
  Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827.characterProjector_conjugatePairSource827_mem_sUnitRange
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827.projectedCandidateSClassObstruction827_conjugatePair_canonical_eq_one,
  IsDedekindDomain.selmerGroup.toSClass_ker
#guard_depends_on
  Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827.relaxedClassProjection827_conjugatePair_canonical_eq_zero,
  Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827.projectedCandidateSClassObstruction827_conjugatePair_canonical_eq_one

/-! The two independent receipts now meet in the repository's literal
finite-S lift constructor.  The resulting canonical `(59, 44)` reflected
lift is unconditional, including at the explicit tame-orbit base place; no
lift provider, class certificate, or localization functional is supplied. -/

#check Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827.canonicalConjugatePairLift827
#check Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827.canonicalBaseConjugatePairLift827
#check Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827.nonempty_canonicalConjugatePairLift827
#check Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827.canonical_classSilentPointedCoordinate827_ne_zero

#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827.canonicalConjugatePairLift827,
  Fermat.FiftyNine.Conservation.DetectorWitness827.ReflectedQRelaxedLocalizationLift827.ofSource_of_sClassObstruction_eq_one
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827.canonicalConjugatePairLift827,
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827.canonical_projected_conjugatePair_coordinate_ne_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827.canonicalConjugatePairLift827,
  Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827.projectedCandidateSClassObstruction827_conjugatePair_canonical_eq_one
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827.canonicalBaseConjugatePairLift827,
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827.canonicalConjugatePairLift827
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827.nonempty_canonicalConjugatePairLift827,
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827.canonicalBaseConjugatePairLift827
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827.canonical_classSilentPointedCoordinate827_ne_zero,
  Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827.nonempty_cyclotomicReflectedQRelaxedLocalizationLift827_iff
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827.canonical_classSilentPointedCoordinate827_ne_zero,
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827.nonempty_canonicalConjugatePairLift827

/-! The canonical lift is seated at the explicit tame-orbit base place and
retains the literal conjugate-pair source.  Canonical Fourier seating then
constructs the pointed Poitou--Tate incidence package, proves its boundary
functional nonzero, and inhabits the normalized reflected fiber.  This is
geometric downstream composition, not a reciprocity or 7a endpoint. -/

#check Fermat.FiftyNine.Conservation.CanonicalConjugatePairIncidence827.canonicalBaseConjugatePairLift827_selectedPlace
#check Fermat.FiftyNine.Conservation.CanonicalConjugatePairIncidence827.canonicalBaseConjugatePairLift827_source
#check Fermat.FiftyNine.Conservation.CanonicalConjugatePairIncidence827.canonicalConjugatePairPointedIncidence827
#check Fermat.FiftyNine.Conservation.CanonicalConjugatePairIncidence827.canonicalConjugatePairBoundaryFunctional827_ne_zero
#check Fermat.FiftyNine.Conservation.CanonicalConjugatePairIncidence827.canonicalConjugatePairNormalizedReflectedFiber827_nonempty

#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairIncidence827.canonicalConjugatePairPointedIncidence827,
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedPointedIncidence59OfLiftCanonical
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairIncidence827.canonicalConjugatePairPointedIncidence827,
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827.canonicalBaseConjugatePairLift827
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairIncidence827.canonicalConjugatePairBoundaryFunctional827_ne_zero,
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedBoundaryFunctional59_ne_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairIncidence827.canonicalConjugatePairBoundaryFunctional827_ne_zero,
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairIncidence827.canonicalConjugatePairPointedIncidence827
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairIncidence827.canonicalConjugatePairBoundaryFunctional827_ne_zero,
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedQLocalizationEquivariance827
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairIncidence827.canonicalConjugatePairNormalizedReflectedFiber827_nonempty,
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedReflectedFiber59_nonempty
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairIncidence827.canonicalConjugatePairNormalizedReflectedFiber827_nonempty,
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairIncidence827.canonicalConjugatePairPointedIncidence827

/-! Installing the same canonical lift in the historical normalized branch
removes its former geometric lift premise, but it does not make that branch
an unconditional 7a proof.  Its one-column reciprocity still annihilates the
normalized coefficient, so the remaining processing premise is exactly
equivalent to vanishing of the complete class-valued gauge.  The final 7a
endpoint below remains deliberately conditional on that circular premise. -/

#check Fermat.FiftyNine.Conservation.CanonicalConjugatePairNormalizedEndpoint59.CanonicalConjugatePairTameSilenceReciprocity59
#check Fermat.FiftyNine.Conservation.CanonicalConjugatePairNormalizedEndpoint59.canonicalConjugatePairNormalizedWildCoefficient59
#check Fermat.FiftyNine.Conservation.CanonicalConjugatePairNormalizedEndpoint59.canonicalConjugatePairNormalizedWildCoefficient59_eq_zero
#check Fermat.FiftyNine.Conservation.CanonicalConjugatePairNormalizedEndpoint59.canonicalConjugatePairProcessesAtLeastSevenA_iff_gauge_eq_zero
#check Fermat.FiftyNine.Conservation.CanonicalConjugatePairNormalizedEndpoint59.vandiverSevenA_of_normalizedContinuousCanonicalConjugatePair

#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairNormalizedEndpoint59.canonicalConjugatePairNormalizedWildCoefficient59,
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildCoefficientOfCanonicalLift59
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairNormalizedEndpoint59.canonicalConjugatePairNormalizedWildCoefficient59,
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827.canonicalBaseConjugatePairLift827
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairNormalizedEndpoint59.canonicalConjugatePairNormalizedWildCoefficient59_eq_zero,
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildCoefficientOfCanonicalLift59_eq_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairNormalizedEndpoint59.canonicalConjugatePairProcessesAtLeastSevenA_iff_gauge_eq_zero,
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedCanonicalLiftProcessesAtLeastSevenA_iff_gauge_eq_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairNormalizedEndpoint59.canonicalConjugatePairProcessesAtLeastSevenA_iff_gauge_eq_zero,
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827.canonicalBaseConjugatePairLift827
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairNormalizedEndpoint59.vandiverSevenA_of_normalizedContinuousCanonicalConjugatePair,
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.vandiverSevenA_of_normalizedContinuousCanonicalLift
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairNormalizedEndpoint59.vandiverSevenA_of_normalizedContinuousCanonicalConjugatePair,
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827.canonicalBaseConjugatePairLift827

/-! The residue-field transport is generic: an honest ring equivalence
preserves the complete tame-symbol value, while changing the primitive-root
coordinate by an `m`-th power produces exactly the visible scalar `m`.
This comparison—not a pointwise Fourier identification—aligns the fixed-root
827 computation with the one globally reduced cyclotomic root. -/

#check Fermat.Conservation.TameSymbol.Context.card_eq_of_ringEquiv
#check Fermat.Conservation.TameSymbol.Context.primitiveRoot_pow_residueCharacter_val
#check Fermat.Conservation.TameSymbol.Context.residueCharacter_map_ringEquiv
#check Fermat.Conservation.TameSymbol.Context.residueCharacter_primitiveRoot_pow
#check Fermat.Conservation.TameSymbol.Context.raw_map_ringEquiv
#check Fermat.Conservation.TameSymbol.Context.value_primitiveRoot_pow
#check Fermat.Conservation.TameSymbol.Context.value_eq_of_residue_equiv

#guard_depends_on
  Fermat.Conservation.TameSymbol.Context.residueCharacter_map_ringEquiv,
  Fermat.Conservation.TameSymbol.Context.primitiveRoot_pow_residueCharacter_val
#guard_depends_on
  Fermat.Conservation.TameSymbol.Context.residueCharacter_primitiveRoot_pow,
  Fermat.Conservation.TameSymbol.Context.primitiveRoot_pow_residueCharacter_val
#guard_depends_on
  Fermat.Conservation.TameSymbol.Context.raw_map_ringEquiv,
  Fermat.Conservation.TameSymbol.Context.raw
#guard_depends_on
  Fermat.Conservation.TameSymbol.Context.value_primitiveRoot_pow,
  Fermat.Conservation.TameSymbol.Context.residueCharacter_primitiveRoot_pow
#guard_depends_on
  Fermat.Conservation.TameSymbol.Context.value_eq_of_residue_equiv,
  Fermat.Conservation.TameSymbol.Context.raw_map_ringEquiv
#guard_depends_on
  Fermat.Conservation.TameSymbol.Context.value_eq_of_residue_equiv,
  Fermat.Conservation.TameSymbol.Context.residueCharacter_map_ringEquiv

/-! The globally normalized ledger uses the reduction of one global
cyclotomic root at every actual height-one place.  Its orbit value is `tau`
times the fixed-root value, so its total is a weighted Fourier sum.  In the
canonical irregular seat that ledger is nonzero but its total is zero:
genuine cancellation among live local entries. -/

#check Fermat.FiftyNine.Conservation.CanonicalTameLedger827.orbitResidueEquiv827
#check Fermat.FiftyNine.Conservation.CanonicalTameLedger827.orbitPlace827_not_mem_placesOver59
#check Fermat.FiftyNine.Conservation.CanonicalTameLedger827.orbitResidueEquiv827_mk
#check Fermat.FiftyNine.Conservation.CanonicalTameLedger827.orbitResidueEquiv827_localReductionHom
#check Fermat.FiftyNine.Conservation.CanonicalTameLedger827.orbitResidueEquiv827_angularComponent
#check Fermat.FiftyNine.Conservation.CanonicalTameLedger827.orbitResidueEquiv827_residueRootUnit
#check Fermat.FiftyNine.Conservation.CanonicalTameLedger827.canonicalOrbitTameContext827
#check Fermat.FiftyNine.Conservation.CanonicalTameLedger827.canonicalOrbitTameContext827_value_eq_context
#check Fermat.FiftyNine.Conservation.CanonicalTameLedger827.tameContext827_value_eq_sigma_mul_canonical
#check Fermat.FiftyNine.Conservation.CanonicalTameLedger827.tameContext827_value_eq_sigma_mul_context
#check Fermat.FiftyNine.Conservation.CanonicalTameLedger827.tameOrbitPlace827_eq_orbitPlace_inv
#check Fermat.FiftyNine.Conservation.CanonicalTameLedger827.canonicalTameOrbitValue827
#check Fermat.FiftyNine.Conservation.CanonicalTameLedger827.canonicalTameOrbitValue827_eq_context_at_place
#check Fermat.FiftyNine.Conservation.CanonicalTameLedger827.actualTameOrbitValue827_eq_inv_mul_canonical
#check Fermat.FiftyNine.Conservation.CanonicalTameLedger827.canonicalTameOrbitValue827_eq_mul_actual
#check Fermat.FiftyNine.Conservation.CanonicalTameLedger827.canonicalTameLedger827
#check Fermat.FiftyNine.Conservation.CanonicalTameLedger827.canonicalTameLedger827_apply_orbit
#check Fermat.FiftyNine.Conservation.CanonicalTameLedger827.canonicalTameLedger827_apply_eq_zero_of_not_over827
#check Fermat.FiftyNine.Conservation.CanonicalTameLedger827.canonicalTameValue_eq_canonicalLedger_of_outside_support
#check Fermat.FiftyNine.Conservation.CanonicalTameLedger827.canonicalTameLedger827_sum_eq_weighted_actual
#check Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827.inverseFirstGenerated_powerFortyThree_fourier_eq_zero
#check Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827.inverseOrientedFullOrbitUnitReading827_powerFortyThree_eq_zero
#check Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827.weightedReflectedLocalizationWave827
#check Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827.powerCharacter59_fortyFour_inv
#check Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827.powerCharacter59_fortyThree_inv
#check Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827.weightedReflectedLocalizationWave827_isPureCharacter
#check Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827.sum_weighted_actualTameOrbitValue827_canonical_irregular_eq_zero
#check Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827.canonicalTameLedger827_canonical_irregular_sum_eq_zero
#check Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827.canonicalTameLedger827_canonical_irregular_ne_zero
#check Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827.wild_eq_zero_of_canonicalTameLedgerReciprocityEquation827

#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalTameLedger827.orbitResidueEquiv827_localReductionHom,
  Fermat.FiftyNine.Conservation.CanonicalTameLedger827.orbitResidueEquiv827_mk
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalTameLedger827.orbitResidueEquiv827_angularComponent,
  Fermat.FiftyNine.Conservation.CanonicalTameLedger827.orbitResidueEquiv827_localReductionHom
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalTameLedger827.orbitResidueEquiv827_residueRootUnit,
  Fermat.FiftyNine.Conservation.CanonicalTameLedger827.orbitResidueEquiv827_mk
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalTameLedger827.canonicalOrbitTameContext827_value_eq_context,
  Fermat.Conservation.TameSymbol.Context.value_eq_of_residue_equiv
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalTameLedger827.tameContext827_value_eq_sigma_mul_canonical,
  Fermat.Conservation.TameSymbol.Context.value_primitiveRoot_pow
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalTameLedger827.tameContext827_value_eq_sigma_mul_context,
  Fermat.FiftyNine.Conservation.CanonicalTameLedger827.canonicalOrbitTameContext827_value_eq_context
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalTameLedger827.actualTameOrbitValue827_eq_inv_mul_canonical,
  Fermat.FiftyNine.Conservation.CanonicalTameLedger827.tameContext827_value_eq_sigma_mul_context
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalTameLedger827.canonicalTameOrbitValue827_eq_mul_actual,
  Fermat.FiftyNine.Conservation.CanonicalTameLedger827.actualTameOrbitValue827_eq_inv_mul_canonical
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalTameLedger827.canonicalTameLedger827_apply_orbit,
  Fermat.FiftyNine.Conservation.SplitPrimeFourier827.indexedPlaceOrbitEquiv827
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalTameLedger827.canonicalTameValue_eq_canonicalLedger_of_outside_support,
  Fermat.FiftyNine.Conservation.CyclotomicTameContext59.value_firstGenerated_candidate_eq_zero_outside_support
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalTameLedger827.canonicalTameLedger827_sum_eq_weighted_actual,
  Fermat.FiftyNine.Conservation.CanonicalTameLedger827.canonicalTameOrbitValue827_eq_mul_actual
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827.inverseOrientedFullOrbitUnitReading827_powerFortyThree_eq_zero,
  Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827.inverseFirstGenerated_powerFortyThree_fourier_eq_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827.weightedReflectedLocalizationWave827_isPureCharacter,
  Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827.actualReflectedLocalizationWave827_isPureCharacter
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827.sum_weighted_actualTameOrbitValue827_canonical_irregular_eq_zero,
  Fermat.FiftyNine.Conservation.FourierPairingProjection827.sum_mul_pureInverse_eq_sum_characterComponent_mul
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827.sum_weighted_actualTameOrbitValue827_canonical_irregular_eq_zero,
  Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827.inverseOrientedFullOrbitUnitReading827_powerFortyThree_eq_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827.canonicalTameLedger827_canonical_irregular_sum_eq_zero,
  Fermat.FiftyNine.Conservation.CanonicalTameLedger827.canonicalTameLedger827_sum_eq_weighted_actual
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827.canonicalTameLedger827_canonical_irregular_ne_zero,
  Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.sum_actualTameOrbitValue827_canonical_irregular_ne_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827.wild_eq_zero_of_canonicalTameLedgerReciprocityEquation827,
  Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827.canonicalTameLedger827_canonical_irregular_sum_eq_zero

/-! Finally, the canonical ledger is connected to the existing global
reciprocity interface.  The adapter still consumes the genuine reciprocity
law, reflected lift, orbit comparison, and outside-place silence; it does
not manufacture any of them.  Once supplied, the proved canonical tame
cancellation forces the distinguished wild value—and in particular the
actual lambda-place value—to vanish. -/

#check Fermat.FiftyNine.Conservation.CanonicalGlobalReciprocity827.lambdaPlace59_not_mem_placesOver827
#check Fermat.FiftyNine.Conservation.CanonicalGlobalReciprocity827.readings_eq_single_add_canonicalTameLedger827
#check Fermat.FiftyNine.Conservation.CanonicalGlobalReciprocity827.wild_add_canonicalTameLedger827_sum_eq_zero_of_globalReciprocity
#check Fermat.FiftyNine.Conservation.CanonicalGlobalReciprocity827.pairAt_distinguished_eq_zero_of_globalReciprocity827
#check Fermat.FiftyNine.Conservation.CanonicalGlobalReciprocity827.pairAt_lambdaPlace59_eq_zero_of_globalReciprocity827

#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalGlobalReciprocity827.readings_eq_single_add_canonicalTameLedger827,
  Fermat.FiftyNine.Conservation.CanonicalTameLedger827.canonicalTameLedger827_apply_eq_zero_of_not_over827
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalGlobalReciprocity827.wild_add_canonicalTameLedger827_sum_eq_zero_of_globalReciprocity,
  Fermat.FiftyNine.Conservation.CanonicalGlobalReciprocity827.readings_eq_single_add_canonicalTameLedger827
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalGlobalReciprocity827.wild_add_canonicalTameLedger827_sum_eq_zero_of_globalReciprocity,
  Fermat.Conservation.TatePairing.GlobalReciprocityLaw.sum_eq_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalGlobalReciprocity827.pairAt_distinguished_eq_zero_of_globalReciprocity827,
  Fermat.FiftyNine.Conservation.CanonicalGlobalReciprocity827.wild_add_canonicalTameLedger827_sum_eq_zero_of_globalReciprocity
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalGlobalReciprocity827.pairAt_distinguished_eq_zero_of_globalReciprocity827,
  Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827.canonicalTameLedger827_canonical_irregular_sum_eq_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalGlobalReciprocity827.pairAt_lambdaPlace59_eq_zero_of_globalReciprocity827,
  Fermat.FiftyNine.Conservation.CanonicalGlobalReciprocity827.lambdaPlace59_not_mem_placesOver827

/-! Installing the canonical base lift removes the last lift parameter from
the globally root-oriented tame ledger.  The concrete ledger is nonzero but
has zero scalar total.  Global reciprocity still remains visible: the final
wild-place vanishing theorem consumes the honest orbit comparison and
outside-place silence rather than manufacturing either one. -/

#check Fermat.FiftyNine.Conservation.CanonicalConjugatePairGlobalLedger827.canonicalConjugatePairTameOrbitValue827
#check Fermat.FiftyNine.Conservation.CanonicalConjugatePairGlobalLedger827.canonicalConjugatePairGlobalLedger827
#check Fermat.FiftyNine.Conservation.CanonicalConjugatePairGlobalLedger827.canonicalConjugatePairGlobalLedger827_apply_orbit
#check Fermat.FiftyNine.Conservation.CanonicalConjugatePairGlobalLedger827.canonicalConjugatePairGlobalLedger827_sum_eq_zero
#check Fermat.FiftyNine.Conservation.CanonicalConjugatePairGlobalLedger827.canonicalConjugatePairGlobalLedger827_ne_zero
#check Fermat.FiftyNine.Conservation.CanonicalConjugatePairGlobalLedger827.pairAt_lambdaPlace59_eq_zero_of_canonicalConjugatePair827

#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairGlobalLedger827.canonicalConjugatePairTameOrbitValue827,
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827.canonicalBaseConjugatePairLift827
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairGlobalLedger827.canonicalConjugatePairGlobalLedger827,
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827.canonicalBaseConjugatePairLift827
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairGlobalLedger827.canonicalConjugatePairGlobalLedger827_apply_orbit,
  Fermat.FiftyNine.Conservation.CanonicalTameLedger827.canonicalTameLedger827_apply_orbit
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairGlobalLedger827.canonicalConjugatePairGlobalLedger827_sum_eq_zero,
  Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827.canonicalTameLedger827_canonical_irregular_sum_eq_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairGlobalLedger827.canonicalConjugatePairGlobalLedger827_ne_zero,
  Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827.canonicalTameLedger827_canonical_irregular_ne_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairGlobalLedger827.pairAt_lambdaPlace59_eq_zero_of_canonicalConjugatePair827,
  Fermat.FiftyNine.Conservation.CanonicalGlobalReciprocity827.pairAt_lambdaPlace59_eq_zero_of_globalReciprocity827
#guard_depends_on
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairGlobalLedger827.pairAt_lambdaPlace59_eq_zero_of_canonicalConjugatePair827,
  Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827.canonicalBaseConjugatePairLift827

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
#check Fermat.FiftyNine.Conservation.PointedTateIncidence.reflectedBoundaryFunctional827
#check Fermat.FiftyNine.Conservation.PointedTateIncidence.reflectedBoundaryFunctional827_apply
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
  Fermat.FiftyNine.Conservation.PointedTateIncidence.reflectedBoundaryFunctional827_apply,
  Fermat.FiftyNine.Conservation.PointedTateIncidence.reflectedCoordinatePairing827
#guard_depends_on
  Fermat.FiftyNine.Conservation.PointedTateIncidence.reflectedBoundaryFunctional827_apply,
  Fermat.FiftyNine.Conservation.PointedTateIncidence.reflectedPointedLocalization827
#guard_depends_on
  Fermat.FiftyNine.Conservation.PointedTateIncidence.PointedTateIncidence827.connecting_apply,
  Fermat.FiftyNine.Conservation.PointedTateIncidence.reflectedCoordinatePairing827
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

/-! W4 activates only the conditional fixed future justified by the W1
seating premise.  There is deliberately no closed branch theorem because
the seating and Poitou--Tate interfaces remain uninhabited. -/

#check Fermat.FiftyNine.Conservation.TransversalityVerdict827.pointedConormalClass_eq_zero_of_fourierSeating
#check Fermat.FiftyNine.Conservation.TransversalityVerdict827.fixedPointedClassReadoutOfFourierSeating827
#check Fermat.FiftyNine.Conservation.TransversalityVerdict827.fixedPointedReadoutOfFourierSeating_pullback
#check Fermat.FiftyNine.Conservation.TransversalityVerdict827.fixedGauge_preimage_independent_of_fourierSeating
#check Fermat.FiftyNine.Conservation.TransversalityVerdict827.reflectedDualObstructionGain_eq_one_of_seating
#check Fermat.FiftyNine.Conservation.TransversalityVerdict827.fixedGainAllocation_of_seating
#check Fermat.FiftyNine.Conservation.TransversalityVerdict827.no_transverseDirection_of_seating

#guard_depends_on
  Fermat.FiftyNine.Conservation.TransversalityVerdict827.pointedConormalClass_eq_zero_of_fourierSeating,
  Fermat.FiftyNine.Conservation.SplitPrimeFourier827.fixedAttention_of_fourierSeating
#guard_depends_on
  Fermat.FiftyNine.Conservation.TransversalityVerdict827.fixedPointedReadoutOfFourierSeating_pullback,
  Fermat.FiftyNine.Conservation.GaugeSteering827.fixedPointedReadout_pullback
#guard_depends_on
  Fermat.FiftyNine.Conservation.TransversalityVerdict827.fixedGauge_preimage_independent_of_fourierSeating,
  Fermat.FiftyNine.Conservation.GaugeSteering827.fixedGauge_preimage_independent
#guard_depends_on
  Fermat.FiftyNine.Conservation.TransversalityVerdict827.reflectedDualObstructionGain_eq_one_of_seating,
  Fermat.FiftyNine.Conservation.PointedTateIncidence.reflectedGain_eq_one_of_fourierSeating
#guard_depends_on
  Fermat.FiftyNine.Conservation.TransversalityVerdict827.fixedGainAllocation_of_seating,
  Fermat.FiftyNine.Conservation.TransversalityVerdict827.reflectedDualObstructionGain_eq_one_of_seating
#guard_depends_on
  Fermat.FiftyNine.Conservation.TransversalityVerdict827.fixedGainAllocation_of_seating,
  Fermat.FiftyNine.Conservation.PointedTateIncidence.PointedTateIncidence827.conserved_bit
#guard_depends_on
  Fermat.FiftyNine.Conservation.TransversalityVerdict827.no_transverseDirection_of_seating,
  Fermat.FiftyNine.Conservation.SplitPrimeFourier827.no_transverseDirection_of_fourierSeating

/-! Ulam W0 exposes the actual localization covector and freezes the missing
q-relaxed pairing extension plus normalized reflected-class shape.  The 827
normalization and Fermat Tate-pairing values remain deliberately distinct.
No inhabitant, pairing vanishing, or comparison equality is asserted. -/

#check Fermat.FiftyNine.Conservation.UlamTypeFreeze.ReflectedWildCarrierExtension827
#check Fermat.FiftyNine.Conservation.UlamTypeFreeze.ReflectedWildCarrierExtension827.qRelaxedWild_reading_oldToQRelaxed
#check Fermat.FiftyNine.Conservation.UlamTypeFreeze.NormalizedReflectedClass827
#check Fermat.FiftyNine.Conservation.UlamTypeFreeze.NormalizedReflectedClass827.yStar_localization_eq_one
#check Fermat.FiftyNine.Conservation.UlamTypeFreeze.NormalizedReflectedClass827.yStarPairingFunctional

#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamTypeFreeze.ReflectedWildCarrierExtension827.qRelaxedWild_reading_oldToQRelaxed,
  Fermat.FiftyNine.Conservation.UlamTypeFreeze.ReflectedWildCarrierExtension827.reading_compatibility
#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamTypeFreeze.NormalizedReflectedClass827.yStar_localization_eq_one,
  Fermat.FiftyNine.Conservation.UlamTypeFreeze.NormalizedReflectedClass827.normalization
#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamTypeFreeze.NormalizedReflectedClass827.yStar_localization_eq_one,
  Fermat.FiftyNine.Conservation.PointedTateIncidence.reflectedBoundaryFunctional827_apply

/-! Ulam W1 keeps the whole normalized 827 fiber, constructs the W0 extension
only from an explicit localization-at-59 producer, and processes the wild and
class-valued readouts through their kernels.  Steps 9 and 10 remain typed
interfaces; the only relation-(7a) endpoint is conditional. -/

/-! ### Steps 1--3: nonzero boundary, exact coordinate, conserved fiber -/

#check Fermat.FiftyNine.Conservation.UlamReadout827.reflectedBoundaryFunctional827_ne_zero
#check Fermat.FiftyNine.Conservation.UlamReadout827.reflectedBoundaryFunctional827_eq_reflectedPointedLocalization827
#check Fermat.FiftyNine.Conservation.UlamReadout827.reflectedBoundaryFunctional827_eq_qLocalizationCoordinate827
#check Fermat.FiftyNine.Conservation.UlamReadout827.NormalizedReflectedFiber827
#check Fermat.FiftyNine.Conservation.UlamReadout827.normalizedReflectedFiber827_nonempty

#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.reflectedBoundaryFunctional827_ne_zero,
  Fermat.FiftyNine.Conservation.PointedTateIncidence.reflectedGain_eq_one_of_fourierSeating
#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.reflectedBoundaryFunctional827_eq_reflectedPointedLocalization827,
  Fermat.FiftyNine.Conservation.PointedTateIncidence.reflectedBoundaryFunctional827_apply
#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.reflectedBoundaryFunctional827_eq_qLocalizationCoordinate827,
  Fermat.FiftyNine.Conservation.PointedTateIncidence.reflectedBoundaryFunctional827_apply
#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.normalizedReflectedFiber827_nonempty,
  Fermat.Conservation.ReadoutLedger.normalizedFiber_nonempty
#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.normalizedReflectedFiber827_nonempty,
  Fermat.FiftyNine.Conservation.UlamReadout827.reflectedBoundaryFunctional827_ne_zero

/-! ### Step 4: localization-at-59 producer -/

#check Fermat.FiftyNine.Conservation.UlamReadout827.ReflectedWildLocalizationAt59
#check Fermat.FiftyNine.Conservation.UlamReadout827.ReflectedWildLocalizationAt59.agrees_with_old
#check Fermat.FiftyNine.Conservation.UlamReadout827.ReflectedWildLocalizationAt59.toWildLocalInterface
#check Fermat.FiftyNine.Conservation.UlamReadout827.ReflectedWildLocalizationAt59.toReflectedWildCarrierExtension827
#check Fermat.FiftyNine.Conservation.UlamReadout827.ReflectedWildLocalizationAt59.toReflectedWildCarrierExtension827_reading

#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.ReflectedWildLocalizationAt59.toReflectedWildCarrierExtension827_reading,
  Fermat.FiftyNine.Conservation.UlamReadout827.ReflectedWildLocalizationAt59.toReflectedWildCarrierExtension827

/-! ### Step 5: lawful or retained STEERABLE row -/

#check Fermat.FiftyNine.Conservation.UlamReadout827.selectedWildFunctional827
#check Fermat.FiftyNine.Conservation.UlamReadout827.SelectedWildLawfulness827
#check Fermat.FiftyNine.Conservation.UlamReadout827.SelectedWildLawfulness827.ker_boundary_le_ker_wild
#check Fermat.FiftyNine.Conservation.UlamReadout827.SteerableWildDirection827
#check Fermat.FiftyNine.Conservation.UlamReadout827.not_lawful_iff_steerableWildDirection
#check Fermat.FiftyNine.Conservation.UlamReadout827.selectedWild_newProcessed_eq_bot

#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.not_lawful_iff_steerableWildDirection,
  SetLike.not_le_iff_exists
#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.selectedWild_newProcessed_eq_bot,
  Fermat.Conservation.ReadoutLedger.fixed_iff_newProcessed_eq_bot

/-! ### Step 6: canonical rank-one factorization -/

#check Fermat.FiftyNine.Conservation.UlamReadout827.existsUnique_selectedWildFactorization
#check Fermat.FiftyNine.Conservation.UlamReadout827.WildLawfulness827
#check Fermat.FiftyNine.Conservation.UlamReadout827.WildLawfulness827.ker_boundary_le_ker_wild
#check Fermat.FiftyNine.Conservation.UlamReadout827.qRelaxedWildBilinear827
#check Fermat.FiftyNine.Conservation.UlamReadout827.wildCoefficient827
#check Fermat.FiftyNine.Conservation.UlamReadout827.qRelaxedWild_factorization

#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.existsUnique_selectedWildFactorization,
  Fermat.Conservation.ReadoutLedger.existsUnique_rankOneFactorization
#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.qRelaxedWild_factorization,
  Fermat.Conservation.ReadoutLedger.existsUnique_bilinearRankOneFactorization

/-! ### Step 7: genuine class-valued gauge and processed-range invariant -/

#check Fermat.FiftyNine.Conservation.UlamReadout827.SevenAGaugeCarrier59
#check Fermat.FiftyNine.Conservation.UlamReadout827.selectedClassGauge59
#check Fermat.FiftyNine.Conservation.UlamReadout827.selectedClassGauge59_value
#check Fermat.FiftyNine.Conservation.UlamReadout827.selectedClassGauge59_eq_zero_iff_vandiverSevenA
#check Fermat.FiftyNine.Conservation.UlamReadout827.ClassValuedSevenAGaugeSeating
#check Fermat.FiftyNine.Conservation.UlamReadout827.ClassValuedSevenAGaugeSeating.gauge_at_fermat
#check Fermat.FiftyNine.Conservation.UlamReadout827.WildProcessesAtLeastSevenA
#check Fermat.FiftyNine.Conservation.UlamReadout827.WildProcessesAtLeastSevenA.ker_wild_le_ker_gauge
#check Fermat.FiftyNine.Conservation.UlamReadout827.WildUsesNothingBeyondSevenA
#check Fermat.FiftyNine.Conservation.UlamReadout827.WildUsesNothingBeyondSevenA.ker_gauge_le_ker_wild
#check Fermat.FiftyNine.Conservation.UlamReadout827.gaugeKernel_eq_wildKernel
#check Fermat.FiftyNine.Conservation.UlamReadout827.gaugeProcessedRangeEquiv827
#check Fermat.FiftyNine.Conservation.UlamReadout827.gaugeProcessedRangeEquiv827_apply

#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.selectedClassGauge59_value,
  Fermat.FiftyNine.Conservation.UlamReadout827.selectedClassGauge59
#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.selectedClassGauge59_eq_zero_iff_vandiverSevenA,
  Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.differenceGauge_eq_zero_iff_vandiverSevenA
#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.gaugeKernel_eq_wildKernel,
  Fermat.FiftyNine.Conservation.UlamReadout827.WildProcessesAtLeastSevenA.ker_wild_le_ker_gauge
#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.gaugeKernel_eq_wildKernel,
  Fermat.FiftyNine.Conservation.UlamReadout827.WildUsesNothingBeyondSevenA.ker_gauge_le_ker_wild
#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.gaugeProcessedRangeEquiv827_apply,
  Fermat.Conservation.ReadoutLedger.processedRangeEquiv_apply

/-! ### Step 8: actual 59-torsion depth -/

#check Fermat.FiftyNine.Conservation.UlamReadout827.fiftyNine_nsmul_gauge_eq_zero
#check Fermat.FiftyNine.Conservation.UlamReadout827.fiftyNine_nsmul_gaugeRange_eq_zero
#check Fermat.FiftyNine.Conservation.UlamReadout827.fiftyEight_nsmul_eq_neg_in_gaugeCarrier
#check Fermat.FiftyNine.Conservation.UlamReadout827.bocksteinDepthDecomposition827
#check Fermat.FiftyNine.Conservation.UlamReadout827.deeperGauge_nextLayerPotential

#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.fiftyNine_nsmul_gauge_eq_zero,
  AddSubgroup.torsionBy.nsmul
#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.fiftyNine_nsmul_gaugeRange_eq_zero,
  AddSubgroup.torsionBy.nsmul
#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.fiftyEight_nsmul_eq_neg_in_gaugeCarrier,
  AddSubgroup.torsionBy.nsmul
#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.bocksteinDepthDecomposition827,
  Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59.bocksteinPowerRootReceiptObservation
#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.deeperGauge_nextLayerPotential,
  nsmul_add

/-! ### Steps 9--10: typed seams, then the conditional endpoint -/

#check Fermat.FiftyNine.Conservation.UlamReadout827.TameSilenceReciprocity827
#check Fermat.FiftyNine.Conservation.UlamReadout827.TameSilenceReciprocity827.globalReciprocity
#check Fermat.FiftyNine.Conservation.UlamReadout827.SurvivingKernelRoute827
#check Fermat.FiftyNine.Conservation.UlamReadout827.SurvivingKernelRoute827.survivingToClass
#check Fermat.FiftyNine.Conservation.UlamReadout827.SurvivingKernelRoute827.classToUnit
#check Fermat.FiftyNine.Conservation.UlamReadout827.SurvivingKernelRoute827.unitToRoot
#check Fermat.FiftyNine.Conservation.UlamReadout827.vandiverSevenA_of_readout_interfaces

#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.vandiverSevenA_of_readout_interfaces,
  Fermat.FiftyNine.Conservation.TateBridge.Lambda_apply_eq_zero_of_reciprocity
#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.vandiverSevenA_of_readout_interfaces,
  Fermat.FiftyNine.Conservation.UlamReadout827.ReflectedWildLocalizationAt59.toReflectedWildCarrierExtension827
#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.vandiverSevenA_of_readout_interfaces,
  Fermat.FiftyNine.Conservation.UlamReadout827.TameSilenceReciprocity827.globalReciprocity
#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.vandiverSevenA_of_readout_interfaces,
  Fermat.FiftyNine.Conservation.UlamReadout827.qRelaxedWild_factorization
#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.vandiverSevenA_of_readout_interfaces,
  Fermat.FiftyNine.Conservation.UlamReadout827.WildProcessesAtLeastSevenA.ker_wild_le_ker_gauge
#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.vandiverSevenA_of_readout_interfaces,
  Fermat.FiftyNine.Conservation.UlamReadout827.ClassValuedSevenAGaugeSeating.gauge_at_fermat
#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.vandiverSevenA_of_readout_interfaces,
  Fermat.FiftyNine.Conservation.UlamReadout827.selectedClassGauge59_eq_zero_iff_vandiverSevenA

/-! V1 now records covered-factor/residual-factor decompositions explicitly.
The normalized plus and minus factors have zero residual once their named
coefficient interface is supplied.  The exact campaign residual remains the
two actual pairing inputs because neither is seated as a normalized factor. -/

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
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.ArtinHasseKummerDecomposition.zero
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.ArtinHasseFactorDecomposition
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.ArtinHasseFactorDecomposition.ofCovered
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.ArtinHasseFactorDecomposition.residualOnly
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.ArtinHasseFactorDecomposition.toArtinHasseKummerDecomposition
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.ArtinHasseFactorDecomposition.ofCovered_residual
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.ArtinHasseFactorDecomposition.residualOnly_residual
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.NormalizedStateFactorArtinHasseDecomposition
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.NormalizedStateFactorArtinHasseDecomposition.plus_mem
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.NormalizedStateFactorArtinHasseDecomposition.minus_mem
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.NormalizedStateFactorArtinHasseDecomposition.plusFactorDecomposition
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.NormalizedStateFactorArtinHasseDecomposition.minusFactorDecomposition
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.NormalizedStateFactorArtinHasseDecomposition.plus_residual_eq_zero
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.NormalizedStateFactorArtinHasseDecomposition.minus_residual_eq_zero
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.CampaignArtinHasseFactorDecomposition
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.CampaignArtinHasseFactorDecomposition.residualOnly
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.CampaignArtinHasseFactorDecomposition.statewiseDecompositionOfResidualEqZero
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.CampaignArtinHasseFactorDecomposition.detectorDecompositionOfResidualEqZero
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.WildClassKind
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.hasArtinHasseDecomposition
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.WildFormulaBudget
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.formulaBudget
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.campaignInventory
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.residualInventory
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.campaignResidualInventory
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.campaignResidualInventory_eq
#check Fermat.FiftyNine.Conservation.ArtinHasseInventory.campaignResidualInventory_length
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
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.ArtinHasseFactorDecomposition.ofCovered_residual,
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.ArtinHasseFactorDecomposition.ofCovered
#guard_depends_on
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.ArtinHasseFactorDecomposition.residualOnly_residual,
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.ArtinHasseFactorDecomposition.residualOnly
#guard_depends_on
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.NormalizedStateFactorArtinHasseDecomposition.plus_residual_eq_zero,
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.NormalizedStateFactorArtinHasseDecomposition.plusFactorDecomposition
#guard_depends_on
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.NormalizedStateFactorArtinHasseDecomposition.minus_residual_eq_zero,
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.NormalizedStateFactorArtinHasseDecomposition.minusFactorDecomposition
#guard_depends_on
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.campaignResidualInventory_eq,
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.campaignResidualInventory
#guard_depends_on
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.campaignResidualInventory_eq,
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.hasArtinHasseDecomposition
#guard_depends_on
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.campaignResidualInventory_length,
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.campaignResidualInventory_eq
#guard_depends_on
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.campaign_formulaBudget_eq_needsVostokov,
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.formulaBudget
#guard_depends_on
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.campaign_formulaBudget_eq_needsVostokov,
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.campaignInventory

/-! The C1 audit binds V3's two literal input maps to their chosen quotient
representatives, retains both whole classes as honest residuals, and proves
that the normalized q-relaxed fiber does not lie in the canonical strict
range.  It makes no Artin--Hasse nonmembership claim and constructs no
splitting. -/

#check Fermat.FiftyNine.Conservation.VostokovShapeAudit59.statewiseKummerClass
#check Fermat.FiftyNine.Conservation.VostokovShapeAudit59.transverseKummerClass
#check Fermat.FiftyNine.Conservation.VostokovShapeAudit59.statewiseRepresentative
#check Fermat.FiftyNine.Conservation.VostokovShapeAudit59.transverseRepresentative
#check Fermat.FiftyNine.Conservation.VostokovShapeAudit59.statewiseRepresentative_readback
#check Fermat.FiftyNine.Conservation.VostokovShapeAudit59.transverseRepresentative_readback
#check Fermat.FiftyNine.Conservation.VostokovShapeAudit59.inputResidualOnly
#check Fermat.FiftyNine.Conservation.VostokovShapeAudit59.inputResidualOnly_statewise_covered
#check Fermat.FiftyNine.Conservation.VostokovShapeAudit59.inputResidualOnly_statewise_residual
#check Fermat.FiftyNine.Conservation.VostokovShapeAudit59.inputResidualOnly_transverse_covered
#check Fermat.FiftyNine.Conservation.VostokovShapeAudit59.inputResidualOnly_transverse_residual
#check Fermat.FiftyNine.Conservation.VostokovShapeAudit59.readingAt59_exact_inputs
#check Fermat.FiftyNine.Conservation.VostokovShapeAudit59.qLocalizationCoordinate827_oldReflected_eq_zero
#check Fermat.FiftyNine.Conservation.VostokovShapeAudit59.normalizedFiber_not_mem_range_oldReflected

#guard_depends_on
  Fermat.FiftyNine.Conservation.VostokovShapeAudit59.statewiseRepresentative_readback,
  Fermat.Conservation.SelmerEigenspace.quotientRepresentative_mk
#guard_depends_on
  Fermat.FiftyNine.Conservation.VostokovShapeAudit59.transverseRepresentative_readback,
  Fermat.Conservation.SelmerEigenspace.quotientRepresentativeAt_mk
#guard_depends_on
  Fermat.FiftyNine.Conservation.VostokovShapeAudit59.inputResidualOnly_statewise_covered,
  Fermat.FiftyNine.Conservation.VostokovShapeAudit59.inputResidualOnly
#guard_depends_on
  Fermat.FiftyNine.Conservation.VostokovShapeAudit59.inputResidualOnly_statewise_residual,
  Fermat.FiftyNine.Conservation.VostokovShapeAudit59.inputResidualOnly
#guard_depends_on
  Fermat.FiftyNine.Conservation.VostokovShapeAudit59.inputResidualOnly_transverse_covered,
  Fermat.FiftyNine.Conservation.VostokovShapeAudit59.inputResidualOnly
#guard_depends_on
  Fermat.FiftyNine.Conservation.VostokovShapeAudit59.inputResidualOnly_transverse_residual,
  Fermat.FiftyNine.Conservation.VostokovShapeAudit59.inputResidualOnly
#guard_depends_on
  Fermat.FiftyNine.Conservation.VostokovShapeAudit59.readingAt59_exact_inputs,
  Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.readingAt59
#guard_depends_on
  Fermat.FiftyNine.Conservation.VostokovShapeAudit59.qLocalizationCoordinate827_oldReflected_eq_zero,
  Fermat.Conservation.SelmerEigenspace.supportValuation_emptySupportInclusion_eq_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.VostokovShapeAudit59.normalizedFiber_not_mem_range_oldReflected,
  Fermat.FiftyNine.Conservation.VostokovShapeAudit59.qLocalizationCoordinate827_oldReflected_eq_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.VostokovShapeAudit59.normalizedFiber_not_mem_range_oldReflected,
  Fermat.FiftyNine.Conservation.UlamReadout827.reflectedBoundaryFunctional827_eq_qLocalizationCoordinate827

/-! V2 supplies only the generic algebraic descent surface for a total
Kummer pairing.  V3 then reduces the concrete seated localization producer
to one representative pairing, one canonical-inclusion landing receipt, and
old-reading calibration.  The Artin--Hasse coefficient and four-term
factorization theorems connect V1's exact residual to that total pairing. -/

/-! ### Generic wild Kummer pairing core -/

#check Fermat.Conservation.WildKummerPairing.RepresentativePairing
#check Fermat.Conservation.WildKummerPairing.Pairing
#check Fermat.Conservation.WildKummerPairing.classOfUnit
#check Fermat.Conservation.WildKummerPairing.classOfUnit_apply
#check Fermat.Conservation.WildKummerPairing.Pairing.onRepresentatives
#check Fermat.Conservation.WildKummerPairing.Pairing.onRepresentatives_apply
#check Fermat.Conservation.WildKummerPairing.classOfUnit_surjective
#check Fermat.Conservation.WildKummerPairing.IsPPowerSilent
#check Fermat.Conservation.WildKummerPairing.isPPowerSilent
#check Fermat.Conservation.WildKummerPairing.IsKummerDescent
#check Fermat.Conservation.WildKummerPairing.RepresentativePairing.descend
#check Fermat.Conservation.WildKummerPairing.RepresentativePairing.descend_classOfUnit_classOfUnit
#check Fermat.Conservation.WildKummerPairing.RepresentativePairing.isKummerDescent_descend
#check Fermat.Conservation.WildKummerPairing.Pairing.descend_onRepresentatives
#check Fermat.Conservation.WildKummerPairing.Pairing.descend_onRepresentatives_apply
#check Fermat.Conservation.WildKummerPairing.Core
#check Fermat.Conservation.WildKummerPairing.Core.ofRepresentative
#check Fermat.Conservation.WildKummerPairing.Core.ofRepresentative_pairing_apply
#check Fermat.Conservation.WildKummerPairing.Core.ofPairing
#check Fermat.Conservation.WildKummerPairing.Core.ofPairing_pairing_apply
#check Fermat.Conservation.WildKummerPairing.Core.ofPairing_representative_apply
#check Fermat.Conservation.WildKummerPairing.Core.pairing_classOfUnit_classOfUnit
#check Fermat.Conservation.WildKummerPairing.IsGaloisEquivariant
#check Fermat.Conservation.WildKummerPairing.GaloisData
#check Fermat.Conservation.WildKummerPairing.GaloisData.action_adjoint
#check Fermat.Conservation.WildKummerPairing.IsArtinHasseCalibrated

#guard_depends_on
  Fermat.Conservation.WildKummerPairing.classOfUnit_apply,
  Fermat.Conservation.WildKummerPairing.classOfUnit
#guard_depends_on
  Fermat.Conservation.WildKummerPairing.Pairing.onRepresentatives_apply,
  Fermat.Conservation.WildKummerPairing.Pairing.onRepresentatives
#guard_depends_on
  Fermat.Conservation.WildKummerPairing.isPPowerSilent,
  ZModModule.char_nsmul_eq_zero
#guard_depends_on
  Fermat.Conservation.WildKummerPairing.RepresentativePairing.descend_classOfUnit_classOfUnit,
  Fermat.Conservation.WildKummerPairing.RepresentativePairing.descend
#guard_depends_on
  Fermat.Conservation.WildKummerPairing.RepresentativePairing.isKummerDescent_descend,
  Fermat.Conservation.WildKummerPairing.RepresentativePairing.descend_classOfUnit_classOfUnit
#guard_depends_on
  Fermat.Conservation.WildKummerPairing.Pairing.descend_onRepresentatives,
  Fermat.Conservation.WildKummerPairing.classOfUnit_surjective
#guard_depends_on
  Fermat.Conservation.WildKummerPairing.Pairing.descend_onRepresentatives_apply,
  Fermat.Conservation.WildKummerPairing.Pairing.descend_onRepresentatives
#guard_depends_on
  Fermat.Conservation.WildKummerPairing.Core.ofRepresentative_pairing_apply,
  Fermat.Conservation.WildKummerPairing.Core.ofRepresentative
#guard_depends_on
  Fermat.Conservation.WildKummerPairing.Core.ofPairing_pairing_apply,
  Fermat.Conservation.WildKummerPairing.Core.ofPairing
#guard_depends_on
  Fermat.Conservation.WildKummerPairing.Core.ofPairing_representative_apply,
  Fermat.Conservation.WildKummerPairing.Core.ofPairing
#guard_depends_on
  Fermat.Conservation.WildKummerPairing.Core.pairing_classOfUnit_classOfUnit,
  Fermat.Conservation.WildKummerPairing.Core.descent
#guard_depends_on
  Fermat.Conservation.WildKummerPairing.GaloisData.action_adjoint,
  Fermat.Conservation.WildKummerPairing.GaloisData.equivariant

/-! ### Discrete Kummer `H¹` and primitive-root orientation

The classical chosen-root cocycle now gives an honest map from the Kummer
quotient to discrete absolute-Galois `H¹`.  A supplied primitive root then
orients the roots-of-unity representation into the trivial coefficient line.
These checks deliberately make no discrete-to-continuous comparison claim. -/

#check Fermat.Conservation.LocalKummerH1.AbsoluteGalois
#check Fermat.Conservation.LocalKummerH1.KummerRoots
#check Fermat.Conservation.LocalKummerH1.nsmul_kummerRoots_eq_zero
#check Fermat.Conservation.LocalKummerH1.rootsRepresentation
#check Fermat.Conservation.LocalKummerH1.DiscreteKummerH1
#check Fermat.Conservation.LocalKummerH1.cocycle
#check Fermat.Conservation.LocalKummerH1.cocycle_apply
#check Fermat.Conservation.LocalKummerH1.continuous_cocycleValue
#check Fermat.Conservation.LocalKummerH1.classOfUnit
#check Fermat.Conservation.LocalKummerH1.classOfUnit_one
#check Fermat.Conservation.LocalKummerH1.classOfUnit_mul
#check Fermat.Conservation.LocalKummerH1.representativeMap
#check Fermat.Conservation.LocalKummerH1.nsmul_discreteKummerH1_eq_zero
#check Fermat.Conservation.LocalKummerH1.map
#check Fermat.Conservation.LocalKummerH1.map_classOfUnit

#guard_depends_on
  Fermat.Conservation.LocalKummerH1.representativeMap,
  Fermat.Conservation.LocalKummerH1.classOfUnit_one
#guard_depends_on
  Fermat.Conservation.LocalKummerH1.continuous_cocycleValue,
  continuous_discrete_rng
#guard_depends_on
  Fermat.Conservation.LocalKummerH1.continuous_cocycleValue,
  stabilizer_isOpen_of_isIntegral
#guard_depends_on
  Fermat.Conservation.LocalKummerH1.representativeMap,
  Fermat.Conservation.LocalKummerH1.classOfUnit_mul
#guard_depends_on
  Fermat.Conservation.LocalKummerH1.map,
  Fermat.Conservation.LocalKummerH1.representativeMap
#guard_depends_on
  Fermat.Conservation.LocalKummerH1.map,
  Fermat.Conservation.LocalKummerH1.nsmul_discreteKummerH1_eq_zero
#guard_depends_on
  Fermat.Conservation.LocalKummerH1.map_classOfUnit,
  Fermat.Conservation.LocalKummerH1.map

#check Fermat.Conservation.KummerOrientation.primitiveUnit
#check Fermat.Conservation.KummerOrientation.algebraicPrimitiveUnit
#check Fermat.Conservation.KummerOrientation.algebraicPrimitiveUnit_isPrimitive
#check Fermat.Conservation.KummerOrientation.rootsEquivZPowers
#check Fermat.Conservation.KummerOrientation.coordinateAddEquiv
#check Fermat.Conservation.KummerOrientation.coordinateLinearEquiv
#check Fermat.Conservation.KummerOrientation.absoluteGalois_smul_root_eq
#check Fermat.Conservation.KummerOrientation.rootsRepresentationEquivTrivial
#check Fermat.Conservation.KummerOrientation.orientH1
#check Fermat.Conservation.KummerOrientation.orientH1_H1pi
#check Fermat.Conservation.KummerOrientation.orientH2
#check Fermat.Conservation.KummerOrientation.orientH2_H2pi
#check Fermat.Conservation.KummerOrientation.leftKummerMap
#check Fermat.Conservation.KummerOrientation.leftKummerMap_classOfUnit

#guard_depends_on
  Fermat.Conservation.KummerOrientation.coordinateLinearEquiv,
  Fermat.Conservation.KummerOrientation.coordinateAddEquiv
#guard_depends_on
  Fermat.Conservation.KummerOrientation.rootsRepresentationEquivTrivial,
  Fermat.Conservation.KummerOrientation.coordinateLinearEquiv
#guard_depends_on
  Fermat.Conservation.KummerOrientation.rootsRepresentationEquivTrivial,
  Fermat.Conservation.KummerOrientation.absoluteGalois_smul_root_eq
#guard_depends_on
  Fermat.Conservation.KummerOrientation.orientH1,
  Fermat.Conservation.KummerOrientation.rootsRepresentationEquivTrivial
#guard_depends_on
  Fermat.Conservation.KummerOrientation.orientH1_H1pi,
  groupCohomology.H1π_comp_map_apply
#guard_depends_on
  Fermat.Conservation.KummerOrientation.orientH2,
  Fermat.Conservation.KummerOrientation.rootsRepresentationEquivTrivial
#guard_depends_on
  Fermat.Conservation.KummerOrientation.orientH2_H2pi,
  groupCohomology.H2π_comp_map_apply
#guard_depends_on
  Fermat.Conservation.KummerOrientation.leftKummerMap,
  Fermat.Conservation.LocalKummerH1.map
#guard_depends_on
  Fermat.Conservation.KummerOrientation.leftKummerMap,
  Fermat.Conservation.KummerOrientation.orientH1

/-! The discrete assembly now closes without supplied Kummer maps: the
chosen primitive root orients the genuine left class, the genuine right
class retains its roots-of-unity coefficients, and only the linear `H²`
invariant remains an arithmetic input. -/

#check Fermat.Conservation.DiscreteKummerTatePairing.localPairing
#check Fermat.Conservation.DiscreteKummerTatePairing.localPairing_apply
#check Fermat.Conservation.DiscreteKummerTatePairing.representativePairing
#check Fermat.Conservation.DiscreteKummerTatePairing.representativePairing_apply
#check Fermat.Conservation.DiscreteKummerTatePairing.representativePairing_ofMul

#guard_depends_on
  Fermat.Conservation.DiscreteKummerTatePairing.localPairing,
  Fermat.Conservation.CohomologicalKummerPairing.localPairing
#guard_depends_on
  Fermat.Conservation.DiscreteKummerTatePairing.localPairing,
  Fermat.Conservation.KummerOrientation.leftKummerMap
#guard_depends_on
  Fermat.Conservation.DiscreteKummerTatePairing.localPairing,
  Fermat.Conservation.LocalKummerH1.map
#guard_depends_on
  Fermat.Conservation.DiscreteKummerTatePairing.localPairing,
  Fermat.Conservation.KummerTateReadout.orientedReadoutClasses
#guard_depends_on
  Fermat.Conservation.DiscreteKummerTatePairing.representativePairing,
  Fermat.Conservation.WildKummerPairing.Pairing.onRepresentatives
#guard_depends_on
  Fermat.Conservation.DiscreteKummerTatePairing.representativePairing_ofMul,
  Fermat.Conservation.KummerOrientation.orientH1
#guard_depends_on
  Fermat.Conservation.DiscreteKummerTatePairing.representativePairing_ofMul,
  Fermat.Conservation.LocalKummerH1.classOfUnit

/-! ### Oriented low-degree Kummer--Tate construction

These checks cover the concrete cochain cup product, its descent through
`H¹`, scalar readout through a supplied local invariant, functorial Kummer
transport, and the resulting quotient-level pairing.  They do not claim an
arithmetic construction of either Kummer map or of the local invariant. -/

#check Fermat.Conservation.KummerTateCup.orientedCupCochain
#check Fermat.Conservation.KummerTateCup.orientedCupCochain_mem_cocycles₂
#check Fermat.Conservation.KummerTateCup.orientedCupCocycle
#check Fermat.Conservation.KummerTateCup.orientedCupCocycle_apply
#check Fermat.Conservation.KummerTateCup.orientedCupCocyclesRight
#check Fermat.Conservation.KummerTateCup.orientedCupCoboundaryPrimitive
#check Fermat.Conservation.KummerTateCup.orientedCupCochain_d₀₁
#check Fermat.Conservation.KummerTateCup.orientedCupCocycle_mem_coboundaries₂_of_mem_coboundaries₁
#check Fermat.Conservation.KummerTateCup.orientedCupToH2
#check Fermat.Conservation.KummerTateCup.orientedCupToH2_eq_zero_of_mem_coboundaries₁
#check Fermat.Conservation.KummerTateCup.ker_H1π_le_ker_orientedCupToH2
#check Fermat.Conservation.KummerTateCup.H1π_hom_surjective
#check Fermat.Conservation.KummerTateCup.orientedCupH1Right
#check Fermat.Conservation.KummerTateCup.orientedCupH1Right_H1π
#check Fermat.Conservation.KummerTateCup.orientedCupH1
#check Fermat.Conservation.KummerTateCup.orientedCupH1_apply_H1π
#check Fermat.Conservation.KummerTateCup.trivialLine
#check Fermat.Conservation.KummerTateCup.orientedCupH1Classes
#check Fermat.Conservation.KummerTateCup.orientedCupH1Classes_apply

#guard_depends_on
  Fermat.Conservation.KummerTateCup.orientedCupCocycle,
  Fermat.Conservation.KummerTateCup.orientedCupCochain_mem_cocycles₂
#guard_depends_on
  Fermat.Conservation.KummerTateCup.orientedCupCocycle_mem_coboundaries₂_of_mem_coboundaries₁,
  Fermat.Conservation.KummerTateCup.orientedCupCochain_d₀₁
#guard_depends_on
  Fermat.Conservation.KummerTateCup.orientedCupToH2_eq_zero_of_mem_coboundaries₁,
  Fermat.Conservation.KummerTateCup.orientedCupCocycle_mem_coboundaries₂_of_mem_coboundaries₁
#guard_depends_on
  Fermat.Conservation.KummerTateCup.ker_H1π_le_ker_orientedCupToH2,
  Fermat.Conservation.KummerTateCup.orientedCupToH2_eq_zero_of_mem_coboundaries₁
#guard_depends_on
  Fermat.Conservation.KummerTateCup.orientedCupH1Right,
  Fermat.Conservation.KummerTateCup.ker_H1π_le_ker_orientedCupToH2
#guard_depends_on
  Fermat.Conservation.KummerTateCup.orientedCupH1Right,
  Fermat.Conservation.KummerTateCup.H1π_hom_surjective
#guard_depends_on
  Fermat.Conservation.KummerTateCup.orientedCupH1_apply_H1π,
  Fermat.Conservation.KummerTateCup.orientedCupH1Right_H1π
#guard_depends_on
  Fermat.Conservation.KummerTateCup.orientedCupH1Classes,
  Fermat.Conservation.KummerTateCup.orientedCupH1
#guard_depends_on
  Fermat.Conservation.KummerTateCup.orientedCupH1Classes_apply,
  Fermat.Conservation.KummerTateCup.orientedCupH1Classes

#check Fermat.Conservation.KummerTateReadout.orientedReadoutRight
#check Fermat.Conservation.KummerTateReadout.orientedReadoutRight_apply
#check Fermat.Conservation.KummerTateReadout.orientedReadout
#check Fermat.Conservation.KummerTateReadout.orientedReadout_apply
#check Fermat.Conservation.KummerTateReadout.orientedReadout_H1π
#check Fermat.Conservation.KummerTateReadout.orientedReadout_zero_invariant
#check Fermat.Conservation.KummerTateReadout.orientedReadout_add_invariant
#check Fermat.Conservation.KummerTateReadout.orientedReadout_smul_invariant
#check Fermat.Conservation.KummerTateReadout.orientedReadout_postcomp
#check Fermat.Conservation.KummerTateReadout.orientedReadoutClasses
#check Fermat.Conservation.KummerTateReadout.orientedReadoutClasses_apply

#guard_depends_on
  Fermat.Conservation.KummerTateReadout.orientedReadout,
  Fermat.Conservation.KummerTateCup.orientedCupH1
#guard_depends_on
  Fermat.Conservation.KummerTateReadout.orientedReadout_H1π,
  Fermat.Conservation.KummerTateCup.orientedCupH1_apply_H1π
#guard_depends_on
  Fermat.Conservation.KummerTateReadout.orientedReadoutClasses,
  Fermat.Conservation.KummerTateReadout.orientedReadout
-- `orientedReadoutClasses_apply` is proved by `rfl`; its implementation body is
-- only reflexivity, while the named cup constructor occurs in its type.  Since
-- dependency guards intentionally ignore declaration types, the signature is
-- audited by the `#check` above rather than by a spurious value-dependency.

#check Fermat.Conservation.LocalKummerTransport.unitMap
#check Fermat.Conservation.LocalKummerTransport.unitMap_apply
#check Fermat.Conservation.LocalKummerTransport.unitMap_powerSubgroup_le
#check Fermat.Conservation.LocalKummerTransport.mapMul
#check Fermat.Conservation.LocalKummerTransport.mapMul_mk
#check Fermat.Conservation.LocalKummerTransport.map
#check Fermat.Conservation.LocalKummerTransport.map_classOfUnit
#check Fermat.Conservation.LocalKummerTransport.map_id
#check Fermat.Conservation.LocalKummerTransport.map_comp
#check Fermat.Conservation.LocalKummerTransport.Pairing.pullback
#check Fermat.Conservation.LocalKummerTransport.Pairing.pullback_apply
#check Fermat.Conservation.LocalKummerTransport.Pairing.pullback_classOfUnit
#check Fermat.Conservation.LocalKummerTransport.Pairing.pullback_id
#check Fermat.Conservation.LocalKummerTransport.Pairing.pullback_comp

#guard_depends_on
  Fermat.Conservation.LocalKummerTransport.mapMul,
  Fermat.Conservation.LocalKummerTransport.unitMap_powerSubgroup_le
#guard_depends_on
  Fermat.Conservation.LocalKummerTransport.map,
  Fermat.Conservation.LocalKummerTransport.mapMul
#guard_depends_on
  Fermat.Conservation.LocalKummerTransport.map_comp,
  Fermat.Conservation.LocalKummerTransport.map
#guard_depends_on
  Fermat.Conservation.LocalKummerTransport.Pairing.pullback,
  Fermat.Conservation.LocalKummerTransport.map
#guard_depends_on
  Fermat.Conservation.LocalKummerTransport.Pairing.pullback_comp,
  Fermat.Conservation.LocalKummerTransport.map_comp

#check Fermat.Conservation.CohomologicalKummerPairing.localPairing
#check Fermat.Conservation.CohomologicalKummerPairing.localPairing_apply
#check Fermat.Conservation.CohomologicalKummerPairing.globalPairing
#check Fermat.Conservation.CohomologicalKummerPairing.globalPairing_apply
#check Fermat.Conservation.CohomologicalKummerPairing.globalPairing_classOfUnit

#guard_depends_on
  Fermat.Conservation.CohomologicalKummerPairing.localPairing,
  Fermat.Conservation.KummerTateReadout.orientedReadoutClasses
#guard_depends_on
  Fermat.Conservation.CohomologicalKummerPairing.globalPairing,
  Fermat.Conservation.LocalKummerTransport.Pairing.pullback
-- `globalPairing_apply` is likewise a definitional (`rfl`) readback.  The
-- constructor dependency is guarded on `globalPairing`; its expanded formula
-- is checked above without pretending that `rfl` has a value dependency on a
-- constant appearing only in the theorem statement.

/-! ### Readout restricted to the actual Kummer cup span

The scalar domain is now narrowed from all discrete `H²` to the submodule
generated by classes actually produced by the two Kummer maps.  This closes
the algebraic pairing constructor without assigning values to unrelated or
possibly discontinuous cohomology classes.  It does not identify the span
readout with the normalized continuous local invariant. -/

#check Fermat.Conservation.KummerCupSpanReadout.cupClass
#check Fermat.Conservation.KummerCupSpanReadout.cupGenerators
#check Fermat.Conservation.KummerCupSpanReadout.cupSpan
#check Fermat.Conservation.KummerCupSpanReadout.cupClass_mem_cupSpan
#check Fermat.Conservation.KummerCupSpanReadout.cupInSpan
#check Fermat.Conservation.KummerCupSpanReadout.cupInSpan_coe
#check Fermat.Conservation.KummerCupSpanReadout.cupInSpan_zero_left
#check Fermat.Conservation.KummerCupSpanReadout.cupInSpan_zero_right
#check Fermat.Conservation.KummerCupSpanReadout.cupInSpan_add_left
#check Fermat.Conservation.KummerCupSpanReadout.cupInSpan_add_right
#check Fermat.Conservation.KummerCupSpanReadout.SpanReadout
#check Fermat.Conservation.KummerCupSpanReadout.localPairing
#check Fermat.Conservation.KummerCupSpanReadout.localPairing_apply
#check Fermat.Conservation.KummerCupSpanReadout.discreteCupSpan
#check Fermat.Conservation.KummerCupSpanReadout.discretePairing
#check Fermat.Conservation.KummerCupSpanReadout.discretePairing_apply
#check Fermat.Conservation.KummerCupSpanReadout.discretePairing_classOfUnit

#guard_depends_on
  Fermat.Conservation.KummerCupSpanReadout.cupClass,
  Fermat.Conservation.KummerTateCup.orientedCupH1Classes
#guard_depends_on
  Fermat.Conservation.KummerCupSpanReadout.cupSpan,
  Fermat.Conservation.KummerCupSpanReadout.cupGenerators
#guard_depends_on
  Fermat.Conservation.KummerCupSpanReadout.cupInSpan,
  Fermat.Conservation.KummerCupSpanReadout.cupClass_mem_cupSpan
#guard_depends_on
  Fermat.Conservation.KummerCupSpanReadout.localPairing,
  Fermat.Conservation.KummerCupSpanReadout.cupInSpan
#guard_depends_on
  Fermat.Conservation.KummerCupSpanReadout.localPairing,
  Fermat.Conservation.KummerCupSpanReadout.cupInSpan_add_left
#guard_depends_on
  Fermat.Conservation.KummerCupSpanReadout.localPairing,
  Fermat.Conservation.KummerCupSpanReadout.cupInSpan_add_right
#guard_depends_on
  Fermat.Conservation.KummerCupSpanReadout.discretePairing,
  Fermat.Conservation.KummerCupSpanReadout.localPairing
#guard_depends_on
  Fermat.Conservation.KummerCupSpanReadout.discretePairing,
  Fermat.Conservation.KummerOrientation.leftKummerMap
#guard_depends_on
  Fermat.Conservation.KummerCupSpanReadout.discretePairing,
  Fermat.Conservation.LocalKummerH1.map

/-! ### Tier-(c) total Iwasawa trace-product reduction -/

#check Fermat.Conservation.IwasawaTracePairing.TotalAugmentedCoordinates
#check Fermat.Conservation.IwasawaTracePairing.TotalAugmentedCoordinates.representative
#check Fermat.Conservation.IwasawaTracePairing.TotalAugmentedCoordinates.representative_apply
#check Fermat.Conservation.IwasawaTracePairing.TotalAugmentedCoordinates.toWildKummerCore
#check Fermat.Conservation.IwasawaTracePairing.TotalAugmentedCoordinates.toWildKummerCore_representative
#check Fermat.Conservation.IwasawaTracePairing.TotalAugmentedCoordinates.toWildKummerCore_pairing_classOfUnit_classOfUnit
#check Fermat.Conservation.IwasawaTracePairing.ArithmeticSpecification
#check Fermat.Conservation.IwasawaTracePairing.Realizes
#check Fermat.Conservation.IwasawaTracePairing.IsComparedOn
#check Fermat.Conservation.IwasawaTracePairing.Reduction
#check Fermat.Conservation.IwasawaTracePairing.Reduction.representative
#check Fermat.Conservation.IwasawaTracePairing.Reduction.toWildKummerCore
#check Fermat.Conservation.IwasawaTracePairing.Reduction.representative_apply
#check Fermat.Conservation.IwasawaTracePairing.Reduction.representative_eq_reading

#guard_depends_on
  Fermat.Conservation.IwasawaTracePairing.TotalAugmentedCoordinates.representative_apply,
  Fermat.Conservation.IwasawaTracePairing.TotalAugmentedCoordinates.representative
#guard_depends_on
  Fermat.Conservation.IwasawaTracePairing.TotalAugmentedCoordinates.toWildKummerCore_representative,
  Fermat.Conservation.IwasawaTracePairing.TotalAugmentedCoordinates.toWildKummerCore
#guard_depends_on
  Fermat.Conservation.IwasawaTracePairing.TotalAugmentedCoordinates.toWildKummerCore_pairing_classOfUnit_classOfUnit,
  Fermat.Conservation.WildKummerPairing.Core.pairing_classOfUnit_classOfUnit
#guard_depends_on
  Fermat.Conservation.IwasawaTracePairing.TotalAugmentedCoordinates.toWildKummerCore_pairing_classOfUnit_classOfUnit,
  Fermat.Conservation.IwasawaTracePairing.TotalAugmentedCoordinates.representative_apply
#guard_depends_on
  Fermat.Conservation.IwasawaTracePairing.Reduction.representative_apply,
  Fermat.Conservation.IwasawaTracePairing.Reduction.representative
#guard_depends_on
  Fermat.Conservation.IwasawaTracePairing.Reduction.representative_eq_reading,
  Fermat.Conservation.IwasawaTracePairing.Reduction.comparison
#guard_depends_on
  Fermat.Conservation.IwasawaTracePairing.Reduction.representative_eq_reading,
  Fermat.Conservation.IwasawaTracePairing.Reduction.realizes

/-! ### Actual cyclotomic lambda-adic completion

The local field is now Mathlib's adic completion at the height-one place
`lambda = (zeta_59 - 1)`.  The localization embedding, primitive root, and
proof that this place lies above 59 are all constructed.  No invariant or
reciprocity theorem is introduced by this structural bridge. -/

#check Fermat.FiftyNine.Conservation.LocalCompletion59.LocalField59
#check Fermat.FiftyNine.Conservation.LocalCompletion59.localization59
#check Fermat.FiftyNine.Conservation.LocalCompletion59.localization59_apply
#check Fermat.FiftyNine.Conservation.LocalCompletion59.globalPrimitiveRoot59
#check Fermat.FiftyNine.Conservation.LocalCompletion59.globalPrimitiveRoot59_isPrimitive
#check Fermat.FiftyNine.Conservation.LocalCompletion59.localPrimitiveRoot59
#check Fermat.FiftyNine.Conservation.LocalCompletion59.localPrimitiveRoot59_eq
#check Fermat.FiftyNine.Conservation.LocalCompletion59.localPrimitiveRoot59_isPrimitive
#check Fermat.FiftyNine.Conservation.LocalCompletion59.localPrimitiveRoot59_pow
#check Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaIdeal59
#check Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaIdeal59_isPrime
#check Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaIdeal59_ne_bot
#check Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaIdeal59_liesOver
#check Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaPlace59
#check Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaPlace59_asIdeal
#check Fermat.FiftyNine.Conservation.LocalCompletion59.LambdaLocalField59
#check Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaLocalization59
#check Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaLocalPrimitiveRoot59
#check Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaLocalPrimitiveRoot59_isPrimitive

#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalCompletion59.localPrimitiveRoot59,
  Fermat.FiftyNine.Conservation.LocalCompletion59.localization59
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalCompletion59.localPrimitiveRoot59_isPrimitive,
  Fermat.FiftyNine.Conservation.LocalCompletion59.globalPrimitiveRoot59_isPrimitive
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalCompletion59.localPrimitiveRoot59_isPrimitive,
  Fermat.FiftyNine.Conservation.LocalCompletion59.localization59
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalCompletion59.localPrimitiveRoot59_pow,
  Fermat.FiftyNine.Conservation.LocalCompletion59.localPrimitiveRoot59_isPrimitive
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaIdeal59_isPrime,
  IsCyclotomicExtension.Rat.isPrime_span_zeta_sub_one'
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaIdeal59_ne_bot,
  Fermat.FiftyNine.Conservation.LocalCompletion59.globalPrimitiveRoot59_isPrimitive
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaIdeal59_liesOver,
  IsCyclotomicExtension.Rat.liesOver_span_zeta_sub_one
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaPlace59,
  Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaIdeal59_isPrime
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaPlace59,
  Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaIdeal59_ne_bot
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaLocalization59,
  Fermat.FiftyNine.Conservation.LocalCompletion59.localization59
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaLocalPrimitiveRoot59,
  Fermat.FiftyNine.Conservation.LocalCompletion59.localPrimitiveRoot59
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaLocalPrimitiveRoot59_isPrimitive,
  Fermat.FiftyNine.Conservation.LocalCompletion59.localPrimitiveRoot59_isPrimitive

/-! ### Canonical cyclotomic action: Package B discharged

The ambient field, unit, Kummer-quotient, and place actions are constructed
canonically.  `CyclotomicValuationCovariance59 K` remains the named shape of
the crucial arithmetic law, and `cyclotomicValuationCovariance59 K` proves
it.  Consequently the strict action, complete 827-supported action, their
compatibility, and the reflected landing are all canonical constructions
with no supplied action, covariance, or landing certificate. -/

#check Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicFieldAction59
#check Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicUnitEquiv59
#check Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicUnitEquiv59_one_apply
#check Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicUnitEquiv59_mul_apply
#check Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicUnitEquiv59_maps_powerRange
#check Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicKummerHom59
#check Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicKummerHom59_mk
#check Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicKummerHom59_one_apply
#check Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicKummerHom59_mul_apply
#check Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicPlaceEquiv59
#check Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicPlaceEquiv59_asIdeal
#check Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicPlaceEquiv59_under_int
#check Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicPlaceEquiv59_mem_placesOver827_iff
#check Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.CyclotomicValuationCovariance59
#check Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicValuationCovariance59
#check Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.CyclotomicStableSupport59
#check Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicStableSupport59_empty
#check Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicStableSupport59_placesOver827
#check Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicSelmerAddHomAt59
#check Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicSelmerLinearMapAt59
#check Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicSelmerRepresentationAt59
#check Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicStrictSelmerRepresentation59
#check Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicQRelaxedSelmerRepresentation827
#check Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicEmptySupportActionCompatibility827
#check Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicReflectedEmptySupportLanding827

#guard_depends_on
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicKummerHom59,
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicUnitEquiv59_maps_powerRange
#guard_depends_on
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicKummerHom59_mul_apply,
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicUnitEquiv59_mul_apply
#guard_depends_on
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicPlaceEquiv59_mem_placesOver827_iff,
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicPlaceEquiv59_under_int
#guard_depends_on
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicStableSupport59_placesOver827,
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicPlaceEquiv59_mem_placesOver827_iff
#guard_depends_on
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicValuationCovariance59,
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicUnitEquiv59
#guard_depends_on
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicValuationCovariance59,
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicPlaceEquiv59
#guard_depends_on
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicSelmerLinearMapAt59,
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicSelmerAddHomAt59
#guard_depends_on
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicSelmerRepresentationAt59,
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicSelmerLinearMapAt59
#guard_depends_on
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicStrictSelmerRepresentation59,
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicStableSupport59_empty
#guard_depends_on
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicStrictSelmerRepresentation59,
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicValuationCovariance59
#guard_depends_on
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicQRelaxedSelmerRepresentation827,
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicStableSupport59_placesOver827
#guard_depends_on
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicQRelaxedSelmerRepresentation827,
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicValuationCovariance59
#guard_depends_on
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicEmptySupportActionCompatibility827,
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicStrictSelmerRepresentation59
#guard_depends_on
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicEmptySupportActionCompatibility827,
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicQRelaxedSelmerRepresentation827
#guard_depends_on
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicReflectedEmptySupportLanding827,
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicEmptySupportActionCompatibility827

/-! ### Canonical empty-support reflected inclusion -/

#check Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.emptySupportInclusionPadic
#check Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.emptySupportInclusionPadic_injective
#check Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.EmptySupportEigenspaceLanding
#check Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.EmptySupportActionCompatibility
#check Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.EmptySupportActionCompatibility.toEigenspaceLanding
#check Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.emptySupportEigenspaceInclusionPadic
#check Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.emptySupportEigenspaceInclusionPadic_apply
#check Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.emptySupportEigenspaceInclusionPadic_intertwines
#check Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.emptySupportEigenspaceInclusion
#check Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.emptySupportEigenspaceInclusion_apply
#check Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.emptySupportEigenspaceInclusion_injective
#check Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.toKummerQuotientAt_emptySupportEigenspaceInclusion
#check Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.toKummerClassAt_emptySupportEigenspaceInclusion
#check Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.ReflectedEmptySupportLanding827
#check Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.EmptySupportActionCompatibility827
#check Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.EmptySupportActionCompatibility827.toReflectedLanding
#check Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.oldReflectedToQRelaxed827
#check Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.oldReflectedToQRelaxed827_injective
#check Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.toKummerClassAt_oldReflectedToQRelaxed827

#guard_depends_on
  Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.emptySupportInclusionPadic_injective,
  Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.emptySupportInclusionPadic
#guard_depends_on
  Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.emptySupportEigenspaceInclusionPadic_apply,
  Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.emptySupportEigenspaceInclusionPadic
#guard_depends_on
  Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.emptySupportEigenspaceInclusionPadic_intertwines,
  Fermat.Conservation.SelmerEigenspace.mem_characterEigenspaceAt_iff
#guard_depends_on
  Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.emptySupportEigenspaceInclusion_apply,
  Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.emptySupportEigenspaceInclusion
#guard_depends_on
  Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.emptySupportEigenspaceInclusion_injective,
  Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.emptySupportInclusionPadic_injective
#guard_depends_on
  Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.toKummerQuotientAt_emptySupportEigenspaceInclusion,
  Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.emptySupportEigenspaceInclusion
#guard_depends_on
  Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.toKummerClassAt_emptySupportEigenspaceInclusion,
  Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.emptySupportEigenspaceInclusion
#guard_depends_on
  Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.oldReflectedToQRelaxed827_injective,
  Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.emptySupportEigenspaceInclusion_injective
#guard_depends_on
  Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.toKummerClassAt_oldReflectedToQRelaxed827,
  Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.toKummerClassAt_emptySupportEigenspaceInclusion

/-! ### Strict 59/827 arithmetic core and constructor -/

#check Fermat.FiftyNine.Conservation.VostokovLocalization59.OldPrimal59
#check Fermat.FiftyNine.Conservation.VostokovLocalization59.OldReflectedDual59
#check Fermat.FiftyNine.Conservation.VostokovLocalization59.OldWildInterface59
#check Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59
#check Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.wildKummerCore
#check Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.readingAt59
#check Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.readingAt59_apply
#check Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.adjoint_law
#check Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.pairing_artinHasseExpansion_left
#check Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.pairing_artinHasseExpansion_right
#check Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.pairing_campaignFactorDecomposition
#check Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.agrees_with_old
#check Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.toReflectedWildLocalizationAt59
#check Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.nonempty_reflectedWildLocalizationAt59

#guard_depends_on
  Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.wildKummerCore,
  Fermat.Conservation.WildKummerPairing.Core.ofPairing
#guard_depends_on
  Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.readingAt59,
  Fermat.Conservation.SelmerEigenspace.toKummerClassAt
#guard_depends_on
  Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.readingAt59_apply,
  Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.readingAt59
#guard_depends_on
  Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.adjoint_law,
  Fermat.Conservation.InvolutiveBase.hash_apply_single
#guard_depends_on
  Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.adjoint_law,
  MonoidAlgebra.induction_linear
#guard_depends_on
  Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.pairing_artinHasseExpansion_left,
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.ArtinHasseKummerDecomposition.decomposition
#guard_depends_on
  Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.pairing_artinHasseExpansion_right,
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.ArtinHasseKummerDecomposition.decomposition
#guard_depends_on
  Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.pairing_campaignFactorDecomposition,
  Fermat.FiftyNine.Conservation.ArtinHasseInventory.ArtinHasseFactorDecomposition.reconstruction
#guard_depends_on
  Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.agrees_with_old,
  Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.toKummerClassAt_oldReflectedToQRelaxed827
#guard_depends_on
  Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.agrees_with_old,
  Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.old_calibration
#guard_depends_on
  Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.toReflectedWildLocalizationAt59,
  Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.oldReflectedToQRelaxed827_injective
#guard_depends_on
  Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.toReflectedWildLocalizationAt59,
  Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.adjoint_law
#guard_depends_on
  Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.toReflectedWildLocalizationAt59,
  Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.agrees_with_old
#guard_depends_on
  Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.nonempty_reflectedWildLocalizationAt59,
  Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.toReflectedWildLocalizationAt59

/-! ### Cohomological 59-local adapter

This adapter feeds the quotient pairing assembled by localization, the two
Kummer maps, cup product, and the supplied local invariant into the real
59-local core.  Its final calibration remains a separate theorem argument;
the checks below do not manufacture that arithmetic comparison. -/

#check Fermat.FiftyNine.Conservation.KummerTateLocalization59.pairing
#check Fermat.FiftyNine.Conservation.KummerTateLocalization59.pairing_apply
#check Fermat.FiftyNine.Conservation.KummerTateLocalization59.discretePairing
#check Fermat.FiftyNine.Conservation.KummerTateLocalization59.discretePairing_apply
#check Fermat.FiftyNine.Conservation.KummerTateLocalization59.discretePairing_classOfUnit
#check Fermat.FiftyNine.Conservation.KummerTateLocalization59.CompletionDiscreteH2Readout59
#check Fermat.FiftyNine.Conservation.KummerTateLocalization59.actualCompletionPairing
#check Fermat.FiftyNine.Conservation.KummerTateLocalization59.actualCompletionPairing_apply
#check Fermat.FiftyNine.Conservation.KummerTateLocalization59.actualCompletionPairing_classOfUnit
#check Fermat.FiftyNine.Conservation.KummerTateLocalization59.toReflectedWildKummerCoreAt59
#check Fermat.FiftyNine.Conservation.KummerTateLocalization59.toReflectedWildKummerCoreAt59_pairing_apply
#check Fermat.FiftyNine.Conservation.KummerTateLocalization59.toCanonicalReflectedWildKummerCoreAt59
#check Fermat.FiftyNine.Conservation.KummerTateLocalization59.toCanonicalDiscreteReflectedWildKummerCoreAt59
#check Fermat.FiftyNine.Conservation.KummerTateLocalization59.toCanonicalDiscreteReflectedWildKummerCoreAt59_pairing_apply
#check Fermat.FiftyNine.Conservation.KummerTateLocalization59.toActualCompletionCanonicalReflectedWildKummerCoreAt59
#check Fermat.FiftyNine.Conservation.KummerTateLocalization59.toActualCompletionCanonicalReflectedWildKummerCoreAt59_pairing_apply

#guard_depends_on
  Fermat.FiftyNine.Conservation.KummerTateLocalization59.pairing,
  Fermat.Conservation.CohomologicalKummerPairing.globalPairing
-- `pairing_apply` is the third definitional readback in this chain, so its
-- expanded cup formula is a signature audit (`#check`) rather than a
-- value-dependency claim about its `rfl` proof body.
#guard_depends_on
  Fermat.FiftyNine.Conservation.KummerTateLocalization59.discretePairing,
  Fermat.Conservation.DiscreteKummerTatePairing.localPairing
#guard_depends_on
  Fermat.FiftyNine.Conservation.KummerTateLocalization59.discretePairing,
  Fermat.Conservation.LocalKummerTransport.Pairing.pullback
#guard_depends_on
  Fermat.FiftyNine.Conservation.KummerTateLocalization59.discretePairing_apply,
  Fermat.Conservation.KummerOrientation.leftKummerMap
#guard_depends_on
  Fermat.FiftyNine.Conservation.KummerTateLocalization59.discretePairing_apply,
  Fermat.Conservation.LocalKummerH1.map
#guard_depends_on
  Fermat.FiftyNine.Conservation.KummerTateLocalization59.discretePairing_classOfUnit,
  Fermat.Conservation.LocalKummerTransport.unitMap
#guard_depends_on
  Fermat.FiftyNine.Conservation.KummerTateLocalization59.actualCompletionPairing,
  Fermat.FiftyNine.Conservation.KummerTateLocalization59.discretePairing
#guard_depends_on
  Fermat.FiftyNine.Conservation.KummerTateLocalization59.actualCompletionPairing,
  Fermat.FiftyNine.Conservation.LocalCompletion59.localization59
#guard_depends_on
  Fermat.FiftyNine.Conservation.KummerTateLocalization59.actualCompletionPairing,
  Fermat.FiftyNine.Conservation.LocalCompletion59.localPrimitiveRoot59
#guard_depends_on
  Fermat.FiftyNine.Conservation.KummerTateLocalization59.toReflectedWildKummerCoreAt59,
  Fermat.FiftyNine.Conservation.KummerTateLocalization59.pairing
#guard_depends_on
  Fermat.FiftyNine.Conservation.KummerTateLocalization59.toReflectedWildKummerCoreAt59_pairing_apply,
  Fermat.FiftyNine.Conservation.KummerTateLocalization59.toReflectedWildKummerCoreAt59
#guard_depends_on
  Fermat.FiftyNine.Conservation.KummerTateLocalization59.toCanonicalReflectedWildKummerCoreAt59,
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicReflectedEmptySupportLanding827
#guard_depends_on
  Fermat.FiftyNine.Conservation.KummerTateLocalization59.toCanonicalReflectedWildKummerCoreAt59,
  Fermat.FiftyNine.Conservation.KummerTateLocalization59.toReflectedWildKummerCoreAt59
#guard_depends_on
  Fermat.FiftyNine.Conservation.KummerTateLocalization59.toCanonicalDiscreteReflectedWildKummerCoreAt59,
  Fermat.FiftyNine.Conservation.KummerTateLocalization59.discretePairing
#guard_depends_on
  Fermat.FiftyNine.Conservation.KummerTateLocalization59.toCanonicalDiscreteReflectedWildKummerCoreAt59,
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicReflectedEmptySupportLanding827
#guard_depends_on
  Fermat.FiftyNine.Conservation.KummerTateLocalization59.toCanonicalDiscreteReflectedWildKummerCoreAt59_pairing_apply,
  Fermat.FiftyNine.Conservation.KummerTateLocalization59.toCanonicalDiscreteReflectedWildKummerCoreAt59
#guard_depends_on
  Fermat.FiftyNine.Conservation.KummerTateLocalization59.toActualCompletionCanonicalReflectedWildKummerCoreAt59,
  Fermat.FiftyNine.Conservation.KummerTateLocalization59.toCanonicalDiscreteReflectedWildKummerCoreAt59
#guard_depends_on
  Fermat.FiftyNine.Conservation.KummerTateLocalization59.toActualCompletionCanonicalReflectedWildKummerCoreAt59,
  Fermat.FiftyNine.Conservation.LocalCompletion59.localization59
#guard_depends_on
  Fermat.FiftyNine.Conservation.KummerTateLocalization59.toActualCompletionCanonicalReflectedWildKummerCoreAt59_pairing_apply,
  Fermat.FiftyNine.Conservation.KummerTateLocalization59.toActualCompletionCanonicalReflectedWildKummerCoreAt59

/-! ### Continuous Kummer--Tate adapter at the literal lambda place

This layer keeps the complete continuous `H²(mu_59)` class until an explicit
linear or continuous-linear readout is supplied.  The checks therefore cover
the two differently typed `H¹` seats, the retained `H²` target, scalarization,
and global pullback without asserting a local invariant or comparison theorem.
-/

#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.LambdaOrientedContinuousH1
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.LambdaRootsContinuousH1
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.LambdaRootsContinuousH2
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.LambdaOrientedContinuousH2
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2CoefficientOrientationEquiv59
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2CoefficientOrientationEquiv59_apply
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.LambdaContinuousCup59
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.LambdaContinuousH2Readout59
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.exists_conditionalNoncanonicalLambdaH2Readout_eq_one
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.LambdaOrientedContinuousH2Readout59
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2SuppliedLinearReadoutTransportEquiv59
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2SuppliedLinearReadoutTransportEquiv59_apply
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2SuppliedLinearReadoutTransportEquiv59_symm_apply
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.LambdaContinuousH2ContinuousReadout59
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.LambdaOrientedContinuousH2ContinuousReadout59
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2SuppliedContinuousReadoutTransportEquiv59
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2SuppliedContinuousReadoutTransportEquiv59_apply
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2SuppliedContinuousReadoutTransportEquiv59_symm_apply
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalH2PairingFromCup
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalH2PairingFromCup_apply
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalPairingFromCup
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalPairingFromCup_apply
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalPairingFromContinuousReadout
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalPairingFromContinuousReadout_apply
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaGlobalPairingFromCup
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaGlobalPairingFromCup_apply
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaContinuousCup59
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaContinuousCup59_apply
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalH2Pairing
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalH2Pairing_apply
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalPairing
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalPairing_apply
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalPairingWithContinuousReadout
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalPairingWithContinuousReadout_apply
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaGlobalPairing
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaGlobalPairing_apply
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.toCanonicalReflectedWildKummerCoreAt59
#check Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.toCanonicalReflectedWildKummerCoreAt59_pairing_apply

/-! ### Unconditional normalized pairing and downstream wild localization

The exact norm obstruction now supplies a noncanonical algebraic readout on
the retained continuous `H²(mu_59)` target.  Composing it with the genuine
continuous cup gives total local and global Kummer pairings, normalized on
both the twisted-lambda and unit-60 classes.  Restriction to the old seated
carrier constructs its own calibrated interface and fires the q-relaxed
localization consumer.  This does not claim that the algebraic readout is a
continuous-linear map or identify the constructed interface with a separately
supplied historical reading. -/

#check Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.oldReadingOfPairing
#check Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.oldReadingOfPairing_apply
#check Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.oldReadingOfPairing_adjoint
#check Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.oldWildInterfaceOfPairing
#check Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.oldWildInterfaceOfPairing_reading
#check Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.pairing_calibrates_oldWildInterfaceOfPairing
#check Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.oldWildInterfaceOfPairing_eq_iff_calibration
#check Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.continuousOldWildInterface59
#check Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.continuousOldWildInterface59_reading
#check Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.continuousReflectedWildKummerCoreAt59
#check Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.continuousReflectedWildKummerCoreAt59_pairing
#check Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.continuousReflectedWildLocalizationAt59
#check Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.exists_normalizedContinuousReflectedWildKummerCoreAt59
#check Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.exists_normalizedContinuousReflectedWildLocalizationAt59

#check Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.normalizedInflationReadout59
#check Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.normalizedInflationReadout59_comp
#check Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.normalizedInflationReadout59_twistedLambdaCup
#check Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.normalizedInflationReadout59_unit60Cup
#check Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.normalizedInflationReadout59_twistedLambdaCup_eq_neg_logResidue
#check Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.normalizedLambdaLocalPairing59
#check Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.normalizedLambdaGlobalPairing59
#check Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.normalizedLambdaLocalPairing59_apply
#check Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.normalizedLambdaGlobalPairing59_apply
#check Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.globalTwistedLambdaRadicandUnit59
#check Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.globalUnit60RadicandUnit59
#check Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.unitMap_globalTwistedLambdaRadicandUnit59
#check Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.unitMap_globalUnit60RadicandUnit59
#check Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.unitMap_globalPrimitiveUnit59
#check Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.normalizedLambdaLocalPairing59_twistedLambda_primitive
#check Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.normalizedLambdaLocalPairing59_unit60_primitive
#check Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.normalizedLambdaGlobalPairing59_twistedLambda_primitive
#check Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.normalizedLambdaGlobalPairing59_unit60_primitive
#check Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.toNormalizedReflectedWildKummerCoreAt59
#check Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.toNormalizedReflectedWildKummerCoreAt59_pairing_apply

#check Fermat.FiftyNine.Conservation.NormalizedContinuousWildLocalization59.normalizedOldWildInterface59
#check Fermat.FiftyNine.Conservation.NormalizedContinuousWildLocalization59.normalizedOldWildInterface59_reading
#check Fermat.FiftyNine.Conservation.NormalizedContinuousWildLocalization59.normalizedReflectedWildKummerCore59
#check Fermat.FiftyNine.Conservation.NormalizedContinuousWildLocalization59.normalizedReflectedWildKummerCore59_pairing
#check Fermat.FiftyNine.Conservation.NormalizedContinuousWildLocalization59.normalizedReflectedWildKummerCore59_calibration
#check Fermat.FiftyNine.Conservation.NormalizedContinuousWildLocalization59.normalizedReflectedWildKummerCore59_unit60_primitive
#check Fermat.FiftyNine.Conservation.NormalizedContinuousWildLocalization59.normalizedReflectedWildLocalization59
#check Fermat.FiftyNine.Conservation.NormalizedContinuousWildLocalization59.normalizedReflectedWildLocalization59_agrees_with_old

/-! Fixed attention plus one nonzero reflected coordinate algebraically
constructs the pointed incidence.  Fourier seating and a typed reflected lift
supply those inputs without selecting a complement or splitting. -/

#check Fermat.FiftyNine.Conservation.AlgebraicPointedIncidence827.reflectedCoordinatePairing827_flip_injective
#check Fermat.FiftyNine.Conservation.AlgebraicPointedIncidence827.pointedTateIncidence827_of_fixed_of_localization_ne_zero
#check Fermat.FiftyNine.Conservation.AlgebraicPointedIncidence827.reflectedPointedLocalization827_ne_zero_of_lift
#check Fermat.FiftyNine.Conservation.AlgebraicPointedIncidence827.pointedTateIncidence827_of_fourierSeating_of_localization_ne_zero
#check Fermat.FiftyNine.Conservation.AlgebraicPointedIncidence827.pointedTateIncidence827_of_fourierSeating_of_lift

/-! Reciprocity for the exact one-column localization now derives wild
lawfulness.  The normalized readout endpoint therefore constructs the
localization, boundary witness, retained fiber, and lawfulness internally;
only incidence/seating, class-gauge processing, and reciprocity remain as
explicit inputs. -/

#check Fermat.FiftyNine.Conservation.CyclotomicLocalizationEquivariance827.indexedPlaceOrbitEquiv827_eq_cyclotomicPlaceEquiv59
#check Fermat.FiftyNine.Conservation.CyclotomicLocalizationEquivariance827.cyclotomicQLocalizationEquivariance827
#check Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827.projectedCandidateSClassObstruction827_eq_one_of_lift
#check Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827.classSilentPointedCoordinate827
#check Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827.classSilentPointedCoordinate827_apply
#check Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827.nonempty_reflectedQRelaxedLocalizationLift827_iff
#check Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827.qLocalizationCoordinate_ne_zero_at_every_place_of_lift
#check Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827.nonempty_cyclotomicReflectedQRelaxedLocalizationLift827_iff
#check Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827.tameSilence827_ne_zero_of_lift

/-! Rational 827 is a concrete relaxed source in the trivial character
mode.  Projecting it supplies an actual reflected localization lift only
under the explicit condition that the reflected character is trivial; the
general reflected-character seam remains visible. -/

#check Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827.attestationPrimeFieldUnit827
#check Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827.attestationPrime_valuation_toAdd_eq_neg_one
#check Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827.attestationPrime_valuation_toAdd_eq_zero_of_not_mem
#check Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827.attestationPrimeSource827
#check Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827.cyclotomicQRelaxedSelmerRepresentation827_attestationPrimeSource
#check Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827.attestationPrimeSource827_ne_zero
#check Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827.attestationPrimeSource827_mem_trivial_characterEigenspace
#check Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827.attestationPrimeSource827_mem_reflectedCharacter_of_eq_one

#check Fermat.FiftyNine.Conservation.TrivialReflectedAttestationPrimeLift827.attestationPrime_reflectedProjector_eq_source827
#check Fermat.FiftyNine.Conservation.TrivialReflectedAttestationPrimeLift827.attestationPrimeDetectorSUnit827
#check Fermat.FiftyNine.Conservation.TrivialReflectedAttestationPrimeLift827.fromSUnitLift_attestationPrimeDetectorSUnit827
#check Fermat.FiftyNine.Conservation.TrivialReflectedAttestationPrimeLift827.projectedCandidateSClassObstruction827_attestationPrime_eq_one
#check Fermat.FiftyNine.Conservation.TrivialReflectedAttestationPrimeLift827.qLocalizationCoordinate827_attestationPrime_ne_zero
#check Fermat.FiftyNine.Conservation.TrivialReflectedAttestationPrimeLift827.attestationPrimeReflectedLocalizationLift827
#check Fermat.FiftyNine.Conservation.TrivialReflectedAttestationPrimeLift827.nonempty_attestationPrimeReflectedLocalizationLift827

#check Fermat.FiftyNine.Conservation.UlamReadout827.wildLawfulness827_of_reciprocity
#check Fermat.FiftyNine.Conservation.UlamReadout827.wildProcessesAtLeastSevenA_zero_iff
#check Fermat.FiftyNine.Conservation.UlamReadout827.vandiverSevenA_of_classGauge_eq_zero
#check Fermat.FiftyNine.Conservation.UlamReadout827.wildCoefficient827_eq_zero_of_reciprocity
#check Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.oldPrimal59_nsmul_eq_zero
#check Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedQLocalizationEquivariance827
#check Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedReflectedWildCarrierExtension59
#check Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedReflectedWildCarrierExtension59_reading
#check Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedBoundaryFunctional59_ne_zero
#check Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedReflectedFiber59_nonempty
#check Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.NormalizedWildLawfulness59
#check Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildCoefficient59
#check Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildCoefficient59_factorization
#check Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.NormalizedTameSilenceReciprocity59
#check Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildLawfulness59_of_reciprocity
#check Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildCoefficientOfReciprocity59
#check Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildCoefficientOfReciprocity59_eq_zero
#check Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedPointedIncidence59OfLift
#check Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedPointedIncidence59OfLiftCanonical
#check Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildCoefficientOfLift59
#check Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildCoefficientOfLift59_eq_zero
#check Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildCoefficientOfCanonicalLift59
#check Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildCoefficientOfCanonicalLift59_eq_zero
#check Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedProcessesAtLeastSevenA_iff_gauge_eq_zero
#check Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedLiftProcessesAtLeastSevenA_iff_gauge_eq_zero
#check Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedCanonicalLiftProcessesAtLeastSevenA_iff_gauge_eq_zero
#check Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.vandiverSevenA_of_normalizedContinuousReadout
#check Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.vandiverSevenA_of_normalizedContinuousReciprocity
#check Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.vandiverSevenA_of_normalizedContinuousLift
#check Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.vandiverSevenA_of_normalizedContinuousCanonicalLift

/-! The statewise bridge restores the normalization denominator before
localization and exposes, rather than invents, the remaining historical
identification with the old-primal state. -/

#check Fermat.FiftyNine.Conservation.StatewiseTwistedLambdaBridge59.rawPlusKummerClass59_eq_normalizedPlus_add_denominator
#check Fermat.FiftyNine.Conservation.StatewiseTwistedLambdaBridge59.localize_fixedDenominatorKummerClass59
#check Fermat.FiftyNine.Conservation.StatewiseTwistedLambdaBridge59.localizedRawPlusKummerClass59_eq_normalizedPlus_add_lambda
#check Fermat.FiftyNine.Conservation.StatewiseTwistedLambdaBridge59.localizedNormalizedPlus_eq_twistUnit_iff_rawPlus_eq_twistedLambda
#check Fermat.FiftyNine.Conservation.StatewiseTwistedLambdaBridge59.localizedStatewiseRepresentative_readback59
#check Fermat.FiftyNine.Conservation.StatewiseTwistedLambdaBridge59.localizedStatewise_eq_twistUnit_iff_rawPlus_eq_twistedLambda_of_eq_normalized

/-! ### Explicit carry class and the exact local cyclic-lift seam

The finite carry class is concrete and nonzero.  After pullback, its
vanishing is exactly equivalent to a continuous `C59²` lift.  The specified
twisted-lambda character and roots-valued H² class are therefore checked
here, while their no-lift arithmetic remains a visible proposition rather
than an installed witness.
-/

/-! The finite cyclic `H²` normalization is now prime-parametric.  The
historical `59` declarations are retained and definitionally identified with
the generic specialization. -/

#check Fermat.Conservation.PrimeCyclicH2.CyclicGroup
#check Fermat.Conservation.PrimeCyclicH2.coefficients
#check Fermat.Conservation.PrimeCyclicH2.generator
#check Fermat.Conservation.PrimeCyclicH2.cyclicGroup_card
#check Fermat.Conservation.PrimeCyclicH2.generator_ne_one
#check Fermat.Conservation.PrimeCyclicH2.generator_generates
#check Fermat.Conservation.PrimeCyclicH2.invariantOne
#check Fermat.Conservation.PrimeCyclicH2.coefficients_norm_eq_zero
#check Fermat.Conservation.PrimeCyclicH2.finiteCyclicH2Class
#check Fermat.Conservation.PrimeCyclicH2.finiteCyclicH2Class_ne_zero
#check Fermat.Conservation.PrimeCyclicH2.finiteCyclicH2Class_spans
#check Fermat.Conservation.PrimeCyclicH2.finiteCyclicH2GeneratorMap
#check Fermat.Conservation.PrimeCyclicH2.finiteCyclicH2GeneratorMap_bijective
#check Fermat.Conservation.PrimeCyclicH2.finiteCyclicH2LinearEquiv
#check Fermat.Conservation.PrimeCyclicH2.finiteCyclicH2ReadoutEquiv
#check Fermat.Conservation.PrimeCyclicH2.finiteCyclicH2ReadoutEquiv_class
#check Fermat.Conservation.PrimeCyclicH2.carry
#check Fermat.Conservation.PrimeCyclicH2.carryFunction
#check Fermat.Conservation.PrimeCyclicH2.carryFunction_mem_cocycles₂
#check Fermat.Conservation.PrimeCyclicH2.carryCocycle
#check Fermat.Conservation.PrimeCyclicH2.carryCocycle_apply
#check Fermat.Conservation.PrimeCyclicH2.val_neg_one_prime
#check Fermat.Conservation.PrimeCyclicH2.carry_generator_apply
#check Fermat.Conservation.PrimeCyclicH2.sum_carryCocycle_generator
#check Fermat.Conservation.PrimeCyclicH2.sum_discreteBoundary_generator
#check Fermat.Conservation.PrimeCyclicH2.carryCocycle_not_mem_coboundaries₂
#check Fermat.Conservation.PrimeCyclicH2.continuousCoefficients
#check Fermat.Conservation.PrimeCyclicH2.continuousCarryCycle
#check Fermat.Conservation.PrimeCyclicH2.continuousCarryCycle_not_boundary
#check Fermat.Conservation.PrimeCyclicH2.continuousCarryH2Class
#check Fermat.Conservation.PrimeCyclicH2.continuousCarryH2Class_ne_zero
#check Fermat.Conservation.PrimeCyclicH2.cyclicCycleValue
#check Fermat.Conservation.PrimeCyclicH2.cyclicCycleSum
#check Fermat.Conservation.PrimeCyclicH2.cyclicCycleSum_continuousCarryCycle
#check Fermat.Conservation.PrimeCyclicH2.sum_continuousBoundary_generator
#check Fermat.Conservation.PrimeCyclicH2.cyclicCycleSum_eq_zero_of_h2Projection_eq_zero
#check Fermat.Conservation.PrimeCyclicH2.ker_h2Projection_le_ker_cyclicCycleSum
#check Fermat.Conservation.PrimeCyclicH2.h2Projection_surjective
#check Fermat.Conservation.PrimeCyclicH2.continuousCyclicH2Readout
#check Fermat.Conservation.PrimeCyclicH2.continuousCyclicH2Readout_h2Projection
#check Fermat.Conservation.PrimeCyclicH2.actualContinuousCyclicH2Readout
#check Fermat.Conservation.PrimeCyclicH2.actualContinuousCyclicH2Readout_continuousCarryH2Class
#check Fermat.Conservation.PrimeCyclicH2.actualContinuousCyclicH2Generator
#check Fermat.Conservation.PrimeCyclicH2.actualContinuousCyclicH2Readout_generator
#check Fermat.Conservation.PrimeCyclicH2.actualContinuousCyclicH2Readout_surjective
#check Fermat.Conservation.PrimeCyclicH2.actualContinuousCyclicH2Generator_injective
#check Fermat.Conservation.PrimeCyclicH2.discreteTwoOfContinuous
#check Fermat.Conservation.PrimeCyclicH2.discreteTwoOfContinuous_mem_cocycles₂
#check Fermat.Conservation.PrimeCyclicH2.discreteCocycleOfContinuous
#check Fermat.Conservation.PrimeCyclicH2.continuousCycleOfDiscrete_discreteCocycleOfContinuous
#check Fermat.Conservation.PrimeCyclicH2.continuousBoundary_of_mem_discreteCoboundaries
#check Fermat.Conservation.PrimeCyclicH2.continuousCycleOfDiscreteLinear
#check Fermat.Conservation.PrimeCyclicH2.discreteCarryH2Class_ne_zero
#check Fermat.Conservation.PrimeCyclicH2.discreteCarryH2Class_spans
#check Fermat.Conservation.PrimeCyclicH2.continuousCarryCycle_spans_h2Projection
#check Fermat.Conservation.PrimeCyclicH2.continuousCarryH2Class_spans
#check Fermat.Conservation.PrimeCyclicH2.actualContinuousCyclicH2Readout_injective
#check Fermat.Conservation.PrimeCyclicH2.actualContinuousCyclicH2Readout_bijective
#check Fermat.Conservation.PrimeCyclicH2.actualContinuousCyclicH2LinearEquiv
#check Fermat.Conservation.PrimeCyclicH2.actualContinuousCyclicH2LinearEquiv_apply
#check Fermat.Conservation.PrimeCyclicH2.actualContinuousCyclicH2LinearEquiv_symm_apply

#check Fermat.Conservation.PrimeCyclicH2At59.generator_eq_generator59
#check Fermat.Conservation.PrimeCyclicH2At59.carry_eq_carry59
#check Fermat.Conservation.PrimeCyclicH2At59.carryCocycle_eq_carryCocycle59
#check Fermat.Conservation.PrimeCyclicH2At59.continuousCarryCycle_eq_continuousCarryCycle59
#check Fermat.Conservation.PrimeCyclicH2At59.continuousCarryH2Class_eq_continuousCarryH2Class59
#check Fermat.Conservation.PrimeCyclicH2At59.cyclicCycleSum_eq_cyclicCycleSum59
#check Fermat.Conservation.PrimeCyclicH2At59.actualContinuousCyclicH2Readout_eq_59
#check Fermat.Conservation.PrimeCyclicH2At59.actualContinuousCyclicH2Generator_eq_59
#check Fermat.Conservation.PrimeCyclicH2At59.actualContinuousCyclicH2LinearEquiv_eq_59

#check Fermat.Conservation.PrimeCyclicExtension.CyclicGroup
#check Fermat.Conservation.PrimeCyclicExtension.CyclicGroupSquared
#check Fermat.Conservation.PrimeCyclicExtension.p_dvd_p_sq
#check Fermat.Conservation.PrimeCyclicExtension.reduction
#check Fermat.Conservation.PrimeCyclicExtension.standardSection
#check Fermat.Conservation.PrimeCyclicExtension.kernelEmbedValue
#check Fermat.Conservation.PrimeCyclicExtension.reduction_standardSection
#check Fermat.Conservation.PrimeCyclicExtension.reduction_kernelEmbedValue
#check Fermat.Conservation.PrimeCyclicExtension.cast_p_mul_val_add
#check Fermat.Conservation.PrimeCyclicExtension.kernelEmbed
#check Fermat.Conservation.PrimeCyclicExtension.standardSection_mul
#check Fermat.Conservation.PrimeCyclicExtension.kernelCoordinate
#check Fermat.Conservation.PrimeCyclicExtension.kernelEmbed_kernelCoordinate
#check Fermat.Conservation.PrimeCyclicExtension.kernelCoordinate_kernelEmbed
#check Fermat.Conservation.PrimeCyclicExtension.kernelEmbed_injective
#check Fermat.Conservation.PrimeCyclicExtension.reduction_surjective
#check Fermat.Conservation.PrimeCyclicExtension.reduction_eq_one_iff_exists_kernelEmbed
#check Fermat.Conservation.PrimeCyclicExtension.kernelEmbed_range_eq_reduction_ker

/-! The entire carry--Kummer--Albert construction now has a prime-parametric
spine.  The `At59` modules below are definitional compatibility receipts,
not independent copies of the construction. -/

#check Fermat.Conservation.PrimeContinuousHomogeneousPullback.coefficients
#check Fermat.Conservation.PrimeContinuousHomogeneousPullback.coefficients_action
#check Fermat.Conservation.PrimeContinuousHomogeneousPullback.precompose₁
#check Fermat.Conservation.PrimeContinuousHomogeneousPullback.precompose₂
#check Fermat.Conservation.PrimeContinuousHomogeneousPullback.precompose₃
#check Fermat.Conservation.PrimeContinuousHomogeneousPullback.precompose₄
#check Fermat.Conservation.PrimeContinuousHomogeneousPullback.threeValue
#check Fermat.Conservation.PrimeContinuousHomogeneousPullback.twoValue_invariant
#check Fermat.Conservation.PrimeContinuousHomogeneousPullback.threeValue_invariant
#check Fermat.Conservation.PrimeContinuousHomogeneousPullback.pullbackOne
#check Fermat.Conservation.PrimeContinuousHomogeneousPullback.pullbackTwo
#check Fermat.Conservation.PrimeContinuousHomogeneousPullback.pullbackThree
#check Fermat.Conservation.PrimeContinuousHomogeneousPullback.pullback_differential_one_two
#check Fermat.Conservation.PrimeContinuousHomogeneousPullback.pullback_differential_two_three
#check Fermat.Conservation.PrimeContinuousHomogeneousPullback.pullbackCycleTwo
#check Fermat.Conservation.PrimeContinuousHomogeneousPullback.pullbackCycleTwo_of_boundary

#check Fermat.Conservation.PrimeContinuousCarryLift.pulledCarryCycle
#check Fermat.Conservation.PrimeContinuousCarryLift.NoContinuousLift
#check Fermat.Conservation.PrimeContinuousCarryLift.primitiveValue
#check Fermat.Conservation.PrimeContinuousCarryLift.liftedValue
#check Fermat.Conservation.PrimeContinuousCarryLift.boundary_primitive_equation
#check Fermat.Conservation.PrimeContinuousCarryLift.primitiveValue_one
#check Fermat.Conservation.PrimeContinuousCarryLift.liftedValue_one
#check Fermat.Conservation.PrimeContinuousCarryLift.liftAlgebra_identity
#check Fermat.Conservation.PrimeContinuousCarryLift.liftedValue_mul
#check Fermat.Conservation.PrimeContinuousCarryLift.continuous_primitiveValue
#check Fermat.Conservation.PrimeContinuousCarryLift.continuous_liftedValue
#check Fermat.Conservation.PrimeContinuousCarryLift.boundaryLift
#check Fermat.Conservation.PrimeContinuousCarryLift.reduction_comp_boundaryLift
#check Fermat.Conservation.PrimeContinuousCarryLift.exists_continuous_lift_of_pulledCarryCycle_boundary
#check Fermat.Conservation.PrimeContinuousCarryLift.pulledCarryCycle_not_boundary_of_noContinuousLift
#check Fermat.Conservation.PrimeContinuousCarryLift.pulledCarryH2Class
#check Fermat.Conservation.PrimeContinuousCarryLift.pulledCarryH2Class_ne_zero_of_noContinuousLift
#check Fermat.Conservation.PrimeContinuousCarryLift.liftCorrection
#check Fermat.Conservation.PrimeContinuousCarryLift.comparison_mem_kernel
#check Fermat.Conservation.PrimeContinuousCarryLift.comparison_eq_kernelEmbed
#check Fermat.Conservation.PrimeContinuousCarryLift.section_eq_lift_mul_kernel
#check Fermat.Conservation.PrimeContinuousCarryLift.liftCorrection_add
#check Fermat.Conservation.PrimeContinuousCarryLift.continuous_liftCorrection
#check Fermat.Conservation.PrimeContinuousCarryLift.liftPrimitiveRaw
#check Fermat.Conservation.PrimeContinuousCarryLift.liftPrimitive
#check Fermat.Conservation.PrimeContinuousCarryLift.differential_liftPrimitive
#check Fermat.Conservation.PrimeContinuousCarryLift.pulledCarryCycle_boundary_of_exists_continuous_lift
#check Fermat.Conservation.PrimeContinuousCarryLift.pulledCarryCycle_boundary_iff_exists_continuous_lift
#check Fermat.Conservation.PrimeContinuousCarryLift.pulledCarryCycle_not_boundary_iff_noContinuousLift
#check Fermat.Conservation.PrimeContinuousCarryLift.pulledCarryH2Class_eq_zero_iff_exists_continuous_lift
#check Fermat.Conservation.PrimeContinuousCarryLift.pulledCarryH2Class_ne_zero_iff_noContinuousLift

#check Fermat.Conservation.PrimeContinuousCarryLiftAt59.coefficients_eq_59
#check Fermat.Conservation.PrimeContinuousCarryLiftAt59.pullbackOne_eq_59
#check Fermat.Conservation.PrimeContinuousCarryLiftAt59.pullbackTwo_eq_59
#check Fermat.Conservation.PrimeContinuousCarryLiftAt59.pullbackCycleTwo_eq_59
#check Fermat.Conservation.PrimeContinuousCarryLiftAt59.reduction_eq_59
#check Fermat.Conservation.PrimeContinuousCarryLiftAt59.standardSection_eq_59
#check Fermat.Conservation.PrimeContinuousCarryLiftAt59.kernelEmbed_eq_59
#check Fermat.Conservation.PrimeContinuousCarryLiftAt59.pulledCarryCycle_eq_59
#check Fermat.Conservation.PrimeContinuousCarryLiftAt59.noContinuousLift_eq_59
#check Fermat.Conservation.PrimeContinuousCarryLiftAt59.pulledCarryH2Class_eq_59
#check Fermat.Conservation.PrimeContinuousCarryLiftAt59.liftCorrection_eq_59
#check Fermat.Conservation.PrimeContinuousCarryLiftAt59.liftPrimitive_eq_59
#check Fermat.Conservation.PrimeContinuousCarryLiftAt59.pulledCarryH2Class59_eq_zero_iff_exists_continuous_lift

#check Fermat.Conservation.PrimeKummerCyclicQuotient.kummerPolynomial
#check Fermat.Conservation.PrimeKummerCyclicQuotient.kummerPolynomial_irreducible
#check Fermat.Conservation.PrimeKummerCyclicQuotient.kummerExtension
#check Fermat.Conservation.PrimeKummerCyclicQuotient.kummerExtension_isSplittingField
#check Fermat.Conservation.PrimeKummerCyclicQuotient.kummerGalEquiv
#check Fermat.Conservation.PrimeKummerCyclicQuotient.kummerCharacter
#check Fermat.Conservation.PrimeKummerCyclicQuotient.kummerCharacter_surjective
#check Fermat.Conservation.PrimeKummerCyclicQuotientAt59.kummerPolynomial59_eq_primeKummerPolynomial
#check Fermat.Conservation.PrimeKummerCyclicQuotientAt59.kummerExtension59_eq_primeKummerExtension
#check Fermat.Conservation.PrimeKummerCyclicQuotientAt59.kummerGalEquiv59_eq_primeKummerGalEquiv
#check Fermat.Conservation.PrimeKummerCyclicQuotientAt59.kummerCharacter59_eq_primeKummerCharacter

#check Fermat.Conservation.PrimeKummerCarryLiftCriterion.kummerCarryCycle
#check Fermat.Conservation.PrimeKummerCarryLiftCriterion.kummerCarryH2Class
#check Fermat.Conservation.PrimeKummerCarryLiftCriterion.KummerNoContinuousLift
#check Fermat.Conservation.PrimeKummerCarryLiftCriterion.kummerCarryCycle_boundary_iff_exists_continuous_lift
#check Fermat.Conservation.PrimeKummerCarryLiftCriterion.kummerCarryH2Class_eq_zero_iff_exists_continuous_lift
#check Fermat.Conservation.PrimeKummerCarryLiftCriterion.kummerCarryH2Class_ne_zero_iff_noContinuousLift

#check Fermat.Conservation.PrimeKummerCharacterComparison.splittingRoot
#check Fermat.Conservation.PrimeKummerCharacterComparison.radicand_ne_zero
#check Fermat.Conservation.PrimeKummerCharacterComparison.splittingRoot_pow
#check Fermat.Conservation.PrimeKummerCharacterComparison.splittingRootUnit
#check Fermat.Conservation.PrimeKummerCharacterComparison.splittingRootUnit_pow
#check Fermat.Conservation.PrimeKummerCharacterComparison.radicandUnit
#check Fermat.Conservation.PrimeKummerCharacterComparison.restrictedGalois_acts_on_splittingRoot
#check Fermat.Conservation.PrimeKummerCharacterComparison.algebraicPowerRoot
#check Fermat.Conservation.PrimeKummerCharacterComparison.coordinate_algebraicPowerRoot
#check Fermat.Conservation.PrimeKummerCharacterComparison.cocycleValue_eq_algebraicPowerRoot
#check Fermat.Conservation.PrimeKummerCharacterComparison.orientedKummerValue
#check Fermat.Conservation.PrimeKummerCharacterComparison.orientedKummerValue_mul
#check Fermat.Conservation.PrimeKummerCharacterComparison.orientedKummerCharacter
#check Fermat.Conservation.PrimeKummerCharacterComparison.orientedKummerValue_eq_kummerCharacter_toAdd
#check Fermat.Conservation.PrimeKummerCharacterComparison.kummerCharacter_eq_orientedKummerCharacter
#check Fermat.Conservation.PrimeKummerCharacterComparisonAt59.splittingRoot59_eq_primeSplittingRoot
#check Fermat.Conservation.PrimeKummerCharacterComparisonAt59.splittingRootUnit59_eq_primeSplittingRootUnit
#check Fermat.Conservation.PrimeKummerCharacterComparisonAt59.radicandUnit59_eq_primeRadicandUnit
#check Fermat.Conservation.PrimeKummerCharacterComparisonAt59.algebraicPowerRoot59_eq_primeAlgebraicPowerRoot
#check Fermat.Conservation.PrimeKummerCharacterComparisonAt59.orientedKummerValue59_eq_primeOrientedKummerValue
#check Fermat.Conservation.PrimeKummerCharacterComparisonAt59.orientedKummerCharacter59_eq_primeOrientedKummerCharacter
#check Fermat.Conservation.PrimeKummerCharacterComparisonAt59.kummerCharacter59_eq_orientedKummerCharacter_via_prime

#check Fermat.Conservation.PrimeOrientedCarryH2Class.orientedCarryH2Class
#check Fermat.Conservation.PrimeOrientedCarryH2Class.orientedCarryH2Class_ne_zero_of_noContinuousLift
#check Fermat.Conservation.PrimeOrientedCarryH2Class.orientedCarryH2Class_eq_zero_iff_exists_continuous_lift
#check Fermat.Conservation.PrimeOrientedCarryH2Class.rootsCarryH2Class
#check Fermat.Conservation.PrimeOrientedCarryH2Class.orientH2Equiv_rootsCarryH2Class
#check Fermat.Conservation.PrimeOrientedCarryH2Class.rootsCarryH2Class_ne_zero_of_noContinuousLift
#check Fermat.Conservation.PrimeOrientedCarryH2Class.rootsCarryH2Class_eq_zero_iff_exists_continuous_lift
#check Fermat.Conservation.PrimeOrientedCarryH2ClassAt59.orientedCarryH2Class_eq_59
#check Fermat.Conservation.PrimeOrientedCarryH2ClassAt59.rootsCarryH2Class_eq_59

#check Fermat.Conservation.PrimeConcreteTwistedLiftCupBridge.twistedCorrection
#check Fermat.Conservation.PrimeConcreteTwistedLiftCupBridge.twistedComparison_mem_kernel
#check Fermat.Conservation.PrimeConcreteTwistedLiftCupBridge.twistedComparison_eq_kernelEmbed
#check Fermat.Conservation.PrimeConcreteTwistedLiftCupBridge.section_eq_twisted_mul_kernel
#check Fermat.Conservation.PrimeConcreteTwistedLiftCupBridge.twistedCorrection_add
#check Fermat.Conservation.PrimeConcreteTwistedLiftCupBridge.continuous_twistedCorrection
#check Fermat.Conservation.PrimeConcreteTwistedLiftCupBridge.twistedCupPrimitive
#check Fermat.Conservation.PrimeConcreteTwistedLiftCupBridge.twistedCupPrimitive_equation

#check Fermat.Conservation.PrimeIntegratedTwistedKummerCup.characterValue
#check Fermat.Conservation.PrimeIntegratedTwistedKummerCup.characterValue_mul
#check Fermat.Conservation.PrimeIntegratedTwistedKummerCup.characterCochain
#check Fermat.Conservation.PrimeIntegratedTwistedKummerCup.characterCycle
#check Fermat.Conservation.PrimeIntegratedTwistedKummerCup.multiplicationPairing
#check Fermat.Conservation.PrimeIntegratedTwistedKummerCup.characterCupCycle
#check Fermat.Conservation.PrimeIntegratedTwistedKummerCup.kummerNominalCycle
#check Fermat.Conservation.PrimeIntegratedTwistedKummerCup.kummerNominalCycle_actualClass
#check Fermat.Conservation.PrimeIntegratedTwistedKummerCup.orientedKummerNominalCycle
#check Fermat.Conservation.PrimeIntegratedTwistedKummerCup.orientedKummerNominalCycle_rawClass
#check Fermat.Conservation.PrimeIntegratedTwistedKummerCup.orient_continuousClassOfUnit_representative
#check Fermat.Conservation.PrimeIntegratedTwistedKummerCup.characterCycle_orientedKummerCharacter
#check Fermat.Conservation.PrimeIntegratedTwistedKummerCup.coefficients_absoluteGalois_eq_trivialTopLine
#check Fermat.Conservation.PrimeIntegratedTwistedKummerCup.characterCycle_actualClass_eq_orientedKummer
#check Fermat.Conservation.PrimeIntegratedTwistedKummerCup.kummerCupNominalCycle
#check Fermat.Conservation.PrimeIntegratedTwistedKummerCup.kummerCupH1_representative
#check Fermat.Conservation.PrimeIntegratedTwistedKummerCup.orientNominalCycleTwo
#check Fermat.Conservation.PrimeIntegratedTwistedKummerCup.orientNominalCycleTwo_kummerCup
#check Fermat.Conservation.PrimeIntegratedTwistedKummerCup.homologyLinearEquiv_h2Projection_apply
#check Fermat.Conservation.PrimeIntegratedTwistedKummerCup.orientH2_h2Projection
#check Fermat.Conservation.PrimeIntegratedTwistedKummerCup.orientH2_kummerCupH1
#check Fermat.Conservation.PrimeIntegratedTwistedKummerCup.homogeneousPrimitiveValue
#check Fermat.Conservation.PrimeIntegratedTwistedKummerCup.homogeneousPrimitive
#check Fermat.Conservation.PrimeIntegratedTwistedKummerCup.homogeneousPrimitive_differential_apply
#check Fermat.Conservation.PrimeIntegratedTwistedKummerCup.pulledCarry_sub_characterCup_eq_boundary_of_twistedLift
#check Fermat.Conservation.PrimeIntegratedTwistedKummerCup.h2Projection_pulledCarry_eq_characterCup_of_twistedLift
#check Fermat.Conservation.PrimeIntegratedTwistedKummerCup.actualH2_pulledCarry_eq_characterCup_of_twistedLift
#check Fermat.Conservation.PrimeIntegratedTwistedKummerCup.pulledCarry_actualH2_eq_orientedKummerCup_of_twistedLift

#check Fermat.Conservation.PrimeCompatibleKummerLift.exists_rootUnit_of_baseUnit
#check Fermat.Conservation.PrimeCompatibleKummerLift.cyclotomicRootSquared
#check Fermat.Conservation.PrimeCompatibleKummerLift.cyclotomicRootSquared_pow
#check Fermat.Conservation.PrimeCompatibleKummerLift.cyclotomicRootSquared_isPrimitive
#check Fermat.Conservation.PrimeCompatibleKummerLift.kummerRootSquared
#check Fermat.Conservation.PrimeCompatibleKummerLift.kummerRootSquared_pow
#check Fermat.Conservation.PrimeCompatibleKummerLift.compatibleCocycleValueSquared
#check Fermat.Conservation.PrimeCompatibleKummerLift.compatibleCocycleValueSquared_coe
#check Fermat.Conservation.PrimeCompatibleKummerLift.continuous_compatibleCocycleValueSquared
#check Fermat.Conservation.PrimeCompatibleKummerLift.rootsEquivZPowersSquared
#check Fermat.Conservation.PrimeCompatibleKummerLift.coordinateAddEquivSquared
#check Fermat.Conservation.PrimeCompatibleKummerLift.compatibleKummerCoordinateSquaredValue
#check Fermat.Conservation.PrimeCompatibleKummerLift.compatibleKummerCoordinateSquared
#check Fermat.Conservation.PrimeCompatibleKummerLift.coordinateAddEquivSquared_symm_intCast_coe
#check Fermat.Conservation.PrimeCompatibleKummerLift.coordinateAddEquivSquared_symm_natCast_coe
#check Fermat.Conservation.PrimeCompatibleKummerLift.coordinateAddEquivPrime_symm_intCast_coe
#check Fermat.Conservation.PrimeCompatibleKummerLift.coordinateAddEquivPrime_symm_natCast_coe
#check Fermat.Conservation.PrimeCompatibleKummerLift.powPRoot
#check Fermat.Conservation.PrimeCompatibleKummerLift.powPRoot_coe
#check Fermat.Conservation.PrimeCompatibleKummerLift.coordinateAddEquiv_powPRoot
#check Fermat.Conservation.PrimeCompatibleKummerLift.powP_compatibleCocycleValueSquared_eq_continuousCocycle
#check Fermat.Conservation.PrimeCompatibleKummerLift.reduction_compatibleKummerCoordinateSquared
#check Fermat.Conservation.PrimeCompatibleKummerLift.includeRootMulHom
#check Fermat.Conservation.PrimeCompatibleKummerLift.includeRoot
#check Fermat.Conservation.PrimeCompatibleKummerLift.includeRoot_coe
#check Fermat.Conservation.PrimeCompatibleKummerLift.includeRootAddHom
#check Fermat.Conservation.PrimeCompatibleKummerLift.inclusionCoordinateHom
#check Fermat.Conservation.PrimeCompatibleKummerLift.timesPHom
#check Fermat.Conservation.PrimeCompatibleKummerLift.timesPHom_intCast
#check Fermat.Conservation.PrimeCompatibleKummerLift.coordinateAddEquivPrime_symm_one_coe
#check Fermat.Conservation.PrimeCompatibleKummerLift.coordinateAddEquivSquared_symm_p_coe
#check Fermat.Conservation.PrimeCompatibleKummerLift.coordinateGenerator_unit_eq
#check Fermat.Conservation.PrimeCompatibleKummerLift.includeRoot_coordinateGenerator_mul
#check Fermat.Conservation.PrimeCompatibleKummerLift.includeRoot_coordinateGenerator
#check Fermat.Conservation.PrimeCompatibleKummerLift.inclusionCoordinateHom_one
#check Fermat.Conservation.PrimeCompatibleKummerLift.inclusionCoordinateHom_eq_timesP
#check Fermat.Conservation.PrimeCompatibleKummerLift.inclusionCoordinateHom_apply_coordinate
#check Fermat.Conservation.PrimeCompatibleKummerLift.coordinateAddEquivSquared_includeRoot
#check Fermat.Conservation.PrimeCompatibleKummerLift.cyclotomicActionRoot
#check Fermat.Conservation.PrimeCompatibleKummerLift.cyclotomicActionRoot_coe
#check Fermat.Conservation.PrimeCompatibleKummerLift.coordinate_cyclotomicActionRoot
#check Fermat.Conservation.PrimeCompatibleKummerLift.compatibleCocycleValueSquared_mul
#check Fermat.Conservation.PrimeCompatibleKummerLift.rootSquared_eq_cyclotomicRoot_pow_coordinateVal
#check Fermat.Conservation.PrimeCompatibleKummerLift.smul_rootSquared_unit
#check Fermat.Conservation.PrimeCompatibleKummerLift.smul_rootSquared
#check Fermat.Conservation.PrimeCompatibleKummerLift.coordinateAddEquivSquared_smul
#check Fermat.Conservation.PrimeCompatibleKummerLift.coordinate_cyclotomicActionRoot_pow
#check Fermat.Conservation.PrimeCompatibleKummerLift.coordinate_cyclotomicPower_compatibleCocycle
#check Fermat.Conservation.PrimeCompatibleKummerLift.coordinate_included_cyclotomicPower
#check Fermat.Conservation.PrimeCompatibleKummerLift.coordinate_smul_compatibleCocycle
#check Fermat.Conservation.PrimeCompatibleKummerLift.compatibleKummerCoordinateSquared_twisted
#check Fermat.Conservation.PrimeCompatibleKummerLift.pulledCarry_actualH2_eq_orientedKummerCup
#check Fermat.Conservation.PrimeCompatibleKummerLiftAt59.cyclotomicRoot3481_eq_primeCyclotomicRootSquared
#check Fermat.Conservation.PrimeCompatibleKummerLiftAt59.kummerRoot3481_eq_primeKummerRootSquared
#check Fermat.Conservation.PrimeCompatibleKummerLiftAt59.compatibleCocycleValue3481_eq_primeCompatibleCocycleValueSquared
#check Fermat.Conservation.PrimeCompatibleKummerLiftAt59.compatibleKummerCoordinate3481_eq_primeCompatibleKummerCoordinateSquared
#check Fermat.Conservation.PrimeCompatibleKummerLiftAt59.pulledCarry_actualH2_eq_orientedKummerCup_via_prime

#check Fermat.Conservation.PrimeKummerNormLiftH2Criterion.PrimitiveRootIsNorm
#check Fermat.Conservation.PrimeKummerNormLiftH2Criterion.CompatibleContinuousLift
#check Fermat.Conservation.PrimeKummerNormLiftH2Criterion.kummerRootsCarryH2Class
#check Fermat.Conservation.PrimeKummerNormLiftH2Criterion.rootsKummerCupObstruction
#check Fermat.Conservation.PrimeKummerNormLiftH2Criterion.orientedKummerCupObstruction
#check Fermat.Conservation.PrimeKummerNormLiftH2Criterion.kummerCarryH2Class_eq_orientedKummerCupObstruction
#check Fermat.Conservation.PrimeKummerNormLiftH2Criterion.kummerRootsCarryH2Class_eq_rootsKummerCupObstruction
#check Fermat.Conservation.PrimeKummerNormLiftH2Criterion.orientedKummerCupObstruction_eq_zero_iff_roots
#check Fermat.Conservation.PrimeKummerNormLiftH2Criterion.primitiveRoot_isNorm_iff_exists_compatibleLift
#check Fermat.Conservation.PrimeKummerNormLiftH2Criterion.primitiveRoot_isNorm_iff_kummerCarryH2Class_eq_zero
#check Fermat.Conservation.PrimeKummerNormLiftH2Criterion.primitiveRoot_isNorm_iff_orientedKummerCupObstruction_eq_zero
#check Fermat.Conservation.PrimeKummerNormLiftH2Criterion.primitiveRoot_isNorm_iff_rootsKummerCupObstruction_eq_zero
#check Fermat.Conservation.PrimeKummerNormLiftH2Criterion.compatibleLift_iff_kummerCarryH2Class_eq_zero
#check Fermat.Conservation.PrimeKummerNormLiftH2Criterion.compatibleLift_iff_orientedKummerCupObstruction_eq_zero
#check Fermat.Conservation.PrimeKummerNormLiftH2Criterion.compatibleLift_iff_rootsKummerCupObstruction_eq_zero
#check Fermat.Conservation.PrimeKummerNormLiftH2Criterion.kummerCarryH2Class_eq_zero_iff_orientedKummerCupObstruction
#check Fermat.Conservation.PrimeKummerNormLiftH2Criterion.kummerCarryH2Class_eq_zero_iff_rootsKummerCupObstruction
#check Fermat.Conservation.PrimeKummerNormLiftH2Criterion.kummerRootsCarryH2Class_eq_zero_iff_rootsKummerCupObstruction
#check Fermat.Conservation.PrimeKummerNormLiftH2Criterion.primitiveRoot_not_norm_iff_noContinuousLift
#check Fermat.Conservation.PrimeKummerNormLiftH2Criterion.primitiveRoot_not_norm_iff_kummerCarryH2Class_ne_zero
#check Fermat.Conservation.PrimeKummerNormLiftH2Criterion.primitiveRoot_not_norm_iff_orientedKummerCupObstruction_ne_zero
#check Fermat.Conservation.PrimeKummerNormLiftH2Criterion.primitiveRoot_not_norm_iff_rootsKummerCupObstruction_ne_zero
#check Fermat.Conservation.PrimeKummerNormLiftH2Criterion.orientedKummerCupObstruction_ne_zero_iff_noContinuousLift
#check Fermat.Conservation.PrimeKummerNormLiftH2Criterion.rootsKummerCupObstruction_ne_zero_iff_noContinuousLift

#check Fermat.FiftyNine.Conservation.PrimeKummerNormLiftH2CriterionAt59.twistedLambdaKummerExtension59_eq_primeKummerExtension
#check Fermat.FiftyNine.Conservation.PrimeKummerNormLiftH2CriterionAt59.twistedLambdaKummerCharacter59_eq_primeKummerCharacter
#check Fermat.FiftyNine.Conservation.PrimeKummerNormLiftH2CriterionAt59.twistedLambdaRadicandUnit59_eq_primeRadicandUnit
#check Fermat.FiftyNine.Conservation.PrimeKummerNormLiftH2CriterionAt59.twistedLambdaNoContinuousLift59_eq_primeKummerNoContinuousLift
#check Fermat.FiftyNine.Conservation.PrimeKummerNormLiftH2CriterionAt59.twistedLambdaOrientedCarryH2Class59_eq_primeKummerCarryH2Class
#check Fermat.FiftyNine.Conservation.PrimeKummerNormLiftH2CriterionAt59.twistedLambdaRootsCarryH2Class59_eq_primeKummerRootsCarryH2Class
#check Fermat.FiftyNine.Conservation.PrimeKummerNormLiftH2CriterionAt59.twistedLambdaKummerCupH2Class59_eq_primeRootsKummerCupObstruction
#check Fermat.FiftyNine.Conservation.PrimeKummerNormLiftH2CriterionAt59.twistedLambdaOrientedKummerCup_eq_primeOrientedKummerCupObstruction
#check Fermat.FiftyNine.Conservation.PrimeKummerNormLiftH2CriterionAt59.primitiveRoot_is_norm_iff_exists_continuous_lift_via_prime
#check Fermat.FiftyNine.Conservation.PrimeKummerNormLiftH2CriterionAt59.primitiveRoot_is_norm_iff_twistedLambdaOrientedCarryH2Class59_eq_zero_via_prime
#check Fermat.FiftyNine.Conservation.PrimeKummerNormLiftH2CriterionAt59.primitiveRoot_is_norm_iff_twistedLambdaRootsCarryH2Class59_eq_zero_via_prime
#check Fermat.FiftyNine.Conservation.PrimeKummerNormLiftH2CriterionAt59.primitiveRoot_is_norm_iff_twistedLambdaKummerCupH2Class59_eq_zero_via_prime
#check Fermat.FiftyNine.Conservation.PrimeKummerNormLiftH2CriterionAt59.twistedLambdaOrientedCarry_eq_orientedKummerCup_via_prime
#check Fermat.FiftyNine.Conservation.PrimeKummerNormLiftH2CriterionAt59.twistedLambdaRootsCarryH2Class59_eq_kummerCup_via_prime
#check Fermat.FiftyNine.Conservation.PrimeKummerNormLiftH2CriterionAt59.primitiveRoot_not_norm_iff_twistedLambdaNoContinuousLift59_via_prime
#check Fermat.FiftyNine.Conservation.PrimeKummerNormLiftH2CriterionAt59.twistedLambdaKummerCupH2Class59_ne_zero_iff_noContinuousLift_via_prime
#check Fermat.FiftyNine.Conservation.PrimeKummerNormLiftH2CriterionAt59.twistedLambdaKummerCupH2Class59_ne_zero_iff_primitiveRoot_not_norm_via_prime

#check Fermat.Conservation.PrimeAlbertDescentDatum.exists_albert_descent_datum
#check Fermat.Conservation.PrimeAlbertDescentDatum.concreteKummerGenerator
#check Fermat.Conservation.PrimeAlbertDescentDatum.concreteKummer_exists_albert_descent_datum
#check Fermat.Conservation.PrimeAlbertExtension.albertPolynomial
#check Fermat.Conservation.PrimeAlbertExtension.albertOverfield
#check Fermat.Conservation.PrimeAlbertExtension.albertPolynomial_irreducible
#check Fermat.Conservation.PrimeAlbertExtension.albertLiftAlgHom
#check Fermat.Conservation.PrimeAlbertExtension.albertLiftAlgHom_root
#check Fermat.Conservation.PrimeAlbertExtension.albertLiftAlgHom_algebraMap
#check Fermat.Conservation.PrimeAlbertExtension.albertLiftAlgEquiv
#check Fermat.Conservation.PrimeAlbertExtension.albertLiftAlgEquiv_root
#check Fermat.Conservation.PrimeAlbertExtension.albertLiftAlgEquiv_algebraMap
#check Fermat.Conservation.PrimeAlbertExtension.orbitProduct
#check Fermat.Conservation.PrimeAlbertExtension.albertLiftAlgEquiv_pow_algebraMap
#check Fermat.Conservation.PrimeAlbertExtension.albertLiftAlgEquiv_pow_root
#check Fermat.Conservation.PrimeAlbertExtension.orbitProduct_eq_algebraMap_norm
#check Fermat.Conservation.PrimeAlbertExtension.mappedRootOfUnity
#check Fermat.Conservation.PrimeAlbertExtension.scalarRootAutomorphism
#check Fermat.Conservation.PrimeAlbertExtension.scalarRootAutomorphism_root
#check Fermat.Conservation.PrimeAlbertExtension.scalarRootAutomorphism_algebraMap
#check Fermat.Conservation.PrimeAlbertExtension.albertLiftAlgEquiv_pow_prime
#check Fermat.Conservation.PrimeAlbertOrder.scalarRootAutomorphism_pow_algebraMap
#check Fermat.Conservation.PrimeAlbertOrder.scalarRootAutomorphism_pow_root
#check Fermat.Conservation.PrimeAlbertOrder.scalarRootAutomorphism_pow_prime
#check Fermat.Conservation.PrimeAlbertOrder.scalarRootAutomorphism_ne_one
#check Fermat.Conservation.PrimeAlbertOrder.albertLiftAlgEquiv_pow_primeSquared
#check Fermat.Conservation.PrimeAlbertOrder.albertLiftAlgEquiv_pow_prime_ne_one
#check Fermat.Conservation.PrimeAlbertOrder.albertLiftAlgEquiv_orderOf
#check Fermat.Conservation.PrimeAlbertGalois.albertOverfield_finrank
#check Fermat.Conservation.PrimeAlbertGalois.albertLiftAlgEquiv_distinct_powers
#check Fermat.Conservation.PrimeAlbertGalois.albertOverfield_card_aut
#check Fermat.Conservation.PrimeAlbertGalois.albertOverfield_isGalois
#check Fermat.Conservation.PrimeAlbertGalois.albertLiftAlgEquiv_zpowers_eq_top
#check Fermat.Conservation.PrimeAlbertCyclicQuotient.albertClosureEmbedding
#check Fermat.Conservation.PrimeAlbertCyclicQuotient.albertClosureEmbedding_restrictDomain
#check Fermat.Conservation.PrimeAlbertCyclicQuotient.albertClosureField
#check Fermat.Conservation.PrimeAlbertCyclicQuotient.albertOverfieldEquivClosure
#check Fermat.Conservation.PrimeAlbertCyclicQuotient.albertClosureField_isGalois
#check Fermat.Conservation.PrimeAlbertCyclicQuotient.albertClosureGenerator
#check Fermat.Conservation.PrimeAlbertCyclicQuotient.albertClosureGenerator_zpowers_eq_top
#check Fermat.Conservation.PrimeAlbertCyclicQuotient.albertClosureField_card_aut
#check Fermat.Conservation.PrimeAlbertCyclicQuotient.albertClosureGalEquiv
#check Fermat.Conservation.PrimeAlbertCyclicQuotient.albertCharacter
#check Fermat.Conservation.PrimeAlbertCyclicQuotient.albertCharacter_surjective
#check Fermat.Conservation.PrimeAlbertCyclicCompatibility.albertLiftAlgEquiv_restrictNormal
#check Fermat.Conservation.PrimeAlbertCyclicCompatibility.generatorGalEquiv
#check Fermat.Conservation.PrimeAlbertCyclicCompatibility.generatorGalEquiv_apply_generator
#check Fermat.Conservation.PrimeAlbertCyclicCompatibility.reduction_ofAdd_one
#check Fermat.Conservation.PrimeAlbertCyclicCompatibility.albertClosureRestriction
#check Fermat.Conservation.PrimeAlbertCyclicCompatibility.albertClosureRestriction_generator
#check Fermat.Conservation.PrimeAlbertCyclicCompatibility.albertClosureGalEquiv_apply_generator
#check Fermat.Conservation.PrimeAlbertCyclicCompatibility.albertFiniteCyclicCompatibility
#check Fermat.Conservation.PrimeAlbertCyclicCompatibility.albertBase_le_closure
#check Fermat.Conservation.PrimeAlbertCyclicCompatibility.albertBaseInsideClosure
#check Fermat.Conservation.PrimeAlbertCyclicCompatibility.albertBaseEquivInsideClosure
#check Fermat.Conservation.PrimeAlbertCyclicCompatibility.albertOverfieldEquivClosure_commutes_base
#check Fermat.Conservation.PrimeAlbertCyclicCompatibility.albertConcreteRestriction
#check Fermat.Conservation.PrimeAlbertCyclicCompatibility.albertConcreteRestriction_generator
#check Fermat.Conservation.PrimeAlbertCyclicCompatibility.albertConcreteFiniteCyclicCompatibility
#check Fermat.Conservation.PrimeAlbertCyclicCompatibility.albertConcreteRestriction_absoluteGalois
#check Fermat.Conservation.PrimeAlbertCyclicCompatibility.generatorCharacter
#check Fermat.Conservation.PrimeAlbertCyclicCompatibility.albertCharacter_reduction_eq_generatorCharacter
#check Fermat.Conservation.PrimeAlbertCyclicCompatibility.generatorGalEquiv_eq_kummerGalEquiv
#check Fermat.Conservation.PrimeAlbertCyclicCompatibility.concreteKummer_exists_albertCharacter
#check Fermat.Conservation.PrimeAlbertCyclicConverse.reduction_ker_eq_zpowers
#check Fermat.Conservation.PrimeAlbertCyclicConverse.reduction_preimage_generator_isUnit
#check Fermat.Conservation.PrimeAlbertCyclicConverse.surjective_of_reduction_comp_surjective
#check Fermat.Conservation.PrimeAlbertCyclicConverse.continuous_surjective_of_reduction_comp_surjective
#check Fermat.Conservation.PrimeAlbertCyclicConverse.prime_pow_fixes_successive_ratio
#check Fermat.Conservation.PrimeAlbertCyclicConverse.orbitProduct_successive_ratio
#check Fermat.Conservation.PrimeAlbertCyclicConverse.cyclicSquaredKernel
#check Fermat.Conservation.PrimeAlbertCyclicConverse.cyclicSquaredKernel_isOpen
#check Fermat.Conservation.PrimeAlbertCyclicConverse.cyclicSquaredFixedField
#check Fermat.Conservation.PrimeAlbertCyclicConverse.cyclicSquaredFixedField_finiteDimensional
#check Fermat.Conservation.PrimeAlbertCyclicConverse.cyclicSquaredFixedField_isGalois
#check Fermat.Conservation.PrimeAlbertCyclicConverse.cyclicSquaredFixedFieldGalEquiv
#check Fermat.Conservation.PrimeAlbertCyclicConverse.cyclicSquaredFixedField_finrank
#check Fermat.Conservation.PrimeAlbertCyclicConverse.cyclicSquaredFixedField_fixingSubgroup
#check Fermat.Conservation.PrimeAlbertCyclicConverse.concreteKummer_le_cyclicSquaredFixedField
#check Fermat.Conservation.PrimeAlbertCyclicConverse.kummerCharacter_eq_one_of_mem_fixingSubgroup
#check Fermat.Conservation.PrimeAlbertCyclicConverse.fixedField_restriction_mem_zpowers_prime
#check Fermat.Conservation.PrimeAlbertCyclicConverse.fixedBy_prime_mem_kummerExtension
#check Fermat.Conservation.PrimeAlbertCyclicConverse.exists_cyclicSquared_generator_eigenvector
#check Fermat.Conservation.PrimeAlbertCyclicConverse.concreteKummer_exists_norm_of_albertCharacter
#check Fermat.Conservation.PrimeAlbertCyclicConverse.concreteKummer_norm_iff_exists_albertCharacter
#check Fermat.Conservation.PrimeAlbertCyclicConverseAt59.reduction59_eq_primeReduction
#check Fermat.Conservation.PrimeAlbertCyclicConverseAt59.concreteKummer_exists_norm_of_albertCharacter3481_via_prime

#check Fermat.Conservation.KummerOnePlusRootNormPrime.prod_one_add_roots
#check Fermat.Conservation.KummerOnePlusRootNormPrime.norm_one_add_kummerRoot
#check Fermat.Conservation.KummerOnePlusRootNorm59.prod_one_add_roots59
#check Fermat.Conservation.KummerOnePlusRootNorm59.norm_one_add_kummerRoot59

/-! Every element of a prime Kummer extension now has selected-root power
coordinates and an exact finite conjugate-product norm formula. -/

#check Fermat.Conservation.PrimeKummerExplicitNorm.selectedKummerRoot
#check Fermat.Conservation.PrimeKummerExplicitNorm.selectedKummerRoot_pow
#check Fermat.Conservation.PrimeKummerExplicitNorm.selectedKummerPowerBasis
#check Fermat.Conservation.PrimeKummerExplicitNorm.selectedKummerPowerBasis_gen
#check Fermat.Conservation.PrimeKummerExplicitNorm.selectedKummerPowerBasis_dim
#check Fermat.Conservation.PrimeKummerExplicitNorm.exists_bounded_aeval_eq
#check Fermat.Conservation.PrimeKummerExplicitNorm.indexedKummerAutomorphism
#check Fermat.Conservation.PrimeKummerExplicitNorm.indexedKummerAutomorphism_root
#check Fermat.Conservation.PrimeKummerExplicitNorm.algebraMap_norm_eq_prod_indexed
#check Fermat.Conservation.PrimeKummerExplicitNorm.algebraMap_norm_aeval_eq_prod
#check Fermat.Conservation.PrimeKummerExplicitNorm.exists_bounded_explicit_norm
#check Fermat.Conservation.PrimeKummerExplicitNorm.norm_one_add_smul_root_pow
#check Fermat.Conservation.PrimeKummerTrace.sum_fin_primitiveRoot_pow_eq_zero
#check Fermat.Conservation.PrimeKummerTrace.algebraMap_trace_eq_sum_indexed
#check Fermat.Conservation.PrimeKummerTrace.trace_algebraMap_eq_natCast_mul
#check Fermat.Conservation.PrimeKummerTrace.trace_selectedKummerRoot_pow_eq_zero
#check Fermat.Conservation.PrimeKummerTrace.trace_aeval_eq_natCast_mul_coeff_zero
#check Fermat.Conservation.PrimeKummerTrace.exists_bounded_aeval_trace_eq

/-! The bounded polynomial coordinates admit a finite triangular
factorization into elementary Kummer factors and one exact residual factor.
The accompanying spectral estimates control both the residual norm and its
quadratic error after the trace term. -/

#check Fermat.Conservation.PrimeTriangularUnitFactorization.triangularProduct
#check Fermat.Conservation.PrimeTriangularUnitFactorization.triangularCoefficient
#check Fermat.Conservation.PrimeTriangularUnitFactorization.triangularProduct_eq_prod
#check Fermat.Conservation.PrimeTriangularUnitFactorization.triangularProduct_coeff_eq
#check Fermat.Conservation.PrimeTriangularUnitFactorization.X_pow_dvd_sub_triangularProduct
#check Fermat.Conservation.PrimeTriangularUnitFactorization.exists_triangular_remainder
#check Fermat.Conservation.PrimeTriangularUnitFactorization.normalizeConstant
#check Fermat.Conservation.PrimeTriangularUnitFactorization.exists_scaled_triangular_remainder
#check Fermat.Conservation.PrimeTriangularUnitFactorization.exists_aeval_scaled_triangular_remainder
#check Fermat.Conservation.PrimeTriangularUnitFactorization.exists_aeval_multiplicative_remainder
#check Fermat.Conservation.PrimeTriangularNormBounds.triangularCoefficient_norm_le
#check Fermat.Conservation.PrimeTriangularNormBounds.sub_triangularProduct_supNorm_le_sq
#check Fermat.Conservation.PrimeTriangularNormBounds.exists_triangular_remainder_supNorm_le_sq
#check Fermat.Conservation.PrimeTriangularValuationDepth.triangularProduct_coefficient_depth
#check Fermat.Conservation.PrimeTriangularValuationDepth.remainder_coeff_valuation_le
#check Fermat.Conservation.PrimeTriangularValuationDepth.exists_triangular_remainder_coefficient_depth_double
#check Fermat.Conservation.NonarchimedeanProductRemainder.prod_one_add_first_order_bound
#check Fermat.Conservation.NonarchimedeanProductRemainder.polynomialSupAbsoluteValue
#check Fermat.Conservation.NonarchimedeanProductRemainder.polynomial_prod_one_add_first_order_bound
#check Fermat.Conservation.SpectralNormProductRemainder.prod_one_add_first_order_bound
#check Fermat.Conservation.SpectralNormProductRemainder.norm_one_add_sub_one_norm_le
#check Fermat.Conservation.SpectralNormProductRemainder.norm_one_add_sub_trace_norm_le_sq
#check Fermat.Conservation.PolynomialSpectralNormBound.spectralNorm_aeval_le_supNorm
#check Fermat.Conservation.PrimeTriangularSpectralContraction.exists_triangular_remainder_spectralNorm_le_sq
#check Fermat.Conservation.PrimeTriangularSpectralContraction.exists_evaluated_triangular_remainder_spectralNorm_le_sq
#check Fermat.Conservation.PrimeTriangularExplicitNorm.norm_aeval_triangularProduct
#check Fermat.Conservation.ValuationProductDominant.prod_one_add_sub_one_lt
#check Fermat.Conservation.ValuationProductDominant.prod_one_add_sub_one_le
#check Fermat.Conservation.ValuationProductDominant.valuation_prod_one_add_eq_of_unique_dominant
#check Fermat.Conservation.ValuationProductDominant.each_valuation_le_of_prod_one_add_sub_one_le
#check Fermat.Conservation.PrimeTriangularSpectralAbsorption.evaluated_triangularProduct_spectralNorm_eq_one
#check Fermat.Conservation.PrimeTriangularSpectralAbsorption.evaluated_triangularProduct_spectralNorm_eq_one_of_alpha_lt_one
#check Fermat.Conservation.PrimeTriangularSpectralAbsorption.spectralNorm_div_le_of_eq_one
#check Fermat.Conservation.PrimeTriangularSpectralAbsorption.absorb_additive_remainder_by_spectral_unit
#check Fermat.Conservation.PrimeTriangularSpectralAbsorption.exists_evaluated_triangular_absorption_spectralNorm_le_sq

/-! A unit-norm element in the twisted Kummer extension has an honest
degree-`< 59` selected-root expansion whose coefficients are integral and
whose constant coefficient is a unit.  This is the input interface for the
finite contraction loop. -/

#check Fermat.FiftyNine.Conservation.EisensteinIntegrality59.adjoin_twistedLambdaRoot59_eq_top
#check Fermat.FiftyNine.Conservation.EisensteinIntegrality59.twistedLambdaPowerBasis59_dim
#check Fermat.FiftyNine.Conservation.EisensteinIntegrality59.norm_algebraNorm_eq_spectralNorm_pow59
#check Fermat.FiftyNine.Conservation.EisensteinIntegrality59.spectralNorm_eq_one_of_algebraNorm_valuation_eq_one
#check Fermat.FiftyNine.Conservation.EisensteinIntegrality59.twistedLambdaPowerBasis59_coeff_valuation_le_one_of_norm_unit
#check Fermat.FiftyNine.Conservation.EisensteinIntegrality59.twistedLambdaPowerBasis59_coeff_zero_valuation_eq_one_of_norm_unit
#check Fermat.FiftyNine.Conservation.EisensteinIntegrality59.exists_integral_bounded_aeval_of_norm_valuation_eq_one

/-! The generic spectral contraction has now been translated back into the
actual integer lambda-depth filtration at 59. -/

#check Fermat.FiftyNine.Conservation.TriangularSpectralDepth59.depthRadius59
#check Fermat.FiftyNine.Conservation.TriangularSpectralDepth59.valuation_le_exp_neg_iff_norm_le_depthRadius59
#check Fermat.FiftyNine.Conservation.TriangularSpectralDepth59.depthRadius59_sq
#check Fermat.FiftyNine.Conservation.TriangularSpectralDepth59.coefficient_valuation_le_exp_neg_of_weighted_norm_le_depthRadius59
#check Fermat.FiftyNine.Conservation.TriangularSpectralDepth59.twistedLambdaPowerBasis59_coeff_valuation_le_exp_neg_of_spectralNorm
#check Fermat.FiftyNine.Conservation.TriangularSpectralDepth59.exists_evaluated_triangular_remainder_with_coefficient_depth

/-! The 58 elementary norm perturbations cannot hide by cancellation:
their nonzero valuations are pairwise distinct modulo 59. -/

#check Fermat.FiftyNine.Conservation.TriangularNormSeparation59.twistedMonomialValuation_ne
#check Fermat.FiftyNine.Conservation.TriangularNormSeparation59.triangularNormPerturbation59
#check Fermat.FiftyNine.Conservation.TriangularNormSeparation59.triangularCoefficient_valuation_le_one
#check Fermat.FiftyNine.Conservation.TriangularNormSeparation59.triangularNormPerturbation59_valuation_lt_one
#check Fermat.FiftyNine.Conservation.TriangularNormSeparation59.triangularNormPerturbation59_valuation_le_depth_one
#check Fermat.FiftyNine.Conservation.TriangularNormSeparation59.norm_aeval_triangularProduct_mem_U1
#check Fermat.FiftyNine.Conservation.TriangularNormSeparation59.each_triangularNormPerturbation59_valuation_le
#check Fermat.FiftyNine.Conservation.TriangularNormSeparation59.triangularNormPerturbations59_mem_U60_of_product_mem_U59
#check Fermat.FiftyNine.Conservation.TriangularNormSeparation59.triangularNormPerturbations59_mem_U60_of_norm_mem_U59
#check Fermat.FiftyNine.Conservation.TriangularNormSeparation59.norm_aeval_triangularProduct_mem_U60_of_mem_U59

/-! Residual normalization adds one depth, contraction doubles it, and the
absorbed base factor has an actual norm unit in `U_60`. -/

#check Fermat.FiftyNine.Conservation.TriangularResidualNormalization59.HasCoordinateDepth59
#check Fermat.FiftyNine.Conservation.TriangularResidualNormalization59.residualPolynomial59
#check Fermat.FiftyNine.Conservation.TriangularResidualNormalization59.normalizedResidualPolynomial59
#check Fermat.FiftyNine.Conservation.TriangularResidualNormalization59.residualElement59
#check Fermat.FiftyNine.Conservation.TriangularResidualNormalization59.normalizedResidualPolynomial59_data
#check Fermat.FiftyNine.Conservation.TriangularResidualNormalization59.residualElement59_eq_constant_mul_normalized
#check Fermat.FiftyNine.Conservation.TriangularResidualStep59.nextDepth59
#check Fermat.FiftyNine.Conservation.TriangularResidualStep59.triangularBase59
#check Fermat.FiftyNine.Conservation.TriangularResidualStep59.exists_residual_step
#check Fermat.FiftyNine.Conservation.TriangularResidualStep59.triangularNormPerturbation59_depth60
#check Fermat.FiftyNine.Conservation.TriangularResidualStep59.exists_triangularBase59_normUnit_mem_U60
#check Fermat.FiftyNine.Conservation.TriangularResidualStep59.exists_residual_step_with_normUnit
#check Fermat.FiftyNine.Conservation.TriangularTerminalResidual59.depthRadius59_add
#check Fermat.FiftyNine.Conservation.TriangularTerminalResidual59.norm_twistedLambda59_eq_depthRadius_one
#check Fermat.FiftyNine.Conservation.TriangularTerminalResidual59.spectralNorm_le_depthRadius59_of_coordinateDepth
#check Fermat.FiftyNine.Conservation.TriangularTerminalResidual59.spectralNorm_twistedLambda_mul_le_depthRadius_succ
#check Fermat.FiftyNine.Conservation.TriangularTerminalResidual59.norm_residualElement59_sub_one_valuation_le
#check Fermat.FiftyNine.Conservation.TriangularTerminalResidual59.norm_residualElement59_mem_U60_of_depth
#check Fermat.FiftyNine.Conservation.FiveStepResidual59.fiveStepBase59
#check Fermat.FiftyNine.Conservation.FiveStepResidual59.exists_fiveStep_residual_chain_with_normUnit
#check Fermat.FiftyNine.Conservation.FiveStepResidual59.exists_residualElement59_normUnit_mem_U60_of_depth_zero
#check Fermat.FiftyNine.Conservation.InitialIntegralDecomposition59.exists_initial_integral_decomposition
#check Fermat.FiftyNine.Conservation.PowerU1Reflection59.mem_U1_of_pow_fiftyNine_mem_U1
#check Fermat.FiftyNine.Conservation.NormImageBridge59.normUnit_mem_U60_of_eq_norm_of_mem_U59
#check Fermat.FiftyNine.Conservation.NormImageBridge59.twistedLambdaNormUnits59_mem_U60_of_mem_U59
#check Fermat.FiftyNine.Conservation.NormImageBridge59.normImageCriticalUnitLayer59_eq_bot
#check Fermat.FiftyNine.Conservation.NormImageBridge59.primitiveRootNormCorrection59_not_norm
#check Fermat.FiftyNine.Conservation.NormImageBridge59.lambdaLocalPrimitiveRoot59_not_norm
#check Fermat.FiftyNine.Conservation.NormImageBridge59.twistedLambdaKummerCupH2Class59_ne_zero
#check Fermat.FiftyNine.Conservation.NormImageConsequences59.twistedLambdaNoContinuousLift59
#check Fermat.FiftyNine.Conservation.NormImageConsequences59.exists_normalizedInflationReadout59
#check Fermat.FiftyNine.Conservation.NormImageConsequences59.exists_normalizedReadout_twistedLambdaEndpoint59
#check Fermat.FiftyNine.Conservation.ExactNormIntersection59.mem_twistedLambdaNormUnits59_range_of_mem_U60
#check Fermat.FiftyNine.Conservation.ExactNormIntersection59.twistedLambdaNormUnits59_range_inf_U59_eq_U60
#check Fermat.FiftyNine.Conservation.ExactNormIntersection59.mem_twistedLambdaNormUnits59_range_iff_mem_U60_of_mem_U59
#check Fermat.FiftyNine.Conservation.ExactNormIntersection59.not_mem_twistedLambdaNormUnits59_range_iff_not_mem_U60_of_mem_U59
#check Fermat.FiftyNine.Conservation.ExactNormIntersection59.mem_twistedLambdaNormUnits59_range_iff_criticalCoefficient59_eq_zero
#check Fermat.FiftyNine.Conservation.ExactNormIntersection59.not_mem_twistedLambdaNormUnits59_range_iff_criticalCoefficient59_ne_zero
#check Fermat.FiftyNine.Conservation.ExactNormIntersection59.exists_norm_eq_iff_mem_twistedLambdaNormUnits59_range
#check Fermat.FiftyNine.Conservation.ExactNormIntersection59.exists_norm_eq_iff_criticalCoefficient59_eq_zero
#check Fermat.FiftyNine.Conservation.ExactNormIntersection59.not_exists_norm_eq_iff_criticalCoefficient59_ne_zero
#check Fermat.FiftyNine.Conservation.Unit60KummerNormObstruction59.unit60KummerCupH2Class59_ne_zero
#check Fermat.FiftyNine.Conservation.Unit60KummerNormObstruction59.lambdaLocalPrimitiveRoot59_not_norm_from_twistUnit
#check Fermat.FiftyNine.Conservation.Unit60KummerNormObstruction59.twistUnitKummerCharacter59_noContinuousLift

#check Fermat.FiftyNine.Conservation.BareLambdaNorm59.canonicalLambda59_not_pow
#check Fermat.FiftyNine.Conservation.BareLambdaNorm59.bareLambdaKummerExtension59
#check Fermat.FiftyNine.Conservation.BareLambdaNorm59.bareLambdaRoot59
#check Fermat.FiftyNine.Conservation.BareLambdaNorm59.bareLambdaRoot59_pow
#check Fermat.FiftyNine.Conservation.BareLambdaNorm59.norm_one_add_bareLambdaRoot59
#check Fermat.FiftyNine.Conservation.BareLambdaNorm59.exists_bareLambda_norm_eq_primitiveRoot
#check Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59.twistedLambdaRoot59
#check Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59.twistedLambdaRoot59_pow
#check Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59.norm_one_add_twistedLambdaRoot59
#check Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59.primitiveRootNormCorrection59
#check Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59.primitiveRootNormCorrection59_eq
#check Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59.natCast59_valuation
#check Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59.primitiveRoot59_valuation
#check Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59.primitiveRootNormCorrection59_sub_one_valuation
#check Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59.primitiveRootNormCorrection59_ne_zero
#check Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59.exists_correction_norm_of_primitiveRoot_norm
#check Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59.exists_primitiveRoot_norm_of_correction_norm
#check Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59.primitiveRoot_is_norm_iff_correction_is_norm
#check Fermat.FiftyNine.Conservation.CriticalUnitQuotient59.lambdaOneUnits
#check Fermat.FiftyNine.Conservation.CriticalUnitQuotient59.mem_lambdaOneUnits
#check Fermat.FiftyNine.Conservation.CriticalUnitQuotient59.lambdaOneUnits_mono
#check Fermat.FiftyNine.Conservation.CriticalUnitQuotient59.U59
#check Fermat.FiftyNine.Conservation.CriticalUnitQuotient59.U60
#check Fermat.FiftyNine.Conservation.CriticalUnitQuotient59.U60_le_U59
#check Fermat.FiftyNine.Conservation.CriticalUnitQuotient59.correctionFieldUnit59
#check Fermat.FiftyNine.Conservation.CriticalUnitQuotient59.correctionFieldUnit59_val
#check Fermat.FiftyNine.Conservation.CriticalUnitQuotient59.correctionFieldUnit59_mem_U59
#check Fermat.FiftyNine.Conservation.CriticalUnitQuotient59.correctionFieldUnit59_not_mem_U60
#check Fermat.FiftyNine.Conservation.CriticalUnitQuotient59.U60InU59
#check Fermat.FiftyNine.Conservation.CriticalUnitQuotient59.CriticalUnitLayer59
#check Fermat.FiftyNine.Conservation.CriticalUnitQuotient59.correctionInU59
#check Fermat.FiftyNine.Conservation.CriticalUnitQuotient59.correctionClass59
#check Fermat.FiftyNine.Conservation.CriticalUnitQuotient59.correctionClass59_ne_one
#check Fermat.FiftyNine.Conservation.CriticalUnitQuotient59.twistedLambdaNormUnits59
#check Fermat.FiftyNine.Conservation.CriticalUnitQuotient59.normUnitsInU59
#check Fermat.FiftyNine.Conservation.CriticalUnitQuotient59.normImageCriticalUnitLayer59
#check Fermat.FiftyNine.Conservation.CriticalUnitQuotient59.correctionClass59_mem_normImage_of_norm
#check Fermat.FiftyNine.Conservation.CriticalUnitQuotient59.primitiveRoot_not_norm_of_correctionClass_not_mem_normImage

#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.LambdaIntegerRing59
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.LambdaResidueRing59
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.natCast59_eq_zero_in_lambdaResidue
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.exists_fin59_residue_representative
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.zmodCastHom_to_lambdaResidue_surjective
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.zmodEquivLambdaResidue59
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.lambdaResidue_pow_fiftyNine
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.ramificationQuotientIntegral59
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.ramificationQuotientIntegral59_residue_eq_neg_one
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.criticalCoefficientIntegral59
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.criticalCoefficient59
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.criticalCoefficient59_mul
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.criticalCoefficientHom59
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.criticalCoefficient59_eq_zero_iff
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.criticalCoefficientHom59_ker
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.criticalLayerReadout59
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.criticalLayerReadout59_injective
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.correctionCoefficient59
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.correctionCoefficient59_eq_neg_one
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.correctionCoefficient59_ne_zero
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.normalizedCriticalLayerReadout59
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.normalizedCriticalLayerReadout59_injective
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.normalizedCriticalLayerReadout59_correctionClass
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.criticalCoefficientHom59_surjective
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.criticalLayerReadout59_surjective
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.criticalLayerResidueEquiv59
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.criticalLayerZModEquiv59

/-! The depth-60 ambiguity in the critical norm quotient is now removed by
an actual 59th-root construction in the completed integer ring.  Consequently
the quotient membership test is equivalent to the exact field-norm problem
and, through the generic Kummer--Albert spine, to vanishing of the genuine
twisted-lambda cup. -/

#check Fermat.FiftyNine.Conservation.CriticalUnitPowerSurjectivity59.exists_pow59_eq_of_sub_one_mem_lambdaIdeal_pow_sixty
#check Fermat.FiftyNine.Conservation.CriticalUnitPowerSurjectivity59.exists_unit_pow59_eq_of_sub_one_mem_lambdaIdeal_pow_sixty
#check Fermat.FiftyNine.Conservation.CriticalUnitPowerSurjectivity59.exists_fieldUnit_pow59_eq_of_mem_U60
#check Fermat.FiftyNine.Conservation.CriticalUnitPowerSurjectivity59.exists_correction_norm_of_correctionClass59_mem_normImage
#check Fermat.FiftyNine.Conservation.CriticalUnitPowerSurjectivity59.correctionClass59_mem_normImage_iff_correction_is_norm
#check Fermat.FiftyNine.Conservation.CriticalUnitPowerSurjectivity59.primitiveRoot_is_norm_iff_correctionClass59_mem_normImage
#check Fermat.FiftyNine.Conservation.CriticalUnitPowerSurjectivity59.primitiveRoot_not_norm_iff_correctionClass59_not_mem_normImage
#check Fermat.FiftyNine.Conservation.CriticalUnitPowerSurjectivity59.correctionClass59_mem_normImage_iff_twistedLambdaKummerCup_eq_zero
#check Fermat.FiftyNine.Conservation.CriticalUnitPowerSurjectivity59.correctionClass59_not_mem_normImage_iff_twistedLambdaKummerCup_ne_zero

/-! The opposite end of the finite loop is exact as well: every first
one-unit has 59th power in `U_60`.  The critical terms cancel by the computed
Dwork residue and the remaining 57 binomial terms are individually deep. -/

#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.criticalPair59_valuation_le
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.middleBinomialTerm59_valuation_le
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.middleBinomialSum59_valuation_le
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.one_add_pow_fiftyNine_expansion
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.one_add_integral_mul_lambda_pow59_sub_one_valuation_le
#check Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.pow_fiftyNine_mem_U60_of_mem_U1

/-! The explicit norm coordinates already prove that every individual
nonconstant one-monomial factor is silent on the critical layer. -/

#check Fermat.FiftyNine.Conservation.ExplicitNormResidue59.selectedTwistedKummerRoot59_eq_twistedLambdaRoot59
#check Fermat.FiftyNine.Conservation.ExplicitNormResidue59.norm_one_add_twistedLambdaRootPow59
#check Fermat.FiftyNine.Conservation.ExplicitNormResidue59.monomialDepthGap59
#check Fermat.FiftyNine.Conservation.ExplicitNormResidue59.norm_one_add_twistedLambdaRootPow59_depthGap

#check Fermat.FiftyNine.Conservation.TwistedLambdaCupUnitReduction59.bareLambdaRadicandUnit59
#check Fermat.FiftyNine.Conservation.TwistedLambdaCupUnitReduction59.unit60RadicandUnit59
#check Fermat.FiftyNine.Conservation.TwistedLambdaCupUnitReduction59.twistedLambdaRadicandUnit59_eq_unit60_mul_bareLambda
#check Fermat.FiftyNine.Conservation.TwistedLambdaCupUnitReduction59.continuousClassOfTwistedLambda_eq_unit60_add_bareLambda
#check Fermat.FiftyNine.Conservation.TwistedLambdaCupUnitReduction59.bareLambdaKummerCupH2Class59
#check Fermat.FiftyNine.Conservation.TwistedLambdaCupUnitReduction59.unit60KummerCupH2Class59
#check Fermat.FiftyNine.Conservation.TwistedLambdaCupUnitReduction59.exists_bareLambda_compatibleKummerLift59
#check Fermat.FiftyNine.Conservation.TwistedLambdaCupUnitReduction59.bareLambdaRootsCarryH2Class59_eq_zero
#check Fermat.FiftyNine.Conservation.TwistedLambdaCupUnitReduction59.bareLambdaKummerCupH2Class59_eq_zero
#check Fermat.FiftyNine.Conservation.TwistedLambdaCupUnitReduction59.twistedLambdaKummerCupH2Class59_eq_unit60KummerCupH2Class59

#check Fermat.Conservation.CyclicCarryH2Class59.continuousCarryH2Class59_ne_zero
#check Fermat.Conservation.ContinuousCarryLiftObstruction59.boundaryLift59
#check Fermat.Conservation.ContinuousCarryLiftObstruction59.differential_liftPrimitive59
#check Fermat.Conservation.ContinuousCarryLiftObstruction59.pulledCarryCycle59_boundary_iff_exists_continuous_lift
#check Fermat.Conservation.ContinuousCarryLiftObstruction59.pulledCarryCycle59_not_boundary_iff_noContinuousLift
#check Fermat.Conservation.ContinuousCarryLiftObstruction59.pulledCarryH2Class59_ne_zero_of_noContinuousLift
#check Fermat.Conservation.ContinuousCarryH2LiftCriterion59.pulledCarryH2Class59_eq_zero_iff_exists_continuous_lift
#check Fermat.Conservation.ContinuousCarryH2LiftCriterion59.pulledCarryH2Class59_ne_zero_iff_noContinuousLift
#check Fermat.Conservation.ContinuousCyclicH2Readout59.cyclicCycleValue59
#check Fermat.Conservation.ContinuousCyclicH2Readout59.cyclicCycleSum59
#check Fermat.Conservation.ContinuousCyclicH2Readout59.cyclicCycleSum59_continuousCarryCycle59
#check Fermat.Conservation.ContinuousCyclicH2Readout59.sum_continuousBoundary_generator59
#check Fermat.Conservation.ContinuousCyclicH2Readout59.cyclicCycleSum59_eq_zero_of_h2Projection_eq_zero
#check Fermat.Conservation.ContinuousCyclicH2Readout59.ker_h2Projection_le_ker_cyclicCycleSum59
#check Fermat.Conservation.ContinuousCyclicH2Readout59.h2Projection_surjective59
#check Fermat.Conservation.ContinuousCyclicH2Readout59.continuousCyclicH2Readout59
#check Fermat.Conservation.ContinuousCyclicH2Readout59.continuousCyclicH2Readout59_h2Projection
#check Fermat.Conservation.ContinuousCyclicH2Readout59.actualContinuousCyclicH2Readout59
#check Fermat.Conservation.ContinuousCyclicH2Readout59.actualContinuousCyclicH2Readout59_continuousCarryH2Class59
#check Fermat.Conservation.ContinuousCyclicH2Readout59.actualContinuousCyclicH2Generator59
#check Fermat.Conservation.ContinuousCyclicH2Readout59.actualContinuousCyclicH2Readout59_generator59
#check Fermat.Conservation.ContinuousCyclicH2Readout59.actualContinuousCyclicH2Readout59_surjective
#check Fermat.Conservation.ContinuousCyclicH2Readout59.actualContinuousCyclicH2Generator59_injective
#check Fermat.Conservation.ContinuousCyclicH2Equiv59.discreteTwoOfContinuous59
#check Fermat.Conservation.ContinuousCyclicH2Equiv59.discreteTwoOfContinuous59_mem_cocycles₂
#check Fermat.Conservation.ContinuousCyclicH2Equiv59.discreteCocycleOfContinuous59
#check Fermat.Conservation.ContinuousCyclicH2Equiv59.continuousCycleOfDiscrete_discreteCocycleOfContinuous59
#check Fermat.Conservation.ContinuousCyclicH2Equiv59.continuousBoundary_of_mem_discreteCoboundaries59
#check Fermat.Conservation.ContinuousCyclicH2Equiv59.continuousCycleOfDiscreteLinear59
#check Fermat.Conservation.ContinuousCyclicH2Equiv59.discreteCarryH2Class59_ne_zero
#check Fermat.Conservation.ContinuousCyclicH2Equiv59.discreteCarryH2Class59_spans
#check Fermat.Conservation.ContinuousCyclicH2Equiv59.continuousCarryCycle59_spans_h2Projection
#check Fermat.Conservation.ContinuousCyclicH2Equiv59.continuousCarryH2Class59_spans
#check Fermat.Conservation.ContinuousCyclicH2Equiv59.actualContinuousCyclicH2Readout59_injective
#check Fermat.Conservation.ContinuousCyclicH2Equiv59.actualContinuousCyclicH2Readout59_bijective
#check Fermat.Conservation.ContinuousCyclicH2Equiv59.actualContinuousCyclicH2LinearEquiv59
#check Fermat.Conservation.ContinuousCyclicH2Equiv59.actualContinuousCyclicH2LinearEquiv59_apply
#check Fermat.Conservation.ContinuousCyclicH2Equiv59.actualContinuousCyclicH2LinearEquiv59_symm_apply
#check Fermat.Conservation.ContinuousH2Pullback59.pullbackCycleTwoLinear
#check Fermat.Conservation.ContinuousH2Pullback59.pullbackCycleToH2
#check Fermat.Conservation.ContinuousH2Pullback59.pullbackCycleToH2_eq_zero_of_h2Projection_eq_zero
#check Fermat.Conservation.ContinuousH2Pullback59.ker_h2Projection_le_ker_pullbackCycleToH2
#check Fermat.Conservation.ContinuousH2Pullback59.sourceH2Projection_surjective
#check Fermat.Conservation.ContinuousH2Pullback59.pullbackHomologyTwo
#check Fermat.Conservation.ContinuousH2Pullback59.pullbackHomologyTwo_h2Projection
#check Fermat.Conservation.ContinuousH2Pullback59.pullbackActualContinuousH2
#check Fermat.Conservation.ContinuousH2Pullback59.pullbackActualContinuousH2_cycle
#check Fermat.Conservation.ContinuousH2Pullback59.pullbackActualContinuousH2_continuousCarryH2Class59
#check Fermat.Conservation.ContinuousH2Pullback59.readout_pulledCarryH2Class59_eq_one_of_normalized_pullback
#check Fermat.Conservation.ContinuousH2PullbackFunctorial59.pullbackCycleTwo_id
#check Fermat.Conservation.ContinuousH2PullbackFunctorial59.pullbackCycleTwo_comp
#check Fermat.Conservation.ContinuousH2PullbackFunctorial59.exists_cycle_representation
#check Fermat.Conservation.ContinuousH2PullbackFunctorial59.pullbackActualContinuousH2_id
#check Fermat.Conservation.ContinuousH2PullbackFunctorial59.pullbackActualContinuousH2_comp
#check Fermat.Conservation.KummerCyclicQuotient59.kummerCharacter59
#check Fermat.Conservation.KummerCyclicQuotient59.kummerCharacter59_surjective
#check Fermat.Conservation.OrientedCarryH2Class59.rootsCarryH2Class59
#check Fermat.Conservation.OrientedCarryH2Class59.rootsCarryH2Class59_ne_zero_of_noContinuousLift
#check Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59.twistedLambda59_valuation
#check Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59.twistedLambdaKummerCharacter59
#check Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59.twistedLambdaKummerCharacter59_surjective
#check Fermat.FiftyNine.Conservation.TwistedLambdaCarryH2Class59.TwistedLambdaNoContinuousLift59
#check Fermat.FiftyNine.Conservation.TwistedLambdaCarryH2Class59.twistedLambdaRootsCarryH2Class59
#check Fermat.FiftyNine.Conservation.TwistedLambdaCarryH2Class59.lambdaH2CoefficientOrientationEquiv59_twistedLambdaRootsCarry
#check Fermat.FiftyNine.Conservation.TwistedLambdaCarryH2Class59.twistedLambdaRootsCarryH2Class59_ne_zero
#check Fermat.FiftyNine.Conservation.TwistedLambdaCarryH2Class59.exists_twistedLambdaNoncanonicalReadout_eq_one
#check Fermat.FiftyNine.Conservation.TwistedLambdaAlbertCriterion59.exists_twistedLambdaAlbertCharacter3481_of_norm
#check Fermat.FiftyNine.Conservation.TwistedLambdaAlbertCriterion59.exists_surjective_twistedLambdaAlbertCharacter3481_of_norm
#check Fermat.FiftyNine.Conservation.TwistedLambdaAlbertCriterion59.cyclicReduction3481To59_eq_reduction59
#check Fermat.FiftyNine.Conservation.TwistedLambdaAlbertCriterion59.primitiveRoot_not_norm_of_twistedLambdaNoContinuousLift

/-! ### Albert datum, genuine Kummer representative, and twisted carry--cup bridge

The Albert branch now constructs its Hilbert--90 datum and the automorphism
on the first overfield, including the exact 59th-iterate identity.  Separately,
the continuous Kummer character is represented by the genuine chosen-root
cocycle and is identified exactly with the splitting-field character.  An
explicit twisted `C59²` cochain then identifies the pulled carry class with
the genuine oriented Kummer cup in actual continuous `H²`.  These checks do
not claim that the unconditional `C59²` coordinate producer, local invariant,
or Hilbert-symbol comparison has already been constructed. -/

#check Fermat.Conservation.AlbertDescentDatum59.exists_albert_descent_datum59
#check Fermat.Conservation.AlbertDescentDatum59.concreteKummerGenerator59
#check Fermat.Conservation.AlbertDescentDatum59.concreteKummer_exists_albert_descent_datum59
#check Fermat.Conservation.AlbertExtension59.albertPolynomial59_irreducible
#check Fermat.Conservation.AlbertExtension59.albertLiftAlgEquiv59
#check Fermat.Conservation.AlbertExtension59.albertLiftAlgEquiv59_pow_algebraMap
#check Fermat.Conservation.AlbertExtension59.albertLiftAlgEquiv59_pow_root
#check Fermat.Conservation.AlbertExtension59.orbitProduct59_eq_algebraMap_norm
#check Fermat.Conservation.AlbertExtension59.scalarRootAutomorphism59
#check Fermat.Conservation.AlbertExtension59.albertLiftAlgEquiv59_pow_fiftyNine
#check Fermat.Conservation.AlbertOrder59.scalarRootAutomorphism59_pow_fiftyNine
#check Fermat.Conservation.AlbertOrder59.scalarRootAutomorphism59_ne_one
#check Fermat.Conservation.AlbertOrder59.albertLiftAlgEquiv59_pow_3481
#check Fermat.Conservation.AlbertOrder59.albertLiftAlgEquiv59_pow_fiftyNine_ne_one
#check Fermat.Conservation.AlbertOrder59.albertLiftAlgEquiv59_orderOf
#check Fermat.Conservation.AlbertGalois59.albertOverfield59_finrank
#check Fermat.Conservation.AlbertGalois59.albertLiftAlgEquiv59_distinct_powers
#check Fermat.Conservation.AlbertGalois59.albertOverfield59_card_aut
#check Fermat.Conservation.AlbertGalois59.albertOverfield59_isGalois
#check Fermat.Conservation.AlbertGalois59.albertLiftAlgEquiv59_zpowers_eq_top
#check Fermat.Conservation.ContinuousCyclicQuotient.absoluteGaloisRestriction
#check Fermat.Conservation.ContinuousCyclicQuotient.absoluteGaloisRestriction_surjective
#check Fermat.Conservation.ContinuousCyclicQuotient.cyclicQuotient
#check Fermat.Conservation.ContinuousCyclicQuotient.cyclicQuotient_surjective
#check Fermat.Conservation.AlbertCyclicQuotient59.albertClosureEmbedding59
#check Fermat.Conservation.AlbertCyclicQuotient59.albertClosureEmbedding59_restrictDomain
#check Fermat.Conservation.AlbertCyclicQuotient59.albertClosureField59_isGalois
#check Fermat.Conservation.AlbertCyclicQuotient59.albertClosureGenerator59_zpowers_eq_top
#check Fermat.Conservation.AlbertCyclicQuotient59.albertClosureGalEquiv3481
#check Fermat.Conservation.AlbertCyclicQuotient59.albertCharacter3481
#check Fermat.Conservation.AlbertCyclicQuotient59.albertCharacter3481_surjective
#check Fermat.Conservation.AlbertCyclicCompatibility59.cyclicReduction3481To59
#check Fermat.Conservation.AlbertCyclicCompatibility59.albertFiniteCyclicCompatibility59
#check Fermat.Conservation.AlbertCyclicCompatibility59.albertCharacter3481_reduction_eq_generatorCharacter59
#check Fermat.Conservation.AlbertCyclicCompatibility59.generatorGalEquiv59_eq_kummerGalEquiv59
#check Fermat.Conservation.AlbertCyclicCompatibility59.concreteKummer_exists_albertCharacter3481
#check Fermat.Conservation.AlbertCyclicCompatibility59.cyclicReduction3481To59_preimage_generator_isUnit
#check Fermat.Conservation.AlbertCyclicCompatibility59.surjective_of_cyclicReduction3481To59_comp_surjective
#check Fermat.Conservation.AlbertCyclicCompatibility59.continuous_surjective_of_cyclicReduction3481To59_comp_surjective
#check Fermat.Conservation.AlbertCyclicCompatibility59.concreteKummer_exists_surjective_albertCharacter3481
#check Fermat.Conservation.AlbertCyclicConverse59.cyclicReduction3481To59_ker_eq_zpowers
#check Fermat.Conservation.AlbertCyclicConverse59.fiftyNine_pow_fixes_successive_ratio
#check Fermat.Conservation.AlbertCyclicConverse59.orbitProduct_successive_ratio
#check Fermat.Conservation.AlbertCyclicConverse59.cyclic3481Kernel
#check Fermat.Conservation.AlbertCyclicConverse59.cyclic3481Kernel_isOpen
#check Fermat.Conservation.AlbertCyclicConverse59.cyclic3481FixedField
#check Fermat.Conservation.AlbertCyclicConverse59.cyclic3481FixedField_finiteDimensional
#check Fermat.Conservation.AlbertCyclicConverse59.cyclic3481FixedField_isGalois
#check Fermat.Conservation.AlbertCyclicConverse59.cyclic3481FixedFieldGalEquiv
#check Fermat.Conservation.AlbertCyclicConverse59.cyclic3481FixedField_finrank
#check Fermat.Conservation.AlbertCyclicConverse59.cyclic3481FixedField_fixingSubgroup
#check Fermat.Conservation.AlbertCyclicConverse59.concreteKummer_le_cyclic3481FixedField
#check Fermat.Conservation.AlbertCyclicConverse59.kummerCharacter59_eq_one_of_mem_fixingSubgroup
#check Fermat.Conservation.AlbertCyclicConverse59.fixedField_restriction_mem_zpowers_fiftyNine
#check Fermat.Conservation.AlbertCyclicConverse59.fixedBy_fiftyNine_mem_kummerExtension59
#check Fermat.Conservation.AlbertCyclicConverse59.exists_cyclic3481_generator_eigenvector
#check Fermat.Conservation.AlbertCyclicConverse59.concreteKummer_exists_norm_of_albertCharacter3481
#check Fermat.Conservation.AlbertCyclicConverse59.concreteKummer_norm_iff_exists_albertCharacter3481

#check Fermat.Conservation.OrientedKummerRepresentative59.orientedKummerCharacter
#check Fermat.Conservation.OrientedKummerRepresentative59.orient_continuousClassOfUnit_representative
#check Fermat.Conservation.OrientedKummerRepresentative59.characterCycle_orientedKummerCharacter
#check Fermat.Conservation.OrientedKummerRepresentative59.characterCycle_actualClass_eq_orientedKummer
#check Fermat.Conservation.OrientedKummerRepresentative59.kummerCupH1_representative
#check Fermat.Conservation.OrientedKummerRepresentative59.orientH2_kummerCupH1
#check Fermat.Conservation.KummerCharacterComparison59.cocycleValue_eq_algebraicPowerRoot59
#check Fermat.Conservation.KummerCharacterComparison59.orientedKummerValue_eq_kummerCharacter59_toAdd
#check Fermat.Conservation.KummerCharacterComparison59.kummerCharacter59_eq_orientedKummerCharacter

#check Fermat.Conservation.ConcreteTwistedLiftCupBridge59.twistedCorrection59
#check Fermat.Conservation.ConcreteTwistedLiftCupBridge59.twistedComparison_eq_kernelEmbed59
#check Fermat.Conservation.ConcreteTwistedLiftCupBridge59.twistedCorrection59_add
#check Fermat.Conservation.ConcreteTwistedLiftCupBridge59.continuous_twistedCorrection59
#check Fermat.Conservation.CompatibleKummerLift59.cyclotomicRoot3481
#check Fermat.Conservation.CompatibleKummerLift59.cyclotomicRoot3481_pow59
#check Fermat.Conservation.CompatibleKummerLift59.compatibleKummerCoordinate3481
#check Fermat.Conservation.CompatibleKummerLift59.reduction59_compatibleKummerCoordinate3481
#check Fermat.Conservation.CompatibleKummerLift59.compatibleKummerCoordinate3481_twisted
#check Fermat.Conservation.CompatibleKummerLift59.pulledCarry_actualH2_eq_orientedKummerCup
#check Fermat.Conservation.ConcreteTwistedLiftCupBridge59.twistedCupPrimitive59
#check Fermat.Conservation.ConcreteTwistedLiftCupBridge59.twistedCupPrimitive59_equation
#check Fermat.Conservation.IntegratedTwistedKummerCup59.pulledCarry_sub_characterCup_eq_boundary_of_twistedLift
#check Fermat.Conservation.IntegratedTwistedKummerCup59.h2Projection_pulledCarry_eq_characterCup_of_twistedLift
#check Fermat.Conservation.IntegratedTwistedKummerCup59.actualH2_pulledCarry_eq_characterCup_of_twistedLift
#check Fermat.Conservation.IntegratedTwistedKummerCup59.pulledCarry_actualH2_eq_orientedKummerCup_of_twistedLift
#check Fermat.FiftyNine.Conservation.TwistedLambdaKummerCupComparison59.twistedLambdaRadicandUnit59
#check Fermat.FiftyNine.Conservation.TwistedLambdaKummerCupComparison59.twistedLambdaKummerCharacter59_eq_orientedKummerCharacter
#check Fermat.FiftyNine.Conservation.TwistedLambdaKummerCupComparison59.twistedLambdaKummerCupH2Class59
#check Fermat.FiftyNine.Conservation.TwistedLambdaKummerCupComparison59.twistedLambdaOrientedCarry_eq_orientedKummerCup
#check Fermat.FiftyNine.Conservation.TwistedLambdaKummerCupComparison59.twistedLambdaRootsCarryH2Class59_eq_kummerCup
#check Fermat.FiftyNine.Conservation.TwistedLambdaKummerLiftCriterion59.twistedLambdaKummerCupH2Class59_eq_zero_iff_exists_continuous_lift
#check Fermat.FiftyNine.Conservation.TwistedLambdaKummerLiftCriterion59.twistedLambdaKummerCupH2Class59_ne_zero_iff_noContinuousLift
#check Fermat.FiftyNine.Conservation.TwistedLambdaKummerLiftCriterion59.twistedLambdaKummerCupH2Class59_eq_zero_of_primitiveRoot_norm
#check Fermat.FiftyNine.Conservation.TwistedLambdaKummerLiftCriterion59.primitiveRoot_not_norm_of_twistedLambdaKummerCupH2Class59_ne_zero
#check Fermat.FiftyNine.Conservation.TwistedLambdaKummerNormCriterion59.primitiveRoot_is_norm_iff_twistedLambdaKummerCupH2Class59_eq_zero
#check Fermat.FiftyNine.Conservation.TwistedLambdaKummerNormCriterion59.twistedLambdaKummerCupH2Class59_ne_zero_iff_primitiveRoot_not_norm
#check Fermat.FiftyNine.Conservation.TwistedLambdaKummerNormCriterion59.twistedLambdaKummerCupH2Class59_ne_zero_iff_every_norm_ne_primitiveRoot
#check Fermat.FiftyNine.Conservation.TwistedLambdaH2Inflation59.twistedLambdaH2Inflation59
#check Fermat.FiftyNine.Conservation.TwistedLambdaH2Inflation59.twistedLambdaH2Inflation59_continuousCarryH2Class59
#check Fermat.FiftyNine.Conservation.TwistedLambdaH2Inflation59.readout_twistedLambdaKummerCupH2Class59_eq_one_of_normalized_inflation

#check Fermat.Conservation.CyclicLiftNaturality59.exists_continuous_lift_iff_of_compatible_equiv
#check Fermat.Conservation.CyclicLiftNaturality59.noContinuousLift_iff_of_compatible_equiv
#check Fermat.Conservation.CyclicLiftNaturality59.exists_compatible_scalarRotation59
#check Fermat.Conservation.CyclicLiftNaturality59.noContinuousLift_iff_scalarRotation59

#check Fermat.FiftyNine.Conservation.TwistedArtinHasse59.samePrimeFiniteLog_twist59_eq
#check Fermat.FiftyNine.Conservation.TwistedArtinHasse59.normalizedFiniteLog59_mod59
#check Fermat.FiftyNine.Conservation.TwistedArtinHasse59.cyclotomicFinrank59
#check Fermat.FiftyNine.Conservation.TwistedArtinHasse59.trace_algebraMap_normalizedFiniteLog59
#check Fermat.FiftyNine.Conservation.TwistedArtinHasse59.normalizedTraceFiniteLog59_mod59_ne_zero
#check Fermat.FiftyNine.Conservation.TwistedArtinHasse59.trace_algebraMap_normalizedFiniteLog59_mod59_ne_zero
#check Fermat.FiftyNine.Conservation.LocalCyclotomicTrace59.localTensorMap59_surjective
#check Fermat.FiftyNine.Conservation.LocalCyclotomicTrace59.shiftedCyclotomic59PadicInt_isEisenstein
#check Fermat.FiftyNine.Conservation.LocalCyclotomicTrace59.shiftedCyclotomic59Q_irreducible
#check Fermat.FiftyNine.Conservation.LocalCyclotomicTrace59.minpoly_valuedCyclotomicLambda59
#check Fermat.FiftyNine.Conservation.LocalCyclotomicTrace59.localFinrank59
#check Fermat.FiftyNine.Conservation.LocalCyclotomicTrace59.localTrace59_algebraMap
#check Fermat.FiftyNine.Conservation.LocalCyclotomicTrace59.localTrace59_algebraMap_rat
#check Fermat.FiftyNine.Conservation.TwistedArtinHasseLocalTrace59.normalizedLocalTraceFiniteLog59
#check Fermat.FiftyNine.Conservation.TwistedArtinHasseLocalTrace59.normalizedLocalTraceFiniteLog59_eq
#check Fermat.FiftyNine.Conservation.TwistedArtinHasseLocalTrace59.rationalIntegerToZMod_rationalInteger59OfRIntegral
#check Fermat.FiftyNine.Conservation.TwistedArtinHasseLocalTrace59.normalizedLocalTraceFiniteLog59Integer_mod59
#check Fermat.FiftyNine.Conservation.TwistedArtinHasseLocalTrace59.normalizedLocalTraceFiniteLog59_ne_zero
#check Fermat.FiftyNine.Conservation.TwistedFiniteLogLocalTrace59.samePrimeFiniteLog_twist59_eq_scaledNormalizedFiniteLog59
#check Fermat.FiftyNine.Conservation.TwistedFiniteLogLocalTrace59.localTrace_scaledNormalizedFiniteLog59
#check Fermat.FiftyNine.Conservation.TwistedFiniteLogLocalTrace59.normalizedLocalTraceFiniteLog59_eq_inv_prime_mul_trace_scaled
#check Fermat.FiftyNine.Conservation.TwistedFiniteLogLocalTrace59.packageFiniteLogReceipt59_and_localTraceNormalization
#check Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59.principalUnit60RIntegral
#check Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59.completedLogUnit60
#check Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59.completedLogArg_unit60
#check Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59.completedLog_unit60_eval59_eq_scaledNormalizedFiniteLog59
#check Fermat.FiftyNine.Conservation.AdicCompleteValuedInteger59.instCompleteSpaceValuedIntegerRing59
#check Fermat.FiftyNine.Conservation.AdicCompleteValuedInteger59.mem_lambdaIdeal_pow_iff_valuation_le
#check Fermat.FiftyNine.Conservation.AdicCompleteValuedInteger59.norm_valuedCyclotomicLambdaInteger_lt_one
#check Fermat.FiftyNine.Conservation.AdicCompleteValuedInteger59.norm_le_norm_lambda_pow_of_mem
#check Fermat.FiftyNine.Conservation.AdicCompleteValuedInteger59.lambdaIdeal59_isAdic
#check Fermat.FiftyNine.Conservation.AdicCompleteValuedInteger59.instIsAdicCompleteLambdaIdealValuedInteger59
#check Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59.dworkCompleteToValuedInteger59
#check Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59.dworkCompleteToValuedInteger59_algebraMap
#check Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59.completedLogUnit60ValuedInteger
#check Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59.completedLogUnit60ValuedInteger_mod_lambda59
#check Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59.completedLogUnit60ValuedInteger_sub_scaled_mem
#check Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59.valuedIntegerToLambdaCompletion59
#check Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59.completedLogUnit60Lambda
#check Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59.valuedInteger_scaledNormalizedFiniteLog59_eq_algebraMap
#check Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59.completedLogUnit60Lambda_eq_scaled_add_deep_error
#check Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59.trace_completedLogUnit60Lambda_eq_scaled_add_deep_error
#check Fermat.FiftyNine.Conservation.CompletedLogTail59.completedLogUnit60ValuedInteger_sub_scaled_eq_prime_mul_lambda
#check Fermat.FiftyNine.Conservation.CompletedLogTail59.completedLogUnit60Lambda_eq_scaled_add_prime_mul_lambda_error
#check Fermat.FiftyNine.Conservation.CompletedLogTail59.trace_completedLogUnit60Lambda_eq_prime_mul_normalized_add_lambda_error
#check Fermat.FiftyNine.Conservation.LocalIntegralTrace59.dworkValuedAlgEquiv59
#check Fermat.FiftyNine.Conservation.LocalIntegralTrace59.valuedIntegerBasis59
#check Fermat.FiftyNine.Conservation.LocalIntegralTrace59.map_rationalMaximalIdeal_eq_lambdaIdeal_pow_pred
#check Fermat.FiftyNine.Conservation.LocalIntegralTrace59.integerTrace_mem_maximalIdeal_of_mem_lambda
#check Fermat.FiftyNine.Conservation.LocalIntegralTrace59.localTrace59_valuedInteger_eq_integerTrace
#check Fermat.FiftyNine.Conservation.LocalIntegralTrace59.exists_rationalInteger_eq_localTrace_valuedInteger59
#check Fermat.FiftyNine.Conservation.LocalIntegralTrace59.exists_rationalInteger_localTrace_eq_prime_mul_of_mem_lambda
#check Fermat.FiftyNine.Conservation.CompletedLogTraceNonzero59.normalizedCompletedLogTrace59
#check Fermat.FiftyNine.Conservation.CompletedLogTraceNonzero59.normalizedCompletedLogTrace59_eq_finite_add_prime_mul_integer
#check Fermat.FiftyNine.Conservation.CompletedLogTraceNonzero59.exists_integer_normalizedCompletedLogTrace59_and_residue
#check Fermat.FiftyNine.Conservation.CompletedLogTraceNonzero59.normalizedCompletedLogTrace59_ne_zero
#check Fermat.FiftyNine.Conservation.CompletedLogResidue59.normalizedCompletedLogTrace59Integer
#check Fermat.FiftyNine.Conservation.CompletedLogResidue59.normalizedCompletedLogTrace59Integer_coe
#check Fermat.FiftyNine.Conservation.CompletedLogResidue59.normalizedCompletedLogTrace59Integer_unique
#check Fermat.FiftyNine.Conservation.CompletedLogResidue59.normalizedCompletedLogTrace59Residue
#check Fermat.FiftyNine.Conservation.CompletedLogResidue59.normalizedCompletedLogTrace59Residue_eq_neg_one
#check Fermat.FiftyNine.Conservation.CompletedLogResidue59.normalizedCompletedLogTrace59Residue_ne_zero
#check Fermat.FiftyNine.Conservation.CompletedLogPowerObstruction59.completedLogValuedInteger59
#check Fermat.FiftyNine.Conservation.CompletedLogPowerObstruction59.completedLogValuedInteger59_mem_lambda
#check Fermat.FiftyNine.Conservation.CompletedLogPowerObstruction59.completedLogUnit60_not_pow_in_completedLogDomain
#check Fermat.FiftyNine.Conservation.CompletedLogLocalPowerObstruction59.lambdaIdeal59_eq_maximalIdeal
#check Fermat.FiftyNine.Conservation.CompletedLogLocalPowerObstruction59.lambdaResidueCharP59
#check Fermat.FiftyNine.Conservation.CompletedLogLocalPowerObstruction59.unit_mem_completedLogDomain_of_pow_eq_unit60
#check Fermat.FiftyNine.Conservation.CompletedLogLocalPowerObstruction59.completedLogUnit60_not_pow_in_valuedIntegerUnits
#check Fermat.FiftyNine.Conservation.CompletedLogLocalPowerObstruction59.twistUnit59_not_pow_in_localField
#check Fermat.FiftyNine.Conservation.TwistedLambdaNormalizationSign59.neg_normalizedCompletedLogTrace59Residue_eq_one
#check Fermat.FiftyNine.Conservation.TwistedLambdaNormalizationSign59.finiteCarryReadout_eq_neg_normalizedCompletedLogTrace59Residue
#check Fermat.FiftyNine.Conservation.TwistedLambdaNormalizationSign59.normalizedReadout_twistedLambdaKummerCup_eq_neg_completedLogResidue
#check Fermat.FiftyNine.Conservation.TwistedLambdaNormalizedEndpoint59.twistedLambdaKummerCupH2Class59_ne_zero_of_normalized_readout
#check Fermat.FiftyNine.Conservation.TwistedLambdaNormalizedEndpoint59.normalizedReadout_twistedLambdaEndpoint59

#check Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.twistUnit59Unit
#check Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.twistUnit59Unit_val
#check Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.twistUnitKummerClass59
#check Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.twistUnitKummerClass59_ne_zero
#check Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.twistUnitKummerPolynomial59
#check Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.twistUnitKummerPolynomial59_irreducible
#check Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.twistUnitKummerExtension59
#check Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.twistUnitKummerCharacter59
#check Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.twistUnitKummerCharacter59_surjective
#check Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.canonicalLambda59Unit
#check Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.canonicalLambda59Unit_val
#check Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.canonicalLambdaKummerClass59
#check Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.twistedLambda59Unit
#check Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.twistedLambda59Unit_val
#check Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.twistedLambdaRadicandKummerClass59
#check Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.twistedLambdaRadicandKummerClass59_eq_add
#check Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.twistedLambdaRadicandKummerClass59_ne_canonicalLambdaKummerClass59
#check Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.exists_normalizedInflationReadout_of_twistedLambdaKummerCup_ne_zero
#check Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.exists_normalizedInflationReadout_iff_twistedLambdaKummerCup_ne_zero
#check Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.exists_normalizedInflationReadout_iff_primitiveRoot_not_norm
#check Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.exists_normalizedInflationReadout_iff_noContinuousLift

#guard_depends_on
  Fermat.Conservation.PrimeCyclicH2.finiteCyclicH2Class_ne_zero,
  Fermat.Conservation.PrimeCyclicH2.coefficients_norm_eq_zero
#guard_depends_on
  Fermat.Conservation.PrimeCyclicH2.finiteCyclicH2Class_spans,
  Fermat.Conservation.PrimeCyclicH2.generator_generates
#guard_depends_on
  Fermat.Conservation.PrimeCyclicH2.finiteCyclicH2GeneratorMap_bijective,
  Fermat.Conservation.PrimeCyclicH2.finiteCyclicH2Class_spans
#guard_depends_on
  Fermat.Conservation.PrimeCyclicH2.finiteCyclicH2ReadoutEquiv_class,
  Fermat.Conservation.PrimeCyclicH2.finiteCyclicH2LinearEquiv
#guard_depends_on
  Fermat.Conservation.PrimeCyclicH2.sum_carryCocycle_generator,
  Fermat.Conservation.PrimeCyclicH2.carry_generator_apply
#guard_depends_on
  Fermat.Conservation.PrimeCyclicH2.carryCocycle_not_mem_coboundaries₂,
  Fermat.Conservation.PrimeCyclicH2.sum_carryCocycle_generator
#guard_depends_on
  Fermat.Conservation.PrimeCyclicH2.continuousCarryCycle_not_boundary,
  Fermat.Conservation.PrimeCyclicH2.carryCocycle_not_mem_coboundaries₂
#guard_depends_on
  Fermat.Conservation.PrimeCyclicH2.continuousCarryH2Class_ne_zero,
  Fermat.Conservation.PrimeCyclicH2.continuousCarryCycle_not_boundary
#guard_depends_on
  Fermat.Conservation.PrimeCyclicH2.cyclicCycleSum_continuousCarryCycle,
  Fermat.Conservation.PrimeCyclicH2.sum_carryCocycle_generator
#guard_depends_on
  Fermat.Conservation.PrimeCyclicH2.cyclicCycleSum_eq_zero_of_h2Projection_eq_zero,
  Fermat.Conservation.PrimeCyclicH2.sum_continuousBoundary_generator
#guard_depends_on
  Fermat.Conservation.PrimeCyclicH2.continuousCyclicH2Readout_h2Projection,
  Fermat.Conservation.PrimeCyclicH2.ker_h2Projection_le_ker_cyclicCycleSum
#guard_depends_on
  Fermat.Conservation.PrimeCyclicH2.actualContinuousCyclicH2Readout_continuousCarryH2Class,
  Fermat.Conservation.PrimeCyclicH2.cyclicCycleSum_continuousCarryCycle
#guard_depends_on
  Fermat.Conservation.PrimeCyclicH2.discreteCarryH2Class_spans,
  Fermat.Conservation.PrimeCyclicH2.finiteCyclicH2Class_spans
#guard_depends_on
  Fermat.Conservation.PrimeCyclicH2.continuousCarryCycle_spans_h2Projection,
  Fermat.Conservation.PrimeCyclicH2.discreteCarryH2Class_spans
#guard_depends_on
  Fermat.Conservation.PrimeCyclicH2.continuousCarryH2Class_spans,
  Fermat.Conservation.PrimeCyclicH2.continuousCarryCycle_spans_h2Projection
#guard_depends_on
  Fermat.Conservation.PrimeCyclicH2.actualContinuousCyclicH2Readout_injective,
  Fermat.Conservation.PrimeCyclicH2.continuousCarryH2Class_spans
#guard_depends_on
  Fermat.Conservation.PrimeCyclicH2.actualContinuousCyclicH2Readout_bijective,
  Fermat.Conservation.PrimeCyclicH2.actualContinuousCyclicH2Readout_injective
#guard_depends_on
  Fermat.Conservation.PrimeCyclicH2.actualContinuousCyclicH2LinearEquiv,
  Fermat.Conservation.PrimeCyclicH2.actualContinuousCyclicH2Readout_bijective
#guard_depends_on
  Fermat.Conservation.PrimeCyclicH2.actualContinuousCyclicH2LinearEquiv_symm_apply,
  Fermat.Conservation.PrimeCyclicH2.actualContinuousCyclicH2Readout_injective

#guard_depends_on
  Fermat.Conservation.PrimeCyclicExtension.reduction_standardSection,
  Fermat.Conservation.PrimeCyclicExtension.p_dvd_p_sq
#guard_depends_on
  Fermat.Conservation.PrimeCyclicExtension.kernelEmbed,
  Fermat.Conservation.PrimeCyclicExtension.cast_p_mul_val_add
#guard_depends_on
  Fermat.Conservation.PrimeCyclicExtension.standardSection_mul,
  Fermat.Conservation.PrimeCyclicH2.carry
#guard_depends_on
  Fermat.Conservation.PrimeCyclicExtension.kernelEmbed_injective,
  Fermat.Conservation.PrimeCyclicExtension.kernelCoordinate_kernelEmbed
#guard_depends_on
  Fermat.Conservation.PrimeCyclicExtension.reduction_surjective,
  Fermat.Conservation.PrimeCyclicExtension.reduction_standardSection
#guard_depends_on
  Fermat.Conservation.PrimeCyclicExtension.reduction_eq_one_iff_exists_kernelEmbed,
  Fermat.Conservation.PrimeCyclicExtension.kernelEmbed_kernelCoordinate
#guard_depends_on
  Fermat.Conservation.PrimeCyclicExtension.reduction_eq_one_iff_exists_kernelEmbed,
  Fermat.Conservation.PrimeCyclicExtension.reduction_kernelEmbedValue
#guard_depends_on
  Fermat.Conservation.PrimeCyclicExtension.kernelEmbed_range_eq_reduction_ker,
  Fermat.Conservation.PrimeCyclicExtension.reduction_eq_one_iff_exists_kernelEmbed

#guard_depends_on
  Fermat.FiftyNine.Conservation.CompletedLogLocalPowerObstruction59.lambdaResidueCharP59,
  Fermat.FiftyNine.Conservation.CompletedLogLocalPowerObstruction59.lambdaIdeal59_eq_maximalIdeal
#guard_depends_on
  Fermat.FiftyNine.Conservation.CompletedLogLocalPowerObstruction59.unit_mem_completedLogDomain_of_pow_eq_unit60,
  Fermat.FiftyNine.Conservation.CompletedLogLocalPowerObstruction59.lambdaResidueCharP59
#guard_depends_on
  Fermat.FiftyNine.Conservation.CompletedLogLocalPowerObstruction59.completedLogUnit60_not_pow_in_valuedIntegerUnits,
  Fermat.FiftyNine.Conservation.CompletedLogLocalPowerObstruction59.unit_mem_completedLogDomain_of_pow_eq_unit60
#guard_depends_on
  Fermat.FiftyNine.Conservation.CompletedLogLocalPowerObstruction59.completedLogUnit60_not_pow_in_valuedIntegerUnits,
  Fermat.FiftyNine.Conservation.CompletedLogPowerObstruction59.completedLogUnit60_not_pow_in_completedLogDomain
#guard_depends_on
  Fermat.FiftyNine.Conservation.CompletedLogLocalPowerObstruction59.twistUnit59_not_pow_in_localField,
  Fermat.FiftyNine.Conservation.CompletedLogLocalPowerObstruction59.completedLogUnit60_not_pow_in_valuedIntegerUnits
#guard_depends_on
  Fermat.FiftyNine.Conservation.CompletedLogLocalPowerObstruction59.twistUnit59_not_pow_in_localField,
  Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59.twistUnit59_valuation

#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.twistUnitKummerClass59_ne_zero,
  Fermat.FiftyNine.Conservation.CompletedLogLocalPowerObstruction59.twistUnit59_not_pow_in_localField
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.twistUnitKummerPolynomial59_irreducible,
  Fermat.Conservation.KummerCyclicQuotient59.kummerPolynomial59_irreducible
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.twistUnitKummerCharacter59_surjective,
  Fermat.Conservation.KummerCyclicQuotient59.kummerCharacter59_surjective
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.twistedLambdaRadicandKummerClass59_ne_canonicalLambdaKummerClass59,
  Fermat.FiftyNine.Conservation.CompletedLogLocalPowerObstruction59.twistUnit59_not_pow_in_localField
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.exists_normalizedInflationReadout_of_twistedLambdaKummerCup_ne_zero,
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.exists_conditionalNoncanonicalLambdaH2Readout_eq_one
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.exists_normalizedInflationReadout_of_twistedLambdaKummerCup_ne_zero,
  Fermat.Conservation.ContinuousCyclicH2Equiv59.continuousCarryH2Class59_spans
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.exists_normalizedInflationReadout_iff_twistedLambdaKummerCup_ne_zero,
  Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.exists_normalizedInflationReadout_of_twistedLambdaKummerCup_ne_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.exists_normalizedInflationReadout_iff_twistedLambdaKummerCup_ne_zero,
  Fermat.FiftyNine.Conservation.TwistedLambdaNormalizedEndpoint59.twistedLambdaKummerCupH2Class59_ne_zero_of_normalized_readout
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.exists_normalizedInflationReadout_iff_primitiveRoot_not_norm,
  Fermat.FiftyNine.Conservation.TwistedLambdaKummerNormCriterion59.twistedLambdaKummerCupH2Class59_ne_zero_iff_primitiveRoot_not_norm
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.exists_normalizedInflationReadout_iff_noContinuousLift,
  Fermat.FiftyNine.Conservation.TwistedLambdaKummerLiftCriterion59.twistedLambdaKummerCupH2Class59_ne_zero_iff_noContinuousLift

#guard_depends_on
  Fermat.Conservation.AlbertDescentDatum59.concreteKummer_exists_albert_descent_datum59,
  Fermat.Conservation.AlbertDescentDatum59.exists_albert_descent_datum59
#guard_depends_on
  Fermat.Conservation.AlbertExtension59.albertLiftAlgEquiv59_pow_fiftyNine,
  Fermat.Conservation.AlbertExtension59.orbitProduct59_eq_algebraMap_norm
#guard_depends_on
  Fermat.Conservation.AlbertOrder59.albertLiftAlgEquiv59_orderOf,
  Fermat.Conservation.AlbertExtension59.albertLiftAlgEquiv59_pow_fiftyNine
#guard_depends_on
  Fermat.Conservation.AlbertOrder59.albertLiftAlgEquiv59_orderOf,
  Fermat.Conservation.AlbertOrder59.albertLiftAlgEquiv59_pow_3481
#guard_depends_on
  Fermat.Conservation.AlbertGalois59.albertOverfield59_isGalois,
  Fermat.Conservation.AlbertGalois59.albertOverfield59_card_aut
#guard_depends_on
  Fermat.Conservation.AlbertGalois59.albertLiftAlgEquiv59_zpowers_eq_top,
  Fermat.Conservation.AlbertOrder59.albertLiftAlgEquiv59_orderOf
#guard_depends_on
  Fermat.Conservation.AlbertCyclicQuotient59.albertClosureField59_isGalois,
  Fermat.Conservation.AlbertGalois59.albertOverfield59_isGalois
#guard_depends_on
  Fermat.Conservation.AlbertCyclicQuotient59.albertCharacter3481_surjective,
  Fermat.Conservation.ContinuousCyclicQuotient.cyclicQuotient_surjective
#guard_depends_on
  Fermat.Conservation.AlbertCyclicCompatibility59.albertCharacter3481_reduction_eq_generatorCharacter59,
  Fermat.Conservation.AlbertCyclicCompatibility59.albertConcreteFiniteCyclicCompatibility59
#guard_depends_on
  Fermat.Conservation.AlbertCyclicCompatibility59.concreteKummer_exists_albertCharacter3481,
  Fermat.Conservation.AlbertCyclicCompatibility59.albertCharacter3481_reduction_eq_generatorCharacter59
#guard_depends_on
  Fermat.Conservation.AlbertCyclicCompatibility59.concreteKummer_exists_albertCharacter3481,
  Fermat.Conservation.AlbertDescentDatum59.concreteKummer_exists_albert_descent_datum59
#guard_depends_on
  Fermat.Conservation.AlbertCyclicCompatibility59.surjective_of_cyclicReduction3481To59_comp_surjective,
  Fermat.Conservation.AlbertCyclicCompatibility59.cyclicReduction3481To59_preimage_generator_isUnit
#guard_depends_on
  Fermat.Conservation.AlbertCyclicCompatibility59.concreteKummer_exists_surjective_albertCharacter3481,
  Fermat.Conservation.AlbertCyclicCompatibility59.concreteKummer_exists_albertCharacter3481
#guard_depends_on
  Fermat.Conservation.AlbertCyclicConverse59.concreteKummer_exists_norm_of_albertCharacter3481,
  Fermat.Conservation.AlbertCyclicConverse59.exists_cyclic3481_generator_eigenvector
#guard_depends_on
  Fermat.Conservation.AlbertCyclicConverse59.concreteKummer_exists_norm_of_albertCharacter3481,
  Fermat.Conservation.AlbertCyclicConverse59.fixedBy_fiftyNine_mem_kummerExtension59
#guard_depends_on
  Fermat.Conservation.AlbertCyclicConverse59.concreteKummer_exists_norm_of_albertCharacter3481,
  Fermat.Conservation.AlbertCyclicConverse59.orbitProduct_successive_ratio
#guard_depends_on
  Fermat.Conservation.AlbertCyclicConverse59.concreteKummer_norm_iff_exists_albertCharacter3481,
  Fermat.Conservation.AlbertCyclicConverse59.concreteKummer_exists_norm_of_albertCharacter3481
#guard_depends_on
  Fermat.Conservation.AlbertCyclicConverse59.concreteKummer_norm_iff_exists_albertCharacter3481,
  Fermat.Conservation.AlbertCyclicCompatibility59.concreteKummer_exists_albertCharacter3481
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistedLambdaAlbertCriterion59.exists_twistedLambdaAlbertCharacter3481_of_norm,
  Fermat.Conservation.AlbertCyclicCompatibility59.concreteKummer_exists_albertCharacter3481
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistedLambdaAlbertCriterion59.exists_surjective_twistedLambdaAlbertCharacter3481_of_norm,
  Fermat.Conservation.AlbertCyclicCompatibility59.concreteKummer_exists_surjective_albertCharacter3481
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistedLambdaAlbertCriterion59.primitiveRoot_not_norm_of_twistedLambdaNoContinuousLift,
  Fermat.FiftyNine.Conservation.TwistedLambdaAlbertCriterion59.exists_twistedLambdaAlbertCharacter3481_of_norm
#guard_depends_on
  Fermat.Conservation.KummerCharacterComparison59.kummerCharacter59_eq_orientedKummerCharacter,
  Fermat.Conservation.KummerCharacterComparison59.cocycleValue_eq_algebraicPowerRoot59
#guard_depends_on
  Fermat.Conservation.CompatibleKummerLift59.compatibleKummerCoordinate3481_twisted,
  Fermat.Conservation.CompatibleKummerLift59.reduction59_compatibleKummerCoordinate3481
#guard_depends_on
  Fermat.Conservation.CompatibleKummerLift59.pulledCarry_actualH2_eq_orientedKummerCup,
  Fermat.Conservation.IntegratedTwistedKummerCup59.pulledCarry_actualH2_eq_orientedKummerCup_of_twistedLift
#guard_depends_on
  Fermat.Conservation.IntegratedTwistedKummerCup59.pulledCarry_actualH2_eq_orientedKummerCup_of_twistedLift,
  Fermat.Conservation.IntegratedTwistedKummerCup59.actualH2_pulledCarry_eq_characterCup_of_twistedLift
#guard_depends_on
  Fermat.Conservation.IntegratedTwistedKummerCup59.pulledCarry_actualH2_eq_orientedKummerCup_of_twistedLift,
  Fermat.Conservation.OrientedKummerRepresentative59.orientH2_kummerCupH1
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistedLambdaKummerCupComparison59.twistedLambdaOrientedCarry_eq_orientedKummerCup,
  Fermat.Conservation.CompatibleKummerLift59.pulledCarry_actualH2_eq_orientedKummerCup
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistedLambdaKummerCupComparison59.twistedLambdaRootsCarryH2Class59_eq_kummerCup,
  Fermat.FiftyNine.Conservation.TwistedLambdaKummerCupComparison59.twistedLambdaOrientedCarry_eq_orientedKummerCup
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistedLambdaKummerCupComparison59.twistedLambdaRootsCarryH2Class59_eq_kummerCup,
  Fermat.Conservation.CompatibleKummerLift59.pulledCarry_actualH2_eq_orientedKummerCup
#guard_depends_on
  Fermat.Conservation.ContinuousCarryH2LiftCriterion59.pulledCarryH2Class59_eq_zero_iff_exists_continuous_lift,
  Fermat.Conservation.ContinuousCarryLiftObstruction59.pulledCarryCycle59_boundary_iff_exists_continuous_lift
#guard_depends_on
  Fermat.Conservation.ContinuousCarryH2LiftCriterion59.pulledCarryH2Class59_ne_zero_iff_noContinuousLift,
  Fermat.Conservation.ContinuousCarryH2LiftCriterion59.pulledCarryH2Class59_eq_zero_iff_exists_continuous_lift
#guard_depends_on
  Fermat.Conservation.ContinuousCyclicH2Readout59.cyclicCycleSum59_continuousCarryCycle59,
  Fermat.Conservation.CyclicCarryH2Class59.sum_carryCocycle59_generator59
#guard_depends_on
  Fermat.Conservation.ContinuousCyclicH2Readout59.cyclicCycleSum59_eq_zero_of_h2Projection_eq_zero,
  Fermat.Conservation.ContinuousCyclicH2Readout59.sum_continuousBoundary_generator59
#guard_depends_on
  Fermat.Conservation.ContinuousCyclicH2Readout59.continuousCyclicH2Readout59_h2Projection,
  Fermat.Conservation.ContinuousCyclicH2Readout59.ker_h2Projection_le_ker_cyclicCycleSum59
#guard_depends_on
  Fermat.Conservation.ContinuousCyclicH2Readout59.actualContinuousCyclicH2Readout59_continuousCarryH2Class59,
  Fermat.Conservation.ContinuousCyclicH2Readout59.cyclicCycleSum59_continuousCarryCycle59
#guard_depends_on
  Fermat.Conservation.ContinuousCyclicH2Readout59.actualContinuousCyclicH2Readout59_generator59,
  Fermat.Conservation.ContinuousCyclicH2Readout59.actualContinuousCyclicH2Readout59_continuousCarryH2Class59
#guard_depends_on
  Fermat.Conservation.ContinuousCyclicH2Readout59.actualContinuousCyclicH2Readout59_surjective,
  Fermat.Conservation.ContinuousCyclicH2Readout59.actualContinuousCyclicH2Readout59_generator59
#guard_depends_on
  Fermat.Conservation.ContinuousCyclicH2Readout59.actualContinuousCyclicH2Generator59_injective,
  Fermat.Conservation.ContinuousCyclicH2Readout59.actualContinuousCyclicH2Readout59_generator59
#guard_depends_on
  Fermat.Conservation.ContinuousCyclicH2Equiv59.continuousBoundary_of_mem_discreteCoboundaries59,
  Fermat.Conservation.DiscreteToContinuousH2.continuousCycleOfDiscrete
#guard_depends_on
  Fermat.Conservation.ContinuousCyclicH2Equiv59.discreteCarryH2Class59_spans,
  Fermat.Conservation.FiniteCyclicH2Generator59.finiteCyclicH2Class59_spans
#guard_depends_on
  Fermat.Conservation.ContinuousCyclicH2Equiv59.continuousCarryCycle59_spans_h2Projection,
  Fermat.Conservation.ContinuousCyclicH2Equiv59.continuousBoundary_of_mem_discreteCoboundaries59
#guard_depends_on
  Fermat.Conservation.ContinuousCyclicH2Equiv59.continuousCarryH2Class59_spans,
  Fermat.Conservation.ContinuousCyclicH2Equiv59.continuousCarryCycle59_spans_h2Projection
#guard_depends_on
  Fermat.Conservation.ContinuousCyclicH2Equiv59.actualContinuousCyclicH2Readout59_injective,
  Fermat.Conservation.ContinuousCyclicH2Equiv59.continuousCarryH2Class59_spans
#guard_depends_on
  Fermat.Conservation.ContinuousCyclicH2Equiv59.actualContinuousCyclicH2LinearEquiv59_symm_apply,
  Fermat.Conservation.ContinuousCyclicH2Equiv59.actualContinuousCyclicH2Readout59_injective
#guard_depends_on
  Fermat.Conservation.ContinuousH2Pullback59.pullbackCycleToH2_eq_zero_of_h2Projection_eq_zero,
  Fermat.Conservation.ContinuousHomogeneousPullback59.pullbackCycleTwo_of_boundary
#guard_depends_on
  Fermat.Conservation.ContinuousH2Pullback59.pullbackHomologyTwo_h2Projection,
  Fermat.Conservation.ContinuousH2Pullback59.ker_h2Projection_le_ker_pullbackCycleToH2
#guard_depends_on
  Fermat.Conservation.ContinuousH2Pullback59.pullbackActualContinuousH2_continuousCarryH2Class59,
  Fermat.Conservation.ContinuousH2Pullback59.pullbackActualContinuousH2_cycle
#guard_depends_on
  Fermat.Conservation.ContinuousH2Pullback59.readout_pulledCarryH2Class59_eq_one_of_normalized_pullback,
  Fermat.Conservation.ContinuousH2Pullback59.pullbackActualContinuousH2_continuousCarryH2Class59
#guard_depends_on
  Fermat.Conservation.ContinuousH2Pullback59.readout_pulledCarryH2Class59_eq_one_of_normalized_pullback,
  Fermat.Conservation.ContinuousCyclicH2Readout59.actualContinuousCyclicH2Readout59_continuousCarryH2Class59
#guard_depends_on
  Fermat.Conservation.ContinuousH2PullbackFunctorial59.pullbackActualContinuousH2_id,
  Fermat.Conservation.ContinuousH2PullbackFunctorial59.exists_cycle_representation
#guard_depends_on
  Fermat.Conservation.ContinuousH2PullbackFunctorial59.pullbackActualContinuousH2_id,
  Fermat.Conservation.ContinuousH2PullbackFunctorial59.pullbackCycleTwo_id
#guard_depends_on
  Fermat.Conservation.ContinuousH2PullbackFunctorial59.pullbackActualContinuousH2_comp,
  Fermat.Conservation.ContinuousH2PullbackFunctorial59.pullbackCycleTwo_comp
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistedLambdaKummerLiftCriterion59.twistedLambdaKummerCupH2Class59_eq_zero_iff_exists_continuous_lift,
  Fermat.FiftyNine.Conservation.TwistedLambdaKummerCupComparison59.twistedLambdaRootsCarryH2Class59_eq_kummerCup
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistedLambdaKummerLiftCriterion59.twistedLambdaKummerCupH2Class59_eq_zero_iff_exists_continuous_lift,
  Fermat.Conservation.ContinuousCarryH2LiftCriterion59.pulledCarryH2Class59_eq_zero_iff_exists_continuous_lift
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistedLambdaKummerLiftCriterion59.twistedLambdaKummerCupH2Class59_eq_zero_of_primitiveRoot_norm,
  Fermat.FiftyNine.Conservation.TwistedLambdaAlbertCriterion59.exists_twistedLambdaAlbertCharacter3481_of_norm
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistedLambdaKummerLiftCriterion59.primitiveRoot_not_norm_of_twistedLambdaKummerCupH2Class59_ne_zero,
  Fermat.FiftyNine.Conservation.TwistedLambdaKummerLiftCriterion59.twistedLambdaKummerCupH2Class59_eq_zero_of_primitiveRoot_norm
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistedLambdaKummerNormCriterion59.primitiveRoot_is_norm_iff_twistedLambdaKummerCupH2Class59_eq_zero,
  Fermat.Conservation.AlbertCyclicConverse59.concreteKummer_exists_norm_of_albertCharacter3481
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistedLambdaKummerNormCriterion59.primitiveRoot_is_norm_iff_twistedLambdaKummerCupH2Class59_eq_zero,
  Fermat.FiftyNine.Conservation.TwistedLambdaKummerLiftCriterion59.twistedLambdaKummerCupH2Class59_eq_zero_iff_exists_continuous_lift
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistedLambdaKummerNormCriterion59.twistedLambdaKummerCupH2Class59_ne_zero_iff_primitiveRoot_not_norm,
  Fermat.FiftyNine.Conservation.TwistedLambdaKummerNormCriterion59.primitiveRoot_is_norm_iff_twistedLambdaKummerCupH2Class59_eq_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistedLambdaH2Inflation59.twistedLambdaH2Inflation59_continuousCarryH2Class59,
  Fermat.Conservation.ContinuousH2Pullback59.pullbackActualContinuousH2_continuousCarryH2Class59
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistedLambdaH2Inflation59.twistedLambdaH2Inflation59_continuousCarryH2Class59,
  Fermat.FiftyNine.Conservation.TwistedLambdaKummerCupComparison59.twistedLambdaRootsCarryH2Class59_eq_kummerCup
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistedLambdaH2Inflation59.readout_twistedLambdaKummerCupH2Class59_eq_one_of_normalized_inflation,
  Fermat.FiftyNine.Conservation.TwistedLambdaH2Inflation59.twistedLambdaH2Inflation59_continuousCarryH2Class59
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistedLambdaH2Inflation59.readout_twistedLambdaKummerCupH2Class59_eq_one_of_normalized_inflation,
  Fermat.Conservation.ContinuousCyclicH2Readout59.actualContinuousCyclicH2Readout59_continuousCarryH2Class59
#guard_depends_on
  Fermat.Conservation.CyclicLiftNaturality59.noContinuousLift_iff_scalarRotation59,
  Fermat.Conservation.CyclicLiftNaturality59.exists_compatible_scalarRotation59
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistedArtinHasse59.normalizedTraceFiniteLog59_mod59_ne_zero,
  Fermat.FiftyNine.Conservation.TwistedArtinHasse59.normalizedTraceFiniteLog59_mod59
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistedArtinHasse59.trace_algebraMap_normalizedFiniteLog59_mod59_ne_zero,
  Fermat.FiftyNine.Conservation.TwistedArtinHasse59.trace_algebraMap_normalizedFiniteLog59_mod59
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalCyclotomicTrace59.localFinrank59,
  Fermat.FiftyNine.Conservation.LocalCyclotomicTrace59.shiftedCyclotomic59Q_irreducible
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalCyclotomicTrace59.localFinrank59,
  Fermat.FiftyNine.Conservation.LocalCyclotomicTrace59.localTensorMap59_surjective
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalCyclotomicTrace59.localTrace59_algebraMap,
  Fermat.FiftyNine.Conservation.LocalCyclotomicTrace59.localFinrank59
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistedArtinHasseLocalTrace59.normalizedLocalTraceFiniteLog59Integer_mod59,
  Fermat.FiftyNine.Conservation.TwistedArtinHasse59.normalizedTraceFiniteLog59_mod59
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistedArtinHasseLocalTrace59.normalizedLocalTraceFiniteLog59_ne_zero,
  Fermat.FiftyNine.Conservation.TwistedArtinHasseLocalTrace59.normalizedLocalTraceFiniteLog59Integer_mod59_ne_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistedFiniteLogLocalTrace59.samePrimeFiniteLog_twist59_eq_scaledNormalizedFiniteLog59,
  Fermat.FiftyNine.Conservation.TwistedArtinHasse59.samePrimeFiniteLog_twist59_eq
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistedFiniteLogLocalTrace59.packageFiniteLogReceipt59_and_localTraceNormalization,
  Fermat.FiftyNine.Conservation.TwistedArtinHasseLocalTrace59.normalizedLocalTraceFiniteLog59_eq
#guard_depends_on
  Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59.completedLogArg_unit60,
  Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59.completedLogUnit60
#guard_depends_on
  Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59.completedLog_unit60_eval59_eq_scaledNormalizedFiniteLog59,
  Fermat.FiftyNine.Conservation.TwistedFiniteLogLocalTrace59.samePrimeFiniteLog_twist59_eq_scaledNormalizedFiniteLog59
#guard_depends_on
  Fermat.FiftyNine.Conservation.AdicCompleteValuedInteger59.instIsAdicCompleteLambdaIdealValuedInteger59,
  Fermat.FiftyNine.Conservation.AdicCompleteValuedInteger59.lambdaIdeal59_isAdic
#guard_depends_on
  Fermat.FiftyNine.Conservation.AdicCompleteValuedInteger59.instIsAdicCompleteLambdaIdealValuedInteger59,
  Fermat.FiftyNine.Conservation.AdicCompleteValuedInteger59.instCompleteSpaceValuedIntegerRing59
#guard_depends_on
  Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59.dworkCompleteToValuedInteger59,
  Fermat.FiftyNine.Conservation.AdicCompleteValuedInteger59.instIsAdicCompleteLambdaIdealValuedInteger59
#guard_depends_on
  Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59.completedLogUnit60Lambda_eq_scaled_add_deep_error,
  Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59.completedLog_unit60_eval59_eq_scaledNormalizedFiniteLog59
#guard_depends_on
  Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59.trace_completedLogUnit60Lambda_eq_scaled_add_deep_error,
  Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59.completedLog_unit60_eval59_eq_scaledNormalizedFiniteLog59
#guard_depends_on
  Fermat.FiftyNine.Conservation.CompletedLogTail59.completedLogUnit60ValuedInteger_sub_scaled_eq_prime_mul_lambda,
  Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59.completedLogUnit60ValuedInteger_sub_scaled_mem
#guard_depends_on
  Fermat.FiftyNine.Conservation.CompletedLogTail59.completedLogUnit60Lambda_eq_scaled_add_prime_mul_lambda_error,
  Fermat.FiftyNine.Conservation.CompletedLogTail59.completedLogUnit60ValuedInteger_sub_scaled_eq_prime_mul_lambda
#guard_depends_on
  Fermat.FiftyNine.Conservation.CompletedLogTail59.trace_completedLogUnit60Lambda_eq_prime_mul_normalized_add_lambda_error,
  Fermat.FiftyNine.Conservation.CompletedLogTail59.completedLogUnit60Lambda_eq_scaled_add_prime_mul_lambda_error
#guard_depends_on
  Fermat.FiftyNine.Conservation.CompletedLogTail59.trace_completedLogUnit60Lambda_eq_prime_mul_normalized_add_lambda_error,
  Fermat.FiftyNine.Conservation.TwistedFiniteLogLocalTrace59.localTrace_scaledNormalizedFiniteLog59
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalIntegralTrace59.dworkValuedAlgEquiv59,
  Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59.dworkCompleteToValuedInteger59_algebraMap
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalIntegralTrace59.valuedIntegerBasis59,
  Fermat.FiftyNine.Conservation.LocalIntegralTrace59.dworkValuedAlgEquiv59
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalIntegralTrace59.integerTrace_mem_maximalIdeal_of_mem_lambda,
  Fermat.FiftyNine.Conservation.LocalIntegralTrace59.map_rationalMaximalIdeal_eq_lambdaIdeal_pow_pred
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalIntegralTrace59.localTrace59_valuedInteger_eq_integerTrace,
  Algebra.trace_localization
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalIntegralTrace59.exists_rationalInteger_localTrace_eq_prime_mul_of_mem_lambda,
  Fermat.FiftyNine.Conservation.LocalIntegralTrace59.integerTrace_mem_maximalIdeal_of_mem_lambda
#guard_depends_on
  Fermat.FiftyNine.Conservation.LocalIntegralTrace59.exists_rationalInteger_localTrace_eq_prime_mul_of_mem_lambda,
  Fermat.FiftyNine.Conservation.LocalIntegralTrace59.localTrace59_valuedInteger_eq_integerTrace
#guard_depends_on
  Fermat.FiftyNine.Conservation.CompletedLogTraceNonzero59.normalizedCompletedLogTrace59_eq_finite_add_prime_mul_integer,
  Fermat.FiftyNine.Conservation.CompletedLogTail59.trace_completedLogUnit60Lambda_eq_prime_mul_normalized_add_lambda_error
#guard_depends_on
  Fermat.FiftyNine.Conservation.CompletedLogTraceNonzero59.normalizedCompletedLogTrace59_eq_finite_add_prime_mul_integer,
  Fermat.FiftyNine.Conservation.LocalIntegralTrace59.exists_rationalInteger_localTrace_eq_prime_mul_of_mem_lambda
#guard_depends_on
  Fermat.FiftyNine.Conservation.CompletedLogTraceNonzero59.exists_integer_normalizedCompletedLogTrace59_and_residue,
  Fermat.FiftyNine.Conservation.CompletedLogTraceNonzero59.normalizedCompletedLogTrace59_eq_finite_add_prime_mul_integer
#guard_depends_on
  Fermat.FiftyNine.Conservation.CompletedLogTraceNonzero59.exists_integer_normalizedCompletedLogTrace59_and_residue,
  Fermat.FiftyNine.Conservation.TwistedArtinHasseLocalTrace59.normalizedLocalTraceFiniteLog59Integer_mod59
#guard_depends_on
  Fermat.FiftyNine.Conservation.CompletedLogTraceNonzero59.normalizedCompletedLogTrace59_ne_zero,
  Fermat.FiftyNine.Conservation.CompletedLogTraceNonzero59.exists_integer_normalizedCompletedLogTrace59_and_residue
#guard_depends_on
  Fermat.FiftyNine.Conservation.CompletedLogResidue59.normalizedCompletedLogTrace59Integer,
  Fermat.FiftyNine.Conservation.CompletedLogTraceNonzero59.exists_integer_normalizedCompletedLogTrace59_and_residue
#guard_depends_on
  Fermat.FiftyNine.Conservation.CompletedLogResidue59.normalizedCompletedLogTrace59Residue_eq_neg_one,
  Fermat.FiftyNine.Conservation.CompletedLogTraceNonzero59.exists_integer_normalizedCompletedLogTrace59_and_residue
#guard_depends_on
  Fermat.FiftyNine.Conservation.CompletedLogResidue59.normalizedCompletedLogTrace59Residue_ne_zero,
  Fermat.FiftyNine.Conservation.CompletedLogResidue59.normalizedCompletedLogTrace59Residue_eq_neg_one
#guard_depends_on
  Fermat.FiftyNine.Conservation.CompletedLogPowerObstruction59.completedLogValuedInteger59_mem_lambda,
  KummerCriterion.CyclotomicUnits.completedLog_evalₐ_succ
#guard_depends_on
  Fermat.FiftyNine.Conservation.CompletedLogPowerObstruction59.completedLogUnit60_not_pow_in_completedLogDomain,
  KummerCriterion.CyclotomicUnits.completedLog_pow
#guard_depends_on
  Fermat.FiftyNine.Conservation.CompletedLogPowerObstruction59.completedLogUnit60_not_pow_in_completedLogDomain,
  Fermat.FiftyNine.Conservation.LocalIntegralTrace59.exists_rationalInteger_localTrace_eq_prime_mul_of_mem_lambda
#guard_depends_on
  Fermat.FiftyNine.Conservation.CompletedLogPowerObstruction59.completedLogUnit60_not_pow_in_completedLogDomain,
  Fermat.FiftyNine.Conservation.CompletedLogResidue59.normalizedCompletedLogTrace59Residue_eq_neg_one
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistedLambdaNormalizationSign59.finiteCarryReadout_eq_neg_normalizedCompletedLogTrace59Residue,
  Fermat.Conservation.ContinuousCyclicH2Readout59.actualContinuousCyclicH2Readout59_continuousCarryH2Class59
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistedLambdaNormalizationSign59.finiteCarryReadout_eq_neg_normalizedCompletedLogTrace59Residue,
  Fermat.FiftyNine.Conservation.CompletedLogResidue59.normalizedCompletedLogTrace59Residue_eq_neg_one
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistedLambdaNormalizationSign59.normalizedReadout_twistedLambdaKummerCup_eq_neg_completedLogResidue,
  Fermat.FiftyNine.Conservation.TwistedLambdaH2Inflation59.readout_twistedLambdaKummerCupH2Class59_eq_one_of_normalized_inflation
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistedLambdaNormalizationSign59.normalizedReadout_twistedLambdaKummerCup_eq_neg_completedLogResidue,
  Fermat.FiftyNine.Conservation.CompletedLogResidue59.normalizedCompletedLogTrace59Residue_eq_neg_one
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistedLambdaNormalizedEndpoint59.twistedLambdaKummerCupH2Class59_ne_zero_of_normalized_readout,
  Fermat.FiftyNine.Conservation.TwistedLambdaH2Inflation59.readout_twistedLambdaKummerCupH2Class59_eq_one_of_normalized_inflation
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistedLambdaNormalizedEndpoint59.normalizedReadout_twistedLambdaEndpoint59,
  Fermat.FiftyNine.Conservation.TwistedLambdaNormalizationSign59.normalizedReadout_twistedLambdaKummerCup_eq_neg_completedLogResidue
#guard_depends_on
  Fermat.FiftyNine.Conservation.TwistedLambdaNormalizedEndpoint59.normalizedReadout_twistedLambdaEndpoint59,
  Fermat.FiftyNine.Conservation.TwistedLambdaKummerNormCriterion59.twistedLambdaKummerCupH2Class59_ne_zero_iff_primitiveRoot_not_norm

#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalH2PairingFromCup,
  Fermat.Conservation.ContinuousKummerTateAlgebra.kummerPairingFromCup
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalH2PairingFromCup,
  Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaLocalPrimitiveRoot59
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalH2PairingFromCup,
  Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaLocalPrimitiveRoot59_isPrimitive
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalPairingFromCup,
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalH2PairingFromCup
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalPairingFromContinuousReadout,
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalPairingFromCup
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaGlobalPairingFromCup,
  Fermat.Conservation.LocalKummerTransport.Pairing.pullback
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaGlobalPairingFromCup,
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalPairingFromCup
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaGlobalPairingFromCup,
  Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaLocalization59

#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.LambdaOrientedContinuousH2,
  Fermat.Conservation.ContinuousKummerOrientation.OrientedContinuousH2
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2CoefficientOrientationEquiv59,
  Fermat.Conservation.ContinuousKummerOrientation.orientH2Equiv
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2CoefficientOrientationEquiv59,
  Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaLocalPrimitiveRoot59
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2CoefficientOrientationEquiv59,
  Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaLocalPrimitiveRoot59_isPrimitive
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.exists_conditionalNoncanonicalLambdaH2Readout_eq_one,
  Fermat.Conservation.ContinuousKummerTateAlgebra.exists_conditionalNoncanonicalReadout_eq_one
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.LambdaOrientedContinuousH2Readout59,
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.LambdaOrientedContinuousH2
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2SuppliedLinearReadoutTransportEquiv59,
  Fermat.Conservation.ContinuousKummerOrientation.orientH2ReadoutEquiv
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2SuppliedLinearReadoutTransportEquiv59,
  Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaLocalPrimitiveRoot59
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2SuppliedLinearReadoutTransportEquiv59,
  Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaLocalPrimitiveRoot59_isPrimitive
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.LambdaOrientedContinuousH2ContinuousReadout59,
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.LambdaOrientedContinuousH2
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2SuppliedContinuousReadoutTransportEquiv59,
  Fermat.Conservation.ContinuousKummerOrientation.orientH2ContinuousReadoutEquiv
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2SuppliedContinuousReadoutTransportEquiv59,
  Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaLocalPrimitiveRoot59
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2SuppliedContinuousReadoutTransportEquiv59,
  Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaLocalPrimitiveRoot59_isPrimitive
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaContinuousCup59,
  Fermat.Conservation.ContinuousKummerTateAlgebra.kummerCupH1
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaContinuousCup59,
  Fermat.Conservation.ContinuousKummerTateCup.cupH1
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalH2Pairing,
  Fermat.Conservation.ContinuousKummerTateAlgebra.kummerPairing
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalPairing,
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalPairingFromCup
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalPairing,
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaContinuousCup59
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalPairingWithContinuousReadout,
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalPairingFromContinuousReadout
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalPairingWithContinuousReadout,
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaContinuousCup59
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaGlobalPairing,
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaGlobalPairingFromCup
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaGlobalPairing,
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaContinuousCup59
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.toCanonicalReflectedWildKummerCoreAt59,
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaGlobalPairing
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.toCanonicalReflectedWildKummerCoreAt59,
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicReflectedEmptySupportLanding827
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.toCanonicalReflectedWildKummerCoreAt59_pairing_apply,
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.toCanonicalReflectedWildKummerCoreAt59

/-! The exact norm intersection is driven in both directions by the completed
norm-image bridge and depth-60 Hensel surjectivity; its pointwise form really
passes through the one-coefficient detector. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.ExactNormIntersection59.mem_twistedLambdaNormUnits59_range_of_mem_U60,
  Fermat.FiftyNine.Conservation.CriticalUnitPowerSurjectivity59.exists_fieldUnit_pow59_eq_of_mem_U60
#guard_depends_on
  Fermat.FiftyNine.Conservation.ExactNormIntersection59.twistedLambdaNormUnits59_range_inf_U59_eq_U60,
  Fermat.FiftyNine.Conservation.NormImageBridge59.twistedLambdaNormUnits59_mem_U60_of_mem_U59
#guard_depends_on
  Fermat.FiftyNine.Conservation.ExactNormIntersection59.twistedLambdaNormUnits59_range_inf_U59_eq_U60,
  Fermat.FiftyNine.Conservation.ExactNormIntersection59.mem_twistedLambdaNormUnits59_range_of_mem_U60
#guard_depends_on
  Fermat.FiftyNine.Conservation.ExactNormIntersection59.mem_twistedLambdaNormUnits59_range_iff_criticalCoefficient59_eq_zero,
  Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59.criticalCoefficient59_eq_zero_iff
#guard_depends_on
  Fermat.FiftyNine.Conservation.ExactNormIntersection59.mem_twistedLambdaNormUnits59_range_iff_criticalCoefficient59_eq_zero,
  Fermat.FiftyNine.Conservation.ExactNormIntersection59.mem_twistedLambdaNormUnits59_range_iff_mem_U60_of_mem_U59
#guard_depends_on
  Fermat.FiftyNine.Conservation.ExactNormIntersection59.exists_norm_eq_iff_criticalCoefficient59_eq_zero,
  Fermat.FiftyNine.Conservation.ExactNormIntersection59.exists_norm_eq_iff_mem_twistedLambdaNormUnits59_range
#guard_depends_on
  Fermat.FiftyNine.Conservation.ExactNormIntersection59.not_exists_norm_eq_iff_criticalCoefficient59_ne_zero,
  Fermat.FiftyNine.Conservation.ExactNormIntersection59.exists_norm_eq_iff_criticalCoefficient59_eq_zero

/-! The downstream route is constructor-directed: quotient pairing to seated
reading, normalized `H²` readout to total pairing, then core to localization.
These guards prevent the readback names alone from disguising a detached
harness. -/

#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.oldReadingOfPairing,
  Fermat.Conservation.SelmerEigenspace.toKummerClass
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.oldReadingOfPairing_adjoint,
  Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.oldReadingOfPairing
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.oldWildInterfaceOfPairing,
  Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.oldReadingOfPairing_adjoint
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.oldWildInterfaceOfPairing_eq_iff_calibration,
  Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.oldWildInterfaceOfPairing
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.continuousOldWildInterface59,
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaGlobalPairing
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.continuousReflectedWildKummerCoreAt59,
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicReflectedEmptySupportLanding827
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.continuousReflectedWildLocalizationAt59,
  Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.continuousReflectedWildKummerCoreAt59
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.exists_normalizedContinuousReflectedWildKummerCoreAt59,
  Fermat.FiftyNine.Conservation.NormImageConsequences59.exists_normalizedInflationReadout59
#guard_depends_on
  Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.exists_normalizedContinuousReflectedWildLocalizationAt59,
  Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.continuousReflectedWildLocalizationAt59

#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.normalizedInflationReadout59,
  Fermat.FiftyNine.Conservation.NormImageConsequences59.exists_normalizedInflationReadout59
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.normalizedInflationReadout59_twistedLambdaCup,
  Fermat.FiftyNine.Conservation.TwistedLambdaH2Inflation59.readout_twistedLambdaKummerCupH2Class59_eq_one_of_normalized_inflation
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.normalizedInflationReadout59_unit60Cup,
  Fermat.FiftyNine.Conservation.TwistedLambdaCupUnitReduction59.twistedLambdaKummerCupH2Class59_eq_unit60KummerCupH2Class59
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.normalizedInflationReadout59_twistedLambdaCup_eq_neg_logResidue,
  Fermat.FiftyNine.Conservation.TwistedLambdaNormalizationSign59.normalizedReadout_twistedLambdaKummerCup_eq_neg_completedLogResidue
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.normalizedLambdaLocalPairing59,
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalPairing
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.normalizedLambdaGlobalPairing59,
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaGlobalPairing
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.normalizedLambdaLocalPairing59_twistedLambda_primitive,
  Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.normalizedInflationReadout59_twistedLambdaCup
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.normalizedLambdaLocalPairing59_unit60_primitive,
  Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.normalizedInflationReadout59_unit60Cup
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.normalizedLambdaGlobalPairing59_twistedLambda_primitive,
  Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.normalizedLambdaLocalPairing59_twistedLambda_primitive
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.normalizedLambdaGlobalPairing59_unit60_primitive,
  Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.normalizedLambdaLocalPairing59_unit60_primitive
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.toNormalizedReflectedWildKummerCoreAt59,
  Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.toCanonicalReflectedWildKummerCoreAt59

#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousWildLocalization59.normalizedOldWildInterface59,
  Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.continuousOldWildInterface59
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousWildLocalization59.normalizedReflectedWildKummerCore59,
  Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.continuousReflectedWildKummerCoreAt59
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousWildLocalization59.normalizedReflectedWildKummerCore59_unit60_primitive,
  Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59.normalizedLambdaGlobalPairing59_unit60_primitive
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousWildLocalization59.normalizedReflectedWildLocalization59,
  Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59.continuousReflectedWildLocalizationAt59
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousWildLocalization59.normalizedReflectedWildLocalization59_agrees_with_old,
  Fermat.FiftyNine.Conservation.VostokovLocalization59.ReflectedWildKummerCoreAt59.agrees_with_old

#guard_depends_on
  Fermat.FiftyNine.Conservation.AlgebraicPointedIncidence827.reflectedCoordinatePairing827_flip_injective,
  Fermat.FiftyNine.Conservation.PointedTateIncidence.reflectedCoordinatePairing827
#guard_depends_on
  Fermat.FiftyNine.Conservation.AlgebraicPointedIncidence827.pointedTateIncidence827_of_fixed_of_localization_ne_zero,
  Fermat.FiftyNine.Conservation.AlgebraicPointedIncidence827.reflectedCoordinatePairing827_flip_injective
#guard_depends_on
  Fermat.FiftyNine.Conservation.AlgebraicPointedIncidence827.pointedTateIncidence827_of_fixed_of_localization_ne_zero,
  Fermat.Conservation.ReadoutLedger.existsUnique_rankOneFactorization
#guard_depends_on
  Fermat.FiftyNine.Conservation.AlgebraicPointedIncidence827.reflectedPointedLocalization827_ne_zero_of_lift,
  Fermat.FiftyNine.Conservation.DetectorWitness827.qLocalizationCoordinate827
#guard_depends_on
  Fermat.FiftyNine.Conservation.AlgebraicPointedIncidence827.pointedTateIncidence827_of_fourierSeating_of_localization_ne_zero,
  Fermat.FiftyNine.Conservation.SplitPrimeFourier827.fixedAttention_of_fourierSeating
#guard_depends_on
  Fermat.FiftyNine.Conservation.AlgebraicPointedIncidence827.pointedTateIncidence827_of_fourierSeating_of_localization_ne_zero,
  Fermat.FiftyNine.Conservation.AlgebraicPointedIncidence827.pointedTateIncidence827_of_fixed_of_localization_ne_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.AlgebraicPointedIncidence827.pointedTateIncidence827_of_fourierSeating_of_lift,
  Fermat.FiftyNine.Conservation.AlgebraicPointedIncidence827.reflectedPointedLocalization827_ne_zero_of_lift
#guard_depends_on
  Fermat.FiftyNine.Conservation.AlgebraicPointedIncidence827.pointedTateIncidence827_of_fourierSeating_of_lift,
  Fermat.FiftyNine.Conservation.AlgebraicPointedIncidence827.pointedTateIncidence827_of_fourierSeating_of_localization_ne_zero

#guard_depends_on
  Fermat.FiftyNine.Conservation.CyclotomicLocalizationEquivariance827.indexedPlaceOrbitEquiv827_eq_cyclotomicPlaceEquiv59,
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicPlaceEquiv59
#guard_depends_on
  Fermat.FiftyNine.Conservation.CyclotomicLocalizationEquivariance827.cyclotomicQLocalizationEquivariance827,
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicValuationCovariance59
#guard_depends_on
  Fermat.FiftyNine.Conservation.CyclotomicLocalizationEquivariance827.cyclotomicQLocalizationEquivariance827,
  Fermat.FiftyNine.Conservation.CyclotomicLocalizationEquivariance827.indexedPlaceOrbitEquiv827_eq_cyclotomicPlaceEquiv59

#guard_depends_on
  Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827.projectedCandidateSClassObstruction827_eq_one_of_lift,
  IsDedekindDomain.selmerGroup.toSClass_ker
#guard_depends_on
  Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827.classSilentPointedCoordinate827,
  Fermat.FiftyNine.Conservation.GaugeSteering827.relaxedClassProjection827
#guard_depends_on
  Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827.classSilentPointedCoordinate827,
  Fermat.FiftyNine.Conservation.GaugeSteering827.pointedCoordinate827
#guard_depends_on
  Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827.classSilentPointedCoordinate827_apply,
  Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827.classSilentPointedCoordinate827
#guard_depends_on
  Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827.nonempty_reflectedQRelaxedLocalizationLift827_iff,
  Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827.projectedCandidateSClassObstruction827_eq_one_of_lift
#guard_depends_on
  Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827.nonempty_reflectedQRelaxedLocalizationLift827_iff,
  Fermat.FiftyNine.Conservation.DetectorWitness827.ReflectedQRelaxedLocalizationLift827.ofSource_of_sClassObstruction_eq_one
#guard_depends_on
  Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827.qLocalizationCoordinate_ne_zero_at_every_place_of_lift,
  Fermat.FiftyNine.Conservation.CyclotomicLocalizationEquivariance827.cyclotomicQLocalizationEquivariance827
#guard_depends_on
  Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827.nonempty_cyclotomicReflectedQRelaxedLocalizationLift827_iff,
  Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827.nonempty_reflectedQRelaxedLocalizationLift827_iff
#guard_depends_on
  Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827.nonempty_cyclotomicReflectedQRelaxedLocalizationLift827_iff,
  Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827.qLocalizationCoordinate_ne_zero_at_every_place_of_lift
#guard_depends_on
  Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827.tameSilence827_ne_zero_of_lift,
  Fermat.FiftyNine.Conservation.SplitPrimeFourier827.fixedAttention_of_fourierSeating
#guard_depends_on
  Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827.tameSilence827_ne_zero_of_lift,
  Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827.projectedCandidateSClassObstruction827_eq_one_of_lift

#guard_depends_on
  Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827.attestationPrimeFieldUnit827,
  Fermat.FiftyNine.Conservation.Credit.attestationPrime
#guard_depends_on
  Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827.attestationPrime_valuation_toAdd_eq_neg_one,
  Fermat.FiftyNine.Conservation.SplitPrimeFourier827.attestationPrime_not_dvd_fiftyNine
#guard_depends_on
  Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827.attestationPrime_valuation_toAdd_eq_zero_of_not_mem,
  Fermat.FiftyNine.Conservation.DetectorWitness827.placesOver827
#guard_depends_on
  Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827.attestationPrimeSource827,
  Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827.attestationPrime_valuation_toAdd_eq_zero_of_not_mem
#guard_depends_on
  Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827.cyclotomicQRelaxedSelmerRepresentation827_attestationPrimeSource,
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicKummerHom59_mk
#guard_depends_on
  Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827.attestationPrimeSource827_ne_zero,
  Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827.attestationPrime_valuation_toAdd_eq_neg_one
#guard_depends_on
  Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827.attestationPrimeSource827_mem_trivial_characterEigenspace,
  Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827.cyclotomicQRelaxedSelmerRepresentation827_attestationPrimeSource
#guard_depends_on
  Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827.attestationPrimeSource827_mem_reflectedCharacter_of_eq_one,
  Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827.attestationPrimeSource827_mem_trivial_characterEigenspace

#guard_depends_on
  Fermat.FiftyNine.Conservation.TrivialReflectedAttestationPrimeLift827.attestationPrime_reflectedProjector_eq_source827,
  Fermat.Conservation.SelmerEigenspace.characterProjectorAt_eq_self_of_mem
#guard_depends_on
  Fermat.FiftyNine.Conservation.TrivialReflectedAttestationPrimeLift827.attestationPrimeDetectorSUnit827,
  Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827.attestationPrime_valuation_toAdd_eq_zero_of_not_mem
#guard_depends_on
  Fermat.FiftyNine.Conservation.TrivialReflectedAttestationPrimeLift827.fromSUnitLift_attestationPrimeDetectorSUnit827,
  Fermat.FiftyNine.Conservation.TrivialReflectedAttestationPrimeLift827.attestationPrime_reflectedProjector_eq_source827
#guard_depends_on
  Fermat.FiftyNine.Conservation.TrivialReflectedAttestationPrimeLift827.projectedCandidateSClassObstruction827_attestationPrime_eq_one,
  Fermat.FiftyNine.Conservation.TrivialReflectedAttestationPrimeLift827.fromSUnitLift_attestationPrimeDetectorSUnit827
#guard_depends_on
  Fermat.FiftyNine.Conservation.TrivialReflectedAttestationPrimeLift827.qLocalizationCoordinate827_attestationPrime_ne_zero,
  Fermat.FiftyNine.Conservation.TrivialReflectedAttestationPrimeLift827.attestationPrime_reflectedProjector_eq_source827
#guard_depends_on
  Fermat.FiftyNine.Conservation.TrivialReflectedAttestationPrimeLift827.qLocalizationCoordinate827_attestationPrime_ne_zero,
  Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827.attestationPrime_valuation_toAdd_eq_neg_one
#guard_depends_on
  Fermat.FiftyNine.Conservation.TrivialReflectedAttestationPrimeLift827.attestationPrimeReflectedLocalizationLift827,
  Fermat.FiftyNine.Conservation.TrivialReflectedAttestationPrimeLift827.qLocalizationCoordinate827_attestationPrime_ne_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.TrivialReflectedAttestationPrimeLift827.attestationPrimeReflectedLocalizationLift827,
  Fermat.FiftyNine.Conservation.TrivialReflectedAttestationPrimeLift827.projectedCandidateSClassObstruction827_attestationPrime_eq_one
#guard_depends_on
  Fermat.FiftyNine.Conservation.TrivialReflectedAttestationPrimeLift827.nonempty_attestationPrimeReflectedLocalizationLift827,
  Fermat.FiftyNine.Conservation.TrivialReflectedAttestationPrimeLift827.attestationPrimeReflectedLocalizationLift827
#guard_depends_on
  Fermat.FiftyNine.Conservation.TrivialReflectedAttestationPrimeLift827.nonempty_attestationPrimeReflectedLocalizationLift827,
  Fermat.FiftyNine.Conservation.SplitPrimeFourier827.placesOver827_ncard_eq_fiftyEight

#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.wildLawfulness827_of_reciprocity,
  Fermat.FiftyNine.Conservation.TateBridge.Lambda_apply_eq_zero_of_reciprocity
#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.wildProcessesAtLeastSevenA_zero_iff,
  Fermat.FiftyNine.Conservation.UlamReadout827.WildProcessesAtLeastSevenA.ker_wild_le_ker_gauge
#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.vandiverSevenA_of_classGauge_eq_zero,
  Fermat.FiftyNine.Conservation.UlamReadout827.selectedClassGauge59_eq_zero_iff_vandiverSevenA
#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.wildCoefficient827_eq_zero_of_reciprocity,
  Fermat.FiftyNine.Conservation.UlamReadout827.qRelaxedWild_factorization
#guard_depends_on
  Fermat.FiftyNine.Conservation.UlamReadout827.wildCoefficient827_eq_zero_of_reciprocity,
  Fermat.FiftyNine.Conservation.UlamReadout827.wildLawfulness827_of_reciprocity
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.oldPrimal59_nsmul_eq_zero,
  Fermat.Conservation.SelmerEigenspace.p_nsmul_eq_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedQLocalizationEquivariance827,
  Fermat.FiftyNine.Conservation.CyclotomicLocalizationEquivariance827.cyclotomicQLocalizationEquivariance827
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedReflectedWildCarrierExtension59,
  Fermat.FiftyNine.Conservation.NormalizedContinuousWildLocalization59.normalizedReflectedWildLocalization59
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedBoundaryFunctional59_ne_zero,
  Fermat.FiftyNine.Conservation.UlamReadout827.reflectedBoundaryFunctional827_ne_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedReflectedFiber59_nonempty,
  Fermat.FiftyNine.Conservation.UlamReadout827.normalizedReflectedFiber827_nonempty
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.NormalizedWildLawfulness59,
  Fermat.FiftyNine.Conservation.UlamReadout827.WildLawfulness827
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildCoefficient59,
  Fermat.FiftyNine.Conservation.UlamReadout827.wildCoefficient827
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildCoefficient59_factorization,
  Fermat.FiftyNine.Conservation.UlamReadout827.qRelaxedWild_factorization
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.NormalizedTameSilenceReciprocity59,
  Fermat.FiftyNine.Conservation.UlamReadout827.TameSilenceReciprocity827
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.vandiverSevenA_of_normalizedContinuousReadout,
  Fermat.FiftyNine.Conservation.UlamReadout827.vandiverSevenA_of_readout_interfaces
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.vandiverSevenA_of_normalizedContinuousReadout,
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedReflectedFiber59_nonempty
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildLawfulness59_of_reciprocity,
  Fermat.FiftyNine.Conservation.UlamReadout827.wildLawfulness827_of_reciprocity
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildCoefficientOfReciprocity59,
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildLawfulness59_of_reciprocity
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildCoefficientOfReciprocity59_eq_zero,
  Fermat.FiftyNine.Conservation.UlamReadout827.wildCoefficient827_eq_zero_of_reciprocity
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedPointedIncidence59OfLift,
  Fermat.FiftyNine.Conservation.AlgebraicPointedIncidence827.pointedTateIncidence827_of_fourierSeating_of_lift
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedPointedIncidence59OfLiftCanonical,
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedPointedIncidence59OfLift
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedPointedIncidence59OfLiftCanonical,
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedQLocalizationEquivariance827
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildCoefficientOfLift59,
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildCoefficientOfReciprocity59
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildCoefficientOfLift59,
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedPointedIncidence59OfLift
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildCoefficientOfLift59_eq_zero,
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildCoefficientOfReciprocity59_eq_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildCoefficientOfCanonicalLift59,
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildCoefficientOfLift59
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildCoefficientOfCanonicalLift59,
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedQLocalizationEquivariance827
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildCoefficientOfCanonicalLift59_eq_zero,
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildCoefficientOfLift59_eq_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedProcessesAtLeastSevenA_iff_gauge_eq_zero,
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildCoefficientOfReciprocity59_eq_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedProcessesAtLeastSevenA_iff_gauge_eq_zero,
  Fermat.FiftyNine.Conservation.UlamReadout827.wildProcessesAtLeastSevenA_zero_iff
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedLiftProcessesAtLeastSevenA_iff_gauge_eq_zero,
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildCoefficientOfLift59_eq_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedLiftProcessesAtLeastSevenA_iff_gauge_eq_zero,
  Fermat.FiftyNine.Conservation.UlamReadout827.wildProcessesAtLeastSevenA_zero_iff
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedCanonicalLiftProcessesAtLeastSevenA_iff_gauge_eq_zero,
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildCoefficientOfCanonicalLift59_eq_zero
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedCanonicalLiftProcessesAtLeastSevenA_iff_gauge_eq_zero,
  Fermat.FiftyNine.Conservation.UlamReadout827.wildProcessesAtLeastSevenA_zero_iff
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.vandiverSevenA_of_normalizedContinuousReciprocity,
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.vandiverSevenA_of_normalizedContinuousReadout
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.vandiverSevenA_of_normalizedContinuousReciprocity,
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedWildLawfulness59_of_reciprocity
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.vandiverSevenA_of_normalizedContinuousLift,
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.vandiverSevenA_of_normalizedContinuousReciprocity
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.vandiverSevenA_of_normalizedContinuousLift,
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedPointedIncidence59OfLift
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.vandiverSevenA_of_normalizedContinuousCanonicalLift,
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.vandiverSevenA_of_normalizedContinuousLift
#guard_depends_on
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.vandiverSevenA_of_normalizedContinuousCanonicalLift,
  Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59.normalizedQLocalizationEquivariance827

#guard_depends_on
  Fermat.FiftyNine.Conservation.StatewiseTwistedLambdaBridge59.rawPlusKummerClass59_eq_normalizedPlus_add_denominator,
  Fermat.FiftyNine.Conservation.StateFactorPair.normalizedPlusFactor_spec
#guard_depends_on
  Fermat.FiftyNine.Conservation.StatewiseTwistedLambdaBridge59.localize_fixedDenominatorKummerClass59,
  Fermat.Conservation.LocalKummerTransport.map_classOfUnit
#guard_depends_on
  Fermat.FiftyNine.Conservation.StatewiseTwistedLambdaBridge59.localizedRawPlusKummerClass59_eq_normalizedPlus_add_lambda,
  Fermat.FiftyNine.Conservation.StatewiseTwistedLambdaBridge59.rawPlusKummerClass59_eq_normalizedPlus_add_denominator
#guard_depends_on
  Fermat.FiftyNine.Conservation.StatewiseTwistedLambdaBridge59.localizedNormalizedPlus_eq_twistUnit_iff_rawPlus_eq_twistedLambda,
  Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59.twistedLambdaRadicandKummerClass59_eq_add
#guard_depends_on
  Fermat.FiftyNine.Conservation.StatewiseTwistedLambdaBridge59.localizedStatewiseRepresentative_readback59,
  Fermat.FiftyNine.Conservation.VostokovShapeAudit59.statewiseRepresentative_readback
#guard_depends_on
  Fermat.FiftyNine.Conservation.StatewiseTwistedLambdaBridge59.localizedStatewise_eq_twistUnit_iff_rawPlus_eq_twistedLambda_of_eq_normalized,
  Fermat.FiftyNine.Conservation.StatewiseTwistedLambdaBridge59.localizedNormalizedPlus_eq_twistUnit_iff_rawPlus_eq_twistedLambda

/--
info: 'Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.LambdaOrientedContinuousH2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.LambdaOrientedContinuousH2

/--
info: 'Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2CoefficientOrientationEquiv59' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2CoefficientOrientationEquiv59

/--
info: 'Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2CoefficientOrientationEquiv59_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2CoefficientOrientationEquiv59_apply

/--
info: 'Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.exists_conditionalNoncanonicalLambdaH2Readout_eq_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.exists_conditionalNoncanonicalLambdaH2Readout_eq_one

/--
info: 'Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.LambdaOrientedContinuousH2Readout59' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.LambdaOrientedContinuousH2Readout59

/--
info: 'Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2SuppliedLinearReadoutTransportEquiv59' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2SuppliedLinearReadoutTransportEquiv59

/--
info: 'Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2SuppliedLinearReadoutTransportEquiv59_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2SuppliedLinearReadoutTransportEquiv59_apply

/--
info: 'Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2SuppliedLinearReadoutTransportEquiv59_symm_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2SuppliedLinearReadoutTransportEquiv59_symm_apply

/--
info: 'Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.LambdaOrientedContinuousH2ContinuousReadout59' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.LambdaOrientedContinuousH2ContinuousReadout59

/--
info: 'Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2SuppliedContinuousReadoutTransportEquiv59' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2SuppliedContinuousReadoutTransportEquiv59

/--
info: 'Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2SuppliedContinuousReadoutTransportEquiv59_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2SuppliedContinuousReadoutTransportEquiv59_apply

/--
info: 'Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2SuppliedContinuousReadoutTransportEquiv59_symm_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaH2SuppliedContinuousReadoutTransportEquiv59_symm_apply

/--
info: 'Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaContinuousCup59' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaContinuousCup59

/--
info: 'Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaContinuousCup59_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaContinuousCup59_apply

/--
info: 'Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalH2Pairing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalH2Pairing

/--
info: 'Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalH2Pairing_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalH2Pairing_apply

/--
info: 'Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalPairing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalPairing

/--
info: 'Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalPairing_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalPairing_apply

/--
info: 'Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalPairingWithContinuousReadout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalPairingWithContinuousReadout

/--
info: 'Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalPairingWithContinuousReadout_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaLocalPairingWithContinuousReadout_apply

/--
info: 'Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaGlobalPairing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaGlobalPairing

/--
info: 'Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaGlobalPairing_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.lambdaGlobalPairing_apply

/--
info: 'Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.toCanonicalReflectedWildKummerCoreAt59' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.toCanonicalReflectedWildKummerCoreAt59

/--
info: 'Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.toCanonicalReflectedWildKummerCoreAt59_pairing_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59.toCanonicalReflectedWildKummerCoreAt59_pairing_apply

-- All nine pairing readbacks, the canonical cup readback, the coefficient-
-- orientation readback, and the four supplied-readout transport readbacks are
-- definitional
-- (`rfl`).  Their expanded formulas are signature audits above; dependency
-- guards intentionally do not pretend that constants occurring only in
-- theorem types occur in the proof values.

/-! ### Span-restricted pairing at the literal lambda place

This is the narrowest compiled local adapter.  Completion, lambda place,
primitive root, both Kummer maps, quotient pullback, canonical actions, and
strict-to-relaxed landing are derived.  Its remaining inputs are a linear
readout on the actual Kummer cup span and an independent old-reading
calibration; neither continuous comparison nor calibration is fabricated. -/

#check Fermat.FiftyNine.Conservation.KummerCupSpanLocalization59.LambdaKummerCupSpan59
#check Fermat.FiftyNine.Conservation.KummerCupSpanLocalization59.LambdaKummerCupSpanReadout59
#check Fermat.FiftyNine.Conservation.KummerCupSpanLocalization59.lambdaLocalPairing
#check Fermat.FiftyNine.Conservation.KummerCupSpanLocalization59.pairing
#check Fermat.FiftyNine.Conservation.KummerCupSpanLocalization59.pairing_apply
#check Fermat.FiftyNine.Conservation.KummerCupSpanLocalization59.pairing_classOfUnit
#check Fermat.FiftyNine.Conservation.KummerCupSpanLocalization59.toCanonicalReflectedWildKummerCoreAt59
#check Fermat.FiftyNine.Conservation.KummerCupSpanLocalization59.toCanonicalReflectedWildKummerCoreAt59_pairing_apply

#guard_depends_on
  Fermat.FiftyNine.Conservation.KummerCupSpanLocalization59.lambdaLocalPairing,
  Fermat.Conservation.KummerCupSpanReadout.discretePairing
#guard_depends_on
  Fermat.FiftyNine.Conservation.KummerCupSpanLocalization59.lambdaLocalPairing,
  Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaLocalPrimitiveRoot59
#guard_depends_on
  Fermat.FiftyNine.Conservation.KummerCupSpanLocalization59.pairing,
  Fermat.Conservation.LocalKummerTransport.Pairing.pullback
#guard_depends_on
  Fermat.FiftyNine.Conservation.KummerCupSpanLocalization59.pairing,
  Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaLocalization59
#guard_depends_on
  Fermat.FiftyNine.Conservation.KummerCupSpanLocalization59.toCanonicalReflectedWildKummerCoreAt59,
  Fermat.FiftyNine.Conservation.KummerCupSpanLocalization59.pairing
#guard_depends_on
  Fermat.FiftyNine.Conservation.KummerCupSpanLocalization59.toCanonicalReflectedWildKummerCoreAt59,
  Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59.cyclotomicReflectedEmptySupportLanding827
#guard_depends_on
  Fermat.FiftyNine.Conservation.KummerCupSpanLocalization59.toCanonicalReflectedWildKummerCoreAt59_pairing_apply,
  Fermat.FiftyNine.Conservation.KummerCupSpanLocalization59.toCanonicalReflectedWildKummerCoreAt59

/-! ### Tier-(c) 59/827 adapter -/

#check Fermat.FiftyNine.Conservation.IwasawaLocalization59.CalibratedReductionAt59
#check Fermat.FiftyNine.Conservation.IwasawaLocalization59.descend_eq_oldReading
#check Fermat.FiftyNine.Conservation.IwasawaLocalization59.toReflectedWildKummerCoreAt59
#check Fermat.FiftyNine.Conservation.IwasawaLocalization59.toReflectedWildLocalizationAt59

#guard_depends_on
  Fermat.FiftyNine.Conservation.IwasawaLocalization59.descend_eq_oldReading,
  Fermat.FiftyNine.Conservation.VostokovShapeAudit59.statewiseRepresentative_readback
#guard_depends_on
  Fermat.FiftyNine.Conservation.IwasawaLocalization59.descend_eq_oldReading,
  Fermat.FiftyNine.Conservation.VostokovShapeAudit59.transverseRepresentative_readback
#guard_depends_on
  Fermat.FiftyNine.Conservation.IwasawaLocalization59.descend_eq_oldReading,
  Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827.toKummerClassAt_oldReflectedToQRelaxed827
#guard_depends_on
  Fermat.FiftyNine.Conservation.IwasawaLocalization59.descend_eq_oldReading,
  Fermat.Conservation.IwasawaTracePairing.Reduction.representative_eq_reading

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
#guard_standard_axioms_prefix Fermat.Conservation.SelmerEigenspace
#guard_standard_axioms_prefix Fermat.Conservation.TatePairing
#guard_standard_axioms_prefix Fermat.Conservation.TamePlacePairing
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.TateBridge
#guard_standard_axioms_prefix Fermat.Conservation.FocusConormal
#guard_standard_axioms_prefix Fermat.Conservation.SteeringFiber
#guard_standard_axioms_prefix Fermat.Conservation.ExteriorTransfer
#guard_standard_axioms_prefix Fermat.Conservation.ReadoutLedger
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.DetectorWitness827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.GaugeSteering827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.SplitPrimeFourier827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.FourierPairingProjection827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.PrimalOrbitResidue827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.OrbitPlace827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.LocalReduction827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.CyclotomicTameContext59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.FullOrbitReciprocity827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.RawOrbitReciprocity827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.ExplicitTameOrbitNonvanishing827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.ActualTameLedger827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.ActualTameLedgerNonvanishing827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.ConjugationFixedClassDivisibility59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.ConjugationFixedPrincipalDivisor59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.ConjugatePairSource827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.ConjugatePlaceOrbit827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.CanonicalConjugatePairIncidence827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.CanonicalConjugatePairNormalizedEndpoint59
#guard_standard_axioms_prefix Fermat.Conservation.TameSymbol.Context
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.CanonicalTameLedger827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.CanonicalGlobalReciprocity827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.CanonicalConjugatePairGlobalLedger827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.PointedTateIncidence
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.AlgebraicPointedIncidence827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.TransversalityVerdict827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.UlamTypeFreeze
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.UlamReadout827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.ArtinHasseInventory
#guard_standard_axioms_prefix Fermat.Conservation.WildKummerPairing
#guard_standard_axioms_prefix Fermat.Conservation.IwasawaTracePairing
#guard_standard_axioms_prefix Fermat.Conservation.KummerTateCup
#guard_standard_axioms_prefix Fermat.Conservation.KummerTateReadout
#guard_standard_axioms_prefix Fermat.Conservation.LocalKummerH1
#guard_standard_axioms_prefix Fermat.Conservation.KummerOrientation
#guard_standard_axioms_prefix Fermat.Conservation.DiscreteKummerTatePairing
#guard_standard_axioms_prefix Fermat.Conservation.KummerCupSpanReadout
#guard_standard_axioms_prefix Fermat.Conservation.LocalKummerTransport
#guard_standard_axioms_prefix Fermat.Conservation.CohomologicalKummerPairing
#guard_standard_axioms_prefix Fermat.Conservation.AlbertDescentDatum59
#guard_standard_axioms_prefix Fermat.Conservation.AlbertExtension59
#guard_standard_axioms_prefix Fermat.Conservation.AlbertOrder59
#guard_standard_axioms_prefix Fermat.Conservation.AlbertGalois59
#guard_standard_axioms_prefix Fermat.Conservation.ContinuousCyclicQuotient
#guard_standard_axioms_prefix Fermat.Conservation.AlbertCyclicQuotient59
#guard_standard_axioms_prefix Fermat.Conservation.AlbertCyclicCompatibility59
#guard_standard_axioms_prefix Fermat.Conservation.AlbertCyclicConverse59
#guard_standard_axioms_prefix Fermat.Conservation.OrientedKummerRepresentative59
#guard_standard_axioms_prefix Fermat.Conservation.KummerCharacterComparison59
#guard_standard_axioms_prefix Fermat.Conservation.ConcreteTwistedLiftCupBridge59
#guard_standard_axioms_prefix Fermat.Conservation.IntegratedTwistedKummerCup59
#guard_standard_axioms_prefix Fermat.Conservation.CompatibleKummerLift59
#guard_standard_axioms_prefix Fermat.Conservation.CyclicLiftNaturality59
#guard_standard_axioms_prefix Fermat.Conservation.ContinuousCarryH2LiftCriterion59
#guard_standard_axioms_prefix Fermat.Conservation.ContinuousCyclicH2Readout59
#guard_standard_axioms_prefix Fermat.Conservation.ContinuousCyclicH2Equiv59
#guard_standard_axioms_prefix Fermat.Conservation.ContinuousH2Pullback59
#guard_standard_axioms_prefix Fermat.Conservation.ContinuousH2PullbackFunctorial59
#guard_standard_axioms_prefix Fermat.Conservation.PrimeCyclicH2
#guard_standard_axioms_prefix Fermat.Conservation.PrimeCyclicH2At59
#guard_standard_axioms_prefix Fermat.Conservation.PrimeCyclicExtension
#guard_standard_axioms_prefix Fermat.Conservation.PrimeContinuousHomogeneousPullback
#guard_standard_axioms_prefix Fermat.Conservation.PrimeContinuousCarryLift
#guard_standard_axioms_prefix Fermat.Conservation.PrimeContinuousCarryLiftAt59
#guard_standard_axioms_prefix Fermat.Conservation.PrimeKummerCyclicQuotient
#guard_standard_axioms_prefix Fermat.Conservation.PrimeKummerCyclicQuotientAt59
#guard_standard_axioms_prefix Fermat.Conservation.PrimeKummerCarryLiftCriterion
#guard_standard_axioms_prefix Fermat.Conservation.PrimeKummerCharacterComparison
#guard_standard_axioms_prefix Fermat.Conservation.PrimeKummerCharacterComparisonAt59
#guard_standard_axioms_prefix Fermat.Conservation.PrimeOrientedCarryH2Class
#guard_standard_axioms_prefix Fermat.Conservation.PrimeOrientedCarryH2ClassAt59
#guard_standard_axioms_prefix Fermat.Conservation.PrimeConcreteTwistedLiftCupBridge
#guard_standard_axioms_prefix Fermat.Conservation.PrimeIntegratedTwistedKummerCup
#guard_standard_axioms_prefix Fermat.Conservation.PrimeCompatibleKummerLift
#guard_standard_axioms_prefix Fermat.Conservation.PrimeCompatibleKummerLiftAt59
#guard_standard_axioms_prefix Fermat.Conservation.PrimeKummerNormLiftH2Criterion
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.PrimeKummerNormLiftH2CriterionAt59
#guard_standard_axioms_prefix Fermat.Conservation.PrimeAlbertDescentDatum
#guard_standard_axioms_prefix Fermat.Conservation.PrimeAlbertExtension
#guard_standard_axioms_prefix Fermat.Conservation.PrimeAlbertOrder
#guard_standard_axioms_prefix Fermat.Conservation.PrimeAlbertGalois
#guard_standard_axioms_prefix Fermat.Conservation.PrimeAlbertCyclicQuotient
#guard_standard_axioms_prefix Fermat.Conservation.PrimeAlbertCyclicCompatibility
#guard_standard_axioms_prefix Fermat.Conservation.PrimeAlbertCyclicConverse
#guard_standard_axioms_prefix Fermat.Conservation.PrimeAlbertCyclicConverseAt59
#guard_standard_axioms_prefix Fermat.Conservation.KummerOnePlusRootNormPrime
#guard_standard_axioms_prefix Fermat.Conservation.KummerOnePlusRootNorm59
#guard_standard_axioms_prefix Fermat.Conservation.PrimeKummerExplicitNorm
#guard_standard_axioms_prefix Fermat.Conservation.PrimeKummerTrace
#guard_standard_axioms_prefix Fermat.Conservation.PrimeTriangularUnitFactorization
#guard_standard_axioms_prefix Fermat.Conservation.PrimeTriangularNormBounds
#guard_standard_axioms_prefix Fermat.Conservation.PrimeTriangularValuationDepth
#guard_standard_axioms_prefix Fermat.Conservation.NonarchimedeanProductRemainder
#guard_standard_axioms_prefix Fermat.Conservation.SpectralNormProductRemainder
#guard_standard_axioms_prefix Fermat.Conservation.PolynomialSpectralNormBound
#guard_standard_axioms_prefix Fermat.Conservation.PrimeTriangularSpectralContraction
#guard_standard_axioms_prefix Fermat.Conservation.PrimeTriangularExplicitNorm
#guard_standard_axioms_prefix Fermat.Conservation.ValuationProductDominant
#guard_standard_axioms_prefix Fermat.Conservation.PrimeTriangularSpectralAbsorption
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.BareLambdaNorm59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.CriticalUnitQuotient59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.CriticalUnitPowerSurjectivity59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.ExplicitNormResidue59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.EisensteinIntegrality59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.TriangularSpectralDepth59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.TriangularNormSeparation59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.TriangularResidualNormalization59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.TriangularResidualStep59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.TriangularTerminalResidual59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.FiveStepResidual59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.InitialIntegralDecomposition59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.PowerU1Reflection59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.NormImageBridge59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.ExactNormIntersection59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.NormImageConsequences59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.Unit60KummerNormObstruction59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.TwistedLambdaCupUnitReduction59
#guard_standard_axioms_prefix Fermat.Conservation.ContinuousH2Nonboundary
#guard_standard_axioms_prefix Fermat.Conservation.FiniteCyclicH2Generator59
#guard_standard_axioms_prefix Fermat.Conservation.DiscreteToContinuousH2
#guard_standard_axioms_prefix Fermat.Conservation.CyclicCarryH2Class59
#guard_standard_axioms_prefix Fermat.Conservation.ContinuousHomogeneousPullback59
#guard_standard_axioms_prefix Fermat.Conservation.ContinuousCarryLiftObstruction59
#guard_standard_axioms_prefix Fermat.Conservation.ContinuousCyclicQuotient59
#guard_standard_axioms_prefix Fermat.Conservation.KummerCyclicQuotient59
#guard_standard_axioms_prefix Fermat.Conservation.OrientedCarryH2Class59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.CyclotomicLocalizationEquivariance827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.TrivialReflectedAttestationPrimeLift827
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.LocalCompletion59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.VostokovLocalization59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.VostokovShapeAudit59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.IwasawaLocalization59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.KummerTateLocalization59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.NormalizedContinuousWildLocalization59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.StatewiseTwistedLambdaBridge59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.TwistedLambdaCarryH2Class59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.TwistedLambdaKummerCupComparison59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.TwistedLambdaKummerLiftCriterion59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.TwistedLambdaKummerNormCriterion59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.TwistedLambdaH2Inflation59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.TwistedLambdaAlbertCriterion59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.TwistedArtinHasse59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.LocalCyclotomicTrace59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.TwistedArtinHasseLocalTrace59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.TwistedFiniteLogLocalTrace59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.AdicCompleteValuedInteger59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.CompletedLogTail59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.LocalIntegralTrace59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.CompletedLogTraceNonzero59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.CompletedLogResidue59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.CompletedLogPowerObstruction59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.CompletedLogLocalPowerObstruction59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.TwistedLambdaNormalizationSign59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.TwistedLambdaNormalizedEndpoint59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.TwistUnitKummerObstruction59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.KummerCupSpanLocalization59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59
#guard_standard_axioms_prefix Fermat.FiftyNine.Conservation.TransformerProbe

#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.GaugeSteering827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.SplitPrimeFourier827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.FourierPairingProjection827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.PrimalOrbitResidue827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.OrbitPlace827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.LocalReduction827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.CyclotomicTameContext59
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.FullOrbitReciprocity827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.RawOrbitReciprocity827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.ExplicitTameOrbitNonvanishing827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.ActualTameLedger827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.ActualTameLedgerNonvanishing827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.ConjugationFixedClassDivisibility59
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.ConjugationFixedPrincipalDivisor59
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.ConjugatePairSource827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.ConjugatePlaceOrbit827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.CanonicalConjugatePairIncidence827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.CanonicalConjugatePairNormalizedEndpoint59
#audit_no_product_equiv_types_prefix Fermat.Conservation.TameSymbol.Context
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.CanonicalTameLedger827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.CanonicalGlobalReciprocity827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.CanonicalConjugatePairGlobalLedger827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.PointedTateIncidence
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.AlgebraicPointedIncidence827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.TransversalityVerdict827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.UlamTypeFreeze
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.UlamReadout827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.ArtinHasseInventory
#audit_no_product_equiv_types_prefix Fermat.Conservation.WildKummerPairing
#audit_no_product_equiv_types_prefix Fermat.Conservation.IwasawaTracePairing
/- `KummerTateCup` is intentionally outside this exact-sequence guard: its
degree-two inhomogeneous cochains are functions on `G × G`, and its canonical
trivial-coefficient conversion genuinely uses Mathlib's `H¹` equivalence. -/
#audit_no_product_equiv_types_prefix Fermat.Conservation.KummerTateReadout
#audit_no_product_equiv_types_prefix Fermat.Conservation.LocalKummerH1
#audit_no_product_equiv_types_prefix Fermat.Conservation.KummerOrientation
#audit_no_product_equiv_types_prefix Fermat.Conservation.DiscreteKummerTatePairing
#audit_no_product_equiv_types_prefix Fermat.Conservation.KummerCupSpanReadout
#audit_no_product_equiv_types_prefix Fermat.Conservation.LocalKummerTransport
#audit_no_product_equiv_types_prefix Fermat.Conservation.CohomologicalKummerPairing
#audit_no_product_equiv_types_prefix Fermat.Conservation.TamePlacePairing
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.CyclotomicLocalizationEquivariance827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.TrivialReflectedAttestationPrimeLift827
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.LocalCompletion59
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.VostokovLocalization59
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.VostokovShapeAudit59
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.IwasawaLocalization59
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.KummerTateLocalization59
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.ExactNormIntersection59
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.NormalizedContinuousWildLocalization59
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.StatewiseTwistedLambdaBridge59
#audit_no_product_equiv_types_prefix Fermat.FiftyNine.Conservation.KummerCupSpanLocalization59
#audit_no_product_equiv_types_prefix Fermat.Conservation.FocusConormal
#audit_no_product_equiv_types_prefix Fermat.Conservation.SteeringFiber
#audit_no_product_equiv_types_prefix Fermat.Conservation.ExteriorTransfer
#audit_no_product_equiv_types_prefix Fermat.Conservation.ReadoutLedger

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
