# LEDGER-LITERAL boundary map

This map is the deliverable for `LEDGER-LITERAL-TASK.md`.  It maps the
current proof boundary; it does not attempt Lemma I / relation (7a), a
stock-credit transformer, or an exponent-59 endpoint.  Existing obstruction
probes are evidence for the boundary and are not replacements for the
missing constructions.

## Mechanical rule

All classifications are relative to a named identity.  The command

```lean
#guard_depends_on source, identity
```

walks the transitive constant graph of `source`'s elaborated implementation
value.  Declaration types are ignored.  Thus an identity in a theorem's
statement, a structure field, a comment, or an unused hypothesis is not
enough.

- **LITERAL**: the guard succeeds; the named identity is load-bearing in the
  implementation value.
- **DECORATIVE**: a correctly typed identity is already present in the same
  proof cone, but the implementation bypasses it and the guard fails.
- **ABSENT**: the cone has no accounting carrier or adapter on which the
  requested identity can be stated.  Importing the generic identity beside
  the theorem would not repair this; a new invariant is required first.

An identity lemma is an audit anchor, not a consumer of itself.  The global
classification below is controlling.  Native/local dependency is reported
separately because it identifies useful implementation that can feed a
future adapter, but it does not upgrade an **ABSENT** global result.

The three campaign anchors are:

- global accounting: `Fermat.Conservation.Ledger.conservation_identity`,
  namely `stock + credit + converted = total`;
- Bernoulli channels:
  `Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.depth_conservation`,
  namely `depth = min depth 2 + surplus` together with the stored
  lift/coupling decomposition;
- repayment layers:
  `Fermat.Conservation.Credit.Repayment.repay_layer_conservation`, namely
  `source.residual = residual.residual ^ p` and
  `residual.totalLayers + 1 = source.totalLayers`.

The generic carrier itself is genuinely literal:
`Fermat.Conservation.Ledger.vacuum_conservation`,
`Fermat.Conservation.Ledger.repay_conservation`, and
`Fermat.Conservation.Ledger.repayNat_conservation` all depend on
`Fermat.Conservation.Ledger.conservation_identity`.  What is absent below is
not the formula; it is the map from each native cone into this carrier.

## Stock receipt N1--N7

`Fermat.FiftyNine.Conservation.stockSpineReceipt` is one proof with seven
fields, so the local column audits the declaration selected for each field.
Only its N2 and N6 paths depend on a native theorem named as a ledger.  The
receipt never constructs `Fermat.Conservation.Ledger`, so every rung remains
globally **ABSENT**.

| Rung / receipt field | Selected declaration | Global status | Native/local dependency | Exact missing global invariant |
| --- | --- | --- | --- | --- |
| N1 `n1_vacuum` | `Fermat.One.coupling_empty` | **ABSENT** | **DECORATIVE** with respect to `Fermat.One.charge_ledger`; the selected proof uses the independently simplified coupling | An adapter `Ledger ℕ` with `stock = charge u + charge v`, `credit = coupling u v`, `converted = 0`, and `total = charge (u + v)`, plus a theorem deriving the empty credit channel from `Ledger.conservation_identity`. |
| N2 `n2_balance` | `Fermat.Two.charge_ledger` | **ABSENT** | The `stockSpineReceipt` consumer is **LITERAL** with respect to the selected anchor `Fermat.Two.charge_ledger`. | An additive accounting adapter into one carrier with stock `charge u + charge v`, credit `2 * coupling u v`, converted zero, and total `charge (u + v)`.  The native real equality is present, but no `Ledger ℝ` state exposes it through the global identity. |
| N3 `n3_drain` | `Fermat.Three.Conservation.drainCharge_pred_lt` | **ABSENT** | **DECORATIVE** with respect to `Fermat.Three.Conservation.ledger_identity`; the drain route uses norm multiplicativity and powers instead | A state-level accounting map connecting the cubic factor `(a + b) * charge (ofCoeffs a b)` to a positive ramified amount moved from stock/credit into converted, with unchanged total.  In particular the multiplicity drop must be the stock projection of that transfer, not an unrelated `3 ^ m < 3 ^ n`. |
| N4 `n4_positive` | `Fermat.Four.Conservation.PrimitiveSolution.stateCharge_pos` | **ABSENT** | **DECORATIVE** with respect to `Fermat.Two.charge_ledger`; positivity bypasses the balance equation | A ledger-valued primitive state and a descent equality `S.stateCharge = next.stateCharge + spent` with `0 < spent`, together with before/after credit and converted columns whose changes account for exactly `spent`.  The current proof has positivity and a strict comparison but no conserved transfer. |
| N5 `n5_gauge` | `Fermat.Five.Conservation.charge_gauge_invariant` | **ABSENT** | **DECORATIVE** with respect to `Fermat.Five.Conservation.quintic_ledger`; the gauge proof uses norm multiplicativity and unit norm | A gauge-equivariant adapter from the golden factor state to `Ledger α`: unit multiplication must preserve all four columns, and each descent must give an explicit credit-to-converted amount while total stays fixed. |
| N6 `n6_fold` | `Fermat.Six.Conservation.sixth_ledger` | **ABSENT** | The `stockSpineReceipt` consumer is **LITERAL** with respect to the selected anchor `Fermat.Six.Conservation.sixth_ledger`. | An adapter carrying the factor `(a ^ 2 + b ^ 2) * charge (cofactorElement a b)` as accounted stock/credit and `a ^ 6 + b ^ 6` as total, followed by a successor law that transports this same ledger and records the positive converted drain. |
| N7 `n7_lattice` | `Fermat.Seven.Conservation.gauge_decomposition` | **ABSENT** | **DECORATIVE** with respect to `Fermat.Seven.Conservation.septic_ledger`; coordinate decomposition does not use the septic factor equation | A full-gauge ledger morphism and a ramified-drain equation: gauge coordinates must preserve stock, credit, converted, and total, while one drain step moves a quantified amount into converted and leaves total unchanged. |

### Main stock theorem paths

The receipt is deliberately not used as a proxy for the complete cones.
The following are the main downstream paths checked against each cone's
native ledger anchor.  Their global status is still **ABSENT** for the
adapter reason in the preceding table.

| Cone | Native status and exact declarations | Boundary for every non-literal path |
| --- | --- | --- |
| N1 | `Fermat.One.solvable`, `Fermat.One.always_balances`, and `Fermat.One.not_holdsAt_one` are **DECORATIVE** with respect to `Fermat.One.charge_ledger`. | The solvability/endpoint proof must consume the N1 `Ledger ℕ` adapter described above and project balance from `conservation_identity`, rather than normalize the power equation independently. |
| N2 | `Fermat.Two.pythagoras`, `Fermat.Two.emptyCoupling_of_additive`, and `Fermat.Two.pythagoras_conserved` are locally **LITERAL** through `Fermat.Two.charge_ledger`.  `Fermat.Two.charge_conserved` is **DECORATIVE** with respect to that ledger. | For `charge_conserved`, the missing invariant is functoriality of the N2 accounting adapter under a linear isometry, column by column; equality of the scalar charge alone does not conserve credit or converted. |
| N3 | `Fermat.Three.Conservation.drainCharge_eq`, `Fermat.Three.Conservation.drainCharge_pred_lt`, `Fermat.Three.Conservation.Euler.GeneralizedStatement.euler_descent_charge_lt`, and `Fermat.Three.holdsAt_three_conservation` are **DECORATIVE** with respect to `Fermat.Three.Conservation.ledger_identity`. | The missing invariant is the state-linked cubic ledger transfer described above: the successor's lower multiplicity and the factor ledger must be two projections of one conserved before/after state. |
| N4 | `Fermat.Four.Conservation.pythagorean_balance_engine` is a useful native balance theorem and is load-bearing in `Fermat.Four.Conservation.PrimitiveSolution.charged_descent`, but both are **DECORATIVE** with respect to `Fermat.Two.charge_ledger`; `Fermat.Four.Conservation.not_stronger_solution_conservation` is likewise decorative. | A typed map from the integer Pythagorean state into the N2 balance ledger, followed by the exact positive debit/conversion equation for the smaller hypotenuse, is missing.  Merely calling the independently proved balance engine does not identify the conserved columns. |
| N5 | `Fermat.Five.Conservation.fermatEquation_five_ledger`, `Fermat.Five.Conservation.PrimitiveFifthSolution.equation`, `Fermat.Five.Conservation.not_five_dvd_c_seed`, `Fermat.Five.Conservation.five_dvd_c_seed`, `Fermat.Five.Conservation.not_five_dvd_c_impossible`, `Fermat.Five.Conservation.five_dvd_c_impossible`, and `Fermat.Five.holdsAt_five_conservation` are locally **LITERAL** through `Fermat.Five.Conservation.quintic_ledger`.  `Fermat.Five.Conservation.not_five_dvd_c_charged_descent`, `Fermat.Five.Conservation.five_dvd_c_charged_descent`, and the `ChargedState`, `NotFiveDvdCState`, and `FiveDvdCState` gauge laws are **DECORATIVE** with respect to it. | Each decorative state transition needs a gauge-equivariant before/after ledger with an exact positive converted increment and conserved total.  The outer endpoint happens to retain the seed ledger, but the iterative transition itself currently carries only a strict scalar charge inequality. |
| N6 | `Fermat.Six.Conservation.PrimitiveSolution.native_ledger` is locally **LITERAL** through `Fermat.Six.Conservation.sixth_ledger`.  `Fermat.Six.Conservation.pythagorean_cube_balance`, `Fermat.Six.Conservation.PrimitiveSolution.cube_balance`, `Fermat.Six.Conservation.exists_orientedStateCharge_lt`, and `Fermat.Six.Conservation.PrimitiveSolution.impossible_conservation` are **DECORATIVE** with respect to the sixth ledger. | The oriented successor must retain the native factor decomposition and exhibit an amount converted during the multiplicity drop.  The current transition reconstructs only a strict power-of-three comparison. |
| N7 | `Fermat.Seven.Conservation.Reconstruction.Lebesgue.seven_dvd_t_branch_impossible`, `Fermat.Seven.Conservation.Reconstruction.Lebesgue.not_seven_dvd_t_branch_impossible`, `Fermat.Seven.Conservation.Reconstruction.Lebesgue.ternaryOnlyTrivial_lebesgue`, `Fermat.Seven.Conservation.Reconstruction.Lebesgue.holdsAt_seven_lebesgue`, and `Fermat.Seven.holdsAt_seven_conservation` are locally **LITERAL** through `Fermat.Seven.Conservation.septic_ledger`.  The gauge laws, `Fermat.Seven.Conservation.drainCharge_eq`, `Fermat.Seven.Conservation.drainCharge_step`, `Fermat.Seven.Conservation.Reconstruction.Lebesgue.ChargedState.impossible_conservation`, and `Fermat.Seven.Conservation.Reconstruction.Lebesgue.SevenDvdTBranchState.impossible_conservation` are **DECORATIVE** with respect to it. | The decorative inner drains need a septic-ledger-valued successor with a full-gauge column-preservation law and an exact ramified amount transferred into converted.  The outer branch wrappers rewrite through the septic identity, but the generic charged-state floor does not. |

## Credit rungs C1--C3

| Rung / declarations | Global status | Native/channel/layer status | Exact missing invariant |
| --- | --- | --- | --- |
| C1: `Fermat.Conservation.Credit.kummer_credit_vacuum` | **ABSENT** | Locally **LITERAL** through `Fermat.Conservation.Credit.generated_eq_bot_of_no_generator`. | An additive accounting map from the set-valued matrix `Fermat.Conservation.Credit.Ledger Node Generator` to a common `α`, with `account ⊥ = 0` and `account (merge L R) = account L + account R`.  Only then can C1 construct `Fermat.Conservation.Ledger.vacuum` or another zero-credit global state. |
| C2: `Fermat.Conservation.Credit.Cycle.capacityIndex_eq_relIndex`, `Fermat.Conservation.Credit.Cycle.CapacityData.capacity_eq_relIndex`, `Fermat.Conservation.Credit.Cycle.CapacityData.capacity_pos`, `Fermat.Conservation.Credit.Cycle.CapacityCertificate.sound`, and `Fermat.Conservation.Credit.Cycle.IndexCertificate.sound` | **ABSENT** | **ABSENT** as conservation: these are finite-index/capacity facts, not an accounted transfer. | A credit-length morphism from `Fermat.Conservation.Credit.Cycle.generatedSubledger`/relative index to the global carrier, and a spending law `credit_before = credit_after + spent`.  Finiteness and coprimality do not say which conserved column contains the capacity. |
| Legacy C3: `Fermat.Conservation.Credit.Repayment.repay_of_deep_generated_cycle` | **ABSENT** | **DECORATIVE** with respect to `repay_layer_conservation`; it returns only `IsRepaid p u`. | A constructor of `C G closed funded 1`, an explicit `C ... 0` residual, and the equality `u = residual ^ p` paired with `0 + 1 = 1`.  The generic d=1 adapter now supplies this route, but the old generic theorem itself remains a verdict theorem. |
| Graded C3: `Fermat.Conservation.Credit.Repayment.repay_totalLayers` and `nonempty_repay_one_iff` | **ABSENT** | **LITERAL** through `repay_layer_conservation`. | To become globally literal, grades need an accounting map with `accountCredit state = state.totalLayers` (or an explicitly justified weighted version) and a theorem that one layer decreases credit by one and increases converted by one while stock and total are fixed. |
| Higher graded C3: `Fermat.Conservation.Credit.Repayment.LayerTransport` and `Fermat.Conservation.Credit.Repayment.Repay.ofLayerTransport` | **ABSENT** globally | The interface shape is **LITERAL** through `Fermat.Conservation.Credit.Repayment.LayerConservation`; the adapter is literal through both the interface and layer equation.  A concrete inhabitant is **ABSENT**. | For every `d > 1` and funded source, produce `residual : C ... (d - 1)` with exactly `source.residual = residual.residual ^ p` and `residual.totalLayers + 1 = source.totalLayers`.  No conductor-specific theorem currently supplies the depth-`(d+1)p` congruence funding that chosen residual. |

The d=1 statement is no longer a boundary at 59:
`Fermat.FiftyNine.Conservation.Instance.nonempty_repayOne_iff_deep_repayment59`
and the legacy-shaped
`Fermat.FiftyNine.Conservation.Instance.repayment_of_capacity_and_flow`
are **LITERAL** through `repay_layer_conservation`.  They remain globally
**ABSENT** only in the separate sense that no layer-to-three-column
accounting adapter has yet been supplied.

## Flow and Bernoulli channels

| Path | Global status | Channel/local status | Exact missing invariant for non-global rows |
| --- | --- | --- | --- |
| Additive exponent flow: `Fermat.Conservation.Credit.Flow.GeneratorOrbit.product_conservation` and `sum_conservation` | **ABSENT** | These are native identity anchors.  The high-flow forcing chain is **DECORATIVE** with respect to them: it does not route through either theorem. | An additive `accountFlow` from coefficient vectors to the common carrier, with product/sum flow identified as credit and the vanished/spent component identified as converted.  Its conservation theorem must connect these Finsupp equalities to the global total. |
| Non-lossy Bernoulli compatibility: `Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.depth_eq_min_two_add_depth_sub_two` and `Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.cubeFree_of_surplus_eq_zero` | **ABSENT** globally | **LITERAL** through `Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.depth_conservation`. | A bridge assigning retained depth to the global credit column and the capped/used part to converted, proving the same total depth before and after the view.  The channel itself is already non-lossy. |
| Generic real/non-real forcing: `Fermat.Conservation.Credit.Flow.FlowCertificate.eigenvalue_cubeFree`, `Fermat.Conservation.Credit.RealFlow.FlowCertificate.eigenvalue_cubeFree`, `Fermat.Conservation.Credit.RealFlow.FlowCertificate.depthAtMostTwo`, and `Fermat.Conservation.Credit.RealFlow.DepthTwoCertificate.atMostTwo` | **ABSENT** globally | **LITERAL** through channel conservation. | The same flow accounting bridge is missing; cube-freeness is now correctly a projection of retained channels, but it has not been identified with stock/credit conversion. |
| Selected forcing: `Fermat.FiftyNine.Conservation.Instance.BernoulliCertificate.highBernoulliNumerator_cubeFree`, `Fermat.FiftyNine.Conservation.Instance.noBernoulliCubeObstruction59`, `Fermat.FiftyNine.Conservation.Instance.deepExponentForcing_of_flow`, and `Fermat.FiftyNine.Conservation.Instance.deepExponentForcing_on_exponentCycle_of_flow` | **ABSENT** globally | **LITERAL** through channel conservation. | A conductor-59 specialization of `accountFlow` must identify the table's `depth`, `couplingChannel`, and `surplus` with the credit and converted amounts consumed by repayment. |
| Selected exact-depth data: `Fermat.FiftyNine.Conservation.DepthCertificate.depthTwoCertificate` | **ABSENT** globally | Structurally non-lossy but mechanically **DECORATIVE** with respect to `Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.depth_conservation`: the definition stores the channels and square-attained witness without calling the identity.  Its consumer `Fermat.Conservation.Credit.RealFlow.DepthTwoCertificate.atMostTwo` is **LITERAL**. | The square-attained row must be mapped to one funded repayment layer in the global carrier; currently it certifies arithmetic depth but not an accounted transfer. |

The 59 table itself is non-lossy:
`Fermat.FiftyNine.Conservation.Instance.BernoulliCertificate.channelCertificate`
stores `depth`, `liftChannel`, `couplingChannel`, and `surplus`, while
`channelCertificate_surplus_eq_zero` is the computed fact that the retained
surplus happens to vanish.  The old Boolean is a derived view, not a storage
boundary.

## Gauge quotient

| Declarations | Global status | Local status | Exact missing invariant |
| --- | --- | --- | --- |
| Generic `PrimeData.quotientLedger_eq_bot`, `quotientCharge_quotientState`, and `quotient_vacuum_and_charge_eq` in `Fermat.Conservation.Credit.GaugeQuotient` | **ABSENT** | Locally **LITERAL** through the C1 vacuum identity and the named quotient charge equality. | An accounting morphism for the source and quotient set-valued ledgers, and an equality `accountCredit source = accountCredit quotient + convertedAmount`, in the same carrier as stock charge.  Bottom residual credit plus unchanged scalar stock charge does not record where the repaid credit went. |
| Selected `Fermat.FiftyNine.Conservation.GaugeQuotient.debitLedger_quotient_eq_bot` and `quotient_vacuum_and_charge_eq` | **ABSENT** | Locally **LITERAL** through the generic quotient vacuum and charge facts. | The conductor-59 debit ledger needs the same morphism, with the selected repayment root's amount explicitly placed in converted and the N7 norm charge mapped to stock. |

Thus the quotient proves two true projections—vacuum residual credit and
equal stock charge—but no theorem yet proves their joint
`stock + credit + converted = total` balance.

## Fold and allocated class ledger

| Declarations | Global status | Native/local status | Exact missing invariant |
| --- | --- | --- | --- |
| `Fermat.Conservation.Credit.Fold.relativeNormFold_apply_of_conjugation` | **ABSENT** | **LITERAL** through `relativeNormFold_apply`. | An additive map from every class-ledger entry to the common carrier, preserving transpose and proving `account (relativeNormFold L) = account L + account (conjugateTranspose L)` as a global channel equation. |
| `relativeNormFold_class_eq_zero_of_coprime_card` and `conjugate_class_fold_eq_zero_of_coprime_card` | **ABSENT** | **DECORATIVE** with respect to the matrix identity: their proofs use ideal relative norm/principalization directly. | A channelwise class-accounting theorem connecting the ideal relative norm to the matrix fold, and identifying the killed class amount as converted rather than merely concluding class zero. |
| `Fermat.Conservation.Credit.Fold.odd_torsion_netting` and the `Fermat.Conservation.KummerDrain.factorPrincipalizationPermit_*` consumers | **ABSENT** | **DECORATIVE** with respect to a conserved fold: (7a), (7d), and torsion are consumed as hypotheses; their occurrence in types does not count. | A state-produced allocated balance whose debit and receivable class channels add to the same conserved total, with principalized/netted class explicitly transferred to converted. |
| `Fermat.FiftyNine.Conservation.Fold.vandiverSevenD_of_relativeNormFold`, `vandiverSevenD_of_conjugationTranspose`, and `factorPrincipalizationPermit_of_sevenA_and_conjugationTranspose` | **ABSENT** | The relative-norm equality is mathematically active, but the selected proof is **DECORATIVE** with respect to `relativeNormFold_apply`; (7a) remains an input. | A conductor-59 class-accounting adapter plus the state-linked (7a) producer below.  Conjugation gives the two-channel (7d) fold, but no proof allocates the weighted (7a) channel or connects the netted amount to stock/converted. |

## N59 instance summary

| Instance surface | Controlling status | Reason / exact remaining invariant |
| --- | --- | --- |
| `Fermat.FiftyNine.Conservation.stockSpineReceipt` and `Fermat.FiftyNine.Conservation.Instance.regularClosure59` | Global **ABSENT**; mixed native receipt, locally literal only through N2 and N6 ledger anchors (C1 vacuum is also locally literal). | Construct one common-carrier adapter for all selected stock and matrix-credit objects.  `Fermat.FiftyNine.Conservation.Instance.RegularClosure59` is presently a conjunction, not a `Ledger` whose zero credit and stock columns share a total. |
| `Fermat.FiftyNine.Conservation.Instance.BernoulliCertificate.highBernoulliNumerator_cubeFree`, `Fermat.FiftyNine.Conservation.Instance.noBernoulliCubeObstruction59`, and the selected deep-flow forcing | Channel **LITERAL**, global **ABSENT**. | Supply the depth-to-credit/converted accounting bridge; no new numerical certificate is missing. |
| `Fermat.FiftyNine.Conservation.Instance.nonempty_repayOne_iff_deep_repayment59` and `Fermat.FiftyNine.Conservation.Instance.repayment_of_capacity_and_flow` | Layer **LITERAL**, global **ABSENT**. | Supply the layer-to-credit/converted accounting bridge.  The one-layer operator and its explicit grade-zero residual now exist. |
| `Fermat.FiftyNine.Conservation.GaugeQuotient.quotient_vacuum_and_charge_eq` | Global **ABSENT**, locally literal. | Prove the source-credit decomposition and converted increment in the same carrier as the preserved stock charge. |
| `Fermat.FiftyNine.Conservation.Fold.factorPrincipalizationPermit_of_sevenA_and_conjugationTranspose` | Global **ABSENT**. | Produce statewise (7a), then account the class fold/netting as conversion. |
| `Fermat.FiftyNine.Conservation.FermatState.StockCreditTransformer` | **ABSENT**. | Construct the state-linked global ledger morphism and the strict stock-drain equality described below. |

No row in this table claims or implies
`Fermat.FiftyNine.holdsAt_fiftyNine_conservation`; that declaration remains
absent by scope.

## Named open seams

### 1. Lemma I / relation (7a)

The exact missing selected proposition is

```lean
(allocatedPair hζ S hz).ledger.VandiverSevenA 0 1
```

that is, the state-linked class equation
`rootClass 0 + 58 • rootClass 1 = 0`.  The consumers
`Fermat.FiftyNine.Conservation.StateFactorConjugation.StateLinkedIdealPair.factorPrincipalizationPermit_of_sevenA`
and
`Fermat.FiftyNine.Conservation.Fold.factorPrincipalizationPermit_of_sevenA_and_conjugationTranspose`
are present, while the producer is **ABSENT**.

The missing invariant is not generic group algebra.  It is an allocation
law from the actual Fermat factor state to the debit and weighted
receivable class channels, proving their conserved total is zero and
mapping the resulting principalized amount into the converted column.
Neither root-class `59`-torsion nor the already-derived conjugation fold
(7d) forces this weighted equation.  This is precisely the statewise
Takagi--Furtwängler reflection step traditionally called Lemma I, and it is
outside this session.

### 2. Stock-credit transformer successor

The exact demanded interface is
`Fermat.FiftyNine.Conservation.FermatState.StockCreditTransformer`, whose
pointwise output is
`Fermat.FiftyNine.Conservation.FermatState.StrictSuccessor S`.
`Fermat.FiftyNine.Conservation.Instance.repayment_of_capacity_and_flow hζ hdeep`
returns `Fermat.Conservation.Credit.Repayment.IsRepaid 59 u`, not a successor
solution, and
`Fermat.FiftyNine.Conservation.CyclotomicFiftyNine.drainCharge_step hζ n`
compares ramified norm charges,
not `next.charge < S.charge`.

The missing invariant is a state-linked before/after `Ledger ℕ` morphism.
It must construct an actual `next : PrimitiveSecondCaseSolution`, a positive
`spentStock`, and equations

```text
S.charge = next.charge + spentStock
before.stock + before.credit + before.converted = before.total
after.stock  + after.credit  + after.converted  = after.total
before.total = after.total
```

with `before.stock = S.charge`, `after.stock = next.charge`, and the exact
credit decrease plus `spentStock` accounted in the increase of converted.
Without these equations, repayment and ramified drain are unrelated scalar
facts and cannot produce the strict successor.

### 3. Higher layer transport

`Fermat.Conservation.Credit.Repayment.LayerTransport` is a named,
mechanically guarded interface, but there is no concrete inhabitant for
`Fermat.FiftyNine.Conservation.Instance.RepaymentFunded59`.  The missing
producer must return, for every
`d > 1` and every source state, a funded residual with the full equation

```text
source.residual = residual.residual ^ 59
residual.totalLayers + 1 = source.totalLayers
```

and must derive the residual's depth-`d` funding from the source's
depth-`(d+1)` congruence.
`Fermat.Conservation.Credit.Repayment.Repay.ofLayerTransport` only packages
such a producer; it does not inhabit the seam.  A global completion additionally
needs the layer-count accounting map that changes credit by `-1`, converted
by `+1`, and leaves stock and total fixed.

## Literal gate inventory

These are the downstream declarations claimed **LITERAL** above, grouped by
the identity against which a matching `#guard_depends_on` belongs.  Identity
anchors themselves are omitted.

- Against `Fermat.Conservation.Ledger.conservation_identity`:
  `Fermat.Conservation.Ledger.vacuum_conservation`,
  `Fermat.Conservation.Ledger.repay_conservation`, and
  `Fermat.Conservation.Ledger.repayNat_conservation`.
- Against `Fermat.Two.charge_ledger`:
  `Fermat.Two.pythagoras`, `Fermat.Two.emptyCoupling_of_additive`,
  `Fermat.Two.pythagoras_conserved`, and
  `Fermat.FiftyNine.Conservation.stockSpineReceipt`.
- Against `Fermat.Five.Conservation.quintic_ledger`:
  `Fermat.Five.Conservation.fermatEquation_five_ledger`,
  `Fermat.Five.Conservation.PrimitiveFifthSolution.equation`,
  `Fermat.Five.Conservation.not_five_dvd_c_seed`,
  `Fermat.Five.Conservation.five_dvd_c_seed`,
  `Fermat.Five.Conservation.not_five_dvd_c_impossible`,
  `Fermat.Five.Conservation.five_dvd_c_impossible`, and
  `Fermat.Five.holdsAt_five_conservation`.
- Against `Fermat.Six.Conservation.sixth_ledger`:
  `Fermat.Six.Conservation.PrimitiveSolution.native_ledger` and
  `Fermat.FiftyNine.Conservation.stockSpineReceipt`.
- Against `Fermat.Seven.Conservation.septic_ledger`:
  `Fermat.Seven.Conservation.Reconstruction.Lebesgue.seven_dvd_t_branch_impossible`,
  `Fermat.Seven.Conservation.Reconstruction.Lebesgue.not_seven_dvd_t_branch_impossible`,
  `Fermat.Seven.Conservation.Reconstruction.Lebesgue.ternaryOnlyTrivial_lebesgue`,
  `Fermat.Seven.Conservation.Reconstruction.Lebesgue.holdsAt_seven_lebesgue`,
  and `Fermat.Seven.holdsAt_seven_conservation`.
- Against `Fermat.Conservation.Credit.generated_eq_bot_of_no_generator`:
  `Fermat.Conservation.Credit.kummer_credit_vacuum` and, transitively,
  `Fermat.Conservation.Credit.GaugeQuotient.PrimeData.quotientLedger_eq_bot`.
- Against
  `Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.depth_conservation`:
  `Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.depth_eq_min_two_add_depth_sub_two`,
  `Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.cubeFree_of_surplus_eq_zero`,
  `Fermat.Conservation.Credit.Flow.FlowCertificate.eigenvalue_cubeFree`,
  `Fermat.Conservation.Credit.RealFlow.FlowCertificate.eigenvalue_cubeFree`,
  `Fermat.Conservation.Credit.RealFlow.FlowCertificate.depthAtMostTwo`,
  `Fermat.Conservation.Credit.RealFlow.DepthTwoCertificate.atMostTwo`,
  `Fermat.FiftyNine.Conservation.Instance.BernoulliCertificate.highBernoulliNumerator_cubeFree`,
  `Fermat.FiftyNine.Conservation.Instance.noBernoulliCubeObstruction59`,
  `Fermat.FiftyNine.Conservation.Instance.deepExponentForcing_of_flow`,
  and
  `Fermat.FiftyNine.Conservation.Instance.deepExponentForcing_on_exponentCycle_of_flow`.
- Against
  `Fermat.Conservation.Credit.Repayment.repay_layer_conservation`:
  `Fermat.Conservation.Credit.Repayment.repay_totalLayers`,
  `Fermat.Conservation.Credit.Repayment.nonempty_repay_one_iff`,
  `Fermat.FiftyNine.Conservation.Instance.nonempty_repayOne_iff_deep_repayment59`,
  and
  `Fermat.FiftyNine.Conservation.Instance.repayment_of_capacity_and_flow`.
- Against the named higher-layer interface:
  `Fermat.Conservation.Credit.Repayment.LayerTransport` depends on
  `Fermat.Conservation.Credit.Repayment.LayerConservation`, and
  `Fermat.Conservation.Credit.Repayment.Repay.ofLayerTransport` depends on
  both.  These
  guards certify the interface's shape, not a concrete inhabitant.
- Against the local gauge/fold identities:
  `Fermat.Conservation.Credit.GaugeQuotient.PrimeData.quotient_vacuum_and_charge_eq`,
  `Fermat.FiftyNine.Conservation.GaugeQuotient.debitLedger_quotient_eq_bot`,
  `Fermat.FiftyNine.Conservation.GaugeQuotient.quotient_vacuum_and_charge_eq`,
  and
  `Fermat.Conservation.Credit.Fold.relativeNormFold_apply_of_conjugation`.
- Against its two native grade-zero inputs:
  `Fermat.FiftyNine.Conservation.Instance.regularClosure59` depends on both
  `Fermat.FiftyNine.Conservation.stockSpineReceipt` and
  `Fermat.Conservation.Credit.kummer_credit_vacuum`.

The inventory intentionally contains no claim that a legacy stock theorem,
C1/C2 object, quotient, fold, or N59 assembly depends on the global
three-column identity.  That absence is the mapped boundary.

## Scope and probe status

The pre-inspection prediction lives in
`Fermat/Conservation/Credit/PREDICTIONS.md`; discovery is recorded in both
`Fermat/Conservation/Credit/FINDINGS.md` and
`Fermat/FiftyNine/Conservation/FINDINGS.md`.  This map preserves the task's
ruling: no Lemma-I proof, no transformer implementation, and no endpoint
assembly.  In particular, the guarded type mismatches in
`Fermat/FiftyNine/Conservation/TransformerProbe.lean` remain the intended
evidence for the (7a), repayment-to-successor, and ramified-charge-to-stock
seams.  The layer-transport interface is guarded in Verification, but is
not asserted to be inhabited.
