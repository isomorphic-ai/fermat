# TRANSFER boundary map

This map began as the deliverable for `LEDGER-LITERAL-TASK.md` and is updated
in place by `TRANSFER-TASK.md`.  Each retrofitted row keeps its former
classification visible as `before → after`.  This session mints the common
accounted transaction and repairs real proof cones, but still does not attempt
Lemma I / relation (7a), a stock-credit transformer inhabitant, or an
exponent-59 endpoint.  Existing obstruction probes remain evidence for those
boundaries and are not replacements for the missing constructions.

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

The four campaign anchors are:

- global accounting: `Fermat.Conservation.Ledger.conservation_identity`,
  namely `stock + credit + converted = total`;
- route-neutral transactions: `Fermat.Conservation.Transfer.available_eq`
  and `converted_decomposition`, namely
  `available before = available after + spent` and
  `after.converted = before.converted + spent`, with total preserved;
- Bernoulli channels:
  `Fermat.Conservation.Credit.Bernoulli.ChannelCertificate.depth_conservation`,
  namely `depth = min depth 2 + surplus` together with the stored
  lift/coupling decomposition;
- repayment layers:
  `Fermat.Conservation.Credit.Repayment.repay_layer_conservation`, namely
  `source.residual = residual.residual ^ p` and
  `residual.totalLayers + 1 = source.totalLayers`.

The generic carrier and transfer algebra are genuinely literal:
`Fermat.Conservation.Ledger.vacuum_conservation`,
`Fermat.Conservation.Ledger.repay_conservation`, and
`Fermat.Conservation.Ledger.repayNat_conservation` all depend on
`Fermat.Conservation.Ledger.conservation_identity`;
`Fermat.Conservation.Transfer.comp` chains transactions, and the older
strict/floor vocabulary is derived by
`available_lt_of_spent_pos`, `floor_hstep_of_positiveSteps`, and
`impossible_of_positive_transfer_drain`.  What remains absent below is not
the formula; it is the state-linked map from a native cone into this carrier.

### IsoConserve tunnel

The scheduler checkout used Lean `v4.30.0`, while this repository uses
`v4.31.0-rc1`; the mandated mismatch branch therefore vendors the minimal
L1/L4/Noether/KummerNoetherLedger statement shapes in
`Fermat.Conservation.IsoConserveStatements`, with scheduler commit, source
paths, and SHA-256 digests in the header.  The compiled correspondence is
bidirectional:

- `IsoConserveBridge.transfer_L1_conservation` maps every `Transfer` to the
  scheduler's balanced L1 step and conserved accounted total;
- `IsoConserveBridge.ofBalancedStep` maps the general balanced-step shape
  back to `Transfer`, with a proved round trip;
- `IsoConserveBridge.KummerNoether.schedulerStep_instantiates_transfer`
  supplies the concrete converse for both scheduler steps, existentially
  because the source `Step` is `Prop`-valued.

L4 remains its distinct per-column integral equation rather than being
conflated with L1 total preservation.  The Fermat and scheduler
Kummer/Noether tunnel ends therefore meet in a compiled module pair.

The W3 campaign completes nine map rows: N3, N2, graded C3, N5, N4,
additive flow, Bernoulli depth, C1, and C2.  N6 and N7 were compiler/type
audited and stopped at their lost-origin state boundaries; no partial row is
counted as a retrofit.

## Stock receipt N1--N7

`Fermat.FiftyNine.Conservation.stockSpineReceipt` is one proof with seven
fields, so the local column audits the declaration selected for each field.
Originally only its N2 and N6 paths depended on a native theorem named as a
ledger and every field was globally **ABSENT**.  The N3 and N5 selected
declarations now project actual transfers; N2 and N4 gained global adapters
on their main paths, but their selected receipt declarations were not changed.

| Rung / receipt field | Selected declaration | Global status, before → after | Native/local dependency | Exact remaining invariant |
| --- | --- | --- | --- | --- |
| N1 `n1_vacuum` | `Fermat.One.coupling_empty` | **ABSENT → ABSENT** | **DECORATIVE** with respect to `Fermat.One.charge_ledger`; the selected proof uses the independently simplified coupling | An adapter `Ledger ℕ` with `stock = charge u + charge v`, `credit = coupling u v`, `converted = 0`, and `total = charge (u + v)`, plus a theorem deriving the empty credit channel from `Ledger.conservation_identity`. |
| N2 `n2_balance` | `Fermat.Two.charge_ledger` | **ABSENT → ABSENT** for this selected field | The receipt remains **LITERAL** only with respect to the native equality.  The new `chargeLedger` and `isometryTransfer` repair the separate Noether path, not this proof value. | Route this selected balance equality through `chargeLedger` if receipt-level global literalness is wanted. |
| N3 `n3_drain` | `Fermat.Three.Conservation.drainCharge_pred_lt` | **ABSENT → LITERAL (Transfer)** | The selected strict drop now depends on `drainTransfer_stock_decomposition`, `Transfer.available_eq`, and the same transaction's cubic ledger endpoint. | Closed: `drainLedger` over `ℕ × ℤ` links ramified stock and the cubic factor at one fixed budget. |
| N4 `n4_positive` | `Fermat.Four.Conservation.PrimitiveSolution.stateCharge_pos` | **ABSENT → ABSENT** for this selected positivity field | Positivity still bypasses accounting; the separate `charged_descent` main path is now a positive Transfer projection. | No transfer is needed to prove positivity alone; route the receipt through the accounted descent if a global transaction claim is intended. |
| N5 `n5_gauge` | `Fermat.Five.Conservation.charge_gauge_invariant` | **ABSENT → LITERAL (Transfer)** | The scalar equality is now the stock projection of zero-spent `gaugeTransfer`, whose four columns are preserved. | Closed for gauge invariance.  The receipt still makes no stronger claim connecting the seed quintic ledger to every later charged state. |
| N6 `n6_fold` | `Fermat.Six.Conservation.sixth_ledger` | **ABSENT → ABSENT** | The receipt remains **LITERAL** only with respect to the selected native factor identity. | The oriented successor discards the originating primitive solution/native ledger; it must retain that state before a factor-linked Transfer can be built. |
| N7 `n7_lattice` | `Fermat.Seven.Conservation.gauge_decomposition` | **ABSENT → ABSENT** | **DECORATIVE** with respect to `Fermat.Seven.Conservation.septic_ledger`; coordinate decomposition does not use the septic factor equation. | The Lebesgue charged successor lacks the original `(x,y,z)` septic factor state; retaining it is prerequisite to the requested gauge/drain Transfer. |

### Main stock theorem paths

The receipt is deliberately not used as a proxy for the complete cones.
The following are the main downstream paths checked against each cone's
native ledger and Transfer anchors.  Split rows are intentional: a repaired
transition does not retroactively make an unrelated formula or seed
constructor transaction-literal.

| Cone | Status, before → after, and exact declarations | Remaining boundary |
| --- | --- | --- |
| N1 | Global **ABSENT → ABSENT** and native **DECORATIVE → DECORATIVE**: `Fermat.One.solvable`, `always_balances`, and `not_holdsAt_one` still bypass `charge_ledger`. | The solvability path must consume an N1 global ledger adapter and project balance from it. |
| N2 | `pythagoras`, `emptyCoupling_of_additive`, and `pythagoras_conserved` remain locally **LITERAL** through `charge_ledger`.  `charge_conserved` is (global **ABSENT**, native **DECORATIVE**) → **LITERAL (Transfer)**: `chargeLedger` exposes stock, coupling-credit, converted, and total, `isometryTransfer` preserves each column with `spent = 0`, and the legacy theorem is its total projection. | Closed for Noether/isometry conservation.  The independent Pythagoras statements retain their older native classification. |
| N3 | `drainCharge_pred_lt`, Euler's `euler_descent_charge_lt`, and `holdsAt_three_conservation` are (global **ABSENT**, native **DECORATIVE**) → **LITERAL (Transfer)**.  `drainTransfer`/Euler `accountTransfer` use product carriers and fixed budgets so factor endpoints and the multiplicity debit are projections of one composable transaction.  The formula-only `drainCharge_eq` remains native, not a transaction claim. | Closed for the requested state-linked cubic drain. |
| N4 | `PrimitiveSolution.charged_descent`, `not_stronger_solution_conservation`, and `holdsAt_four_conservation` are (global **ABSENT**, native **DECORATIVE**) → **LITERAL (Transfer)** through fixed-budget `accountLedger`, positive `charged_descent_transfer`, and the exact stock decomposition.  `pythagorean_balance_engine` remains a native arithmetic input rather than a transaction consumer. | Closed for the charged descent.  No claim is made that the receipt's standalone positivity proof is a transfer. |
| N5 | Both branch transitions, `not_five_dvd_c_charged_descent` and `five_dvd_c_charged_descent`, their impossible consumers, `holdsAt_five_conservation`, and all three charged-state gauge laws are (global **ABSENT**, native **DECORATIVE**) → **LITERAL (Transfer)**.  The gauge step spends zero and preserves all four columns; each descent has positive exact spend under a fixed budget.  The seed/equation constructors remain locally **LITERAL** through `quintic_ledger`. | The branch state retains its origin tag but no equation identifying the origin quintic ledger with the current golden charge; this unclaimed cross-link remains outside the completed transition row. |
| N6 | Global **ABSENT → ABSENT** and native **DECORATIVE → DECORATIVE** for `pythagorean_cube_balance`, `cube_balance`, `exists_orientedStateCharge_lt`, and `impossible_conservation`; `native_ledger` remains locally **LITERAL**. | `OrientedState` must retain the originating `PrimitiveSolution`/native sixth ledger.  A norm-only fixed-budget transfer would not close this factor-linked row. |
| N7 | Global **ABSENT → ABSENT** and native **DECORATIVE → DECORATIVE** for the gauge/drain and inner charged-state floor; outer branch wrappers remain locally **LITERAL** through `septic_ledger`. | `Lebesgue.ChargedState` must retain the original septic `(x,y,z)` state.  Its current five fields cannot state the requested endpoint correspondence. |

## Credit rungs C1--C3

| Rung / declarations | Global status, before → after | Native/channel/layer status | Exact remaining invariant |
| --- | --- | --- | --- |
| C1: `kummer_credit_accounted_vacuum` and legacy `kummer_credit_vacuum` | **ABSENT → LITERAL (Ledger)** | `MatrixAccount` faithfully records every routed entry; `accountMatrix_merge` turns native union-merge into addition, reflects zero, and `accountLedger` identifies generated bottom with the global vacuum.  The legacy theorem now projects from the accounted theorem. | Closed for C1. |
| C2: `capacityIndex_eq_relIndex`, `CapacityData.capacity_eq_relIndex`, `capacity_pos`, `CapacityCertificate.sound`, and `IndexCertificate.sound` | **ABSENT → LITERAL (Transfer/Ledger)** | `CapacityData.accountCredit` is the generated sub-ledger's relative index; an `Account` fixes that as total and splits it between remaining credit and converted.  `spendingTransfer` is the exact bounded debit, while finite index funds a positive one-unit transfer.  Every listed legacy equality/positivity theorem is now a ledger or Transfer projection. | Closed for capacity accounting and spending. |
| Legacy C3: `repay_of_deep_generated_cycle` | **ABSENT → ABSENT** globally | Still verdict-shaped and **DECORATIVE** with respect to `repay_layer_transfer`; it returns only `IsRepaid p u`. | Construct a typed `C ... 1` source and `C ... 0` residual before the global adapter can apply. |
| Graded C3: `repay_totalLayers` | **ABSENT → LITERAL (Transfer)** | `C.accountCredit = totalLayers`; `C.accountLedger` threads accumulated conversion; `repay_layer_transfer` spends exactly one with stock/total fixed, and the legacy layer equality is its credit projection. | Closed for every actual `Repay`. |
| Verdict view: `nonempty_repay_one_iff` | **ABSENT → ABSENT** globally | Remains layer-**LITERAL** through `repay_layer_conservation`, but an existence equivalence has no reason to inspect the global columns. | Use the witnessed `Repay` with `repay_layer_transfer`; do not relabel the verdict itself as a transaction. |
| Higher graded C3: `LayerTransport` and `Repay.ofLayerTransport` | Concrete inhabitant **ABSENT → ABSENT** | The interface remains mechanically **LITERAL** through `LayerConservation`.  Once it yields a `Repay`, the now-global `repay_layer_transfer` supplies a spent-one transaction automatically. | Only the concrete funded residual producer remains; the column adapter is no longer missing. |

The d=1 statement is no longer a boundary at 59:
`Fermat.FiftyNine.Conservation.Instance.nonempty_repayOne_iff_deep_repayment59`
and the legacy-shaped
`Fermat.FiftyNine.Conservation.Instance.repayment_of_capacity_and_flow`
are **LITERAL** through `repay_layer_conservation`.  They remain globally
**ABSENT** as verdict-shaped declarations.  Their witnessed `Repay` objects,
when used through `repay_layer_transfer`, now have globally accounted
credit-to-converted steps; no second layer adapter is missing.

## Flow and Bernoulli channels

| Path | Global status, before → after | Channel/local status | Exact remaining invariant for non-global rows |
| --- | --- | --- | --- |
| Additive exponent flow: `GeneratorOrbit.product_conservation` and `sum_conservation` | **ABSENT → LITERAL (Transfer)** | `accountFlow` is the canonical additive map into coefficient space.  Binary and finite assembly are zero-spent transfers from credited inputs to combined stock; both legacy equalities are `available_eq` projections. | Closed for product/sum conservation.  The separate high-flow forcing chain still does not consume these assembly theorems, so this row alone does not reclassify that chain. |
| Non-lossy Bernoulli compatibility: `ChannelCertificate.depth_eq_min_two_add_depth_sub_two` and `cubeFree_of_surplus_eq_zero` | **ABSENT → LITERAL (Transfer)** | `depthTransfer` has before credit `depth`, after credit `surplus`, spent/converted `min depth 2`, zero stock, and unchanged total `depth`; `depth_conservation` is its credit projection. | Closed. |
| Generic real/non-real forcing: `FlowCertificate.eigenvalue_cubeFree`, real `eigenvalue_cubeFree`, `depthAtMostTwo`, and `DepthTwoCertificate.atMostTwo` | **ABSENT → LITERAL (Transfer)** | Their existing dependency on `depth_conservation` now reaches `depthTransfer` and the global ledger identity; direct guards certify each claim. | Closed for channel-to-column accounting. |
| Selected forcing: `highBernoulliNumerator_cubeFree`, `noBernoulliCubeObstruction59`, `deepExponentForcing_of_flow`, and `deepExponentForcing_on_exponentCycle_of_flow` | **ABSENT → LITERAL (Transfer)** | The selected channel certificate instantiates the same generic `depthTransfer`; direct N59 guards reach the global ledger identity. | Closed for depth accounting, but this does not itself fund a higher repayment layer. |
| Selected exact-depth data: `DepthCertificate.depthTwoCertificate` | **ABSENT → ABSENT** for the definition | It still stores channel data and square attainment without calling `depth_conservation`; its consumer `RealFlow.DepthTwoCertificate.atMostTwo` is now globally **LITERAL**. | Connecting square attainment to the concrete funded repayment residual remains part of the higher-layer seam. |

The 59 table itself is non-lossy:
`Fermat.FiftyNine.Conservation.Instance.BernoulliCertificate.channelCertificate`
stores `depth`, `liftChannel`, `couplingChannel`, and `surplus`, while
`channelCertificate_surplus_eq_zero` is the computed fact that the retained
surplus happens to vanish.  The old Boolean is a derived view, not a storage
boundary.

## Gauge quotient

| Declarations | Global status, before → after | Local status | Exact missing invariant |
| --- | --- | --- | --- |
| Generic `PrimeData.quotientLedger_eq_bot`, `quotientCharge_quotientState`, and `quotient_vacuum_and_charge_eq` | **ABSENT → Ledger-LITERAL, Transfer-ABSENT** | The quotient-vacuum declarations now reach C1's faithful global ledger; the stock charge equality remains separately load-bearing. | A source-to-quotient Transfer in one carrier, with the lost credit equal to the converted increment. |
| Selected `debitLedger_quotient_eq_bot` and `quotient_vacuum_and_charge_eq` | **ABSENT → Ledger-LITERAL, Transfer-ABSENT** | Direct guards reach the generic accounted C1 vacuum and the selected stock-charge projection. | The same joint transaction specialized to the selected repayment root and N7 stock account. |

Thus the quotient's residual credit is now a globally accounted vacuum, and
its equal stock charge remains true, but no theorem makes them endpoints of
one `Transfer` or identifies the converted increment.

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
| `stockSpineReceipt` and `Instance.regularClosure59` | Global assembly **ABSENT → ABSENT**, but the receipt now mechanically reaches `Ledger.conservation_identity` through its repaired N3 field and reaches a global C1 vacuum. | This is still a heterogeneous conjunction, not one common-carrier `Ledger`; N1, the selected N2 balance field, N4 positivity, N6, and N7 are not silently upgraded by N3/N5. |
| Selected Bernoulli cube-freeness and deep-flow forcing | Channel **LITERAL**, global **ABSENT → LITERAL (Transfer)** for depth accounting. | The generic `depthTransfer` supplies credit/converted columns.  Concrete higher-layer funding remains separate. |
| `nonempty_repayOne_iff_deep_repayment59` and `repayment_of_capacity_and_flow` | Layer **LITERAL**, verdict-global **ABSENT → ABSENT**. | The generic one-layer `Repay` has a global spent-one transfer, but these selected declarations return existence/verdict forms rather than the typed transition. |
| `Fermat.FiftyNine.Conservation.GaugeQuotient.quotient_vacuum_and_charge_eq` | **ABSENT → Ledger-LITERAL, Transfer-ABSENT**. | C1 now accounts the vacuum projection; prove the joint source-to-quotient credit decomposition and converted increment in the stock carrier. |
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

In Transfer vocabulary, the missing inhabitant is a state-linked allocated
class transaction.  Its before available columns must be the accounted
images of `rootClass 0` and `58 • rootClass 1`; its after/converted columns
must record the net principal class with unchanged total.  The displayed
`VandiverSevenA 0 1` equality must then be a projection of that transaction,
not an input field or a parallel group calculation.  Root-class
`59`-torsion and the already-derived conjugation fold (7d) do not inhabit
this Transfer.  No such producer is attempted here.

### 2. Stock-credit transformer successor

The existing demanded interface is
`Fermat.FiftyNine.Conservation.FermatState.StockCreditTransformer`, but its
missing implementation should now be stated first as

```text
∀ S, ∃ next (τ : Transfer ℕ),
  τ.before = account S ∧
  τ.after = account next ∧
  0 < τ.spent
```

with `Transfer.available (account S) = S.charge` (and likewise for `next`).
`Transfer.available_lt_of_spent_pos` then derives `StrictSuccessor S`, and
the function assigning these witnesses derives `StockCreditTransformer`.
The existing repayment verdict and ramified norm comparison inhabit neither
endpoint equality, so they remain unrelated projections until this Transfer
producer exists.  It is not attempted here.

### 3. Higher layer transport

The exact missing object is a concrete
`LayerTransport 59 RegularClosure59 (RepaymentFunded59 hζ)`.  It must return,
for every `d > 1` and every source state, a funded residual with

```text
source.residual = residual.residual ^ 59
residual.totalLayers + 1 = source.totalLayers
```

and must derive the residual's depth-`d` funding from the source's
depth-`(d+1)` congruence.
Once that producer exists, `Repay.ofLayerTransport` and the already-compiled
`repay_layer_transfer` automatically give a `Transfer ℕ` with `spent = 1`,
credit decreased by one, converted increased by one, and stock/total fixed.
Thus the only remaining seam is the residual/root/depth funding theorem; the
global column adapter is complete.  No inhabitant is attempted here.

## Literal gate inventory

These are the downstream declarations claimed **LITERAL** above, grouped by
the identity against which a matching `#guard_depends_on` belongs.  Identity
anchors themselves are omitted.

- Core Transfer guards cover `Transfer.refl`, `comp`, and `ofRepay` against
  `Ledger.conservation_identity`; `available_lt_of_spent_pos` against
  `Transfer.available_eq`; and the positive-path floor and impossibility
  projections against that strict projection.
- Tunnel guards cover `IsoConserveBridge.transfer_L1_conservation`,
  `ofBalancedStep` and its round trip, both concrete Kummer scheduler-step
  constructors, and the existential scheduler-step conservation theorem.
- N2 guards cover `isometryTransfer` against all four column laws and
  `charge_conserved` against both that Transfer and the global ledger
  identity.
- N3 guards cover `ledger_identity`, `drainCharge_pred_lt`, Euler
  `Solution.accountTransfer_projections`, `euler_descent_transfer`,
  `euler_descent_charge_lt`, and `holdsAt_three_conservation`.  The selected
  `stockSpineReceipt` is also guarded against `Transfer.available_eq` through
  its N3 field.
- N4 guards cover `PrimitiveSolution.accountTransfer`, its stock projection,
  `charged_descent_transfer`, legacy `charged_descent`,
  `not_stronger_solution_conservation`, and `holdsAt_four_conservation`.
- N5 guards cover the global and state-level `gaugeTransfer` projections,
  `ChargedState.charged_descent_transfer`, both case-specific positive
  transfers and strict descents, both impossible consumers, and
  `holdsAt_five_conservation`.  The selected receipt is separately guarded
  against the N5 gauge Transfer.
- C1 guards cover `accountMatrix_merge`, `accountLedger_conservation`,
  `kummer_credit_accounted_vacuum`, and legacy `kummer_credit_vacuum` against
  its accounted source and `Ledger.conservation_identity`.
- C2 guards cover `capacityIndex_eq_relIndex`,
  `CapacityData.Account.spendingTransfer` and its credit/converted/total
  projections, `full_credit_eq_relIndex`, `CapacityData.capacity_eq_relIndex`,
  positive `CapacityData.capacity_pos`, `CapacityCertificate.sound`, and
  `IndexCertificate.sound`.
- Graded C3 guards cover `repay_layer_transfer` against both layer and global
  conservation; its credit, converted, and total projections; and legacy
  `repay_totalLayers` against the spent-one Transfer.  Guards on
  `nonempty_repay_one_iff` and the selected verdicts certify only their layer
  status, not a global-transaction claim.
- Flow guards cover `productTransfer` and `sumTransfer` against `accountFlow`
  and the global identity, and both legacy conservation equalities against
  their Transfer, `available_eq`, and the global identity.
- Bernoulli guards cover `depthTransfer`, its exact credit projection,
  `depth_conservation`, both generic compatibility readings, all four
  generic/real consumers, and all four selected conductor-59 consumers
  against the global ledger identity.
- The generic and selected gauge-quotient vacuum declarations are guarded
  against `Ledger.conservation_identity` through C1.  They are deliberately
  not guarded against a source-to-quotient Transfer, which remains absent.
- The older native/local guards remain: N2 Pythagoras against `charge_ledger`;
  N5 seed/equation paths against `quintic_ledger`; N6 `native_ledger` and the
  selected receipt against `sixth_ledger`; the five outer N7 declarations
  against `septic_ledger`; and the fold declarations against their native
  matrix identities.
- `LayerTransport` and `Repay.ofLayerTransport` remain guarded against
  `LayerConservation`; these certify the interface shape, not the missing
  concrete conductor-59 inhabitant.

`stockSpineReceipt` and `regularClosure59` now reach global identities
transitively, but no guard or classification asserts that either is a single
common-carrier N59 ledger.  That assembly distinction remains explicit.

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
not asserted to be inhabited.  The generic selected-prime source-literal
gate now scans `Transfer.lean` alongside the other route-neutral cores, and
the dedicated Transfer, N3, N4, N5, generic-credit, and N59 verification
leaves compile with every old and new dependency guard intact.
