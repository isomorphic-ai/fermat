# TRANSFER boundary map

This file is the in-place closing revision of the LEDGER-LITERAL and
TRANSFER boundary map.  Historical classifications remain visible as
before → after.  A row is final-LITERAL only when a compiled
#guard_depends_on command reaches its named Ledger, Transfer, Heis, or
AreaTransfer anchor through the declaration value; a matching type, comment,
or unused premise does not count.

Every classified row is LITERAL except the following named seams.

No Lemma-I proof, stock-credit transformer inhabitant, higher-layer transport
inhabitant, or exponent-59 endpoint is constructed here.

## Mechanical rule

- LITERAL means the implementation value transitively consumes
  Fermat.Conservation.Ledger.conservation_identity, a named
  Fermat.Conservation.Transfer projection, Bernoulli channel conservation,
  Repayment.repay_layer_transfer, or a named Heis/AreaTransfer payload law as
  appropriate.
- DECORATIVE was the historical state in which a compatible identity existed
  beside a proof but was bypassed.
- ABSENT was the historical state in which no common accounting carrier or
  state-linked adapter existed.
- SEAM is reserved below for one of the three named missing producers.  A
  theorem conditional on a seam premise may itself be LITERAL.

The common D=1 transaction vocabulary is Fermat.Conservation.Transfer.  Its
available_eq and converted_decomposition fields account the amount moved,
while total_preserved and both endpoint Ledger identities prevent loss.
Fermat.Conservation.AreaTransfer is its additive D=2 refinement: its generated
abelianProjection is the old Transfer, while one ordered Heisenberg word and
the before/after payloads retain the enclosed area.

### IsoConserve tunnel

The scheduler checkout and this repository use different Lean versions, so
the minimal L1/L4/Noether/KummerNoether statement shapes remain vendored in
Fermat.Conservation.IsoConserveStatements with their source digests.
Fermat.Conservation.IsoConserveBridge still compiles in both directions:

- transfer_L1_conservation maps every Transfer to the scheduler L1 shape.
- ofBalancedStep maps the scheduler balanced-step shape back to Transfer and
  has a proved round trip.
- KummerNoether.schedulerStep_instantiates_transfer supplies both concrete
  scheduler steps.

L4 remains a distinct columnwise integral statement.  It is not conflated
with L1 total preservation.

The D=2 carrier is now vendored in Fermat.Conservation.Heis with source commit
and SHA-256 provenance.  The compiled Ledger shadow is exactly

    (Transfer.available ledger, ledger.converted)
      = (ledger.stock + ledger.credit, ledger.converted).

These are the two visible coordinates of `ledgerPayload`; their sum is the
carried Ledger total.  This is not a false equivalence with all three named
columns: abelianization forgets both the stock/credit split and the central
area.  IsoConserveBridge.PayloadDictionary therefore has a canonical forward
lift with a chosen center and a reverse direction requiring an explicit
stock/credit split.  With that split and center supplied, both dictionary
round trips compile.

AreaTransfer composition uses the twisted order `first.word * second.word`,
and its abelianProjection and chain projection are the existing Transfer
composition and chain.  The bridge's PayloadBalancedStep conversions compile
exactly in both directions.  Its L1 theorem is derived from
transfer_L1_conservation on the generated projection; no parallel
conservation proof is stored.

The ported structural no-erasure law is injectivity of
`c ↦ Heis.center c * word`.  It does not make the false pointwise claim that a
chosen nonzero central coordinate can never land at zero: the compiled exact
cancellation iff says this happens precisely when `word.c = -c`.

## Stock receipt N1–N7

Fermat.FiftyNine.Conservation.stockSpineReceipt remains a heterogeneous
seven-field receipt, not one common-carrier Ledger.  Each selected field is
nevertheless mechanically LITERAL on its own route.

| Rung / selected declaration | Status, before → after | Final accounted route |
| --- | --- | --- |
| N1 Fermat.One.coupling_empty | ABSENT → LITERAL (Ledger) | chargeLedger has stock charge u + charge v, coupling credit, zero conversion, and total charge (u + v); the public vacuum and endpoint views project conservation_identity. |
| N2 Fermat.Two.charge_ledger | ABSENT → LITERAL (Ledger) | chargeLedger owns the raw norm expansion; charge_ledger and all Pythagorean consumers project its global identity. |
| N3 Fermat.Three.Conservation.drainCharge_pred_lt | ABSENT → LITERAL (Transfer) | The fixed-budget product transfer joins cubic factor stock to the positive ramified debit. |
| N4 PrimitiveSolution.stateCharge_pos | ABSENT → LITERAL (Transfer) | Internal descent bootstraps from raw solution positivity; the public theorem is derived from charged_descent_transfer and available_lt_of_spent_pos. |
| N5 Fermat.Five.Conservation.charge_gauge_invariant | ABSENT → LITERAL (Transfer) | gaugeTransfer is zero-spent and preserves all columns; selected descent branches use positive fixed-budget transfers. |
| N6 Fermat.Six.Conservation.sixth_ledger | ABSENT → LITERAL (Ledger/Transfer) | The exponent-six wrapper retains its PrimitiveSolution origin, native sixth ledger, and fixed-budget accounted successor. |
| N7 Fermat.Seven.Conservation.gauge_decomposition | ABSENT → LITERAL (Ledger) | The full gauge decomposition projects a global Ledger; the ordinary septic successor separately carries its septic origin and positive product transfer. |

## Main stock theorem paths

| Cone / declarations | Status, before → after | Final account |
| --- | --- | --- |
| N1 solvable, always_balances, not_holdsAt_one | Global ABSENT and native DECORATIVE → LITERAL (Ledger) | Every public balance and endpoint view now routes through the N1 chargeLedger identity. |
| N2 pythagoras, emptyCoupling_of_additive, pythagoras_conserved | Native LITERAL but global ABSENT → LITERAL (Ledger) | Public charge_ledger is the conservation_identity projection, so all three consumers reach the global account. |
| N2 charge_conserved | Global ABSENT, native DECORATIVE → LITERAL (Transfer) | isometryTransfer is zero-spent and preserves stock, credit, converted, and total. |
| N3 drain, Euler successor, holdsAt_three_conservation | Global ABSENT, native DECORATIVE → LITERAL (Transfer) | Product-carrier transfers retain factor and charge endpoints; strict decrease and the floor are projections. |
| N4 charged_descent, not_stronger_solution_conservation, holdsAt_four_conservation | Global ABSENT, native DECORATIVE → LITERAL (Transfer) | One fixed-budget accountTransfer supplies the exact positive stock debit. |
| N5 both charged branches, gauge laws, impossible consumers, holdsAt_five_conservation | Global ABSENT, native DECORATIVE → LITERAL (Transfer) | Origin-tagged branch states and their fixed-budget transfers retain every claimed endpoint. |
| N6 pythagorean_cube_balance, cube_balance, exists_orientedStateCharge_lt, impossible_conservation, holdsAt_six_conservation | Global ABSENT, native DECORATIVE → LITERAL (Ledger/Transfer) | OrientedState carries origin plus generic current state; factor ledger and strict successor are projections of accountTransfer. |
| N7 gauge/drain, branch closures, ternary assembly, holdsAt_seven_conservation | Global ABSENT, native DECORATIVE → LITERAL (Ledger/Transfer) | SepticChargedState carries the originating septic factor state through the ordinary successor.  The exceptional 7 ∣ T closure is ex-falso but remains Ledger-LITERAL through its retained septic origin; it is not falsely classified as a positive Transfer. |

All N6/N7 public endpoint statements keep their prior types and compile.  No
new exponent-59 endpoint is part of this map.

## Credit rungs C1–C3

| Rung / declarations | Status, before → after | Final account or seam |
| --- | --- | --- |
| C1 kummer_credit_accounted_vacuum and kummer_credit_vacuum | ABSENT → LITERAL (Ledger) | MatrixAccount is faithful, union-additive, zero-reflecting, and its generated bottom is the global vacuum. |
| C2 capacityIndex_eq_relIndex, capacity_pos, CapacityCertificate.sound, IndexCertificate.sound | ABSENT → LITERAL (Ledger/Transfer) | A capacity Account splits the fixed relative-index total; spendingTransfer moves bounded credit to converted, and finite capacity funds a positive first spend. |
| Graded C3 repay_totalLayers and repayment projections | ABSENT → LITERAL (Transfer) | C.accountLedger threads conversion; repay_layer_transfer spends exactly one with fixed stock and total. |
| Legacy C3 repay_of_deep_generated_cycle | ABSENT → LITERAL (Transfer) | The finite-index arithmetic exists once in Repay.oneOfDeepGeneratedCycle.  The legacy verdict builds a funded C1 state and projects repay_one_accounted. |
| Verdict view nonempty_repay_one_iff | Globally ABSENT, layer-LITERAL → LITERAL (Transfer) | Its forward direction uses repay_one_accounted, which pairs the residual equation with the exact credit debit. |
| Selected d = 1 nonempty_repayOne_iff_deep_repayment59 and repayment_of_capacity_and_flow | Verdict-global ABSENT → LITERAL (Transfer) | repayOne_of_capacity_and_flow specializes the typed constructor directly; both legacy-shaped declarations reach repay_layer_transfer. |
| Higher graded C3 | Concrete inhabitant ABSENT → SEAM | Repay.ofLayerTransport is already an accounted adapter, but the concrete conductor-59 LayerTransport producer is missing. |

Transfer ℕ intentionally forgets the residual group element.  The truthful
bridge is repay_one_accounted: LayerConservation proves the root equation and
the same result carries the global one-unit column transfer.

## Flow, Bernoulli, and exact depth

| Path | Status, before → after | Final account |
| --- | --- | --- |
| GeneratorOrbit.product_conservation and sum_conservation | ABSENT → LITERAL (Transfer) | accountFlow is the canonical additive stock map; productTransfer and sumTransfer are zero-spent assemblies. |
| ChannelCertificate depth compatibility and cube-free view | ABSENT → LITERAL (Transfer) | depthTransfer moves min depth 2 from credit to converted and leaves surplus explicit. |
| Generic real/non-real forcing and DepthTwoCertificate.atMostTwo | ABSENT → LITERAL (Transfer) | Every compatibility view reaches the Bernoulli depth transaction and global endpoint ledgers. |
| Selected highBernoulliNumerator_cubeFree, noBernoulliCubeObstruction59, and both deepExponentForcing declarations | ABSENT → LITERAL (Transfer) | accountedChannelTransfer uses CoefficientSpace × ℕ: accountFlow is fixed stock and coupling is the debited credit channel. |
| Selected DepthCertificate.depthTwoCertificate | ABSENT → LITERAL (Transfer) | The square witness is row 21 of the same accounted flow transaction.  fundedRow_maps_to_repayLayer separately and conditionally equates all natural-coordinate endpoints with a genuinely funded d = 1 repayment at conversion counter 1. |

The selected table retains depth, lift, coupling, and surplus.  Row 21 has
depth 2, lift 1, coupling 1, surplus 0, and spent 1.  The table identifies the
amount; it does not manufacture a funded state or higher residual.

## Gauge quotient

| Declarations | Status, before → after | Final account |
| --- | --- | --- |
| Generic PrimeData quotientLedger_eq_bot, quotientCharge_quotientState, quotient_vacuum_and_charge_eq | Ledger-LITERAL but Transfer-ABSENT → LITERAL (Ledger/Transfer) | GaugeAccount is ℕ × MatrixAccount.  sourceToQuotientTransfer retains stock charge and moves the entire generated source matrix from credit to converted. |
| Selected debitLedger_quotient_eq_bot and quotient_vacuum_and_charge_eq | Ledger-LITERAL but Transfer-ABSENT → LITERAL (Ledger/Transfer) | The conductor-59 wrapper specializes that faithful product transaction; its charge equality is the first-coordinate projection of total_preserved. |

No scalar cardinality replaces the generated matrix, and no quotient row
depends on a stock-credit successor.

## Fold and allocated class ledger

| Declarations | Status, before → after | Final account |
| --- | --- | --- |
| relativeNormFold_apply and relativeNormFold_apply_of_conjugation | ABSENT → LITERAL (Ledger) | relativeNormFoldLedger accounts the debit and transposed receivable entry as the two spendable columns. |
| relativeNormFold_class_eq_zero_of_coprime_card and conjugate_class_fold_eq_zero_of_coprime_card | ABSENT, formerly DECORATIVE → LITERAL (Transfer) | The ideal argument constructs a foldToVacuumTransfer whose spent field retains debit + receivable; class zero is its converted_decomposition projection. |
| odd_torsion_netting and generic KummerDrain permit consumers | ABSENT, formerly DECORATIVE → LITERAL (Transfer) | oddTorsionNettingTransfer uses Class × Class, keeps debit and receivable separate, and derives both zero coordinates from the converted equation. |
| Selected vandiverSevenD declarations and factorPrincipalizationPermit_of_sevenA consumers | ABSENT → LITERAL (Transfer), conditional on supplied (7a) | Generic, conductor-59, and StateLinkedIdealPair wrappers retain the fold-to-vacuum transaction.  Conditional consumers inherit oddTorsionNettingTransfer. |

The conditional permit declarations are LITERAL even though their (7a)
argument is a seam premise.  Only production of that premise from the
canonical state belongs to the frontier.

## Vendored Selmer class sequence and common-action boundary

The sequence port is sourced from
[`fabianx-ai/mathlib4` pull request 1](https://github.com/fabianx-ai/mathlib4/pull/1),
head commit `6c01b3a6a13de72eabd868ca50d743f43888af92`.  Its sole source file,
`Mathlib/RingTheory/DedekindDomain/SelmerGroup.lean`, has SHA-256
`37d78b8e5b3f9b757d1eb8b33286680501820aba250644a407e36381ee34c4d2`.
`Fermat/Conservation/SelmerSequence.lean` records the complete port delta:
ordinary imports and omitted module export-control commands; repeated
file-local notation/options; the pinned names `MonoidHom.restrict` and
`Set.mem_setOf_eq`; and omission of an unrelated four-line, API-neutral
change in the pre-existing upstream valuation proof.  No theorem statement
or proof strategy is changed.

| Declarations/checklist item | Status, before → after | Final account |
| --- | --- | --- |
| `IsDedekindDomain.selmerGroup.toClass`, `toClass_ker`, `toClass_range` | ABSENT at the pin → LITERAL (vendored theorem surface) | The explicit root-ideal class map has kernel equal to `fromUnitLift.range` and range equal to the class-group power-map kernel. |
| `CommonActionStage.WithheldSelmerClassSequenceRealization` | Named SEAM proposition → THEOREM | `selmerClassProjection` is the additive `toClass` restricted to `ClassPTorsion`; middle exactness and surjectivity use the two vendored theorems. |
| Selected `StrictRouteBoundary.sequence` | Supplied field → LITERAL specialization | The field is removed; `kummerBinding` is tied directly to the canonical realization at `p = 59`. |
| Selected allocated Selmer obstruction | Supplied value plus equality → DERIVED when the character pair/allocation is supplied | `StrictRouteBoundary.selmerObstruction` is definitionally `allocatedSelmerObstruction` from the guarded exact pair, both directional class allocations, and roots `0,1`; it is no longer separately stored. |
| Both Kummer character allocations | ABSENT → SEAM (first remaining item at a fixed reflected pair) | No `KummerPairedBinding.chi`/`.chiStar` producer or selected character projector exists.  For one supplied `ReflectedExactFilteredPair`, `CharacterDualAllocationTarget` asks for those allocations, the separate reflected-dual allocation, and readbacks preserving the actual roots; it does not quantify over every possible carrier. |
| Omega-dual laws, both integral guards, both beta compatibilities | ABSENT → SEAM (downstream checklist) | The structures state the required equivalences/action laws, integral ideal plus sharp law, and state/conversion equalities, but the selected cone has no producer.  Supplying a reflected pair to inspect the earlier character seam already supplies that pair's omega-dual laws; it is a parameter of the conditional result, not an unconditional construction. |
| Selected typed outcome | Unconditional `selmerClassExactness` localized wall → fixed-pair `characterDualAllocation` localized wall | The obsolete exactness wall is removed.  The character wall and typed result are conditional on one supplied reflected exact pair, because the selected cone names no concrete character carrier.  The later `strictRouteRhoWall` remains valid only behind a complete `StrictRouteBoundary`. |
| Local Tate pairing and adjoint law | ABSENT → INTERFACE | `TatePairing.PlaceIndexedLocalPairing` retains the local readings as a place-indexed `Finsupp` and states `pair_v (a • x) y = pair_v x (a# • y)` using the existing `InvolutiveBase.hash`; no arithmetic pairing value is manufactured. |
| Global reciprocity and conservation tunnel | ABSENT → INTERFACE law / PROVEN wiring | `TatePairing.GlobalReciprocityLaw` is the class-field-theory interface.  From that law, `PlaceLedger.toLedger`, `toVacuumTransfer`, and `reciprocity_L1_conservation` compile its zero sum through `Ledger`, `Transfer`, and `IsoConserveBridge`. |
| Selected relation-(7a) arithmetic inputs | Unnamed missing producer → THREE NAMED INTERFACES | `gauge_eq_local_tate_pairing`, `transverse_detector_exists`, and `bank_silences_other_places` are typed, falsifiable targets.  The selected bank receipts used by the audit are proved, but their localization and placewise orthogonality guards are not. |
| Conditional Tate master implication | ABSENT → PROVEN (conditional) | The pairing laws plus exactly the three named arithmetic hypotheses force the difference gauge to vanish; `differenceGauge_eq_zero_iff_vandiverSevenA` then yields `VandiverSevenA 0 1`.  This is not an unconditional proof of (7a). |

## N59 assembly summary

| Instance surface | Status, before → after | Final reading |
| --- | --- | --- |
| stockSpineReceipt | Global assembly ABSENT → LITERAL per field | All seven named fields have direct guards to their own Ledger/Transfer routes.  The receipt remains heterogeneous. |
| Instance.regularClosure59 | ABSENT → LITERAL per field | Its stock half reaches stockSpineReceipt and its credit half reaches the accounted C1 vacuum. |
| Selected flow and exact depth | ABSENT → LITERAL (Transfer) | accountFlow, the Bernoulli debit, row-21 square attainment, and the conditional funded-layer mapping share one transaction path. |
| Selected grade-one repayment verdicts | Verdict-global ABSENT → LITERAL (Transfer) | The public result shapes are unchanged, but their proof values consume repay_layer_transfer. |
| Selected gauge quotient | Transfer-ABSENT → LITERAL (Ledger/Transfer) | The full matrix debit is transferred to conversion with stock fixed. |
| Selected fold and principalization consumers | ABSENT → LITERAL (Transfer), conditional on supplied (7a) | Derived (7d) and odd-torsion netting are accounted; only the missing producer is a seam. |
| Selected common-action stage | Selmer exactness SEAM → character-allocation SEAM at a fixed reflected pair | The vendored sequence and its additive realization are unconditional.  Once a reflected pair is supplied, the typed gauge attempt retains the class obstruction at the first missing character service; the selected cone itself does not manufacture that pair, and rho remains a later conditional wall. |
| Selected Tate route to (7a) | Unnamed Lemma-I seam → PROVEN conditional implication over three INTERFACES | The compiled route consumes `gauge_eq_local_tate_pairing`, `transverse_detector_exists`, and `bank_silences_other_places`; it concludes (7a) only under all three, with no endpoint or transformer. |
| FermatState.StockCreditTransformer | ABSENT → SEAM | No state-linked positive successor transaction is constructed. |

The guarded transformer probes remain evidence of type boundaries, not
substitutes for the missing constructions.  The forbidden exponent-59
endpoint declarations remain absent.

## Literal gate inventory

The verification leaves contain at least one direct guard for every final
LITERAL row:

- TransferVerification covers the common transaction algebra and both
  IsoConserve tunnel directions.  It now also covers the Heis group, center,
  abelianization and commutator-area anchors; the Ledger shadow; AreaTransfer
  composition and chain projection; both payload-dictionary directions and
  lifted-step round trips; and the no-erasure/exact-cancellation pair.  The
  same leaf now guards the two-account flow trichotomy and exit theorem, the
  closed critical AreaTransfer word, the quotient-energy warning, every
  receipted class-carrier projection, the concrete Minkowski representative,
  the polynomial Bézout kill law, and both retained lamp livelock channels.
- N3, N4, N5, N6, and N7 verification cover the origin-carrying stock
  successors, endpoints, and floor projections.
- Credit Verification covers C1, C2, both C3 views, accountFlow, Bernoulli
  depth, generic gauge quotient, relative-norm fold, class-zero transfer, and
  odd-torsion consumers.
- LinkingVerification covers the generic place-indexed pairing surface, the
  arithmetic adjoint law, and the compiled reciprocity passage through the
  `Ledger`/`Transfer`/`IsoConserveBridge` tunnel.
- N59 Verification covers every selected receipt field, conductor-59 flow
  and depth, funded row mapping, selected repayment, selected quotient,
  selected (7d), the three named Tate targets, their conditional master
  implication, and the consumers conditional on supplied (7a).

The selected-prime literal scan includes Transfer.lean, Heis.lean,
AreaTransfer.lean, Interaction.lean, ClassCarrier.lean,
TransverseAnnihilator.lean, TatePairing.lean, and the generic credit, drain,
and Kummer source cone.  It now includes SelmerSequence.lean as well.
LinkingVerification checks and dependency-guards every new
sequence/realization and pairing declaration and freezes the standard axiom
trio; N59 Verification guards the exact (7a) gauge reading, the relocalized
selected wall, the derived allocated lift, and the conditional Tate route.
Forbidden declaration/module guards continue to exclude the classical
irregular, regular, ladder, transport, and endpoint cones.

## The remaining frontier

every classified row is LITERAL except the following named seams.

### 1. Common-action character allocation

The former Selmer-class exactness address is closed by the vendored
`toClass_ker` and `toClass_range` theorems.  The first uninhabited item in the
selected `StrictRouteBoundary` is now both commuting Kummer character
allocations.  The omega-dual realization, integral source/reflected ideals
and sharp guard, theta, and both beta compatibilities are also still
interfaces.  Only after all of them are supplied does the existing
`strictRouteRhoWall` identify the missing arithmetic representation.

For any one fixed reflected pair, `typedLocalizedResult` therefore has
address `characterDualAllocation`.  It is deliberately parameterized by that
pair: the selected cone does not contain a concrete character carrier, and a
universal demand over arbitrary reflected pairs would falsely force the root
classes to vanish on degenerate carriers.  Its retained difference-gauge
value is the open (7a) class `r₀ + 58 • r₁`; it is neither a proof that the
corner ideal is the unit ideal nor a named nonunit common factor.

### 2. Lemma I / relation (7a): the conditional Tate route

The current seam is no longer an unnamed request for a class-group
transaction.  It is the following compiled route with every boundary marked
explicitly.

| Component | Status | Exact boundary |
| --- | --- | --- |
| `TatePairing.character_mul_reflectedCharacter` and finite-support projections | **PROVEN** | The existing `#` machinery proves `chi * chi* = omega`, and the `Finsupp` carrier proves that every displayed family of local readings has finite support. |
| `TatePairing.PlaceIndexedLocalPairing` and its adjoint law | **INTERFACE** | Mathlib supplies neither the local Kummer--Artin/Tate pairing nor its arithmetic compatibility with `InvolutiveBase.hash`.  The interface states the law and retains finite support without pretending to construct it. |
| `TatePairing.GlobalReciprocityLaw` | **INTERFACE** | The global sum-zero theorem is the missing class-field-theory input. |
| `PlaceLedger.toLedger`, `PlaceLedger.toVacuumTransfer`, and `GlobalReciprocityLaw.reciprocity_L1_conservation` | **PROVEN** | Once reciprocity is supplied, the place-indexed sum is literally carried through `Ledger`, a zero-spent `Transfer`, and the `IsoConserveBridge` L1 identity. |
| `gauge_eq_local_tate_pairing` | **INTERFACE** | One selected detector and a unit must identify its 59-local reading with the computed difference gauge and reflect zero scalar reading back to zero of that retained class-group gauge. |
| `transverse_detector_exists` | **INTERFACE** | Poitou--Tate must construct one global detector with the 59-place and one lamp-selected auxiliary place `q` as its only possible readings.  The same detector witness is consumed by the other two hypotheses. |
| Capacity, bounded Sinnott, funded flow/repayment, and the statewise (7d) fold | **PROVEN** | These are genuine selected bank receipts and are retained in the place-by-place audit rather than redescribed as local theorems. |
| Localization compatibility and `LocalOrthogonalityGuard` at each audited place | **INTERFACE** | The bank receipts live in relative-index, real-unit, and ideal-class carriers.  They do not by themselves show that the localized primal and dual conditions are orthogonal.  In particular, Selmer membership alone never silences a place. |
| `bank_silences_other_places` | **INTERFACE**, with **PROVEN** bank fields | Its audit must separately silence the auxiliary `q` reading and every reading outside `{59, q}` using explicit orthogonality guards.  Merely proving support in `{59, q}` would leave `pair_59 + pair_q = 0`, not `pair_59 = 0`. |
| Conditional master implication | **PROVEN** | Given the W1 laws and exactly the three named W2 hypotheses, the bank kills every non-59 column, reciprocity kills the 59-column, the unit-valued gauge comparison kills the retained difference gauge, and `differenceGauge_eq_zero_iff_vandiverSevenA` projects exactly `pair.ledger.VandiverSevenA 0 1`. |

Thus the public result is an implication, not a new producer of any of its
three arithmetic premises.  There is no unconditional
`StateLinkedIdealPair.vandiverSevenA`, no unconditional (7a) transaction,
and no endpoint or transformer in this route.

**NAMED RISK — `mu_59_to_the_n`.**  The first interface is deliberately the
mod-59 layer.  If the class detected by relation (7a) lives deeper in a
`mu_{59^n}` tower, the local pairing must instead retain a
`ZMod (59 ^ n)`-valued reading (or equivalent integral lift).  Reducing too
early identifies `58` with `-1` and discards the `+59` correction instead of
routing it through the bank.  The conditional master theorem therefore does
not certify that mod 59 is the final arithmetic depth.

#### Historical AreaTransfer obstruction (2026-08-04)

Before the Tate route was named, the attempted direct crossing asked, for the
canonical allocated state pair with r₀ = ledger.rootClass 0 and r₁ =
ledger.rootClass 1, for a transaction constructed without taking
VandiverSevenA as an input:

    τ : Transfer (Additive (ClassGroup (𝓞 K)))
    τ.before.stock     = r₀
    τ.before.credit    = 58 • r₁
    τ.before.converted = 0
    τ.before.total     = r₀ + 58 • r₁
    τ.after            = Ledger.vacuum
    τ.spent            = r₀ + 58 • r₁

Its converted_decomposition then projects r₀ + 58 • r₁ = 0, exactly
VandiverSevenA 0 1.  Existing root-class torsion, derived (7d), netting, and
principalization consumers do not construct this transaction.

**PREDICTION — not theorem (D=2 rereading).**  Relation (7d) is predicted to
be the endpoint/abelian half of the two class relations, while (7a) is the
area/holonomy half.  Let `w₇a : Heis ℤ` denote an explicitly unconstructed
closed reflection word and let `c₇a` be its unconstructed incoming central
receipt.  The prediction is that conjugation reverses the reflection's
orientation: it fixes the abelian endpoint, sends the signed area of `w₇a` to
its negative, and lets the two conjugate views net endpoint-wise while the
central coordinate retains the residual.

The candidate whose existence would be (7a) is an unconstructed

    τ₂ : AreaTransfer (Additive (ClassGroup (𝓞 K))) ℤ

whose `τ₂.abelianProjection` has exactly the `r₀`, `58 • r₁`, vacuum, and
spent fields displayed above, with
`τ₂.beforePayload = Heis.center c₇a`,
`τ₂.afterPayload = Heis.center 0`, and `τ₂.word = w₇a`.  Its payload equation
would therefore realize exact central cancellation `w₇a.c = -c₇a`.
Producing such a `τ₂` from the canonical allocated state, without accepting
`VandiverSevenA` as an input, would project to exactly `VandiverSevenA 0 1`.
No `w₇a`, `c₇a`, or `τ₂` is asserted here.

**FINDING — typed obstruction at the authorized crossing (2026-08-04).**
The no-input core patch reaches exactly

    pair.ledger.VandiverSevenA 0 1

after allocation, conjugation transpose, capacity, bounded Sinnott, and (7d)
have all elaborated.  The current `AreaTransfer` cannot discharge this goal:
it extends an already valid `Transfer`, and `abelianProjection` is
definitionally that parent.  With the displayed class-group endpoints,
`total_preserved` and `converted_decomposition` each require
`r₀ + 58 • r₁ = 0` before `beforePayload`, `afterPayload`, or `word` can
contribute.  Meanwhile exact central cancellation has type

    w₇a.c = -c₇a : Prop

in `ℤ`; there is no dependent map from this equality, or from any
`StateLinkedIdealPair`, into the class-group relation.  The compiled theorem
`StateLinkedIdealPair.vandiverSevenA_of_areaTransfer_to_vacuum` proves the
one available direction: any area transfer with the wanted abelian endpoints
already projects to (7a).  `TransformerProbe` guards the reverse carrier
mismatch directly.

Thus, inside that historical AreaTransfer attempt, the exact missing
sub-construction was not central cancellation but the statewise theorem

    StateLinkedIdealPair.vandiverSevenA
      (pair : StateLinkedIdealPair hζ S hz) :
      pair.ledger.VandiverSevenA 0 1

equivalently principality of `pair.plusIdeal * pair.minusIdeal ^ 58`.
This is Vandiver's Lemma I through Leopoldt's 1958 Spiegelungssatz and
Kummer's primary unramified-extension argument.  The permitted cone proves
`59 ∤ h⁺`, but it has no primary-radicand/unramified-Kummer reflection
constructor and no state-to-real-unit/Heisenberg bridge; flow and repayment
end in the unrelated real-unit carrier.  KummerCriterion's available weak
reflection compares global class-number divisibility and does not imply this
special class relation.  No forbidden implementation was imported or copied,
so `τ₂` and the unconditional `FactorPrincipalizationPermit` remain absent.

**DERIVED GAUGE READING — earned swap quotient
(2026-08-05; discharges `ERRATA.md` E1).**  Put `x = r₀` and `y = r₁`
before applying the earned swap.  Since the allocated ledger proves
`59 • r₁ = 0`, the open (7a) expression satisfies

    r₀ + 58 • r₁ = r₀ - r₁ = x - y,

whereas the compiled (7d) relation is

    r₀ + r₁ = x + y.

The strict route words `1 - R` and `1 + R` map along `quotientMap` to
`SwapQuotient.sevenARelationWord` and
`SwapQuotient.sevenDRelationWord` in `A_swap`.  The compiled theorems
`sevenARelationWord_eigenspace` and `sevenDRelationWord_eigenspace` derive
that (7a) is the `-1`/difference word (`piCommon` kills it and
`piDifference` fixes it), while (7d) is the `+1`/common word (`piCommon`
fixes it and `piDifference` kills it).  Thus the proved (7d) kills the
common mode and the open (7a) is the difference mode, reversing the former
labels exactly as recorded in E1.

The former inference that (7a) must use a third party because it is the
conserved common mode is therefore withdrawn.  The interaction-side
common-mode observation now attaches to (7d), and its existing arithmetic
proof already takes a genuine third-structure route: it sends the selected
ideal through the relative norm to the maximal real subfield, principalizes
there using the plus-class-number coprimality, and extends back to identify
the norm with the product of the two conjugate ideals.  This is not an
internal transfer between the two class accounts.  The swap-quotient
computation by itself neither requires nor excludes a lamp or Stickelberger
third view for the open difference-mode (7a); such a transverse route needs
the missing common arithmetic representation and remains a named interface,
not a theorem.

There are also two unrelated readings of the numeral two which must not be
conflated.  `DepthCertificate.depthTwoCertificate` measures Bernoulli
valuation depth `2`; critical interaction gain `g = 2` marks period-two
livelock.  A theorem connecting those readings would need a typed map from
the depth filtration to the interaction action.  That **two-2s
correspondence is open future work**, not a theorem or heuristic rewrite in
the present cone.

### 3. Stock-credit transformer successor

For every PrimitiveSecondCaseSolution S, the missing producer must retain a
fixed budget B = S.charge and construct next plus

    τ : Transfer ℕ
    τ.before = stateLedger B S
    τ.after  = stateLedger B next
    τ.spent  = S.charge - next.charge
    0 < τ.spent
    Transfer.available (stateLedger B S) = S.charge
    Transfer.available (stateLedger B next) = next.charge

where stateLedger has stock equal to the current charge, zero credit,
converted equal to B minus that charge, and total B.
Transfer.available_lt_of_spent_pos would then derive StrictSuccessor S, and
the family of witnesses would inhabit StockCreditTransformer.  Repayment and
the ramified norm comparison provide neither endpoint equality.

**PREDICTION — not theorem (D=2 rereading).**  For
`δ = S.charge - next.charge`, the successor receipt must not be an arbitrary
payload label.  It is predicted to carry the ordered closed word

    wS = Heis.commutator factorLeg repaymentLeg

of the as-yet-unconstructed actual factor-normalization and repayment legs.
The required `τ₂ : AreaTransfer ℕ ℤ` would have
`τ₂.abelianProjection` equal to the fixed-budget Transfer above with
`spent = δ`, normalized incoming central coordinate
`τ₂.beforePayload.c = 0`, and payload law

    τ₂.afterPayload.c =
      τ₂.beforePayload.c + Heis.area factorLeg repaymentLeg.

Thus `τ₂.afterPayload.c = Heis.area factorLeg repaymentLeg`: the successor's
receipt is predicted to equal its enclosed area.  No factor leg, repayment
leg, `next`, `wS`, AreaTransfer, or transformer inhabitant is constructed
here.

### 4. Higher layer transport

The missing object is exactly

    LayerTransport 59 RegularClosure59 (RepaymentFunded59 hζ)

For every d > 1 and funded source C ... d it must construct a funded residual
C ... (d - 1) together with LayerConservation: the source residual is the
59th power of the target residual and the grade drops by one.  Once supplied,
Repay.ofLayerTransport and repay_layer_transfer already produce

    τ : Transfer ℕ
    τ.before = source.accountLedger converted
    τ.after  = residual.accountLedger (converted + 1)
    τ.spent  = 1

with credit down one, conversion up one, and stock/total fixed.  No concrete
inhabitant is asserted here.

**PREDICTION — not theorem (D=2 rereading).**  The grading `C_d` is predicted
to be a commutator-depth filtration: one LayerTransport peels exactly one
commutator layer, retains the explicit `C_(d-1)` residual, and has an
AreaTransfer whose abelianProjection is the existing `spent = 1` transaction
above.  At D=3 the next carrier would add only the two length-three brackets
`[A,[A,B]]` and `[B,[A,B]]`, distinguishing routes with equal endpoints and
equal enclosed area.  This merely names the next datum.  Constructing a D=3
carrier, a Magnus/lower-central tower, or any concrete layer-transport
inhabitant is explicitly out of scope.
