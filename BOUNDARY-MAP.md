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

## Vendored PowerRoot cube and common-action boundary

The generic obstruction and its Selmer integration are sourced from
[`fabianx-ai/mathlib4` pull request 1](https://github.com/fabianx-ai/mathlib4/pull/1),
generator commit `4ea7450c8a5844417866addb7fba766275a1945a` and integration/head
commit `889be7a3fee66e6630d25332a501409fa35d8590`.
`Mathlib/GroupTheory/PowerRootObstruction.lean` is byte-identical at those
two commits and has SHA-256
`44c80744a6c74bf4793cb45c7289f54512b43e6326c0ef46aac308f9cfb31d25`.
The integrated `Mathlib/RingTheory/DedekindDomain/SelmerGroup.lean` has
SHA-256
`a6fb493fdaf8686eed654b4b0f7abe84ef14d4198304ef4dcf9f8160c8afd2f6`.
`Fermat/Conservation/PowerRootObstruction.lean` and
`Fermat/Conservation/SelmerSequence.lean` record their complete compatibility
deltas: ordinary imports and omitted module export-control commands; the
pinned `MonoidHom.restrict` spelling; repeated file-local notation/options;
one explicit quotient type argument required by Lean 4.31; and omission of
unrelated pre-existing upstream proof-engineering changes.  No theorem
statement or proof strategy is changed.

The pin also contains `selmerGroup S p` for arbitrary support `S`; only the
vendored unit/class exact sequence above is specialized to empty support.
Commit `1d0c3e4` uses that existing carrier directly at the places over 827.
Its proved
`SelmerEigenspace.supportValuation_ker_eq_range_emptySupportInclusion`
identifies the localization kernel with the embedded empty-support group.
It does **not** identify the image of supported valuation.  The named
incoming `FiniteSupportSelmerLocalizationSequence` must add an obstruction
arrow and `Function.Exact relaxedValuation obstruction`; a requested local
q-vector lifts only after a proof that its obstruction vanishes, not by an
assumed surjectivity theorem.  A separate incoming
`FiniteSupportSelmerSUnitClassSequence` must supply the S-unit/S-class arrows,
their correctly placed injection, kernel/range, and surjection statements,
and comparison squares.  At this snapshot `~/Mathlib` branch
`finite-s-selmer` has no finite-support implementation or new vendorable
provenance, so these names are interfaces only; commit and SHA provenance
will be recorded when that branch is ready.

| Declarations/checklist item | Status, before → after | Final account |
| --- | --- | --- |
| `PowerRoot.root`, `root_mul`, `root_shift`, `obstruction`, `obstruction_ker`, `obstruction_range` | ABSENT at the pin → LITERAL (provenance-pinned generator) | The route-neutral generator constructs the unique root and its cokernel obstruction; representative shift, multiplicativity, kernel, and range are proved generically. |
| `PowerRootExactSequence.principalIdealComplex` and `principalIdealExtensionClass` | ABSENT → LITERAL, unsplit | The actual arrow `Kˣ → (FractionalIdeal R⁰ K)ˣ` is a two-term complex.  Its `pi₁` is canonically `Rˣ`, its `pi₀` is canonically `ClassGroup R`, and the Selmer middle retains the exact unit/class extension without a product equivalence.  A declaration-type audit mechanically rejects any public product-splitting equivalence. |
| `IsDedekindDomain.selmerGroup.toClass`, `toClass_ker`, `toClass_range` | Hand-written root-ideal implementation → LITERAL generic derivation | `toClass` is now the instantiated `PowerRoot.obstruction`; its kernel is `fromUnitLift.range` and its range is the class-group power-map kernel. |
| `PowerRootNaturality` Delta, reflection, and localization faces | ABSENT → PROVEN generically / NAMED INTERFACE where carriers are absent | Every commuting arrow square transports roots and obstructions; `root_mul` and `root_shift` are exposed as the multiplication and representative-change engines.  Delta basis actions and reflected equivalences are typed, while localization names the missing local carrier and its exact square law. |
| `CommonActionStage.WithheldSelmerClassSequenceRealization` | Named SEAM proposition → THEOREM | `selmerClassProjection` is the additive `toClass` restricted to `ClassPTorsion`; middle exactness and surjectivity use the two vendored theorems. |
| Selected `StrictRouteBoundary.sequence` | Supplied field → LITERAL specialization | The field is removed; `kummerBinding` is tied directly to the canonical realization at `p = 59`. |
| Selected allocated Selmer obstruction | Supplied value plus equality → DERIVED when the character pair/allocation is supplied | `StrictRouteBoundary.selmerObstruction` is definitionally `allocatedSelmerObstruction` from the guarded exact pair, both directional class allocations, and roots `0,1`; it is no longer separately stored. |
| Both Kummer character allocations | ABSENT → SEAM (first remaining item at a fixed reflected pair) | The q-relaxed carrier now has a genuine generic `characterProjectorAt`, but the arithmetic `Delta` representation and a source whose projected q-localization is nonzero are not constructed.  For one supplied `ReflectedExactFilteredPair`, `CharacterDualAllocationTarget` still asks for the allocations and readbacks preserving the actual roots; it does not quantify over every possible carrier. |
| Omega-dual laws, both integral guards, both beta compatibilities | ABSENT → SEAM (downstream checklist) | The structures state the required equivalences/action laws, integral ideal plus sharp law, and state/conversion equalities, but the selected cone has no producer.  Supplying a reflected pair to inspect the earlier character seam already supplies that pair's omega-dual laws; it is a parameter of the conditional result, not an unconditional construction. |
| Selected typed outcome | Unconditional `selmerClassExactness` localized wall → fixed-pair `characterDualAllocation` localized wall | The obsolete exactness wall is removed.  The character wall and typed result are conditional on one supplied reflected exact pair, because the selected cone names no concrete character carrier.  The later `strictRouteRhoWall` remains valid only behind a complete `StrictRouteBoundary`. |
| `LinkingInterfaces.ArithmeticRepresentation.rho` | Pair/class action → principal-arrow action | `rho` is a monoid action by equivariant endomorphisms of the actual principal-ideal arrow, so its root and obstruction squares are forced by generic naturality.  The route action on the reflected Selmer pair remains separately named `selmerAction`; the summit does not infer it from a class shadow. |
| `GaugeAsNaturalityDefect59.gaugeNaturalityOutcome59` | Four candidates → **OUTCOME 4** | The two routes of a genuine PowerRoot localization face start from one divisible class and commute.  The implemented selected readings instead retain distinct ledger sources `0` and `1`, while the comparison route is the reflected-dual wild Tate reading.  Thus the constructed selected route is not that same-input naturality defect.  This is a source-provenance result, not a universal claim that unrelated scalar values cannot coincide. |
| `bocksteinPowerRootReceiptObservation` | Depth correction erased implicitly → NAMED OBSERVATION | The formal integral lift records `r₀ + 58 r₁ = (r₀ - r₁) + 59 r₁`; reduction kills the `59 r₁` receipt by the proved first-layer torsion law.  No nonzero arithmetic Bockstein, depth theorem, or two-2s transport is asserted. |
| Local Tate pairing and adjoint law | ABSENT → INTERFACE | `TatePairing.PlaceIndexedLocalPairing` retains the local readings as a place-indexed `Finsupp` and states `pair_v (a • x) y = pair_v x (a# • y)` using the existing `InvolutiveBase.hash`; no arithmetic pairing value is manufactured. |
| Global reciprocity and conservation tunnel | ABSENT → INTERFACE law / PROVEN wiring | `TatePairing.GlobalReciprocityLaw` is the class-field-theory interface.  From that law, `PlaceLedger.toLedger`, `toVacuumTransfer`, and `reciprocity_L1_conservation` compile its zero sum through `Ledger`, `Transfer`, and `IsoConserveBridge`. |
| Selected relation-(7a) arithmetic inputs | Unnamed missing producer → STOKES KERNEL EXPOSED / Q-RELAXED WITNESS WALL TYPED | The arbitrary-support carrier, reflected-character projector, supported valuation, and nonzero 827 capacity readout now compile.  The old empty-support contradiction no longer applies at q.  `ReflectedQRelaxedLocalizationLift827` is the exact uninhabited global-lift/source wall, followed by `SelectedTameComparison`; neither is a consequence of faithfulness. |
| Conditional Tate master implication | ABSENT → PROVEN (conditional), now factored through Stokes | `Lambda_apply_eq_zero_of_reciprocity` kills the complete wild detector functional.  Evaluating it at the shared detector and using the existing gauge comparison yields the same conditional `VandiverSevenA 0 1`.  This is not an unconditional proof of (7a). |

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
| Selected PowerRoot cube test | Unclassified comparison → TYPED OUTCOME 4 | Generic localization naturality is proved, but the actual `r₀,r₁` arise from distinct allocated root inputs and the selected comparison is wild reflected-dual Tate data.  Stage 3 therefore retains the wild route rather than replacing it with a generic defect. |
| Selected Tate route to (7a) | Unnamed Lemma-I seam → STOKES KERNEL plus a typed finite-S lifting obstruction | The complete detector `Lambda` is the existing 59-local pairing family.  Tame/away vanishing and reciprocity prove `Lambda x = 0`; `wild_detector_faithful : ker Lambda = 0` remains the final nondegeneracy interface.  `DetectorWitness827` now supplies the q-relaxed carrier/projector and clean nonzero 827 readout, but no source with nonzero projected q-localization.  The incoming finite-S sequence must test the desired local vector against its obstruction; it is not assumed surjective.  The wild formula inventory is `NEEDS-VOSTOKOV`. |
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
- LinkingVerification covers the provenance-pinned PowerRoot generator, the
  unsplit principal-ideal extension, all three naturality faces, the stronger
  principal-arrow `rho`, the generic place-indexed pairing surface, the
  arithmetic adjoint law, and the compiled reciprocity passage through the
  `Ledger`/`Transfer`/`IsoConserveBridge` tunnel.
- N59 Verification covers every selected receipt field, conductor-59 flow
  and depth, funded row mapping, selected repayment, selected quotient,
  selected (7d), the four-way gauge classification and outcome-4 evidence,
  the named Bockstein-receipt observation, the three named Tate targets,
  their conditional master implication, and the consumers conditional on
  supplied (7a).

The selected-prime literal scan includes Transfer.lean, Heis.lean,
AreaTransfer.lean, Interaction.lean, ClassCarrier.lean,
TransverseAnnihilator.lean, TatePairing.lean, the generic credit, drain, and
Kummer source cone, and now `PowerRootObstruction.lean`,
`PowerRootExactSequence.lean`, `PowerRootNaturality.lean`, and
`SelmerSequence.lean`.  LinkingVerification checks and dependency-guards the
new generator, unsplit sequence, cube faces, representation, realization,
and pairing declarations and freezes the standard axiom trio; N59
Verification also guards the selected four-way classification, exact gauge
reading, named depth observation, relocalized wall, derived allocated lift,
and conditional Tate route.
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

### 2. Lemma I / relation (7a): nondegeneracy of the Stokes detector

The current seam is no longer an unnamed request for a class-group
transaction or a request to find another conservation law.  Reciprocity is
already the Stokes law: after the tame faces vanish, it puts the remaining
difference-mode potential in the kernel of the wild detector.  The frontier
is to prove that this detector is nondegenerate.  Every carrier boundary is
marked explicitly below.

| Component | Status | Exact boundary |
| --- | --- | --- |
| `TatePairing.character_mul_reflectedCharacter` and finite-support projections | **PROVEN** | The existing `#` machinery proves `chi * chi* = omega`, and the `Finsupp` carrier proves that every displayed family of local readings has finite support. |
| `TameSymbol.Context`, its explicit symbol, and the two seated Selmer legs | **PROVEN**, relative to named local realization data | `TameSymbol` constructs the degree-`p` symbol in `ZMod p` and proves bilinearity, antisymmetry, Steinberg, moved-place/fixed-place equivariance, both-units silence, `p`-divisible-valuation silence, and Kummer-quotient descent.  The original `SelmerChi` and `DOmegaSelmerChiStar` remain literal empty-support eigenspaces.  `SelmerCarrierAt`, `characterEigenspaceAt`, and `characterProjectorAt` now generalize the carrier/eigen/projector algebra to arbitrary support without changing those seated legs.  The angular-component/primitive-root context and arithmetic `Delta` representation remain named realization seams. |
| `TamePlacePairing.WildLocalInterface.toPlaceIndexedLocalPairing` and `Seated.Realization.ofWild` | **PROVEN zero on the empty-support tame rows** / **NOT an explicit two-place detector pairing** | The only supplied local reading is one bilinear, `#`-adjoint value at the distinguished wild place, and the complete `Finsupp` family is constructed as that single column.  On the literal empty-support Selmer eigenspaces, Mathlib's valuation receipt makes every tame row zero.  This is a correct realization of those local conditions, but it cannot also realize a nonzero q-relaxed detector coordinate. |
| `H_FLT`, `pair_59`, and `Lambda` | **PROVEN definitions** | `H_FLT` is honestly the selected primal Selmer carrier, and `Lambda : H_FLT →+ (DOmegaSelmerChiStar →+ ZMod 59)` is definitionally the existing wild reading.  `Lambda_apply` identifies evaluation with `pairAt` at the distinguished place.  This does not manufacture a map from the Selmer carrier to `AllocatedClass K`; `GaugeComparison` remains that explicit seating boundary. |
| `TatePairing.GlobalReciprocityLaw` | **INTERFACE** | The global sum-zero theorem is the missing class-field-theory input. |
| `PlaceLedger.toLedger`, `PlaceLedger.toVacuumTransfer`, and `GlobalReciprocityLaw.reciprocity_L1_conservation` | **PROVEN** | Once reciprocity is supplied, the place-indexed sum is literally carried through `Ledger`, a zero-spent `Transfer`, and the `IsoConserveBridge` L1 identity. |
| `Lambda_apply_eq_zero_of_reciprocity` | **PROVEN Stokes theorem**, conditional only on the named reciprocity law | Every non-wild column is zero by the constructed single support.  Applying reciprocity for every reflected-dual detector proves the functional equality `Lambda x = 0`, not merely one scalar coordinate. |
| `wild_detector_faithful` | **SINGLE FRONTIER INTERFACE** | The exact target is `(Lambda wild).ker = ⊥`: the wild detector family separates the remaining potential.  Poitou--Tate nondegeneracy is its natural arithmetic source.  If `H_FLT` has finrank one, `wild_detector_faithful_of_finrank_one` proves that one nonzero transverse reading suffices.  No inhabitant is asserted. |
| `gauge_eq_local_tate_pairing` | **INTERFACE** | One selected detector and a unit must identify its 59-local reading with the computed difference gauge and reflect zero scalar reading back to zero of that retained class-group gauge. |
| `transverse_detector_exists` | **ABSTRACT PRE-WITNESS INTERFACE** | The existing proposition packages an arbitrary dual value, a lamp action, and a place label, but its single-wild-column pairing forces the q-reading to zero and it contains no global Kummer representative or q-relaxed local condition.  It remains sufficient for the old conditional implication, but is not the explicit Stage-2 witness requested here. |
| `DetectorWitness827` q-relaxed repair | **CARRIER/PROJECTOR/READOUT PROVEN; WITNESS UNINHABITED AT A NEW WALL** | `QRelaxedSelmerCarrier827` is Mathlib's actual Selmer group supported at all places over 827.  `qRelaxedReflectedProjector827` lands in the reflected eigenspace, and `localizationResidueReadout827` compares its supported valuation with the actual first capacity functional of value `48`.  Thus the old empty-support no-go dissolves at q.  `ReflectedQRelaxedLocalizationLift827` still requires a global source with nonzero projected q-coordinate and a representative supported over 59 and 827; `SelectedTameComparison` then identifies the actual tame reading with the computed readout.  Neither structure is inhabited. |
| Finite-S kernel and incoming localization sequence | **KERNEL PROVEN / IMAGE-COKERNEL INTERFACE NOT ASSUMED** | `supportValuation_ker_eq_range_emptySupportInclusion` proves exactly the kernel of supported valuation at the existing pin.  The named incoming `FiniteSupportSelmerLocalizationSequence` must place an obstruction after localization and prove exactness; a target q-vector lifts only after its obstruction is zero.  `FiniteSupportSelmerSUnitClassSequence` separately records the S-unit/S-class bookkeeping and comparison squares.  The external `finite-s-selmer` branch has no vendorable implementation/provenance at this snapshot, and no valuation-surjectivity shortcut is used. |
| `ArtinHasseInventory.campaign_formulaBudget_eq_needsVostokov` | **PROVEN COVERAGE VERDICT: `NEEDS-VOSTOKOV`; PRECISE EXIT INTERFACE NAMED** | `zeta`, `1-zeta`, and generated cyclotomic units have explicit provenance.  `NormalizedStateFactorArtinHasseDecomposition hζ S hz` would give explicit Kummer-class coefficient decompositions of both normalized state factors into `zetaUnit`, nonzero `fixedDenominator`, and every `generatedUnit`; a one-sided proof also needs conjugation stability to obtain the other row.  This factor statement alone does not seat the chosen statewise Selmer preimage or the selected detector lift, nor provide their local Hilbert-symbol comparison.  The current verdict is missing-decomposition, not nonmembership. |
| Capacity, bounded Sinnott, funded flow/repayment, and the statewise (7d) fold | **PROVEN** | These are genuine selected bank receipts and are retained in the place-by-place audit rather than redescribed as local theorems. |
| `LocalOrthogonalityGuard` | **RETAINED where it binds; not needed for a proved tame row** | The generic guard remains available and explicit.  Stage 1 does not turn a bank receipt into a localization theorem: instead it computes the actual tame symbol on the seated quotient classes.  In the selected single-wild-column model there is consequently no remaining away row on which an orthogonality guard binds. |
| `bank_silences_other_places` | **PROVEN** | The audit contains the already proved capacity, bounded-Sinnott, plus-class-number, deep-flow, repayment, and (7d) receipts.  Its auxiliary and every other non-59 verdict now follow from the constructed single support, whose tame realization is justified by the two Selmer valuation receipts; the former auxiliary/other orthogonality fields have been removed at their source. |
| Conditional master implication | **PROVEN** | Given the one 59-local interface, global reciprocity, detector existence, and the unit-valued gauge comparison, the proof first obtains `Lambda x = 0` from the Stokes theorem, evaluates it at the shared detector, and applies `differenceGauge_eq_zero_iff_vandiverSevenA` to obtain exactly `pair.ledger.VandiverSevenA 0 1`.  There is no `hBank` premise. |

Thus conservation has already done its job: tame cancellation plus
reciprocity proves that the selected potential lies in the Stokes detector's
kernel.  The final arithmetic frontier is still nondegeneracy of that
detector, not a second conservation identity.  Stage 2 now has the literal
q-relaxed carrier, reflected projector, localization coordinate, and
nonzero 827 comparison coefficient.  Its next wall is concrete: produce a
`ReflectedQRelaxedLocalizationLift827` by showing that the desired local
vector lies in the kernel of the incoming finite-S obstruction, then supply
`SelectedTameComparison`.  The old every-place valuation-zero argument no
longer applies at q, but exactness does not make localization automatically
surjective.  At the remaining wild place the present generator inventory
requires the general Vostokov budget unless the normalized factors are
decomposed as named above and the actual selected inputs are seated in those
decompositions.

The public Tate result remains an implication, not a new producer of the
wild local reading, reciprocity, detector, faithfulness, or gauge-comparison
inputs.  In particular, detector faithfulness lives on `SelmerChi`, while
relation (7a) lives in `AllocatedClass K`; the existing zero-reflecting gauge
comparison is still required to cross that typed boundary.  There is no
unconditional `StateLinkedIdealPair.vandiverSevenA`, no unconditional (7a)
transaction, and no endpoint or transformer in this route.

**NAMED RISK — `mu_59_to_the_n`.**  The first interface is deliberately the
mod-59 layer.  If the class detected by relation (7a) lives deeper in a
`mu_{59^n}` tower, the local pairing must instead retain a
`ZMod (59 ^ n)`-valued reading (or equivalent integral lift).  Reducing too
early identifies `58` with `-1` and discards the `+59` correction instead of
routing it through the bank.  The conditional master theorem therefore does
not certify that mod 59 is the final arithmetic depth.  The named
`BocksteinPowerRootReceiptObservation` now retains this exact correction as
the formal integral term `59 • r₁`, proves only that its first-layer
reduction vanishes, and marks the possible depth/Bockstein interpretation as
an observation.  Its `TwoTwosCorrespondenceStatus` remains explicitly open:
no map connects Bernoulli depth two to critical interaction period two.

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
third view for the open difference-mode (7a).  The existing pairing packages
all such transverse readings as `Lambda`; the precise frontier is now
nondegeneracy of this Stokes detector on the remaining potential, together
with the still-explicit Selmer/class seating.  Neither is asserted as a
theorem.

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
