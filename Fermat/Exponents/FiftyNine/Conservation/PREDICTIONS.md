# N59 conservation predictions

Recorded before inspecting or editing any Lean implementation for the
conservation proof.

## 2026-08-19 — complementary-depth Dwork cup prediction

- **Committed C1 guess: both inputs are now literal Dwork shapes.**  The
  newly banked covariance and finite-projector readback theorems should expose
  the seated power-15 and power-44 Kummer classes by concrete 58-factor unit
  products whose factors come from `1 + dworkParameter^15` and
  `1 + dworkParameter^44`.  Unlike the historical universal old-carrier
  audit, neither selected input should retain an arbitrary quotient-class
  residual.
- **Committed tier guess: specialized tier C2(b) is mathematically
  sufficient.**  Since `15 + 44 = 59`, the first complementary-depth term in
  the classical Artin--Hasse local-symbol formula should be a nonzero scalar
  modulo 59; higher terms should lie beyond the required truncation.  No
  Iwasawa-total-coordinate or full Vostokov--Brueckner machinery should be
  needed for these two selected principal-unit products.
- **Committed session guess: the current library stops at one exact
  arithmetic formula signature.**  I predict the structural reduction from
  the projected cups to a finite Dwork-orbit product will compile, but that
  the tree does not yet contain the theorem identifying the continuous cup /
  normalized invariant of complementary principal units with the classical
  Artin--Hasse coefficient.  Unless inspection finds that comparison already
  banked, the honest endpoint will therefore be the smallest named
  complementary-depth evaluation whose nonzero value implies
  `∃ u : (ZMod 59)ˣ, dworkSeatedLambdaCupClass59 =
  (u : ZMod 59) • twistedLambdaKummerCupH2Class59 K`, with no value
  fabricated and no stronger tier opened.

## 2026-08-17 — Vostokov two-shape core prediction

- **Committed C1 guess: the two shapes have unequal but narrowly bounded
  coverage.**  I expect `statewiseSelmerLift` to reduce entirely to the
  banked `artinHasseKummerSubgroup` after exposing its already-fixed
  denominator and generated-unit factors.  I expect
  `transverseDetectorComponent` to be the sole genuine escape, but only as
  an Artin--Hasse-covered class times one explicit zeta/prime-element
  extension rather than an arbitrary principal-unit class.  The shape audit,
  not this guess, will decide both claims before any formula is attempted.
- **Committed tier guess: tier (b) is cheapest sufficient.**  I expect the
  banked special values alone to underdetermine the one transverse extension,
  while the classical Artin--Hasse formulas for `(ζ, u)` and `(π, u)`,
  specialized to these two representatives, close it without Iwasawa or
  general Vostokov--Brückner series machinery.
- **Committed session guess: `ReflectedWildKummerCoreAt59` inhabits.**  I
  predict that the representative pairing, reflected empty-support landing,
  and theorem-level calibration to `wild.reading` all compile this session.
  This predicts no unconditional relation (7a), no reciprocity theorem, no
  kernel erasure, and no fiber collapse.

### Recorded outcome

- The C1 coverage guess was falsified: both literal inputs are arbitrary
  quotient classes at the current interface, and neither has a proved small
  Artin--Hasse extension.  The normalized 827 fiber is moreover proved
  outside the canonical strict range, without choosing a complement.
- The tier-(b) guess was falsified twice: its hypotheses are not licensed by
  the two literal representatives, and the declared core requires a total
  pairing plus calibration on every old-carrier pair.  Tier (c) is the
  cheapest unrefuted tier; its total trace-product algebra and exact
  arithmetic-realization boundary now compile.  Tier (d) was not opened.
- The session-inhabitation guess was not met.  The new tier-(c) adapter
  derives the complete core and localization from an independently
  calibrated total-coordinate reduction plus ambient action compatibility,
  but neither arithmetic input is inhabited in the current tree.  Thus no
  localization premise or downstream (7a) premise is reported discharged.

### Later boundary update — 2026-08-18

- The outcome above remains the correct score for the original task and its
  independently supplied historical `wild.reading`.  It is not rewritten
  retrospectively.  A later route closed a different, carefully typed branch:
  the exact critical norm calculation gives a nonzero genuine Kummer cup;
  one-dimensional linear algebra then supplies a normalized algebraic
  readout, and the actual continuous cup constructs a total local/global
  Kummer pairing.
- `oldWildInterfaceOfPairing` restricts any such quotient pairing to the two
  old seated eigenspaces.  Its full `hash omega` adjoint law is formal there.
  For the interface constructed by this restriction, calibration is
  definitional, so `normalizedReflectedWildKummerCore59` and
  `normalizedReflectedWildLocalization59` are now inhabited without opening
  formula tier (d).
- This does **not** identify the constructed interface with an independently
  supplied historical wild reading.  The exact remaining comparison is
  kernel-checked as
  `oldWildInterfaceOfPairing_eq_iff_calibration`: equality of interfaces is
  equivalent to the original universal old-reading calibration theorem.
  The later theorem `wildLawfulness827_of_reciprocity` shows that the same
  still-open one-column reciprocity interface supplies wild lawfulness, so
  lawfulness is no longer an independent seam.  The normalized readout
  endpoint also constructs localization, boundary nonvanishing, and a fiber
  member internally.  `pointedTateIncidence827_of_fourierSeating_of_lift`
  additionally constructs the incidence package from Fourier seating and a
  nonzero q-relaxed localization lift.  The later theorem
  `cyclotomicQLocalizationEquivariance827`, exposed here as
  `normalizedQLocalizationEquivariance827`, proves the Fourier seating law for
  the canonical cyclotomic action and localization.  Thus the strongest
  theorem, `vandiverSevenA_of_normalizedContinuousCanonicalLift`, needs the
  reflected lift but no separately supplied seating premise.  The remaining
  literal inputs are that lift, relation-(7a) gauge seating and
  `ker Lambda ≤ ker G`, and reciprocity.  The lift itself now has an exact
  boundary:
  `nonempty_cyclotomicReflectedQRelaxedLocalizationLift827_iff` identifies it,
  at any chosen 827-place, with nonvanishing of
  `classSilentPointedCoordinate827` on the kernel of the projected finite-S
  class obstruction.  At this checkpoint that nonvanishing was not proved.
  The later resolution attached to the 2026-08-08 prediction below constructs
  it at every 827-place.  The resulting lift is a full reflected-character
  wave with every 827 coordinate nonzero, not a point mass.  A subsequent
  kernel audit makes the
  logical boundary sharper: reciprocity forces this one-column coefficient
  to be the zero map
  (`normalizedWildCoefficientOfCanonicalLift59_eq_zero`), and
  `normalizedCanonicalLiftProcessesAtLeastSevenA_iff_gauge_eq_zero` proves
  that the advertised `WildProcessesAtLeastSevenA` premise is then equivalent
  to the *entire* class-valued gauge being zero.  Since
  `vandiverSevenA_of_classGauge_eq_zero` already obtains (7a) by evaluating
  that vanishing gauge at the Fermat class, the compiled lift endpoint is a
  valid conditional/regression theorem but not a non-circular proof of (7a).
  The next arithmetic step must provide a finer nonzero readout or an
  independent comparison that does not already contain the target.  No full
  Case-II or unconditional (7a)/FLT conclusion is claimed.
- The generic reciprocity layer now records one exact candidate shape for that
  next step.  `pairAt_add_pairAt_eq_zero_of_outside_two` retains a distinct
  auxiliary column and proves `wild + auxiliary = 0`; its oriented form
  `pairAt_eq_neg_pairAt_of_outside_two` gives `wild = -auxiliary`.  This is
  structural conservation algebra only, and the tame realization now routes
  its outside-two bookkeeping through this theorem.  It is not yet the
  literal p=59 successor: the full-wave theorem shows that a cyclotomic lift
  retains all 58 coordinates above 827.  At this checkpoint the arithmetic
  route still had to sum that orbit.  The later canonical conjugate-pair
  ledger performs the globally oriented sum; its pairing comparison,
  reciprocity producer, outside-place silence, and class-gauge comparison
  remain open.

## 2026-08-13 — Vostokov wild-reading prediction

- **Committed guess: the V1 coverage upgrade does not close.**  I expect the
  existing Artin--Hasse families to absorb the normalized state-factor part
  of the campaign inventory, but not every factor introduced by the relaxed
  827 carrier.  I will test this by extending the named
  `NormalizedStateFactorArtinHasseDecomposition` middle path before building
  any residue or series machinery.
- **Committed guess: exactly one `WildClassKind` residual remains.**  My guess
  is that the uncovered class is the genuinely relaxed 827-local factor,
  while the root-of-unity, prime-element, cyclotomic-unit, and normalized
  state-factor classes reduce to already banked Artin--Hasse coverage.
- **Committed guess: V3 ends this session at a strictly smaller named
  arithmetic core.**  I expect the inclusion, additivity, adjoint assembly,
  and old-carrier agreement to become a constructor theorem, with the one
  residual symbol/localization producer left as the only named input.  This
  predicts neither a fabricated pairing value nor an unconditional 7a
  endpoint.

## 2026-08-13 — Ulam W1 readout-ledger prediction

- **Committed guess: `reflectedBoundaryFunctional827 ≠ 0` needs one new
  typed seating interface.**  I expect the banked Fourier/incidence API to
  identify the functional with the intended 827-local coordinate, but not
  yet to contain an inhabited normalized fiber or an explicit class with
  nonzero coordinate.  The interface should state exactly that missing
  arithmetic nonvanishing; it must not choose a public probe or identify the
  meter with one.
- **Committed guess: the step-5 kernel inclusion holds on the selected
  Fermat carrier.**  Local reciprocity at 59 should make the extended wild
  pairing constant on normalized 827 fibers, equivalently
  `ker q ≤ ker (B₅₉(h_F, ·))`.  I expect the generic equivalence and
  factorization to compile, while the arithmetic inclusion itself may remain
  a named typed interface.  If the compiled bank instead produces a
  nonzero restriction to `ker q`, I will record the resulting STEERABLE bit
  and stop the factorization branch.
- **Committed guess: `59 • im G = 0` closes from the banked root-ideal
  seating.**  The genuine class-valued 7a gauge should be generated by the
  root-ideal classes `[I]` and `[J]`, whose 59-torsion receipts are already
  present.  Thus the actual processed range should have exponent 59 without
  scalarizing through an arbitrary readout.  If its carrier is deeper than
  that, the surviving `c + r₁` layer must remain visible through the
  existing Bockstein receipt.
- This prediction preserves the exact unknown fiber throughout, chooses no
  complement, and claims no unconditional 7a endpoint; tame silence and
  reciprocity remain typed inputs for steps 9 and 10.

## 2026-08-13 — Ulam W0 type-freeze prediction

- **Committed guess: the STOP condition fires.**  I expect the current W4
  verdict surface to expose the allocation `(0, 1)`, fixedness, and
  preimage-independence laws, but no term inhabiting an actual reflected
  dual class or scalar-valued functional `y*`.  If that is what the type
  audit finds, W0 should stop with a typed obstruction probe naming the
  missing carrier and its required pullback/normalization laws; Lane 1 must
  not manufacture that term from the dimension count.
- The carrier identity is predicted to fight at the semantic seam between
  the concrete `ZMod 59` gauge/local Tate reading and W4's generic
  steering/fixed-readout carrier.  I expect the scalar codomain itself to
  match after specialization, while the reflected bit is represented only
  by a proposition or allocation coordinate rather than by an element of
  the Tate dual carrier.  A dimension equality will therefore not close the
  identification.
- The existing `SteeringFiber` pullback law is predicted to be sufficient
  for the descent theorem: specialize it to `ker gauge_7a`, export its real
  dependency with `#guard_depends_on`, and use the standard quotient/range
  equivalence for the detector-budget bound.  I do not expect a second
  duality proof; at most a quotient-specialized bridge lemma should be
  needed to align the existing theorem's types with `Q_7a`.
- Gauge linearity and the consumed implication from gauge vanishing to
  relation (7a) are predicted to already be definitionally nearby.  The
  converse, if absent, should require a theorem identifying the ledger
  proposition with exactly the same two-coordinate scalar equation, not
  detector injectivity.  Quotient-form consumer siblings should need only
  the comparison implication `wildReading h_F = 0 → gauge_7a h_F = 0`;
  the ambient kernel remains deliberately present.

## 2026-08-09 — transversality prediction

- **Committed guess: the split-orbit Fourier theorem alone decides
  `FIXED`.**  Since `827 ≡ 1 (mod 59)`, its 58 places form the regular
  Galois orbit.  In the position/character Fourier dictionary, a nonzero
  pure-character vector has a nonzero coordinate at every place, whereas a
  delta at the pointed place contains every frequency.  I therefore expect
  the reflected-character localization together with silence at the other
  57 places to force the pointed coordinate to vanish.  Equivalently, the
  selected reading should lie in the dual pullback from the lawful
  class/nonpointed constraint map, so the `GaugeSteering827` branch is
  `FIXED` without a determinant computation.
- The precise falsifier is a seating failure: if the current reflected
  projector does not make the full 58-place localization vector a genuine
  pure-character vector for the regular orbit action, Fourier support cannot
  be applied to the pointed kernel condition.  In that case W1 should stop
  at the exact missing equivariance/identification interface rather than
  infer `FIXED` from a suggestive basis analogy.
- **Committed conserved-bit prediction: primal steering gain is zero and
  reflected-dual obstruction gain is one.**  The pointed Tate five-term
  balance should send the unique one-dimensional local quotient to the
  reflected dual Selmer obstruction.  Thus the pre-compiled class-dual
  pullback future, not the gauge-48 receipted lift, should activate if W1--W3
  type as predicted.
- This prediction creates no unconditional relation (7a), exponent-59
  endpoint, transformer, or Selmer splitting.  W4 remains gated on clean W1,
  W2, and W3 implementations.

## 2026-08-08 — finite-S 827 lift prediction

- **Committed guess: `ReflectedQRelaxedLocalizationLift827` inhabits this
  session.**  The finite-S Selmer class sequence at Mathlib commit
  `9ec933d517` should turn the selected 827 divisor coordinate into an honest
  global relaxed class: its S-class-torsion surjection should supply the
  global class leg, while its kernel description should identify the
  representative ambiguity with the S-unit leg.  I expect matching the
  quotient representative to be formal once those maps are ported.
- The likely bite point is proving that the chosen class has a nonzero
  coordinate after the reflected-character projector, rather than merely
  producing some element of the relaxed Selmer group.  The checked first
  capacity row and 827 lamp arithmetic are predicted to discharge that
  point without a new chosen localization-surjectivity interface.  If they
  do not, the honest obstruction should be the precise divisor/class-map
  condition on the selected q-basis vector, not a generic claim that the
  global lift is difficult.
- If the lift inhabits, `SelectedTameComparison` is predicted to compile from
  the same representative/localization compatibility plus the existing
  capacity readout.  The reassembled transverse witness should then remain
  conditional only at the wild 59-coordinate.  This predicts no
  unconditional relation (7a), endpoint, or transformer, and preserves the
  no-splitting guard.

### Later resolution — 2026-08-18

- The original session did not meet the prediction: the arbitrary finite-`S`
  root remembered only valuation congruences and did not prove the required
  joint class-silence/nonvanishing condition.  That historical outcome is not
  rewritten.
- A later construction closes the exact seam.  From an actual 827-place `P`,
  it retains the plus-class provenance of the conjugation-fixed divisor
  `P * conjugate(P)`, obtains a literal 827-unit source, proves its canonical
  reflected `(59,44)` projection has value
  `reduction(1 / 58) * (-2) ≠ 0`, and proves its projected finite-`S` class
  obstruction is the identity.  `canonicalConjugatePairLift827` therefore
  constructs the genuine lift, while
  `canonical_classSilentPointedCoordinate827_ne_zero` proves the exact
  criterion at every place over 827.  No splitting or per-prime lift
  certificate was introduced.
- At the explicit orbit base place the constructed lift now also yields the
  actual pointed incidence package, a nonzero reflected boundary functional,
  and `Nonempty NormalizedReflectedFiber827`; the whole fiber is retained.
- The normalized endpoint can now install that lift internally as well.  Its
  exact diagnostic remains `processes ↔ gauge = 0` under one-column
  reciprocity, so removing the lift argument does not turn the historical
  regression theorem into a non-circular proof of (7a).
- This resolution does not automatically prove the separately predicted
  `SelectedTameComparison`.  The concrete global ledger now installs the
  lift and is nonzero with total zero, but global reciprocity, comparison of
  the chosen pairing with all 58 orbit values, outside-place silence where
  required, the independent class-gauge bridge, relation (7a), Case II, and
  FLT remain open.

## 2026-08-07 — q-relaxed reflected-carrier repair prediction

- **Committed guess: the relaxed 827 witness inhabits modulo its wild
  59-coordinate.**  Replacing the reflected dual's empty-support Selmer
  carrier by Mathlib's existing finite-support carrier at the places over
  `q = 827` should remove exactly the theorem that forced its q-valuation to
  vanish.  I expect the Delta action to preserve this support, the reflected
  character projector to generalize without new arithmetic input, and the
  first capacity-matrix coordinate to compare with a nonzero q-reading.
- The likely compiler friction is not the finite calculation but the global
  lift behind that reading.  If the arbitrary-`S` carrier does not by itself
  construct a class mapping to the selected q-local residue row, the next
  honest obstruction should be the missing finite-`S` localization
  surjectivity together with its kernel/cokernel bookkeeping.  That result is
  being developed separately on Mathlib branch `finite-s-selmer`; this
  session will name its exact incoming interface and will not assume it.
- Empty support is predicted to have been load-bearing only for the global
  valuation-zero receipt and the tame-zero specialization derived from it,
  not for the character algebra, quotient action, projector, or both-units
  law.  Every actual dependency found during generalization will be recorded
  explicitly in `FINDINGS.md`.
- This prediction claims no wild 59-reading, detector faithfulness,
  unconditional relation (7a), endpoint, or transformer.  The Vostokov
  middle path will be stated only as the exact decomposition interface that
  would reduce the two normalized state factors to the existing
  Artin--Hasse generators.

## 2026-08-07 — detector-witness and Artin–Hasse fork prediction

- **W1 prediction: 827 admits the requested transverse witness.**  The first
  conductor-59 certified lamp should supply a concrete dual-leg candidate
  after the appropriate reflected-character projection.  I expect its
  divisor to be supported only over `59` and `827`, the both-units law to
  silence every other tame place, and the surviving 827 coordinates to
  reduce to executable finite-field power/residue-symbol calculations.  The
  likely implementation friction is realizing the lamp polynomial as a
  global Kummer element in the existing seated Selmer carrier, not the
  residue arithmetic itself.  If that realization fails, the fallback table
  should expose the failure as a named channel rather than permit a chosen
  detector interface to stand in for the element.
- **W2 prediction: `AH-SUFFICES`.**  I expect the campaign's statewise
  Fermat/gauge inputs to be generated locally by roots of unity, the prime
  element `1 - zeta`, and cyclotomic units, and I expect the 59-component of
  the 827 witness to be represented by the same cyclotomic-unit family up to
  a 59th power.  On that inventory, bilinearity together with the two
  Artin–Hasse special-value families `(zeta, b)` and `(pi, b)` should
  determine every required wild reading.  A genuinely general principal
  unit outside this generated subgroup would overturn the call and force
  `NEEDS-VOSTOKOV`; it will not be silently abstracted behind a wild pairing
  oracle.
- The construction is predicted to inhabit only the witness *modulo its
  wild 59-reading*.  It will not construct `wild_detector_faithful`, infer
  unconditional relation (7a), or introduce an endpoint or transformer.

## 2026-08-07 — cohomological Stokes detector prediction

- The existing shared-detector master should repackage as a linear map
  `Lambda` on the remaining difference-mode potential, with evaluation
  given by the already-seated conductor-59 pairing.  I expect the main type
  friction to be choosing the honest dual carrier: the pairing API is
  additive and finite-support-valued, while the stage carrier may expose the
  candidate only through a selected gauge/readout.
- Tame vanishing plus global reciprocity should prove `Lambda x = 0` for the
  master theorem's selected class without proving `x = 0`.  The sole new
  frontier must therefore be the explicit injectivity statement
  `ker Lambda = 0`, naturally supplied by Poitou--Tate nondegeneracy.  No
  unconditional (7a) will be inferred from the kernel statement unless that
  frontier hypothesis is supplied.
- If the remaining potential has finrank one, one nonzero transverse
  functional should suffice; I expect this to be recorded as a generic
  dimension-reduction theorem or precise docstring, depending on how much
  finite-dimensional structure the existing stage exposes.
- `BOUNDARY-MAP.md` should consequently stop asking for another conservation
  law and name nondegeneracy of the Stokes detector as the frontier.  The
  axis-3 correction will touch docstrings only: structure supplies routes,
  focus supplies analytic weights, and transfer spans structure, focus,
  alignment, and agency.  No refactor, endpoint, transformer, or
  unconditional relation (7a) is predicted.

## 2026-08-06 — Tate bridge prediction

- Of the three named arithmetic targets, `bank_silences_other_places` is
  predicted to get furthest into the existing bank.  Capacity, bounded
  Sinnott, the funded flow/repayment receipt, and the state-produced (7d)
  fold already provide genuine silence certificates on their own carriers.
  The likely stopping point is the arithmetic localization map showing that
  those certificates put the particular local class of `x` in the
  orthogonal complement of the particular dual local condition containing
  `y`; no ledger identity can infer that guard from Selmer membership alone.
- `gauge_eq_local_tate_pairing` is predicted to remain an interface at the
  class-field-theory boundary.  The scalar gauge `r₀ + 58 • r₁` is already
  compiled, but the clean cone is not expected to contain a local Kummer or
  Artin pairing identifying that scalar with the reading at 59.  The
  structural theorem should expose a detector and a unit without choosing
  either retrospectively.
- `transverse_detector_exists` is predicted to remain an interface at the
  Poitou–Tate boundary while admitting the strongest structural wiring: the
  existing lamp/server graph should type the distinguished place 59, an
  auxiliary place `q`, and the assertion that all other readings are dark.
  The key honesty constraint is that reciprocity forbids treating an
  arbitrary 59-only detector as globally legal; `q` must supply the second
  local coordinate rather than merely annotate a detector already assumed
  global.
- The orthogonality audit is predicted to bite place by place before the
  global sum is simplified.  At 59 the gauge comparison is its own named
  interface; at `q` the bank may genuinely kill the second reading only if
  the (7d)/repayment data is connected to the local conditions; at every
  other finite or infinite place the explicit local-condition
  orthogonality guard should remain visible even when the transverse support
  theorem says the detector has no reading there.
- Once the pairing adjoint law, reciprocity conservation law, and the three
  arithmetic hypotheses are supplied, the master implication is expected to
  be formal ledger algebra: all non-59 readings vanish, reciprocity kills the
  59 reading, the unit-valued gauge identity kills the gauge, and the
  existing exact-7a vanishing theorem yields `VandiverSevenA 0 1`.
- The first implementation will stay at the mod-59 layer.  A named
  `mu_59_pow_n` risk must remain attached to the master surface: if the
  arithmetic class lives below mod 59, replacing `58` by `-1` in `ZMod 59`
  erases the correction term instead of transporting it through the bank,
  so a later proof may require a `ZMod (59 ^ n)`-valued pairing.

## 2026-08-04 — seam 7a reflection crossing prediction

- The generic `Heis`/`AreaTransfer` layer is predicted to make exact central
  cancellation routine once a reflection word is present: a word of area
  `-c₇a` should carry `Heis.center c₇a` to `Heis.center 0`, and its
  abelian projection should expose the wanted `r₀ + 58 • r₁ = 0` relation.
- The likely resistance is the producer from the canonical allocated state,
  not the payload packaging.  In decreasing order of risk: (1) turning the
  `StateFactorPair` allocation and its `StateFactorConjugation` view into an
  actual ordered word on `Additive (ClassGroup (𝒪 K))`; (2) proving on that
  statewise word that conjugation fixes its abelian endpoint and negates its
  signed area; (3) extracting a non-postulated incoming central receipt
  `c₇a` whose exact cancellation has arithmetic content rather than choosing
  the receipt retrospectively as `-w.c`.
- `boundedSinnottBridge`, `capacityCertificate`, flow, and repayment are
  predicted to certify that the special plus-side draw is silent, but their
  current conclusions may live respectively in class-number and real-unit
  carriers without a map to the ordered class-group word.  If that carrier
  bridge is absent, the typed obstruction should be localized to precisely
  this state-to-reflection-word constructor, credited to Leopoldt's 1958
  Spiegelungssatz and Vandiver's Lemma I, rather than disguised as an assumed
  `VandiverSevenA` premise.
- If the constructor does compile, projection of the resulting `τ₂` is
  expected to feed the existing conditional `factorPrincipalizationPermit_of_sevenA`
  theorem directly.  No stock transformer, successor, or endpoint should be
  entered in this crossing.

## 2026-07-29 — credit-seam patch prediction

- Seam 1 should fall first.  The expected tractable core is a generated
  `28 × 28` map over `ZMod 59`: once the 827 residue evaluations are exposed
  as homomorphisms on the actual generated subgroup, nonsingularity should
  force full mod-59 span and hence rule out a factor 59 in the subgroup
  index.  The likely resistance is not the finite matrix calculation but the
  realization boundary from abstract real-field units to residue values at a
  prime above 827, together with the passage from mod-59 span to finite
  integral index.
- Seam 2 is predicted to resist most sharply.  The consumed direction is
  `59 ∣ h⁺ → 59 ∣ [E:C]` (used contrapositively), specialized to conductor
  59.  Mathlib is unlikely to expose the analytic circular-unit index formula
  at the required number-field API boundary, so this seam may end in a
  precise obstruction map unless the prime-conductor equality can be
  reconstructed without copying forbidden implementation.
- Seam 3 is predicted to fall after Seam 1 if the generated relation already
  retains enough coefficient data.  Vandiver's Lemma II calculation should
  turn the depth-118 congruence into the requested coefficient-wise
  `59 ^ 3` divisibilities.  Its likely resistance is normalization:
  translating a congruence of cyclotomic integers into all 28 generated
  coefficient statements without importing the forbidden generic adapter.
  The incoming Bernoulli hypothesis is expected to be usable in its current
  non-obstruction form; if the calculation instead consumes explicit
  mod-`59 ^ 3` residues, that interface mismatch will be recorded
  immediately in `FINDINGS.md`.

## Expected composition

- The N1 vacuum should supply the zero/empty ledger identity without creating
  new arithmetic obligations.
- The N2 balance pattern should generalize to a three-column equation
  `stock + credit + converted = quantity`, with a converse saying that an
  empty channel closes the balance.
- The N3 drain and its shared `Fermat.Conservation.Floor` should supply the
  well-founded endpoint.  N59 should consume that floor rather than mint a
  new descent principle.
- The N4 lesson should compose the balance engine inside the drain: repayment
  moves funded credit into the converted column, after which the existing
  floor closes the ledger.
- The N5 and N7 gauge lessons should generalize structurally.  In particular,
  rank 28 should be represented by a finite family/lattice invariant rather
  than by 28 separately enumerated arguments.
- The N6 state-fold should be useful for packaging coordinate changes as data
  transformations, even though 59 itself is prime.

## Expected bite point

The new obstruction should appear exactly between gauge invariance and the
strict drain.  For a regular prime, the two-column ledger sends all conserved
stock directly to conversion.  At 59, the irregular pair `(59, 44)` should
leave a residual class-group draw.  I expect the proof to require three
explicit ingredients:

1. a named `credit` quantity measuring that residual draw;
2. a certified finite capacity, obtained only from the allowed N59 numerical
   certificate boundary;
3. a repayment map/theorem converting every admissible draw into drainable
   charge.

The capacity theorem is expected to compose cleanly as finite arithmetic.
The repayment theorem is the likely irreducible obligation: the earlier seven
spines explain how to conserve and drain a funded state, but none is expected
to provide the N59-specific exact-sequence bridge from a class-group credit
draw to converted charge.

## Expected resistance and audit risks

- Earlier conservation spines may expose their ideas through exponent-specific
  theorem signatures rather than reusable abstractions.  If so, the proof
  should factor out only the minimal shared ledger combinators needed here and
  record that interface gap in `FINDINGS.md`.
- The allowed certificate modules may import forbidden classical proof-shape
  modules transitively.  Their import cones must be tested before use; if the
  boundary is contaminated, the required numerical facts must be reconstructed
  and credited.
- A theorem that merely assumes repayment would make the ledger conditional
  and would not prove `Fermat.HoldsAt 59`.  The final proof must discharge
  repayment, not package it as an unproved field or hypothesis.
- Rephrasing `GenericLemmaTwo` or either classical case proof inside the new
  directory would violate the assignment even if the names differ.  Compiler
  pressure must be used to locate the genuinely new conservation obligation,
  and any collision with that route must be recorded immediately.

## Predicted public surface

I expect the finished cone to expose:

- a three-column ledger state and its conservation equation;
- `credit` plus a finite/capacity theorem;
- gauge invariance for the rank-28 coordinate family;
- a repayment theorem;
- a drain-to-floor theorem composed from the earlier primitives;
- `Fermat.FiftyNine.holdsAt_fiftyNine_conservation :
  Fermat.HoldsAt 59`;
- an executable `Verification.lean` checking all public axioms and proving
  every forbidden name is unknown.
