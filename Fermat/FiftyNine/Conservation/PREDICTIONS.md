# N59 conservation predictions

Recorded before inspecting or editing any Lean implementation for the
conservation proof.

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
