# N59 conservation predictions

Recorded before inspecting or editing any Lean implementation for the
conservation proof.

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
