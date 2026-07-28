# N59 conservation predictions

Recorded before inspecting or editing any Lean implementation for the
conservation proof.

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
