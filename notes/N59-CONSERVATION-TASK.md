# TASK N59 — FLT exponent 59, strictly as a conservation law

**TruthSeed:** `fermat-n59:the-credit-column-debuts`
**For:** PRO Goblin (GPT 5.6 Sol Ultra) via codex, working in ~/fermat.
**Target:** `Fermat.FiftyNine.holdsAt_fiftyNine_conservation : Fermat.HoldsAt 59`
**Location:** `Fermat/Exponents/FiftyNine/Conservation/`

## Why 59, and why now

The ladder n = 1..7 is complete and audited. Its seven primitives:

1. **N1 vacuum** — unconditional balance; the ledger's identity
   element (`Fermat.One`, coupling identically empty, [propext] only).
2. **N2 balance** — charge + coupling channel; balance iff the channel
   is empty, with converse (`Fermat.Two.PythagorasConservation`).
3. **N3 drain** — multiplicative charge, infinite descent as strictly
   decreasing potential; the floor minted
   (`Fermat.Three.Conservation`, `Fermat.Conservation.Floor`).
4. **N4 composition** — a balance engine running inside a drain; the
   floor shared, not re-minted (`Fermat.Four.Conservation`).
5. **N5 gauge, rank 1** — charge invariant under the infinite unit
   tower of ℚ(√5) (`Fermat.Five.Conservation`).
6. **N6 state-fold** — composite exponents fold state coordinates,
   not propositions (`Fermat.Six.Conservation`).
7. **N7 gauge, rank 2** — the unit *lattice*, the regulator, strict
   norm-charge drain replacing induction (`Fermat.Seven.Conservation`).

Every prime so far is **regular**: the drain never leaks, and the
ledger ran on two columns (stock, converted). **59 is irregular** —
the pair (59, 44): 59 divides the numerator of B₄₄. Kummer's drain
leaks at exactly that position; the classical descent does not close.
This is the rung where the ledger's third column must finally earn its
seat:

**Q = stock + credit + converted.**

The credit line is the 59-part of the class group of ℚ(ζ₅₉), funded by
the Bernoulli factor. The conservation proof must (a) open the credit
line explicitly, (b) show its capacity is finite and *known* (the
certificate data), and (c) show every draw on it is repaid — converted
through the drain — so the ledger still closes. This is the
Kummer–Selmer exact-sequence discipline in ledger form: no leak, no
unfunded debt. Same accounting law as the scheduler paper and the
Wiles reading; first time it runs inside a per-exponent FLT proof.

## The assignment: COMPOSE, do not re-derive

Fabian's instruction verbatim: *"Simply using strictly the
conservation law and composing out of the 7 primitives."* Import the
conservation spines of the earlier rungs wherever they fit; the shared
floor (`Fermat.Conservation.Floor`) is already minted — use it. The
measure of success is not just that the theorem closes but that the
proof reads as a **composition**: vacuum + balance + drain + shared
floor + gauge (rank 28 now — the N7 lattice lesson is why this is
structural, not enumerative) + the new credit column. Where a
primitive doesn't generalize cleanly, that gap is a FINDING — name it.

## Import boundary (the non-circularity cone)

**FORBIDDEN — must be absent from the import cone** (each one gets a
forbidden-name guard in Verification.lean, and the verifier proves
them *unknown*, not just unused):

- `Fermat.FiftyNine.GenericProof`, `Fermat.FiftyNine.FirstCase`,
  `Fermat.FiftyNine.GenericSecondCase`, `Fermat.FiftyNine.Folding`,
  `Fermat.FiftyNine.GenericChannels`, `Fermat.FiftyNine.GenericLemmaTwo`
  (the repository's classical 59 route),
- `Fermat.GenericIrregular.*`, `Fermat.Irregular.*`, `Fermat.Ladder.*`
  (the generic irregular machinery — the conservation rung must stand
  on its own ledger),
- `Fermat.HoldsAt.mono_of_dvd` (import `Fermat.Statement.Basic` only,
  never the wider `Fermat.Statement` facade),
- anything imported by the above that carries the classical proof
  shape.

**ALLOWED in bounded roles, boundary LISTED** (the flt9/KN pattern):

- `Fermat.FiftyNine.ArithmeticCertificate`,
  `Fermat.FiftyNine.CircularUnitCertificate`,
  `Fermat.FiftyNine.CircularUnitIndex`,
  `Fermat.FiftyNine.CircularUnitResidues` — as **numerical facts
  only** (the credit line's audited capacity). List in FINDINGS.md
  exactly which certified numbers you consume and in what role. If any
  of these modules transitively pulls in a forbidden proof-shape
  module, reconstruct the needed data instead (credited, the N3 Euler
  pattern).
- Mathlib, and the six conservation spines above, freely.

## House rules (fleet standard — they bind here)

1. PRE-REGISTER: `PREDICTIONS.md` in the Conservation/ directory,
   committed BEFORE any Lean work — where you expect the credit
   column to bite, which primitives you expect to compose cleanly,
   which to resist.
2. `FINDINGS.md` at discovery time, newest first; deviations are
   findings. Commit early and often.
3. Executable `Verification.lean` in-tree (the N4 pattern): axiom
   guards (`#print axioms` on every public theorem — standard trio
   [propext, Classical.choice, Quot.sound] only) AND forbidden-name
   guards for every name in the forbidden list.
4. The cone must build green standalone
   (`lake build Fermat.FiftyNine.Conservation.Verification`); do not
   attempt the root build (pre-existing flt-regular manifest drift +
   one exit-137 module block it — not yours to fix).
5. `ps` before heavy builds — the box is shared.
6. Credited reconstruction is honorable (N3 precedent); silent
   re-derivation of a forbidden route is not. If you find yourself
   re-proving GenericLemmaTwo line-for-line, stop and write the
   finding.
7. Commit messages tell the truth about what compiles and what
   doesn't, every time.

## Success criteria

- `Fermat.FiftyNine.holdsAt_fiftyNine_conservation : Fermat.HoldsAt 59`
  compiles; `#print axioms` = standard trio (or less).
- Forbidden names are *unknown constants* in the cone.
- The credit ledger is explicit in the code: a named `credit` (or
  equivalent) quantity, its finiteness/capacity theorem, and its
  repayment theorem — not folklore in comments.
- PREDICTIONS committed first; FINDINGS current; Verification.lean
  green.

— Fable (reviewer), on behalf of Fabian, 2026-07-28
