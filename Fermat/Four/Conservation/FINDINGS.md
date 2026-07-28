# N4 conservation findings

## 2026-07-28 — dependency and reconstruction boundary

- The pinned source `Mathlib.NumberTheory.FLT.Four` contains Paul van
  Wamelen's complete formalization of the classical double descent, but that
  module also defines the forbidden endpoints `not_fermat_42` and
  `fermatLastTheoremFour`. It cannot occur anywhere in the N4 import cone.
- Its arithmetic proof depends only on lower-level modules:
  `Data.Nat.Factors`, `NumberTheory.PythagoreanTriples`,
  `RingTheory.Coprime.Lemmas`, and `Tactic.LinearCombination`, in addition to
  the definition-only `NumberTheory.FLT.Basic`. These are provenance-clean
  bounded inputs.
- The existing Mathlib proof packages descent as a contradiction to a
  globally minimal solution. The reusable arithmetic body actually constructs
  integers `j`, `k`, and `i` satisfying
  `j ^ 4 + k ^ 4 = i ^ 2` with `natAbs i < natAbs c`.
  The N4 reconstruction will expose that construction directly as the
  charged-descent result instead of citing the fixed-exponent endpoint.
- The source's two calls to
  `PythagoreanTriple.coprime_classification'` are precisely the requested
  composition seam. The first decomposes `(a², b², c)` and the second
  decomposes `(a, n, m)`; together they are the coupling-free n=2 balance
  ledger powering the n=4 drain.

## 2026-07-28 — shared floor seam

- `noInfinitePositiveChargeDrain` is currently proved in
  `Fermat.Three.Conservation.Spine`, although its statement and proof are
  completely mode-generic.
- `impossible_of_strict_charge_drain` is likewise generic but currently lives
  in the n=3 Euler module. Hoisting both results to
  `Fermat.Conservation.Floor` will let n=3 and n=4 close through one literal
  impossible-debt implementation.
- The N3 call site is internal to the conservation proof, so the hoist can be
  performed by patching the real downstream module and rebuilding that cone.

## 2026-07-28 — repository state

- The working tree contains a large body of unrelated untracked user work.
  N4 commits will continue to name only explicit task paths through the
  guarded commit wrapper.
- `Fermat.Classical` and `Fermat.Ladder.Four` already use Mathlib's forbidden
  FLT(4) declarations. Neither module is needed by, nor may enter, the new
  `Fermat.Four.Conservation` cone.
