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

## 2026-07-28 — realized balance-inside-drain transformer

- `StrongerSolution x y z` is the nontrivial integer equation
  `x ^ 4 + y ^ 4 = z ^ 2`, and its charge is literally `z.natAbs`.
  No ring extension or surrogate measure is used.
- `PrimitiveSolution` means exactly that the two nonzero legs are coprime.
  Odd-leg orientation and positivity of the hypotenuse are obtained inside
  each step by swapping the legs or negating `z`; both transformations
  preserve the charge.
- `pythagorean_balance_engine` turns the stronger equation into the closed
  n=2 ledger `PythagoreanTriple (x ^ 2) (y ^ 2) z`.
  The charged transformer then invokes
  `PythagoreanTriple.coprime_classification'` twice:
  first on `(x², y², z)`, then on the internal triangle `(x, n, m)`.
- Coprime square-product extraction yields
  `m = i²`, `r = ±j²`, and `s = ±k²`, hence the new stronger solution
  `j⁴ + k⁴ = i²`. Coprimality of `j` and `k` is recovered through
  `IsCoprime.pow_iff` and the sign invariance lemmas, so the successor is
  itself an iterable primitive state.
- The literal strict-charge estimate is
  `natAbs i ≤ i² = m ≤ m² < m² + n² = z = natAbs z`.
  It closes the public theorem
  `PrimitiveSolution.charged_descent`, which produces a primitive successor
  with strictly smaller `stateCharge`.
- Global minimality is used only once to obtain an initial coprime state from
  an arbitrary stronger solution. It is not an invariant or a premise of the
  charged step; the infinite sequence is generated entirely by the explicit
  double-descent transformer.

## 2026-07-28 — shared floor and final assembly

- `noInfinitePositiveChargeDrain` and the generic
  `impossible_of_strict_charge_drain` now live together in
  `Fermat.Conservation.Floor`.
- The actual N3 downstream proof was patched to use the shared impossible-debt
  theorem and its complete conservation cone rebuilt successfully.
- `not_stronger_solution_conservation` rules out the stronger square
  equation only by seeding a primitive state, applying the public charged
  step indefinitely, and invoking the shared floor.
- `Fermat.Four.holdsAt_four_conservation : Fermat.HoldsAt 4` reduces a
  hypothetical fourth-power solution to that stronger theorem by taking
  `z²` as the square hypotenuse.

## 2026-07-28 — verification

- The combined build of `Fermat.Conservation.Floor`,
  `Fermat.Three.Conservation`, `Fermat.Four.Conservation`, and
  `Fermat.Four.Conservation.Verification` completed successfully with 3,486
  jobs.
- The committed verification leaf checks `#print axioms` for the statement
  boundary, both shared-floor theorems, every public n=2 balance theorem, and
  every public N4 theorem. Every declaration depends on exactly the standard
  `[propext, Classical.choice, Quot.sound]` trio.
- In the isolated environment after importing only
  `Fermat.Four.Conservation`, executable `#guard_msgs` tests confirm that
  `fermatLastTheoremFour`, `not_fermat_42`, `Fermat.holdsAt_four`, and
  `Fermat42.not_minimal` are all unknown. This audits the transitive import
  cone, not merely source spelling.
- The forbidden-import scan, the `sorry`/`admit`/`axiom` scan, and
  `git diff --check` are clean for the delivered modules. The only occurrences
  of forbidden names in Lean sources are the expected unknown-identifier
  assertions in the verification leaf.
- A root `lake build Fermat` reached the pre-existing repository failures:
  the manifest-pinned `flt-regular` lacks `KummerFullValuation`, while
  `Fermat.Cases` and `Fermat.Regular.KummerCriterion` expect signatures from
  the unpublished local dependency branch. `Fermat.KummerIso` and therefore
  the root target cannot build under that pin. The independent N3/N4
  conservation targets are green.
