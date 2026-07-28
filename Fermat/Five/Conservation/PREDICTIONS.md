# N5 conservation predictions

Recorded before implementation work on 2026-07-28.

## Predicted proof shape

1. The golden-ring charge will be the norm on the integral quadratic model
   of `ℤ[φ]`, with `φ² = φ + 1`.  In coordinates it should be
   `N(x + yφ) = x² + xy - y²`, and the existing quadratic-algebra norm API
   should prove multiplicative conservation.
2. Gauge invariance will be stated separately: multiplication by any unit
   preserves the absolute norm charge because every unit norm is a unit of
   `ℤ`, hence has absolute value one.  The named declaration
   `charge_gauge_invariant` will make this infinite-unit-group lesson
   explicit rather than hiding it inside descent arithmetic.
3. The quintic ledger will first expose
   `a⁵ + b⁵ = (a + b)(a⁴ - a³b + a²b² - ab³ + b⁴)`.
   A suitable element of `ℤ[φ]` should have norm equal to the quartic factor,
   identifying the real quadratic charge inherited from
   `ℚ(ζ₅) ⊃ ℚ(√5)`.
4. The ramified drain quantum will be represented by the integral element
   `√5 = 2φ - 1`; its norm is `-5`, so its absolute charge is `5`.
5. A primitive hypothetical Fermat solution will split on `5 ∣ c`.
   Each branch will be exposed as one named charged-descent theorem producing
   an iterable successor whose positive natural charge is strictly smaller.
   Repeated descent will close only through
   `Fermat.Conservation.impossible_of_strict_charge_drain`.
6. The public endpoint will be
   `Fermat.Five.holdsAt_five_conservation : Fermat.HoldsAt 5`.

## Predicted compiler pressure

- The exact pinned Mathlib representation and simplification lemmas for
  quadratic integers, norms, conjugation, and units will require small
  compile probes.
- The norm representation of the quintic cofactor is likely to require a
  non-obvious coordinate choice and an explicit polynomial identity.
- The hard seam will be turning the repository's Dirichlet arithmetic into
  two independently named, iterable charged steps without importing or
  citing any existing `Fermat.Five` implementation module.
- Unit normalization may alter representatives during descent.  The natural
  measure must therefore be absolute norm, so the proof remains invariant
  under the infinite gauge symmetry rather than choosing a bounded set of
  unit representatives.
- The implementation will patch the real downstream conservation theorem and
  compile its actual obligations.  A certificate, provider structure, or
  isolated harness will not replace either charged branch.

## Predicted audit

- The N5 cone will import `Fermat.Statement`,
  `Fermat.Conservation.Floor`, and bounded lower-level Mathlib algebra and
  arithmetic modules only.
- It will not import or cite `Fermat.Five.Dirichlet`,
  `Fermat.Five.Reduction`, `Fermat.Five.holdsAt_five`, or any repository
  declaration whose proof depends on that route.
- An executable isolated-import test will require all forbidden names to be
  unknown, auditing the transitive environment rather than source spelling
  alone.
- `Fermat.Five.Conservation.Verification` will run `#print axioms` for every
  public N5 theorem; each result must use at most the standard
  `[propext, Classical.choice, Quot.sound]` trio.
- The delivered cone will contain no `sorry`, `admit`, or added `axiom`;
  forbidden imports/names, whitespace, and the independent N5 Lake build
  must all be clean.
