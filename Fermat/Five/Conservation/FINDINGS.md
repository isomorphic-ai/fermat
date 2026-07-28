# N5 conservation findings

## 2026-07-28 — dependency and reconstruction boundary

- The repository's completed Dirichlet route is spread across ten modules
  under `Fermat/Five`: modular entry, generalized equation, half-sum
  coordinates, integer power splitting, golden-order fifth-power extraction,
  two descent recurrences, initial-state construction, and outer reduction.
  None of those modules may enter the N5 conservation import cone.
- Their implementation uses lower-level integer arithmetic plus
  `Fermat.Quadratic.GoldenUnits`.  The golden-order module does not import any
  `Fermat.Five` module; it supplies the maximal order, multiplicative norm,
  Pell classification of its infinite unit group, and fifth-power reduction
  of units.  It is therefore a provenance-clean algebraic input.
- The new proof will reconstruct the Dirichlet arithmetic locally, with
  attribution in the source header, while importing only
  `Fermat.Statement`, `Fermat.Conservation.Floor`,
  `Fermat.Quadratic.GoldenUnits`, and bounded Mathlib support.

## 2026-07-28 — literal gauge-invariant drain measure

- Each of the two historical normalized states carries a positive coordinate
  `s` divisible by `5`.  The proved arithmetic transformer returns the same
  kind of state with a new coordinate `s' < s`.
- Embed `s` into `ℤ[φ]` and define the state charge as absolute golden norm.
  Since `N(s) = s²`, the existing strict coordinate decrease becomes a
  strict decrease of the literal golden-ring charge `s²`.
- For every unit `u`, `N(u)` is an integer unit and hence has absolute value
  one.  Multiplicativity therefore gives
  `|N(u · x)| = |N(x)|`: the state measure survives arbitrary powers of the
  fundamental golden unit rather than choosing a finite representative set.
- The ramified element `√5 = 2φ - 1` has norm `-5` and absolute charge `5`.
  Its divisibility footprint is the persistent condition `5 ∣ s` in both
  descent families.
- The old implementation closes `s' < s` with a locally duplicated
  least-positive-coordinate argument.  The conservation reconstruction will
  instead package each family as an iterable state and invoke only
  `Fermat.Conservation.impossible_of_strict_charge_drain`.

## 2026-07-28 — repository state

- The current branch already contains a large set of unrelated untracked
  user files.  N5 changes and guarded commits will name only explicit
  conservation paths and will not stage or modify that work.
- The manifest drift affecting the repository's regular-prime development
  is unrelated to the N5 cone.  All acceptance builds will target the
  conservation modules directly.
