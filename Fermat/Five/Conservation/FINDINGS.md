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

## 2026-07-28 — realized infinite gauge and ledger

- The spine and the fifth-power extraction now use one literal ring:
  `Fermat.Quadratic.Golden.MaximalOrder`.  This avoids an artificial
  equivalence boundary between two presentations of `ℤ[φ]`.
- Distinct natural powers of the golden unit are separated by the real
  embedding and strict growth of the positive golden ratio.  Thus
  `infinite_goldenUnitGroup` formally witnesses the infinite gauge group,
  rather than leaving infinitude as prose.
- Every unit has signed norm `1` or `-1`, so the named theorem
  `charge_gauge_invariant` proves
  `|N(u · z)| = |N(z)|` for every unit `u`.
- The quartic cofactor is exactly the norm of the golden element
  `⟨a² + b², -ab⟩`; consequently `quintic_ledger` states the requested
  factorization directly as a norm ledger.
- The ramified element is literally `⟨-1, 2⟩ = 2φ - 1`.  It squares to `5`,
  has signed norm `-5`, and carries absolute charge `5`.

## 2026-07-28 — provenance-clean Dirichlet reconstruction

- The arithmetic of the repository's earlier ten-file Dirichlet route was
  reconstructed under
  `Fermat.Five.Conservation.Reconstruction`, with credit in every source
  header.  No old `Fermat.Five` implementation module or declaration is
  imported or cited.
- The original split on the Fermat right-hand base and the later parity
  split are distinct.  When `5 ∣ c`, division of that visible factor seeds
  `FifthEquation a b z` directly.  When `5 ∤ c`, the modulo-`25` lemma
  forces `5` into `a` or `b`, and a signed permutation seeds the same
  generalized equation.
- A generalized equation then reaches either the odd-coordinate or
  opposite-parity historical state.  Their reconstructed recurrence
  theorems produce a state of the same family with `s' < s`.

## 2026-07-28 — realized charged branches and final assembly

- `ChargedState` is the disjoint union of the two internal parity families.
  Its charge element is the rational integer `s` embedded in `ℤ[φ]`, and
  `stateCharge_eq_coordinate_sq` proves that its absolute norm charge is
  exactly `s²`.
- The strict coordinate result `s' < s` therefore becomes a strict decrease
  of the literal golden-ring norm charge.  State-level gauge theorems prove
  that arbitrary unit normalization leaves this measured charge unchanged.
- `NotFiveDvdCState` and `FiveDvdCState` retain the original primitive
  solution and, respectively, the exact propositions `5 ∤ c` and `5 ∣ c`.
  Their public charged-descent lemmas preserve those tags while advancing
  the internal parity state.
- The copied least-positive-coordinate closures were removed entirely.
  `not_five_dvd_c_impossible` and `five_dvd_c_impossible` each invoke
  `Fermat.Conservation.impossible_of_strict_charge_drain` directly, so both
  branches meet the same shared conservation floor.
- `Fermat.Five.holdsAt_five_conservation` reconstructs pairwise
  coprimality, records the Fermat equation in ledger form, performs an
  actual `by_cases (5 : ℤ) ∣ c`, and dispatches to those two independently
  floor-closed branches.  The complete endpoint builds successfully.
