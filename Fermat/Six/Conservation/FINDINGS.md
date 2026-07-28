# N6 conservation findings

## 2026-07-28 — the statement boundary had to be cut

- `Fermat.Statement` originally defined both the proposition
  `Fermat.HoldsAt` and the forbidden transport
  `Fermat.HoldsAt.mono_of_dvd`.  Consequently no module could state the
  requested N6 endpoint while also making the transport unknown.
- The proposition now lives in the narrower
  `Fermat.Statement.Basic`; the existing `Fermat.Statement` facade imports
  that boundary and retains the transport theorem for its old consumers.
  Thus the real dependency was removed at its source without breaking the
  existing downstream modules.
- Public N4 conservation is also too wide because its assembly imports
  `Fermat.Statement`, although its internal `Spine` and `Descent` modules
  are provenance-clean.  Public N5 is unsuitable for this stricter cone:
  besides the old statement boundary, its golden-order dependency begins
  with a bare `Mathlib` import and transitively exposes fixed-exponent
  theorems.  N6 therefore imports neither public rung.

## 2026-07-28 — the two native ledgers meet

- The correct integral sixth-root model is
  `QuadraticAlgebra ℤ (-1) 1`.  Its generator satisfies the sixth-root
  relation and its norm is
  `N(x + yζ₆) = x² + xy + y²`.
- The element `a² - b²ζ₆` has norm
  `a⁴ - a²b² + b⁴`, giving the native factor ledger
  `a⁶ + b⁶ = (a² + b²) N(a² - b²ζ₆)`.
- The ramified element `1 + ζ₆` has norm `3`; its `m`th power therefore
  carries the literal native charge `3^m`.
- The same sixth-power equation is definitionally both a Pythagorean triple
  on cube coordinates and a cubic equation on square coordinates:
  `(a³)² + (b³)² = (c³)²` and
  `(a²)³ + (b²)³ = (c²)³`.
  This is the exact typed point where the balance and cyclotomic views meet.

## 2026-07-28 — proposition fold versus state fold

- The known cyclotomic transformer does not preserve the subspace in which
  all three cubic coordinates are squares.  After its first step the
  iterable state is a generalized unit-twisted cubic state.  Thus the prime
  fold is genuinely forced as a change of *state coordinates*.
- It is not necessary to manufacture, assume, or prove the universal
  exponent-3 Fermat proposition.  For a primitive sixth-power solution,
  reduction modulo `9` selects exactly one of `a` and `b` as divisible by
  `3`, while `c` and the other base are not divisible by `3`.
- If `3 ∣ a`, the direct seed is
  `(b², -c², a², -1)`; if `3 ∣ b`, it is
  `(a², -c², b², -1)`.  In either case its unit-twisted cubic equation is
  merely the original sixth-power equation rearranged.  Pairwise
  coprimality and the required ramified divisibility follow from primitive
  N6 data.
- The implementation therefore targets rung (a): reconstruct only the
  charged state transformer below N6, seed it directly from sixth-power
  data, and close it through the shared conservation floor.  The result
  should simultaneously record the framework-level finding that composite
  conservation composes through a prime-shaped state space even when no
  prime-exponent theorem statement enters the cone.

## 2026-07-28 — repository state

- The branch contains many unrelated untracked user files.  N6 work and
  guarded commits name only the statement boundary and explicit N6
  conservation paths; none of that unrelated work is staged or modified.
