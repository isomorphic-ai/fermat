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
- Inside the same typed ring, `embeddedCubeRoot = -ζ₆` has cube one and
  `embeddedCubeRoot - 1 = -(1 + ζ₆)`.  Thus the arithmetic descent prime
  and the native degree-six drain quantum differ by the unit `-1`; the
  shared-field identification is not merely prose.
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

## 2026-07-28 — realized neutral transformer

- `Fermat.Conservation.CubicChargedDescent` reconstructs only the arithmetic
  state transformer: a concrete `RawState`, its `λ² ∣ a + b` orientation,
  the ramified multiplicity, and a successor with strictly smaller
  multiplicity.  It contains no universal cubic impossibility proposition
  and no fixed-exponent endpoint.
- The neutral layer imports only lower cyclotomic PID, local
  third-cyclotomic arithmetic, and generic divisibility modules.  It does
  not import any repository exponent-three module or Mathlib fixed-exponent
  FLT module.
- The transformer necessarily allows a unit coefficient in
  `a³ + b³ = u c³`; this is the exact state-space enlargement discovered
  above.  Its public proof endpoints use exactly the standard axiom trio.

## 2026-07-28 — realized direct N6 seed and floor closure

- `PrimitiveSolution` packages nonzero primitive integer data at exponent
  six.  The equation itself proves pairwise coprimality, closes the native
  norm ledger, and supplies the Pythagorean triple of cubes.
- An exhaustive `ZMod 9` computation proves that a primitive solution has
  exactly one ramified leg.  The two literal square-coordinate seeds are
  implemented as predicted:
  `(b², -c², a², -1)` when `3 ∣ a`, and
  `(a², -c², b², -1)` when `3 ∣ b`.
- Norm divisibility transports `3 ∤ x` to
  `(ζ₃ - 1) ∤ x²`, while ramification transports `3 ∣ x` to
  `(ζ₃ - 1) ∣ x²`.  Pairwise coprimality survives integer casting,
  squaring, and the sign on the second coordinate.
- The raw state is oriented, every successor lowers its ramified
  multiplicity, and `drainCharge_lt` turns that into strict loss of the
  literal native sixth-root norm charge
  `N((1 + ζ₆)^m) = 3^m`.
- `PrimitiveSolution.impossible_conservation` invokes only
  `Fermat.Conservation.impossible_of_strict_charge_drain`.
  Primitive normalization then yields the compiled public endpoint
  `Fermat.Six.holdsAt_six_conservation : Fermat.HoldsAt 6`.
- The pre-registered rung (b) was therefore conservative.  The realized
  deliverable is rung **(a)**: the cone contains no exponent-three Fermat
  statement and no exponent transport.  The prime fold appears as a
  necessary internal state-coordinate law, not as a premise or theorem
  shortcut.

## 2026-07-28 — executable verification

- The independent build of the statement-only boundary, shared floor,
  neutral charged transformer, every N6 layer, public assembly, and
  `Fermat.Six.Conservation.Verification` completed successfully with 3,484
  jobs.
- The verification leaf contains 28 exact guarded `#print axioms` checks:
  both floor theorems, all public N6 theorems, both public neutral-transformer
  endpoints, and the final fixed-exponent theorem.  Every result uses a
  subset of `[propext, Classical.choice, Quot.sound]`.
- Thirty-nine executable unknown-name guards cover Mathlib and repository
  exponent-three statements, Mathlib FLT(4) sentinels, the forbidden
  `Fermat.HoldsAt.mono_of_dvd`, every universal Ladder fold sentinel, and
  every current fixed-exponent Ladder transport.  All guards pass after
  importing only `Fermat.Six.Conservation`.
- Direct source/import scans find no forbidden fixed-exponent import,
  repository exponent-three or Ladder import, transport citation,
  placeholder, or added axiom.  The committed-range and N6-path whitespace
  checks are clean.
- A full root-library build was also attempted.  It reached the known
  unrelated `flt-regular` dependency drift: the pinned package lacks
  `FltRegular/NumberTheory/KummerFullValuation.lean`, and its current
  `caseI`/`flt_regular` APIs no longer match existing repository callers.
  The isolated N6 cone and its executable verification remain green
  independently of those pre-existing root failures.
