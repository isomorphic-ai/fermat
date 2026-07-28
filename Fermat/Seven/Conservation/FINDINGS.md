# N7 conservation findings

## 2026-07-28 — the strict reconstruction boundary

- The completed repository proof of FLT(7) is a nine-file Lebesgue chain
  under `Fermat.Seven.Lebesgue`, totaling about 2,000 lines.  Its endpoint
  depends on the symmetric identities, primitive arithmetic, power
  allocation, final coprimality, final substitution, corrected descent, and
  outer reduction.  The useful descent transformer is private inside the
  old module.
- Since every classical `Fermat.Seven.*` implementation declaration is
  forbidden, the reliable boundary is a credited reconstruction of that
  chain under `Fermat.Seven.Conservation.Reconstruction`.  In particular,
  merely wrapping the old endpoint or importing one of its internal files
  would leave the forbidden route in the transitive environment.
- The old outer reduction imports `Fermat.Basic`, which exposes
  `Fermat.HoldsAt.mono_of_dvd`.  The reconstruction must instead use
  `Fermat.Statement.Basic`.
- The corrected Lebesgue transformer lowers the positive index in
  `DescentEquation (a + 1)` to `DescentEquation a`.  This is already the
  exact iterable state boundary needed to replace its strong-induction
  closure by the shared conservation floor.

## 2026-07-28 — the exact septic fold

- The campaign's historical `psi7` is the all-positive polynomial
  `X⁶ + X⁵Y + X⁴Y² + X³Y³ + X²Y⁴ + XY⁵ + Y⁶`.
- Its compressed identity is exactly
  `psi7 X Y = (X - Y)⁶ + 7XY(X² - XY + Y²)²`, and consequently it is the
  difference quotient
  `X⁷ - Y⁷ = (X - Y) * psi7 X Y`.
- The sum ledger therefore requires the sign substitution:
  `a⁷ + b⁷ = (a + b) * psi7 a (-b)`.  Using `psi7 a b` there would be
  false.  The equivalent compressed cofactor is
  `(a + b)⁶ - 7ab(a² + ab + b²)²`.
- The identity will be reconstructed locally with historical credit rather
  than importing `Fermat.ThirtySeven.NeighborFolding` or the exponent-14
  Dirichlet module, both of whose cones are too wide.

## 2026-07-28 — full rank-two gauge and the regulator

- Pinned Mathlib's Dirichlet unit theorem supplies
  `NumberField.Units.fundSystem`, a basis of the free unit quotient, and
  `exist_unique_eq_mul_prod`, the unique decomposition of every unit into
  torsion times powers of the complete fundamental system.
- For a seventh cyclotomic field, the cyclotomic embedding counts give no
  real places and three complex places, hence
  `NumberField.Units.rank K = 2`.  Thus the fundamental-system coordinate
  type has exactly two integer directions; this is a genuine full lattice,
  not two arbitrarily chosen units.
- `NumberField.Units.regulator` is literally the covolume of that unit
  lattice.  Mathlib also proves its positivity and identifies it with the
  regulator of `fundSystem`, so the N7 API can name the regulator without
  manufacturing an analytic surrogate.
- The two explicit circular units available elsewhere in the repository
  are not currently proved independent or of index one.  They will not be
  mislabeled as a fundamental system.  The abstract `fundSystem` is the
  honest full-gauge choice.
- The absolute integral norm charge is invariant under every ambient unit,
  hence under every pair of fundamental-unit exponents and also under the
  torsion factor.  This is stronger than invariance under two selected
  generators.

## 2026-07-28 — class number and drain quantum

- Mathlib has direct cyclotomic PID theorems only for conductors three and
  five.  The available seven-PID certificate lives in the external
  `flt-regular` package, so importing it would defeat the requested
  independence from that manifest.
- A local bounded reconstruction is small: the Minkowski bound has floor
  four, while the inertia degrees of `2` and `3` in
  `ℚ(ζ₇)` are respectively their orders modulo `7`, namely `3` and `6`.
  Their prime-ideal norms therefore exceed four.  Mathlib's Galois
  class-number criterion then proves the ring of integers principal and
  hence the class number equal to one.
- For `λ = 1 - ζ₇`, Mathlib directly computes the norm of `ζ₇ - 1` as
  seven.  Multiplication by the unit `-1` transfers this to the requested
  orientation, so the absolute charge of `λ` is exactly seven.

## 2026-07-28 — repository state

- The branch contains many unrelated untracked user files.  N7 work and
  guarded commits name only explicit N7 conservation paths and the public
  facade; none of that unrelated work will be staged or modified.

## 2026-07-28 — realized charged descent

- The compiler-driven repair kept the corrected private Lebesgue
  transformer intact and removed the public strong-induction closure at its
  source.  A `ChargedState` now carries precisely its positive index, odd
  pairwise-coprime entries, and `DescentEquation`.
- Its charge element in a seventh cyclotomic field is literally
  `(1 - ζ₇) ^ index`; hence its absolute integral norm charge is `7 ^ index`.
  The corrected transformer lowers the index, so the charge drops strictly.
  At index one, the existing modulo-eight contradiction supplies the floor
  case.  The shared `impossible_of_strict_charge_drain` theorem is now the
  only public closure.
- The transformer's four first-stage allocations all enter that one step:
  the first allocation constructs the lower-index state, while the other
  three are eliminated by the original, corrected arithmetic.  Thus every
  surviving state has a strict charged successor.
- State-level gauge invariance is stated with concrete `ℤ × ℤ`
  coordinates obtained from the complete Dirichlet fundamental system.
  This is where rank two bites in the executable descent API: either
  fundamental-unit exponent may change the representative without changing
  the norm charge used by the floor.

## 2026-07-28 — exact outer branches and ledger flow

- The outer proof now performs an explicit split on `7 ∣ t x y z`.
  The exceptional branch stores the exact symmetric definition, product
  equation, coprimalities, congruence, sign, and divisibility data in
  `SevenDvdTBranchState`.  Its local allocation contradiction supplies the
  impossible strict-successor obligation for a literal `λ¹` charge, and its
  named closure invokes the same shared conservation floor.
- The ordinary branch consumes `7 ∤ t` at the power-allocation seam rather
  than silently re-proving it.  It constructs a `ChargedState` through the
  full substitution and sends that state to the iterable strict drain.
- The ternary equation is first rewritten as
  `(x + y) * psiSeven x (-y) + z ^ 7 = 0`; both branch lemmas accept this
  exact signed septic ledger and recover the seventh-power equation from
  the proved ledger identity.  The campaign fold is therefore on the
  downstream proof path rather than a detached polynomial lemma.

## 2026-07-28 — integration and external drift

- The isolated target `Fermat.Seven.Conservation` builds successfully from
  the strict cone.  The repository's main `Fermat.holdsAt_seven` alias now
  points to `Fermat.Seven.holdsAt_seven_conservation`, and its direct import
  of the earlier Lebesgue implementation has been removed.
- A full `lake build Fermat` still reaches the pre-existing external
  `flt-regular` drift: its pinned checkout lacks
  `FltRegular/NumberTheory/KummerFullValuation.lean`, and existing
  `Fermat.Cases` / `Fermat.Regular.KummerCriterion` calls no longer match
  the dependency API.  The N7 cone imports none of those modules and builds
  independently of those failures.  The diagnostic run was stopped after
  those errors and an unrelated large Vandiver module was killed with exit
  code 137; continuing it could not validate N7 any further.

## 2026-07-28 — executable audit

- `Verification.lean` contains 70 exact `#print axioms` guards: every one
  of the 68 public N7 theorems plus the two shared conservation-floor
  theorems.  Sixty-two use the full standard trio, four use
  `[propext, Quot.sound]`, and four use `[propext]`; no theorem exposes any
  additional axiom.
- Forty-eight guarded forbidden-name checks cover the earlier Lebesgue and
  Lamé implementations, the old root endpoint, `HoldsAt.mono_of_dvd`, all
  seven Ladder folds and representative transports, the external
  class-number shortcut, and fixed-exponent FLT sentinels.  All remain
  unknown under the isolated public N7 import.
- The executable verification leaf passes both direct Lean compilation and
  its Lake target (`3497/3497` jobs).  The public cone itself passes
  `lake build Fermat.Seven.Conservation` (`3496/3496` jobs).
