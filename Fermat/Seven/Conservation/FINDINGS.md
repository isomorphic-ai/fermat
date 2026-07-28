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
