# N3 conservation findings

## 2026-07-27 — dependency boundary

- `Fermat.Basic` imported the `Mathlib` umbrella. In this pinned Mathlib,
  that umbrella reaches `Mathlib.NumberTheory.FLT.Three` and therefore
  introduces the forbidden declaration `fermatLastTheoremThree`.
- The definition actually needed by `Fermat.Basic`,
  `FermatLastTheoremFor`, lives in
  `Mathlib.NumberTheory.FLT.Basic`. That definition-only module is therefore
  the intended replacement import.
- `Fermat.Classical` directly imports
  `Mathlib.NumberTheory.FLT.Three` and exposes
  `Fermat.holdsAt_three`. It must not occur in the conservation import cone.
  The classical module itself will remain untouched.

## 2026-07-27 — provenance-clean descent source

- The pinned source
  `Mathlib.NumberTheory.FLT.Three` contains a complete Euler descent, but the
  module itself is forbidden because its public endpoint is precisely
  `fermatLastTheoremThree`.
- Its three non-FLT imports are
  `Mathlib.NumberTheory.FLT.Basic`,
  `Mathlib.NumberTheory.NumberField.Cyclotomic.PID`,
  `Mathlib.NumberTheory.NumberField.Cyclotomic.Three`, and
  `Mathlib.Algebra.Ring.Divisibility.Lemmas`. These are lower-level inputs;
  the import graph is acyclic and none is proved from the FLT(3) endpoint.
- Consequently the safe route is to reconstruct the needed descent under
  `Fermat.Three.Conservation` from those lower-level ingredients, with
  attribution, while never importing the forbidden `FLT.Three` module.
- Mathlib's existing descent measure is the multiplicity of
  `λ = ζ₃ - 1` in the cubic term. To make the requested conservation measure
  literal, the local proof will additionally expose the charge of the
  `λ`-primary component. Multiplicative conservation and `N(λ) = 3` turn a
  one-step multiplicity drop into a strict drop of that charge.

## 2026-07-27 — repository state

- The working tree already contains many unrelated untracked files. They are
  user work and are outside this task.
- All N3 changes will be restricted to explicit paths, and every guarded
  commit will name those paths rather than using a broad pathspec.
