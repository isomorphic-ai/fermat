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

## 2026-07-27 — compiler-driven import repair

- Replacing `Fermat.Basic`'s umbrella import globally made the conservation
  boundary clean, but the first full build revealed that many unrelated
  legacy modules rely on that umbrella for undeclared Mathlib APIs.
- The narrow, non-disruptive boundary is therefore a new
  `Fermat.Statement` module. It owns `Fermat.HoldsAt` and
  `HoldsAt.mono_of_dvd` while importing only
  `Mathlib.NumberTheory.FLT.Basic`.
- `Fermat.Basic` now reexports `Fermat.Statement` while retaining its legacy
  umbrella import. Conservation imports `Fermat.Statement` directly and
  therefore never enters the contaminated legacy cone.

## 2026-07-27 — realized charge and descent

- `QuadraticAlgebra ℤ (-1) (-1)` is the provenance-clean coordinate model of
  `ℤ[ζ₃]` in the pinned Mathlib. Its built-in `QuadraticAlgebra.norm` is a
  monoid hom and specializes definitionally to `x² - xy + y²`.
- The conservation spine compiles with the actual algebraic norm:
  multiplicativity, the cubic ledger, `N(1 - ζ₃) = 3`, the charge formula
  `N((1 - ζ₃)^m) = 3^m`, strict drain, and the named no-infinite-drain floor
  are all proved.
- The complete Euler transformer was reconstructed locally from the clean
  cyclotomic `PID`, `Three`, and generic divisibility modules. Its native
  one-step theorem lowers the multiplicity `m` of `ζ₃ - 1`; the public
  conservation theorem maps this to a strict decrease of the literal norm
  charge `N((1 - ζ₃)^m)`.
- The whole cubic term's norm is not claimed to decrease. The conserved
  quantity that the classical Euler transformer controls is exactly the
  norm of its `λ`-primary component. This is enough to run an infinite
  charge drain and invoke the conservation floor.
- The final endpoint
  `Fermat.Three.holdsAt_three_conservation : Fermat.HoldsAt 3` compiles and
  reaches contradiction only through that charged descent.

## 2026-07-27 — audits and full-build status

- An isolated import test of `Fermat.Three.Conservation` leaves
  `fermatLastTheoremThree` unknown. This checks the transitive import cone,
  not merely the source text.
- `#print axioms` was run for every public theorem in `Fermat.Statement` and
  the conservation modules. Every result uses a subset of the standard
  `[propext, Classical.choice, Quot.sound]` baseline.
- The forbidden-name/import scan, the `sorry`/`admit`/`axiom` scan, and
  `git diff --check` are clean for the delivered modules.
- A bare full `lake build` was run. It built the complete N3 conservation
  cone and more than 9,300 project jobs. Its remaining non-N3 failures expose
  a pre-existing dependency mismatch: `lake-manifest.json` pins
  `flt-regular` at `edd24b3`, while existing project modules use APIs and
  `KummerFullValuation.lean` from the local, unpublished
  `remove-isregularprime` branch at `131f93e`. Lake correctly restores the
  manifest revision, where that source file is absent and the APIs still
  require the old regular-prime premise.
- One additional certificate was killed by the parallel pass with exit 137;
  rebuilding `Fermat.SixtySeven.VandiverDiagonalUnits67` alone succeeded.
  Thus the only terminal full-build blockers are the manifest/dependency
  mismatch, not this task's proof or a remaining resource failure.
