# Power-root cube findings

## 2026-08-07 — final verification

- The W1/W2 target build, the W3 target build, generic
  `LinkingVerification`, generic `Credit.Verification`, and selected
  `FiftyNine.Conservation.Verification` are green.  The combined full
  verification command covering all nine repository verification leaves
  completed successfully at 8,714 jobs.
- The executable audit now checks every new public theorem's proof-value
  wiring, the generator-backed `toClass` kernel/range derivation, the actual
  principal-arrow `rho`, the four-way selected classification, the wild
  comparison, and the Bockstein observation.  The no-product-equivalence
  scan, generic no-59 scan, forbidden declaration checks, and standard axiom
  trio all pass.
- A broader unscoped `lake build` was also attempted, but the existing
  repository baseline is not globally buildable: the external
  `flt-regular` package is missing
  `FltRegular/NumberTheory/KummerFullValuation.lean`, and unrelated
  `Fermat/Core/Cases.lean` / `Fermat/Descent/Regular/KummerCriterion.lean` sources already
  mismatch that package API; a separate large Vandiver target was killed by
  the OS with exit code 137.  Those files are outside this task and were not
  changed.  The requested complete verification cone itself is green.

## 2026-08-07 — implemented cube

- W1 now uses the actual principal-ideal arrow as a two-term complex.  The
  kernel is canonically the unit group, the cokernel is canonically the class
  group, and the power-layer Selmer middle is retained in the named
  `principalIdealExtensionClass`.  Its public data are inclusion, projection,
  injectivity, middle exactness, and surjectivity only: no section,
  retraction, or product equivalence is present.  The permanent declaration-
  type audit rejects any public equivalence whose type also contains a
  product.
- The old local root-ideal calculation in `SelmerSequence` has been replaced
  at its source by the generator derivation from integration commit
  `889be7a3fee66e6630d25332a501409fa35d8590`.  Apart from the recorded
  module/export compatibility changes, the only elaboration delta is an
  explicit quotient carrier argument needed on the pinned Lean 4.31 API.
- W2 proves functorial root and obstruction laws for every commuting arrow
  square.  It exposes `root_mul` and `root_shift` as the multiplication and
  representative-change engines, constructs the Delta basis action, types
  reflection through equivalences, and leaves the unavailable localization
  carrier behind `LocalizationInterface` and `ObstructionSquareLaw`.
- `LinkingInterfaces.ArithmeticRepresentation.rho` now acts by endomorphisms
  of the actual principal-ideal arrow, so preservation of the arrow, root,
  and obstruction squares is derived.  The old reflected-Selmer pair action
  is separately named `selmerAction`; no class-group guess is used to define
  `rho`.
- W3 distinguishes a genuine same-input PowerRoot face from the selected
  conductor-59 route.  The generic face commutes, while the selected record
  retains allocation sources `0` and `1` and the concrete comparison remains
  the wild reflected-dual Tate readout.  Outcome 4 is therefore a statement
  about the provenance of the implemented routes, not a universal
  nonexistence theorem or an inequality of scalar values.
- The named `BocksteinPowerRootReceiptObservation` retains the formal
  integral correction `59 • r1`, proves only that its reduction vanishes in
  the known 59-torsion layer, carries the existing `mu_59_to_the_n` risk, and
  records the two-2s correspondence as open.

## 2026-08-07 — decisive test: outcome 4

- The committed outcome-3 guess is false.  The selected `r0` and `r1` are
  `pair.ledger.rootClass 0` and `pair.ledger.rootClass 1`: class shadows of
  two separately allocated conjugate ideal roots.  They are not the two
  composites of one global element around a localization square.
- For the principal-ideal power-root obstruction, the candidate routes
  `obstruction_local (localize x)` and
  `localize (obstruction_global x)` do factor through the same generic
  obstruction and belong to the localization naturality interface.  At a
  principal local fractional-ideal carrier their class shadow is zero, so
  their defect cannot equal the potentially nonzero selected gauge without
  already proving relation (7a).
- The actual wild local reading in `TateBridge.GaugeComparison` factors
  through a bilinear reflected-dual Tate/Hilbert-symbol carrier and is linked
  to the selected class gauge only by an explicit readout and zero-reflection
  law.  `GlobalReciprocityLaw` sums those pairing readings; it is not a
  naturality 2-cell for the principal-ideal obstruction.
- Therefore the cube lands in **typed outcome 4**: the two implemented
  selected readings are not constructed as the two sides of one same-input
  obstruction square, and the wild arithmetic route is genuinely necessary
  for the current Stage 3 comparison.  This does not prove universal
  nonfactorization or exclude accidental equality after another readout.
  The reflected `χ*`/Tate-twist carrier gap from the prediction is real, but
  it occurs on the wild pairing route and does not turn the two allocated
  ideal roots into same-input naturality composites.

## 2026-08-07 — upstream generator discovery

- The generic contribution is the complete file
  `Mathlib/GroupTheory/PowerRootObstruction.lean`, added at commit
  `4ea7450c8a5844417866addb7fba766275a1945a`.  Its source-file SHA-256 is
  `44c80744a6c74bf4793cb45c7289f54512b43e6326c0ef46aac308f9cfb31d25`.
  The branch contains no later edits to that file.
- Commit `889be7a3fee66e6630d25332a501409fa35d8590` then refactors the Dedekind
  Selmer sequence to instantiate the generic generator at the principal-ideal
  map.  The refactored `SelmerGroup.lean` source has SHA-256
  `a6fb493fdaf8686eed654b4b0f7abe84ef14d4198304ef4dcf9f8160c8afd2f6`.
- The generator already proves the exact laws requested by the cube:
  `root_mul` makes the root a homomorphism, `root_shift` controls a change of
  representative by an `n`-th power, `obstruction_ker` identifies the unit
  side, and `obstruction_range` identifies the torsion component shadow.
  Thus W1/W2 should instantiate and expose these laws, rather than recreate a
  root-ideal calculation or install a new arithmetic premise.
