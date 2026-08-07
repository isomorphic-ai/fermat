# Power-root cube findings

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
- Therefore the cube lands in **typed outcome 4**: the two selected readings
  do not factor through the same obstruction, and the wild arithmetic route
  is genuinely necessary.  The reflected `χ*`/Tate-twist carrier gap from
  the prediction is real, but it occurs on the wild pairing route and does
  not turn the two allocated ideal roots into same-input naturality
  composites.

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
