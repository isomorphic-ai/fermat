# Power-root cube findings

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
