# Fermat: classical fixed-exponent proofs in Lean

This project formalizes the complete classical exponent-specific proofs of
Fermat's Last Theorem for:

- `n = 3`
- `n = 4`
- `n = 5`
- `n = 7`
- `n = 14`

The scope follows the historic source archive in `../fermat-data`. It excludes
Wiles/Taylor–Wiles, modularity, elliptic curves, Kummer's general regular-prime
theory, broad computational verification, and first-case-only results.

The common theorem statement is `Fermat.HoldsAt n`, an abbreviation for
mathlib's `FermatLastTheoremFor n`. Mathlib already contains complete descent
proofs for `n = 3` and `n = 4`; this project reuses those checked proofs and
focuses its new work on `n = 5` and `n = 7`.

The exponent-five result follows Dirichlet's completed 1828 proof, including
both historical parity branches and the exact denominator-`16` descent. It is
exposed as `Fermat.holdsAt_five` and
`Fermat.Five.Dirichlet.holdsAt_five_dirichlet`; see
`docs/dirichlet-n5.md` for the page-level source ledger and the modern
maximal-order and Pell-unit repairs.

The exponent-seven result follows Lebesgue's 1840 proof together with his
published Addition. The Addition repairs the third of the four allocations
that the original note incorrectly dismissed. The checked result is exposed
as `Fermat.holdsAt_seven` and
`Fermat.Seven.Lebesgue.holdsAt_seven_lebesgue`; see
`docs/lebesgue-n7.md` for the exact descent ledger and the repaired branch.

The `n = 14` result follows from the `n = 7` result by divisibility of
exponents. The project also contains a complete formalization of Dirichlet's
original, independent 1832 descent for `n = 14`, exposed as
`Fermat.holdsAt_fourteen` and
`Fermat.Fourteen.Dirichlet.holdsAt_fourteen_dirichlet`; see
`docs/dirichlet-n14.md` for its proof ledger and the unit-sign correction
needed by the historical argument.

## Build

```bash
lake exe cache get
lake build
```
