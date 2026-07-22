# Fermat: classical fixed-exponent proofs in Lean

This project formalizes the complete classical exponent-specific proofs of
Fermat's Last Theorem for:

- `n = 3`
- `n = 4`
- `n = 5`
- `n = 7`
- `n = 11`
- `n = 13`
- `n = 14`

The scope follows the historic source archive in `../fermat-data`. It excludes
Wiles/Taylor–Wiles, modularity, elliptic curves, and broad computational
verification. Work on the first irregular exponent `n = 37` is tracked
honestly as infrastructure until its global Case-II bridges are complete.

The common theorem statement is `Fermat.HoldsAt n`, an abbreviation for
mathlib's `FermatLastTheoremFor n`. Mathlib already contains complete descent
proofs for `n = 3` and `n = 4`; this project reuses those checked proofs and
focuses its new work on the uploaded historical and cyclotomic fixed-exponent
proofs.

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

The exponent-11 and exponent-13 results use kernel-checked class-number-one
certificates and the formal Lamé--Kummer descent supplied by `flt-regular`.
They are exposed as `Fermat.holdsAt_eleven` and `Fermat.holdsAt_thirteen`.
The alternative seven-fold packages retain the neighbor closures, exact
quadratic-period and secondary composition identities, and direct finite
Faulhaber certificates for every low Bernoulli numerator.  These are exposed
through `Fermat.holdsAt_eleven_sevenFold`,
`Fermat.holdsAt_thirteen_sevenFold`, and the corresponding
`Eleven.SevenFold` and `Thirteen.SevenFold` namespaces.  The Faulhaber branch
does not import Kummer's congruence; the class-number-one branch is the first
sufficient branch for the final descent.

For exponent 37, Case I and every Bernoulli numerator condition in
Vandiver's criterion are formalized; the latter are now proved directly by
finite Faulhaber computations, without assuming Kummer's congruence. The
uploaded circular-unit matrix has also been realized by concrete corrected
residue homomorphisms, proving that its relative index in the real-unit
group is prime to `37`. The complete per-character analytic calculation is
also checked: the natural Dirichlet series at `s = 1` is proved to converge
to Mathlib's continued `LFunction 1`, closing the chord-log Fourier identity.
There is deliberately no public
`Fermat.holdsAt_thirtySeven` yet; see `docs/irregular-n37.md` for the exact
remaining theorem boundary.

## Build

```bash
lake exe cache get
lake build
```
