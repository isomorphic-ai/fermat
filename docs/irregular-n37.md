# Exponent 37: formalization status

The uploaded `flt_37_neighbor_folding` package has two logically distinct
layers.  The repository keeps them separate:

- `Fermat/ThirtySeven/NeighborFolding.lean` checks the exact quadratic and
  cubic orbit folds, including the literal exponent-13 factor and the joint
  exponent-11/exponent-7 factors.
- `Fermat/SophieGermain.lean` proves the general auxiliary-prime criterion,
  and `Fermat/ThirtySeven/FirstCase.lean` checks its exact `q = 149`
  hypotheses.  This completes Case I for exponent 37.
- `Fermat/ThirtySeven/ArithmeticCertificate.lean` proves the exact value of
  `B₃₂`, its 37-adic valuation-one certificate, the normalized primary
  quotient, and the independent `2³⁶ mod 37²` check.

There is not yet a public `Fermat.holdsAt_thirtySeven`.  Case II needs
Vandiver's irregular-prime criterion: if `37 ∤ h⁺` and none of the relevant
`Bₙ₍` is divisible by `37³`, then Case II is impossible.  The uploaded
finite data is consistent with that theorem, but Mathlib and `flt-regular`
currently contain neither Vandiver's singular-primary-unit descent nor the
circular-unit index theorem that converts the residue-symbol determinant
into `37 ∤ h⁺`.  Those bridges must be formalized rather than assumed.

The exact primary source is H. S. Vandiver, *On Fermat's Last Theorem*,
Transactions of the AMS 31 (1929), 613–642,
[DOI 10.1090/S0002-9947-1929-1501503-0](https://doi.org/10.1090/S0002-9947-1929-1501503-0).
Vandiver restated the numerical criterion in his 1931 PNAS summary,
[DOI 10.1073/pnas.17.12.661](https://doi.org/10.1073/pnas.17.12.661).
