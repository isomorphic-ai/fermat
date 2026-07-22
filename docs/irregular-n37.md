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
  `B₃₂`, its 37-adic valuation-one certificate, the complete scan showing
  that `32` is the unique irregular index, the normalized primary quotient,
  and the independent `2³⁶ mod 37²` check.
- `Fermat/Irregular/BernoulliData.lean` derives denominator control from
  Mathlib's public von Staudt--Clausen theorem and connects rational 37-adic
  valuations to divisibility of reduced numerators.
- `Fermat/ThirtySeven/HighBernoulli.lean` proves
  `v₃₇(B₁₁₈₄) = 2` by Faulhaber's formula and a 37-term computation
  modulo `37⁴`; it does not expand the 2190-digit Bernoulli numerator.
- `Fermat/Irregular/KummerCongruence.lean` formalizes the exact rational
  congruence interface and proves that it automatically handles every regular
  Vandiver index.  The interface is clearly marked as awaiting the actual
  Voronoi--Kummer theorem.
- `Fermat/Irregular/VandiverData.lean` and
  `Fermat/ThirtySeven/VandiverData.lean` combine that reduction with the
  unique-index scan and the `B₁₁₈₄` certificate.
- `Fermat/ThirtySeven/DirectVandiverData.lean` goes further and proves all
  seventeen required Bernoulli numerator conditions directly by Faulhaber's
  formula.  It needs no Kummer-congruence hypothesis and handles the
  exceptional denominator of `B₇₂` explicitly.
- `Fermat/Irregular/CircularUnits.lean` and
  `Fermat/Irregular/CircularUnitIndex.lean` prove the generic
  residue-determinant-to-unit-index bridge and define the seventeen concrete
  normalized circular units.  The finite certificate modules check an
  explicit inverse of the uploaded `17 × 17` matrix and all 289 of its
  finite-field entries.
- `Fermat/ThirtySeven/ResidueHomomorphisms.lean` constructs the actual
  characteristic-149 specializations and residue characters.  A
  complex-conjugation correction makes the characters vanish on all roots
  of unity while preserving the matrix entries on real circular units.  The
  resulting theorem proves that the circular-unit relative index inside the
  real-unit group is prime to `37`.

There is not yet a public `Fermat.holdsAt_thirtySeven`.  Case II needs
Vandiver's irregular-prime criterion: if `37 ∤ h⁺` and none of the relevant
Bernoulli numerators is divisible by `37³`, then Case II is impossible.  The
entire Bernoulli condition and the residue-symbol-to-real-unit-index chain are
now kernel-checked.  Mathlib and `flt-regular` still contain neither
Vandiver's singular-primary-unit descent nor the Sinnott--Kummer index formula
that identifies this concrete relative index with the class number `h⁺`.
These final two global bridges must be formalized rather than assumed.

The exact primary source is H. S. Vandiver, *On Fermat's Last Theorem*,
Transactions of the AMS 31 (1929), 613–642,
[DOI 10.1090/S0002-9947-1929-1501503-0](https://doi.org/10.1090/S0002-9947-1929-1501503-0).
Vandiver restated the numerical criterion in his 1931 PNAS summary,
[DOI 10.1073/pnas.17.12.661](https://doi.org/10.1073/pnas.17.12.661).
