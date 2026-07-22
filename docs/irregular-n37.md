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
- `Fermat/Irregular/CyclotomicPlaces37.lean`,
  `Fermat/Irregular/CyclotomicSineProduct37.lean`, and
  `Fermat/Irregular/CyclotomicLogCofactor37.lean` give the complementary
  archimedean calculation.  They enumerate the eighteen real places, prove
  the half chord product directly from `Φ37(1) = 37`, and identify the fixed
  `17 × 17` sine determinant with `2¹⁷` times the norm of the product of
  the seventeen nontrivial Fourier coefficients.  Thus the remaining
  Sinnott--Kummer seam is specifically the analytic identification of those
  coefficients with the relevant Dirichlet `L`-values and class-number
  formula, not a finite determinant or indexing assertion.
- `Fermat/Irregular/CyclotomicDirichlet37.lean` carries that calculation to
  the exact per-character analytic boundary.  It identifies quotient-group
  characters with even Dirichlet characters modulo `37`, proves every
  nontrivial lift primitive, changes the Fourier coefficient into half of
  the classical 36-term chord-log sum, and proves the associated Gauss-sum
  norm is `sqrt 37`.  The remaining chord identity is named
  `ChordLogLValueFormula37`; with Mathlib's additive-character convention it
  is exactly
  `S(ψ) = -τ(ψ⁻¹) L(1,ψ)`.  From this single formula the file derives
  the expected `sqrt(37)¹⁷`-scaled product of the seventeen nontrivial even
  `L(1)`-values.

- `Fermat/Irregular/CyclotomicLValue37.lean` proves all but the
  analytic-continuation endpoint of that chord identity.  Dirichlet's test
  and Abel's limit theorem give the naturally ordered unit-circle series
  `sum z^n/n = -log(1-z)`; conjugate-root pairing recovers the real chord
  logarithms; and Mathlib's finite Fourier transform gives exactly the
  inverse-character Gauss sum, including its sign.  Consequently,
  `ChordLogLValueFormula37` now follows from the single named proposition
  `DirichletSeriesAtOneFormula37`, which says that these natural-order
  primitive Dirichlet series converge at `s = 1` to Mathlib's analytically
  continued `LFunction 1`.

There is not yet a public `Fermat.holdsAt_thirtySeven`.  Case II needs
Vandiver's irregular-prime criterion: if `37 ∤ h⁺` and none of the relevant
Bernoulli numerators is divisible by `37³`, then Case II is impossible.  The
entire Bernoulli condition and the residue-symbol-to-real-unit-index chain are
now kernel-checked.  Mathlib and `flt-regular` still contain neither
Vandiver's singular-primary-unit descent nor the Sinnott--Kummer index formula
that identifies this concrete relative index with the class number `h⁺`.
These final two global bridges must be formalized rather than assumed.  On
the circular-unit side, all finite Fourier, cofactor, place-ordering, and
trivial-character factors preceding that analytic identification are now
kernel-checked.

The exact primary source is H. S. Vandiver, *On Fermat's Last Theorem*,
Transactions of the AMS 31 (1929), 613–642,
[DOI 10.1090/S0002-9947-1929-1501503-0](https://doi.org/10.1090/S0002-9947-1929-1501503-0).
Vandiver restated the numerical criterion in his 1931 PNAS summary,
[DOI 10.1073/pnas.17.12.661](https://doi.org/10.1073/pnas.17.12.661).
