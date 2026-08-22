# Case II.2 certificates

Finite exponent-specific receipts for the lifted-Bernoulli, diagonal-unit,
and Vandiver-Lemma-II leg of Case II belong here. Existing files remain at
the exponent root until that proof family receives its own structural
migration.

The exponent-1381 moment route is split into:

- `BernoulliMomentCertificate1381.lean`, which checks the one-channel
  weighted moment, authenticates its weight `561`, and proves the complete
  Bernoulli cube condition;
- `RegularizedKummerEndpoint1381.lean`, which feeds that condition into the
  normalized Kummer unit-extraction route and proves `Fermat.HoldsAt 1381`.

The determinant compresses simultaneous nonvanishing; it does not by itself
identify externally supplied numbers with Bernoulli coefficients.  The 1381
receipt therefore retains one kernel-checked modular power-sum equality as
the weight-provenance bridge, while avoiding imports of the older
exponent-local Faulhaber certificate modules.  Replacing that bridge with a
higher Kummer interpolation checker is an independent future optimization.
