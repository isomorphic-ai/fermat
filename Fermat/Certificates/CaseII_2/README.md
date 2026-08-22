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
identify externally supplied numbers with Bernoulli coefficients.  For 1381,
two kernel-checked low contacts at indices `266` and `1646` authenticate the
weight.  Sun's depth-two Bernoulli interpolation then transports them to the
lifted index `367346` and proves that its normalized residue is exactly `561`.
No power sum at the lifted index is evaluated, and the receipt avoids imports
of the older exponent-local Faulhaber certificate modules.
