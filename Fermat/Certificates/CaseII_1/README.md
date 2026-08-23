# Case II.1 certificates

This directory owns finite receipts for the plus-class/principalization leg
of Case II.

For exponent `1831`, two certificate styles coexist:

- `CircularUnitFourierFactors1831.lean` and
  `CircularUnitCertificateFactored1831.lean` retain the complete
  `914`-frequency determinant receipt at `q = 358877`;
- `CircularUnitIrregularChannel1831.lean` retains only the frequency-`278`
  receipt at `q = 358877`;
- `CircularUnitIrregularChannel1831AtQ18311.lean` checks the same frequency
  at the second split prime `q = 18311`;
- `CircularUnitResidueCertificate1831AtQ18311.lean` authenticates the latter
  phase as the actual circular-unit residue matrix.

The selective descent proves that only the Fourier channel reflected from
the possible irregular Bernoulli index `1274` is required. The two split
primes give different nonzero scalars (`882` and `1165`) multiplying the same
canonical Kummer row, so their selected detector kernels agree. Notably, the
full `q = 18311` matrix is singular at regular frequency `636`; it succeeds
only through the sharper characterwise endpoint.
