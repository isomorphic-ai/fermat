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
  phase as the actual circular-unit residue matrix;
- `CircularUnitProjectionReceipt1831AtQ358877.lean` and
  `CircularUnitProjectionReceipt1831AtQ18311.lean` compile the two
  q-dependent receipts into the same q-free projection-kernel theorem;
- `CircularUnitProjectionReceipt1831.lean` is the neutral production
  selector. It currently uses the smaller prime, and can switch providers
  without changing its public theorem or any downstream proof.

The selective descent proves that only the Fourier channel reflected from
the possible irregular Bernoulli index `1274` is required. The two split
primes give different nonzero scalars (`882` and `1165`) multiplying the same
canonical Kummer row, so their selected detector kernels agree. Notably, the
full `q = 18311` matrix is singular at regular frequency `636`; it succeeds
only through the sharper characterwise endpoint.

The reusable proof is now prime-generic.  Given any checked
`CircularUnitResidues.Certificate p q`,
`AuxiliaryResidueCharacterFactorization.lean` constructs, for every even
character row, an equality

```text
q-dependent residue detector
  = q-dependent orbit scalar * intrinsic Kummer channel.
```

The intrinsic channel is defined on the real residue group
`(ZMod p)ˣ / {±1}` and is independent of `q`.  The finite certificate still
authenticates the chosen reduction root and residue matrix; the theorem does
not turn primality of `q` alone into a receipt.

`AuxiliaryResidueCharacterNaturality.lean` composes the convention laws.  If
the primitive residue root changes from `root` to `root^a`, the phase is
reindexed by `a` and rescaled by `a⁻¹`; the orbit scalar acquires the explicit
nonzero factor `a⁻¹ χ(a)`.  Therefore the detector zero locus is unchanged,
even when its q-dependent orbit scalar happens to vanish.  Separately,
`CyclotomicEvaluationNaturality.lean` identifies every prime above a split
`q` with one of the explicit evaluation kernels.

At exponent `1831`, `CircularUnitChannelCoordinates.lean` contains only the
shared p-dependent character coordinates.  The separate
`CircularUnitChannelAtQ358877.lean` and
`CircularUnitChannelAtQ18311.lean` adapters transport their own stored phase
receipts through the generic constructor.  Kummer row `636`, Bernoulli index
`1274`, inverse Fourier frequency `278`, and Lean slot `277` are proved to be
the same character.  The resulting detectors are exactly `882 * projection`
and `1165 * projection`; Lean proves the second equals `1195` times the first
and hence has the same kernel.  More strongly, multiplying by `882⁻¹` and
`1165⁻¹` respectively makes both normalized detectors literally equal to
`projection`. `CircularUnitResiduesChannelsIntrinsic.lean` consumes only a
normalized projection theorem as an argument; the one-line
`CircularUnitResiduesChannelsNormalized.lean` assembly selects provenance.
