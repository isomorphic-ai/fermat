# Generic fixed-exponent irregular proofs

`Fermat/Descent/GenericIrregular/` factors the completed Vandiver-style campaigns
into one theorem parameterized by a prime and finite certificate data.

The result has the fixed-exponent shape

```lean
∀ {p N}, FixedIrregularCertificate p N → Fermat.HoldsAt p
```

It is not a proof of `∀ p, Fermat.HoldsAt p`: every chosen exponent still
supplies and kernel-checks its own finite Case-II arithmetic and
circular-unit data. Case I is handled uniformly by a proof-producing
Sophie--Germain search, behind one explicit successful-termination axiom.
This matches the intended “one method for any given exponent” reading.

## Dependency flow

```text
exact Faulhaber data ──┐
irregular-index scan ──┼─> FixedChannelCertificate
weighted determinant ─┘              │
                                     ├─> BernoulliCubeCondition
real diagonal units ───┐             │
finite-index proof ────┼─> LemmaTwoUnitSystem ─> VandiverLemmaTwo
derivative congruences ┘                         │
                                                ├─> SecondCaseExcluded
plus-class nondivisibility ─────────────────────┘

proof-producing Sophie--Germain search ─────────┐
SecondCaseExcluded ─────────────────────────────┴─> Fermat.HoldsAt p
```

The modules implement that flow as follows:

- `ExactFaulhaberValuation.lean` extracts the exact `p`-adic valuation of a
  lifted Bernoulli number from a modular power sum.
- `WeightedMoment.lean` proves

  ```text
  det(Vᵀ diag(w) V) = (∏ wᵢ) · det(V)²
  ```

  and therefore recovers every nonzero channel weight from one determinant.
- `ChannelCertificate.lean` combines the complete irregular-index scan,
  per-channel lifted power sums, and that single determinant into
  `BernoulliCubeCondition p`.
- `DeepReality.lean` proves uniformly that Vandiver's depth-`2p` unit is
  fixed by complex conjugation.
- `LemmaTwo.lean` turns an exponent-specific finite-index real-unit family
  and its primitive-relation derivative congruences into Vandiver's exact
  Lemma II alternative.
- `SecondCase.lean` joins the generic historical descent, plus-class input,
  Lemma II system, and channel certificate.
- `FixedExponent.lean` invokes the generic Sophie--Germain search for
  Case I and exports `holdsAt_of_certificate`.

## Axis 8, not seven case splits

The weighted moment is the structure-preserving compression axis.  A
certificate with `N` irregular channels stores one `N × N` determinant,
not seven decomposition branches and not `N` separately assumed
nonvanishing statements.  The Vandermonde factorization proves all channel
weights nonzero.

The seven-fold ladder remains a useful empirical/provenance dataset, but it
is not a dependency of this generic proof.  `GenericIrregular` instead
compresses the finite channel family while preserving the algebra needed by
the historical descent.

The first nontrivial regression is exponent `157`:

```text
levels  = [62, 110]
weights = [3, 16]  in ZMod 157
```

One checked `2 × 2` weighted determinant closes both lifted Bernoulli
channels.

## Honest certificate boundary

The final certificate does **not** store any of:

- `Fermat.HoldsAt p`;
- `Fermat.SecondCaseExcluded p`;
- `VandiverLemmaTwo K p`;
- a first-case conclusion.

Those propositions are derived internally.

Despite its historical type name, `FixedIrregularCertificate` is therefore
a fixed-second-case certificate.  The explicit per-prime
`SophieGermainCertificate` definitions retained in concrete
`GenericProof.lean` files are standalone finite regressions, not fields or
inputs of the generic endpoint.

Three substantial upstream interfaces remain visible:

- `PlusClassNondivisibility K p`, currently obtained in each concrete
  exponent from a circular-unit residue certificate and the generic
  Sinnott--Kummer theorem;
- `PrimitiveRelationCubeCongruences`, currently obtained from the concrete
  polynomial-remainder and high logarithmic-derivative computation.
- `SophieGermainAuxiliarySearchTermination`, the temporary assertion that
  the total proof-producing auxiliary-prime search eventually succeeds.

The first two are not reformulations of FLT or of Lemma II; the third states
only eventual success of an executable checker, not Case I. Future work can
push the certificate boundary further down to raw residue matrices and
derivative tables, and can replace the termination seam, without changing
the downstream theorem.

## Concrete adapters

The generic directory imports only shared machinery.  Concrete instances
live in their exponent directories and import `GenericIrregular`, never the
other way around.  Each completed adapter is split into:

- `GenericChannels.lean`;
- `GenericLemmaTwo.lean`;
- `GenericSecondCase.lean`;
- `GenericProof.lean`.

The checked concrete channel data are:

| Exponent | Channels | Irregular indices | Correction weights | Moment |
| ---: | ---: | --- | --- | ---: |
| `37` | `1` | `[32]` | `[2]` | `1 × 1` |
| `59` | `1` | `[44]` | `[18]` | `1 × 1` |
| `67` | `1` | `[58]` | `[41]` | `1 × 1` |
| `157` | `2` | `[62, 110]` | `[3, 16]` | `2 × 2` |
| `491` | `3` | `[292, 336, 338]` | `[351, 412, 11]` | `3 × 3` |
| `587` | `2` | `[90, 92]` | `[498, 242]` | `2 × 2` |
| `607` | `1` | `[592]` | `[511]` | `1 × 1` |
| `691` | `2` | `[12, 200]` | `[288, 429]` | `2 × 2` |
| `1381` | `1` | `[266]` | `[561]` | `1 × 1` |

Every row supplies the same `FixedIrregularCertificate p N`
fixed-second-case payload; the theorem combines it with the generic
proof-producing Case-I search.  The current campaign deliberately stops at
`1381`; no exponent above it is part of this generic regression set.

Their final `GenericProof` theorems have the standard Lean logical
dependencies plus the explicit search-termination seam:

```text
[propext, Classical.choice, Quot.sound,
 SophieGermainAuxiliarySearchTermination]
```
