# Fermat: historical and classical-tool fixed-exponent proofs in Lean

This repository formalizes proofs of Fermat's Last Theorem one exponent at a
time.  Some modules reconstruct proofs historically published for their
exponents.  Others formalize newly discovered proofs that deliberately use
classical, pre-modularity tools.  The common statement is:

```lean
Fermat.HoldsAt n
```

This abbreviates Mathlib's `FermatLastTheoremFor n`.  The project deliberately
studies descent, cyclotomic, finite-certificate, and decomposition routes
rather than importing the modern modularity proof.

The completed public fixed-exponent results are:

| Exponent | Public theorem after `import Fermat` | Main route |
| ---: | --- | --- |
| 3 | `Fermat.holdsAt_three` | Mathlib's checked classical descent |
| 4 | `Fermat.holdsAt_four` | Mathlib's checked classical descent |
| 5 | `Fermat.holdsAt_five` | Dirichlet's two-branch descent |
| 7 | `Fermat.holdsAt_seven` | Lebesgue's 1840 proof and Addition |
| 11 | `Fermat.holdsAt_eleven` | class number one; direct Faulhaber alternative |
| 13 | `Fermat.holdsAt_thirteen` | class number one; direct Faulhaber alternative |
| 14 | `Fermat.holdsAt_fourteen` | Dirichlet's independent 1832 descent |
| 37 | `Fermat.holdsAt_thirtySeven` | Vandiver--Takagi--Furtwängler |
| 59 | `Fermat.holdsAt_fiftyNine` | Vandiver--Takagi--Furtwängler |
| 67 | `Fermat.holdsAt_sixtySeven` | Vandiver--Takagi--Furtwängler |
| 157 | `Fermat.holdsAt_oneHundredFiftySeven` | two-probe Vandiver descent |
| 491 | `Fermat.holdsAt_fourHundredNinetyOne` | three-channel cyclic-certificate Vandiver descent |
| 587 | `Fermat.holdsAt_fiveHundredEightySeven` | Vandiver--Sinnott; see provenance below |
| 607 | `Fermat.holdsAt_sixHundredSeven` | one-channel circular-unit Vandiver descent |
| 691 | `Fermat.holdsAt_sixHundredNinetyOne` | two-channel cyclic-certificate Vandiver descent |
| 1051 | `Fermat.holdsAt_oneThousandFiftyOne` | complete Bernoulli regularity scan |
| 1381 | `Fermat.holdsAt_oneThousandThreeHundredEightyOne` | one-channel cyclic-certificate Vandiver descent |

The nine completed irregular-prime endpoints from `37` through `1381` are
also reassembled through the regularized Kummer correction.  After
`import Fermat`, their public aliases have the suffix `_kummerIso`, for
example `Fermat.holdsAt_thirtySeven_kummerIso` and
`Fermat.holdsAt_oneThousandThreeHundredEightyOne_kummerIso`.

The exponent directory for `1831` contains work-in-progress finite
certificates.  Its presence does not by itself mean that a public
`Fermat.HoldsAt n` theorem has been completed.

### Provenance and method labels

In this repository, *historical* describes either an actually published
proof or a specifically identified historical segment of an argument.  It
is not a blanket authorship claim for every completed exponent.  Similarly,
*classical-tool* describes the mathematical toolkit, not the date when a
particular proof was discovered.

The exponent-`587` proof is a new mathematical proof.  Its provenance is:

- **research direction and guidance:** Fabian;
- **mathematical proof construction:** GPT-5.6 Pro, under Fabian's guidance
  in 2026;
- **Lean implementation:** GPT-5.6 Sol Ultra, working with Fabian;
- **formal verification:** the Lean kernel.

The proof uses a Vandiver-style cyclotomic descent, Takagi--Furtwängler
reflection, and the circular-unit index machinery associated with Sinnott,
while avoiding elliptic curves, modularity, and the all-prime modern proof.
The latest explicitly named conceptual ingredient in this route is Sinnott's
1978 work on circular units:

- W. Sinnott, [*On the Stickelberger ideal and the circular units of a
  cyclotomic field*](https://annals.math.princeton.edu/1978/108-1/p05),
  *Annals of Mathematics* **108** (1978), 107--134.

The mathematical toolkit can therefore be described as available by 1978;
the exact computation and formal verification are modern.

## Repository map

### Public entry point

[`Fermat.lean`](Fermat.lean) is the umbrella import.  It exposes the public
fixed-exponent theorems and imports the proof-backed ladder datasets.

The foundational statement and elementary transport lemmas live in:

- [`Fermat/Basic.lean`](Fermat/Basic.lean): `HoldsAt`, primitive solutions,
  and transport along divisibility of exponents;
- [`Fermat/Cases.lean`](Fermat/Cases.lean): first-case/second-case interfaces
  and their final recombination;
- [`Fermat/SophieGermain.lean`](Fermat/SophieGermain.lean): the reusable
  auxiliary-prime criterion.

### Exponent-specific proofs

Each completed exponent has its own directory under `Fermat/`.

- `Fermat/Five/`, `Fermat/Seven/`, and `Fermat/Fourteen/` contain
  decompressed historical descents.  The modules separate normalization,
  coprimality, power extraction, allocation, and the final infinite descent.
- `Fermat/Eleven/` and `Fermat/Thirteen/` contain two independent
  class-number certificates: a direct class-number-one calculation and a
  `SevenFold.lean` Faulhaber calculation connected to the same historical
  condition by the formal Kummer criterion.  The patched generic
  `flt-regular` endpoint is checked separately; it no longer consumes
  class-number regularity.
- `Fermat/OneThousandFiftyOne/` contains a complete 524-index regularity
  scan and its resulting cyclotomic class-number certificate.  Its public
  FLT endpoint uses the patched generic descent separately, while the scan
  remains the regular anchor used by the exponent-12613 campaign.
- `Fermat/ThirtySeven/`, `Fermat/FiftyNine/`, `Fermat/SixtySeven/`,
  `Fermat/OneHundredFiftySeven/`, `Fermat/FourHundredNinetyOne/`,
  `Fermat/FiveHundredEightySeven/`, `Fermat/SixHundredSeven/`,
  `Fermat/SixHundredNinetyOne/`, and
  `Fermat/OneThousandThreeHundredEightyOne/` contain the completed
  irregular-prime campaigns. Their final public endpoints are the corresponding
  `VandiverHistoricalAssembly*.lean` modules.

The irregular-prime directories use a deliberately layered layout:

1. `FirstCase.lean` checks the Sophie--Germain auxiliary prime.
2. `ArithmeticCertificate.lean`, `HighBernoulli.lean`, and
   `VandiverData.lean` check the finite Bernoulli channels.
3. `CircularUnit*.lean` checks the concrete real circular-unit data and
   class-number consequence.
4. `TakagiHistorical*.lean` and the reusable reflection modules construct
   the real unramified Kummer extension.
5. `VandiverLemmaTwo*.lean` formalizes the unit/logarithmic part of
   Vandiver's argument.
6. `VandiverHistorical.lean` follows the historical equations (6)--(10).
7. `VandiverHistoricalAssembly*.lean` joins both cases and exports
   `Fermat.HoldsAt n`.

For `157`, the finite probe loop is retained as data: the first probe is
`q = 1571`, and the successful circular-unit probe is `q = 7537`.

For `491`, the Sophie--Germain auxiliary prime and circular-unit modulus are
both `q = 983 = 2 * 491 + 1`.  The complete Bernoulli scan leaves only
the three candidate channels `{292, 336, 338}`.  Its compact circular-unit
certificate reconstructs the source `244 × 244` matrix from 245 cyclic phase
values and a kernel-checked correlation inverse; the three lifted Bernoulli
certificates and Vandiver Lemma II assembly then close the second case.

For `587`, the auxiliary prime and circular-unit probe are both
`q = 8219 = 14 * 587 + 1`.  The complete Bernoulli scan proves that the
irregular channels are exactly `{90, 92}`.  Its real circular-unit
certificate compresses the `292 × 292` residue-symbol matrix into two
length-293 cyclic phase vectors and a kernel-checked correlation identity,
rather than storing 85,264 unrelated inverse entries.

For `607`, the Sophie--Germain auxiliary prime and circular-unit modulus are
both `q = 20639 = 34 * 607 + 1`.  The complete Bernoulli scan leaves the
single irregular channel `{592}`, whose lifted index is `359344`.  Its
source `302 × 302` circular-unit matrix is reconstructed from 303 cyclic
phase values and a kernel-checked correlation inverse.  Sinnott's index
formula, the diagonal-unit calculation, and Vandiver's Lemma II then feed
the historical second-case descent.  The package prime `q* = 118973` is a
separate norm/branch selector, not the circular-unit modulus.

For `691`, the Sophie--Germain auxiliary prime and circular-unit modulus are
both `q = 11057 = 16 * 691 + 1`.  The implication-form Bernoulli scan leaves
only the two candidate channels `{12, 200}`, whose lifts are `8292` and
`138200`.  The source `344 × 344` circular-unit matrix is reconstructed from
345 cyclic phase values; its correlation inverse and determinant residue
`36 mod 691` close the finite side of the two-channel Vandiver descent.

For `1381`, the auxiliary prime and circular-unit modulus are
`q = 38669 = 28 * 1381 + 1`.  The complete Bernoulli scan leaves the single
irregular channel `{266}`, with lifted index `367346`.  Its source
`689 × 689` circular-unit matrix is certified by 690 cyclic correlations.
Those finite facts feed the reusable diagonal-unit and Lemma-II layers, then
the prime-generic Takagi--Furtwängler and historical Vandiver assembly.

### Reusable irregular-prime machinery

[`Fermat/Irregular/`](Fermat/Irregular/) contains the shared number theory
used by the concrete irregular exponents.  Important families include:

- Bernoulli/Faulhaber and Voronoi--Kummer congruences;
- circular units, residue homomorphisms, and the Sinnott index formula;
- cyclotomic characters, Dirichlet `L`-values, and the real class-number
  calculation;
- Takagi--Furtwängler ramification and reflection;
- Vandiver's historical descent, unit lemmas, polynomial remainders, and
  logarithmic derivatives.

Exponent-specific modules instantiate these generic results with explicit
finite data.  Large matrices and Bernoulli numbers are checked using compact
kernel-verifiable certificates rather than trusted external computations.

[`Fermat/GenericIrregular/`](Fermat/GenericIrregular/) is the new
fixed-exponent assembly layer.  Its theorem
`Fermat.GenericIrregular.FixedExponent.holdsAt_of_certificate` proves
`Fermat.HoldsAt p` from a parameterized fixed-second-case certificate
containing:

- plus-class nondivisibility;
- a finite-index real cyclotomic-unit/derivative system;
- a complete family of lifted Bernoulli channels; and
- one nonzero weighted-moment determinant.

It does not store `HoldsAt`, `SecondCaseExcluded`, Vandiver's Lemma II, or
first-case data as certificate fields. Case I is supplied by a generic
proof-producing Sophie--Germain search; its temporary successful-termination
assumption is explicit and separately auditable. The concrete
Sophie--Germain certificates retained in exponent directories are
standalone finite regressions, not inputs to these generic endpoints. The
generic directory
imports only shared machinery; thin concrete adapters live in the exponent
directories. End-to-end regressions are checked at `37`, `59`, `67`, `157`,
`491`, `587`, `607`, `691`, and `1381`. They include the two-channel `157`,
`587`, and `691` cases and the three-channel `491` case, each closed by one
weighted-moment determinant. The current generic campaign stops at `1381`. See the
[GenericIrregular architecture note](Fermat/GenericIrregular/README.md) for
the complete dependency flow, channel table, and certificate boundary.

### The regularized Kummer splice

[`Fermat/KummerIso/`](Fermat/KummerIso/) reassembles those same nine
fixed-second-case certificates through an explicit repair of Kummer's proof.
The two uses of regularity are kept separate:

1. the special Fermat ideal roots are principalized by the historical
   primary/Takagi--Furtwängler route and the checked input `p ∤ h⁺`;
2. the exact historical unit ratio is rooted through a finite diagonal
   correction over `ZMod p`.

On a lifted Bernoulli coordinate with coefficient `Bᵢ`, the diagonal entry
is the actual quotient `(Bᵢ / p²) mod p`; an ordinary coordinate receives
`1`.  The condition `p³ ∤ Bᵢ` makes every entry nonzero, so the diagonal is
invertible.  This full-source correction is formalized for an arbitrary
finite source type.  Separately, the auxiliary channel-weight gauge works
over `Fin N` for every `N`, including `N = 0`; no equality between the two
gauges is assumed.

The historical route is end-to-end complete.  The independently exposed
regular-style `WeightedSolution` is kept honest: its exact ratio is known
to be semiprimary modulo `(p)`, but direct reuse still requires either
`KummerIso.DeepRatio.RegularUnitRatioDeep` or a proof identifying it with
the historical ratio.  Conditional on that explicit depth premise,
`KummerIso.Induction.exists_unweightedSolution_of_regularUnitRatioDeep`
extracts the root, absorbs it into `x`, and returns the unweighted equation
for the next induction step; it does not claim the missing premise.

The finite circular-unit residue certificates also replace the
equation-(7d) seam at all nine completed campaign exponents.  Those closed
regressions retain only `BernoulliValidationBound` and termination of the
generic Sophie--Germain search as project axioms.  See the
[KummerIso architecture note](Fermat/KummerIso/README.md) for the complete
call graph, theorem boundaries, and both regression families.

[`Fermat/Regular/`](Fermat/Regular/) contains reusable Faulhaber
infrastructure and the checked historical bridge

```text
power sums → Bernoulli numerators → cyclotomic class-number regularity
```

The deep Bernoulli/class-group equivalence comes from the pinned
[`KummerCriterion`](https://github.com/riccardobrasca/KummerCriterion)
formalization.  Since the locally patched `flt-regular` core no longer
accepts that condition as a premise, its generic FLT endpoint is deliberately
reported as a separate result with the core's three temporary seams.
[`Fermat/Quadratic/`](Fermat/Quadratic/) contains
quadratic-ring and unit calculations shared by several elementary descents.

### The seven-fold ladder

[`Fermat/Ladder/`](Fermat/Ladder/) records the campaign's measured
decomposition independently of the final theorem statement.

- `Basic.lean` defines the seven folds, checked traces, pass/contradiction
  outcomes, exit schedules, and `ProofBacked`.
- `One.lean` through `Fourteen.lean` are the original fourteen samples.
- `Response.lean` exposes their kernel-checked response vector:

  ```text
  [1, 2, 3, 4, 5, 1, 6, 1, 1, 1, 6, 1, 6, 1]
  ```

- `FaulhaberResponse.lean` retains the independent, proof-backed full-depth
  alternatives for `11` and `13`:

  ```lean
  Fermat.Ladder.FaulhaberResponse.responseData
  -- [(11, 7), (13, 7)]
  ```

  The original response curve still records depth `6` for those exponents.
  In the migrated trace, that fold honestly pairs the independent
  class-number-one certificate with the patched generic FLT endpoint; it
  does not claim that the endpoint consumes the certificate.
- `ThirtySeven.lean`, `FiftyNine.lean`, `SixtySeven.lean`,
  `OneHundredFiftySeven.lean`, `FourHundredNinetyOne.lean`,
  `FiveHundredEightySeven.lean`, and `SixHundredNinetyOne.lean` reuse the
  completed classical-tool
  irregular-prime proofs.  Their measured outcome is tied by
  `ProofBacked.outcome_eq` to the corresponding existing
  `Fermat.HoldsAt n` theorem; the ladder does not maintain a shadow proof.
  All seven campaigns traverse the complete Vandiver--Takagi--Furtwängler
  battery and record machine-readable exit depth `7`.
- `HistoricalResponse.lean` exposes the proof-carrying response curve and
  its seven-point finite projection:

  ```lean
  Fermat.Ladder.HistoricalResponse.responseData
  -- [(37, 7), (59, 7), (67, 7), (157, 7), (491, 7), (587, 7), (691, 7)]
  ```

Code that only fits empirical curves can consume `responseData`.  Code that
needs theorem provenance can consume `responseCurve`, whose points retain
the dependent `ProofBacked` payload.

### Source ledgers

[`docs/`](docs/) contains source and repair ledgers for the fixed-exponent
proof routes at `5`, `7`, `11`, `13`, `14`, and `37`.  The source PDFs,
generated proof packages, and audit material used during development are
kept in the sibling archive `../fermat-data` in the campaign workspace.

## Building

The project pins Lean `v4.31.0-rc1` and exact revisions of Mathlib,
[`flt-regular`](https://github.com/leanprover-community/flt-regular), and
[`KummerCriterion`](https://github.com/riccardobrasca/KummerCriterion).

On a fresh checkout:

```bash
lake exe cache get
lake build
```

The default target is the umbrella module `Fermat`.  Useful targeted builds
include:

```bash
lake build Fermat.Ladder.Response
lake build Fermat.Ladder.FaulhaberResponse
lake build Fermat.Ladder.HistoricalResponse
lake build Fermat.KummerIso
lake build Fermat.KummerIso.Regressions
lake build Fermat.ThirtySeven.VandiverHistoricalAssembly37
lake build Fermat.FourHundredNinetyOne.VandiverHistoricalAssembly491
lake build Fermat.FourHundredNinetyOne.SecondCase
lake build Fermat.FiveHundredEightySeven.VandiverHistoricalAssembly587
lake build Fermat.SixHundredSeven.VandiverHistoricalAssembly607
lake build Fermat.SixHundredNinetyOne.VandiverHistoricalAssembly691
lake build Fermat.OneThousandFiftyOne.Regularity
lake build Fermat.OneThousandThreeHundredEightyOne.VandiverHistoricalAssembly1381
lake build Fermat.Ladder.FourHundredNinetyOne
lake build Fermat.Ladder.FiveHundredEightySeven
lake build Fermat.Ladder.SixHundredNinetyOne
```

A quick consumer file can simply use:

```lean
import Fermat

#check Fermat.holdsAt_thirtySeven
#check Fermat.holdsAt_thirtySeven_kummerIso
#check Fermat.holdsAt_fourHundredNinetyOne
#check Fermat.holdsAt_fiveHundredEightySeven
#check Fermat.holdsAt_sixHundredSeven
#check Fermat.holdsAt_sixHundredNinetyOne
#check Fermat.holdsAt_oneThousandFiftyOne
#check Fermat.holdsAt_oneThousandThreeHundredEightyOne
#check Fermat.holdsAt_oneThousandThreeHundredEightyOne_kummerIso
#check Fermat.holdsAt_eleven_faulhaber
#eval Fermat.Ladder.FaulhaberResponse.responseData
#check Fermat.Ladder.FourHundredNinetyOne.proofBacked
#check Fermat.Ladder.FiveHundredEightySeven.proofBacked
#check Fermat.Ladder.SixHundredNinetyOne.proofBacked
#check Fermat.Ladder.HistoricalResponse.campaignProofs
#eval Fermat.Ladder.HistoricalResponse.responseData
```

The final endpoints are routinely checked with `#print axioms`. Historical
explicit-prime endpoints depend only on Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`. The generic `*_generic` and
`*_kummerIso` endpoint families additionally expose the temporary
`SophieGermainAuxiliarySearchTermination` axiom. The campaign uses no
`sorry` or `admit`; executable searches are reflected back into checked
propositions.
