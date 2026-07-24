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

The exponent directories for `1381` and `1831` contain work-in-progress
finite certificates.  Their presence does not by itself mean that a public
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
- `Fermat/Eleven/` and `Fermat/Thirteen/` contain two independent regularity
  routes: the class-number-one certificate and a direct `SevenFold.lean`
  Faulhaber certificate closed by the formal Kummer criterion.  Both then
  reuse the checked Lamé--Kummer descent.
- `Fermat/ThirtySeven/`, `Fermat/FiftyNine/`, `Fermat/SixtySeven/`,
  `Fermat/OneHundredFiftySeven/`, `Fermat/FourHundredNinetyOne/`, and
  `Fermat/FiveHundredEightySeven/` contain the irregular-prime campaigns.
  Their final public endpoints are the corresponding
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

[`Fermat/Regular/`](Fermat/Regular/) contains reusable Faulhaber
infrastructure and the checked bridge

```text
power sums → Bernoulli numerators → Kummer regularity → FLT.
```

The deep Bernoulli/class-group equivalence comes from the pinned
[`KummerCriterion`](https://github.com/riccardobrasca/KummerCriterion)
formalization.  [`Fermat/Quadratic/`](Fermat/Quadratic/) contains
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

  The original response curve still records depth `6` for those exponents,
  because their class-number-one route is the first sufficient branch.
- `ThirtySeven.lean`, `FiftyNine.lean`, `SixtySeven.lean`,
  `OneHundredFiftySeven.lean`, `FourHundredNinetyOne.lean`, and
  `FiveHundredEightySeven.lean` reuse the completed classical-tool
  irregular-prime proofs.  Their measured outcome is tied by
  `ProofBacked.outcome_eq` to the corresponding existing
  `Fermat.HoldsAt n` theorem; the ladder does not maintain a shadow proof.
  All six campaigns traverse the complete Vandiver--Takagi--Furtwängler
  battery and record machine-readable exit depth `7`.
- `HistoricalResponse.lean` exposes the proof-carrying response curve and
  its six-point finite projection:

  ```lean
  Fermat.Ladder.HistoricalResponse.responseData
  -- [(37, 7), (59, 7), (67, 7), (157, 7), (491, 7), (587, 7)]
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
lake build Fermat.ThirtySeven.VandiverHistoricalAssembly37
lake build Fermat.FourHundredNinetyOne.VandiverHistoricalAssembly491
lake build Fermat.FourHundredNinetyOne.SecondCase
lake build Fermat.FiveHundredEightySeven.VandiverHistoricalAssembly587
lake build Fermat.Ladder.FourHundredNinetyOne
lake build Fermat.Ladder.FiveHundredEightySeven
```

A quick consumer file can simply use:

```lean
import Fermat

#check Fermat.holdsAt_thirtySeven
#check Fermat.holdsAt_fourHundredNinetyOne
#check Fermat.holdsAt_fiveHundredEightySeven
#check Fermat.holdsAt_eleven_faulhaber
#eval Fermat.Ladder.FaulhaberResponse.responseData
#check Fermat.Ladder.FourHundredNinetyOne.proofBacked
#check Fermat.Ladder.FiveHundredEightySeven.proofBacked
#check Fermat.Ladder.HistoricalResponse.campaignProofs
#eval Fermat.Ladder.HistoricalResponse.responseData
```

The final endpoints are routinely checked with `#print axioms`.  They depend
only on Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; the
campaign does not use `sorry`, `admit`, custom project axioms, or
`native_decide`.
