# Fermat: classical fixed-exponent proofs in Lean

This repository formalizes classical proofs of Fermat's Last Theorem one
exponent at a time.  The common statement is:

```lean
Fermat.HoldsAt n
```

This abbreviates Mathlib's `FermatLastTheoremFor n`.  The project deliberately
studies the historical descent, cyclotomic, finite-certificate, and
decomposition routes rather than importing the modern modularity proof.

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

The exponent directories for `491`, `587`, `1381`, and `1831` contain
work-in-progress finite certificates.  Their presence does not by itself
mean that a public `Fermat.HoldsAt n` theorem has been completed.

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
- `Fermat/ThirtySeven/`, `Fermat/FiftyNine/`, `Fermat/SixtySeven/`, and
  `Fermat/OneHundredFiftySeven/` contain the irregular-prime campaigns.
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
- `ThirtySeven.lean`, `FiftyNine.lean`, `SixtySeven.lean`, and
  `OneHundredFiftySeven.lean` reuse the completed historical proofs.  Their
  measured outcome is tied by `ProofBacked.outcome_eq` to the corresponding
  existing `Fermat.HoldsAt n` theorem; the ladder does not maintain a shadow
  proof.
- `HistoricalResponse.lean` exposes the proof-carrying response curve and
  its finite projection:

  ```lean
  Fermat.Ladder.HistoricalResponse.responseData
  -- [(37, 7), (59, 7), (67, 7), (157, 7)]
  ```

Code that only fits empirical curves can consume `responseData`.  Code that
needs theorem provenance can consume `responseCurve`, whose points retain
the dependent `ProofBacked` payload.

### Source ledgers

[`docs/`](docs/) contains source and repair ledgers for the historical
proofs at `5`, `7`, `11`, `13`, `14`, and `37`.  The source PDFs, generated
proof packages, and audit material used during development are kept in the
sibling archive `../fermat-data` in the campaign workspace.

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
```

A quick consumer file can simply use:

```lean
import Fermat

#check Fermat.holdsAt_thirtySeven
#check Fermat.holdsAt_eleven_faulhaber
#eval Fermat.Ladder.FaulhaberResponse.responseData
#check Fermat.Ladder.HistoricalResponse.campaignProofs
#eval Fermat.Ladder.HistoricalResponse.responseData
```

The final endpoints are routinely checked with `#print axioms`.  They depend
only on Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; the
campaign does not use `sorry`, `admit`, custom project axioms, or
`native_decide`.
