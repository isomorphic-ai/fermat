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

The completed fixed-exponent results exposed by the umbrella import are:

| Exponent | Public theorem after `import Fermat` | Main route |
| ---: | --- | --- |
| 3 | `Fermat.holdsAt_three` | Mathlib's checked classical descent |
| 4 | `Fermat.holdsAt_four` | Mathlib's checked classical descent |
| 5 | `Fermat.holdsAt_five` | Dirichlet's two-branch descent |
| 6 | `Fermat.Six.holdsAt_six_conservation` | direct conservation descent |
| 7 | `Fermat.holdsAt_seven` | Lebesgue's 1840 proof and Addition |
| 10 | `Fermat.Eleven.SevenFold.holdsAt_ten` | divisibility transport from exponent 5 |
| 11 | `Fermat.holdsAt_eleven` | class number one; direct Faulhaber alternative |
| 12 | `Fermat.Eleven.SevenFold.holdsAt_twelve` | divisibility transport from exponent 3 |
| 13 | `Fermat.holdsAt_thirteen` | class number one; direct Faulhaber alternative |
| 14 | `Fermat.holdsAt_fourteen` | Dirichlet's independent 1832 descent |
| 37 | `Fermat.holdsAt_thirtySeven` | Vandiver--Takagi--Furtwängler |
| 59 | `Fermat.holdsAt_fiftyNine` | Vandiver--Takagi--Furtwängler |
| 60 | `Fermat.FiftyNine.Folding.holdsAt_sixty_via_three` | divisibility transport from exponent 3; alternatives from 4 and 5 |
| 66 | `Fermat.SixtySeven.NeighborFolding.holdsAt_sixtySix_via_eleven` | divisibility transport from exponent 11; alternative from 3 |
| 67 | `Fermat.holdsAt_sixtySeven` | Vandiver--Takagi--Furtwängler |
| 157 | `Fermat.holdsAt_oneHundredFiftySeven` | two-probe Vandiver descent |
| 229 | `Fermat.holdsAt_twoHundredTwentyNine` | complete Voronoi/Bernoulli regularity scan; patched generic descent |
| 491 | `Fermat.holdsAt_fourHundredNinetyOne` | three-channel cyclic-certificate Vandiver descent |
| 587 | `Fermat.holdsAt_fiveHundredEightySeven` | Vandiver--Sinnott; see provenance below |
| 607 | `Fermat.holdsAt_sixHundredSeven` | one-channel circular-unit Vandiver descent |
| 691 | `Fermat.holdsAt_sixHundredNinetyOne` | two-channel cyclic-certificate Vandiver descent |
| 1051 | `Fermat.holdsAt_oneThousandFiftyOne` | complete Bernoulli regularity scan |
| 1381 | `Fermat.holdsAt_oneThousandThreeHundredEightyOne` | one-channel cyclic-certificate Vandiver descent |

Exponent `59` also exports
`Fermat.holdsAt_fiftyNine_stateEquationEight`.  This additional public
receipt starts with the allocated integral Fermat state, constructs its
literal equation-(8) generators and coefficient units, and feeds them into
the historical support descent before combining the resulting Case-II
contradiction with the checked Sophie--Germain Case-I computation.
The same import exposes the plus and minus
`exists_explicitProjectedUnitLift_classSilent_*` receipts: the concrete
equation-(8) coefficient units are projected in the irregular character
seat and proved to land in the kernel of the actual 59-torsion ideal-class
map.  Their companion
`exists_explicitProjectedUnitDifference_classSilent59` retains one concrete
projected global-unit representative of the actual plus-minus Selmer
difference, identifies it with twice the plus mode, and proves that its
genuine class obstruction vanishes.

The nine completed irregular-prime endpoints from `37` through `1381` are
also reassembled through the regularized Kummer correction.  After
`import Fermat`, their public aliases have the suffix `_kummerIso`, for
example `Fermat.holdsAt_thirtySeven_kummerIso` and
`Fermat.holdsAt_oneThousandThreeHundredEightyOne_kummerIso`.

Exponent `1831` is also complete, but its endpoint currently lives in the
direct module
[`Fermat.Exponents.OneThousandEightHundredThirtyOne.VandiverHistoricalAssembly1831`](Fermat/Exponents/OneThousandEightHundredThirtyOne/VandiverHistoricalAssembly1831.lean)
rather than the `Fermat` umbrella import.  Importing that module exposes
`Fermat.OneThousandEightHundredThirtyOne.holdsAt_oneThousandEightHundredThirtyOne :
Fermat.HoldsAt 1831`.

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

The Lean source tree is organized by role:

- [`Fermat/Core/`](Fermat/Core/) contains stable statement boundaries,
  shared interfaces, and classical wrappers;
- [`Fermat/Descent/`](Fermat/Descent/) contains reusable irregular, Kummer,
  quadratic, and regular descent machinery;
- [`Fermat/Certificates/`](Fermat/Certificates/) contains case-oriented finite
  receipts shared by concrete proof assemblies.  The exponent-`1831`
  Fourier determinant certificate lives under `CaseII_1/`;
- [`Fermat/Exponents/`](Fermat/Exponents/) contains the concrete
  fixed-exponent developments, including historical descents, local finite
  data, and thin certificate adapters.  Exponent directory names remain
  English words;
- [`Fermat/Experiments/`](Fermat/Experiments/) contains the Conservation and
  Ladder laboratories and their proof-backed datasets.

Module paths follow this filesystem taxonomy.  Declaration namespaces remain
stable: for example, the module `Fermat.Experiments.Ladder.Response` still
exposes declarations under `Fermat.Ladder`.

### Public entry point

[`Fermat.lean`](Fermat.lean) is the umbrella import.  It exposes the public
fixed-exponent theorems and imports the proof-backed ladder datasets.

The stable statement and interface layer includes:

- [`Fermat/Core/Statement/Basic.lean`](Fermat/Core/Statement/Basic.lean): the
  proposition-only `HoldsAt` boundary;
- [`Fermat/Core/Statement.lean`](Fermat/Core/Statement.lean): the statement
  facade and transport along divisibility of exponents;
- [`Fermat/Core/Basic.lean`](Fermat/Core/Basic.lean): the broad
  Mathlib-plus-statement prelude used by classical developments;
- [`Fermat/Core/Classical.lean`](Fermat/Core/Classical.lean): the checked
  exponent-`3` and exponent-`4` wrappers and elementary transport to `14`;
- [`Fermat/Core/Cases.lean`](Fermat/Core/Cases.lean): first-case/second-case interfaces
  and their final recombination;
- [`Fermat/Core/SophieGermain.lean`](Fermat/Core/SophieGermain.lean): the reusable
  auxiliary-prime criterion.

### Exponent-specific proofs

Each primary campaign exponent has its own directory under
`Fermat/Exponents/`.

- `Fermat/Exponents/Five/`, `Fermat/Exponents/Seven/`, and `Fermat/Exponents/Fourteen/` contain
  decompressed historical descents.  The modules separate normalization,
  coprimality, power extraction, allocation, and the final infinite descent.
- `Fermat/Exponents/Eleven/` and `Fermat/Exponents/Thirteen/` contain two independent
  class-number certificates: a direct class-number-one calculation and a
  `SevenFold.lean` Faulhaber calculation connected to the same historical
  condition by the formal Kummer criterion.  The patched generic
  `flt-regular` endpoint is checked separately; it no longer consumes
  class-number regularity.
- `Fermat/Exponents/TwoHundredTwentyNine/` contains a complete depth-one
  Voronoi/Bernoulli regularity scan, while
  `Fermat/Exponents/OneThousandFiftyOne/` contains a complete 524-index
  regularity scan and its resulting cyclotomic class-number certificate.
  Their public FLT endpoints use the patched generic descent separately; the
  exponent-1051 scan remains the regular anchor used by the exponent-12613
  campaign.
- `Fermat/Exponents/ThirtySeven/`, `Fermat/Exponents/FiftyNine/`, `Fermat/Exponents/SixtySeven/`,
  `Fermat/Exponents/OneHundredFiftySeven/`, `Fermat/Exponents/FourHundredNinetyOne/`,
  `Fermat/Exponents/FiveHundredEightySeven/`, `Fermat/Exponents/SixHundredSeven/`,
  `Fermat/Exponents/SixHundredNinetyOne/`, and
  `Fermat/Exponents/OneThousandThreeHundredEightyOne/` contain the completed
  umbrella-exported irregular-prime campaigns.  The
  `Fermat/Exponents/OneThousandEightHundredThirtyOne/` campaign is complete as
  well and is available by direct module import.  Their final historical
  endpoints are the corresponding `VandiverHistoricalAssembly*.lean` modules.

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
The parallel [`CaseII_2` moment receipt](Fermat/Certificates/CaseII_2/) checks
only the low contacts at `266` and `1646`; Sun's depth-two interpolation
authenticates the lifted Bernoulli weight `561` without evaluating a power sum
at index `367346`.  Rewiring the legacy consumers to this route is deferred to
one later migration.

### Reusable irregular-prime machinery

[`Fermat/Descent/Irregular/`](Fermat/Descent/Irregular/) contains the shared number theory
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

[`Fermat/Descent/GenericIrregular/`](Fermat/Descent/GenericIrregular/) is the new
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
[GenericIrregular architecture note](Fermat/Descent/GenericIrregular/README.md) for
the complete dependency flow, channel table, and certificate boundary.

### The regularized Kummer splice

[`Fermat/Descent/KummerIso/`](Fermat/Descent/KummerIso/) reassembles those same nine
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

For the prime-parametric assembly, the family of conditions `p³ ∤ Bᵢ` is
now exposed honestly as `KummerIso.MorishimaConjectureAt p`. It is
Morishima's conjecture, distinct from Vandiver's conjecture `p ∤ h⁺`, and is
not inferred from Wiles's proof of FLT. The canonical derivative-source
calculation is a separate temporary seam. Fixed-exponent unit-system and
channel certificates bypass both through kernel-checked finite data.

The certificate-backed fixed-exponent historical route is end-to-end
complete. The separately exposed prime-parametric route is conditional on
Morishima and its named source seams. The independently exposed regular-style
`WeightedSolution` is kept honest: its exact ratio is known to be semiprimary
modulo `(p)`, but direct reuse still requires either
`KummerIso.DeepRatio.RegularUnitRatioDeep` or a proof identifying it with
the historical ratio.  Conditional on that explicit depth premise,
`KummerIso.Induction.exists_unweightedSolution_of_regularUnitRatioDeep`
extracts the root, absorbs it into `x`, and returns the unweighted equation
for the next induction step; it does not claim the missing premise.

The finite circular-unit residue certificates also replace the
equation-(7d) seam at all nine completed campaign exponents.  Those closed
regressions reuse each fixed certificate's checked unit system and axis-8
channels, so they require neither Morishima nor the canonical derivative
source. They reuse the explicit finite Sophie--Germain certificates for
Case I, and therefore contain no project axioms. See the
[KummerIso architecture note](Fermat/Descent/KummerIso/README.md) for the complete
call graph, theorem boundaries, and both regression families.

### Prime-parametric Kummer--Albert and local H² laboratory

[`Fermat/Experiments/Conservation/`](Fermat/Experiments/Conservation/) contains the generic
cohomological and field-theoretic implementation used to investigate the
remaining local step without building a separate proof for each prime.  Its
prime-parametric spine now constructs, for every prime `p` in characteristic
zero:

1. the concrete Kummer splitting field of `X^p - a` and its continuous,
   surjective absolute-Galois character `chi_a : G_F → C_p`;
2. the standard carry class in actual continuous `H²`, together with a
   constructive proof that its pullback vanishes exactly when `chi_a` lifts
   continuously to `C_(p²)`;
3. the genuine chosen-root Kummer cocycle and its oriented Kummer cup,
   including an equality between that cup and the pulled carry/Bockstein
   class; and
4. Albert's construction and converse, which identify a primitive-root norm
   from the concrete Kummer extension with the existence of that compatible
   `C_(p²)` lift.

The public endpoint of this generic chain is
`PrimeKummerNormLiftH2Criterion`.  It proves the full equivalence

```text
primitive p-th root is a norm
↔ compatible continuous C_(p²) lift exists
↔ pulled carry H² class is zero
↔ oriented genuine Kummer cup is zero
↔ roots-valued genuine Kummer cup is zero.
```

The corresponding nonnorm, no-lift, and nonzero forms are proved as well.
The `At59` modules are compatibility receipts showing that the earlier
order-59 constructions are specializations of this generic code rather than
new certificates.

The same directory also contains a second prime-parametric spine for the
global Selmer action.  `CommonActionSelmerCore` isolates the concrete
unit--Selmer--class sequence (`fromUnitLift`, its injectivity theorem, and the
vendored `toClass` exact sequence) from the heavier campaign stage.  This
keeps the reusable spine independent of every numbered-exponent directory.
`PrimeCyclotomicSelmerAction` constructs the actual
field, unit, Kummer-quotient, place, valuation, and stable-support actions for
an arbitrary prime `p`.  `PrimeCyclotomicUnitSelmerNaturality` proves that the
genuine global-unit inclusion intertwines this action, including arbitrary
character projectors.  `PrimeCyclotomicSelmerClassNaturality` constructs the
fractional-ideal and class-group actions and proves naturality of the actual
strict Selmer class map and its `p`-torsion character projectors.  The
independent `PrimeEmptySupportEigenspaceInclusion` module lifts the canonical
strict-to-supported Selmer inclusion to arbitrary character eigenspaces,
proves it injective, and retains its exact Kummer-class readback.  The
corresponding `*59` files preserve the older public API as transparent
specializations; only support at `827` and the solution-dependent Fermat
endpoints remain in those adapters.

`FiniteOrbitLedger` is the coefficient-generic finite placement layer.  For
any finite index type, arbitrary place type, and additive commutative-monoid
coefficients, it seats each supplied value in a `Finsupp` row at its supplied
place.  The index orientation is preserved literally: no inversion or weight
is inserted.  An injective place map gives exact indexed readback; without
injectivity, coincident rows add while the total ledger sum still recovers the
complete indexed sum.  Values outside the map's range vanish, so the actual
finite support is contained in that range, but support equality is not claimed
because supplied coefficients may be zero.  This module introduces neither
character weights nor any local or global reciprocity assertion.

`FiniteOrbitLedgerReciprocity` is the route-neutral conservation layer on top
of that ledger.  Its seven-declaration API reconstructs the literal
place-indexed reading ledger from one distinguished place and one injectively
indexed finite orbit, turns an honestly supplied `GlobalReciprocityLaw` into
the corresponding distinguished-plus-orbit balance, and propagates zero or
nonzero ledger totals to the resulting local conclusions.  The arithmetic
boundary is deliberately explicit: the pairing, reciprocity witness, orbit
map, injectivity and disjointness, every pointwise local comparison, and
silence at all omitted places remain inputs.  It neither identifies the
abstract finite index with arithmetic support nor supplies any cyclotomic,
character, regularity, or cardinality fact.  Unlike
`PrimeFullOrbitReciprocity`, it does not require a group structure on the
orbit index, an orbit of size `p - 1`, or Fourier waves; the latter module is
the parallel prime full-orbit layer that adds character compression and its
orientation-sensitive selected-component conclusions.  At exponent `59`,
`tameOrbitPlace827_range_eq_placesOver827` supplies the deliberately separate
arithmetic receipt that the canonical index range is exactly the set of places
above `827`; the existing ledger-level zero/nonzero consequences and canonical
global-reciprocity wrappers are now thin specializations of the generic
ledger consequences.

`PrimeResidueFourier` supplies the residue-field Fourier dictionary for every
prime `p`: character functions and orthogonality, normalized Fourier
coordinates and reconstruction, the character basis, pure-mode support and
pointed-silence consequences, and reduction of `p`-adic characters modulo
`p`.  `SplitPrimeFourier827` preserves the established order-59 API as a thin
specialization, while the splitting and regular place-orbit arithmetic at
`827` remains correctly campaign-specific.

`PrimeFourierPairingCompression` supplies the corresponding prime-generic
pairing algebra.  Complementary pure character waves have constant pointwise
product; on an orbit of cardinality `p - 1`, their complete sum is the
negative of any selected product.  More generally, pairing an arbitrary raw
vector with a pure inverse-character wave retains exactly its selected
Fourier component, including the explicit inverse-index orientation.  Its
final scalar adapter consumes an honest supplied reciprocity equation; this
module constructs neither local values nor a global pairing, reciprocity law,
Kummer class, or cyclotomic support orbit.

`PrimeFullOrbitReciprocity` connects that finite algebra to an actual
prime-generic `PlaceIndexedLocalPairing`.  From an explicitly supplied
`GlobalReciprocityLaw`, an injectively indexed finite auxiliary orbit disjoint
from the distinguished place, an outside-silence proof, and pointwise local
comparison equations, it first derives the negative complete-orbit balance.
When the orbit has cardinality `p - 1`, complementary waves compress to a
selected product, while a raw primal vector compresses only under the full
sum to its selected Fourier component; the inverse-index specialization keeps
the opposite place orientation visible.  The pairing's representation group
and the orbit-index group remain separate types.  The module does not
construct the pairing, reciprocity law, support silence, local comparisons,
or a cyclotomic orbit: those arithmetic boundaries stay explicit inputs.

`PrimeCyclotomicLocalizationEquivariance` then combines the actual
cyclotomic Selmer representation, its valuation covariance, and the genuine
character projector.  For arbitrary prime `p` and any cyclotomically stable
support, it proves that projected localization along the canonical support
orbit is a single inverse reduced reflected-character mode.  Stability gives
a canonical orbit map but does not falsely assert that it is an equivalence;
the regular orbit equivalence above `827` and its orientation remain in the
thin order-59 adapter.

`PrimeCyclotomicSelmerVerification` is the non-imported executable audit for
this spine: it inventories the generic API, records its intended dependency
graph, rejects public product-equivalence shortcuts, and checks every
declaration against the standard `propext`/choice/quotient axiom budget.
Its recursive import cone stays entirely inside
`Fermat.Experiments.Conservation`: it does not pass through
`CommonActionStage`, either drain module, or any numbered exponent directory.

The concrete local experiment lives in
[`Fermat/Exponents/FiftyNine/Conservation/`](Fermat/Exponents/FiftyNine/Conservation/).  Lean
proves that `60` is not a 59th power in the actual lambda-adic field, while
the bare uniformizer `lambda = zeta_59 - 1` has the explicit norm witness
`Norm(1 + alpha) = zeta_59`.  The same witness kills the bare-lambda Kummer
cup in genuine continuous `H²(mu_59)`, and cup additivity proves that the
cup for `60 * lambda` is exactly the cup for the unit factor `60`.  On the
norm side, the primitive-root question for `60 * lambda` is reduced to the
explicit correction

```text
c = (1 + 60 * lambda) / zeta_59 = 1 + 59 * lambda / zeta_59.
```

Its valuation is checked exactly: `c` lies in the one-unit layer `U_59` but
not in `U_60`.  `CriticalUnitQuotient59` therefore constructs a genuine
nonzero class `[c]` in `U_59 / U_60`, defines the image there of the actual
field norm, and reduces the arithmetic question to the explicit exclusion
`[c] ∉ image(Norm)`.  `CriticalUnitCoefficient59` constructs the
coefficient `(u - 1) / lambda^59 mod lambda`, proves that its kernel is
exactly `U_60`, and upgrades it to an equivalence from `U_59 / U_60` onto
the additive group of the actual lambda residue field.  It then identifies
that residue field canonically with `ZMod 59`, proves Frobenius
`x^59 = x`, transports the cyclotomic Dwork identity
`59 / lambda^58 = -1` into the residue field, and computes the correction's
raw coefficient as exactly `-1`.  Its normalized form therefore sends `[c]`
exactly to `1`.  `CriticalUnitPowerSurjectivity59` proves by an
explicit completed-DVR Newton construction that every element of `U_60` is
a genuine 59th power.  It follows that membership of `[c]` in the quotient
norm image is equivalent—not merely necessary—to an exact norm witness for
`c`, to a norm witness for `zeta_59`, and to vanishing of the genuine
twisted-lambda Kummer cup.  `NormImageBridge59` now proves the expected
one-dimensional norm hyperplane directly from the explicit finite
triangular norm calculation: every actual norm in `U_59` lies in `U_60`, so
the quotient norm image is exactly zero.  Thus `[c]` is excluded without an
Artin--Hasse or local-reciprocity premise.
`PrimeKummerExplicitNorm` supplies every prime Kummer extension with the
selected-root power basis and expands every field norm as the exact finite
product over its Kummer conjugates.  `PrimeKummerTrace` proves in the same
coordinates, for every prime, that every nonconstant basis monomial has trace
zero and hence
`Trace(f(alpha)) = p * f.coeff 0` whenever `degree(f) < p`.
At `59`, `ExplicitNormResidue59` computes
`Norm(1 + c * alpha^j) = 1 + c^59 * (60 * lambda)^j` and proves for every
`0 < j < 59` that entering `U_59` forces this norm into `U_60`.  Thus all
single nonconstant power-basis perturbations are already silent at the
critical layer.  `PrimeTriangularUnitFactorization` now factors every bounded
polynomial, through degree `p - 1`, into those elementary factors and one
exact residual factor `1 + a*y`; this is a generic finite recursion rather
than a 59-case enumeration.  `PrimeTriangularNormBounds` proves that if the
nonconstant coefficients begin with a common ultrametric bound `q ≤ 1`, all
installed elementary coefficients retain that bound while the exact
`X^p` remainder improves to `q²`.  Its valuation-native companion
`PrimeTriangularValuationDepth` proves, over any `ℤᵐ⁰`-valued field, that
coefficients beyond every installed stage and the exact `X^p` quotient have
doubled depth.  `PolynomialSpectralNormBound` transports
this coefficient estimate into the extension: evaluation at a spectral
one-unit cannot enlarge the polynomial supremum norm.
`PrimeTriangularSpectralContraction` composes the two statements into one
exact evaluated factorization whose residual `a`-multiple has bound `q²`.
`PrimeTriangularExplicitNorm` computes the norm of the complete evaluated
triangular product as the exact base-field product
`∏ j, (1 + c_j^p * a^j)`, exposing the valuation residue of every factor.
`ValuationProductDominant` supplies the matching generic cancellation law:
when the nonzero perturbations have distinct valuations, a depth bound on
their full product forces the same bound on every perturbation.
`SpectralNormProductRemainder` then proves that norms of sufficiently deep
residual one-units stay that deep and that the error after the linear trace
term is quadratically smaller.  At the two ends of the local calculation,
`TwistedLambdaEisensteinIntegrality59` gives every unit-norm extension
element a degree-`< 59` selected-root expansion with integral coefficients
and unit constant term, while `CriticalUnitPowerKernel59` proves by the
computed Dwork/Frobenius cancellation that every first one-unit has 59th
power in `U_60`.  `TriangularSpectralDepth59` identifies real spectral
radii with exact integer lambda-depth, recovers the depth of every
selected-root coordinate, and specializes the generic contraction to an
actual depth-doubling remainder in the twisted extension.
`TriangularNormSeparation59` proves that the 58 elementary perturbations
have pairwise distinct nonzero valuations modulo 59; therefore, if their
complete triangular norm enters `U_59`, every elementary perturbation is
already in `U_60`, and their whole triangular-product norm is in `U_60`.
`TriangularResidualNormalization59` and
`PrimeTriangularSpectralAbsorption` normalize the residual one-unit and
absorb the additive remainder without losing its spectral bound.
`TriangularResidualStep59` packages one complete actual round: an exact
extension-field factorization, the depth recurrence `s ↦ 2*s+2`, and a
concrete unit in `U_60` equal to the norm of the extracted base factor.
`TriangularTerminalResidual59` proves that coordinate depth `s` puts the
actual residual norm in depth `s+1`; in particular, the depth-62 terminal
residual is already in `U_63 ⊆ U_60`.  `FiveStepResidual59` performs the
literal finite iteration
`0 → 2 → 6 → 14 → 30 → 62`, retaining the exact five-factor
decomposition and a concrete `U_60` unit equal to the product of their
actual field norms.  `InitialIntegralDecomposition59` connects an arbitrary
extension element with unit norm to the depth-zero input, using strict
smallness of the selected root at the closed integral coefficient boundary.
`PowerU1Reflection59` proves by residue Frobenius that
`u^59 ∈ U_1` forces `u ∈ U_1`.  Finally, `NormImageBridge59` composes
these results with triangular norm separation: every actual norm in `U_59`
already lies in `U_60`, so the complete critical quotient norm image is
bottom.  The explicit depth-59 correction and hence the local primitive
59th root are not norms, and the genuine twisted-lambda Kummer cup is
nonzero.  `NormImageConsequences59` propagates this unconditional input
through the local Kummer/cyclic-lift interfaces used inside Case II: the
Kummer character has no continuous `C_(59²)` lift, a normalized roots-valued inflation readout
exists, and one existential theorem packages that readout together with its
full normalization equation and all five normalized endpoint conclusions.
`Unit60KummerNormObstruction59` then cancels the already-trivial bare-lambda
cup from the twisted class and obtains a second unconditional obstruction:
the genuine unit-`60` Kummer cup is nonzero, `zeta_59` is not a norm from
the extension generated by a 59th root of `60`, and that extension's
concrete Kummer character has no continuous `C_(59²)` lift.
`ExactNormIntersection59` sharpens the norm result to the exact identity
`range(Norm) ⊓ U_59 = U_60`; at critical depth it identifies norm membership
and literal field-norm existence with vanishing of one named coefficient.
`NormalizedContinuousKummerPairing59` selects a normalized algebraic readout
and composes it with the genuine continuous cup to obtain total local and
global pairings.  This selected scalar readout is linear, but is not claimed
continuous or canonical as a local invariant.  `TwistedLambdaCupReceipt59`
retains the two differently typed degree-one factors, their actual
roots-valued continuous cup class, its proved nonvanishing, and its
normalized reading `= 1`; it does not collapse the primal and reflected
coefficient seats or claim a new global eigenspace theorem.
`ContinuousOldWildAdapter59`
restricts any such pairing to the old eigenspace seats and proves the full
`hash omega` adjoint law.  Finally,
`NormalizedContinuousWildLocalization59` inhabits all three fields of the
59-local core and the complete q-relaxed localization for the old-shaped
interface constructed from that same pairing.  Its self-calibration is
definitional; equality with an independently supplied historical wild
reading remains exactly the explicit universal calibration seam.
`wildLawfulness827_of_reciprocity` proves that reciprocity for this
one-column localization automatically supplies lawfulness on the conserved
827 kernel; reciprocity itself remains an open arithmetic interface.
`NormalizedContinuousReadout59` then compiles a stronger relation-(7a)
endpoint which internally supplies localization, boundary nonvanishing, a
member of the retained normalized fiber, and that reciprocity-derived
lawfulness.  `AlgebraicPointedIncidence827` proves that Fourier seating plus
a nonzero `ReflectedQRelaxedLocalizationLift827` constructs the formerly
independent `PointedTateIncidence827` package; no complement or splitting is
chosen.  `CyclotomicLocalizationEquivariance827` proves the Fourier seating
law for the canonical cyclotomic action and localization, so
`vandiverSevenA_of_normalizedContinuousCanonicalLift` is the strongest direct
endpoint: callers pass a reflected lift but neither incidence nor seating.
No such lift is inhabited.  `ReflectedLocalizationLiftCriterion827` makes
this exact: at any chosen 827-place, lift inhabitation is equivalent to
nonvanishing of `classSilentPointedCoordinate827` on the kernel of the
projected finite-S class obstruction.  That nonvanishing remains open, and
any hypothetical lift is proved to be a full reflected-character wave with
all 58 coordinates above 827 nonzero.  The remaining concrete inputs are
that lift, class-valued (7a) gauge seating,
`WildProcessesAtLeastSevenA`, and reciprocity.  There is an important exact boundary:
`normalizedWildCoefficientOfCanonicalLift59_eq_zero` proves that reciprocity
makes this one-column coefficient the zero map, while
`normalizedCanonicalLiftProcessesAtLeastSevenA_iff_gauge_eq_zero` proves that its
`WildProcessesAtLeastSevenA` premise is then equivalent to vanishing of the
entire class-valued gauge.  That gauge vanishing already implies (7a) directly
by `vandiverSevenA_of_classGauge_eq_zero`.  Thus this lift-facing endpoint is
a kernel-checked conditional/regression theorem, not by itself a
non-circular derivation of (7a); a finer nonzero readout or genuinely
independent comparison remains necessary within that local branch.  The
generic reciprocity layer now supplies a precise next shape:
`pairAt_add_pairAt_eq_zero_of_outside_two` retains an auxiliary column and
proves `wild + auxiliary = 0`, equivalently `wild = -auxiliary`, instead of
killing the only retained reading; the tame realization has a compiled
wrapper from its outside-two bookkeeping to that balance.  For the actual
cyclotomic lift this one-column theorem remains only a prototype, because the
lift is a full 58-place wave.  The full-orbit successor is the strict-Selmer
route below: it now retains and Fourier-processes the complete 827 orbit and
constructs the class readout, while leaving its lambda/Poitou--Tate comparison
explicit.  It does not provide a new all-prime FLT theorem.

For the full strict-Selmer Artin route, the class gauge and its tame reading
are now concrete.  `FermatFactorClassGaugeSeating59` exposes the genuine
strict-Selmer class map onto `ClassTorsion59`; its kernel is exactly the
global-unit range, and its value on the literal Fermat-factor difference is
`selectedClassGauge59`.  `StrictTameOrbitClassFactorization827` defines the
scalar reading as the literal sum of all 58 globally-root-oriented tame rows.
`ArbitraryUnitLocalReduction827` and
`ArbitraryUnitRawTameCarrierBridge827` then follow an actual ring unit through
Mathlib's `unitInclusion` and identify every row with its raw residue wave,
the genuine supported valuation of the relaxed input, the forced inverse
place orientation, and the global-root coordinate factor.

`ArbitraryUnitOrbitDecomposition827` and
`ArbitraryUnitFourierSilence827` prove that every global-unit residue wave has
zero inverse-oriented mode-43 coefficient.  Consequently
`ArbitraryUnitTameOrbitSilence827` kills the complete strict tame functional
whenever the relaxed valuation vector is the canonical pure reflected mode;
the quotient-representative argument upgrades this from ring units to all
`UnitModP` classes.  `NormalizedFullOrbitGlobalRealization827` removes the
former profile-existence premise: the retained normalized reflected fiber is
nonempty, and an actual global 827-relaxed Selmer carrier realizes the exact
58-coordinate normalized profile.  `NormalizedFullOrbitUnitSilence827`
combines these results with the exact strict Selmer sequence and constructs
the unique class readout factoring the concrete tame functional.  The
readout is forced by the quotient; it is not yet identified with an
arithmetic Artin map, and no distinguished relaxed carrier is chosen.

The W7 class-side seam is correspondingly much smaller than global
injectivity.  `PointwiseFaithfulSevenAReadout827` proves that the unique
factorizing readout only has to reflect zero at the single selected class:

```text
readout (selectedClassGauge59 pair) = 0
  -> selectedClassGauge59 pair = 0
```

Under that pointwise hypothesis, tame-orbit silence at the literal Fermat
factor difference is equivalent to `VandiverSevenA 0 1`.  No dimension bound
or injectivity theorem for the complete 59-torsion class group is required.
`FermatFactorClassGaugeCharacterBoundary59` also isolates the first step of
the optional character-component route: the selected class is fixed by the
canonical irregular projector exactly when the difference between the
literal Fermat Selmer class and its irregular projection lies in the genuine
global-unit range.  That unit-range receipt is not currently supplied, and
the reduction is transitively independent of the older Takagi proof.
`AllocatedPlusRootOddSupport59` nevertheless removes half of the support
problem unconditionally.  The root-of-unity normalization correction is in
the literal global-unit range, so the genuine class map kills it; cyclotomic
`-1` then carries the allocated plus root to the minus root, while the proved
relation `(7d)` makes the latter the negative of the former.  Hence both the
plus root and the actual `selectedClassGauge59` are fixed by the complete odd
projector.  Their remaining chi=15 obligation is now exactly the vanishing of
an explicit odd-minus-chi=15 complement, rather than an opaque seating claim.

`CharacterLinePointwiseFaithfulness59` makes the other W7 inputs equally
literal.  If the selected gauge is fixed by the actual chi=15 projector, the
image of that projector has `ZMod 59`-finrank one, and the constructed class
readout is nonzero on that image, then the readout reflects zero at the
selected gauge and the W7 equivalence follows.  Full class-group injectivity
is neither assumed nor needed.  The still-missing arithmetic facts are the
vanishing of the explicit odd complement, rank one of the selected character
line, and nonvanishing of the Artin readout on that line.

`FermatFactorArtinFourierBoundary827` removes the abstract value of that
readout from the remaining statement.  Every strict Selmer representative
has a well-defined 58-coordinate residue wave (independent of the chosen
Kummer representative), and every genuine tame row is its residue coordinate
times the supported valuation of the relaxed input.  Against the normalized
profile this gives the map-level identity, for every strict input `x`,

```text
classReadout (classGauge x) = - FourierCoefficient₄₄ (residueWave x).
```

The normalized profile determines both the strict functional and its class
readout independently of which global point in the reflected fiber is used.
For the Fermat-factor input, `(7a)` already implies that the displayed
coefficient is zero; W5 is now precisely the converse zero-reflection
statement for this concrete coefficient, not an unspecified Artin map.
`FermatFactorArtinCharacterCovariance827` further proves that each apparent
representative coordinate is a descended tame-symbol linear functional,
obtained by pairing with the inverse canonical uniformizer.  The whole wave
and mode-44 reading are therefore genuinely linear and satisfy the expected
chi=15 covariance on strict eigenspaces and on the image of the actual class
projector.  This establishes character alignment, but does not manufacture
character support, rank one, or nonvanishing.

`CanonicalModeFortyFourClassFactorization827` removes the normalized-fiber
point from this construction altogether.  The correctly signed mode-44
linear map kills the genuine `UnitModP` range, so exactness produces a unique
class-level factorization with no chosen reflected carrier in either its
statement or result.  Its kernel is the pullback of the class-readout kernel,
and injectivity is equivalent to the exact remaining zero-reflection law

```text
FourierCoefficient₄₄ (residueWave x) = 0
  -> classGauge x = 0.
```

Thus the class readout itself is now canonical; proving that it is faithful
on the needed class (or on the chi=15 line) remains arithmetic work.

`KummerFrobeniusRead827` gives this canonical readout a genuine local
arithmetic meaning.  In the universal residue Kummer algebra
`ZMod 827[T]/(T^59-u)`, literal residue Frobenius sends the Kummer root to
`u^14 * T`, since `827 = 59 * 14 + 1`.  The stored residue-character
coordinate is proved to be exactly the exponent of that multiplier, then
transported through the actual residue-field equivalences at every one of
the 58 places above 827.  Consequently the canonical class readout pulls
back to the negative mode-44 Fourier coefficient of the genuine
residue-Frobenius exponent wave.  This is the local Kummer--Frobenius half of
W5; it does not construct a global ray-class Artin map, prove global
reciprocity, or establish faithfulness of the resulting class readout.

`LocalKummerFrobeniusFactorization827` bundles Frobenius as an actual
`ZMod 827`-algebra endomorphism and promotes the comparison to the map-level
identity

```text
canonicalModeFortyFourClassReadout827 ∘ fermatFactorClassGaugeMap59
  = localKummerFrobeniusModeFortyFourLinearMap827.
```

For every reflected carrier realizing the normalized 58-coordinate profile,
the same module restricts this identity to the genuine irregular primal
Poitou--Tate test space: its seated orbit boundary is simultaneously the
canonical class readout and the Fourier read of the literal Frobenius
exponent wave.  This supplies the local/profile comparison part of the
requested W5 equality of maps; producing that carrier with W1's lambda
coordinate and upgrading local Frobenius to global Artin reciprocity remain
separate obligations.

`ResidueKummerFrobeniusAutomorphism827` further proves that the bundled
Frobenius endomorphism is reversible.  Its explicit inverse sends the
universal Kummer root to `u^(-14) * T`, and the two compositions are the
identity algebra map; the automorphism's order divides 59.
`StrictOrbitKummerFrobeniusAutomorphism827` instantiates this reversible
action at each of the 58 actual orbit coordinates and identifies its root
multiplier with the stored exponent-wave coordinate.  The local read
therefore comes from genuine cyclic algebra automorphisms, while no global
class-field-theoretic Artin element is claimed.

`LocalKummerFrobeniusFaithfulness827` proves the corresponding sharp local
detection statement.  A nonzero stored exponent makes the local
automorphism nonidentity, so its order is exactly 59.  Consequently a
nonzero canonical class readout produces at least one exact-order
Frobenius action among the 58 actual coordinates.  Nonvanishing on the
chi=15 class line additionally produces an existential genuine strict
Selmer preimage in that line with such an action; no class-group section is
chosen.  This is local faithfulness and does not assert the converse or
global Artin faithfulness.

`GlobalClassKummerFrobeniusReadout827` records the strongest presently
proved global descent of this local construction.  There is a unique
`ZMod 59`-linear readout on the actual 59-torsion ideal class group whose
pullback along the strict-Selmer class gauge is the signed mode-44 Fourier
coefficient of the 58 genuine local Frobenius exponents.  In particular,
the coefficient is independent of the chosen strict-Selmer representative
and vanishes on every representative of the zero ideal class.  This is a
class-level descent theorem; it still does not identify the readout with a
ray-class Artin character or prove the global Kummer--Artin comparison
required to cancel the W1 Poitou--Tate boundary.

`StrictOrbitResidueWavePlaceCovariance827` proves the missing transport law
for the actual 58 place coordinates.  Cyclotomic action on a strict Kummer
class becomes the corresponding translation of the orbit place, including
the forced change of globally rooted residue coordinates.  Consequently the
complete residue and Frobenius exponent waves of every genuine chi=15
strict class are pure mode 44.  On that eigenspace, one nonzero local
coordinate therefore forces the mode-44 Fourier coefficient to be nonzero.
The theorem does not itself produce such a coordinate or invoke global
Artin reciprocity.

The wild-side comparison has also moved beyond abstract linear algebra.
`WildOrbitBoundaryComparison827` transports the two explicit global Kummer
classes to exactly the retained W1 `H¹` factors, recovers the W1 `H²` cup and
its normalized value one, and curries both the normalized lambda reading and
all 58 genuine tame rows into linear functionals on the same actual seated
Selmer space.  For the same globally realized 827-relaxed reflected point,
the orbit functional is literally the restriction of the strict tame
functional.  Under the existing `GlobalReciprocityLaw` interface, Lean now
proves the two maps are negatives, have equal kernels, inhabit one explicit
one-dimensional line, and differ by a unique unit whenever the orbit map is
nonzero.

The remaining wild-side obligations are therefore sharply localized.  The
normalized 827 point is not yet proved to have the exact lambda-local
reflected factor retained by W1.  `LambdaOrbitLocalizationFiber827` now
packages the actual lambda class and all 58 supported valuations into one
`ZMod 59`-linear localization map and defines its fiber over the exact W1+W3
target.  Nonemptiness of that fiber is proved equivalent to the existing
normalized W3 fiber containing a point with W1's prescribed lambda
localization.  `LambdaOrbitAffineKernelCriterion827` sharpens this further.
After fixing any existing normalized W3 point `y₀`, a compatible point
exists exactly when

```text
W1.reflected - lambdaLocalization(y₀)
```

lies in the range of lambda localization restricted to the kernel of all 58
orbit-valuation coordinates.  A lambda-plus-827 Poitou--Tate theorem must
still prove precisely that range membership; no point is hidden in the
definition.  `LambdaOrbitAffineCokernel827` records the same condition as a
literal cokernel class and proves it independent of the chosen W3
basepoint.  `CanonicalW1LambdaObstruction827` exposes that class without a
publicly selected lift, and `CanonicalW1LambdaBoundary827` evaluates it
against the complete dual annihilator of the restricted lambda image.  Lean
proves the exact point-free equivalences

```text
W1W3CompatibleFiber827 is nonempty
  <-> canonicalW1LambdaObstruction827 = 0
  <-> canonicalW1LambdaBoundary827 = 0.
```

These are the canonical obstruction and all of its scalar boundary charges,
not a proof that either vanishes.  `CanonicalW1PoitouTateReduction827` now
maps the genuine strict chi=15 primal space into the complete annihilator
test space and proves, under the explicit global-reciprocity interface, that
the canonical boundary restricted to those tests is exactly

```text
W1 receipt functional + local Kummer--Frobenius mode-44 functional.
```

It then proves boundary vanishing, obstruction vanishing, and nonemptiness
of the W1+W3 compatible fiber from exactly two visible hypotheses:
surjectivity of this primal-test representation (the Poitou--Tate theorem)
and cancellation of those two displayed functionals (the remaining global
Kummer--Artin comparison).  Neither hypothesis is manufactured or hidden.

`CanonicalW1PointedIncidenceBridge827` now gives a more literal two-charge
form of that reduction.  It combines genuine reflected lambda localization
and the selected 827 coordinate into one map

```text
global reflected carrier -> H1_lambda x ZMod 59
```

and defines the corresponding boundary into the dual of the actual
chi=15 primal test space.  Global reciprocity proves the inclusion
`range(localization) <= ker(boundary)`.  The reverse inclusion is isolated
as the exact missing Poitou--Tate lifting direction; together with the
map-level equality saying
that the W1 receipt is the negative local Frobenius functional, it produces
the nonempty W1+W3 compatible fiber directly, without a selected lift.  The
current lambda factor is still the ambient unprojected continuous `H1`.
The intended cheaper formulation should replace it by the reflected local
quotient/character seat described in `notes/7A-ARTIN-READ.md`; the module records
the stronger ambient-surjectivity diagnostic without presenting it as that
final PT theorem.

`LambdaReflectedLocalSeatAudit827` also prevents an unsafe shortcut in that
refinement.  Since `GaloisIndex59` is definitionally `(ZMod 59)ˣ`, Lean can
infer its ordinary scalar action on local continuous `H¹`; this is not the
outer cyclotomic action.  The module proves that using this accidental
action makes the reflected power-44 eigenspace zero.  For an honest outer
local representation it defines the intended reflected seat and proves
that the smallest carrier containing every genuine reflected localization
and W1's retained receipt lies in that seat exactly when localization
covariance and receipt seating both hold.  Constructing the completion-level
cyclotomic action and its induced cohomological naturality remains open.

The nonzero ambient W1 cup has not yet
been shown nonzero after restriction to the genuine seated primal Selmer
space, and
`TwistedLambdaStrictSelmerObstruction59` shows why its obvious left factor
cannot serve as that witness: the explicit W1 radicand has lambda valuation
`-1`, whereas every strict 59-Selmer representative has lambda valuation
divisible by 59.  Thus a different strict chi=15 class must be produced and
paired nontrivially with W1's retained reflected factor.
`IrregularPrimalClassGaugeBridge827` proves that the class gauge restricted
to that strict chi=15 primal space has range exactly the genuine chi=15
class-projector image.  Consequently seated-orbit transversality in W4 is
equivalent to nonvanishing of the canonical class readout on that image—the
W7 nonvanishing input.  `CanonicalW4ClassReadoutBridge827` carries this
equivalence through genuine global reciprocity: both wild transversality
and the unique-unit wild/orbit comparison now consume that same canonical
W7 nonvanishing premise directly, with no independent `horbit` hypothesis.
Those are now one seam, not two.  The rank-one and selected-class seating
inputs of W7 remain separate, and
`GlobalReciprocityLaw` is still consumed rather than constructed.

There is now, however, a separate completed state-to-history route at the
same exponent.  `FermatStateTakagiSevenA59` proves the Takagi relation for the
allocated Fermat pair and kills both actual root classes.
`FermatStateEquationEight59` turns this into literal factorizations
`q = epsilon * rho^59`; `FermatStateSelmerUnitLifts59` and
`FermatStatePrimalUnitProjection59` identify the resulting genuine Selmer
and irregular-mode unit classes.  The actual unit/class bridge is organized
as follows:

```text
CyclotomicUnitSelmerNaturality59
  unit quotient action + inclusion intertwiner + projector naturality
→ CyclotomicSelmerClassNaturality59
  actual class-group action + strict Selmer class-map intertwiner
→ FermatFactorClassProjection59
  Takagi kills the projected actual class obstructions
→ FermatStateUnitClassKernel59
  explicit projected equation-(8) coefficient units and their actual
  plus-minus difference land in that kernel
```

The action and naturality portion of this chain is prime-parametric; the
equation-(8), Takagi, and plus/minus Fermat-state endpoints shown here remain
specific to exponent `59`.  Thus this is not an all-prime FLT theorem, and it
does not close the separate Vostokov/local-reciprocity branch.  Finally,
`FermatStateHistoricalDescent59` constructs the initial historical state at
`m = 29`, produces an admissible successor at `m = 57` with strictly smaller
prime-ideal support, invokes the proved uniform continuation, and exports
both `SecondCaseExcluded 59` and `Fermat.HoldsAt 59`.  This route closes the
fixed exponent without claiming that the still-experimental local
reciprocity branch has been completed.

[`Fermat/Exponents/FiftyNine/Conservation/Verification.lean`](Fermat/Exponents/FiftyNine/Conservation/Verification.lean)
is the non-imported executable audit leaf for this campaign.  It checks the
named endpoints, dependency guards, compatibility modules, and the standard
axiom budget separately from the public umbrella import.
[`Fermat/Exponents/FiftyNine/Conservation/HistoricalVerification.lean`](Fermat/Exponents/FiftyNine/Conservation/HistoricalVerification.lean)
is its deliberately separate sibling audit for the state-to-history route,
including the unit/class naturality and class-kernel receipts.  Keeping the
two leaves separate preserves the clean conservation laboratory's exclusion
of the historical imports.

[`Fermat/Descent/Regular/`](Fermat/Descent/Regular/) contains reusable Faulhaber
infrastructure and the checked historical bridge

```text
power sums → Bernoulli numerators → cyclotomic class-number regularity
```

The deep Bernoulli/class-group equivalence comes from the pinned
[`KummerCriterion`](https://github.com/riccardobrasca/KummerCriterion)
formalization.  Since the locally patched `flt-regular` core no longer
accepts that condition as a premise, its generic FLT endpoint is deliberately
reported as a separate result with every temporary premise and seam exposed.
[`Fermat/Descent/Quadratic/`](Fermat/Descent/Quadratic/) contains
quadratic-ring and unit calculations shared by several elementary descents.

### The seven-fold ladder

[`Fermat/Experiments/Ladder/`](Fermat/Experiments/Ladder/) records the campaign's measured
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

[`notes/`](notes/) contains task briefs, audits, handoffs, and working or
provenance records.  It is outside the Lean library and is not the
authoritative surface for current theorem status; the checked Lean endpoints
and the public-results table above are.

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
lake build Fermat.Experiments.Ladder.Response
lake build Fermat.Experiments.Ladder.FaulhaberResponse
lake build Fermat.Experiments.Ladder.HistoricalResponse
lake build Fermat.Descent.KummerIso
lake build Fermat.Descent.KummerIso.Regressions
lake build Fermat.Exponents.ThirtySeven.VandiverHistoricalAssembly37
lake build Fermat.Exponents.FourHundredNinetyOne.VandiverHistoricalAssembly491
lake build Fermat.Exponents.FourHundredNinetyOne.SecondCase
lake build Fermat.Exponents.FiveHundredEightySeven.VandiverHistoricalAssembly587
lake build Fermat.Exponents.SixHundredSeven.VandiverHistoricalAssembly607
lake build Fermat.Exponents.SixHundredNinetyOne.VandiverHistoricalAssembly691
lake build Fermat.Exponents.OneThousandFiftyOne.Regularity
lake build Fermat.Exponents.OneThousandThreeHundredEightyOne.VandiverHistoricalAssembly1381
lake build Fermat.Exponents.OneThousandEightHundredThirtyOne.VandiverHistoricalAssembly1831
lake build Fermat.Experiments.Ladder.FourHundredNinetyOne
lake build Fermat.Experiments.Ladder.FiveHundredEightySeven
lake build Fermat.Experiments.Ladder.SixHundredNinetyOne
lake build Fermat.Experiments.Conservation.PrimeCyclotomicSelmerVerification
lake build Fermat.Exponents.FiftyNine.Conservation.CyclotomicUnitSelmerNaturality59
lake build Fermat.Exponents.FiftyNine.Conservation.CyclotomicSelmerClassNaturality59
lake build Fermat.Exponents.FiftyNine.Conservation.FermatFactorClassProjection59
lake build Fermat.Exponents.FiftyNine.Conservation.FermatStateUnitClassKernel59
lake build Fermat.Exponents.FiftyNine.ConservationProof
lake build Fermat.Exponents.FiftyNine.Conservation.HistoricalVerification
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
#check Fermat.holdsAt_fiftyNine_stateEquationEight
#check Fermat.FiftyNine.Conservation.CyclotomicUnitSelmerNaturality59.unitInclusionLinearMap59_characterProjector
#check Fermat.FiftyNine.Conservation.CyclotomicSelmerClassNaturality59.strictSelmerClassLinearMap59_characterProjector
#check Fermat.FiftyNine.Conservation.FermatStateUnitClassKernel59.exists_explicitProjectedUnitLift_classSilent_fermatPlus59
#check Fermat.FiftyNine.Conservation.FermatStateUnitClassKernel59.exists_explicitProjectedUnitLift_classSilent_fermatMinus59
#check Fermat.FiftyNine.Conservation.FermatStateUnitClassKernel59.exists_explicitProjectedUnitDifference_classSilent59
#eval Fermat.Ladder.FaulhaberResponse.responseData
#check Fermat.Ladder.FourHundredNinetyOne.proofBacked
#check Fermat.Ladder.FiveHundredEightySeven.proofBacked
#check Fermat.Ladder.SixHundredNinetyOne.proofBacked
#check Fermat.Ladder.HistoricalResponse.campaignProofs
#eval Fermat.Ladder.HistoricalResponse.responseData
```

The final endpoints are routinely checked with `#print axioms`. Historical
explicit-prime endpoints and the nine finite
`KummerIso.ResidueRegressions` endpoints depend only on Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`. The generic `*_generic` and
`*_kummerIso` endpoint families additionally expose the temporary
`SophieGermainAuxiliarySearchTermination` axiom. The campaign uses no
`sorry` or `admit`; executable searches are reflected back into checked
propositions.
