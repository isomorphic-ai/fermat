# Kummer--Tate / former Vostokov tier-(c) theory handoff

**Date:** 2026-08-17
**Repository:** `~/fermat`, branch `credit-flow`
**Implementation checkpoint:** `cc18d35`
**Audience:** the theory goblin deciding the next mathematical lemma, not the
Lean engineer packaging it

## 2026-08-17 Kummer--Tate update (current route)

The earlier tier-(c) logarithmic recommendation below is now historical
context, not the foundational implementation plan.  The current route keeps
the complete local Kummer classes and uses their cohomological interaction:

```text
global Kummer class
  -> localization into the local Kummer quotient
  -> left/right H¹ Kummer maps
  -> oriented cup product in H²
  -> readout on the actual Kummer-cup span
  -> normalized continuous local-invariant comparison
  -> ZMod 59 reading
```

The following parts are now kernel-checked:

- `LocalKummerTransport` maps Kummer quotients functorially along a field map
  and pulls a local quotient pairing back to global classes.
- `KummerTateCup` proves the explicit low-degree cup cochain is a cocycle,
  proves right-coboundary independence, descends through Mathlib's actual
  `H¹` quotient, and bundles the result bilinearly.
- `KummerTateReadout` composes cup product with a supplied linear
  `H² -> k` readout.  Calling that map the normalized local invariant still
  requires the continuous comparison theorem below.
- `CohomologicalKummerPairing` assembles two supplied Kummer homomorphisms and
  a supplied linear readout into `WildKummerPairing.Pairing`; the genuine
  discrete Kummer maps enter at `DiscreteKummerTatePairing` below.
- `LocalKummerH1` constructs the discrete absolute-Galois Kummer map
  `Fˣ/(Fˣ)^n -> H¹(G_F, μ_n)`: chosen roots define the cocycles, and
  an explicit multiplication-defect coboundary proves multiplicativity before
  descent through the power quotient.  The file does not expose a separate
  theorem comparing cocycles built from two arbitrary choices of the same
  root.
- `LocalKummerH1.continuous_cocycleValue` proves that this concrete cocycle is
  continuous for the Krull topology: every nonempty fiber is a coset of the
  chosen algebraic root's open stabilizer.  Thus continuity of the Kummer
  cocycle itself is no longer part of the theory request.
- `KummerOrientation` uses a supplied primitive `n`-th root in `F` to prove
  that absolute Galois fixes `μ_n`, constructs an equivariant representation
  isomorphism `μ_n ≃ ZMod n`, and transports the actual Kummer class to the
  trivial left coefficient line.  The same orientation is implemented in
  degree two.
- `DiscreteKummerTatePairing` closes the generic discrete assembly using the
  two genuine Kummer maps; its older total-`H²` readout remains a useful
  algebraic adapter, not a claim about the canonical continuous invariant.
- `KummerCupSpanReadout` takes the cheaper sufficient tier: it asks for a
  linear scalar readout only on the submodule spanned by cups of actual
  Kummer images, assigning no values to unrelated discrete `H²` classes.
- `LocalCompletion59` constructs the literal cyclotomic place
  `lambda = (zeta_59 - 1)`, proves that its ideal is nonzero, prime, and lies
  over `59`, and supplies its adic completion, embedding, and transported
  primitive root.
- `KummerCupSpanLocalization59` installs the span-restricted pairing at that
  actual lambda completion, pulls it back to global Kummer classes, derives
  the strict-to-827-supported landing, and constructs the quotient-first core
  from only the span readout and independent old-reading calibration.
- `ReflectedWildKummerCoreAt59` is now quotient-first.  It stores that
  pairing directly; representative formulas are optional constructors or
  comparison charts.
- `KummerTateLocalization59` feeds the cohomological pairing into the real
  59-local consumer.  Its generic adapter retains landing and calibration as
  separate theorem inputs; its canonical-action specialization derives the
  landing and retains only calibration.
- `CyclotomicSelmerAction59` constructs the common ambient cyclotomic action,
  its strict and 827-supported restrictions, and the intertwining inclusion,
  proves height-one valuation covariance from ideal-multiplicity transport,
  and derives the reflected landing with no supplied certificate.

The remaining arithmetic is sharply typed and must not be conflated:

1. Package the now-proved continuous Kummer cocycles in continuous local
   Galois cohomology, and compare that low-degree theory's cup product with
   the constructed **discrete** absolute-Galois cup and chosen-`zeta_59`
   orientations.  The concrete cocycle continuity, algebraic maps, and actual
   lambda completion are no longer missing; the cohomology-level
   topology/comparison layer is.
2. Construct and normalize the continuous
   `H²(G_(K_lambda), mu_59) -> F_59` invariant, prove the cup--Hilbert-symbol
   comparison with the fixed sign convention, and factor its reading through
   `LambdaKummerCupSpanReadout59`.
3. Prove the independent comparison with the existing old wild reading.
4. Separately, use Poitou--Tate exactness for the required global reflected
   lift.  Local duality does not fabricate that class.

The current `KummerTateCup` layer uses Mathlib's discrete low-degree group
cohomology.  It validates the algebraic cup/descent mechanism, but it is not
yet a declaration of continuous local Galois cohomology.  That topology seam
must remain visible.

Lean library boundary: the pinned
`Mathlib/Algebra/Category/ContinuousCohomology/Basic`
provides the abstract homogeneous continuous-cochain complex,
`continuousCohomology`, and a degree-zero adapter.  It does not provide
continuous `H¹`/`H²` aliases, an inhomogeneous-cocycle inlet, a continuous cup
product, a normalized local invariant, or local
reciprocity/Hilbert-symbol/Tate-duality theorems.  Those are real
infrastructure tasks, not missing imports.

Nor does the present adapter prove a filtration, perfect local Tate duality,
or local `Delta`-equivariance of the cup-span readout.  The downstream
`hash omega` adjoint law is currently derived formally from the already-seated
character eigenspaces and bilinearity; it is not a substitute for an ambient
local equivariance theorem.

Dimension target, not a checked statement about the current discrete Lean
types: the intended **continuous** local degree-one spaces are
60-dimensional perfect dual partners in the stated 59-adic situation.  Their
direct sum has the canonical hyperbolic/symplectic form.  Calling either
individual 60-dimensional space symplectic requires an additional
self-identification and alternating-form choice.  No finite-dimensionality or
perfectness theorem for the repository's discrete `H¹` is asserted.

The Iwasawa trace-product material below remains useful as a later coordinate
comparison on the 58-dimensional analytic layer.  It is no longer the
foundational object and must not erase the valuation or torsion directions.

## Historical tier-(c) short version

Everything from this heading through the historical bottom line records the
earlier Iwasawa tier-(c) work queue.  It is retained as provenance, but it is
not the current frontier: the canonical actions are now constructed and the
current local seam is the cup-span/continuous-invariant comparison described
above.

The Lean algebra is no longer the obstruction.

We have a checked constructor which turns a total Iwasawa-shaped trace
product into the representative Kummer pairing, descends it through 59th
powers, proves calibration on quotient classes from calibration on chosen
representatives, derives the strict-to-relaxed landing from action
compatibility, and then constructs the complete wild localization object.

What is missing is arithmetic provenance for two abstract inputs:

1. **Local-symbol provenance.** Construct total local coordinates on
   `Kˣ`, including valuation and cyclotomic-torsion information, and prove
   that their trace product is the actual 59-Hilbert/wild reading.
2. **Galois-action provenance.** Construct the actual actions on the strict
   and 827-relaxed Selmer carriers and prove that the canonical support
   inclusion intertwines them.

The present parameters `wild`, `rho`, and `rhoQ` are arbitrary structures
satisfying only their displayed algebraic laws. Those laws do not determine
the intended arithmetic objects. This is why more tactic search cannot close
the gap.

Tier (c) is therefore **uninhabited but unrefuted**: no implementation of
the intended arithmetic package exists in the tree, but the shape audit did
not prove that such a package cannot exist. That is not permission to open
the forbidden tier-(d) series.

This document spells out exactly what is already proved, where the theory
must enter, and what a useful answer should contain.

## 1. Why this local problem exists

This is the conservation proof of relation (7a) at exponent 59. It is not the
already completed historical/Vandiver proof of FLT(59), and it is not the
separate regularized-Kummer splice.

The `flt9_*` regularized-Kummer material repairs a different global Case-II
route: ideal principalization/equation (7d), deep unit ratios, Bernoulli
precision, and a proposed Selmer-regulator step. It does not currently
construct a wild Hilbert symbol, a norm-coherent local lift, a local trace
formula, or the action naturality requested here. Importing its proposed
regulator would be a larger reciprocity-level alternative, not a proof of
the present tier-(c) interface.

The global conservation route has already handled the tame local readings.
Its remaining local input is the wild reading at the prime over 59. The Ulam
readout wants that reading not only on the old strict reflected Selmer
carrier, but on the carrier whose local condition is relaxed at the places
over 827.

At checkpoint `29fdbe9`, the compiled target was representative-first.  The
current target has since been migrated to:

```lean
structure ReflectedWildKummerCoreAt59 ... where
  pairing : WildKummerPairing.Pairing 59 K
  landing : ReflectedEmptySupportLanding827 rho rhoQ omega chi
  old_calibration : ∀ x : OldPrimal59 rho chi,
      ∀ y : OldReflectedDual59 rho omega chi,
    pairing (toKummerClass x) (toKummerClass y) =
      wild.reading x y
```

See
[`VostokovLocalization59.lean`](Fermat/FiftyNine/Conservation/VostokovLocalization59.lean#L70-L85).

An inhabitant of those three fields already constructs the complete
`ReflectedWildLocalizationAt59`, including:

- the canonical strict-to-relaxed map;
- injectivity of that map;
- the total q-relaxed reading;
- the full group-algebra `hash omega` adjoint law; and
- agreement with the old reading.

Those downstream steps are finished Lean engineering. They are not the
current mathematical gap.

Nothing here proves relation (7a) unconditionally. Even after localization,
wild lawfulness, class-valued gauge seating, the endpoint kernel inclusion,
global reciprocity, and a normalized-fiber member remain separate inputs.
The surviving `ker G` and the whole normalized fiber remain intact.

## 2. What the C1 shape audit actually found

The task began with the hope that the two residual labels
`statewiseSelmerLift` and `transverseDetectorComponent` denoted two special
Artin--Hasse shapes. They do not, at the current typed boundary.

The literal inputs are:

```lean
statewiseKummerClass x  = toKummerClass x
transverseKummerClass y = toKummerClassAt y
```

where

```lean
x : OldPrimal59 rho chi
y : QRelaxedReflectedDual827 rhoQ omega chi
```

Their exposed representatives are the classical quotient choices
`quotientRepresentative x` and `quotientRepresentativeAt y`. Lean proves
that they read back to the exact quotient classes, but no theorem identifies
either choice with a normalized Fermat factor or an Artin--Hasse generator
combination.

Accordingly, the honest current decomposition has covered part zero and
retains each complete class as residual. This is **not** a theorem that the
classes are mathematically outside the Artin--Hasse subgroup. It is a theorem
that the present interface contains no coverage proof.

There is a second, stronger shape fact. Every old strict reflected class has
827-coordinate zero after canonical inclusion, whereas every point of the
normalized q-relaxed fiber has selected coordinate one. Hence:

```lean
normalizedFiber_not_mem_range_oldReflected
```

No normalized fiber point is secretly an old strict point. Therefore old
calibration cannot be extended to the relaxed carrier by pretending that the
new point came from the old carrier, and no section/complement/splitting is
available or allowed.

See
[`VostokovShapeAudit59.lean`](Fermat/FiftyNine/Conservation/VostokovShapeAudit59.lean).

### Consequence for the formula ladder

- Tier (a), the current banked Artin--Hasse values, is insufficient at the
  tracked interface.
- Tier (b), the special `(zeta,u)` and `(pi,u)` formulas, is not licensed by
  the current representative shapes. More decisively, the target stores a
  total pairing and calibrates **every**
  `OldPrimal59 × OldReflectedDual59` pair, not two selected campaign values.
- Tier (c), an Iwasawa-style total extension, is the cheapest tier not
  refuted.
- Tier (d), the full Vostokov--Brueckner series, remains forbidden until
  tier (c) is structurally refuted.

## 3. The tier-(c) algebra that Lean has already finished

The generic constructor is in
[`IwasawaTracePairing.lean`](Fermat/Conservation/IwasawaTracePairing.lean).

For a ring `A`, it asks for three additive maps:

```lean
structure TotalAugmentedCoordinates (p) (K) (A) where
  leftCoordinate  : Additive Kˣ →+ A
  rightCoordinate : Additive Kˣ →+ A
  traceModP       : A →+ ZMod p
```

It **defines**, rather than assumes, the representative pairing:

```lean
B(a,b) = traceModP (leftCoordinate a * rightCoordinate b)
```

Lean has proved:

1. additivity in both variables;
2. silence on 59th powers, formally from bilinearity and characteristic 59;
3. descent through both Kummer quotients; and
4. exact evaluation of the descended pairing on chosen representatives.

Thus the questions “is it bilinear?” and “does it descend?” are closed.

The remaining arithmetic is deliberately exposed as:

```lean
structure ArithmeticSpecification ... where
  normLiftKappaDerivative : Additive Kˣ → A
  totalAugmentedLogarithmicCoordinate : Additive Kˣ → A
  traceValue : A → ZMod p

structure Realizes (coordinates) (arithmetic) : Prop where
  leftCoordinate_eq  : ...
  rightCoordinate_eq : ...
  traceModP_eq        : ...

def IsComparedOn (arithmetic) (leftRep) (rightRep) (reading) : Prop :=
  ∀ x y,
    arithmetic.traceValue
      (arithmetic.normLiftKappaDerivative (leftRep x) *
       arithmetic.totalAugmentedLogarithmicCoordinate (rightRep y)) =
    reading x y
```

`Reduction` packages the coordinates, their arithmetic realization, and the
independent comparison theorem. It stores no arbitrary pairing value.

At 59, [`IwasawaLocalization59.lean`](Fermat/FiftyNine/Conservation/IwasawaLocalization59.lean)
binds that reduction to the exact C1 representatives. The theorem
`descend_eq_oldReading` proves quotient-level calibration from:

- representative-level comparison;
- the two quotient-representative readback theorems; and
- the strict/q-relaxed Kummer-class identity.

Given that reduction and action compatibility,
`toReflectedWildKummerCoreAt59` fills all three target fields and
`toReflectedWildLocalizationAt59` fires the complete localization producer.

## 4. Gap A — construct and identify the actual wild symbol

### 4.1 Required mathematical object

We need an independently defined arithmetic package, for the completion of
the cyclotomic field at the prime over 59, which supplies:

\[
L : K^\times \longrightarrow A,
\qquad
R : K^\times \longrightarrow A,
\qquad
T : A \longrightarrow \mathbf F_{59},
\]

with `L`, `R`, and `T` additive after wrapping multiplication in
`Additive Kˣ`. These maps must be total on `Kˣ`, because Lean uses them to
define a total representative pairing. The minimum comparison theorem only
has to identify that pairing on the chosen representatives of every
`OldPrimal59 × OldReflectedDual59` pair. A stronger theorem on all of
`Kˣ × Kˣ` would be welcome, but is not required to fill the present core.

On the required pairs, we need

\[
(a,b)_{59}=T(L(a)R(b))
\]

for every pair required by the total representative pairing. Here `L` is
the norm-coherent lift/kappa-derivative side and `R` is the logarithmic side.

The common coefficient ring `A` may be a genuine local coefficient algebra,
a graded algebra retaining several contributions, or another natural ring
in which multiplication plus trace produces the required cross-terms. The
Lean constructor does not force `A` to be one-dimensional.

If the natural Iwasawa formula is a finite sum rather than literally one
scalar product, it may still fit by placing the summands in an augmented
coefficient algebra. The theory goblin should say what `A`, `L`, `R`, and
`T` actually are. If no natural such encoding exists without weakening the
law, that is a genuine refutation of the current tier-(c) constructor and
must be stated explicitly.

### 4.2 Why a principal-unit logarithm is not enough

The available completed logarithm is defined on an already-normalized
principal-unit domain. A total element of a local field has, schematically,

\[
a=\pi^{v(a)}\,\tau(a)\,u_1(a),
\]

where `pi` is a uniformizer, `tau(a)` retains residue/torsion information,
and `u_1(a)` is a principal unit.

Keeping only `log(u_1(a))` loses information:

- the pinned library proves the cyclotomic uniformizer has nonzero lambda
  valuation (`lambdaPiFieldUnit_valuation`);
- the same-prime finite logarithm vanishes on the cyclotomic root-of-unity
  direction (`samePrimeFiniteLog_zetaPowSubOne_eq_zero`); and
- uniformizer--unit and torsion--unit cross-terms can contribute to a total
  Hilbert pairing.

Therefore “divide by a power of `pi`, take the principal log, and forget the
rest” is not a valid total formula.

There is also a clean algebraic obstruction to the most obvious choice of
coefficient ring. If `A` is 59-torsion-free, as a characteristic-zero local
completion is, every additive homomorphism

```text
Additive Kˣ →+ A
```

kills the subgroup `μ₅₉`: the image of an element of additive order 59
must itself have order dividing 59. Thus the existing completed logarithm
cannot become the total right coordinate merely by changing its domain.
The theory must either use an augmented coefficient algebra with a genuine
mod-59/torsion block (and whatever valuation block is needed), or explain
why the classical formula requires a more general internal constructor than
one product `T(L(a) * R(b))`. Generalizing that internal constructor is
allowed if necessary; weakening the final bilinear pairing is not.

There is a potentially useful refinement for the theory expert. Strict
Selmer representatives have valuation divisible by 59 at every height-one
place. Locally, the uniformizer contribution may therefore be removable by
a 59th-power change of representative, and the prime-to-59 Teichmueller part
may also be a 59th power. The remaining 59-torsion/root-of-unity factor is
not removed by the logarithm. A theorem giving the exact quotient-level
normal form

\[
[a]=[\zeta^{j}u_1]
\quad\text{in }K_v^\times/(K_v^\times)^{59}
\]

could substantially simplify the right coordinate. That theorem is not
currently in the Lean tree, and the total representative target still needs
an honest extension to arbitrary representatives.

### 4.3 The decisive comparison theorem

Even perfect coordinates do not yet solve the typed target. The current
`wild` parameter is an arbitrary `WildLocalInterface`. It contains only:

```lean
reading : OldPrimal59 →+ (OldReflectedDual59 →+ ZMod 59)
adjoint_law : reading (a • x) y = reading x ((hash omega a) • y)
```

See
[`TamePlacePairing.lean`](Fermat/Conservation/TamePlacePairing.lean#L167-L188).

Bilinearity and the adjoint law do not characterize the Hilbert symbol. For
example, scalar multiples of a lawful reading retain those formal laws. So
Lean cannot prove that an independently defined Iwasawa formula equals every
possible supplied `wild.reading`.

The theory must provide arithmetic provenance in one of two honest forms:

1. **Preferred:** construct the actual Hilbert/Iwasawa wild interface and
   thread that specific object through the consumer; or
2. supply a realization theorem saying that the already selected `wild` is
   the restriction of the independently defined Hilbert symbol.

The required comparison is, substantively:

```lean
∀ x : OldPrimal59 rho chi,
  ∀ y : OldReflectedDual59 rho omega chi,
    T (L (representative x) *
       R (representative (include y))) =
      wild.reading x y
```

It must quantify over every old-carrier pair. Two numerical values or two
campaign samples are insufficient.

There is one more provenance detail: the current `distinguishedPlace`
parameter is an arbitrary height-one place. The local formula is naturally
at the cyclotomic lambda prime. A concrete instance must specialize the
distinguished place to that prime, or prove the required identification.

### 4.4 What already exists nearby

The pinned `KummerCriterion` dependency already contains useful pieces:

- the cyclotomic lambda prime and explicit uniformizer;
- its valuation calculation;
- valuation-completion integer and field infrastructure;
- formal Artin--Hasse exponential/logarithm machinery;
- `completedLog` on the principal-unit domain `U₁`, including its
  additivity, power, depth, and cyclotomic-equivariance laws;
- residue-lift and Dwork-coordinate calculations; and
- a rank-58 Dwork power basis over the rational completed integer ring.

Some source comments advertise a broader lambda decomposition and a
truncated logarithmic term, but no declarations currently construct a total
`Kˣ` decomposition or such a total logarithmic coordinate. Likewise,
`KummerLogTrace.lean` contains basis-representation and matrix data; it does
not yet provide the normalized local field trace
`Tr_(K_lambda / Q_59)`, its integrality theorem, and reduction to `ZMod 59`.

What it does not currently assemble is:

- a total, lossless local normal form on all `Kˣ`;
- a norm-coherent Iwasawa tower lift and kappa derivative;
- total additive `L` and `R` coordinates retaining valuation and 59-torsion;
- the correctly normalized local trace, integrality, and mod-59 reduction;
- the trace-product theorem for the Hilbert symbol; or
- the theorem comparing that symbol with this repository's `wild.reading`.

This is the main theory problem.

## 5. Gap B — prove the strict-to-relaxed action is natural

The landing field is no longer mysterious. The clean current adapter reduces
it to one ambient intertwining theorem:

```lean
structure EmptySupportActionCompatibility rho rhoQ : Prop where
  inclusion_intertwines : ∀ delta x,
    rhoQ delta (emptySupportInclusionPadic x) =
      emptySupportInclusionPadic (rho delta x)
```

See
[`EmptySupportReflectedInclusion827.lean`](Fermat/FiftyNine/Conservation/EmptySupportReflectedInclusion827.lean#L69-L118).

Once this is supplied, Lean already proves:

- landing in every character eigenspace;
- the reflected landing used at 59/827;
- the integral-group-algebra-linear strict-to-relaxed inclusion;
- injectivity; and
- equality of strict and included Kummer classes.

The obstruction is again provenance. `rho` and `rhoQ` are arbitrary
representations passed as parameters. `QRelaxedSelmerDeltaRepresentation827`
is merely an abbreviation for a representation on the supported Selmer
carrier; its type does not state that it came from the same Galois action as
`rho`. Arbitrary representations need not agree along the inclusion.

Strictly speaking, the core needs only the weaker character-specific
landing

```text
inclusion(E_(omega * chi⁻¹)(rho)) ⊆ E_(omega * chi⁻¹)(rhoQ).
```

The ambient compatibility above is a stronger and cleaner sufficient
condition chosen by the adapter. A theory argument may supply the weaker
landing directly if that is genuinely cheaper, although canonical actions
should make the stronger naturality statement routine.

The mathematical repair should therefore be one of:

1. construct the canonical Galois representation on the empty-support
   Selmer group and the canonical representation on the
   `placesOver827 K`-supported Selmer group, then prove naturality of the
   support inclusion; or
2. attach a common arithmetic-action realization to the supplied
   representations and derive the intertwining theorem from it.

For the canonical route, the likely mathematical content is:

- the set of places over 827 is stable under the cyclotomic Galois action;
- the action on Kummer classes preserves the relevant local valuation
  conditions; and
- forgetting the stricter local condition commutes with that action.

This construction may also help the separately open
`QLocalizationEquivariance827` seam, because both gaps currently arise from
the q-relaxed action being supplied abstractly rather than constructed from
field automorphisms.

## 6. Exact deliverables requested from the theory goblin

The most useful response is not “use Iwasawa's formula.” We need the
following theorem-sized data.

### Package A — local formula and comparison

Please specify:

1. the local field/completion and the distinguished lambda place;
2. the coefficient ring or algebra `A`;
3. the total left coordinate `L`, including the norm-coherent lift and
   kappa derivative;
4. the total right coordinate `R`, including exactly how valuation,
   Teichmueller data, and 59-torsion are retained;
5. the normalized local trace, its integrality statement, the chosen
   identification of `μ₅₉` with an additive exponent in `ZMod 59`, and the
   resulting reduction map `T : A → ZMod 59`;
6. proofs that `L`, `R`, and `T` are additive in the required sense;
7. at minimum, the formula theorem identifying `T(L(a)R(b))` with the
   additive exponent of the 59-Hilbert symbol on the representatives of
   every old-carrier pair (a theorem on all `Kˣ × Kˣ` is stronger than
   required);
8. independently, the theorem identifying that Hilbert-symbol exponent with
   `wild.reading` on every old-carrier pair; and
9. any independence-of-lift or independence-of-representative theorem used
   before the formal Kummer descent.

A Lean-shaped answer could ultimately produce:

```lean
def iwasawaArithmetic59 : ArithmeticSpecification 59 K A := ...
def iwasawaCoordinates59 : TotalAugmentedCoordinates 59 K A := ...

theorem iwasawaCoordinates59_realizes :
  Realizes iwasawaCoordinates59 iwasawaArithmetic59 := ...

theorem iwasawa59_compared_on_old :
  IsComparedOn iwasawaArithmetic59
    oldPrimalRepresentative
    includedOldReflectedRepresentative
    (fun x y => wild.reading x y) := ...
```

Names are negotiable; the mathematical content is not.

### Package B — canonical actions

Please specify or prove:

```lean
def canonicalStrictSelmerAction59 : ... := ...
def canonicalQRelaxedSelmerAction827 : ... := ...

theorem canonical_emptySupportActionCompatibility827 :
  EmptySupportActionCompatibility827
    canonicalStrictSelmerAction59
    canonicalQRelaxedSelmerAction827 := ...
```

If the intended `rho` and `rhoQ` already exist elsewhere under different
names, identify them and state the comparison theorem connecting them to
these carriers.

## 7. Questions which would materially unblock Lean

1. What is the exact Iwasawa formula for arbitrary first input and arbitrary
   second input modulo 59th powers? If the classical theorem assumes the
   second input is principal, what is the exact root-of-unity/uniformizer
   extension?
2. Does the Selmer valuation-divisibility condition give a canonical-enough
   reduction to `zeta^j * principalUnit` modulo 59th powers?
3. What coefficient algebra `A` packages all required cross-terms as one
   trace product without choosing a public splitting of `Kˣ`?
4. What norm-coherent lift is used, what is the kappa derivative, and why is
   its value independent of the lift?
5. Which normalization fixes the sign and root-of-unity convention for the
   comparison with the 59-Hilbert symbol?
6. Is the repository's intended `wild.reading` literally that Hilbert symbol,
   or must we construct a new canonical `WildLocalInterface` and thread it
   through the conservation route?
7. Are `rho` and `rhoQ` intended to be canonical actions induced from the
   same Galois action? If so, what exact field-automorphism construction
   should Lean use?

## 8. Answers which do not close the gap

Please do not return any of the following as the proposed solution:

- values on only `(zeta,u)`, `(pi,u)`, or the two campaign samples;
- a formula defined by setting it equal to `wild.reading`;
- a claim that bilinearity and the adjoint law uniquely determine the
  reading;
- a projection-after-inclusion argument which loses injectivity or the
  Kummer-class identity;
- a section, complement, or product splitting of the strict and relaxed
  carriers;
- a principal-unit logarithm extended by zero on valuation or torsion;
- a weakened bilinearity/equivariance law;
- reciprocity, unconditional relation (7a), or erasure of `ker G`; or
- full tier-(d) Vostokov--Brueckner machinery while tier (c) remains
  unrefuted.

## 9. Current proof-flow diagram

```text
Package A:
  total arithmetic coordinates + Realizes + independent comparison
                             │
                             ▼
                  CalibratedReductionAt59
                             │
                             ├── defined representative pairing
                             ├── bilinearity
                             ├── 59th-power silence
                             ├── Kummer descent
                             └── old quotient calibration

Package B:
  canonical strict/q-relaxed actions + inclusion naturality
                             │
                             ▼
          EmptySupportActionCompatibility827
                             │
                             ├── reflected eigenspace landing
                             ├── canonical inclusion
                             ├── injectivity
                             └── Kummer-class identity

Package A + Package B
          │
          ▼
ReflectedWildKummerCoreAt59
          │  (already compiled)
          ▼
ReflectedWildLocalizationAt59
          │
          ▼
later independent seams: lawfulness, gauge seating,
ker Lambda <= ker G, reciprocity, normalized-fiber member
```

## 10. Historical verification snapshot and relevant commits

This is the verification snapshot of the superseded tier-(c) route.  Its
target list and job count predate `KummerCupSpanReadout`,
`LocalCompletion59`, and `KummerCupSpanLocalization59`; they must not be read
as current guard coverage for those later modules.

The following standalone targets are green on Lean 4.31:

```text
Fermat.Conservation.IwasawaTracePairing
Fermat.FiftyNine.Conservation.VostokovShapeAudit59
Fermat.FiftyNine.Conservation.IwasawaLocalization59
Fermat.FiftyNine.Conservation.Verification
```

The aggregate verification cone has 8,657 jobs. Every new theorem has
`#check` and `#guard_depends_on` coverage; every new namespace passes the
standard-axiom and no-product-equivalence audits. There are no new
postulates, unfinished proofs, fabricated pairing values, or tier-(d)
definitions.

Relevant commits, in dependency order:

```text
3dec330  Record Vostokov core predictions
c28f437  Record Vostokov C1 shape finding
86a4bbd  Record universal Vostokov core mismatch
cc5ed25  Add term-level Vostokov shape audit
8f91b78  Record the tier-c total-coordinate boundary
78cb2e3  Add the tier-c trace-product constructor
29fdbe9  Bridge tier-c coordinates to the 59 localization core
bd3a92f  Reconcile the tier-c Vostokov frontier
```

## Historical bottom line (superseded)

The present gap is not “formalize all of Vostokov.” It is narrower:

> Construct the actual total Iwasawa/Hilbert pairing with its normalization
> and prove its provenance, and construct the canonical strict/relaxed
> Galois actions with natural support inclusion.

Once those two packages are supplied, the Lean route from them to the full
wild localization is already written and checked.

## Current bottom line

The canonical strict/827-supported cyclotomic actions and their support
inclusion are now constructed.  The local work queue is instead:

> compare the continuous local Kummer cup with the retained discrete cup
> span, construct and normalize the continuous local invariant and
> cup--Hilbert-symbol comparison, factor that reading through
> `LambdaKummerCupSpanReadout59`, and independently calibrate it against the
> pre-existing old wild reading.

Poitou--Tate production of the required global reflected lift remains a
separate seam; neither local duality nor the cup-span adapter manufactures
that class.
