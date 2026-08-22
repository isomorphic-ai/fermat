# The regularized Kummer splice

`Fermat/Descent/KummerIso/` reconstructs the completed fixed-irregular proofs
through one explicit repair of Kummer's unit argument. It is a
fixed-exponent method:

```lean
Fermat.KummerIso.FixedExponent.holdsAt_of_certificate
  : FixedIrregularCertificate p N → Fermat.HoldsAt p
```

Each chosen prime still supplies finite, kernel-checked arithmetic. The
parameter `N` is arbitrary; the theorem is not a proof of FLT for every
prime simultaneously.

The directory also contains a prime-parametric historical assembly. That
route is deliberately conditional on `MorishimaConjectureAt p` and still has
separate temporary equation-(7d) and canonical derivative-source seams. It
must not be read as an unconditional all-prime theorem.

## Why there are two repairs

Kummer's regular-prime proof uses regularity at two different mathematical
objects.

1. An ideal `I` has `I ^ p` principal, and regularity is used to conclude
   that `I` itself is principal.
2. A particular unit ratio `u = ε₁ / ε₂` must be shown to be a `p`-th
   power before the descent can continue.

The Bernoulli correction acts only on the second object. It does not make
an irregular class group regular and cannot principalize arbitrary ideal
classes.

The first repair is therefore the historical primary
Takagi--Furtwängler route. For the special Fermat-produced ideal roots, a
nonprincipal Kummer-primary root would produce `p`-torsion in the real class
group. The checked input `p ∤ h⁺` rules that out. The second repair is the
diagonal correction described below.

## The actual correction

Let `aᵢ` be the exponents in a primitive relation among the relevant
cyclotomic units, and let `Bᵢ` be Vandiver's lifted Bernoulli numerators.
The logarithmic-derivative calculation supplies

```text
p³ ∣ aᵢ Bᵢ.
```

For every source coordinate define

```text
cᵢ = (Bᵢ / p²) mod p    when p² ∣ Bᵢ,
     1                   otherwise.
```

The no-cube-obstruction condition `p³ ∤ Bᵢ` makes every lifted entry
`cᵢ` nonzero. For a prime-parametric proof, its assertion at every relevant
coordinate is exactly `MorishimaConjectureAt p`. This is Morishima's
conjecture, not Vandiver's conjecture `p ∤ h⁺`, and it is not a consequence
of FLT. Ordinary coordinates receive the identity entry. Thus

```text
Cₚ = diag(cᵢ)
```

is a linear automorphism over `ZMod p`. After cancelling the certified
`p²` on a lifted row, the derivative congruence says that the corrected
coordinate is zero. The ordinary scalar argument gives the same equation
on every remaining row:

```text
Cₚ · (aᵢ mod p) = 0.
```

Applying `Cₚ⁻¹` proves `p ∣ aᵢ` for every exponent. The existing product
and Bézout lemmas then extract a `p`-th root of the exact unit ratio.

The mixed construction is formalized for an abstract finite source type.
`BernoulliCorrection` builds the genuine `Bᵢ / p²` entry directly from the
integer divisibility witness on each lifted coordinate and uses `1`
elsewhere. The generic route takes `MorishimaConjectureAt p` explicitly.
The fixed-exponent channel certificates instead prove the required statement
`p³ ∤ Bᵢ` by kernel-checked finite computation; they do not identify their
separate Faulhaber `weight` with this quotient.

Independently, the reusable `DiagonalGauge p (Fin N)` and
`fixedChannelAutomorphism` work for every `N`, including the empty block,
and package the nonzero finite channel weights as an automorphism. No
equality between that auxiliary weighted gauge and the full-source
`BernoulliCorrection` is assumed.

## Dependency flow

```text
special Fermat ideals ─> primary/Takagi reflection ─> selected ideals principal
             p ∤ h⁺ ────────────────────────────────┘

historical equations (7)--(10) ─> exact ratio ε₁/ε₂ at depth 2p
canonical derivative source ───> primitive-relation cube congruences
Morishima at p / checked channels ─> p³ ∤ Bᵢ
                                  │
                                  v
                     actual Bᵢ/p² diagonal automorphism
                                  │
                                  v
                         ε₁/ε₂ is a p-th power
                                  │
                                  v
                    historical descent ─> SecondCaseExcluded

generic Sophie--Germain search + SecondCaseExcluded ─> Fermat.HoldsAt p
```

The modules implement this flow as follows:

- `WeightedSolution.lean` names the weighted equation and its exact unit
  ratio.
- `Principalization.lean` exposes pointwise selected-quotient adapters and
  reuses the checked historical primary/Takagi principalization.
- `Correction.lean` defines the diagonal linear equivalence, the actual
  mixed Bernoulli correction, and the corrected root-extraction theorem.
  It also exposes the separate arbitrary-`N` weighted automorphism without
  claiming an equality between the two gauges.
- `UnitExtraction.lean` moves the deep unit into the real-unit subgroup and
  routes Vandiver's primitive relation through `Correction`.
- `DeepRatio.lean` connects the literal historical ratio to its depth and
  to the correction-based unit theorem.
- `Induction.lean` is the conditional regular-style adapter: from
  `RegularUnitRatioDeep`, it extracts the root of `ε₁ / ε₂`, absorbs that
  root into `x`, and produces the unweighted equation for the next
  induction step.
- `SecondCase.lean` performs the complete historical second-case descent.
- `BernoulliValidationBound.lean` names `MorishimaConjectureAt p`, derives
  the former valuation bound from that explicit hypothesis, and keeps the
  unrelated canonical derivative source under its own temporary axiom.
- `ValidatedSecondCase.lean` threads the explicit Morishima premise through
  the prime-parametric historical Case-II assembly.
- `FixedExponent.lean` invokes the proof-producing Sophie--Germain search
  for Case I.
- `Regressions.lean` checks the resulting endpoint at every completed
  fixed irregular exponent in scope.
- `FermatEquationSevenDBruteForce.lean` replaces equation (7d) with a
  finite circular-unit residue certificate and provides a canonical
  cyclotomic-field Case-II closure helper.
- `ResidueRegressions.lean` uses that helper to close all nine completed
  campaign exponents with their explicit finite, checked Sophie--Germain
  certificates and no project axioms.

The factor allocation and descent algebra are reused from the pinned
`flt-regular` dependency. The historical primary, reflection, real-unit,
Bernoulli, and logarithmic-derivative layers are reused from
`Fermat/Descent/Irregular/` and `Fermat/Descent/GenericIrregular/`; this directory does not
maintain a shadow copy of them.

## What is complete, and what remains distinct

The certificate-backed fixed-exponent historical path is complete.
`WeightedReductionData.highCongruence` proves depth
`(1 - ζ) ^ (2 * p)` for its literal ratio `ε₁ / ε₂`. `UnitExtraction`
applies the correction to that exact ratio, and the historical descent
consumes the resulting root. The separate prime-parametric assembly remains
conditional on Morishima and its two visibly named temporary seams.

The direct regular-style witness is a separate object. For a
`KummerIso.WeightedSolution`, the repository proves that its literal ratio
is semiprimary modulo `(p)`, but it does not currently prove either:

- `KummerIso.DeepRatio.RegularUnitRatioDeep hζ w`; or
- an identification of that ratio with the independently constructed
  historical ratio.

Given `RegularUnitRatioDeep`, the theorem
`KummerIso.DeepRatio.regularUnitRatio_isPower` closes every downstream step
through the same correction. In particular,
`KummerIso.Induction.exists_unweightedSolution_of_regularUnitRatioDeep`
absorbs the extracted root into `x` and returns the corresponding
unweighted equation. This is a conditional adapter, not a proof of the
depth premise or a new end-to-end FLT endpoint. The premise is intentionally
visible and is not hidden in a certificate.

## End-to-end regressions

Nine existing fixed-second-case certificates are reassembled through the
normalized correction:

| Exponent | Irregular channels | Public regression theorem |
| ---: | ---: | --- |
| `37` | `1` | `Fermat.KummerIso.Regressions.holdsAt_thirtySeven` |
| `59` | `1` | `Fermat.KummerIso.Regressions.holdsAt_fiftyNine` |
| `67` | `1` | `Fermat.KummerIso.Regressions.holdsAt_sixtySeven` |
| `157` | `2` | `Fermat.KummerIso.Regressions.holdsAt_oneHundredFiftySeven` |
| `491` | `3` | `Fermat.KummerIso.Regressions.holdsAt_fourHundredNinetyOne` |
| `587` | `2` | `Fermat.KummerIso.Regressions.holdsAt_fiveHundredEightySeven` |
| `607` | `1` | `Fermat.KummerIso.Regressions.holdsAt_sixHundredSeven` |
| `691` | `2` | `Fermat.KummerIso.Regressions.holdsAt_sixHundredNinetyOne` |
| `1381` | `1` | `Fermat.KummerIso.Regressions.holdsAt_oneThousandThreeHundredEightyOne` |

These regressions do not call the older `holdsAt_*_generic` endpoints.
They reuse the same raw certificate types, reconstruct Case II through the
correction, and then rejoin the first and second cases through the generic
search.  The standalone concrete Sophie--Germain certificates retained in
the exponent directories are not inputs to these regressions. Their axiom
audit therefore includes the explicit
`SophieGermainAuxiliarySearchTermination` seam.

The parallel theorems in `Fermat.KummerIso.ResidueRegressions` use the
same exponent names and additionally replay the finite circular-unit
residue matrices. For example:

```lean
Fermat.KummerIso.ResidueRegressions.holdsAt_thirtySeven
Fermat.KummerIso.ResidueRegressions.holdsAt_fiftyNine
Fermat.KummerIso.ResidueRegressions.holdsAt_oneThousandThreeHundredEightyOne
```

All nine residue regressions bypass `FermatEquationSevenD` and reuse their
fixed unit systems and axis-8 channels instead of assuming Morishima or the
canonical derivative source. They also reuse the explicit finite, checked
Sophie--Germain certificates in the corresponding `FirstCase.lean` modules
instead of the generic search. Their axiom audits therefore contain only
Lean's standard axioms, with no
`SophieGermainAuxiliarySearchTermination`.

After `import Fermat`, the `KummerIso.Regressions` endpoints are also
available through concise `_kummerIso` aliases. The residue regressions
deliberately keep their qualified names so the finite-matrix route and its
axiom provenance remain visible.
