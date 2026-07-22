# Dirichlet's completed `n = 5` proof

Primary source: G. Lejeune Dirichlet, “Mémoire sur l'impossibilité de
quelques équations indéterminées du cinquième degré,” *Journal für die reine
und angewandte Mathematik* 3 (1828), 354–375.  The addition begins on
Crelle p. 368.  The supplied scan is
`../fermat-data/fermats-last-theorem-n-equals-proofs.zip`, entry
`downloads/n5/Dirichlet_1828_n5_Crelle_GDZ.pdf`; the collected-works OCR used
to locate passages is entry
`downloads/n5/Dirichlet_1889_Werke_Band1_IA_ocr.txt`.

Equations below are transcriptions, not quotations of the surrounding prose.
Page numbers and the Greek equation labels are those printed in the Crelle
article.  “Source” records Dirichlet's step.  “Lean repair” identifies the
modern justification used where the formal proof does not take the source's
quadratic representation assertions on trust.

## Entry equation and the parity split

Dirichlet's congruence calculation modulo `25` occupies Crelle pp. 366–368.
Applied to a primitive Fermat equation, it forces one of the three entries to
be divisible by `5`; that entry can be isolated and written as `5z`.  The
addition closes the remaining case by proving the impossibility of

```text
x^5 ± y^5 = 5^5 z^5,                 gcd(x,y)=1.       (E)
```

This specialization is stated explicitly in the final paragraph of the proof
on p. 375.  The source uses the sign `±`; Lean keeps a plus sign and permits
signed integer bases.

The parity split is made in Theorem VIII on p. 372:

| parity of `x,y` in (E) | historical route | Lean core |
| --- | --- | --- |
| both odd | `z` is even, so (E) becomes the `m=5,n=5,A=1` case of Theorem V | `EvenCore` |
| opposite parity | the new argument in the addition, Theorem VIII | `OddCore` |

The Lean names refer to the later coordinates, not to the parity of the
original pair `x,y`.

For opposite parity, p. 372 sets

```text
p = x ± y,       q = x ∓ y,
```

so `p,q` are odd, and obtains

```text
p(p^4 + 10p²q² + 5q^4) = 2^4 5^5 z^5.
```

The factor `p` is divisible by `5`; putting `p=5r` gives

```text
r H(q,r) = 2^4 5^3 z^5,

H(q,r) = q^4 + 50q²r² + 125r^4.                    (C)
```

Here `q,r` are both odd.  In the both-odd branch, Theorem V first writes
`x±y=2p`, `x∓y=2q` (p. 363).  Since `z=2z₀`, its parameters are
`m=n=5`; after `p=5r` the same calculation gives (C), now with `q` odd and
`r` even.  Thus the two source branches really do enter the same core
equation with different coordinate parity.  This is the content of
`Fermat/Five/Coordinates.lean` and `Fermat/Five/InitialArithmetic.lean`.

## The quartic used in both descents

The recurring factor is

```text
F(t,s) = t^4 + 10t²s² + 5s^4.                     (F)
```

It first appears in the coefficient equations of Theorem V on p. 364 and in
the product labelled `(β)` at the foot of that page.  It reappears in the
addition's coordinate equations on p. 373 and in `(δ)` on p. 374.  The two
norm identities behind the repetitions are

```text
(t²+5s²)² - 5(2s²)² = F(t,s),

((t²+5s²)/2)² - 5(s²)² = F(t,s)/4.
```

The first is used when `t` is odd and `s` even (Crelle p. 365); the second
when `t,s` are both odd (p. 374).  In Lean, `F` and these two descent
normalizations are in `Fermat/Five/Descent.lean`.

## The old branch: both original entries odd

This is the route already available through Theorem V before the addition.
The source proves the more general impossibility of the equation labelled
`(α)` on p. 362,

```text
x^5 ± y^5 = 2^m 5^n A z^5,                           (α)
```

under its stated restrictions on `m,n,A`.  Pages 363–364 choose positive
integers `μ,ν` such that

```text
m+μ-1 ≡ 0 (mod 5),       n+ν-2 ≡ 0 (mod 5).
```

For the Fermat specialization `m=n=5,A=1`, take `μ=1`, `ν=2`.  The source
then defines on p. 364

```text
g = 2μ-1 = 1,       h = 2ν = 4.
```

The exact initial arithmetic in Lean is

```text
2·25r = a^5,       H(q,r) = b^5,

P = q²+25r²,    Q = 10r²,
P²-5Q² = b^5,

2r² = s F(t,s).
```

Consequently the first state is

```text
2^1 5^4 s F(t,s) = w^5,
```

with `t` odd, `s` even and divisible by `5`, and `5∤t`.  This is precisely
`EvenCore.exists_evenState`, which returns `EvenState 1 4 t s w` in
`Fermat/Five/Initial.lean`.

For the repeating step, the source retains an auxiliary coefficient and
considers

```text
2^g 5^h C s F(t,s)                                      (β)
```

as a fifth power (p. 364).  The factor allocation and Theorem IV give on
p. 365

```text
2s² = 5s' F(t',s').
```

The new coordinates have the same parity and coprimality properties, `5∣s'`,
and p. 365 proves `s'<s`.  Squaring the complementary fifth-power factor
produces `(β')` with

```text
g' = 2g-1,       h' = 2h+1,       C' = C².             (R_even)
```

For the Fermat specialization `C` starts at `1`, and `C'=C²` keeps it there;
Lean therefore omits `C` from `EvenState`.

These formulas and the strict decrease are formalized by
`EvenState.nextOfCoordinates`, `EvenCoordinates.smaller`, and
`EvenState.descends`.  Page 366 turns the indefinitely decreasing positive
sequence `s,s',s'',...` into the contradiction.

## The addition branch: opposite parity of the original entries

The denominator in this branch is part of the source, not a modern
renormalization.  On p. 369 Dirichlet states the odd-odd representation in
the form

```text
P + Q√5 = (φ + ψ√5)^5 / 16.                       (D16)
```

Pages 369–371 derive it by converting `P²-5Q²=4L` to a Pell-type
representation, reducing the exponent of `9±4√5`, and absorbing the
remaining factor.  The expanded coordinates on p. 371 are

```text
P = φ(φ^4 + 50φ²ψ² + 125ψ^4) / 16,
Q = 5ψ(φ^4 + 10φ²ψ² + 5ψ^4) / 16.
```

Theorem VII, begun on p. 371 and completed on p. 372, records the hypotheses:
`P,Q` are coprime and odd, `5∣Q`, `5∤P`, and `P²-5Q²` is four times a
fifth power.  In Lean these formulas are
`half_fifth_coordinate_formulas` and `exists_odd_half_coordinates` in
`Fermat/Five/PowerExtraction.lean`.

For (C) with `q,r` odd, the source factor allocation on pp. 373–374, at
`n=5,A=1`, is exactly

```text
25r = a^5,       H(q,r) = 16b^5,

P = (q²+25r²)/2,    Q = 5r²,
P²-5Q² = 4b^5,

16r² = s F(t,s).
```

On p. 373 the auxiliary exponent `ν` is chosen with
`n+ν-2 ≡ 0 (mod 5)`.  Thus `n=5` gives `ν=2`; p. 374 sets `h=2ν`,
so the historical initial exponent is

```text
h = 4,       5^4 s F(t,s) = 16 w^5.
```

This is `OddCore.exists_oddState`, returning `OddState 4 t s w` in
`Fermat/Five/Initial.lean`.

For the repeating step, the source again retains the auxiliary coefficient:

```text
5^h C s F(t,s),                                          (δ)
```

equal to `2^4` times a fifth power (p. 374).  Theorem VII applied to
`F(t,s)/4` gives

```text
16s² = 5s' F(t',s').
```

Again `5∣s'` and `s'<s`.  Squaring the other fifth-power factor gives the
equation `(δ')` printed at the top of p. 375, with

```text
h' = 2h+1,       C' = C².                              (R_odd)
```

Here too `C=1` throughout the Fermat specialization, so it is absent from
Lean's `OddState`.

Lean formalizes these exact statements as `OddState.nextOfCoordinates`,
`OddCoordinates.smaller`, and `OddState.descends`.  The comparison of `(δ')`
with `(δ)` and the smaller positive `s'` is the infinite descent used on
p. 375.

## Modern rigorous repairs

### Maximal order and UFD extraction

**Source step.**  Theorem IV on pp. 361–362 supplies
`P+Q√5=(φ+ψ√5)^5` in the opposite-parity case.  Theorem VII on
pp. 371–372 supplies the half-integral formula (D16).  Dirichlet reaches
Theorem IV through preceding representation lemmas and induction on the
prime divisors of the norm (see especially pp. 359–361); he does not state
that `ℤ[√5]` is a UFD.

**Lean repair.**  A global UFD argument in `ℤ[√5]` would be invalid:
that order is nonmaximal and is not integrally closed.  The formal proof
instead works in the maximal order

```text
O₅ = ℤ[(1+√5)/2].
```

`Fermat/Quadratic/Golden.lean` proves that the absolute norm is Euclidean,
so `O₅` has the UFD infrastructure needed for coprime-factor extraction.
`Fermat/Five/PowerExtraction.lean` proves that the two conjugate factors are
coprime in `O₅`, extracts a fifth power up to a unit, and removes the unit
ambiguity.  When `P,Q` have opposite parity, a modulo-`2` argument returns
the root to `ℤ[√5]`.  When `P,Q` are both odd, the algebraic integer is
`(P+Q√5)/2`; clearing its fifth-power denominator gives exactly the source's
factor `16`.

This is a modern justification of the representation step, not an
attribution of a false UFD claim to Dirichlet.

### Pell units

**Source step.**  On p. 361 Dirichlet uses

```text
t+u√5 = (9±4√5)^p
```

for the positive solutions of `t²-5u²=1`, referring in a footnote to
Euler's *Additions à l'Algèbre*, article 75.  In the addition, p. 370 reduces
the exponent modulo `5`; pp. 370–371 isolate the admissible residue and turn
the resulting factor into (D16).

**Lean repair.**  `Fermat/Quadratic/GoldenUnits.lean` proves the required
classification.  It identifies `9+4√5` as the fundamental norm-one Pell
solution and proves that every unit of `O₅` is

```text
±ϕ^k,       ϕ=(1+√5)/2.
```

The sign is a fifth power because the exponent is odd.  The unit exponent is
reduced modulo `5`, and the finite coordinate congruence
`phi_remainder_eq_zero` in `Fermat/Five/PowerExtraction.lean` eliminates the
remaining residue.  This supplies, within Lean, the classification and unit
absorption used informally in the source calculations.

## Lean dependency ledger

The checked proof is split into the following modules:

- `Fermat/Five/Modular.lean` proves the modulo-`25` entry calculation;
- `Fermat/Five/Equation.lean` performs the signed permutation that puts the
  entry divisible by `5` on the right of (E);
- `Fermat/Five/Reduction.lean` reduces primitive FLT data to impossibility of
  `FifthEquation`;
- `Fermat/Five/PowerSplitting.lean` supplies the signed odd-power allocation
  for coprime integer factors;
- `Fermat/Five/Coordinates.lean` constructs `OddCore` and `EvenCore`;
- `Fermat/Five/InitialArithmetic.lean` proves the coprime allocations from
  (C), including the exact factors `16`, `25`, and `2·25`;
- `Fermat/Quadratic/Golden.lean` and
  `Fermat/Quadratic/GoldenUnits.lean` provide the Euclidean maximal order and
  its Pell-based unit classification;
- `Fermat/Five/PowerExtraction.lean` proves the two quadratic representation
  interfaces and their coordinate formulas;
- `Fermat/Five/Initial.lean` constructs the initial states at `h=4` and
  `(g,h)=(1,4)`;
- `Fermat/Five/Descent.lean` proves both exact recurrences and both strict
  descents;
- `Fermat/Five/Dirichlet.lean` joins the branches and proves
  `Fermat.Five.Dirichlet.holdsAt_five_dirichlet`.

Thus the formal dependency chain follows the completed memoir and addition;
it does not obtain exponent `5` from a more general FLT theorem.
