# Dirichlet's direct `n = 14` proof

Primary source: G. Lejeune Dirichlet, “Démonstration du théorème de Fermat
pour le cas des 14ièmes puissances,” *Journal für die reine und angewandte
Mathematik* 9 (1832), 390–393. The supplied scan is
`../fermat-data/fermats-last-theorem-n-equals-proofs.zip`, entry
`downloads/n14/Dirichlet_1832_n14_Zenodo_article.pdf`.

This route is intentionally independent of the short implication from the
`n = 7` theorem.

## Proof ledger

Dirichlet begins with a primitive solution

```text
t^14 = u^14 + v^14.                                      (1)
```

Exactly one variable is even; after swapping `u` and `v` when necessary, any
variable divisible by `7` is `v`. Transposition and factorization give

```text
t^14 - u^14 = v^14,                                      (2)

(t²-u²)[(t²-u²)^6 + 7t²u²(t⁴-t²u²+u⁴)²] = v^14.         (3)
```

Writing

```text
φ = t²-u²,
ψ = tu(t⁴-t²u²+u⁴),
```

equation (3) becomes

```text
φ(φ^6 + 7ψ²) = v^14.                                     (4)
```

The paper proves `φ` and `ψ` coprime. If `7 ∤ v`, the two factors in (4) are
coprime fourteenth powers. Dirichlet's earlier representation theorem for
`x² + 7y²` then gives, after accounting for the units,

```text
φ³ + ψ√-7 = ε(g + h√-7)^14,       ε ∈ {+1,-1}.
```

The coefficient of `√-7` on the right is divisible by `7`, whereas
`ψ = tu((t²-u²)²+t²u²)` is not. This eliminates the first case.

For `7 ∣ v`, write `v = 7w` and enlarge the target to

```text
t^14 - u^14 = 2^m 7^(1+n) w^14,                          (5)
```

where `m,n ≥ 0`, `t,u,w` are nonzero, and `t,u` remain coprime. Equation (4)
forces `φ = 7χ` and

```text
7²χ(ψ² + 7(7²χ³)²) = 2^m 7^(1+n) w^14.
```

Coprimality makes the quadratic-form factor a fourteenth power. The same
representation theorem supplies a sign `ε` and coprime `r,s`, of opposite parity and with
`7 ∤ r`, such that

```text
ψ + 7²χ³√-7 = ε(r + s√-7)^14.
```

Define

```text
R = (r²+7s²)(r⁴-2·7²r²s²+7²s⁴).
```

Comparing imaginary parts and refactoring yields

```text
7⁶χ³ = ε·2·7⁵rs (R+7(4rs)³)(R-7(4rs)³).
```

The formal proof carries `ε` explicitly and performs factor allocation on
absolute values.

The three factors on the right are pairwise coprime. Consequently there are
new integers `t',u',v'` with

```text
|R+7(4rs)³| = t'^14,
|R-7(4rs)³| = u'^14,
4|rs| = 2^(3m+1) 7^(1+n') v'^14.
```

The first two signed factors cannot have opposite signs: their absolute values
are odd fourteenth powers, hence both are `1 mod 8`, while their difference is
divisible by `8`. After orienting them, subtraction and substitution produce a
new instance of (5):

```text
t'^14-u'^14 = 2^(9m+4) 7^(3n'+4) w'^14,
```

with coprime `t',u'`. For the rigorous descent bound, put `a = r² + 7s²`.
Norm comparison gives `a < |t|`. Moreover `4|rs| ≤ a` and `|R| ≤ 7a³`, so
`max(t'^14,u'^14) ≤ 14a³ < a^14`; hence `|t'|,|u'| < a < |t|`. Infinite
descent finishes.

## Lean status

The checked proof is split into the following modules:

- `Fermat/Quadratic/NegSeven.lean` constructs
  `ℤ[(1+√-7)/2]`, proves its norm-Euclidean algorithm (with rounding error
  at most `11/16`), and classifies its units as `±1`;
- `Fermat/Fourteen/PowerExtraction.lean` proves the specialized signed
  fourteenth-power representation and returns the extracted root to
  `ℤ[√-7]` by a modulo-`2` argument;
- `Fermat/Fourteen/FirstCase.lean` completes the case `7 ∤ tuv`;
- `Fermat/Fourteen/DescentSetup.lean` performs the first factor allocation in
  the generalized equation;
- `Fermat/Fourteen/DescentArithmetic.lean` proves the three-factor
  coprimality, mod-`8` orientation, and strict size estimates;
- `Fermat/Fourteen/DescentConstruction.lean` constructs the smaller solution,
  including the exceptional `n = 0` valuation, and proves
  `Fermat.Fourteen.Dirichlet.holdsAt_fourteen_dirichlet`.

The theorem's dependency chain does not contain the `n = 7` result.

## Unit-sign repair

The paper prints the two representation formulas without `ε`. That unsigned
statement is false for even powers. For example, in `ℤ[√-7]`,

```text
(4-√-7)^14 = -1094457159 - 1218605752√-7.
```

Thus `P = 1094457159` and `Q = 1218605752` are coprime, of opposite parity,
and `7 ∤ P`, with `P²+7Q² = 23^14`, but `P+Q√-7` is the negative of the
displayed fourteenth power. Dirichlet imported the representation argument
from an odd-power setting, where `-1` can be absorbed into the base; that move
is unavailable for exponent `14`.

For the first case, the omission is harmless because either sign still makes
the `√-7` coefficient divisible by `7`. For the descent case, Lean's version
retains the unit and allocates it among the signed real factors. No global UFD
claim about `ℤ[√-7]` is used: it is a nonmaximal order. Power extraction is
instead performed in the Euclidean maximal order `ℤ[(1+√-7)/2]`; the parity
hypothesis then forces the root back into `ℤ[√-7]`.
