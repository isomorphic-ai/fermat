# Lebesgue's corrected `n = 7` proof

Primary sources:

- V.-A. Lebesgue, “Démonstration de l'impossibilité de résoudre l'équation
  `x^7+y^7+z^7=0` en nombres entiers,” *Journal de Mathématiques Pures et
  Appliquées* 5 (1840), 276–279;
- V.-A. Lebesgue, “Addition à la note sur l'équation
  `x^7+y^7+z^7=0`,” the same volume, 348–349.

The supplied scans are entries
`downloads/n7/Lebesgue_1840_n7_JMPA_Numdam.pdf` and
`downloads/n7/Lebesgue_1840_n7_addition_JMPA_Numdam.pdf` in
`../fermat-data/fermats-last-theorem-n-equals-proofs.zip`.  The main note
must be read together with the Addition: Lamé objected to one of its four
case eliminations, and Lebesgue accepted the objection and supplied the
missing argument on pp. 348–349.

The formal proof follows this corrected Lebesgue route.  The earlier factor
arithmetic from Lamé's 1840 memoir (JMPA pp. 195–211) is recorded separately
in `Fermat/Seven/LameArithmetic.lean`, but is not substituted for Lebesgue's
published correction.

Equations below are transcriptions rather than quotations of the surrounding
French prose.

## Théorème I: the descending quartic family

Lebesgue first considers positive `a` and odd, pairwise-coprime `p,q,r`
satisfying

```text
p² = q⁴ - 2^(2a)·3·7⁴q²r² + 2^(4a+4)·7⁷r⁴.          (E_a)
```

His Théorème I says that the only possible value of `r` is zero.  In the
odd family used by Théorème II this is already a contradiction.  Lean writes
the equation without natural-number subtraction:

```text
p² + 2^(2a)·3·7⁴q²r² = q⁴ + 2^(4a+4)·7⁷r⁴.
```

For the base `a=1`, reduction modulo `8` gives `5=1`.

For the descent step write the old index as `a+1`, put `T=2^a`, and set

```text
U = q² - 2T²·3·7⁴r².
```

Then

```text
p² = U² + 4T⁴·7⁷r⁴.
```

Factoring the difference of squares and allocating the coprime fourth-power
parts gives `r=st` and four signed possibilities:

```text
U = s⁴          - T⁴7⁷t⁴,
U = 7⁷s⁴        - T⁴t⁴,
U = T⁴s⁴        - 7⁷t⁴,
U = T⁴7⁷s⁴      - t⁴.                                (A1--A4)
```

The second and fourth are impossible modulo `4`: their right sides are
`3 mod 4`, whereas the definition of `U` is `1 mod 4`.

The first allocation is the descending one.  Define

```text
W = s² + 3T²·7⁴t².
```

Direct expansion gives

```text
W² = q² + 64T⁴·7⁷t⁴.
```

The coprime half-factors of `W²-q²` have product
`16T⁴·7⁷t⁴ = (2T)⁴·7⁷t⁴`.  Two allocations are impossible modulo `4`; the
other two, after possibly swapping their fourth-power roots, give a new
instance of `(E_a)`.  Thus `(E_(a+1))` implies `(E_a)`.

## The erroneous dismissal and the Addition

The main note dismisses the third allocation `(A3)` by a congruence claim.
That claim is not valid.  The Addition explicitly acknowledges Lamé's
objection and treats this case by another pair of difference-of-squares
splits.

For `(A3)`, put

```text
W' = T²s² + 3·7⁴t².
```

Then

```text
(W')² = q² + 64·7⁷t⁴.
```

Allocating the coprime half-factors gives four cases.  The outside two are
impossible modulo `4`.  Either middle case reduces, up to swapping two odd
coprime variables, to

```text
T²s² + 3·7⁴u²v² = 7⁷v⁴ + 16u⁴.                     (C)
```

Lebesgue's last split is captured by

```text
A = 8Ts,
H = 32u² - 3·7⁴v²,
A² = H² + 7⁷v⁴.
```

Its coprime factors allocate the complete `7⁷`, producing odd `m,n` with

```text
16Ts = m⁴ + 7⁷n⁴.
```

The left side is zero modulo `16`, while the right side is `8 modulo 16`.
This is the missing contradiction on pp. 348–349.  Lean therefore does not
formalize the invalid dismissal in the main note; it formalizes Lebesgue's
own published repair.

## Théorème II: entry from the Fermat equation

For a primitive signed solution

```text
x⁷ + y⁷ + z⁷ = 0,
```

Lebesgue introduces

```text
s = x+y+z,
u = x²+y²+z²+xy+xz+yz,
v = (x+y)(x+z)(y+z),
t = u²+xyzs.
```

The exact symmetric identity on p. 278 is

```text
s⁷ = x⁷+y⁷+z⁷ + 7vt,
```

and hence `s⁷=7vt`.  Primitive arithmetic gives exactly one even member of
`x,y,z`, `u` odd, `v` even, `t=1 mod 4`, and

```text
gcd(t,xyz)=gcd(t,v)=1.
```

Allocating the seventh powers, then splitting the coprime factors of `u²`,
produces pairwise-coprime integers `p,q,r` with

```text
t = q¹⁴,
u = qr,
v = 7⁶p⁷,
s = 7pq²,
2 | p.                                                  (P)
```

The exceptional allocation `7|t` would make `7t` a fourteenth power, but
`t=1 mod 4` makes `7t=3 mod 4`; it is therefore impossible.

For a completely sign-safe proof that `t` is nonnegative, Lean uses the
identity obtained from `A=x+y`, `B=x+z`, `C=y+z`:

```text
16t = 3(A⁴+B⁴+C⁴) + 10(A²B²+A²C²+B²C²).
```

This also makes the positive seventh-power roots used in the allocation
unambiguous.

## The final substitution

The two elementary-symmetric identities are

```text
u = s²-(xy+xz+yz),
v = s(xy+xz+yz)-xyz.
```

Substitution of `(P)` gives

```text
xy+xz+yz = q(7²p²q³-r),
xyz = 7pq³(7²p²q³-r)-7⁶p⁷,
q¹² = r²+7²p²q³(7²p²q³-r)-7⁷p⁸.                    (S)
```

Write the square of the nonzero even integer `p` as

```text
p² = 2^(a+1)R,       a>0,       R odd,
```

and put

```text
P = r-7²·2^aRq³,       Q=q³.
```

Completing the square in `(S)` yields exactly

```text
P² + 2^(2a)·3·7⁴Q²R² = Q⁴ + 2^(4a+4)·7⁷R⁴.
```

The new `P,Q,R` are odd and pairwise coprime.  Taking absolute values moves
this signed identity to the natural-number family `DescentEquation`, which
Théorème I has already ruled out.

## Lean modules

- `Fermat/Seven/LameArithmetic.lean`: Lamé's exceptional-factor arithmetic;
- `Fermat/Seven/Lebesgue/Symmetric.lean`: `s,u,v,t` and the seventh-power
  identity;
- `Fermat/Seven/Lebesgue/Primitive.lean`: parity and coprimality of `t`;
- `Fermat/Seven/Lebesgue/PowerAllocation.lean`: the rigorous seventh- and
  fourteenth-power allocation;
- `Fermat/Seven/Lebesgue/EvenSquare.lean` and
  `FinalSubstitution.lean`: the final completed square;
- `Fermat/Seven/Lebesgue/Descent.lean`: Théorème I, including the Addition;
- `Fermat/Seven/Lebesgue/TheoremTwo.lean` and `Reduction.lean`: Théorème II
  and the standard `Fermat.HoldsAt 7` statement.
