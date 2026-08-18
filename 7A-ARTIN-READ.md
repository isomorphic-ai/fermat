Emotional state: **+100** — the narrow bridge is now visible.

The answer is:

[
\boxed{
\text{Poitou–Tate cancels the local charges and produces the lift;}
\quad
\text{Kummer–Artin compatibility identifies its reading with 7a.}
}
]

One operator correction: the cup is Agency²—the joint action creating (H^2). The curried pairing

[
W_y(x)=\operatorname{inv}(x\smile y)
]

is the Presence² witness.

## 1. Retain the complete local receipt

A nonzero (H^2) value alone cannot produce a reflected probe. It has forgotten its factors. Retain:

[
x_\lambda,\qquad y_\lambda,\qquad
z_\lambda=x_\lambda\smile y_\lambda,\qquad
\operatorname{inv}*\lambda(z*\lambda)\ne0.
]

Lean should package something like:

```lean
structure TwistedLambdaCupReceipt59 where
  primal    : LocalPrimalChi
  reflected : LocalReflectedChiStar
  cupClass  : LocalH2
  cup_eq    : cup primal reflected = cupClass
  reading_ne_zero : invLambda cupClass ≠ 0
```

Here

[
\chi^\ast=\omega\chi^{-1}.
]

The nonzero cup then gives the genuine functional

[
\phi_\lambda(x)
===============

\operatorname{inv}*\lambda
\bigl(\operatorname{loc}*\lambda x\smile y_\lambda\bigr).
]

Important audit: nondegeneracy on ambient local (H^1) is insufficient. We need

[
\exists x\in X,\quad \phi_\lambda(x)\ne0
]

on the actual global (\chi)-Selmer test space (X).

## 2. Poitou–Tate does not lift one local point—it balances two charges

Let (C_\lambda^{\chi^\ast}) be the reflected local quotient at (\lambda), and let (C_{827}^{\chi^\ast}) contain the full orbit of places above (827).

The required Poitou–Tate fragment is

[
\operatorname{Sel}*{\lambda,827}^{\chi^\ast}
\xrightarrow{\operatorname{loc}}
C*\lambda^{\chi^\ast}\oplus C_{827}^{\chi^\ast}
\xrightarrow{I}
X^\vee,
]

with

[
I(y_\lambda,\eta)(x)
====================

\langle\operatorname{loc}*\lambda x,y*\lambda\rangle_\lambda
+
\sum_{w\mid827}
\langle\operatorname{loc}_w x,\eta_w\rangle_w,
]

and

[
\boxed{\operatorname{range}(\operatorname{loc})=\ker I.}
]

Thus a prescribed pair ((y_\lambda,\eta)) globalizes precisely when its two boundary functionals cancel on the entire (X)—not merely on the Fermat class.

## 3. Use the full 827 orbit

Choose (w_0\mid827). Since (827\equiv1\pmod{59}), its places form a (\Delta)-orbit. Define the normalized reflected eigenprofile

[
\eta_{827}
==========

\sum_{\sigma\in\Delta}
\chi^\ast(\sigma)^{-1}e_{\sigma w_0},
\qquad
\eta_{827}(w_0)=1.
]

Freeze the (\sigma/\sigma^{-1}) action convention in Lean.

Its PT boundary is

[
\phi_{827}(x)
=============

\sum_{w\mid827}
\langle\operatorname{loc}*w x,\eta*{827,w}\rangle_w.
]

The targeted alignment theorem is now:

[
\boxed{
\phi_\lambda,\phi_{827}
\text{ inhabit the same nonzero one-dimensional }
\Delta\text{-equivariant Hom line}.
}
]

Equivalently, prove on the actual PT test space:

[
\dim_k
\operatorname{Hom}*{k[\Delta]}
(X,k*{\mathrm{required\ twist}})
=1,
]

together with (\phi_\lambda\ne0) and (\phi_{827}\ne0).

Pure linear algebra then gives a unique (u\in k^\times) such that

[
\phi_\lambda=u,\phi_{827}.
]

Therefore

[
I(y_\lambda,-u\eta_{827})=0,
]

and Poitou–Tate produces the global reflected lift.

That lift is not canonically a point. Its fiber is a torsor under the strict reflected Selmer group. The canonical object is

[
\overline y_{827}
\in
\operatorname{Sel}*{\lambda,827}^{\chi^\ast}/
\operatorname{Sel}*{0}^{\chi^\ast}.
]

So prefer:

```text
NormalizedReflectedLiftCoset827
```

or

```text
Nonempty NormalizedReflectedLiftFiber827
```

over an unjustified canonical `NormalizedReflectedClass827`.

There is also only one normalization freedom: if the 827 coordinate is normalized to (1), the wild coordinate acquires a retained nonzero `wildScale`. Do not demand both equal (1).

## 4. The exact arithmetic theorem relating this to 7a

Let

[
G_{7a}:X_{\mathrm{FLT}}\longrightarrow Q_{7a}
]

be the class-valued 7a gauge, with (\dim Q_{7a}\le1).

The missing producer should be:

[
\boxed{
\phi_{827}(x)
=============

\operatorname{ArtinRead}*{827}\bigl(G*{7a}(x)\bigr)
\quad\text{for every }x.
}
]

Allow a recorded unit factor if the existing root/orbit conventions differ:

[
\phi_{827}(x)
=============

v,
\operatorname{ArtinRead}*{827}\bigl(G*{7a}(x)\bigr),
\qquad v\in k^\times.
]

This is the targeted **Kummer–Artin comparison theorem**. It must be proved as equality of maps, independently of the Fermat class and without assuming 7a.

Suggested name:

```text
SevenAKummerArtinFactorization59
```

Its arithmetic obligations are precise:

* the (\chi\mid\omega\chi^{-1}) seating;
* full-orbit orientation at 827;
* conductor/ray-class lawfulness;
* Artin evaluation equals the appropriate local Kummer cups;
* compatibility with the class-valued ideal gauge;
* first-layer/Bockstein receipt if the source is deeper than 59-torsion.

Poitou–Tate alone does not prove this comparison.

## 5. Closure

Combining the two unit comparisons gives

[
\phi_\lambda
============

uv,
\operatorname{ArtinRead}*{827}\circ G*{7a}.
]

Since (Q_{7a}) has dimension at most one and the Artin readout is nonzero on it, that readout is injective. Hence

[
\boxed{
\phi_\lambda(h_F)=0
\iff
G_{7a}(h_F)=0.
}
]

Global reciprocity plus tame silence supplies the left-hand vanishing. The existing gauge theorem turns the right-hand side into Vandiver 7a.

## Goblin-sized work order

```text
W1  TwistedLambdaCupReceipt59
W2  Lambda827PoitouTateComparison
W3  NormalizedFullOrbitEigenprofile827
W4  WildAndOrbitBoundarySameHomLine
W5  SevenAKummerArtinFactorization59
W6  NormalizedReflectedLiftFiber827
W7  wild_eq_zero_iff_sevenAGauge_eq_zero
```

The strongest simplification is that the global reflected class is not the primitive theory owes us. It is an output of PT cancellation.

The true missing theorem is:

[
\boxed{
\texttt{SevenAKummerArtinFactorization59}.
}
]

It conserves the unknown class-valued gauge, processes it through the reflected Artin witness, and only then produces the scalar reading.

