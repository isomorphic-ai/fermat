# N6 conservation predictions

Recorded before implementation work on 2026-07-28.

## Pre-registered rung

I expect rung **(b)**: a native degree-6 conservation development that
reaches a small list of exact, separately falsifiable closure lemmas, but
does not initially close those lemmas without reconstructing a 3-shaped
descent inline.

If compiler-driven repair shows that the remaining lemma is definitionally
just an exponent-3 Fermat statement rather than a genuinely narrower
Pythagorean-cube obligation, I will reclassify the result as rung **(c)** and
type the forced reduction on the native degree-6 solution object.  I do not
expect to use or expose `Fermat.HoldsAt 3`, any existing exponent-3 theorem,
or `Fermat.HoldsAt.mono_of_dvd`.

## Predicted proof shape

1. A hypothetical sixth-power solution will be represented directly, with
   the degree-6 ledger
   `a ^ 6 + b ^ 6 = (a ^ 2 + b ^ 2) *
     (a ^ 4 - a ^ 2 * b ^ 2 + b ^ 4)`.
   The second factor will also be exposed as the norm-form value
   `(a ^ 2) ^ 2 - (a ^ 2) * (b ^ 2) + (b ^ 2) ^ 2` in Eisenstein
   coordinates.
2. The balance-at-the-top view will turn the same solution into the
   Pythagorean triple
   `(a ^ 3) ^ 2 + (b ^ 3) ^ 2 = (c ^ 3) ^ 2`.
3. Primitive normalization, parity, and the N2 balance engine should provide
   coprime parameters `m,n` with cube legs represented by
   `m ^ 2 - n ^ 2` and `2 * m * n`.
4. Coprimality should force the factors in the even-leg equation to be cubes
   up to the visible power of `2`.  Propagating those cube constraints back
   through `m ^ 2 - n ^ 2` is expected to produce a smaller charged
   Pythagorean-cube state.
5. If that transformer can be constructed inline, its positive hypotenuse
   charge will drain through
   `Fermat.Conservation.impossible_of_strict_charge_drain`, yielding rung
   (a).  My registered expectation is that one exact cube-propagation lemma
   will remain, yielding rung (b).

## Predicted compiler pressure

- The pinned Pythagorean-triple API may orient the odd and even cube legs
  differently, so parity transport and sign normalization will require
  compile probes.
- Extracting cubes from pairwise-coprime products over `ℕ` or `ℤ` is likely
  to require local valuation arithmetic not already packaged at the needed
  granularity.
- The hardest point should be converting
  `a ^ 3 = m ^ 2 - n ^ 2` and `b ^ 3 = 2 * m * n` into an iterable state
  with a strictly smaller native degree-6 charge.  This is precisely where
  a direct composite drain may reveal the prime fold as its composition
  law.
- A conditional closure lemma will be stated on the smallest native typed
  state possible.  It will not be hidden behind a provider structure or an
  assumption equivalent by definition to `Fermat.HoldsAt 3`.

## Predicted audit

- The N6 cone will import only `Fermat.Statement`,
  `Fermat.Conservation.Floor`, bounded N2/N4 conservation support, and
  bounded algebra/arithmetic modules.
- It will not import Mathlib FLT modules, any `Fermat.Three` module, any
  existing exponent-3 Fermat declaration, `Fermat.HoldsAt.mono_of_dvd`, or
  a Ladder transport/fold theorem.
- An executable isolated-import verification leaf will require all forbidden
  names, including `Fermat.HoldsAt.mono_of_dvd`, to be unknown in the
  transitive environment.
- Every public theorem will receive a guarded `#print axioms` check.  The
  accepted axiom surface is at most
  `[propext, Classical.choice, Quot.sound]`.
- The delivered cone will contain no `sorry`, `admit`, or added `axiom`;
  the independent N6 build, standard trio audit, forbidden-name guards, and
  whitespace checks must all be clean.
