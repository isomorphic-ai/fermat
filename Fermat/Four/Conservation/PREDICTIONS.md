# N4 conservation predictions

Recorded before implementation work on 2026-07-28.

## Predicted proof shape

1. The stronger auxiliary equation will be represented directly over `ℤ`:
   `x ^ 4 + y ^ 4 = z ^ 2`, with charge `z.natAbs`.
2. A hypothetical nonzero solution will first be normalized to a primitive
   positive solution. Parity and coprimality should make
   `(x ^ 2, y ^ 2, z)` a primitive Pythagorean triple.
3. Mathlib's Pythagorean-triple parametrization will expose the closed
   n=2 ledger
   `(m ^ 2 - n ^ 2, 2 * m * n, m ^ 2 + n ^ 2)`. This coupling-free
   decomposition, already interpreted as balance in
   `Fermat.Two.PythagorasConservation`, should be the engine that exposes the
   smaller square-triangle solution needed by the n=4 drain.
4. The classical coprime double descent will become a charged step:
   from one primitive nonzero solution, construct another solution of the
   stronger equation with strictly smaller `natAbs` hypotenuse charge.
5. The generic no-infinite-positive-charge floor currently housed in the n=3
   spine will be hoisted to `Fermat.Conservation.Floor` and reused by both
   rungs rather than duplicated.
6. The public endpoint will first rule out the stronger square equation by
   drain plus floor and then prove
   `Fermat.Four.holdsAt_four_conservation : Fermat.HoldsAt 4`.

## Predicted compiler pressure

- The pinned Mathlib Pythagorean-triple API is expected to use naturals and
  may orient legs or parity differently from the integer auxiliary equation.
  Source inspection and small compile probes will be needed to identify its
  actual eliminator.
- Primitive normalization is expected to require careful transport through
  `Int.natAbs`, gcd division, signs, and zero cases.
- The hard arithmetic seam should be the second parametrization: extracting
  coprime squares from the pairwise-coprime factors produced by the first
  right-triangle ledger, then assembling the strictly smaller solution.
- The real downstream stronger theorem will be patched and compiled in place;
  a standalone certificate or provider abstraction will not substitute for
  the charged transformer.

## Predicted audit

- Every Mathlib import will have a bounded documented role: Pythagorean
  triples, integer/natural parity, coprimality, square extraction, or general
  algebra only.
- No module in the N4 dependency cone will import Mathlib's FLT-four proof or
  cite `fermatLastTheoremFour`, `not_fermat_42`, or anything derived from
  them.
- An isolated import test will require those forbidden names to be unknown,
  auditing the transitive cone rather than only source spelling.
- Every public theorem will receive a `#print axioms` check against the
  standard `[propext, Classical.choice, Quot.sound]` baseline.
- The delivered cone will contain no `sorry`, `admit`, or added `axiom`; its
  Lake build and whitespace checks will be clean independently of the known
  repository manifest drift.
