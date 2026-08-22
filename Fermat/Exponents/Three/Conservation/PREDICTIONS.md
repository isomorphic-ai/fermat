# N3 conservation predictions

Recorded before implementation work on 2026-07-27.

## Predicted proof shape

1. The Eisenstein charge will be exposed as the integer-valued coordinate
   polynomial
   `charge (x + y * ζ₃) = x ^ 2 - x * y + y ^ 2`.
   Ring normalization should prove that it is multiplicative.
2. The Fermat ledger
   `a ^ 3 + b ^ 3 = (a + b) * charge (a + b * ζ₃)`
   should close by integer polynomial normalization.
3. For `λ = 1 - ζ₃`, coordinate reduction should give `charge λ = 3`.
4. The conservation floor should be independent of the number theory:
   well-foundedness of `<` on positive natural charges will rule out a
   sequence whose charge strictly decreases at every successor.
5. The arithmetic core will normalize a hypothetical nonzero cubic solution,
   perform Euler's descent, and feed the resulting smaller solution back into
   the floor. The expected final theorem is
   `Fermat.Three.holdsAt_three_conservation : Fermat.HoldsAt 3`.

## Predicted compiler pressure

- The likely representation is Mathlib's Eisenstein-integer or quadratic-ring
  API, but its exact coordinate and norm names are expected to require source
  inspection.
- Positivity is expected to require a separate lemma characterizing zero
  charge; keeping the floor on `ℕ` should make strict descent reusable.
- Coprimality and the prime above `3` are expected to be the hard part of the
  descent transformer. The first attempt will patch the real downstream
  theorem, not introduce a certificate or provider abstraction.
- If the full Euler transformer cannot be closed in this session, the only
  permitted open rung is one named descent-step statement with all hypotheses
  and the strict charge conclusion visible. All earlier spine rungs must
  remain proved.

## Predicted audit

- No module in the conservation dependency cone will import or cite
  `fermatLastTheoremThree`, `Fermat.holdsAt_three`, or an intermediate proved
  from either.
- The module docstrings will list every Mathlib import and its bounded role.
- Delivered theorems will contain no `sorry`, `admit`, or added `axiom`.
- The final pass will run the full Lake build, whitespace checks, forbidden
  dependency searches, and `#print axioms` checks for every public theorem.
