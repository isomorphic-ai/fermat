# Generic Kummer automorphism fork

This note records an isolated debugging experiment against
`leanprover-community/flt-regular` commit
`edd24b3f160b0fd5ce0ee489b69f8247117ff1ed`. It does not modify the
production `FltRegular` dependency or any production Lean module.

The experiment copied the complete upstream Case-II induction and statement,
removed the regular-prime premise, and resumed the original descent through
two narrow commuting transports. The complete patched `InductionStep.lean`,
the complete downstream `Statement.lean`, and
`GenericCaseIIHarness.lean` all compiled with Lean `4.31.0-rc1`.

The resulting arbitrary-prime endpoint had this shape:

```lean
FltRegular.caseII
  (hrepair :
    RelevantCaseIIAutomorphismTransport
      (CyclotomicField p ℚ) p)
  (hodd : p ≠ 2)
  (hprod : a * b * c ≠ 0)
  (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
  (caseII : (p : ℤ) ∣ a * b * c) :
  a ^ p + b ^ p ≠ c ^ p
```

## The two undischarged transports

1. `idealTransport` supplies, for each exact allocated ideal quotient `I`,
   a class-group automorphism `E` satisfying
   `E [I] = [I] ^ p`. The unchanged proof already has `[I] ^ p = 1`;
   injectivity of `E` then gives `[I] = 1` and the descent resumes.
   Constructing this automorphism at a nonzero `p`-torsion class is itself
   the missing special-ideal principalization. The current generic source
   route still requires Kummer primarity and plus-class nondivisibility.

2. `unitTransport` applies only to the literal ratio of a
   `CaseIIWeightedSolution`. It receives the semiprimary congruence proved by
   the unchanged induction and supplies a `FullValuationUnitTransport`.
   The full-valuation diagonal automorphism is constructed and inverted
   internally. Its undischarged arithmetic field is exactly
   `PrimitiveRelationFullValuationCongruences`, requiring adaptive precision
   `p ^ (v_p(B_i) + 1) ∣ a_i * B_i`. The existing fixed-cube source theorem
   proves only `p ^ 3 ∣ a_i * B_i`.

Thus the automorphism mechanics and the rest of Kummer's descent are generic
in `p` and in the number of coordinates. The current library does not derive
the two transports from primality alone.

## Reproduction provenance

At experiment time the surrounding Fermat repository was at
`149c95592d78f5a3787262a0f7345d55092d5242`. The full-valuation correction
used by the fork entered the repository in commit `5d71f6b`.

The generated experimental patch was 509 lines and had SHA-256:

```text
7e08253e67fcdfc9952089b13d0edecf5f5f60747afa62f9b307171a437f3d73
```

The preserved harness below has SHA-256:

```text
d377b64f015e0491b2b63241b26c03e1282fa29ef62017b7532e8c5a66259b68
```

The successful compiles used:

```bash
lake env bash -c 'LEAN_PATH=/tmp/kummer-generic-iso/local-olean:$LEAN_PATH exec /tmp/lean-4.31.0-rc1-linux/bin/lean -R /tmp/kummer-generic-iso/flt-regular -o /tmp/kummer-generic-iso/local-olean/FltRegular/CaseII/InductionStep.olean /tmp/kummer-generic-iso/flt-regular/FltRegular/CaseII/InductionStep.lean'

lake env bash -c 'LEAN_PATH=/tmp/kummer-generic-iso/local-olean:$LEAN_PATH exec /tmp/lean-4.31.0-rc1-linux/bin/lean -R /tmp/kummer-generic-iso/flt-regular -o /tmp/kummer-generic-iso/local-olean/FltRegular/CaseII/Statement.olean /tmp/kummer-generic-iso/flt-regular/FltRegular/CaseII/Statement.lean'

lake env bash -c 'LEAN_PATH=/tmp/kummer-generic-iso/local-olean:$LEAN_PATH exec /tmp/lean-4.31.0-rc1-linux/bin/lean -R /tmp/kummer-generic-iso /tmp/kummer-generic-iso/GenericCaseIIHarness.lean'
```

The harness is documentary source: it compiles after applying the
experimental patch to the isolated `flt-regular` tree. It is intentionally
not imported by the production repository.
