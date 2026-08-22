# Power-root cube predictions

Recorded after reading `CUBE-TASK.md` and before creating or editing any Lean
implementation for the power-root cube.

## W1 — two-term principal-ideal arrow

- The upstream generator should vendor as route-neutral code with only pinned
  API normalization, not a new arithmetic premise.  Its root witness and
  obstruction should expose the kernel/cokernel behavior needed to regard
  `Kˣ → FracIdeal(𝒪 K)` as a two-term complex.
- Units should occur as retained degree-one morphisms and the class group as
  degree-zero components.  The Selmer group should be the middle extension
  carrying both pieces.  I do not expect a canonical product decomposition;
  the honest public object should name the extension class and retain the
  exact maps.
- The no-splitting rule should be executable source/declaration auditing, in
  addition to proof-value dependency checks.  In particular, no public result
  should accept or manufacture an equivalence between the Selmer middle and a
  product of the unit quotient with class-group torsion.

## W2 — three naturality directions

- Group-ring equivariance should be the most concrete face.  Multiplication
  and exponent shift on the principal-ideal arrow are expected to commute
  with the root/obstruction generator by the upstream `root_mul` and
  `root_shift` laws.
- Reflection should compile at the abstract arrow level, but identifying its
  arithmetic target with the `χ*` eigenspace is expected to require the
  already-named reflected-dual glue.  The involution law can be proved while
  the carrier identification remains an explicit interface.
- Localization should expose a commuting-square interface rather than a
  fabricated completion Selmer group.  The pinned library is not expected to
  contain a local carrier of exactly the required shape.
- `rho` should move from a guessed class-group action to data acting
  equivariantly on both terms of the principal-ideal arrow and preserving the
  power-root square.  Any summit result should consume that stronger arrow
  action and derive its class shadow.

## W3 — committed outcome guess

**Committed guess: outcome 3.**  I predict that the two proposed readings do
not initially share a type: the local-obstruction route lands in the local
`χ*`/Tate-twisted dual carrier, while localizing the global obstruction lands
in an untwisted class shadow.  Inserting the reflected character and Tate
twist should name the missing carrier and make the comparison well-typed;
this session should locate that carrier, not claim direct commutativity.

Consequently I do not predict an unconditional (7a).  Outcome 1 would require
a square whose two sides already have the same carrier, outcome 2 would
require the comparison to be typed before reciprocity sums it, and outcome 4
would require a typed comparison proving that the two readings factor through
different obstructions.  The first compiler-visible mismatch will decide
whether this pre-registration survives contact with the actual arrows.

The mod-59 identity is expected to erase a depth receipt: the exact integer
rewrite retains `59 • r1`, while reduction to the 59-torsion layer sees only
the defect `r0 - r1`.  This should be recorded as a named Bockstein-receipt
observation, not promoted to a theorem about arithmetic depth.

## Audit prediction

The completed cone should add proof-value guards for every public theorem,
an exhaustive standard-axiom scan, a generic source-literal gate, the new
mechanical no-splitting gate, and the existing forbidden endpoint,
transformer, and unconditional-(7a) checks.  Generic files should remain
prime-parametric; the numeral 59 should occur only in the selected outcome
and receipt instance.
