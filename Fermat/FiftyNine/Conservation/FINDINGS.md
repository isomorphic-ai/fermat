# N59 conservation findings

## 2026-07-29 — the numerical certificates do not certify credit capacity by themselves

- A kernel-checked inverse for the `28 × 28` residue matrix proves only that
  the displayed matrix is nonsingular.  Turning that fact into
  `¬ 59 ∣ realUnitRelIndex ...` requires the residue-functional realization
  and determinant/index transfer found only in
  `Fermat.Irregular.CircularUnitResidues` and
  `Fermat.Irregular.CircularUnitIndex`.
- Turning that relative-index conclusion into a plus-class-number statement
  then requires the forbidden prime-generic Sinnott bridge.  Mathlib and the
  conservation spines contain no replacement for either structural map.
- Likewise, `B₄₄` having exactly one factor of 59 identifies one Bernoulli
  valuation; no permitted theorem identifies that valuation with the
  cardinality or exponent of the 59-primary class-group credit.  Calling its
  value the credit capacity would therefore overstate what the certificate
  proves.
- The local residues `38` and `473` are unused numerical shadows in the
  existing repository proof.  Without a newly proved bridge, they cannot
  truthfully serve as repayment evidence.

## 2026-07-29 — compiler surgery reaches a genuine repayment theorem

- The shared floor has one decisive input:
  `hstep : ∀ state, ∃ next, charge next < charge state`.  None of the seven
  permitted spines contains a declaration that constructs such a successor
  from an exponent-59 counterexample; they contribute the charge,
  balance/gauge laws, and the floor only.
- The first N59-specific theorem needed to fund that successor is the
  following mathematical repayment statement in substance: for a primitive
  59th root `ζ` and a unit `u`, a depth-118 congruence
  `(1 - ζ) ^ 118 ∣ u - c ^ 59` must force `u` to be a 59th power.  This is
  the `KummerUnitPowerConclusion` seam used by the repository's historical
  state transformer.
- The existing proof of that seam is exactly Vandiver's Lemma II.  Its
  finite unit-system adapter is the forbidden
  `Fermat.FiftyNine.GenericLemmaTwo`; the specialized alternative imports
  `Fermat.Irregular.VandiverLemmaTwoBridge` and
  `Fermat.Irregular.VandiverRealUnits`.  The state-to-state reduction itself
  is likewise exposed only by the forbidden historical machinery.
- Consequently a ledger theorem parameterized by repayment would compile,
  but it would not prove `Fermat.HoldsAt 59` and is expressly ruled out by
  the pre-registered audit risk.  The work queue is therefore the
  unconditional repayment/strict-successor theorem itself, not another
  provider structure or harness.

## 2026-07-29 — N5 carried an unused forbidden statement facade

- `Fermat.Five.Conservation.Spine` imported the wider `Fermat.Statement`
  even though no declaration in the file uses the fixed-exponent statement.
  That facade defines `Fermat.HoldsAt.mono_of_dvd`, so importing the N5
  gauge primitive made a forbidden name visible in the N59 cone.
- The source-level repair is to remove that unused import from the actual N5
  spine.  Its remaining imports supply the shared floor, golden-unit
  arithmetic, and ring normalization directly.  This preserves the N5 API
  while making the rank-one gauge primitive composable under the N59
  non-circularity boundary.
- Rebuilding the real N5 public cone after that surgery exposed the one
  legitimate downstream dependency: `Conservation.Reduction` states a
  theorem returning `Fermat.HoldsAt 5`.  It now imports
  `Fermat.Statement.Basic` explicitly.  Thus the proposition remains
  available exactly where used without restoring the forbidden transport.

## 2026-07-29 — every listed certificate facade is transitively contaminated

- `Fermat.FiftyNine.ArithmeticCertificate` imports the exponent-37 scanner
  and opens `Fermat.Irregular.VandiverData`; its public conclusions are
  numerical, but its environment is not inside the required cone.
- `Fermat.FiftyNine.CircularUnitCertificate` directly imports
  `Fermat.Irregular.CircularUnitIndex`.
- `Fermat.FiftyNine.CircularUnitIndex` directly imports the forbidden
  `Fermat.FiftyNine.FirstCase` module and several `Fermat.Irregular.*`
  modules.
- `Fermat.FiftyNine.CircularUnitResidues` likewise imports the forbidden
  first-case module and generic irregular circular-unit machinery.
- Therefore none of the four listed facades can be imported by the
  conservation cone.  Following the task's credited-reconstruction rule,
  only exact finite data that the finished ledger actually consumes will be
  restated and kernel-checked locally.  The final consumed-number list will
  be maintained below when that boundary is fixed.

## 2026-07-29 — the reusable gauge primitive is generic, but the rung roots are not

- `Fermat.Seven.Conservation.Spine` defines absolute integral norm charge,
  full Dirichlet gauge coordinates, unique unit decomposition, gauge
  invariance, and regulator positivity for an arbitrary number field.  This
  is the clean primitive for the rank-28 N59 gauge; only the rank calculation
  is conductor-specific.
- The N3, N4, N5, N6, and N7 public FLT endpoints remain
  exponent-specific.  They cannot themselves turn an exponent-59 state into
  a strict successor.  Their reusable contribution is the ledger/drain/gauge
  interface, not a transported proposition.
- The root `Fermat.Four.Conservation` imports the wider
  `Fermat.Statement`, which exposes the expressly forbidden
  `Fermat.HoldsAt.mono_of_dvd`.  N59 may use the N4 spine idea or its narrow
  implementation files, but cannot import that public root.

## 2026-07-29 — the existing N59 endpoint is exactly the forbidden route

- `Fermat.FiftyNine.GenericProof.holdsAt_fiftyNine_generic` packages the
  Sophie--Germain first case and a generic-irregular second-case
  certificate.  Its second-case chain consumes the plus-class-number
  theorem, a 28-unit system, derivative congruences, and the sole
  Bernoulli channel at index 44.
- This confirms that wrapping the existing endpoint, importing its
  intermediate conclusions, or duplicating its `GenericLemmaTwo` adapter
  would violate the assignment.  The conservation implementation must
  expose a different state boundary: funded credit, its finite capacity,
  repayment, and a strict successor passed to the already-minted floor.

## Consumed reconstructed certificate data

No certificate number is consumed yet.  Entries will be added here at the
same time as the corresponding executable reconstruction.
