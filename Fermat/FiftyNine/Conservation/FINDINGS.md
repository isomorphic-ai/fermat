# N59 conservation findings

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
