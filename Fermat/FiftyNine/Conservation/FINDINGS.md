# N59 conservation findings

## 2026-07-29 — Sophie--Germain is clean; the shared case assembler has API drift

- `Fermat.SophieGermain` used the legacy `Fermat.Basic` umbrella only for
  generic Mathlib arithmetic and the fixed-exponent proposition.  Replacing
  that import by `Mathlib` plus `Fermat.Statement.Basic` compiles and makes
  `Fermat.HoldsAt.mono_of_dvd` unknown in a direct environment probe.
- Compiling `Fermat.Cases` after the repair reaches a pre-existing
  `flt-regular` mismatch: its call supplies the Case-I predicate to
  `FltRegular.caseI`, while the pinned declaration now first demands an
  `IsRegularPrime p` argument.  No `Fermat.Cases` object file is therefore
  available.
- This does not change the credit obstruction.  If the N59 second case is
  eventually excluded locally, the short Sophie--Germain final assembly
  must also be reconstructed at the narrow statement boundary rather than
  importing the currently broken facade.

## 2026-07-29 — the doctrine invalidates the scalar-credit ledger

- The earlier `Ledger` placed `stock`, `credit`, and `converted` in one
  additive commutative monoid and implemented repayment by subtraction from
  the scalar credit column.  The accepted obstruction map now makes that a
  type error: stock is additive node data, while credit is a semilattice
  matrix on node pairs.
- The real source must therefore be patched, not wrapped.  The scalar-credit
  structure and its seven transfer theorems will be removed from the N59
  spine.  The stock balance and generated credit matrix will remain
  orthogonal fields, with an explicit seam where an arithmetic repayment
  witness permits a stock conversion.

## 2026-07-29 — the generated N59 cycle explains 28, 4×7, +1, and ×2

- Multiplication by `4` modulo `59` has exact order `29`.  Starting from the
  seed `1` therefore produces a 29-cycle; its 28 non-closing successive
  edges generate the unit-rank-28 sub-ledger.
- `Fin 28` is reindexed by the structural equivalence
  `Fin 4 × Fin 7 ≃ Fin (4 * 7)`.  No list of 28 units or 784 matrix positions
  is needed to define the ledger.
- Negation of an exponent is complex conjugation.  The debit and receivable
  sides are therefore the two orientations of the same generated matrix,
  accounting for the outer factor `2` in `59 = 2 * 29 + 1`.
- The auxiliary prime has the required generation story
  `827 = 2 * 59 * 7 + 1`.  If its residue certificate is consumed, its root
  must likewise be derived as `2 ^ (2 * 7)`, not introduced as an opaque
  literal `671`.

## 2026-07-29 — endpoint surgery now has five exact seams

- The elementary endpoint assembly can be made import-clean by narrowing
  `Fermat.SophieGermain` from the legacy `Fermat.Basic` facade to
  `Mathlib` plus `Fermat.Statement.Basic`.  That exposes
  `holdsAt_of_auxiliaryPrime_of_secondCaseExcluded` without exposing the
  forbidden divisibility transport.
- The remaining work queue is, in order: generated Sophie--Germain facts at
  827; generated circular-unit certificate to finite index (C2); the bounded
  Sinnott index-to-plus-class bridge (C4); Vandiver deep-congruence
  coefficient forcing and repayment (C3); and the state transformer that
  turns principal generators into a strict successor.
- Existing implementations of those seams transitively load, respectively,
  the forbidden `FirstCase`, `Fermat.Irregular.*`, generic Lemma-II, and
  historical descent machinery.  The current ramified-scale theorem proves
  only `59^n < 59^(n+1)`; it does not construct a successor from a Fermat
  counterexample.
- Thus the floor remains clean and sufficient once a successor exists, but
  neither a capacity number nor an abstract repayment record can manufacture
  that successor.

## 2026-07-29 — the executable structural audit is green

- `Verification.lean` checks all 19 public theorems in the N59 structural
  spine plus both shared-floor theorems.  Ledger transfers use
  `[propext, Quot.sound]`; every gauge/rank/drain and floor theorem uses the
  standard trio `[propext, Classical.choice, Quot.sound]`.
- An environment-level command rejects every declaration beneath each of
  the six forbidden N59 module prefixes and beneath
  `Fermat.GenericIrregular`, `Fermat.Irregular`, and `Fermat.Ladder`.
  Direct guards also prove the forbidden divisibility transport and the
  historical/KummerIso N59 endpoints unknown.
- The standalone target
  `lake build Fermat.FiftyNine.Conservation.Verification` is green
  (`8520/8520`).  The audit deliberately does not claim the requested final
  endpoint: that theorem cannot be added until the repayment/strict-successor
  obligation below is discharged.

## 2026-07-29 — the clean structural spine compiles, and isolates the bite point

- `Conservation.Spine` now imports all seven primitives through their narrow
  boundaries.  It defines the explicit equation
  `stock + credit + converted = total`, the N1 vacuum ledger, and generic
  repayment as an internal transfer from credit to converted.  The transfer
  preserves the audited total by commutative-monoid bookkeeping.
- The generic N7 norm/gauge API specializes cleanly: a 59th cyclotomic field
  has free unit rank 28, its full gauge has positive regulator, multiplication
  by any gauge unit preserves charge, `λ = 1 - ζ₅₉` has charge 59, and the
  ramified scale is exactly `59 ^ n` and strictly monotone.
- The isolated Lake target builds warning-free.  This confirms that vacuum,
  ledger transfer, gauge, ramified drain, and the shared floor are not the
  obstruction.
- The compiled `Ledger.repay` is intentionally only the accounting law: it
  transfers an amount already known to be available.  It neither identifies
  class-group capacity nor proves that a Fermat-produced unit admits a
  59th-power repayment.  Treating it as the requested arithmetic repayment
  would hide the precise missing theorem recorded below.

## 2026-07-29 — no independent Case-II or endpoint escape hatch exists

- Exhaustive declaration and import-graph searches found exponent-59
  endpoints only in the forbidden generic proof, the historical Vandiver
  chain, the KummerIso regressions (which import the same forbidden
  machinery), and the Ladder facade.
- Mathlib's FLT development proves exponents three and four and supplies
  only statement/polynomial infrastructure beyond them.  Its exponent
  monotonicity theorem gives no reduction for the prime exponent 59.
- The nearest external Kummer unit theorem assumes that 59 is coprime to
  the full cyclotomic class-group cardinality.  That is the regular-prime
  hypothesis and is precisely unavailable at the irregular prime 59; it
  cannot implement the credit repair.
- Sophie--Germain's auxiliary-prime theorem forces a primitive solution
  into Case II but does not exclude Case II.  There is no multi-auxiliary
  aggregation theorem in the repository or dependencies, and finitely many
  auxiliary divisibilities alone do not contradict three unbounded integer
  entries.
- Thus the unconditional repayment and strict successor cannot be obtained
  by selecting another existing safe theorem.  They require genuinely new
  class-group/unit mathematics or a relaxation of the stated import
  boundary.

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
