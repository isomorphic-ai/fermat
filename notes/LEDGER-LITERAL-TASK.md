# TASK LEDGER-LITERAL (W) — the formula must appear, or it is Kummer in new clothes

**TruthSeed:** `fermat-ledger:the-proof-reveals-itself-or-it-is-not-conservation`
**For:** PRO Goblin (GPT 5.6 Sol Ultra) via codex, working in ~/fermat.
**Ruling (Fabian, 2026-08-01):** we do NOT attempt Lemma I / 7a, NOT the
transformer, NOT the endpoint. The classical case is already formalized
in this tree; the campaign is EXPANSION, and expansion means finding
the boundaries first. The goal is not to prove 59. The goal is to find
the conservation-law invariants under which the proof reveals itself.
The test is literal: the ledger formula must appear LOAD-BEARING in the
proof terms. Where it does not, that is a boundary — map it, do not
paper over it.

## W1 — the non-lossy certificate (kill the boolean)

Refactor the Bernoulli certificate layer to the structure-preserving
form (per the Sol-instance analysis committed in the certificate doc):

- depth decomposes over named channels:
  `depth = liftChannel + couplingChannel`, with liftChannel proven
  structurally = 1 (the v_p of the index) and couplingChannel a
  certified field per position;
- the surplus is explicit and conserved, never projected away:
  `e = min(e,2) + (e-2)+` — a field `(coupling - 1)+`, present even
  when zero. Nothing that can be nonzero may exit any interface as a
  Boolean.
- the old `NoBernoulliCubeObstruction` becomes a corollary so nothing
  downstream breaks; the 59 instance re-certifies via the existing
  computed table (channel values derivable from
  BERNOULLI-CUBE-CERTIFICATE.md; interface change only, no new
  computation needed).

## W2 — the layered repayment operator (totality over verdicts)

Introduce the graded obstruction states and the operator signature:

- `C_d` = obstruction state carrying residual coupling-depth d, with
  the exact-sequence reading documented (current repayment handles
  M/pM; the residual pM IS the d-1 state — the energy has an address);
- `Repay : C_d -> C_(d-1)` (d >= 1), with the conservation law: total
  layer count decreases by exactly one and the residual is carried
  explicitly — no layer silently disappears (the Taylor-Wiles patching
  discipline, credited by name);
- base case `C_0` = the vacuum/regular closure (C1 + stock rungs);
- the d = 1 instance IS the existing
  `repayment_of_capacity_and_flow` — prove the equivalence so 59
  consumes the new shape for free;
- the induction step's missing input (what supplies the depth-(k+1)p
  congruence funding layer k — "layer transport") is a NAMED interface,
  stated and guarded, not proven: it is expected to be a boundary.

## W3 — the ledger-literal audit and the BOUNDARY-MAP

The heart of the session. For EVERY main theorem in the conservation
cones (stock rungs N1-N7, credit rungs C1-C3, flow, gauge quotient,
fold, repayment, the N59 instance layer):

1. Determine mechanically whether the conservation identity
   (`Ledger` equation stock + credit + converted = total, the channel
   decomposition, the layer conservation) is LOAD-BEARING in its proof
   term — build a `#guard_depends_on` environment command (sibling of
   your `#guard_no_decl_prefix`) that checks a declaration's proof
   transitively uses a named identity lemma. Classify: LITERAL
   (identity load-bearing) / DECORATIVE (identity defined nearby but
   bypassed) / ABSENT.
2. Write notes/BOUNDARY-MAP.md: the classification table, and for every
   DECORATIVE/ABSENT theorem and every named open seam (7a/Lemma-I,
   the transformer successor, layer transport), state the boundary in
   invariant terms: WHICH conserved quantity is missing such that the
   proof would route through the ledger. Boundaries are the
   deliverable — each one is a candidate new invariant, i.e. the
   actual product of this campaign.
3. Add the ledger-literal gate to Verification.lean: the identity
   lemmas exist, and the theorems claimed LITERAL are guarded as such
   by `#guard_depends_on`. The gate must be green for the
   classification to be trusted.

## House rules (binding, unchanged)

PREDICTIONS entry first — predict per cone which theorems will turn
out DECORATIVE (the honest expectation: several stock rungs route
through charge arithmetic without the three-column equation; say so
before looking). FINDINGS at discovery. Generic core over p; literals
only in instance layers; all existing guards stay green. No Lemma I,
no endpoint, no transformer — obstruction probes for THOSE seams stay
exactly as they are; this session maps, it does not cross. Truthful
commits; ps before builds.

— Fable (reviewer), on behalf of Fabian, 2026-08-01

## Amendment (Fabian, 2026-08-01) — the isomorphism target for the NEXT session

The scheduler laws are themselves formalized in Lean
(goblin@i9 ~/scheduler/iso-conserve-lean: IsoConserve.L1Conservation,
L2Monotone, L3Absorbing, L4Integral, Noether, KummerNoetherLedger). An
isomorphism should therefore EXIST as a compilable object: after the
BOUNDARY-MAP lands, the follow-up session builds the formal bridge
`Fermat.Conservation.Ledger` <-> `IsoConserve.L1/L4` (lake path
dependency or vendored module with provenance — mechanics free, the
theorem is the point). The fermat proofs should ultimately consume the
scheduler's conservation law itself, not a lookalike. Note that
IsoConserve.KummerNoetherLedger is the same bridge already built from
the scheduler side — the two ends of the tunnel should meet.
