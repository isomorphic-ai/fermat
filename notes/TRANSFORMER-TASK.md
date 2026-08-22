# TASK TRANSFORMER — divide out the gauge, descend on our own rungs

**TruthSeed:** `fermat-n59:quotient-then-compose-nothing-borrowed`
**For:** PRO Goblin (GPT 5.6 Sol Ultra) via codex, working in ~/fermat.
**Target:** fill `TransformerProbe.lean`'s typed hole exactly —
`IsRepaid 59 u → ∃ next, next.charge < state.charge` — then the case
assembly and, if everything holds, the endpoint
`Fermat.FiftyNine.holdsAt_fiftyNine_conservation : Fermat.HoldsAt 59`
with the crown audit.

## Fabian's construction (2026-07-30)

Divide out the u₁…uₙ of the generated matrix, then assemble the proof
STRICTLY from the existing regular primitives that used the
conservation law to prove the regular exponents. Nothing classical is
borrowed: the quotient regularizes the state; the seven audited stock
rungs do the descent; the pullback returns the smaller state.

## W1 — the gauge quotient as a ledger morphism (generic)

Define the quotient of a charged state by the generated credit
sub-ledger. Its legality rests on exactly three permits, ALL already
proven — consume them as theorems, do not re-derive:

1. **Faithful at p** — capacity index prime to p
   (`capacityCertificate`, C2).
2. **No dangling debt** — every deep draw returns
   (`repayment_of_capacity_and_flow`, C3+flow).
3. **Charge-preserving (Jacobian-one)** — the Bernoulli correction
   factors have depth exactly 2, never worse
   (the certificate's second reading, commit 28d4f77): dividing them
   out multiplies the measure by a λ²-unit. This is the ()=2 fact —
   the division cannot create or destroy p-charge.

Conclusion of W1: the quotient state has vacuum credit (C1 — a
regular ledger) and the same charge. Generic over p; the permits are
fields of the prime-data record.

## W2 — the descent, strictly from OUR regular rungs

On the regularized state, run Kummer's second-case descent assembled
ONLY from the conservation primitives that proved the regular
exponents:

- the shared floor (`Fermat.Conservation.Floor`) — consume, never
  re-mint (N3/N4 lesson);
- the multiplicative charge + strict drain engines (N3, N7:
  `drainCharge_strictMono`, `charge_pow`, the λ-charge lemma);
- gauge invariance up to lattice rank (N5, N7:
  `charge_gauge_invariant`, the generic norm/gauge API that already
  "specializes cleanly" per your own N59 findings);
- composition of a balance engine inside a drain (N4);
- the state-fold vocabulary where coordinates need repackaging (N6).

The λ-factorization bookkeeping of the second case (the x+ζⁱy factor
normalization) is expected work — write it in ledger form (each factor
a node, the gauge units the credit already netted by W1, repayment
supplying the p-th roots to absorb). If a genuinely new generic lemma
is needed, mint it in the route-neutral core with the usual guards; if
you find yourself re-deriving a forbidden file line-for-line, stop and
record the finding (rule 6). The classical `Fermat.Regular.*`,
`Fermat.KummerIso.*` trees and all previously forbidden namespaces are
NOT importable for this descent — the point is that our rungs suffice.

## W3 — the pullback and the strict decrease

Lift the descended state back along the quotient. Charge strictly
decreased because W1 was charge-preserving and W2 strictly drained.
This fills the TransformerProbe type exactly. Wire it as
`stockSpineReceipt`'s missing producer.

## W4 — cases, assembly, endpoint (only if W1–W3 close)

Case I: Sophie–Germain via conservation (`Fermat.SophieGermain` at its
cleaned basic-statement boundary). Case II: W1–W3. Assemble
`holdsAt_fiftyNine_conservation`. Crown audit: `#print axioms` =
standard trio, every forbidden name unknown, the 59-literal grep gate
green over the generic core, all five-plus targets green. If any W
resists, the typed obstruction probe is the deliverable, as before.

## House rules (unchanged, binding)

PREDICTIONS entry first — where the quotient fights, whether W2 needs
new generic mint, expected patch of the probe. FINDINGS at discovery.
Generic core over p; 59 only in the instance layer; grep gate extended
to the new modules. Verification.lean guards for every public theorem.
Standalone green cones; no root build. ps before heavy builds.
Truthful commits. Credit Kummer by name for the second-case descent
shape — discovered by him, assembled from our primitives.

— Fable (reviewer), on behalf of Fabian, 2026-07-30
