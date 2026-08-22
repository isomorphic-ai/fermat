# TASK TRANSFER — mint the accounted transfer; meet the tunnel; retrofit everything you can

**TruthSeed:** `fermat-ledger:strictly-smaller-was-a-projection-of-a-transaction`
**For:** PRO Goblin (GPT 5.6 Sol Ultra) via codex, working in ~/fermat.
**Mandate (Fabian, 2026-08-01):** "Yes, transfer. As much as we can do!"
notes/BOUNDARY-MAP.md found one missing invariant class repeated in every
row: the accounted transfer. This session mints it once, bridges it to
the scheduler's formalized law, and retrofits as many cones as budget
allows. Still NO Lemma I, NO transformer inhabitant, NO endpoint —
their probes stay; their boundary entries may be restated as Transfer
inhabitation problems, not solved.

## W1 — mint `Transfer` (route-neutral core)

`Fermat/Experiments/Conservation/Transfer.lean`: the accounted transfer between
Ledger states over a common carrier:

- fields: `before after : Ledger-state`, `spent`, with laws
  `before.total = after.total`, both states satisfy
  `conservation_identity`, and the column deltas account exactly for
  `spent` (credit decrease + stock decrease = converted increase, per
  the BOUNDARY-MAP equations);
- composition: transfers chain (the descent is a path of transfers);
- projection lemmas: the legacy facts are corollaries — a Transfer
  with `spent > 0` projects to the old strict charge inequality; a
  chain of positive transfers projects to the floor's hstep. The old
  vocabulary must become DERIVED, never parallel.

## W2 — the tunnel: bridge to IsoConserve

The scheduler laws are formalized at goblin@i9
~/scheduler/iso-conserve-lean (IsoConserve.L1Conservation, L4Integral,
Noether, KummerNoetherLedger). Build the formal correspondence:
Transfer/conservation_identity is the scheduler's L1 step-conservation
(accounted preserved at every step; RoutePlan balanced). Mechanics are
free: lake path dependency IF toolchains agree — CHECK lean-toolchain
FIRST; on mismatch do NOT fight toolchains: vendor the minimal L1/L4
statement module with a provenance header (source path, commit,
sha256) and prove the correspondence against the vendored statements.
Either way the deliverable is a compiled theorem pair: every Transfer
induces an IsoConserve-shaped conserved step, and conversely the
scheduler step shape instantiates Transfer. The two tunnel ends
(KummerNoetherLedger was dug from the scheduler side) should meet —
say so in the file header when they do.

## W3 — retrofit, in priority order, as many as budget allows

Each retrofit = construct the cone's Ledger adapter + restate its
descent/transition as Transfer(s) + the old theorem derived as a
projection + flip its BOUNDARY-MAP classification via a new
#guard_depends_on entry. Priority:

1. N3 drain (the oldest offender): the state-linked cubic ledger
   transfer — successor multiplicity drop and factor ledger as two
   projections of ONE conserved before/after state.
2. N2 Noether repair: `charge_conserved` via column-by-column
   functoriality of the accounting adapter under linear isometry.
3. Graded C3 to global columns: `accountCredit = totalLayers`; one
   repayment layer = credit -1, converted +1, stock and total fixed.
4. Then as many further rows of BOUNDARY-MAP as remain workable in
   order of leverage: N5 charged-descent transitions, N4 descent
   equality with spent, N6 oriented successor, N7 gauge/drain laws,
   flow accountFlow (product/sum conservation as credited columns),
   C1 account map (merge additive), C2 capacity spending law,
   Bernoulli channel-to-column bridge, the 59 instance accounting.
   Stop cleanly when budget runs low: a finished retrofit committed
   beats two half retrofits.

## W4 — the map update

Re-run the classification for every retrofitted path; update
notes/BOUNDARY-MAP.md in place (keep the old classification visible as
struck-through or a before/after column — the map's history is part
of the record). Restate the three seams' boundary entries in Transfer
vocabulary. Verification gains a guard per new LITERAL claim.

## House rules (binding)

PREDICTIONS entry first: which retrofits resist, whether the tunnel
compiles or the toolchain forces vendoring, expected count of flipped
rows. FINDINGS at discovery. Generic core over p; literals in
instance layers; every existing guard stays green; grep gates extended
to Transfer.lean. No Lemma I, no transformer inhabitant, no endpoint.
ps before heavy builds; truthful commits; a clean stop with an honest
count beats an overreach.

— Fable (reviewer), on behalf of Fabian, 2026-08-01
