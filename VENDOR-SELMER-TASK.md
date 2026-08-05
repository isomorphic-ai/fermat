# TASK VENDOR-SELMER — inhabit the unconditional wall from the fork PR

**TruthSeed:** `fermat-selmer:the-wall-gets-a-patch-with-a-url`
**For:** PRO Goblin (GPT 5.6 Sol Ultra) via codex, working in ~/fermat.
**Authorization (Fabian, 2026-08-05):** continue the fermat campaign by
copying the sub-lemma from the Mathlib branch, with citable provenance:
https://github.com/fabianx-ai/mathlib4/pull/1 (open, AI-disclosure
labeled, head commit 6c01b3a6a13de72eabd868ca50d743f43888af92, verified
live today). Standing rules unchanged: NO endpoint, NO transformer; the
STAGE task's typed gauge outcomes may be attempted where the machinery
now reaches.

## W1 — vendor with provenance (the established discipline)

Port the selmer-class-sequence material (toClass, toClass_ker,
toClass_range and their private helpers) from ~/Mathlib branch
selmer-class-sequence into this tree as
Fermat/Conservation/SelmerSequence.lean (route-neutral core).
Provenance header: the PR URL above, the head commit, and per-source
SHA-256 (the IsoConserveStatements pattern). The fermat pin is mathlib
rev 0531bb79 on Lean 4.31.0-rc1 - the research audit confirmed
SelmerGroup.lean is IDENTICAL between pin and master, so the API should
port cleanly; adapt module-system syntax differences (public import /
expose) to this pin's conventions and document every delta in the
header. Faithful port, no improvements - deltas are findings.

## W2 — inhabit the realization

Construct the instance of SelmerClassSequenceRealization (the withheld
structure in Fermat/Conservation/CommonActionStage.lean and its
selected N59 counterpart): classProjection from the vendored toClass
(through the Additive wrapping the stage already uses), middle
exactness from toClass_ker, surjectivity onto the p-torsion from
toClass_range. WithheldSelmerClassSequenceRealization becomes a
theorem. The unconditional wall falls; update BOUNDARY-MAP.md
accordingly (before -> after, provenance cited).

## W3 — advance honestly through what unlocks

With the realization inhabited, walk the StrictRouteBoundary checklist
(exactness, both character allocations, the omega-dual laws, both
integral guards, the allocated Selmer lift, both beta compatibilities):
discharge what the campaign machinery now genuinely supplies, and
re-localize the remaining conditional wall (rho or whichever item now
binds first). If the corner unit-ideal gauge reading becomes
attemptable on the stage, attempt it per the STAGE task's three typed
outcomes (identity / named factor / localized wall) - all three remain
results. The endpoint and transformer stay forbidden regardless.

## House rules (binding)

PREDICTIONS first (port-delta expectations; which StrictRouteBoundary
item binds next; committed guess for the gauge reading). FINDINGS at
discovery. All guards, grep gates, and the full verification stay
green; SelmerSequence.lean enters the literal gates; new guards per
public theorem; standard trio. ps before heavy builds (a second codex
session is writing docs in ~/mathlib-selmer-notes - it is light, but
check). Truthful commits.

— Fable (reviewer), on behalf of Fabian, 2026-08-05
