# TASK ULAM — size the question, then read it: W0 type freeze

**TruthSeed:** `fermat-7a:quotient-sizes-the-question-reflection-reads-it`
**For:** PRO Goblin (GPT 5.6 Sol Ultra) via codex, working in ~/fermat.
**Provenance:** Fabian + Ultra Goblin Ulam session, 2026-08-13. The
universe added Ulam; three readings survived triage (detector budget,
transfer duality, lawful branching); this task executes the first
consequence.

## The core correction (supersedes the old frontier)

We do NOT need `ker Λ = 0` on all of H_rem, and we must NOT infer
`dim H_rem = 1` from the FIXED allocation (0,1). One scalar detector
cannot resolve a higher-dimensional Selmer space — and it does not
have to. The claim-relevant potential is the quotient

    Q_7a := H_rem / ker(gauge_7a)

which has dim ≤ 1 because the gauge is scalar-valued (rank–nullity —
this is Borsuk–Ulam's only lawful finite-field shadow here: a detector
budget, not a topology import). W4's one reflected bit is therefore
dimensionally sufficient for the one-bit question 7a — PROVIDED
arithmetic proves it reads this same quotient. The weakest sufficient
comparison, and the new frontier, is:

    wildReading h_F = 0  ⟹  gauge_7a h_F = 0

(preferred stronger form: gauge_7a = u · λ_wild, u a unit, on Q_7a or
merely on the Fermat-produced subspace). No ambient potential is
erased: ker gauge_7a stays retained, unresolved, in the ledger.

The campaign sentence: Ulam sizes the question; reflection supplies
its coordinate; arithmetic reads it; reciprocity forces it to zero;
receipted descent repeats the completed cell.

## W0 — freeze the exact types (THIS SESSION'S GATE)

Work against the real objects; do not build parallel ones:

- the gauge chain: `gauge_eq_local_tate_pairing` (TateBridge.lean:457)
  and its consumer at TateBridge.lean:604 producing
  `pair.ledger.VandiverSevenA 0 1`;
- the detector: `wild_detector_faithful`,
  `eq_zero_of_wild_detector_faithful`,
  `wild_detector_faithful_of_finrank_one` (TateBridge.lean);
- the steering gauge: `gaugeReading827` (GaugeSteering827.lean:182);
- the verdict surface: `fixedPointedReadoutOfFourierSeating_pullback`,
  `fixedGainAllocation_of_seating`, `no_transverseDirection_of_seating`,
  `fixedGauge_preimage_independent_of_fourierSeating`
  (TransversalityVerdict827.lean);
- the duality that W0 must AUDIT BEFORE BUILDING:
  `rhoDual_pullback_of_silence`, `jointDual_pullback`,
  `reading_preimage_independent`,
  `focusConormalClass_eq_zero_iff_fixed` (SteeringFiber.lean). The
  fixed pullback law λ|ker ρ = 0 ↔ λ = ρ*λ̄ likely already exists
  there — if so, EXPORT a dependency bridge (`#guard_depends_on`),
  do not re-derive.

Prove/confirm, in order:

1. **Gauge linearity.** The 7a gauge (the r₀+58r₁ reading) is linear
   over F₅₉, or its vacuum offset is zero. Name the theorem.
2. **Gauge ↔ relation.** `gauge_7a h_F = 0 ↔ Relation7a` — the ⟹
   direction exists (TateBridge:604 chain); confirm it and state
   precisely what the converse would need if absent. The weakest
   sufficient program only consumes the ⟹ direction.
3. **Carrier identity.** W4's reflected bit and the local Tate pairing
   (`pair_59`) inhabit the same carrier, or construct the explicit
   identification. Do NOT paper over a carrier mismatch with a
   dimension count.
4. **Descent.** The FIXED functional descends to Q_7a — seat it via
   the SteeringFiber pullback law on the quotient by ker gauge_7a.
   Define `Q_7a` and prove `finrank ≤ 1` (rank–nullity on a
   scalar-valued map — this is the detector-budget theorem
   instantiated, nothing topological).
5. **Re-seat the consumers.** Every consumer of
   `wild_detector_faithful` gets a quotient-form sibling that only
   demands faithfulness ON Q_7a (equivalently: the comparison
   implication). Mark the global interface as sufficient-but-not-
   necessary in doc comments. DO NOT delete it — retained conversion,
   not deletion.
6. **BOUNDARY-MAP.md.** Restate the frontier: it is now the three
   arithmetic interfaces of the comparison program — (a) exact-pair
   tame silence ⟨h_F, y*⟩_v = 0 for v ≠ 59 including 827, (b) an
   actual global reciprocity producer Σ_v ⟨h_F, y*⟩_v = 0, (c) the
   character-seating comparison gauge_7a = u·λ_wild via a
   one-dimensional equivariant Hom-space. `ker Λ = 0` is demoted to
   a historical sufficient condition.

**STOP CONDITION (binding):** if the verdict architecture supplies
only a dimension count / allocation numbers and NOT an actual dual
class or functional y*, then W0's deliverable is the typed obstruction
probe naming exactly the object W1 needs — same discipline as
TransformerProbe. Do not fabricate a functional from a count.

## If and only if W0 closes green: Lane 1 (reflected carrier)

Realize the canonical reflected dual class y* (or equivalent
functional), normalized through the 827 incidence. Prove
representative independence and the fixed pullback law for it. Keep
strictly separate: the NORMALIZATION of y* at 827 (may be 1) versus
the local PAIRING ⟨h_F, y*⟩ at 827 (may be 0) — these are different
numbers and conflating them is the named failure mode. Lanes 2–4
(tame silence, reciprocity producer, comparison seating) are NOT this
session's scope; leave typed interfaces where they will plug in.

## Explicit refusals (binding, from the Ulam triage)

- Do not infer global detector injectivity from one reflected bit.
- Do not infer dim H_rem = 1 from allocation (0,1).
- Do not erase ker gauge_7a when only the gauge has vanished.
- Do not import literal topological Borsuk–Ulam over F₅₉.
- Do not recurse through reflection: τ² = 1 is the proven period-two
  livelock (g = 2), never a descent.
- Do not replace universal termination with probabilistic extinction.
- Do not compute a Vostokov scalar before the structural
  proportionality route fails.
- Do not claim unconditional 7a while reciprocity remains an
  interface.
- Do not use H(H(C)) with the induced zero differential anywhere;
  depth transport is exact-couple/Bockstein or nothing.

## House rules (unchanged, binding)

PREDICTIONS entry first (where the carrier identity fights, whether
the SteeringFiber export suffices or a new quotient lemma is needed,
committed guess on the STOP condition firing). FINDINGS at discovery.
Generic core over p where a statement allows it; 59/827 only in the
instance layer. Verification.lean guards + `#guard_depends_on` for
every public theorem. Standalone green cones; no root build; ps
before heavy builds. Truthful commits. The tree contains UNTRACKED
scratch from a parallel exploration (Credit/*Probe.lean, FiveHundred
EightySeven/, OneThousandEightHundredThirtyOne/, TwelveThousandSix
HundredThirteen/, *-run.log) — do not touch, import, build, or delete
any of it, and do not disturb the running codex process on pts/6.

— Fable (reviewer), on behalf of Fabian, 2026-08-13
