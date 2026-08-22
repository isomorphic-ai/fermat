# TASK VOSTOKOV-CORE — two shapes need less than all of Vostokov

**TruthSeed:** `fermat-7a:two-shapes-need-less-than-all-of-vostokov`
**For:** PRO Goblin (GPT 5.6 Sol Ultra), persistent session, ~/fermat.
**Provenance:** Fabian's continue-order 2026-08-17. This is also the
framework's own test case: if the fiber/quotient discipline lets the
two-shape residual bypass most of Vostokov's generality, the
conservation architecture has earned its first arithmetic keep.

## Target

Inhabit the three fields of `ReflectedWildKummerCoreAt59`
(VostokovLocalization59.lean), whose compiled constructor
`toReflectedWildLocalizationAt59` then fires the entire W1 step-4
chain with no further wiring:

1. the representative bilinear wild Kummer pairing at 59;
2. `ReflectedEmptySupportLanding827` (the eigenspace landing);
3. calibration against the banked `wild.reading` on the old carrier.

## Strategy — cheapest sufficient formula, in this order

C1 — SHAPE AUDIT FIRST. The V1 residual is exactly two input kinds:
`statewiseSelmerLift` and `transverseDetectorComponent`
(`campaignResidualInventory_eq`). Before any formula work, compute
what these two shapes actually are as Kummer classes: their
representatives, and their position relative to the banked
`artinHasseKummerSubgroup`, the zeta/fixed-denominator classes, and
the generated-unit classes in ArtinHasseInventory.lean. Committed
guess required: do both shapes reduce to Artin–Hasse-covered classes
times a small explicit extension, or does one genuinely escape?

C2 — FORMULA TIER LADDER. Take the cheapest tier that covers what C1
found, and STOP there:
  (a) banked Artin–Hasse special values alone (if C1 shows coverage
      was under-counted, bank the upgrade theorem and skip ahead);
  (b) classical Artin–Hasse 1928 explicit formulas for the pairings
      (ζ, u) and (π, u) on principal units, specialized to the two
      shapes — this needs only finite truncations of the 59-adic
      logarithm on principal units (convergence is elementary there),
      not the general Vostokov series;
  (c) Iwasawa-style extension where (b)'s hypotheses fail;
  (d) full Vostokov/Brückner series — ONLY if C1 proves both cheaper
      tiers structurally insufficient, and then the deliverable is a
      REDUCED NAMED CORE (the minimal series lemma set) with a
      constructor theorem, not the whole formalization.
Where a tier needs infrastructure Mathlib lacks (p-adic log on
principal units exists — check `PadicInt` and `Polynomial`/power
series APIs first; formal residues likely absent), build the minimal
generic piece in the route-neutral core or reduce by theorem.

C3 — LANDING + CALIBRATION. Field 2 is module algebra against the
character projectors; field 3 must be a theorem equating the new
pairing with `wild.reading` on the included old carrier — calibration
is NEVER a definition.

C4 — FIRE AND RECONCILE. If the core inhabits: apply the constructor,
let the W1 consumers fire, and record in FINDINGS + BOUNDARY-MAP
exactly which premises of the conditional endpoint are now DISCHARGED
(localization, carrier extension) and which remain (lawfulness,
gauge seating, kernel comparison, reciprocity, fiber member). Append
the session as a new row to notes/CONSERVATION-AUDIT.md in the established
row format (input / processed with receipt / conserved / axis /
audit), and mark row 24's open cell accordingly. If the core does NOT
inhabit, the reduced named core per C2(d) is the deliverable and gets
the same audit-row treatment.

## Refusals (binding)

- All standing refusals (ULAM/READOUT/VOSTOKOV) remain in force:
  no unconditional 7a; reciprocity stays an interface; ker G never
  erased; the fiber never collapsed; no axioms, no sorry.
- No fabricated pairing values: every value from a definition on
  representatives, a banked calibration, or a named interface.
- Do not build tier (d) machinery while a cheaper tier is unrefuted —
  the refutation must be recorded (a finding), not assumed.
- Do not weaken bilinearity/equivariance to make a tier fit; a tier
  that fits only a weakened law is insufficient by definition.

## House rules (unchanged, binding)

PREDICTIONS entry first, committed guesses: (i) C1 outcome per shape,
(ii) the tier that closes, (iii) core inhabited this session yes/no.
FINDINGS at discovery. Generic over p where statements allow; 59/827
only in the instance layer. Verification.lean guards +
`#guard_depends_on` for every public theorem; grep gates; no-splitting
audit; standalone green cones; no root build; ps before heavy builds.
Truthful commits, one concern per commit. Untracked parallel-session
scratch stays untouched.

— Fable (reviewer), on behalf of Fabian, 2026-08-17
