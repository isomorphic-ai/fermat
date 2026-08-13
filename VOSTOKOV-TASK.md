# TASK VOSTOKOV — the wild reading at 59, or its exact residual core

**TruthSeed:** `fermat-7a:wild-symbol-extends-artin-hasse-or-names-its-residue`
**For:** PRO Goblin (GPT 5.6 Sol Ultra) via codex, working in ~/fermat.
**Provenance:** Fabian's directive 2026-08-13 ("Let's add VOSTOKOV!"),
after Ulam W1 isolated the single missing arithmetic producer.

## Standing-order update

The old refusal "do not compute a Vostokov scalar before the
structural proportionality route fails" is LIFTED BY FABIAN for the
localization producer only: the wild 59-local reading itself is now
in scope. It remains binding for the comparison lane — the gauge/wild
seating stays the processed-range equivalence im G ≃ im Λ; no scalar
is ever the invariant there.

## Target

Inhabit, or reduce to a strictly smaller named arithmetic core:

    ReflectedWildLocalizationAt59   (UlamReadout827.lean:169)

whose four fields are: an injective IntegralPadicGroupAlgebra-linear
inclusion oldToQRelaxed; the reading
readingAt59 : SelmerChi →+ (QRelaxedReflectedDual827 … →+ ZMod 59);
the adjoint law readingAt59 (a • x) y = readingAt59 x (hash ω a • y);
and agreement with the existing wild.reading on the included old
carrier. Its two consumers (toWildLocalInterface,
toReflectedWildCarrierExtension827) are already built — supplying the
structure unlocks W1 step 4 with no further wiring.

"Reduce" has a precise meaning here, the same discipline as every
stop before: if full inhabitation is out of reach, the deliverable is
a NAMED structure strictly smaller than the current hole — e.g. only
the residue-formula core, or only the missing series infrastructure —
together with a constructor showing named-core ⟹
ReflectedWildLocalizationAt59. The frontier must strictly shrink and
the reduction must be a theorem, not a comment.

## The tree's own plan — follow it in order

V1 — COVERAGE FIRST (the FactorDecomposition middle path). The
NEEDS-VOSTOKOV verdict (campaign_formulaBudget_eq_needsVostokov,
ArtinHasseInventory.lean:233) is a coverage audit: the Artin–Hasse
decompositions cover part of campaignInventory and the wild formula
budget is charged for the rest. Extend
NormalizedStateFactorArtinHasseDecomposition (the named discharge
interface at :171): decompose each uncovered WildClassKind into an
Artin–Hasse-covered factor times an explicit residual factor. If the
whole campaign inventory decomposes with trivial residual, the
verdict upgrades and Vostokov's series may not even be needed —
check this FIRST, cheaply, before any series work. Commit the
upgraded budget theorem if it holds; commit the exact residual
inventory if it does not.

V2 — THE SYMBOL ON THE RESIDUAL. For whatever residual V1 leaves,
build the wild pairing as a typed object with its defining laws, in
the TameSymbol house style (explicit, integral, over the 59-adics):
bilinearity/additivity in the shape readingAt59 needs; Galois
equivariance strong enough to yield the adjoint law through hash ω;
compatibility on the Artin–Hasse-covered part with the already-banked
classes (calibration, not re-derivation); Steinberg/norm-residue laws
only insofar as downstream consumers (tame silence is already inside
WildLocalInterface; reciprocity stays an interface) will need them —
name what you skip. Where the classical construction needs
infrastructure Mathlib lacks (Witt vectors are present; check what
of formal residues / power-series calculus over PadicInt is usable),
build the minimal generic piece in the route-neutral core or name it
as the reduced hole per the Target clause.

V3 — LOCALIZE. Assemble readingAt59 from the V1+V2 pairing via the
59-place localization, prove the adjoint law from equivariance, prove
agreement with wild.reading on the old carrier, package the
structure, and let the two existing consumers fire. Then compile the
conditional cascade as far as it now reaches: with
SelectedWildLawfulness827 and the kernel comparison still open, state
exactly which hypotheses of the W1 conditional endpoint are now
DISCHARGED and which remain, in FINDINGS and BOUNDARY-MAP.

## Refusals (binding)

- All ULAM/READOUT refusals remain in force except the one lifted
  above; in particular: no unconditional 7a, reciprocity stays an
  interface, ker G is never erased, the fiber is never collapsed.
- No axioms, no `sorry`, no fabricated pairing values: every value of
  the symbol must come from a definition, a calibration against the
  banked Artin–Hasse classes, or a named interface.
- Do not re-derive the tame symbol or the Artin–Hasse classes —
  consume them (`#guard_depends_on`).
- Do not identify the strict and relaxed carriers by an equivalence
  (the W0 lesson stands); the inclusion is a map with an injectivity
  receipt, nothing more.
- If V1 shows the residual is empty, do NOT build series machinery
  anyway — bank the upgrade and go straight to V3.

## House rules (unchanged, binding)

PREDICTIONS entry first, with committed guesses: does the V1 coverage
upgrade close (yes/no); if not, how many WildClassKind residuals
remain; does V3 close this session or end at a reduced named core.
FINDINGS at discovery. Generic core over p where statements allow;
59/827 only in the instance layer. Verification.lean guards +
`#guard_depends_on` for every public theorem; grep gates extended to
new modules; no-splitting audit; standalone green cones; no root
build; ps before heavy builds. Truthful commits. The untracked
parallel-session scratch (Credit/*Probe.lean,
FiveHundredEightySeven/, OneThousandEightHundredThirtyOne/,
TwelveThousandSixHundredThirteen/, *-run.log) stays untouched; the
pts/6 codex process stays undisturbed.

— Fable (reviewer), on behalf of Fabian, 2026-08-13
