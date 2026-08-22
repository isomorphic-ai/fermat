# TASK TAME-SYMBOLS — Stage 1: the tame layer and the Selmer legs

**TruthSeed:** `fermat-tame:the-pairing-is-the-hilbert-symbol`
**For:** PRO Goblin (GPT 5.6 Sol Ultra) via codex, working in ~/fermat.
**Authorization (Fabian, 2026-08-06):** Stage 1 of the Tier-3 explicit
route from the CFT feasibility report. Because mu_p lies in K, the
local pairing IS the degree-p Hilbert symbol and no cohomology is
forced. This session builds the TAME layer and seats the Selmer legs.
NO unconditional 7a, NO endpoint, NO transformer. The wild place at p
and the global product formula are OUT of scope (later stages).

## W1 — the tame Hilbert symbol (generic, route-neutral)

New module (e.g. Fermat/Experiments/Conservation/TameSymbol.lean): for a place v
with residue characteristic NOT p and residue field of size q with
p | q - 1, the explicit tame symbol
  (a,b)_v = omega( (-1)^{v(a)v(b)} * a^{v(b)} / b^{v(a)} )^{(q-1)/p}
valued in ZMod p (via a primitive root / the Teichmuller-style
character of the residue field). Prove: bilinearity, antisymmetry,
Steinberg ((a, 1-a) = 0 where defined), Galois equivariance (the
adjoint law shape against InvolutiveBase where expressible), and the
silence law: v(a) = 0 and v(b) = 0 implies (a,b)_v = 0 — BOTH-UNITS
SILENCE, the workhorse. Source discipline: Fesenko-Vostokov Ch. IV
para 5 / Neukirch V.3, credited in the header; cohomology-free by
construction. Where Mathlib residue-field machinery is thin, build the
minimal generic lemmas (they are Mathlib-welcome pieces; note them).

## W2 — seat the Selmer legs on Mathlib's own carrier

Instantiate the stage's SelmerChi / reflected-dual legs on
IsDedekindDomain.HeightOneSpectrum.selmerGroup eigenspaces (at-pin
Mathlib — the sleeper asset; we vendored its exact-sequence extension
already). The chi-eigenspace via the Delta-action from InvolutiveBase;
document any gap between the abstract carrier the stage expects and
the concrete selmerGroup subtype as named glue lemmas.

## W3 — discharge the tame rows

With W1+W2: realize PlaceIndexedLocalPairing at tame places (the
readings ARE tame symbols of the seated classes); discharge the tame
rows of the bank_silences_other_places audit and the
outside_two_readings support condition by valuation bookkeeping
(Selmer elements are unramified outside the defining set - the
both-units silence law does the rest). Update BOUNDARY-MAP: interface
1 splits into PROVEN-at-tame-places + INTERFACE-at-59; the audit
table gains its tame verdicts. The orthogonality guard stays explicit
where it still binds.

## Conventions and guards

Mirror FLT-project statement conventions where objects overlap (their
PRs 1110/1105 own the abstract statements; our explicit symbols must
be trivially alignable later - note the correspondence in FINDINGS).
PREDICTIONS first (where residue-field arithmetic fights; whether the
Steinberg relation is needed this stage or deferrable). FINDINGS at
discovery. All guards and the full verification stay green; new
guards per public theorem; standard trio; generic over p, 59 only in
instances; ps first (a second session runs in ~/FLT). Truthful
commits.

— Fable (reviewer), on behalf of Fabian, 2026-08-06
