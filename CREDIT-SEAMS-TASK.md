# TASK CREDIT-SEAMS — fill C2, C4-bounded, C3; the transformer waits

**TruthSeed:** `fermat-credit:four-holes-three-yours`
**For:** PRO Goblin (GPT 5.6 Sol Ultra) via codex, working in ~/fermat.
**Starting point:** your own seam localization (HEAD ad51517,
`Fermat/FiftyNine/Conservation/FINDINGS.md`). The ladder C1–C3 and the
generated N59 instantiation are accepted and audited (endpoint absent,
forbidden names unknown, 30+37 theorems at standard trio — verified
independently). This session fills the seams you named, in order:

## Seam 1 — C2: `Credit.CapacityCertificateGoal hζ`

Prove `(generatedSubledger hζ).FiniteIndex ∧ ¬59 ∣ capacityIndex hζ`.
The residue-functional realization is the work: connect the generated
edge units to their images mod the tower prime 827 (generator
671 = 2^(2·7), orderOf = 59 — already kernel-checked), realize the
28×28 evaluation as a genuine group homomorphism argument, and derive
finite index + index prime to 59 from nonsingularity. Reconstruction of
the needed linear algebra in generated form is expected (credited, the
N3 pattern); importing the forbidden `Fermat.Irregular` realization is
not. The lamp reading may help structure it: mod 827, x^59 − 1 splits
completely — the units' images are 59th roots of unity made concrete;
nonsingularity says the unfolding has no crease.

## Seam 2 — C4 bounded: `Credit.BoundedSinnottBridge hζ`

Prove `¬59 ∣ capacityIndex hζ → ¬59 ∣ classNumber(maximalRealSubfield K)`
at conductor 59 ONLY. Do not build Sinnott in generality. The classical
content is the circular-unit index formula ([E:C] = h⁺) specialized to
prime conductor — Kummer's own case. If Mathlib's
`NumberField.classNumber`/units API cannot yet carry the full identity,
a one-directional inequality suffices for the bridge as stated —
document exactly which direction you prove and why it is the one the
endpoint consumes. If even that requires machinery you must copy
line-for-line from the forbidden namespaces, stop and record the
finding (rule 6).

## Seam 3 — C3: `Credit.DeepCoefficientForcing59 hζ`

The depth-118 congruence must yield Vandiver's coefficient-wise cube
divisibilities for every primitive generated relation. This is
Vandiver's Lemma II calculation in generated form — credit it by name.
NOTE: `NoBernoulliCubeObstruction59` (the finite 28-index Bernoulli
check) is being computed IN PARALLEL by Fable on the sweep
infrastructure; treat it as an incoming certified hypothesis — do NOT
spend session time computing Bernoulli numerators. If your proof shape
needs the finite facts stated differently (e.g. mod 59³ residues rather
than non-divisibility), say so in FINDINGS.md immediately so the
computation can match your interface.

## Out of scope this session

The stock/credit transformer (strict-successor from a primitive
solution) stays out until the three seams above are rigid — the weld
comes last. C5–C7 remain named-not-built. No endpoint assembly unless
all three seams actually close, in which case assemble
`Fermat.FiftyNine.holdsAt_fiftyNine_conservation` and treat its audit
as the session's crown: axioms, forbidden names, and the full guard
suite.

## House rules (unchanged, binding)

PREDICTIONS entry first (append to the existing Credit PREDICTIONS.md:
which seam falls first, where each resists); FINDINGS.md at discovery
time; Verification.lean guards extended for every new public theorem;
standard trio or less; standalone green cones only (root build stays
broken by pre-existing flt-regular drift — not yours); ps before heavy
builds; truthful commit messages; obstruction maps are honorable
deliverables.

— Fable (reviewer), on behalf of Fabian, 2026-07-29
