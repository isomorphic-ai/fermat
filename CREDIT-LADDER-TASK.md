# TASK CREDIT-LADDER — the level-3 curriculum, and N59 composed at last

**TruthSeed:** `fermat-credit:without-a-generator-nothing-provides-credit`
**For:** PRO Goblin (GPT 5.6 Sol Ultra) via codex, working in ~/fermat.
**Locations:** `Fermat/Conservation/Credit/` (the ladder — route-neutral,
like the Floor) and `Fermat/FiftyNine/Conservation/` (the endpoint).
**Endpoint target:**
`Fermat.FiftyNine.holdsAt_fiftyNine_conservation : Fermat.HoldsAt 59`

## Why the previous N59 task failed, and why that failure was correct

Your obstruction map (c81e966 and FINDINGS) was right and is now doctrine:
the seven stock primitives cannot produce the credit column, and the
reason is a TYPE error, not a missing lemma. The state matrix has three
orthogonal levels:

- **flow**  = dQ/dt        — lives on *edges* (the descent maps),
- **stock** = ∫ flow       — lives on *nodes* (a charge vector; additive
  commutative-monoid law) — the n=1..7 ladder,
- **credit** = ∫ flow *banked across a yield* — lives on *node pairs*: a
  two-sided who-owes-whom **matrix** (debits and receivables are one
  matrix viewed from opposite sides; the level's law is semilattice
  merge, not addition).

You cannot build a bank out of flow and stock alone. Credit is its own
level and needs its own seven primitives.

## The level-3 principle (Fabian): credit objects are GENERATED

Levels 1 and 2 have closed forms (derivative, integral). A level-3
object is a **fixed point of self-reference** — a recursion with a
period, whose fixed point is a *generator*:

- `φ = 1 + 1/φ` — period 1; φ is the fundamental unit of ℚ(√5): the N5
  gauge rung re-read one level up, as the thing that generates the unit
  tower out of one self-referring equation.
- `√2 = 1 + 1/(1+√2)` — the Pell generator, same shape.
- General units: arbitrarily long periods; the limit of the principle is
  the endless period (the Iwasawa tower).

**Without a generator there is nothing that can provide credit.** A
regular prime's empty credit ledger is not "matrix = 0" as brute fact;
it is "no generator exists to fund any entry" (Kummer's lemma restated).
The regulator (N7) is the log-volume of what level 3 generates.

## The generation tower of 59

`59 = (4×7+1)×2+1`: the tower 7 → 29 → 59, each step "multiply, add the
seed 1". 29 is a Sophie Germain prime, 59 its safe prime. This tower IS
the credit ledger's anatomy:

- Gal(ℚ(ζ₅₉)⁺/ℚ) ≅ ℤ/29 — prime cyclic; all units and all repayment
  machinery live here. Unit rank 28 = 4×7.
- One level down, Gal(ℚ(ζ₂₉)/ℚ) ≅ ℤ/28 ≅ ℤ/4 × ℤ/7 — the completed
  stock ladder appears as a factor of the tower.
- The ×2 is the two-sided ledger: complex conjugation, plus/minus parts,
  debits/receivables. Each +1 is the generator seed.

## The credit ladder (approved table)

| rung | mode | classical identity | generated form |
|---|---|---|---|
| C1 | vacuum | Kummer's lemma (regular case) | no generator exists ⟹ credit matrix identically empty |
| C2 | balance | capacity | credit capacity = index of the generated sub-ledger (cyclotomic units η_a = (1−ζ^{g^a})/(1−ζ^{g^{a−1}}), the generator's orbit) |
| C3 | drain | Vandiver's Lemma II | repayment: every debt returns through the generator (deep congruence (1−ζ)^{2p} ∣ u − c^p forces u a p-th power) |
| C4 | composition | Sinnott / circular-unit index bridge | generated sub-ledgers compose across the tower; index ⟹ class-number statement |
| C5 | gauge | Herbrand–Ribet | the debt sits exactly in the Galois eigenspace named by the Bernoulli index — gauge decomposition of the matrix |
| C6 | fold | Leopoldt Spiegelung | plus/minus parts = the same matrix viewed from opposite sides |
| C7 | lattice/period | Iwasawa main conjecture layer | the endless-period recursion; char ideal = p-adic L |

## Phasing (this session)

- **Phase I — C1, C2, C3 as ladder rungs** in
  `Fermat/Conservation/Credit/`, each with the generative discipline
  below, each with its own PREDICTIONS/FINDINGS entries and audit
  surface. Small instantiating fields are welcome where they make a rung
  honest (φ and ℚ(√5) for the generator vocabulary — reuse the N5
  spine's arithmetic).
- **Phase II — the N59 endpoint**: instantiate C1–C3 at the 7→29→59
  tower and compose with the seven stock spines to prove
  `holdsAt_fiftyNine_conservation`. Pull C4 forward **only as far as the
  capacity bridge demands** (the index ⟹ class-number step your
  obstruction map identified); if C4-in-full is a campaign rather than a
  bridge, deliver the bounded bridge with its boundary listed and record
  the finding.
- **Phase III — C5, C6, C7**: NOT this session. Name them in FINDINGS
  where they knock; do not build them.

## The generative discipline (binding)

1. **Generated, not enumerated.** One generator plus the tower derives
   the 28×28 structure as the generator's orbit (4×7 structured by
   ℤ/4 × ℤ/7, doubled by conjugation, seeded by 1). Hand-instantiated
   opaque residue tables are stock-thinking and are rejected.
2. **Certificates check, they do not define.** The kernel-checked
   numbers (existing certificate data, reconstructed locally as needed —
   the credited N3 pattern) may VERIFY the generated object; the object's
   definition must come from the generator and the recursion.
3. **No unexplained seeds.** Attestation/lifting primes must be
   tower-generated and stated as such (the current certificate's 827 =
   2·59·7+1 is on the 7-tower — make that a stated property, not an
   accident). Any constant without a generation story is a finding.
4. **Two-sidedness is structural.** Wherever the ledger doubles (±,
   conjugation, debit/receivable), state it as the ×2 of the tower, one
   matrix read from opposite sides.

## Import boundary (unchanged, executable guards required)

FORBIDDEN in every cone (Verification.lean proves them *unknown*):
`Fermat.FiftyNine.GenericProof`, `.FirstCase`, `.GenericSecondCase`,
`.Folding`, `.GenericChannels`, `.GenericLemmaTwo`,
`Fermat.GenericIrregular.*`, `Fermat.Irregular.*`, `Fermat.Ladder.*`,
`Fermat.HoldsAt.mono_of_dvd` (import `Fermat.Statement.Basic` only).
Credited reconstruction in generated/ledger form is expected and
honorable; silent line-for-line re-derivation is not — when
reconstruction converges on a classical proof, credit it by name
(Kummer, Vandiver, Sinnott) in the header, as N3 credited Euler.

## House rules (fleet standard)

1. PREDICTIONS.md first (in Credit/), committed before any Lean: which
   rungs compose cleanly, where C4's bridge bites, where the generative
   discipline will hurt most.
2. FINDINGS.md at discovery time, newest first; deviations are findings.
   Commit early and often, truthful messages.
3. Executable Verification.lean per location: `#print axioms` on every
   public theorem (standard trio or less) + forbidden-name guards.
4. Standalone green cones only; do not attempt the root build
   (pre-existing flt-regular drift + exit-137 module; not yours to fix).
5. `ps` before heavy builds; the box is shared.
6. If the endpoint cannot close under this discipline, the obstruction
   map is again the deliverable — localized to a rung and a seam, with
   the same honesty as c81e966. No parameterized endpoint, no capacity
   overstated beyond what a proof proves.

## Success criteria

- C1–C3 compile as route-neutral ladder rungs with generative form,
  audited.
- `Fermat.FiftyNine.holdsAt_fiftyNine_conservation : Fermat.HoldsAt 59`
  compiles with standard trio, forbidden names unknown, composed from
  the stock spines + credit rungs; OR the next obstruction map, rung-
  and seam-localized.
- The credit ledger explicit in code: generator, orbit, capacity
  (index), repayment — named, not folklore.

— Fable (reviewer), on behalf of Fabian, 2026-07-29
