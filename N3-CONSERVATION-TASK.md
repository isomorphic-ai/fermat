# TASK N3-CONSERVATION — prove FLT(3) strictly via the conservation law

**TruthSeed:** `fermat-n3:drain-mode`
**For:** PRO Goblin (ultra) via codex, in ~/fermat.
**Predecessor:** Fermat/Two/PythagorasConservation.lean — n=2 as the
BALANCE mode (empty coupling ⟹ additive ledger; integer ledger closes
at 3²+4²=5²). Your task is n=3 as the DRAIN mode: the integer ledger
provably cannot close, shown by conservation accounting.

## The conservation structure to realize (the spine is mandatory;
## realization details are yours)

1. **The charge:** on ℤ[ζ₃] (Eisenstein integers), charge := the norm
   N(x + yζ₃) = x² − xy + y². Prove its MULTIPLICATIVE conservation
   (N(uv) = N(u)N(v)) as the n=3 analogue of n=2's isometry invariance
   — the charge conserved under the ring's multiplicative symmetry.
2. **The ledger identity:** a³ + b³ = (a + b) · N(a + bζ₃) over ℤ —
   the Fermat equation at 3 IS a ledger equation: c³ = (a+b)·charge.
3. **The drain unit:** λ = 1 − ζ₃ with N(λ) = 3 — the quantum of
   descent. Each descent step transfers charge strictly downward.
4. **The drain theorem (mode 2 of the proof taxonomy):** formalize the
   floor — no infinite strictly-decreasing sequence of positive charges
   (well-foundedness as the conservation floor) — as a named, reusable
   lemma, then run Euler's descent through it: a hypothetical solution
   yields a smaller solution with strictly smaller charge; the floor
   forbids the infinite drain; contradiction (IMPOSSIBLE-DEBT close).
5. **Assemble:** `Fermat.Three.holdsAt_three_conservation :
   Fermat.HoldsAt 3`, proven through 1–4.

## Import discipline (bounded roles, listed)

- Mathlib's cyclotomic/Eisenstein ring machinery, unit/ideal lemmas,
  and general algebra: FREE, in bounded roles, each named in the
  module docstring.
- **FORBIDDEN: `fermatLastTheoremThree` / `Fermat.holdsAt_three` or
  any import that already contains FLT(3)** — citing the theorem to
  prove the theorem is decoration, not conservation. If a Mathlib
  intermediate you want is itself proven FROM FLT(3), treat it as
  forbidden too (check provenance).
- If full descent formalization exceeds the session: deliver the spine
  (1–4) proven + the descent step as the SINGLE named remaining lemma
  with its exact statement — honest statuses per rung, ladder-style.

## Gates
PREDICTIONS first (commit before work); FINDINGS at discovery; commit
early and often; full lake build; #print axioms (standard trio) on
every public theorem; no sorry/admit/axiom in delivered theorems;
whitespace clean. Work in Fermat/Three/, files under a Conservation
namespace/dir so the classical route stays untouched.

The deliverable either way: n=2 (balance) and n=3 (drain) as the first
two rungs of "proof as conservation" made machine-checked — the
commenters note's conjecture, instantiated.
— Fable (reviewer), on behalf of Fabian, 2026-07-27
