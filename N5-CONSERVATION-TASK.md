# TASK N5-CONSERVATION — prove FLT(5) strictly via the conservation law

**TruthSeed:** `fermat-n5:gauge-invariant-drain`
**For:** PRO Goblin (ultra) via codex, in ~/fermat.
**Predecessors:** Two/ (balance), Three/Conservation (drain, finite unit
group), Four/Conservation (composition, shared floor). This rung's NEW
LESSON: drain with an INFINITE unit group — conservation modulo gauge.

## The conservation structure (spine mandatory)

1. **The charge:** the golden-ring norm on ℤ[φ] ⊂ ℚ(√5) (φ = (1+√5)/2)
   — multiplicative conservation N(uv)=N(u)N(v), and the NEW invariance:
   the unit group is infinite (Pell/φ-powers), units have norm ±1, so
   the charge is GAUGE-INVARIANT — the ledger quantity that survives
   the symmetry the ring imposes. State this as its own named theorem
   (charge_gauge_invariant): the n=5 lesson in one declaration.
2. **The ledger identity:** the quintic factorization
   a⁵+b⁵ = (a+b)·Q(a,b) with Q expressed through the ℚ(√5) norm form
   (ℚ(ζ₅) ⊃ ℚ(√5)) — the Fermat equation at 5 as a ledger equation.
3. **The drain quantum:** √5 (the ramified prime, N = 5) — the n=5
   analogue of λ = 1−ζ₃.
4. **The two-branch drain:** Dirichlet's case split (5 ∤ c and 5 | c)
   as two charged-descent lemmas, both draining the gauge-invariant
   charge strictly, both closed by the SHARED conservation floor
   (Fermat/Conservation/Floor — reuse, never duplicate).
5. **Assemble:** `Fermat.Five.holdsAt_five_conservation :
   Fermat.HoldsAt 5`.

## Import discipline (the established rule)

- FREE in bounded roles (listed): Mathlib's Zsqrtd / quadratic-ring /
  Pell-unit machinery, parity/coprimality/squares, general algebra.
- **FORBIDDEN: this repository's own classical Five route**
  (Fermat.Five.Dirichlet, Fermat.Five.Reduction, holdsAt_five — and
  anything proven from them). Mathlib contains no FLT(5), so the
  circularity risk is ENTIRELY in-repo this time: your clean cone must
  exclude your own earlier work. Reconstruction with credit per the n3
  pattern — credit the repository's Dirichlet formalization in the
  header, prove the cone clean with the forbidden-name-unknown test.
- Executable Verification.lean (the N4 pattern) is now REQUIRED, not
  optional: axiom audits + forbidden-name checks as tree artifacts.
- N5 cone independent of the flt-regular manifest drift, as before.

## Gates
PREDICTIONS first; FINDINGS at discovery; commit early and often;
N5-cone build green; standard axiom trio on every public theorem; no
sorry/admit/axiom; whitespace clean. Honest fallback pre-authorized:
if the two-branch descent exceeds the session, deliver the spine
(1–3) proven + each branch as a single named lemma with exact
statement and honest status.

Deliverable: the fourth rung — drain under infinite gauge — and the
conservation library's first contact with the unit-group weather that
Kummer's lemma, Vandiver, and the regulator all grew up in.
— Fable (reviewer), on behalf of Fabian, 2026-07-28
