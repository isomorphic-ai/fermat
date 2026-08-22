# TASK N4-CONSERVATION — prove FLT(4) strictly via the conservation law

**TruthSeed:** `fermat-n4:balance-powers-drain`
**For:** PRO Goblin (ultra) via codex, in ~/fermat.
**Predecessors:** Fermat/Exponents/Two/PythagorasConservation.lean (BALANCE mode),
Fermat/Exponents/Three/Conservation/ (DRAIN mode, Eisenstein charge). This rung:
n=4 as drain over ℤ itself — with the n=2 balance ledger as the engine.

## The conservation structure (spine mandatory, realization yours)

1. **The charge:** on ℤ, for the STRONGER auxiliary equation
   x⁴ + y⁴ = z² (Fermat's own strengthening), charge := z.natAbs (or
   z²). No ring extension: n=4 is the drain mode native to ℤ.
2. **The balance engine:** the Pythagorean parametrization
   (m²−n², 2mn, m²+n²) is n=2's CLOSED LEDGER reused as the descent's
   transformation — the balance rung powering the drain rung. Make
   this composition explicit in statement/docstring: the coupling-free
   decomposition of a right triangle is what exposes the smaller
   solution. Mathlib's PythagoreanTriple machinery is a FREE import
   (not FLT-derived); connect it narratively to
   Fermat.Two.PythagorasConservation.
3. **The drain step:** from a primitive solution of x⁴+y⁴=z², produce
   a solution with STRICTLY SMALLER charge (the classical coprime
   double-descent), stated as a charged-descent lemma.
4. **The floor:** REUSE the conservation floor from n=3
   (noInfinitePositiveChargeDrain) — hoist it to a shared location
   (e.g. Fermat/Experiments/Conservation/Floor.lean) imported by BOTH Three and
   Four if that keeps cones clean, or import Three's module. The floor
   is mode-generic; do not duplicate it.
5. **Assemble:** `Fermat.Four.holdsAt_four_conservation :
   Fermat.HoldsAt 4`, via the stronger z² statement, closed by
   drain + floor (impossible-debt).

## Import discipline (the n3 rule, verbatim)

- FREE in bounded roles (listed in docstring): Mathlib's Pythagorean
  triple machinery, Int/Nat parity+coprimality+squares lemmas, general
  algebra.
- **FORBIDDEN: Mathlib's FLT-Four module (`fermatLastTheoremFour`,
  `not_fermat_42` etc.) or anything proven from it.** Reconstruction
  with credit is the n3 pattern: if you adapt the Mathlib argument,
  credit its authors in the header and prove your cone clean
  (forbidden-name-unknown test, as you did for n3).
- The pre-existing repo-wide manifest drift (flt-regular pin) is NOT
  yours to fix; keep the N4 cone independent of it as N3's is.

## Gates
PREDICTIONS first (committed before work); FINDINGS at discovery;
commit early and often; N4-cone lake build green; #print axioms
(standard trio) on every public theorem; forbidden-name-unknown test
in the verification record; no sorry/admit/axiom; whitespace clean.

Deliverable: the third machine-checked rung of proof-as-conservation —
and the first COMPOSITION of modes (balance engine inside drain).
— Fable (reviewer), on behalf of Fabian, 2026-07-28
