# TASK READOUT — conserve the fiber; process the quotient (Ulam W1)

**TruthSeed:** `fermat-7a:proof-processes-a-quotient-and-transports-the-fiber`
**For:** PRO Goblin (GPT 5.6 Sol Ultra) via codex, working in ~/fermat.
**Provenance:** Fabian's observation conservation law, 2026-08-13,
correcting the ULAM W0 semantics and unifying the three W0 obstruction
structures into one exact object. Supersedes the W0 reading of Q_7a.

## Semantic correction (binding)

Q_7a = H/ker G is NOT the unknown potential. It is the part the 7a
observation has PROCESSED. The still-unknown quantity is ker G, and it
must remain present in every statement. For any readout f : V → W,
retain the exact sequence

    0 → ker f → V → im f → 0

with [V] = [ker f] + [im f] (K_0; dimension as numerical shadow), no
canonical splitting ever. Compact law: CONSERVE THE FIBER; PROCESS THE
QUOTIENT. Second-readout law: for g after f, only g|_{ker f} is new;
the next row is 0 → ker f ∩ ker g → ker f → g(ker f) → 0, with
g(ker f) = 0 ↔ FIXED (g factors through the processed coordinate) and
g(ker f) ≠ 0 ↔ STEERABLE (new potential processed; ExteriorTransfer
measures the volume gain). This is the exact algebraic form of
"energy flows where attention goes": attention selects g, agency
executes g|_{ker f}, the kernel retains what remains possible.

Mega-mode sentence, to appear in the module docstring: a proof does
not eliminate the unknown; it processes one quotient and transports
the conserved fiber forward.

## Part A — the generic abstraction (route-neutral core)

New module `Fermat/Conservation/ReadoutLedger.lean` (name
`ConservedReadoutComparison` acceptable for the two-readout part),
generic over a field K and K-modules, with generic theorems for:

    unknown        = ker readout
    processed      = range readout
    secondUnknown  = ker f ⊓ ker g
    newProcessed   = range (g restricted to ker f)
    fixed          ↔ newProcessed = ⊥
    sameUnknown    ↔ ker f = ker g ↔ processed ranges canonically
                     equivalent: Φ : im f ≃ im g, Φ(f h) = g(h)

The sameUnknown equivalence is the heart: two readouts with equal
kernels process exactly the same potential while conserving exactly
the same unknown; after bases on one-dimensional images this appears
as g = u·f with u ≠ 0 — unit proportionality is the COORDINATE
SHADOW, the range equivalence is the INVARIANT. Also the affine-fiber
lemma: if q : R → K is a nonzero scalar readout then the normalized
fiber q⁻¹(1) = y₀ + ker q is nonempty (choose z with q z ≠ 0, take
y = (q z)⁻¹ • z) — this constructs one receipted probe WITHOUT
identifying meter with probe and WITHOUT deleting the rest of the
fiber. And the rank-one factorization lemma: if B : H × R → K is
bilinear with ker q ≤ ker (B h ·) for the selected h, then B(h, ·)
is constant on the fiber and there is a unique Λ(h) with
B(h, y) = Λ(h)·q(y) — i.e. B = Λ ⊗ q on the selected carriers.

Audit before building: SteeringFiber/FocusConormal already carry the
two-readout kernel algebra (K_T, jointObservation, fixed iff) —
ReadoutLedger must CONSUME or bridge those (`#guard_depends_on`), not
re-derive them. Where a statement is a repackaging, prove it BY the
existing theorem and record the bridge.

## Part B — the 827 instantiation, in Fabian's order

Targets in `UlamTypeFreeze.lean` / a new instance module. R = the
q-relaxed reflected carrier, q = `reflectedBoundaryFunctional827`.

1. Prove `reflectedBoundaryFunctional827 ≠ 0` (or record the exact
   arithmetic input this needs as a typed interface if it is not yet
   derivable — do not fabricate).
2. Prove it is exactly the seated 827-local coordinate (identify with
   the Fourier/incidence seating already banked).
3. Retain the fiber as the public carrier:
       def NormalizedReflectedFiber827 :=
         { y : R // reflectedBoundaryFunctional827 … y = 1 }
       theorem normalizedReflectedFiber827_nonempty : Nonempty …
   A chosen class is only a RECEIPT; `NormalizedReflectedClass827`
   may be inhabited locally from the fiber but must not become the
   public interface.
4. Build the extended wild pairing (the
   `ReflectedWildCarrierExtension827` hole) from LOCALIZATION AT 59,
   never from a chosen complement.
5. Prove the lawfulness inclusion ker q ≤ ker (B₅₉ h_F, ·) — for h_F
   or the selected Fermat subcarrier first; full H later. If this
   inclusion FAILS, that is a FINDING, not a failure: B₅₉ processes an
   additional reflected degree of freedom, and the architecture must
   retain that new bit (STEERABLE row) rather than pretend the
   reading is canonical. Record and stop that branch.
6. Extract the canonical factorization B₅₉ = Λ ⊗ q via Part A.
7. Replace `SevenAGaugeSeating`'s arbitrary scalar readout with the
   processed-range equivalence: G the genuine class-valued 7a gauge,
   prove/interface ker G = ker Λ and export Φ : im G ≃ im Λ,
   Φ(G h) = Λ(h). The two inclusions have exact meanings — record
   them separately: ker Λ ≤ ker G (wild processes at least the 7a
   question), ker G ≤ ker Λ (wild uses nothing beyond it, so it
   descends to Q_7a). Whichever direction needs arithmetic not yet in
   the tree becomes a NAMED typed interface, not an axiom.
8. Depth audit: prove 59 • im G = 0 (should follow from
   59[I] = 59[J] = 0 for the root-ideal classes), so 58[J] = -[J]
   holds in the actual gauge carrier and fixed-59 W1 is safe. If the
   gauge lives in a deeper 59^n carrier, the conserved next-layer
   potential after r₀ + 58r₁ = (r₀ - r₁) + 59r₁ with r₀ - r₁ = 59c
   is c + r₁, NOT merely r₁ — route it through the existing
   BocksteinPowerRootReceiptObservation; mod-59 zero means "lowest
   layer processed," never "object deleted."

Steps 9 (tame silence + reciprocity execution) and 10 (routing the
surviving kernel through class→unit→root) are NOT this session's
scope: leave the typed interfaces where they plug in. The endpoint
chain (any y in the fiber + tame silence + reciprocity ⟹ B₅₉(h_F,y)=0
⟹ Λ(h_F)=0 ⟹ G(h_F)=0 ⟹ 7a via the banked equivalence) may be
compiled as a CONDITIONAL master theorem consuming those interfaces —
nothing unconditional. Nothing stronger is ever claimed: h_F need not
vanish, Selmer need not vanish, ker G is not erased; only the 7a
component is processed and certified.

## Refusals (all W0 refusals remain binding, plus)

- Do not collapse the fiber to a privileged y* in any public carrier.
- Do not build the pairing extension from a chosen complement.
- Do not treat failure of the kernel inclusion (step 5) as failure —
  it is a retained new bit; record it.
- Do not scalarize the gauge through a noncanonical readout when the
  range equivalence is available.
- Do not erase ker G anywhere; every quotient statement carries its
  exact sequence.
- No unconditional 7a; reciprocity remains an interface.

## House rules (unchanged, binding)

PREDICTIONS entry first (committed guesses: does q ≠ 0 close from the
banked seating or need a new interface; does step 5 hold at h_F; does
59 • im G = 0 close). FINDINGS at discovery. Generic core in Part A
over any p/field where possible; 59/827 only in the instance layer.
Verification.lean guards + `#guard_depends_on` for every public
theorem; grep gates extended to the new modules; no-splitting audit.
Standalone green cones; no root build; ps before heavy builds.
Truthful commits. The untracked parallel-session scratch
(Credit/*Probe.lean, FiveHundredEightySeven/, OneThousandEightHundred
ThirtyOne/, TwelveThousandSixHundredThirteen/, *-run.log) stays
untouched, and the pts/6 codex process stays undisturbed.

— Fable (reviewer), on behalf of Fabian, 2026-08-13
