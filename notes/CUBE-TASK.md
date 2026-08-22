# TASK POWERROOT-CUBE — the naturality square test: is the gauge a defect?

**TruthSeed:** `fermat-cube:every-zero-is-exact-cancellation-or-a-retained-boundary`
**For:** PRO Goblin (GPT 5.6 Sol Ultra) via codex, working in ~/fermat.
**Provenance:** Fabian's higher-dimension intuition + PRO analysis + Sol
continuation. The archive's homological grading: Ledger = degree 0,
Transfer = degree 1, Heis/Area = degree 2, PowerRootObstruction = the
arithmetic Kummer square, reciprocity = arithmetic Stokes. Standing
rules: NO unconditional 7a, NO endpoint, NO transformer. The
deliverable of W3 is WHICH of four typed outcomes - all four are
results.

## W1 — PowerRootExactSequence

Vendor the generic power-root obstruction generator from our own
Mathlib branch (~/Mathlib branch power-root-obstruction, commits
4ea7450c8a + 889be7a3fe; provenance header with commit + SHA-256 as
always) into the route-neutral core, and present the arithmetic
instance as the TWO-TERM-COMPLEX view of the principal-ideal arrow
K^x -> FracIdeal(O_K): pi_1 = units (retained morphisms/receipts),
pi_0 = Cl (the component shadow), Selmer = the middle object carrying
both WITHOUT splitting. Encode the caution as a mechanical guard: no
theorem may consume a splitting Selmer ~ U/U^p x Cl[p]; the extension
data is a named object (the extension class), never silently trivial.

## W2 — PowerRootNaturality

Naturality of the obstruction sequence in the situation: for the three
cube directions - (a) the group-ring/Delta action (equivariance), (b)
reflection (the # involution / chi <-> chi*), (c) localization at a
place (global arrow to local arrow) - state and prove what is
genuinely provable that the induced maps commute with root/obstruction
(the generator's root_shift/root_mul are the engine). Where the local
carrier is missing in Mathlib (completions/local Selmer of the right
shape), the direction enters as a NAMED interface with its law - the
cube face exists even where its arithmetic filling waits. rho is
hereby re-specified: not guessed on the class group but REQUIRED to be
an equivariant action on the principal-ideal arrow preserving the
PowerRoot square - update LinkingInterfaces' summit statement
accordingly.

## W3 — GaugeAsNaturalityDefect59 (the decisive test)

Over the 59-torsion layer, r0 + 58*r1 = r0 - r1. Attempt to identify
  r0(x) = ell( obstruction_local (localize x) )
  r1(x) = ell( localize (obstruction_global x) )
so the gauge is the NATURALITY DEFECT of the square. Classify the
outcome - exactly one of four, each typed and each a result:
  1. The square commutes directly: 7a collapses to generic PowerRoot
     naturality (state what remains, if anything).
  2. It commutes only after summing local readings over places:
     reciprocity is precisely the missing 2-cell (the Stokes reading -
     wire to GlobalReciprocityLaw).
  3. The two sides fail to share a type until chi* and the Tate twist
     are inserted: that LOCATES the missing reflected-dual carrier
     (name it).
  4. The readings do not factor through the same obstruction: the
     wild arithmetic route is genuinely necessary (Stage 3 proceeds
     with this as its justification).
Also record the depth note: r0 + 58*r1 = (r0 - r1) + 59*r1 - the
surviving 59*r1 as a candidate Bockstein/PowerRoot receipt where layer
transport and the two-2s correspondence may meet; state it as a named
observation, not a theorem.

## House rules (binding)

PREDICTIONS first - including a COMMITTED GUESS which of the four
outcomes W3 lands on. FINDINGS at discovery. All guards, grep gates,
and the full verification stay green; the no-splitting guard is new
and mechanical; new guards per public theorem; standard trio; generic
over p, 59 in instances. ps first. Truthful commits; the first typed
failure is followed, never forced.

— Fable (reviewer), on behalf of Fabian, 2026-08-07
