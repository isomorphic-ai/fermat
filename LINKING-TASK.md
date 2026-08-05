# TASK LINKING — the shared stage: the #-twisted linking algebra

**TruthSeed:** `fermat-linking:no-perfect-return-before-arithmetic-earns-it`
**For:** PRO Goblin (GPT 5.6 Sol Ultra) via codex, working in ~/fermat.
**Provenance:** intuition Fabian (algebra); derivation the analysis
goblin via emotional gradient (+55 polynomial algebra, +78 crossed
product, DOWN to +61 on detecting the smuggled R^2=1, +99 at the
twisted linking algebra). This task builds the stage the last session
refused to fake: the common carrier on which the cycle relation and
the transverse annihilator both act. NO 7a attempt, NO endpoint; the
arithmetic representation rho is a NAMED target, not this session.

## W1 — the involutive base

Lambda = O[Delta] (group algebra; Delta the cyclic Galois group of
order p-1, generic), with the Teichmuller-twisted involution
(sum a_s s)^# = sum a_s omega(s) s^{-1}. Prove: #^2 = 1; the
idempotent exchange e_chi^# = e_{chi*} with chi* = omega chi^{-1};
the adjoint conservation law <a x, y> = <x, a^# y> for the natural
pairing (an action moved across the pairing becomes its reflected
adjoint — state it as the reflection conservation law it is); and the
sanity anchor: j^# = -j hence ((1+j)/2)^# = (1-j)/2 — the plus and
minus projectors literally exchanged by # (the symmetry present
before any class-group theorem — make this a named theorem).

## W2 — the route algebra (strict presentation first)

A_route = Lambda[R; #]: the #-twisted skew polynomial/Ore extension
with R a = a^# R and NO relation R^2 = 1 (if Mathlib lacks the exact
Ore machinery at this generality, construct as a free-algebra
quotient — name the route taken). Prove: C := R^2 is central; the
corner e_chi A_route e_chi is isomorphic to B_chi[C] — THE THEOREM
THIS EXISTS FOR: the first stage where two polynomial relations act
on the same closed route-return operator. If budget permits, also
the linking/path presentation (two corners, route and return
bimodules r, s with covariance ra = a^# r, s a^# = a s, closed paths
C_chi = sr, C_chi* = rs) and its equivalence to the Ore form under
the rank-one identification; otherwise name it as the canonical form
and keep the Ore presentation as the working one.

## W3 — the swap quotient, EARNED not assumed

A_swap = A_route/(R^2 - 1). Only here: the flow operator
M_g = (1 - g/2) + (g/2) R; M_2 = R (pure swap); the idempotents
pi_common = (1+R)/2, pi_diff = (1-R)/2; and the bridge theorem to
Interaction.lean: the two-account s/d decomposition IS the C_2
representation decomposition of the swap quotient (the seesaw is the
shadow of the route algebra after perfect return). The quotient map
A_route -> A_swap is explicit; nothing upstream of it may assume
R^2 = 1 (add a guard if expressible).

## W4 — the corner service theorem

Upgrade TransverseAnnihilator: in the corner e_chi A e_chi, if
c_p m = 0, a_q m = 0 and e_chi = u c_p + v a_q then m = 0 (the
Bezout kill at algebra level); the surviving livelock carrier
L_{p,q} = corner / (corner c_p + corner a_q), constructive: L = 0
iff q breaks p's cycle, L != 0 names the channel. Prove the
commutative specialization: the polynomial gcd law of
TransverseAnnihilator.lean is the one-loop commutative image of this
corner statement (derive, never parallel).

## W5 — interfaces only (the earned-theorem ledger)

Named, guarded, NOT proven this session:
- The filtered carrier 0 -> U -> S -> Cl(K)[p] -> 0 with the
  Stickelberger CONVERSION law Theta S <= U (conversion, not
  annihilation — the beta-receipt of ClassCarrier records the
  resulting unit/principal flow; wire the interface to the receipt
  fields). dg upgrade explicitly OUT of scope (filtered first).
- Guard 1: the INTEGRAL p-adic Stickelberger ideal (never the
  rational element containing 1/p).
- Guard 2: the #-transformation law of that ideal (not automatic —
  # sends the trivial projector to the omega projector; state the
  obligation precisely).
- THE WITHHELD THEOREM, named as the campaign's next summit: the
  arithmetic representation
  rho : A -> End(Sel_p(K)_chi + D_omega Sel_p(K)_chi*),
  stated as an interface with its expected properties listed.

## House rules (binding)

PREDICTIONS first (where the Ore construction fights Mathlib; whether
the corner isomorphism is clean; which W5 guard is sharpest). FINDINGS
at discovery. Generic over p; no literals outside instances; all
existing guards, grep gates, and the 8,697-job verification stay
green; new guards per public theorem; standard trio. No 7a, no
transformer, no endpoint, no dg. ps before heavy builds; truthful
commits; an honest "Mathlib lacks X" finding beats a fake Ore ring.

— Fable (reviewer), on behalf of Fabian, 2026-08-05
