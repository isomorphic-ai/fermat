# TASK INTERACTION — the flow-bound theorem, the non-lossy class carrier, and the transverse annihilator

**TruthSeed:** `fermat-interaction:reflection-conserves-s-the-lamp-breaks-the-cycle`
**For:** PRO Goblin (GPT 5.6 Sol Ultra) via codex, working in ~/fermat.
**Provenance:** flow-bound dynamics and carrier spec by Fabian (with a
Sol instance, 2026-08-04); direction located by emotional gradient.
Goal per the standing ruling: invariants, not endpoints. 7a is the
GAUGE READING, never the target. No transformer, no endpoint.

## The insight being formalized

Two accounts under generous transfer f = g*(A-B)/2: the sum s = A+B is
conserved (the pool); the difference d = A-B evolves d -> (1-g)d (the
interaction mode). Flow-bound theorem: in a bounded positive ledger
(|d| <= s), g=2 is the critical livelock (perpetual swap, constant
energy E = d^2) and g>2 is supercritical - impossible forever; it must
stop, exit, or convert. A closed conservative network has no
supercritical mode, and every critical cycle needs an exit.
Consequences: (i) 7d killed the d-mode; 7a lives in the s-mode, and
two-party transfers conserve s - the pair alone can NEVER produce it;
(ii) a THIRD party must supply the transverse interaction that turns
the old common mode into a new difference; (iii) a finite class group
is NOT a bounded positive ledger (quotients wrap: g=3 gives d -> -2d
which is d mod 3 - the quotient erases the energy), so the class
carrier must be geometric + receipted.

## W1 — the interaction dynamics (generic, small, clean)

`Fermat/Experiments/Conservation/Interaction.lean`: the two-account system, s
conservation, d -> (1-g)d, energy E = d^2 with E <= s^2 on positive
ledgers, and the flow-bound trichotomy: g<2 damped, g=2 the period-two
livelock ((A,B) -> (B,A)), g>2 supercritical-impossible-forever in a
bounded positive ledger (derive the exit trilemma: halt, leave, or
convert). Include the quotient-erases-energy warning lemma (the g=3
mod 3 fixed point) as a named theorem - it is the reason W2 exists.
Wire to AreaTransfer where natural (the livelock swap is a closed
word; its invariance is a payload statement).

## W2 — the non-lossy class carrier (Fabian's spec)

`Fermat/Experiments/Conservation/ClassCarrier.lean`: the state is NOT the lossy
class [I]; it is (I_red, beta, annihilator receipts) where I_red lies
in a bounded (Minkowski-type) fundamental region and beta is the
principalization receipt of the reduction I = (beta) * I_red. Laws:
reduction emits receipts - anything discarded by passing to classes
reappears in beta (no silent discard; the class group is the lossy
projection of this carrier, stated as a theorem). Use Mathlib's
Minkowski/finiteness machinery for boundedness where available; where
the full geometric bound fights, a bounded-representative interface
with the receipt discipline is acceptable - name the gap.

## W3 — the two-annihilator Bezout law and the transverse record

Generic over F_p[T] (polynomial annihilators acting on the d-mode of a
module): the cycle relation (T^r - 1) * d = 0 (reflection - we own the
fold) plus a transverse annihilator P(T) * d = 0 implies via Bezout:
gcd(P, T^r - 1) = 1 -> d = 0; a common factor IDENTIFIES the surviving
livelock channel (state this constructively: the gcd factor is the
channel). Two named transverse sources as interfaces: (a) the
Stickelberger annihilator (credit by name; consume from deps if
available, else a named interface field); (b) the lamp: the supporter
prime q = 2kp+1 as transverse partner - state the interface connecting
the SG certificate conditions to gcd-coprimality (condition (a)
failures = shared factors = livelock channels; the sixfold law = the
guaranteed Wendt X^2-X+1 shared factor for 3|k). The sweep's
k_first table is the empirical periodic-annihilator record - cite
notes/GENERATION-CHAINS.md; do not recompute.

## W4 — the gauge readings (predictions, not targets)

Update notes/BOUNDARY-MAP.md: restate 7a in interaction vocabulary - the
s-mode of the (I,J) pair requires a transverse third party (candidate:
the 59-lamp 827 and/or Stickelberger), the old common mode becoming
the new difference of the (state, lamp-view) pair. Named open
correspondence, never conflated: Bernoulli depth 2 vs interaction gain
g = 2 - the "two 2s" theorem is future work and is flagged as such
(Fabian's explicit caution). If during W3 the 59-instance gcd
computation becomes concrete and cheap, compute it and record the
verdict (coprime, or the named channel) - as data, not as a seam
crossing.

## House rules (binding)

PREDICTIONS first (which W resists; whether Minkowski machinery
suffices for W2; whether Stickelberger is reachable in deps). FINDINGS
at discovery. All existing guards, grep gates, and the 8,693-job
verification stay green; new guards for new public theorems; standard
trio; generic core, 59 only in instance layers. No 7a attempt, no
transformer, no endpoint. ps before heavy builds; truthful commits;
an honest interface with a named gap beats a forced geometric bound.

— Fable (reviewer), on behalf of Fabian, 2026-08-04
