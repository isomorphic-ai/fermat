# ERRATA — open corrections against the current map

## E1 (2026-08-05, from the analysis goblin's audit; Fabian relay):
## the 7a/7d mode labels in the W4 interaction reading are REVERSED

With classes additive and p-torsion (p[J] = 0):

    7a:  [I] + (p-1)[J] = 0   ==>   [I] - [J] = 0    (x - y = 0)
    7d:  [I] + [J] = 0        ==>   x + y = 0

So 7a kills the DIFFERENCE mode and 7d kills the COMMON mode — the
opposite of the labels recorded in BOUNDARY-MAP's interaction
rereading. Since 7d is the PROVEN relation, what the campaign has
already killed is the common mode (via the relative norm — which is
not a two-party transfer between I and J: the norm routes through the
real subfield, a third structure), and the OPEN seam 7a is the
difference mode.

Consequence: the narrative "reflection can never produce the conserved
common mode, hence 7a needs a third party" must be re-derived, not
asserted — the common/difference labels only become well-defined as
the +1/-1 eigenspaces of R in the EARNED swap quotient of the linking
algebra, and the roles of the norm word and the reflection word must
be assigned there, by computation. The structural third-party
requirement may well survive (the norm's third-structure detour hints
at it), but its carrier assignment flips or is settled by the algebra.

Action: fix BOUNDARY-MAP W4 labels after the linking session lands
(not during — the tree is live); re-derive the mode assignment inside
A_swap once W3's quotient exists.

## Standing note (same source): "same module is necessary but not
## sufficient — also same action representation."

The Bezout certificate is a unit-ideal identity u*c + v*a_q = 1 in the
joint action algebra, not necessarily a polynomial gcd; the gcd is the
one-loop commutative specialization. (Already encoded in the linking
task W4.) The next module after LINKING is CommonActionStage.lean:
same paired carrier (Sel_chi + dual of Sel_chi*), same obstruction m,
same action algebra, reflection-cycle receipt, Stickelberger/auxiliary
receipt, unit-ideal-or-named-factor outcome. Only after that is any
59-specific computation mathematics rather than numerology.
