# NoBernoulliCubeObstruction59 — computational certificate

**Statement matched:** `forall i : Fin 28, not (59:Z)^3 | (bernoulli ((2*(i+1))*59)).num`
(all indices even, so Mathlib bernoulli/bernoulli-prime convention-independent).

**Result: VERIFIED, all 28 valuations < 3.** Profile: v=1 at 27 indices,
v=2 exactly at i+1=22 (n=2596=44*59, the irregular position of the pair (59,44)).

Methods (independent): (A) exact fraction recurrence to n=236;
(B) p-adic power sums S_n(59) mod 59^4 with Kummer correction, all n;
(C) phase-1 C++ Padic4 sweep 2026-07-26 (row 59,44,9,18: lift 18 != 0 => v=2 exact).
Cross-checks: A=B at n=236 (residue 90388 both); B=C at (59,44).

| i | n=2i*59 | B_n mod 59^3 | v_59 |
|---|---------|--------------|------|
| 1 | 118 | 171159 | 1 |
| 2 | 236 | 90388 | 1 |
| 3 | 354 | 121422 | 1 |
| 4 | 472 | 156527 | 1 |
| 5 | 590 | 50268 | 1 |
| 6 | 708 | 37701 | 1 |
| 7 | 826 | 63307 | 1 |
| 8 | 944 | 180068 | 1 |
| 9 | 1062 | 161306 | 1 |
| 10 | 1180 | 119298 | 1 |
| 11 | 1298 | 180363 | 1 |
| 12 | 1416 | 43070 | 1 |
| 13 | 1534 | 57348 | 1 |
| 14 | 1652 | 139653 | 1 |
| 15 | 1770 | 151335 | 1 |
| 16 | 1888 | 174168 | 1 |
| 17 | 2006 | 114342 | 1 |
| 18 | 2124 | 131452 | 1 |
| 19 | 2242 | 122838 | 1 |
| 20 | 2360 | 118708 | 1 |
| 21 | 2478 | 55578 | 1 |
| 22 | 2596 | 62658 | 2 (irregular r=44) |
| 23 | 2714 | 118413 | 1 |
| 24 | 2832 | 8732 | 1 |
| 25 | 2950 | 130331 | 1 |
| 26 | 3068 | 148798 | 1 |
| 27 | 3186 | 7670 | 1 |
| 28 | 3304 | 137588 | 1 |

Computed 2026-07-29 by Fable, pure Python, 0.075 s; script:
/tmp/bernoulli_cube.py on claude@i9 (to be archived in RH/harness).

## Addendum (Fabian, 2026-07-30): the certificate's second reading

The v-profile [1,...,1,2,1,...,1] certifies TWO hypotheses with one
measurement — the L4 pattern (one quantity, two readings):

1. **Non-divisibility reading (stock):** no 59^3 anywhere — the cube
   obstruction is absent; in the flow interface
   `59^3 | (sum_i a_i * M_{ki}) * B_k`, one factor of 59 survives the
   division by B_k at every character, so the forcing bites everywhere.
2. **Maximum reading (flow):** max depth = 2, attained only at the
   irregular position — the deep-congruence level 118 = 2*59 in
   `DeepFlowLaw59` is SUFFICIENT: the pump reaches depth 2p and no
   eigenvalue can absorb more than depth 2. The "2" in Vandiver's
   (1-zeta)^(2p) is this measured fact, not a convention. Were any
   v = 3, the level-2p congruence would say nothing at that character
   and the law would need level 3p.

Same inequality (v <= 2), two obstructions dissolved: the forcing
cannot be blocked, and the pump cannot be out-run. This is also the
phase-1 sweep's condition-4 "never-worse contract" (v_p(B_rp) = 2
exactly, 0 DEEP flags below 12M) meeting the FLT side: the RH-side
sweep and this certificate are the same measurement in two programs.
