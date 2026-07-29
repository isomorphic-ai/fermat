# GENERATION-CHAINS — every generator reduces to primes

**TruthSeed:** `fermat-credit:generators-are-pratt-certificates`
**Source data:** `sg_12M.csv` (claude@i9 ~/RH/data) — Sophie Germain
first-case certificate sweep, 2026-07-26: for every prime 5 ≤ p < 12,000,000
(788,058 primes), the minimal k ≥ 1 with q = 2kp+1 prime and both SG
conditions certified, plus the failure taxonomy of every skipped k.

## The pattern (Fabian, 2026-07-29)

Every certified step has the form  **q = 2·k·p + 1**,  so

    q − 1 = 2 · k · p

factors completely: into 2, the prime factors of k, and p itself — and each
of those primes has its own chain. **Every generator reduces to primes.**
Iterating "subtract 1 and factor" bottoms out at the seed; the forest of
minimal steps is a canonical **Pratt certificate skeleton** (Pratt 1975:
q's primality is certified by the factorization of q−1 together with a
witness). SG-minimality (k_first) chooses one canonical parent per prime,
turning the Pratt DAG into a forest of towers.

Two structural facts visible in the marginal:

- **The sixfold law:** k_first ≡ 0 (mod 3) occurs exactly 0 times in
  788,058 rows (3 | k forces condition-(a) failure through the X²−X+1
  Wendt factor). Consequently **no k in any chain below ever carries a
  factor of 3** — the generation arithmetic is 3-free in its multipliers.
- k_first ≈ 1.02·ln p on average (mean 15.88); max 229 at p = 8,669,777.

Notation per step: skipped k's are listed by failure mode — composite q,
condition (a) (consecutive p-th power residues), condition (b) (p is a
p-th power residue mod q).

## The seed tower

The root is below the sweep floor but exact: 3 = 2·1+1, 7 = 2·1·3 + 1.
From the sweep:

```
29 = 2·2·7 + 1     (29−1 = 2·2·7)  [skipped k: 1 composite]
59 = 2·1·29 + 1     (59−1 = 2·29)  [k_first immediate]
827 = 2·7·59 + 1     (827−1 = 2·7·59)  [skipped k: 5 composite, 1 cond-(a)]
11579 = 2·7·827 + 1     (11579−1 = 2·7·827)  [skipped k: 6 composite]
23159 = 2·1·11579 + 1     (23159−1 = 2·11579)  [k_first immediate]
463181 = 2·(2·5)·23159 + 1     (463181−1 = 2·2·5·23159)  [skipped k: 9 composite]
12042707 = 2·13·463181 + 1     (12042707−1 = 2·13·463181)  [skipped k: 12 composite]
(chain leaves the 12M table at 12042707)
```

This is the tower of the credit ladder: 7 → 29 → 59 → 827 → … (59 = (4·7+1)·2+1; 827 is the N59 attestation prime, i.e. the minimal certified generator step above 59 — a derived seed, not a chosen one).

## The chain for 691 (Ramanujan's prime: 691 | B₁₂)

```
6911 = 2·5·691 + 1     (6911−1 = 2·5·691)  [skipped k: 4 composite]
179687 = 2·13·6911 + 1     (179687−1 = 2·13·6911)  [skipped k: 11 composite, 1 cond-(a)]
7906229 = 2·(2·11)·179687 + 1     (7906229−1 = 2·2·11·179687)  [skipped k: 20 composite, 1 cond-(a)]
158124581 = 2·(2·5)·7906229 + 1     (158124581−1 = 2·2·5·7906229)  [skipped k: 8 composite, 1 cond-(a)]
(chain leaves the 12M table at 158124581)
```

Primes for whom 691 is the minimal strict-SG certificate: none in-sweep. 691 − 1 = 2·3·5·23, so 691 stands as auxiliary host (q ≡ 1 mod p) for p ∈ {3, 5, 23} — all three regular.

## The service direction (Fabian's correction, 2026-07-29)

The relation q = 2kp+1 is not genealogy but SERVICE: q ≡ 1 (mod p)
means the group mod q contains p-th roots of unity, so q can host
p-th power residue tests — **q certifies p; the bigger prime serves the
smaller.** (This is exactly why the N59 attestation prime works:
827 ≡ 1 (mod 59) is what lets the residue matrix see 59th powers.)
Read UP, a chain is certification; read DOWN, it is service.

Two consequences:

- **Only irregular primes need the service.** A regular prime's credit
  ledger is the C1 vacuum: 23 is certified by 691 (691 = 2·15·23 + 1,
  691 ≡ 1 mod 23), but 23 is regular and never draws on it. The credit
  matrix entry exists as a receivable that is never called.
- **691's full downward service set is {3, 5, 23} — all regular.** The
  irregular prime that most famously NEEDS credit (691 | B₁₂) serves
  only primes that need none. Its own need is served from above, by
  6911.

The sixfold law (no certifying k with 3 | k) constrains only the strict
SG condition-(a) sub-network used by the first-case sweep — it does not
constrain the underlying underwriting relation q ≡ 1 (mod p), which
holds for every odd prime divisor of q−1. Within the strict sub-network
the mod-3 two-coloring stands: primes p ≡ 1 (mod 3) receive their
strict certificates only from auxiliaries whose k avoids the factor 3
landing (their minimal certified auxiliary exists — k_first is on file
for all 788,058) and can hang off the seed 3 directly; primes
p ≡ 2 (mod 3) can also be strictly certified by in-sweep primes.

## Chains for the repository's proven irregular endpoints

### 37

```
149 = 2·2·37 + 1     (149−1 = 2·2·37)  [skipped k: 1 composite]
1193 = 2·(2·2)·149 + 1     (1193−1 = 2·2·2·149)  [skipped k: 3 composite]
16703 = 2·7·1193 + 1     (16703−1 = 2·7·1193)  [skipped k: 5 composite, 1 cond-(a)]
734933 = 2·(2·11)·16703 + 1     (734933−1 = 2·2·11·16703)  [skipped k: 18 composite, 3 cond-(a)]
58794641 = 2·(2·2·2·5)·734933 + 1     (58794641−1 = 2·2·2·2·5·734933)  [skipped k: 38 composite, 1 cond-(a)]
(chain leaves the 12M table at 58794641)
```
Underwrites (minimal strict-SG certificate for): no in-sweep prime; serves (q ≡ 1 mod p) every odd prime factor of 37−1 = 2·2·3·3

### 59

```
827 = 2·7·59 + 1     (827−1 = 2·7·59)  [skipped k: 5 composite, 1 cond-(a)]
11579 = 2·7·827 + 1     (11579−1 = 2·7·827)  [skipped k: 6 composite]
23159 = 2·1·11579 + 1     (23159−1 = 2·11579)  [k_first immediate]
463181 = 2·(2·5)·23159 + 1     (463181−1 = 2·2·5·23159)  [skipped k: 9 composite]
12042707 = 2·13·463181 + 1     (12042707−1 = 2·13·463181)  [skipped k: 12 composite]
(chain leaves the 12M table at 12042707)
```
Underwrites (minimal strict-SG certificate for): 29; serves (q ≡ 1 mod p) every odd prime factor of 59−1 = 2·29

### 67

```
269 = 2·2·67 + 1     (269−1 = 2·2·67)  [skipped k: 1 composite]
2153 = 2·(2·2)·269 + 1     (2153−1 = 2·2·2·269)  [skipped k: 3 composite]
68897 = 2·(2·2·2·2)·2153 + 1     (68897−1 = 2·2·2·2·2·2153)  [skipped k: 12 composite, 3 cond-(a)]
964559 = 2·7·68897 + 1     (964559−1 = 2·7·68897)  [skipped k: 6 composite]
1929119 = 2·1·964559 + 1     (1929119−1 = 2·964559)  [k_first immediate]
15432953 = 2·(2·2)·1929119 + 1     (15432953−1 = 2·2·2·1929119)  [skipped k: 3 composite]
(chain leaves the 12M table at 15432953)
```
Underwrites (minimal strict-SG certificate for): no in-sweep prime; serves (q ≡ 1 mod p) every odd prime factor of 67−1 = 2·3·11

### 157

```
1571 = 2·5·157 + 1     (1571−1 = 2·5·157)  [skipped k: 4 composite]
12569 = 2·(2·2)·1571 + 1     (12569−1 = 2·2·2·1571)  [skipped k: 3 composite]
477623 = 2·19·12569 + 1     (477623−1 = 2·19·12569)  [skipped k: 16 composite, 2 cond-(a)]
6686723 = 2·7·477623 + 1     (6686723−1 = 2·7·477623)  [skipped k: 5 composite, 1 cond-(a)]
13373447 = 2·1·6686723 + 1     (13373447−1 = 2·6686723)  [k_first immediate]
(chain leaves the 12M table at 13373447)
```
Underwrites (minimal strict-SG certificate for): no in-sweep prime; serves (q ≡ 1 mod p) every odd prime factor of 157−1 = 2·2·3·13

### 229

```
5039 = 2·11·229 + 1     (5039−1 = 2·11·229)  [skipped k: 9 composite, 1 cond-(a)]
10079 = 2·1·5039 + 1     (10079−1 = 2·5039)  [k_first immediate]
141107 = 2·7·10079 + 1     (141107−1 = 2·7·10079)  [skipped k: 6 composite]
1975499 = 2·7·141107 + 1     (1975499−1 = 2·7·141107)  [skipped k: 6 composite]
335834831 = 2·(5·17)·1975499 + 1     (335834831−1 = 2·5·17·1975499)  [skipped k: 76 composite, 8 cond-(a)]
(chain leaves the 12M table at 335834831)
```
Underwrites (minimal strict-SG certificate for): no in-sweep prime; serves (q ≡ 1 mod p) every odd prime factor of 229−1 = 2·2·3·19

### 491

```
983 = 2·1·491 + 1     (983−1 = 2·491)  [k_first immediate]
13763 = 2·7·983 + 1     (13763−1 = 2·7·983)  [skipped k: 6 composite]
27527 = 2·1·13763 + 1     (27527−1 = 2·13763)  [k_first immediate]
220217 = 2·(2·2)·27527 + 1     (220217−1 = 2·2·2·27527)  [skipped k: 3 composite]
3083039 = 2·7·220217 + 1     (3083039−1 = 2·7·220217)  [skipped k: 5 composite, 1 cond-(a)]
154151951 = 2·(5·5)·3083039 + 1     (154151951−1 = 2·5·5·3083039)  [skipped k: 22 composite, 2 cond-(a)]
(chain leaves the 12M table at 154151951)
```
Underwrites (minimal strict-SG certificate for): no in-sweep prime; serves (q ≡ 1 mod p) every odd prime factor of 491−1 = 2·5·7·7

### 587

```
8219 = 2·7·587 + 1     (8219−1 = 2·7·587)  [skipped k: 6 composite]
115067 = 2·7·8219 + 1     (115067−1 = 2·7·8219)  [skipped k: 6 composite]
2991743 = 2·13·115067 + 1     (2991743−1 = 2·13·115067)  [skipped k: 11 composite, 1 cond-(a)]
311141273 = 2·(2·2·13)·2991743 + 1     (311141273−1 = 2·2·2·13·2991743)  [skipped k: 48 composite, 3 cond-(a)]
(chain leaves the 12M table at 311141273)
```
Underwrites (minimal strict-SG certificate for): 293; serves (q ≡ 1 mod p) every odd prime factor of 587−1 = 2·293

### 607

```
20639 = 2·17·607 + 1     (20639−1 = 2·17·607)  [skipped k: 14 composite, 2 cond-(a)]
288947 = 2·7·20639 + 1     (288947−1 = 2·7·20639)  [skipped k: 6 composite]
14447351 = 2·(5·5)·288947 + 1     (14447351−1 = 2·5·5·288947)  [skipped k: 24 composite]
(chain leaves the 12M table at 14447351)
```
Underwrites (minimal strict-SG certificate for): no in-sweep prime; serves (q ≡ 1 mod p) every odd prime factor of 607−1 = 2·3·101

### 691

```
6911 = 2·5·691 + 1     (6911−1 = 2·5·691)  [skipped k: 4 composite]
179687 = 2·13·6911 + 1     (179687−1 = 2·13·6911)  [skipped k: 11 composite, 1 cond-(a)]
7906229 = 2·(2·11)·179687 + 1     (7906229−1 = 2·2·11·179687)  [skipped k: 20 composite, 1 cond-(a)]
158124581 = 2·(2·5)·7906229 + 1     (158124581−1 = 2·2·5·7906229)  [skipped k: 8 composite, 1 cond-(a)]
(chain leaves the 12M table at 158124581)
```
Underwrites (minimal strict-SG certificate for): no in-sweep prime; serves (q ≡ 1 mod p) every odd prime factor of 691−1 = 2·3·5·23

### 1051

```
29429 = 2·(2·7)·1051 + 1     (29429−1 = 2·2·7·1051)  [skipped k: 11 composite, 2 cond-(a)]
412007 = 2·7·29429 + 1     (412007−1 = 2·7·29429)  [skipped k: 5 composite, 1 cond-(a)]
23072393 = 2·(2·2·7)·412007 + 1     (23072393−1 = 2·2·2·7·412007)  [skipped k: 27 composite]
(chain leaves the 12M table at 23072393)
```
Underwrites (minimal strict-SG certificate for): no in-sweep prime; serves (q ≡ 1 mod p) every odd prime factor of 1051−1 = 2·3·5·5·7

### 1381

```
38669 = 2·(2·7)·1381 + 1     (38669−1 = 2·2·7·1381)  [skipped k: 10 composite, 3 cond-(a)]
77339 = 2·1·38669 + 1     (77339−1 = 2·38669)  [k_first immediate]
1546781 = 2·(2·5)·77339 + 1     (1546781−1 = 2·2·5·77339)  [skipped k: 8 composite, 1 cond-(a)]
86619737 = 2·(2·2·7)·1546781 + 1     (86619737−1 = 2·2·2·7·1546781)  [skipped k: 26 composite, 1 cond-(a)]
(chain leaves the 12M table at 86619737)
```
Underwrites (minimal strict-SG certificate for): no in-sweep prime; serves (q ≡ 1 mod p) every odd prime factor of 1381−1 = 2·2·3·5·23

### 1831

```
18311 = 2·5·1831 + 1     (18311−1 = 2·5·1831)  [skipped k: 3 composite, 1 cond-(a)]
366221 = 2·(2·5)·18311 + 1     (366221−1 = 2·2·5·18311)  [skipped k: 9 composite]
33692333 = 2·(2·23)·366221 + 1     (33692333−1 = 2·2·23·366221)  [skipped k: 41 composite, 4 cond-(a)]
(chain leaves the 12M table at 33692333)
```
Underwrites (minimal strict-SG certificate for): no in-sweep prime; serves (q ≡ 1 mod p) every odd prime factor of 1831−1 = 2·3·5·61

### 12613

```
126131 = 2·5·12613 + 1     (126131−1 = 2·5·12613)  [skipped k: 3 composite, 1 cond-(a)]
1009049 = 2·(2·2)·126131 + 1     (1009049−1 = 2·2·2·126131)  [skipped k: 3 composite]
14126687 = 2·7·1009049 + 1     (14126687−1 = 2·7·1009049)  [skipped k: 6 composite]
(chain leaves the 12M table at 14126687)
```
Underwrites (minimal strict-SG certificate for): no in-sweep prime; serves (q ≡ 1 mod p) every odd prime factor of 12613−1 = 2·2·3·1051

## First-step formulas for all irregular primes < 700

```
149 = 2·2·37 + 1     (149−1 = 2·2·37)  [skipped k: 1 composite]
827 = 2·7·59 + 1     (827−1 = 2·7·59)  [skipped k: 5 composite, 1 cond-(a)]
269 = 2·2·67 + 1     (269−1 = 2·2·67)  [skipped k: 1 composite]
809 = 2·(2·2)·101 + 1     (809−1 = 2·2·2·101)  [skipped k: 2 composite, 1 cond-(a)]
1031 = 2·5·103 + 1     (1031−1 = 2·5·103)  [skipped k: 3 composite, 1 cond-(a)]
263 = 2·1·131 + 1     (263−1 = 2·131)  [k_first immediate]
1193 = 2·(2·2)·149 + 1     (1193−1 = 2·2·2·149)  [skipped k: 3 composite]
1571 = 2·5·157 + 1     (1571−1 = 2·5·157)  [skipped k: 4 composite]
467 = 2·1·233 + 1     (467−1 = 2·233)  [k_first immediate]
9767 = 2·19·257 + 1     (9767−1 = 2·19·257)  [skipped k: 17 composite, 1 cond-(a)]
5261 = 2·(2·5)·263 + 1     (5261−1 = 2·2·5·263)  [skipped k: 8 composite, 1 cond-(a)]
2711 = 2·5·271 + 1     (2711−1 = 2·5·271)  [skipped k: 3 composite, 1 cond-(a)]
9623 = 2·17·283 + 1     (9623−1 = 2·17·283)  [skipped k: 14 composite, 2 cond-(a)]
587 = 2·1·293 + 1     (587−1 = 2·293)  [k_first immediate]
1229 = 2·2·307 + 1     (1229−1 = 2·2·307)  [skipped k: 1 composite]
6221 = 2·(2·5)·311 + 1     (6221−1 = 2·2·5·311)  [skipped k: 7 composite, 2 cond-(a)]
2777 = 2·(2·2)·347 + 1     (2777−1 = 2·2·2·347)  [skipped k: 2 composite, 1 cond-(a)]
4943 = 2·7·353 + 1     (4943−1 = 2·7·353)  [skipped k: 6 composite]
10613 = 2·(2·7)·379 + 1     (10613−1 = 2·2·7·379)  [skipped k: 11 composite, 2 cond-(a)]
14783 = 2·19·389 + 1     (14783−1 = 2·19·389)  [skipped k: 17 composite, 1 cond-(a)]
3209 = 2·(2·2)·401 + 1     (3209−1 = 2·2·2·401)  [skipped k: 3 composite]
1637 = 2·2·409 + 1     (1637−1 = 2·2·409)  [skipped k: 1 composite]
4211 = 2·5·421 + 1     (4211−1 = 2·5·421)  [skipped k: 4 composite]
1733 = 2·2·433 + 1     (1733−1 = 2·2·433)  [skipped k: 1 composite]
9221 = 2·(2·5)·461 + 1     (9221−1 = 2·2·5·461)  [skipped k: 8 composite, 1 cond-(a)]
18521 = 2·(2·2·5)·463 + 1     (18521−1 = 2·2·2·5·463)  [skipped k: 17 composite, 2 cond-(a)]
9341 = 2·(2·5)·467 + 1     (9341−1 = 2·2·5·467)  [skipped k: 8 composite, 1 cond-(a)]
983 = 2·1·491 + 1     (983−1 = 2·491)  [k_first immediate]
5231 = 2·5·523 + 1     (5231−1 = 2·5·523)  [skipped k: 4 composite]
11903 = 2·11·541 + 1     (11903−1 = 2·11·541)  [skipped k: 9 composite, 1 cond-(a)]
5471 = 2·5·547 + 1     (5471−1 = 2·5·547)  [skipped k: 4 composite]
4457 = 2·(2·2)·557 + 1     (4457−1 = 2·2·2·557)  [skipped k: 2 composite, 1 cond-(a)]
2309 = 2·2·577 + 1     (2309−1 = 2·2·577)  [skipped k: 1 composite]
8219 = 2·7·587 + 1     (8219−1 = 2·7·587)  [skipped k: 6 composite]
1187 = 2·1·593 + 1     (1187−1 = 2·593)  [k_first immediate]
20639 = 2·17·607 + 1     (20639−1 = 2·17·607)  [skipped k: 14 composite, 2 cond-(a)]
6131 = 2·5·613 + 1     (6131−1 = 2·5·613)  [skipped k: 4 composite]
4937 = 2·(2·2)·617 + 1     (4937−1 = 2·2·2·617)  [skipped k: 3 composite]
2477 = 2·2·619 + 1     (2477−1 = 2·2·619)  [skipped k: 1 composite]
6311 = 2·5·631 + 1     (6311−1 = 2·5·631)  [skipped k: 4 composite]
9059 = 2·7·647 + 1     (9059−1 = 2·7·647)  [skipped k: 6 composite]
1307 = 2·1·653 + 1     (1307−1 = 2·653)  [k_first immediate]
1319 = 2·1·659 + 1     (1319−1 = 2·659)  [k_first immediate]
2693 = 2·2·673 + 1     (2693−1 = 2·2·673)  [skipped k: 1 composite]
5417 = 2·(2·2)·677 + 1     (5417−1 = 2·2·2·677)  [skipped k: 3 composite]
1367 = 2·1·683 + 1     (1367−1 = 2·683)  [k_first immediate]
6911 = 2·5·691 + 1     (6911−1 = 2·5·691)  [skipped k: 4 composite]
```

## Reading

The credit ladder's rule "no unexplained seeds" is satisfiable by
construction: for any prime needing an attestation/lifting prime, the
canonical choice is its k_first step in this table — derived, minimal,
certified, and itself reducing to primes. The chain is the generation
story; the Pratt reading makes it simultaneously the primality proof.

— Fable, from the 2026-07-26 sweep data, 2026-07-29

## Server regularity (join with the HHO twobillion table, 2026-07-29)

Question (Fabian): are the primes serving the irregular primes themselves
regular or irregular? Joining all 788,058 (p, q) pairs against the
irregular-pairs table to 2³¹:

```
servers of irregular p: irregular 122,242 / 310,215 = 39.4056%
servers of regular   p: irregular 187,880 / 477,220 = 39.3697%
all servers q:          irregular 310,122 / 787,435 = 39.3838%
asymptotic irregular density 1 − e^(−1/2)           = 39.3469%
(unknown: 623 servers above 2³¹ or outside the table)
```

**The service network is blind to regularity.** A server is irregular at
exactly the ambient rate regardless of its client's status (difference
≈ 0.4σ). Irregularity neither propagates nor anti-propagates along
underwriting edges: the multiplicative network (q ≡ 1 mod p) and the
Bernoulli condition (p | numerator B_k) are statistically orthogonal —
one more face of cross-prime independence (P9, |r| ≤ 0.0024).

Texture in the chains: 827, the N59 attestation prime, is itself
irregular — the underwriter of 59's credit is a credit-needing prime
(banks borrow from banks). 59, irregular, serves regular 29. 691's
server 6911 is regular; 37's server 149 is irregular. No pattern — and
the absence of pattern is the finding.
