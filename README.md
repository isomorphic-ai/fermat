# Fermat: classical fixed-exponent proofs in Lean

This project formalizes the complete classical exponent-specific proofs of
Fermat's Last Theorem for:

- `n = 3`
- `n = 4`
- `n = 5`
- `n = 7`
- `n = 14`

The scope follows the historic source archive in `../fermat-data`. It excludes
Wiles/Taylor–Wiles, modularity, elliptic curves, Kummer's general regular-prime
theory, broad computational verification, and first-case-only results.

The common theorem statement is `Fermat.HoldsAt n` over nonzero integers. The
development will keep the historical descent arguments visible while splitting
their algebraic and number-theoretic lemmas into reusable Lean modules.

## Build

```bash
lake exe cache get
lake build
```
