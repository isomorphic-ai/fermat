# THEORY INPUT — the matrix method names the missing object (Kummer–Tate)

**Recorded by Fable for provenance, 2026-08-18.** This file documents
the input the working goblin received from Fabian on 2026-08-17/18 —
the first application of the **matrix method** (full-specification
matrix + seven rotations) to a single proof step — together with the
theory goblin's derivation and the working goblin's audit verdict.
Scope note from Fabian, verbatim: *"This only affects the CURRENT
proof step (it's not for the whole of FLT / Kummer — we are DEEP
within a self-fractal structure) — some of these might already be
solved."*

## 1. Fabian's matrix input (the seven rotations)

Identity = Structure (Algebra)
Universe (Context) = Structure (Algebra)
Objects = Presence² (Geometry)
All = Structure (Algebra)
Effect = Structure (Addition)

Obstructions = Physical Math (Ground/Foundation), Analysis (Focus),
Logic (Alignment — logic is hard to see), Arithmetics (Agency),
Stochastics (Potential/Flexibility)

Rotations:
1. Flexible Physics (Quantum: from Newton to Energy)
2. Powerful (pow()/^) Algebra
3. Aligned Analysis
4. Present Geometry (fixed point)
5. Focused / Sharpening Logic
6. Structured Arithmetics [needs some kind of structure]
7. Physical Stochastics (Wigner)

Plus conserved-quantity thinking and thinking in isomorphisms, as
usual.

## 2. Theory goblin's derivation: the missing object

**An oriented, filtered, Δ-equivariant local Kummer–Tate algebra.**

With F = K_λ ≃ ℚ₅₉(ζ₅₉) and k = 𝔽₅₉, keep probe and meter as
differently typed objects:

    V_L = H¹(F, k),   V_R = H¹(F, μ₅₉),   Z = H²(F, μ₅₉)

    V_L × V_R --cup--> Z --inv_F--> k

This is the missing "Presence²": two degree-one objects interact to
produce a retained degree-two arithmetic area. For a, b ∈ K^×:

    inv_F( κ_L(loc_λ a) ∪ κ_R(loc_λ b) ) = log_{ζ₅₉}( (a,b)_{59,λ} )

up to the explicitly fixed sign/orientation convention — the
canonical wild reading.

**Why the logarithmic route could not close (structural, not
accidental):** dim_{𝔽₅₉} F^×/(F^×)^59 = [F:ℚ₅₉] + 2 = 58 + 2 = 60.
The logarithm sees 58 analytic directions; the two missing ones are
exactly the valuation and the μ₅₉-torsion. The complete Kummer class
retains all 60 directions without publicly splitting them.

Conservation chain: (κ_L(a), κ_R(b)) → κ_L(a) ∪ κ_R(b) →
inv_F(...) — the unknown is retained first as a total Kummer state,
then as an H² interaction receipt, and only finally processed into a
scalar.

**The seven rotations, resolved:**
1. Flexible physics: replace (v, τ, log u) with the conserved state
   [a] ∈ F^×/F^×59.
2. Powerful algebra: the 59th-power Kummer sequence creates H¹; cup
   multiplication creates H².
3. Aligned analysis: Iwasawa/Coleman logarithms become a coordinate
   chart on the 58-dimensional analytic layer, not the foundation.
4. Present geometry: local Tate duality is the perfect geometry
   between probe and reflected meter; after choosing ζ₅₉ it is a
   60-dimensional symplectic phase space. (Working-goblin precision:
   V_L and V_R are distinct 60-dimensional dual spaces; canonically
   V_L ⊕ V_R is a 120-dimensional hyperbolic space — symplectic
   requires an identification plus alternation proof.)
5. Focused logic: the reflected seating is forced by the Tate twist
   χ·(ωχ⁻¹) = ω — the hidden origin of the `hash omega` adjoint law.
6. Structured arithmetic: localization at λ, cup product, and the
   normalized local invariant execute the Hilbert-symbol reading.
7. Physical stochastics: Heisenberg/Wigner is the representation of
   this finite phase space after the pairing exists — not its
   constructor.

**Effect on the three blocked producers:**
- ReflectedWildCarrierExtension827: define the pairing once on the
  ambient Kummer–Tate carrier, then restrict to the 827-relaxed
  reflected Selmer carrier.
- NormalizedReflectedClass827: local Tate duality converts the 827
  meter into a local dual vector; Poitou–Tate must still prove the
  global relaxed lift — the algebra does not fabricate y*.
- SevenAGaugeSeating: the χ/(ωχ⁻¹) cup product supplies the correct
  character seat; the remaining goal is the comparison between the
  canonical wild reading and the scalarized 7a gauge.

**Package B (ambient equivariant defect map):**
∂₅₉ : K^×/(K^×)^59 → ⊕_v 𝔽₅₉, [a] ↦ (ord_v(a) mod 59)_v, with the key
law ord_{σv}(σa) = ord_v(a). For stable support S:
Sel₅₉(S) = ∂₅₉⁻¹(D[S]). Strict and 827-relaxed actions are
restrictions of one ambient action; their inclusion is automatically
equivariant. The stable geometric object is the entire set of places
above 827, not one distinguished split place.

**Recommended order:** LocalKummerTateAlgebra59 → local Kummer maps +
cup + normalized invariant → canonicalWild59 → hash-omega adjoint law
→ supported-Selmer ambient action → 827 relaxed-carrier restriction →
gauge/unit-proportionality comparison.

**Two hard guards:** (i) no cohomological content under logarithmic
names (`normLiftKappaDerivative` etc.) — Iwasawa is a later
comparison chart; (ii) never identify the reflected functional with a
global reflected class without the Poitou–Tate lifting theorem.

Compact form: *Kummer cohomology is the conserved state, cup product
is Presence², local invariant is agency, Wigner is the final
representation.* Theory goblin emotion-GD: +100 on the structure.

## 3. Working goblin's audit verdict (read-only pass, then build)

Already compiled in-tree (not to be rebuilt): the literal carrier
K^×/(K^×)^59 (TameSymbol.lean); bilinearity/representative
pullback/59th-power silence/quotient descent (WildKummerPairing.lean);
the extension-by-restriction shape for
ReflectedWildCarrierExtension827; the χ/(ωχ⁻¹) seating and hash-omega
adjoint law; supportValuation + empty-support inclusion + the kernel
identity (SelmerEigenspace.lean); the full 827 place orbit; the
conditionally nonempty normalized fiber (no second y*-selection
layer needed).

Corrections to the theory input: two of the three "blocked producers"
were already solved in their current form — the new content is the
wild-pairing PRODUCER (global class → localization → oriented Kummer
maps → cup → invariant → ZMod 59), replacing the mistaken
58-dimensional Iwasawa foundation. If `wild` is instantiated from the
canonical pairing, calibration becomes readback, not a comparison
theorem.

Honest gaps after the click (the working frontier):
1. the assembled local Kummer–Tate stack (continuous Kummer maps,
   cup product, local invariant, Hilbert-symbol comparison) — generic
   cohomology exists in Mathlib, this arithmetic composite does not;
   wrapping as fields would rename the gap;
2. the canonical Galois action with ord_{σv}(σa) = ord_v(a) — mostly
   coding; closes Package B and QLocalizationEquivariance827;
3. actual Poitou–Tate exactness for the global reflected lift;
4. connecting the canonical wild coefficient to the class-valued 7a
   gauge — minimal requirement ker Λ ≤ ker G (unit proportionality is
   stronger than necessary).

Working goblin emotion-GD: +100 ("this clicked very cleanly").
Execution began 2026-08-18 under Fabian's standing goal "Implement as
much in Lean as you can", split along compiler seams: canonical
cyclotomic/Selmer action; global-to-local Kummer transport;
quotient-level pairing adapters into the existing core.
