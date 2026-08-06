/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# The explicit tame Hilbert symbol

This file formalizes the cohomology-free formula for the degree-`p` Hilbert
symbol at a place whose residue characteristic is different from `p`:

`(a,b)_v = omega((-1)^(v(a)v(b)) a^v(b) / b^v(a))^((q-1)/p)`.

The normalization follows Fesenko--Vostokov, *Local Fields and Their
Extensions*, Chapter IV, section 5, and Neukirch, *Algebraic Number Theory*,
Chapter V, section 3.  We retain the multiplicative residue representative as
`raw` and use a chosen primitive `p`-th root to write its `(q-1)/p`-th power
additively in `ZMod p`.

Mathlib currently has the finite-field exponent theorem and the equivalence
between `ZMod p` and the powers of a primitive root, but no generic angular
component attached to a discrete valuation.  `Context` is the minimal honest
interface for that missing construction.  The small generic results
`powerToRoots` and `SteinbergValuationCases.raw_eq_one` are deliberately
factored as Mathlib-welcome residue-field lemmas.  `SteinbergRealization`
names the remaining Mathlib gap: proving the valuation/angular-component
trichotomy for the actual pair `a, 1-a`.
-/
import Fermat.Conservation.InvolutiveBase
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

noncomputable section

namespace Fermat.Conservation.TameSymbol

universe uK uk uDelta uPlace

open scoped Pointwise

/-- The additive Kummer quotient used by Mathlib's `selmerGroup` ambient
carrier.  Naming it here makes the tame pairing/Selmer correspondence
definitionally transparent. -/
abbrev KummerClass (p : ℕ) (K : Type uK) [Field K] :=
  Additive (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range)

/-- Data at a tame place sufficient to evaluate the explicit Hilbert symbol.

`ord` is the additive valuation on nonzero elements and `angularComponent` is
the multiplicative residue of the unit part.  The last two fields say that the
place is away from `p` and that the residue field contains `mu_p`.

The construction of `angularComponent` from a valuation ring, a uniformizer,
and the residue map is the sole local-field realization interface: pinned
Mathlib does not yet expose that composite as a bundled homomorphism. -/
structure Context (p : ℕ) [Fact p.Prime]
    (K : Type uK) (k : Type uk) [Field K] [Fintype k] [Field k] where
  ord : Additive Kˣ →+ ℤ
  angularComponent : Kˣ →* kˣ
  residueChar_ne : ringChar k ≠ p
  card_sub_one_dvd : p ∣ Fintype.card k - 1
  primitiveRoot : kˣ
  primitiveRoot_spec : IsPrimitiveRoot primitiveRoot p

namespace Context

variable {p : ℕ} [Fact p.Prime]
  {K : Type uK} {k : Type uk} [Field K] [Fintype k] [Field k]

/-- The cardinality `q` of the residue field. -/
abbrev residueCard (_ctx : Context p K k) : ℕ := Fintype.card k

/-- The tame exponent `(q - 1) / p`. -/
def tameExponent (ctx : Context p K k) : ℕ :=
  (ctx.residueCard - 1) / p

/-- The multiplicative residue appearing before the `(q-1)/p` power.

Writing `ac` for the angular component, this is exactly
`(-1)^(v(a)v(b)) * ac(a)^v(b) / ac(b)^v(a)`. -/
def raw (ctx : Context p K k) (a b : Kˣ) : kˣ :=
  (-1 : kˣ) ^
      (ctx.ord (Additive.ofMul a) * ctx.ord (Additive.ofMul b)) *
    ctx.angularComponent a ^ ctx.ord (Additive.ofMul b) *
    ctx.angularComponent b ^ (-ctx.ord (Additive.ofMul a))

@[simp]
theorem raw_one_left (ctx : Context p K k) (b : Kˣ) :
    ctx.raw 1 b = 1 := by
  simp [raw]

@[simp]
theorem raw_one_right (ctx : Context p K k) (a : Kˣ) :
    ctx.raw a 1 = 1 := by
  simp [raw]

/-- Multiplicativity of the raw tame residue in the first variable. -/
theorem raw_mul_left (ctx : Context p K k) (a₁ a₂ b : Kˣ) :
    ctx.raw (a₁ * a₂) b = ctx.raw a₁ b * ctx.raw a₂ b := by
  have hord : ctx.ord (Additive.ofMul (a₁ * a₂)) =
      ctx.ord (Additive.ofMul a₁) + ctx.ord (Additive.ofMul a₂) :=
    ctx.ord.map_add _ _
  simp only [raw, hord, map_mul, add_mul, zpow_add, neg_add_rev, mul_zpow]
  ring_nf
  simp only [mul_assoc, mul_left_comm, mul_comm]

/-- Multiplicativity of the raw tame residue in the second variable. -/
theorem raw_mul_right (ctx : Context p K k) (a b₁ b₂ : Kˣ) :
    ctx.raw a (b₁ * b₂) = ctx.raw a b₁ * ctx.raw a b₂ := by
  have hord : ctx.ord (Additive.ofMul (b₁ * b₂)) =
      ctx.ord (Additive.ofMul b₁) + ctx.ord (Additive.ofMul b₂) :=
    ctx.ord.map_add _ _
  simp only [raw, hord, map_mul, mul_add, zpow_add, mul_zpow]
  ring_nf
  simp only [mul_assoc, mul_left_comm]

/-- Swapping the entries inverts the raw tame residue. -/
theorem raw_swap (ctx : Context p K k) (a b : Kˣ) :
    ctx.raw b a = (ctx.raw a b)⁻¹ := by
  rw [raw, raw, mul_comm (ctx.ord (Additive.ofMul b)),
    mul_inv_rev, mul_inv_rev, ← zpow_neg, ← zpow_neg, ← zpow_neg]
  have hsign : (-1 : kˣ) ^
      (-(ctx.ord (Additive.ofMul a) * ctx.ord (Additive.ofMul b))) =
        (-1 : kˣ) ^
          (ctx.ord (Additive.ofMul a) * ctx.ord (Additive.ofMul b)) := by
    rw [zpow_neg, ← inv_zpow]
    simp
  rw [hsign, neg_neg]
  simp only [mul_assoc, mul_left_comm, mul_comm]

/-- The `(q-1)/p` power of a residue unit is a `p`-th root of unity.

This is a small generic finite-field lemma missing from the current Mathlib
API in this bundled form. -/
theorem residue_power_pow_eq_one (ctx : Context p K k) (u : kˣ) :
    (u ^ ctx.tameExponent) ^ p = 1 := by
  change (u ^ ((Fintype.card k - 1) / p)) ^ p = 1
  rw [← pow_mul, Nat.div_mul_cancel ctx.card_sub_one_dvd]
  apply Units.ext
  simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
    (FiniteField.pow_card_sub_one_eq_one (u : k) (Units.ne_zero u))

/-- The `(q-1)/p` power as a homomorphism into the actual group `mu_p`. -/
def powerToRoots (ctx : Context p K k) : kˣ →* rootsOfUnity p k where
  toFun u := ⟨u ^ ctx.tameExponent, ctx.residue_power_pow_eq_one u⟩
  map_one' := by ext; simp
  map_mul' u v := by
    apply Subtype.ext
    exact mul_pow u v _

/-- Identify all `p`-th roots with the powers of the selected primitive root. -/
def rootsEquivZPowers (ctx : Context p K k) :
    rootsOfUnity p k ≃* Subgroup.zpowers ctx.primitiveRoot :=
  MulEquiv.subgroupCongr ctx.primitiveRoot_spec.zpowers_eq.symm

/-- The Teichmuller-style power-residue character, additively coordinated in
`ZMod p` by the chosen primitive root. -/
def residueCharacter (ctx : Context p K k) : Additive kˣ →+ ZMod p :=
  ctx.primitiveRoot_spec.zmodEquivZPowers.symm.toAddMonoidHom.comp
    (MonoidHom.toAdditive
      (ctx.rootsEquivZPowers.toMonoidHom.comp ctx.powerToRoots))

@[simp]
theorem residueCharacter_one (ctx : Context p K k) :
    ctx.residueCharacter (Additive.ofMul 1) = 0 :=
  map_zero _

@[simp]
theorem residueCharacter_mul (ctx : Context p K k) (u v : kˣ) :
    ctx.residueCharacter (Additive.ofMul (u * v)) =
      ctx.residueCharacter (Additive.ofMul u) +
        ctx.residueCharacter (Additive.ofMul v) :=
  map_add _ _ _

/-- The explicit tame Hilbert-symbol value in `ZMod p`. -/
def value (ctx : Context p K k) (a b : Kˣ) : ZMod p :=
  ctx.residueCharacter (Additive.ofMul (ctx.raw a b))

/-- Formula theorem retaining all three explicit stages: raw tame residue,
`(q-1)/p` power into `mu_p`, and primitive-root coordinates in `ZMod p`. -/
theorem value_eq_explicit_formula (ctx : Context p K k) (a b : Kˣ) :
    ctx.value a b =
      ctx.primitiveRoot_spec.zmodEquivZPowers.symm
        (Additive.ofMul
          (ctx.rootsEquivZPowers
            (ctx.powerToRoots (ctx.raw a b)))) :=
  rfl

@[simp]
theorem value_one_left (ctx : Context p K k) (b : Kˣ) :
    ctx.value 1 b = 0 := by
  simp [value]

@[simp]
theorem value_one_right (ctx : Context p K k) (a : Kˣ) :
    ctx.value a 1 = 0 := by
  simp [value]

/-- Bilinearity in the first variable. -/
theorem value_mul_left (ctx : Context p K k) (a₁ a₂ b : Kˣ) :
    ctx.value (a₁ * a₂) b = ctx.value a₁ b + ctx.value a₂ b := by
  rw [value, raw_mul_left, residueCharacter_mul]
  rfl

/-- Bilinearity in the second variable. -/
theorem value_mul_right (ctx : Context p K k) (a b₁ b₂ : Kˣ) :
    ctx.value a (b₁ * b₂) = ctx.value a b₁ + ctx.value a b₂ := by
  rw [value, raw_mul_right, residueCharacter_mul]
  rfl

/-- Antisymmetry of the additive tame Hilbert symbol. -/
theorem value_swap (ctx : Context p K k) (a b : Kˣ) :
    ctx.value b a = -ctx.value a b := by
  rw [value, raw_swap]
  exact map_neg ctx.residueCharacter (Additive.ofMul (ctx.raw a b))

/-- The symbol as a genuine bilinear homomorphism on multiplicative elements
written additively.  This is the statement shape used by the FLT project. -/
def toAddMonoidHom (ctx : Context p K k) :
    Additive Kˣ →+ (Additive Kˣ →+ ZMod p) where
  toFun a :=
    { toFun := fun b ↦ ctx.value (Additive.toMul a) (Additive.toMul b)
      map_zero' := ctx.value_one_right (Additive.toMul a)
      map_add' := fun b₁ b₂ ↦ ctx.value_mul_right
        (Additive.toMul a) (Additive.toMul b₁) (Additive.toMul b₂) }
  map_zero' := by
    ext b
    exact ctx.value_one_left (Additive.toMul b)
  map_add' a₁ a₂ := by
    ext b
    exact ctx.value_mul_left
      (Additive.toMul a₁) (Additive.toMul a₂) (Additive.toMul b)

@[simp]
theorem toAddMonoidHom_apply (ctx : Context p K k) (a b : Additive Kˣ) :
    ctx.toAddMonoidHom a b = ctx.value (Additive.toMul a) (Additive.toMul b) :=
  rfl

/-- The same bilinear symbol curried dual-first.

FLT PR 1110 uses the primal-first order of `toAddMonoidHom`, while the
Poitou--Tate statement layer in PR 1105 writes the local evaluation dual-first.
This named flip makes the two conventions definitionally alignable without
changing either mathematical argument. -/
def toAddMonoidHomDualFirst (ctx : Context p K k) :
    Additive Kˣ →+ (Additive Kˣ →+ ZMod p) where
  toFun b :=
    { toFun := fun a ↦ ctx.value (Additive.toMul a) (Additive.toMul b)
      map_zero' := ctx.value_one_left (Additive.toMul b)
      map_add' := fun a₁ a₂ ↦ ctx.value_mul_left
        (Additive.toMul a₁) (Additive.toMul a₂) (Additive.toMul b) }
  map_zero' := by
    ext a
    exact ctx.value_one_right (Additive.toMul a)
  map_add' b₁ b₂ := by
    ext a
    exact ctx.value_mul_right
      (Additive.toMul a) (Additive.toMul b₁) (Additive.toMul b₂)

@[simp]
theorem toAddMonoidHomDualFirst_apply
    (ctx : Context p K k) (b a : Additive Kˣ) :
    ctx.toAddMonoidHomDualFirst b a =
      ctx.value (Additive.toMul a) (Additive.toMul b) :=
  rfl

/-- Valuation-zero in both entries makes the raw tame residue one. -/
theorem raw_eq_one_of_ord_eq_zero (ctx : Context p K k) (a b : Kˣ)
    (ha : ctx.ord (Additive.ofMul a) = 0)
    (hb : ctx.ord (Additive.ofMul b) = 0) :
    ctx.raw a b = 1 := by
  simp [raw, ha, hb]

/-- **Both-units silence**: two valuation units have zero tame reading. -/
theorem both_units_silence (ctx : Context p K k) (a b : Kˣ)
    (ha : ctx.ord (Additive.ofMul a) = 0)
    (hb : ctx.ord (Additive.ofMul b) = 0) :
    ctx.value a b = 0 := by
  rw [value, ctx.raw_eq_one_of_ord_eq_zero a b ha hb]
  exact ctx.residueCharacter_one

/-- Alias emphasizing the valuation-bookkeeping form used at global tame
places. -/
theorem value_eq_zero_of_ord_eq_zero (ctx : Context p K k) (a b : Kˣ)
    (ha : ctx.ord (Additive.ofMul a) = 0)
    (hb : ctx.ord (Additive.ofMul b) = 0) :
    ctx.value a b = 0 :=
  ctx.both_units_silence a b ha hb

/-- If both valuations are divisible by `p`, the raw tame residue is itself a
`p`-th power.  The witness works uniformly, including `p = 2`. -/
theorem raw_eq_pth_power_of_p_dvd_ord (ctx : Context p K k) (a b : Kˣ)
    (ha : (p : ℤ) ∣ ctx.ord (Additive.ofMul a))
    (hb : (p : ℤ) ∣ ctx.ord (Additive.ofMul b)) :
    ∃ u : kˣ, ctx.raw a b = u ^ p := by
  obtain ⟨m, hm⟩ := ha
  obtain ⟨n, hn⟩ := hb
  refine ⟨(-1 : kˣ) ^ ((p : ℤ) * m * n) *
      ctx.angularComponent a ^ n * ctx.angularComponent b ^ (-m), ?_⟩
  simp only [raw, hm, hn]
  rw [← zpow_natCast, mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul,
    ← zpow_mul]
  congr 1 <;> ring

/-- Selmer-strength tame silence: it is enough that both valuations vanish
modulo `p`; literal valuation zero is not required. -/
theorem value_eq_zero_of_p_dvd_ord (ctx : Context p K k) (a b : Kˣ)
    (ha : (p : ℤ) ∣ ctx.ord (Additive.ofMul a))
    (hb : (p : ℤ) ∣ ctx.ord (Additive.ofMul b)) :
    ctx.value a b = 0 := by
  obtain ⟨u, hu⟩ := ctx.raw_eq_pth_power_of_p_dvd_ord a b ha hb
  rw [value, hu]
  change ctx.residueCharacter (p • Additive.ofMul u) = 0
  rw [map_nsmul]
  exact ZModModule.char_nsmul_eq_zero p _

/-! ## `p`-th-power invariance and descent to the Kummer quotient -/

/-- A `p`-th power in the first entry is silent. -/
theorem value_pow_left (ctx : Context p K k) (a b : Kˣ) (n : ℕ) :
    ctx.value (a ^ n) b = n • ctx.value a b := by
  change ctx.toAddMonoidHom (n • Additive.ofMul a) (Additive.ofMul b) = _
  rw [map_nsmul]
  rfl

/-- A `p`-th power in the second entry is silent. -/
theorem value_pow_right (ctx : Context p K k) (a b : Kˣ) (n : ℕ) :
    ctx.value a (b ^ n) = n • ctx.value a b := by
  change (ctx.toAddMonoidHom (Additive.ofMul a))
    (n • Additive.ofMul b) = _
  rw [map_nsmul]
  rfl

@[simp]
theorem value_pth_power_left (ctx : Context p K k) (a b : Kˣ) :
    ctx.value (a ^ p) b = 0 := by
  rw [ctx.value_pow_left a b p]
  exact ZModModule.char_nsmul_eq_zero p _

@[simp]
theorem value_pth_power_right (ctx : Context p K k) (a b : Kˣ) :
    ctx.value a (b ^ p) = 0 := by
  rw [ctx.value_pow_right a b p]
  exact ZModModule.char_nsmul_eq_zero p _

/-- Multiplicative packaging of one argument, used to invoke
`QuotientGroup.lift`. -/
def rightMonoidHom (ctx : Context p K k) (a : Kˣ) :
    Kˣ →* Multiplicative (ZMod p) :=
  AddMonoidHom.toMultiplicative (ctx.toAddMonoidHom (Additive.ofMul a))

/-- The valuation reduced modulo `p` on representatives. -/
def ordModPRep (ctx : Context p K k) : Additive Kˣ →+ ZMod p :=
  (Int.castAddHom (ZMod p)).comp ctx.ord

/-- The valuation modulo `p`, descended to the same Kummer quotient as the
tame symbol and Mathlib's Selmer group. -/
def ordModP (ctx : Context p K k) : KummerClass p K →+ ZMod p :=
  MonoidHom.toAdditive <|
    QuotientGroup.lift (powMonoidHom p : Kˣ →* Kˣ).range
      (AddMonoidHom.toMultiplicative ctx.ordModPRep) fun x hx ↦ by
        obtain ⟨y, rfl⟩ := hx
        change Multiplicative.ofAdd
          (ctx.ordModPRep (p • Additive.ofMul y)) = 1
        rw [map_nsmul, ZModModule.char_nsmul_eq_zero]
        rfl

@[simp]
theorem ordModP_mk (ctx : Context p K k) (a : Kˣ) :
    ctx.ordModP (Additive.ofMul (QuotientGroup.mk' _ a)) =
      (ctx.ord (Additive.ofMul a) : ZMod p) :=
  rfl

/-- The right-hand symbol descends through exactly Mathlib's Kummer quotient
`Kˣ / (Kˣ)^p`. -/
def rightModP (ctx : Context p K k) (a : Kˣ) :
    Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range →* Multiplicative (ZMod p) :=
  QuotientGroup.lift (powMonoidHom p : Kˣ →* Kˣ).range
    (ctx.rightMonoidHom a) fun x hx ↦ by
      obtain ⟨y, rfl⟩ := hx
      exact congr_arg Multiplicative.ofAdd (ctx.value_pth_power_right a y)

@[simp]
theorem rightModP_mk (ctx : Context p K k) (a b : Kˣ) :
    ctx.rightModP a (QuotientGroup.mk' _ b) =
      Multiplicative.ofAdd (ctx.value a b) :=
  QuotientGroup.lift_mk' _ _ _

/-- The right-descended symbol remains multiplicative in its first
representative. -/
def rightModPFamily (ctx : Context p K k) :
    Kˣ →* ((Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) →*
      Multiplicative (ZMod p)) where
  toFun := ctx.rightModP
  map_one' := by
    apply MonoidHom.ext
    intro q
    refine QuotientGroup.induction_on q ?_
    intro b
    change Multiplicative.ofAdd (ctx.value 1 b) = 1
    rw [ctx.value_one_left]
    rfl
  map_mul' a₁ a₂ := by
    apply MonoidHom.ext
    intro q
    refine QuotientGroup.induction_on q ?_
    intro b
    change Multiplicative.ofAdd (ctx.value (a₁ * a₂) b) =
      Multiplicative.ofAdd (ctx.value a₁ b + ctx.value a₂ b)
    rw [ctx.value_mul_left]

/-- Multiplicative bilinear descent in both variables. -/
def modPMul (ctx : Context p K k) :
    (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) →*
      ((Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) →*
        Multiplicative (ZMod p)) :=
  QuotientGroup.lift (powMonoidHom p : Kˣ →* Kˣ).range
    ctx.rightModPFamily fun x hx ↦ by
      obtain ⟨y, rfl⟩ := hx
      apply MonoidHom.ext
      intro q
      refine QuotientGroup.induction_on q ?_
      intro b
      change Multiplicative.ofAdd (ctx.value (y ^ p) b) = 1
      rw [ctx.value_pth_power_left]
      rfl

/-- The complete bilinear tame symbol on the same Kummer quotient used by
`IsDedekindDomain.selmerGroup`. -/
def modP (ctx : Context p K k) :
    KummerClass p K →+ (KummerClass p K →+ ZMod p) where
  toFun a := MonoidHom.toAdditive (ctx.modPMul (Additive.toMul a))
  map_zero' := by
    apply AddMonoidHom.ext
    intro b
    change (ctx.modPMul 1 (Additive.toMul b)).toAdd = 0
    rw [map_one]
    rfl
  map_add' a₁ a₂ := by
    apply AddMonoidHom.ext
    intro b
    change (ctx.modPMul
      (Additive.toMul a₁ * Additive.toMul a₂) (Additive.toMul b)).toAdd = _
    rw [map_mul]
    rfl

@[simp]
theorem modP_mk_mk (ctx : Context p K k) (a b : Kˣ) :
    ctx.modP
        (Additive.ofMul (QuotientGroup.mk' _ a))
        (Additive.ofMul (QuotientGroup.mk' _ b)) =
      ctx.value a b := by
  rfl

/-- Quotient-level Selmer silence.  This consumes exactly the additive form
of Mathlib's `valuationOfNeZeroMod = 1` membership condition and needs no
choice of normalized representative. -/
theorem modP_eq_zero_of_ordModP_eq_zero (ctx : Context p K k)
    (x y : KummerClass p K)
    (hx : ctx.ordModP x = 0) (hy : ctx.ordModP y = 0) :
    ctx.modP x y = 0 := by
  let a : Kˣ := (Additive.toMul x).out
  let b : Kˣ := (Additive.toMul y).out
  have hxa : Additive.ofMul (QuotientGroup.mk' _ a) = x := by
    exact congr_arg Additive.ofMul (QuotientGroup.out_eq' (Additive.toMul x))
  have hyb : Additive.ofMul (QuotientGroup.mk' _ b) = y := by
    exact congr_arg Additive.ofMul (QuotientGroup.out_eq' (Additive.toMul y))
  rw [← hxa, ctx.ordModP_mk] at hx
  rw [← hyb, ctx.ordModP_mk] at hy
  rw [← hxa, ← hyb, ctx.modP_mk_mk]
  apply ctx.value_eq_zero_of_p_dvd_ord
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hx
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hy

/-! ## Steinberg's relation -/

/-- The valuation/angular-component cases behind the usual proof of
`{a,1-a}=1`.

For a realized discrete valuation these four cases follow from the
ultrametric inequality and reduction to the residue field.  Packaging the
trichotomy separately keeps the generic algebra reusable until Mathlib gains
a bundled angular component. -/
inductive SteinbergValuationCases (ctx : Context p K k) (a b : Kˣ) : Prop
  | leftPositive
      (ha : 0 < ctx.ord (Additive.ofMul a))
      (hb : ctx.ord (Additive.ofMul b) = 0)
      (hac : ctx.angularComponent b = 1)
  | rightPositive
      (ha : ctx.ord (Additive.ofMul a) = 0)
      (hb : 0 < ctx.ord (Additive.ofMul b))
      (hac : ctx.angularComponent a = 1)
  | bothUnits
      (ha : ctx.ord (Additive.ofMul a) = 0)
      (hb : ctx.ord (Additive.ofMul b) = 0)
  | bothNegative
      (hord : ctx.ord (Additive.ofMul b) = ctx.ord (Additive.ofMul a))
      (hac : ctx.angularComponent b = -ctx.angularComponent a)

namespace SteinbergValuationCases

/-- The residue trichotomy is sufficient to make the raw Steinberg symbol
one.  This elementary angular-component lemma is a Mathlib-welcome piece. -/
theorem raw_eq_one {ctx : Context p K k} {a b : Kˣ}
    (h : SteinbergValuationCases ctx a b) : ctx.raw a b = 1 := by
  rcases h with ⟨ha, hb, hac⟩ | ⟨ha, hb, hac⟩ | ⟨ha, hb⟩ | ⟨hord, hac⟩
  · simp [raw, hb, hac]
  · simp [raw, ha, hac]
  · exact ctx.raw_eq_one_of_ord_eq_zero a b ha hb
  · let m := ctx.ord (Additive.ofMul a)
    have heven : Even (m * m - m) := by
      simpa [mul_sub_one] using Int.even_mul_pred_self m
    rw [raw, hord, hac]
    rw [show -ctx.angularComponent a =
      (-1 : kˣ) * ctx.angularComponent a by simp, mul_zpow,
      show ctx.ord (Additive.ofMul a) = m from rfl]
    calc
      (-1 : kˣ) ^ (m * m) * ctx.angularComponent a ^ m *
          ((-1 : kˣ) ^ (-m) * ctx.angularComponent a ^ (-m)) =
        (((-1 : kˣ) ^ (m * m)) * ((-1 : kˣ) ^ (-m))) *
          (ctx.angularComponent a ^ m * ctx.angularComponent a ^ (-m)) := by
            ac_rfl
      _ = (-1 : kˣ) ^ (m * m + -m) *
          ctx.angularComponent a ^ (m + -m) := by
            rw [zpow_add, zpow_add]
      _ = (-1 : kˣ) ^ (m * m - m) := by simp [sub_eq_add_neg]
      _ = 1 := heven.neg_one_zpow

/-- Any pair satisfying the standard valuation/residue cases has zero tame
symbol.  This theorem is purely algebraic and makes no claim that `b = 1-a`. -/
theorem steinberg_of_cases (ctx : Context p K k) (a b : Kˣ)
    (hcases : SteinbergValuationCases ctx a b) :
    ctx.value a b = 0 := by
  rw [value, hcases.raw_eq_one]
  exact ctx.residueCharacter_one

end SteinbergValuationCases

/-- The missing local realization behind Steinberg's relation.

For an actual unit `a` for which `1-a` is nonzero, a discrete valuation and
its angular component put the canonical unit `Units.mk0 (1-a)` into one of
`SteinbergValuationCases`.  Pinned Mathlib does not yet bundle the angular
component or prove this one-minus trichotomy, so it remains a named and
inspectable compatibility seam. -/
structure SteinbergRealization (ctx : Context p K k) where
  one_sub_cases : ∀ (a : Kˣ) (hOneSub : 1 - (a : K) ≠ 0),
    SteinbergValuationCases ctx a (Units.mk0 (1 - (a : K)) hOneSub)

/-- Steinberg's relation for the canonical nonzero pair `a, 1-a`.

Unlike `steinberg_of_cases`, this public surface genuinely uses the field
relation: the second unit is definitionally `Units.mk0 (1-a)`, and the named
local realization supplies its valuation/residue cases. -/
theorem steinberg (ctx : Context p K k)
    (realization : SteinbergRealization ctx) (a : Kˣ)
    (hOneSub : 1 - (a : K) ≠ 0) :
    ctx.value a (Units.mk0 (1 - (a : K)) hOneSub) = 0 :=
  SteinbergValuationCases.steinberg_of_cases ctx a _
    (realization.one_sub_cases a hOneSub)

/-! ## Galois equivariance and the adjoint shape -/

/-- Compatibility of a family of tame contexts with an action that may move
the place.  The residue fields are identified with `k` along the orbit; this
is the usual choice made before writing an explicit local symbol. -/
structure PlaceGaloisData
    {Place : Type uPlace} (contexts : Place → Context p K k)
    (Delta : Type uDelta) [CommGroup Delta] [MulAction Delta Place] where
  sourceAction : Delta →* MulAut Kˣ
  residueAction : Delta →* MulAut kˣ
  omega : Delta →* (ZMod p)ˣ
  ord_action : ∀ sigma v a,
    (contexts (sigma • v)).ord
        (Additive.ofMul (sourceAction sigma a)) =
      (contexts v).ord (Additive.ofMul a)
  angularComponent_action : ∀ sigma v a,
    (contexts (sigma • v)).angularComponent (sourceAction sigma a) =
      residueAction sigma ((contexts v).angularComponent a)
  residue_neg_one : ∀ sigma, residueAction sigma (-1) = -1
  residueCharacter_action : ∀ sigma v u,
    (contexts (sigma • v)).residueCharacter
        (Additive.ofMul (residueAction sigma u)) =
      (omega sigma : ZMod p) *
        (contexts v).residueCharacter (Additive.ofMul u)

namespace PlaceGaloisData

variable {Place : Type uPlace} {Delta : Type uDelta}
  [CommGroup Delta] [MulAction Delta Place]

/-- The raw tame formula is equivariant while the place moves. -/
theorem raw_place_action (contexts : Place → Context p K k)
    (data : PlaceGaloisData contexts Delta)
    (sigma : Delta) (v : Place) (a b : Kˣ) :
    (contexts (sigma • v)).raw
        (data.sourceAction sigma a) (data.sourceAction sigma b) =
      data.residueAction sigma ((contexts v).raw a b) := by
  simp only [raw, data.ord_action, data.angularComponent_action]
  rw [map_mul, map_mul, map_zpow, map_zpow, map_zpow,
    data.residue_neg_one]

/-- Honest moved-place Galois equivariance:
`(sigma a, sigma b)_(sigma v) = omega(sigma) (a,b)_v`. -/
theorem value_place_galois_equivariant
    (contexts : Place → Context p K k)
    (data : PlaceGaloisData contexts Delta)
    (sigma : Delta) (v : Place) (a b : Kˣ) :
    (contexts (sigma • v)).value
        (data.sourceAction sigma a) (data.sourceAction sigma b) =
      (data.omega sigma : ZMod p) * (contexts v).value a b := by
  rw [value, data.raw_place_action, data.residueCharacter_action]
  rfl

end PlaceGaloisData

/-- Compatibility data for an action at a tame place.

The last field is the primitive-root coordinate form of
`sigma(zeta) = zeta ^ omega(sigma)`.  It is deliberately stated for the
already explicit residue character, avoiding any cohomological interface.
This is the fixed-place (decomposition-group/stabilizer) specialization of
`PlaceGaloisData`. -/
structure GaloisData (ctx : Context p K k) (Delta : Type uDelta)
    [CommGroup Delta] where
  sourceAction : Delta →* MulAut Kˣ
  residueAction : Delta →* MulAut kˣ
  omega : Delta →* (ZMod p)ˣ
  ord_action : ∀ sigma a,
    ctx.ord (Additive.ofMul (sourceAction sigma a)) =
      ctx.ord (Additive.ofMul a)
  angularComponent_action : ∀ sigma a,
    ctx.angularComponent (sourceAction sigma a) =
      residueAction sigma (ctx.angularComponent a)
  residue_neg_one : ∀ sigma, residueAction sigma (-1) = -1
  residueCharacter_action : ∀ sigma u,
    ctx.residueCharacter (Additive.ofMul (residueAction sigma u)) =
      (omega sigma : ZMod p) *
        ctx.residueCharacter (Additive.ofMul u)

namespace GaloisData

variable {Delta : Type uDelta} [CommGroup Delta]

/-- The raw formula commutes with the residue action. -/
theorem raw_action (ctx : Context p K k) (data : GaloisData ctx Delta)
    (sigma : Delta) (a b : Kˣ) :
    ctx.raw (data.sourceAction sigma a) (data.sourceAction sigma b) =
      data.residueAction sigma (ctx.raw a b) := by
  simp only [raw, data.ord_action, data.angularComponent_action]
  rw [map_mul, map_mul, map_zpow, map_zpow, map_zpow,
    data.residue_neg_one]

/-- Galois equivariance of the tame Hilbert symbol. -/
theorem value_galois_equivariant
    (ctx : Context p K k) (data : GaloisData ctx Delta)
    (sigma : Delta) (a b : Kˣ) :
    ctx.value (data.sourceAction sigma a) (data.sourceAction sigma b) =
      (data.omega sigma : ZMod p) * ctx.value a b := by
  rw [value, data.raw_action, data.residueCharacter_action]
  rfl

/-- The pointwise `omega(sigma) * sigma⁻¹` adjoint law.  Extending this
identity linearly over the group algebra gives exactly the
`InvolutiveBase.hash` adjoint shape used by `PlaceIndexedLocalPairing`. -/
theorem value_action_adjoint
    (ctx : Context p K k) (data : GaloisData ctx Delta)
    (sigma : Delta) (a b : Kˣ) :
    ctx.value (data.sourceAction sigma a) b =
      ctx.value a
        ((data.sourceAction sigma⁻¹ b) ^ (data.omega sigma : ZMod p).val) := by
  have heq := data.value_galois_equivariant ctx sigma a
    (data.sourceAction sigma⁻¹ b)
  have hcancel : data.sourceAction sigma (data.sourceAction sigma⁻¹ b) = b := by
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      MulAut.one_apply]
  rw [hcancel] at heq
  rw [ctx.value_pow_right]
  calc
    ctx.value (data.sourceAction sigma a) b =
        (data.omega sigma : ZMod p) *
          ctx.value a (data.sourceAction sigma⁻¹ b) := heq
    _ = (data.omega sigma : ZMod p).val •
          ctx.value a (data.sourceAction sigma⁻¹ b) := by
      rw [nsmul_eq_mul, ZMod.natCast_zmod_val]

end GaloisData

end Context

end Fermat.Conservation.TameSymbol
