/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Transport of explicit tame symbols across residue-field equivalences

The explicit tame symbol is independent of the presentation chosen for its
finite residue field.  This file proves that invariance from the actual
power-residue coordinate: a residue-field equivalence transports the angular
component and primitive root, and leaves the resulting `ZMod p` value fixed.

This is a genuine comparison theorem.  It introduces no local or global
reciprocity assumption and no chosen symbol value.
-/
import Fermat.Conservation.TameSymbol

noncomputable section

namespace Fermat.Conservation.TameSymbol.Context

universe uK uk ul

variable {p : ℕ} [Fact p.Prime]
  {K : Type uK} {k : Type uk} {l : Type ul}
  [Field K] [Fintype k] [Field k] [Fintype l] [Field l]

lemma card_eq_of_ringEquiv (e : k ≃+* l) :
    Fintype.card k = Fintype.card l :=
  Fintype.card_congr e.toEquiv

/-- Raising the chosen primitive root to the finite-logarithm coordinate
recovers the powered residue represented by that coordinate. -/
lemma primitiveRoot_pow_residueCharacter_val
    (ctx : Context p K k) (u : kˣ) :
    ctx.primitiveRoot ^
        (ctx.residueCharacter (Additive.ofMul u)).val =
      u ^ ctx.tameExponent := by
  let root : rootsOfUnity p k := ctx.powerToRoots u
  let power : Subgroup.zpowers ctx.primitiveRoot := ctx.rootsEquivZPowers root
  let coordinate : ZMod p :=
    ctx.primitiveRoot_spec.zmodEquivZPowers.symm (Additive.ofMul power)
  have h := ctx.primitiveRoot_spec.zmodEquivZPowers.apply_symm_apply
    (Additive.ofMul power)
  change ctx.primitiveRoot_spec.zmodEquivZPowers coordinate =
      Additive.ofMul power at h
  rw [← ZMod.natCast_zmod_val coordinate,
    IsPrimitiveRoot.zmodEquivZPowers_apply_coe_nat] at h
  have hval : ctx.primitiveRoot ^ coordinate.val = power.1 := by
    exact congrArg (fun x ↦ (Additive.toMul x).1) h
  change ctx.primitiveRoot ^ coordinate.val = u ^ ctx.tameExponent
  rw [hval]
  rfl

/-- Primitive-root coordinates commute with a residue-field equivalence. -/
lemma residueCharacter_map_ringEquiv
    (ctx : Context p K k) (e : k ≃+* l)
    (ctx' : Context p K l)
    (hprimitive : Units.map e.toRingHom ctx.primitiveRoot = ctx'.primitiveRoot)
    (u : kˣ) :
    ctx'.residueCharacter (Additive.ofMul (Units.map e.toRingHom u)) =
      ctx.residueCharacter (Additive.ofMul u) := by
  let c' : ZMod p := ctx'.residueCharacter
    (Additive.ofMul (Units.map e.toRingHom u))
  let c : ZMod p := ctx.residueCharacter (Additive.ofMul u)
  apply ZMod.val_injective p
  have hleft := primitiveRoot_pow_residueCharacter_val ctx'
    (Units.map e.toRingHom u)
  have hright := primitiveRoot_pow_residueCharacter_val ctx u
  change ctx'.primitiveRoot ^ c'.val = _ at hleft
  change ctx.primitiveRoot ^ c.val = _ at hright
  have htame : ctx'.tameExponent = ctx.tameExponent := by
    unfold tameExponent
    change (Fintype.card l - 1) / p = (Fintype.card k - 1) / p
    rw [← card_eq_of_ringEquiv e]
  have hpow : ctx'.primitiveRoot ^ c'.val =
      ctx'.primitiveRoot ^ c.val := by
    calc
      ctx'.primitiveRoot ^ c'.val =
          (Units.map e.toRingHom u) ^ ctx'.tameExponent := hleft
      _ = (Units.map e.toRingHom u) ^ ctx.tameExponent := by rw [htame]
      _ = Units.map e.toRingHom (u ^ ctx.tameExponent) := by rw [map_pow]
      _ = Units.map e.toRingHom (ctx.primitiveRoot ^ c.val) := by rw [hright]
      _ = (Units.map e.toRingHom ctx.primitiveRoot) ^ c.val := by rw [map_pow]
      _ = ctx'.primitiveRoot ^ c.val := by rw [hprimitive]
  exact pow_injOn_Iio_orderOf
    (by
      exact (ZMod.val_lt c').trans_eq
        ctx'.primitiveRoot_spec.eq_orderOf)
    (by
      exact (ZMod.val_lt c).trans_eq
        ctx'.primitiveRoot_spec.eq_orderOf)
    hpow

/-- If a second context uses the `m`-th power of the first context's
primitive root, its finite-logarithm coordinate is rescaled by `m`.

The multiplication is kept on the left-hand side, so this theorem does not
need a separate coprimality premise: primitivity of both stored roots already
contains that information. -/
lemma residueCharacter_primitiveRoot_pow
    (ctx ctx' : Context p K k) (m : ℕ)
    (hprimitive : ctx'.primitiveRoot = ctx.primitiveRoot ^ m)
    (u : kˣ) :
    (m : ZMod p) * ctx'.residueCharacter (Additive.ofMul u) =
      ctx.residueCharacter (Additive.ofMul u) := by
  let c' : ZMod p := ctx'.residueCharacter (Additive.ofMul u)
  let c : ZMod p := ctx.residueCharacter (Additive.ofMul u)
  have hleft := primitiveRoot_pow_residueCharacter_val ctx' u
  have hright := primitiveRoot_pow_residueCharacter_val ctx u
  change ctx'.primitiveRoot ^ c'.val = _ at hleft
  change ctx.primitiveRoot ^ c.val = _ at hright
  have htame : ctx'.tameExponent = ctx.tameExponent := rfl
  have hpow : ctx.primitiveRoot ^ (m * c'.val) =
      ctx.primitiveRoot ^ c.val := by
    rw [pow_mul, ← hprimitive, hleft, htame, hright]
  have hmod : m * c'.val ≡ c.val [MOD p] := by
    have hmod' : m * c'.val ≡ c.val
        [MOD orderOf ctx.primitiveRoot] :=
      pow_eq_pow_iff_modEq.mp hpow
    rwa [← ctx.primitiveRoot_spec.eq_orderOf] at hmod'
  have hz : ((m * c'.val : ℕ) : ZMod p) = (c.val : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  calc
    (m : ZMod p) * c' =
        (m : ZMod p) * (c'.val : ZMod p) := by
          rw [ZMod.natCast_zmod_val]
    _ = ((m * c'.val : ℕ) : ZMod p) := by rw [Nat.cast_mul]
    _ = (c.val : ZMod p) := hz
    _ = c := ZMod.natCast_zmod_val c

/-- The raw tame residue commutes with a residue-field equivalence whenever
the valuation and angular component do. -/
lemma raw_map_ringEquiv
    (ctx : Context p K k) (e : k ≃+* l)
    (ctx' : Context p K l)
    (hord : ctx'.ord = ctx.ord)
    (hangular : ∀ a, ctx'.angularComponent a =
      Units.map e.toRingHom (ctx.angularComponent a))
    (a b : Kˣ) :
    ctx'.raw a b = Units.map e.toRingHom (ctx.raw a b) := by
  rw [raw, raw]
  rw [hord]
  simp only [hangular, map_mul, map_zpow]
  rw [show Units.map e.toRingHom (-1 : kˣ) = (-1 : lˣ) by
    ext
    simp]

/-- Changing only the primitive-root coordinate by an `m`-th power rescales
the complete tame-symbol value by `m`. -/
lemma value_primitiveRoot_pow
    (ctx ctx' : Context p K k) (m : ℕ)
    (hord : ctx'.ord = ctx.ord)
    (hangular : ctx'.angularComponent = ctx.angularComponent)
    (hprimitive : ctx'.primitiveRoot = ctx.primitiveRoot ^ m)
    (a b : Kˣ) :
    (m : ZMod p) * ctx'.value a b = ctx.value a b := by
  have hraw : ctx'.raw a b = ctx.raw a b := by
    rw [raw, raw, hord, hangular]
  rw [value, value, hraw]
  exact residueCharacter_primitiveRoot_pow ctx ctx' m hprimitive _

/-- The additive explicit tame Hilbert symbol is invariant under an honest
change of residue-field presentation. -/
theorem value_eq_of_residue_equiv
    (ctx : Context p K k) (e : k ≃+* l)
    (ctx' : Context p K l)
    (hord : ctx'.ord = ctx.ord)
    (hangular : ∀ a, ctx'.angularComponent a =
      Units.map e.toRingHom (ctx.angularComponent a))
    (hprimitive : Units.map e.toRingHom ctx.primitiveRoot = ctx'.primitiveRoot)
    (a b : Kˣ) :
    ctx'.value a b = ctx.value a b := by
  rw [value, value, raw_map_ringEquiv ctx e ctx' hord hangular]
  exact residueCharacter_map_ringEquiv ctx e ctx' hprimitive _

end Fermat.Conservation.TameSymbol.Context
