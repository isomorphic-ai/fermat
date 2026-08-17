/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Transport and pullback of Kummer classes

A ring homomorphism between fields maps nonzero elements to nonzero elements,
and maps `p`-th powers to `p`-th powers.  It therefore induces a canonical
additive homomorphism on the Kummer quotients

`Kˣ / (Kˣ)^p → Fˣ / (Fˣ)^p`.

This file implements that mechanical transport directly.  It also pulls a
quotient-level local Kummer pairing back along the transport in both
variables.  No local-symbol formula, reciprocity law, or cohomological
interpretation is assumed here.
-/
import Fermat.Conservation.WildKummerPairing

noncomputable section

namespace Fermat.Conservation.LocalKummerTransport

open Fermat.Conservation.TameSymbol
open Fermat.Conservation.WildKummerPairing

universe uK uF uE

variable {p : ℕ}
  {K : Type uK} [Field K]
  {F : Type uF} [Field F]
  {E : Type uE} [Field E]

/-- The map on nonzero elements induced by a ring homomorphism of fields. -/
def unitMap (f : K →+* F) : Kˣ →* Fˣ :=
  Units.map f.toMonoidHom

@[simp]
theorem unitMap_apply (f : K →+* F) (a : Kˣ) :
    (unitMap f a : F) = f a :=
  rfl

/-- Mapping nonzero elements carries `p`-th powers to `p`-th powers. -/
theorem unitMap_powerSubgroup_le (f : K →+* F) :
    (powMonoidHom p : Kˣ →* Kˣ).range ≤
      ((powMonoidHom p : Fˣ →* Fˣ).range).comap (unitMap f) := by
  rintro _ ⟨a, rfl⟩
  exact ⟨unitMap f a, by simp [unitMap, powMonoidHom_apply]⟩

/-- Multiplicative transport on quotients by `p`-th powers. -/
def mapMul (p : ℕ) (f : K →+* F) :
    (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) →*
      (Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range) :=
  QuotientGroup.map
    (powMonoidHom p : Kˣ →* Kˣ).range
    (powMonoidHom p : Fˣ →* Fˣ).range
    (unitMap f) (unitMap_powerSubgroup_le (p := p) f)

@[simp]
theorem mapMul_mk (f : K →+* F) (a : Kˣ) :
    mapMul p f (QuotientGroup.mk' _ a) =
      QuotientGroup.mk' _ (unitMap f a) :=
  rfl

/-- Additive transport of Kummer classes along a ring homomorphism of fields. -/
def map (p : ℕ) (f : K →+* F) :
    KummerClass p K →+ KummerClass p F :=
  MonoidHom.toAdditive (mapMul p f)

@[simp]
theorem map_classOfUnit (f : K →+* F) (a : Kˣ) :
    map p f (classOfUnit p K (Additive.ofMul a)) =
      classOfUnit p F (Additive.ofMul (unitMap f a)) :=
  rfl

/-- Kummer transport along the identity is the identity. -/
@[simp]
theorem map_id :
    map p (RingHom.id K) = AddMonoidHom.id (KummerClass p K) := by
  apply AddMonoidHom.ext
  rintro ⟨a⟩
  rfl

/-- Kummer transport respects composition of ring homomorphisms. -/
@[simp]
theorem map_comp (f : K →+* F) (g : F →+* E) :
    map p (g.comp f) = (map p g).comp (map p f) := by
  apply AddMonoidHom.ext
  rintro ⟨a⟩
  rfl

namespace Pairing

/-- Pull a local quotient-level Kummer pairing back along a field map in both
variables. -/
def pullback (f : K →+* F)
    (localPairing : WildKummerPairing.Pairing p F) :
    WildKummerPairing.Pairing p K where
  toFun x := (localPairing (map p f x)).comp (map p f)
  map_zero' := by
    ext y
    simp
  map_add' x₁ x₂ := by
    ext y
    simp

@[simp]
theorem pullback_apply (f : K →+* F)
    (localPairing : WildKummerPairing.Pairing p F)
    (x y : KummerClass p K) :
    pullback f localPairing x y =
      localPairing (map p f x) (map p f y) :=
  rfl

@[simp]
theorem pullback_classOfUnit (f : K →+* F)
    (localPairing : WildKummerPairing.Pairing p F) (a b : Kˣ) :
    pullback f localPairing
        (classOfUnit p K (Additive.ofMul a))
        (classOfUnit p K (Additive.ofMul b)) =
      localPairing
        (classOfUnit p F (Additive.ofMul (unitMap f a)))
        (classOfUnit p F (Additive.ofMul (unitMap f b))) :=
  rfl

/-- Pulling back along the identity does not change a pairing. -/
@[simp]
theorem pullback_id (localPairing : WildKummerPairing.Pairing p K) :
    pullback (RingHom.id K) localPairing = localPairing := by
  ext x y
  simp

/-- Iterated pullback agrees with pullback along the composite map. -/
@[simp]
theorem pullback_comp (f : K →+* F) (g : F →+* E)
    (localPairing : WildKummerPairing.Pairing p E) :
    pullback f (pullback g localPairing) =
      pullback (g.comp f) localPairing := by
  ext x y
  simp

end Pairing

end Fermat.Conservation.LocalKummerTransport
