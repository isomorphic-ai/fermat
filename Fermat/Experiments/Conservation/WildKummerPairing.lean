/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Constructor-facing wild Kummer pairings

This file isolates the algebraic surface that an explicit wild-symbol
construction must provide.  It deliberately does **not** claim that pinned
Mathlib contains the completed Laurent-series calculus needed by the
Brueckner--Vostokov formula.  In particular, no residue formula or local
reciprocity theorem is postulated here.

The main structure, `WildKummerPairing.Core`, records a total bilinear pairing
on the same Kummer quotient used by Mathlib's Selmer groups, together with an
honest representative-level pairing and a receipt that the latter descends.
`ofRepresentative` proves that any bilinear representative pairing with
values in `ZMod p` has the required `p`-power silence and therefore descends.

`IsGaloisEquivariant` and `GaloisData` name precisely the extra arithmetic law
needed to obtain the pointwise cyclotomic adjoint identity.  The separate
`IsArtinHasseCalibrated` predicate lets an instance record agreement with an
independently banked family of Artin--Hasse values without pretending that
those values are constructed in this generic module.

Steinberg, norm-residue, and reciprocity laws are intentionally absent: the
current wild localization consumer needs neither Steinberg nor norm silence,
and reciprocity remains an external interface in the conservation tree.
-/
import Fermat.Experiments.Conservation.TameSymbol

noncomputable section

namespace Fermat.Conservation.WildKummerPairing

universe uK uDelta uLeft uRight

open Fermat.Conservation.TameSymbol

variable {p : ℕ} [Fact p.Prime]
  {K : Type uK} [Field K]

/-- A bilinear pairing before quotienting nonzero elements by `p`-th powers.

This is the appropriate output type for a future integral residue formula.
The additive wrappers turn multiplication of representatives into addition,
so bilinearity is carried by the two bundled homomorphisms. -/
abbrev RepresentativePairing (p : ℕ) (K : Type uK) [Field K] :=
  Additive Kˣ →+ (Additive Kˣ →+ ZMod p)

/-- A total bilinear wild pairing on Kummer classes. -/
abbrev Pairing (p : ℕ) (K : Type uK) [Field K] :=
  KummerClass p K →+ (KummerClass p K →+ ZMod p)

/-- The canonical class of a nonzero representative in the Kummer quotient. -/
def classOfUnit (p : ℕ) (K : Type uK) [Field K] :
    Additive Kˣ →+ KummerClass p K :=
  MonoidHom.toAdditive
    (QuotientGroup.mk' (powMonoidHom p : Kˣ →* Kˣ).range)

omit [Fact p.Prime] in
@[simp]
theorem classOfUnit_apply (a : Kˣ) :
    classOfUnit p K (Additive.ofMul a) =
      Additive.ofMul (QuotientGroup.mk' _ a) :=
  rfl

omit [Fact p.Prime] in
/-- Every Kummer class has a nonzero representative. -/
theorem classOfUnit_surjective :
    Function.Surjective (classOfUnit p K) := by
  intro x
  refine ⟨Additive.ofMul (Additive.toMul x).out, ?_⟩
  apply Additive.ext
  exact QuotientGroup.out_eq' (Additive.toMul x)

/-- Pull a quotient-level pairing back to nonzero representatives. -/
def Pairing.onRepresentatives (pairing : Pairing p K) :
    RepresentativePairing p K where
  toFun a := (pairing (classOfUnit p K a)).comp (classOfUnit p K)
  map_zero' := by
    ext b
    simp
  map_add' a₁ a₂ := by
    ext b
    simp

@[simp]
theorem Pairing.onRepresentatives_apply
    (pairing : Pairing p K) (a b : Additive Kˣ) :
    pairing.onRepresentatives a b =
      pairing (classOfUnit p K a) (classOfUnit p K b) :=
  rfl

/-- Representative-level `p`-power silence in both variables.

For a genuinely bilinear pairing with target `ZMod p`, this is formal rather
than additional arithmetic data; see `isPPowerSilent`. -/
def IsPPowerSilent (representative : RepresentativePairing p K) : Prop :=
  (∀ a b, representative (p • a) b = 0) ∧
    ∀ a b, representative a (p • b) = 0

/-- Every bilinear `ZMod p`-valued representative pairing kills `p`-th
powers. -/
theorem isPPowerSilent (representative : RepresentativePairing p K) :
    IsPPowerSilent representative := by
  constructor
  · intro a b
    rw [map_nsmul, ZModModule.char_nsmul_eq_zero]
    rfl
  · intro a b
    rw [map_nsmul, ZModModule.char_nsmul_eq_zero]

/-- A quotient pairing realizes a representative formula.

This is the inspectable descent receipt: it identifies every value on chosen
representatives, rather than merely asserting that some quotient map exists. -/
def IsKummerDescent (representative : RepresentativePairing p K)
    (pairing : Pairing p K) : Prop :=
  ∀ a b, pairing (classOfUnit p K a) (classOfUnit p K b) =
    representative a b

namespace RepresentativePairing

/-- Multiplicative packaging of the second variable, used for its Kummer
quotient lift. -/
private def rightMonoidHom (representative : RepresentativePairing p K)
    (a : Additive Kˣ) : Kˣ →* Multiplicative (ZMod p) :=
  AddMonoidHom.toMultiplicative (representative a)

/-- Descend the second variable through `Kˣ / (Kˣ)^p`. -/
private def rightModP (representative : RepresentativePairing p K)
    (a : Additive Kˣ) :
    Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range →*
      Multiplicative (ZMod p) :=
  QuotientGroup.lift (powMonoidHom p : Kˣ →* Kˣ).range
    (representative.rightMonoidHom a) fun x hx ↦ by
      obtain ⟨y, rfl⟩ := hx
      change Multiplicative.ofAdd
        (representative a (p • Additive.ofMul y)) = 1
      rw [map_nsmul, ZModModule.char_nsmul_eq_zero]
      rfl

@[simp]
private theorem rightModP_mk (representative : RepresentativePairing p K)
    (a : Additive Kˣ) (b : Kˣ) :
    representative.rightModP a (QuotientGroup.mk' _ b) =
      Multiplicative.ofAdd (representative a (Additive.ofMul b)) :=
  QuotientGroup.lift_mk' _ _ _

/-- The right-descended family remains multiplicative in the first
representative. -/
private def rightModPFamily (representative : RepresentativePairing p K) :
    Kˣ →* ((Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) →*
      Multiplicative (ZMod p)) where
  toFun a := representative.rightModP (Additive.ofMul a)
  map_one' := by
    apply MonoidHom.ext
    intro q
    refine QuotientGroup.induction_on q ?_
    intro b
    change Multiplicative.ofAdd
      (representative 0 (Additive.ofMul b)) = 1
    rw [map_zero]
    rfl
  map_mul' a₁ a₂ := by
    apply MonoidHom.ext
    intro q
    refine QuotientGroup.induction_on q ?_
    intro b
    change Multiplicative.ofAdd
      (representative
        (Additive.ofMul a₁ + Additive.ofMul a₂)
        (Additive.ofMul b)) =
      Multiplicative.ofAdd
        (representative (Additive.ofMul a₁) (Additive.ofMul b) +
          representative (Additive.ofMul a₂) (Additive.ofMul b))
    rw [map_add]
    rfl

/-- Multiplicative descent through the Kummer quotient in both variables. -/
private def descendMul (representative : RepresentativePairing p K) :
    (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) →*
      ((Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) →*
        Multiplicative (ZMod p)) :=
  QuotientGroup.lift (powMonoidHom p : Kˣ →* Kˣ).range
    representative.rightModPFamily fun x hx ↦ by
      obtain ⟨y, rfl⟩ := hx
      apply MonoidHom.ext
      intro q
      refine QuotientGroup.induction_on q ?_
      intro b
      change Multiplicative.ofAdd
        (representative (p • Additive.ofMul y) (Additive.ofMul b)) = 1
      rw [map_nsmul, ZModModule.char_nsmul_eq_zero]
      rfl

/-- Any bilinear representative pairing descends canonically to a total
pairing on Kummer classes. -/
def descend (representative : RepresentativePairing p K) : Pairing p K where
  toFun a := MonoidHom.toAdditive
    (representative.descendMul (Additive.toMul a))
  map_zero' := by
    apply AddMonoidHom.ext
    intro b
    change (representative.descendMul 1 (Additive.toMul b)).toAdd = 0
    rw [map_one]
    rfl
  map_add' a₁ a₂ := by
    apply AddMonoidHom.ext
    intro b
    change (representative.descendMul
      (Additive.toMul a₁ * Additive.toMul a₂)
      (Additive.toMul b)).toAdd = _
    rw [map_mul]
    rfl

@[simp]
theorem descend_classOfUnit_classOfUnit
    (representative : RepresentativePairing p K) (a b : Additive Kˣ) :
    representative.descend (classOfUnit p K a) (classOfUnit p K b) =
      representative a b := by
  rfl

/-- The canonical quotient construction carries its representative-level
descent receipt. -/
theorem isKummerDescent_descend
    (representative : RepresentativePairing p K) :
    IsKummerDescent representative representative.descend :=
  representative.descend_classOfUnit_classOfUnit

end RepresentativePairing

namespace Pairing

/-- Descending the representative pullback of a quotient-level pairing
recovers the original pairing.

This is the quotient-first adapter: a construction naturally defined on
Kummer classes can pass through representative-biased consumers without a
new arithmetic comparison theorem. -/
@[simp]
theorem descend_onRepresentatives (pairing : Pairing p K) :
    pairing.onRepresentatives.descend = pairing := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨a, rfl⟩ := classOfUnit_surjective (p := p) (K := K) x
  apply AddMonoidHom.ext
  intro y
  obtain ⟨b, rfl⟩ := classOfUnit_surjective (p := p) (K := K) y
  rfl

/-- Pointwise form of `descend_onRepresentatives`. -/
@[simp]
theorem descend_onRepresentatives_apply (pairing : Pairing p K)
    (x y : KummerClass p K) :
    pairing.onRepresentatives.descend x y = pairing x y := by
  rw [pairing.descend_onRepresentatives]

end Pairing

/-- Constructor-facing arithmetic core for a total wild Kummer pairing.

An inhabitant must provide a representative-level definition, a total
quotient pairing, and their descent receipt.  This structure does not assert
that a Vostokov formula, a localization map, or local reciprocity has already
been constructed. -/
structure Core (p : ℕ) [Fact p.Prime]
    (K : Type uK) [Field K] where
  representative : RepresentativePairing p K
  pairing : Pairing p K
  descent : IsKummerDescent representative pairing

namespace Core

/-- Package a representative formula using the canonical algebraic descent. -/
def ofRepresentative (representative : RepresentativePairing p K) : Core p K where
  representative := representative
  pairing := representative.descend
  descent := representative.isKummerDescent_descend

/-- Package a quotient-level pairing by pulling it back to representatives.

Unlike `ofRepresentative`, this constructor preserves the supplied quotient
pairing definitionally.  Its representative field is only the canonical
readback along `classOfUnit`. -/
def ofPairing (pairing : Pairing p K) : Core p K where
  representative := pairing.onRepresentatives
  pairing := pairing
  descent := fun _ _ ↦ rfl

@[simp]
theorem ofRepresentative_pairing_apply
    (representative : RepresentativePairing p K) (x y : KummerClass p K) :
    (ofRepresentative representative).pairing x y =
      representative.descend x y :=
  rfl

@[simp]
theorem ofPairing_pairing_apply
    (pairing : Pairing p K) (x y : KummerClass p K) :
    (ofPairing pairing).pairing x y = pairing x y :=
  rfl

@[simp]
theorem ofPairing_representative_apply
    (pairing : Pairing p K) (a b : Additive Kˣ) :
    (ofPairing pairing).representative a b =
      pairing (classOfUnit p K a) (classOfUnit p K b) :=
  rfl

@[simp]
theorem ofPairing_pairing (pairing : Pairing p K) :
    (ofPairing pairing).pairing = pairing :=
  rfl

@[simp]
theorem ofPairing_representative (pairing : Pairing p K) :
    (ofPairing pairing).representative = pairing.onRepresentatives :=
  rfl

@[simp]
theorem pairing_classOfUnit_classOfUnit (core : Core p K)
    (a b : Additive Kˣ) :
    core.pairing (classOfUnit p K a) (classOfUnit p K b) =
      core.representative a b :=
  core.descent a b

end Core

/-! ## Galois equivariance and the pointwise adjoint law -/

/-- Cyclotomic Galois equivariance of a total Kummer pairing.

The action is kept as an ordinary `DistribMulAction` on Kummer classes.  A
local realization may obtain it by descending field automorphisms, but this
generic predicate does not choose such a realization. -/
def IsGaloisEquivariant (pairing : Pairing p K)
    (Delta : Type uDelta) [CommGroup Delta]
    [DistribMulAction Delta (KummerClass p K)]
    (omega : Delta →* (ZMod p)ˣ) : Prop :=
  ∀ sigma x y,
    pairing (sigma • x) (sigma • y) =
      (omega sigma : ZMod p) * pairing x y

/-- Equivariance data attached to a wild Kummer pairing core. -/
structure GaloisData (core : Core p K)
    (Delta : Type uDelta) [CommGroup Delta]
    [DistribMulAction Delta (KummerClass p K)] where
  omega : Delta →* (ZMod p)ˣ
  equivariant : IsGaloisEquivariant core.pairing Delta omega

namespace GaloisData

variable {Delta : Type uDelta} [CommGroup Delta]
  [DistribMulAction Delta (KummerClass p K)]

/-- The pointwise `omega(sigma) * sigma⁻¹` adjoint law.

This is the exact group-element identity that a later group-algebra assembly
can extend linearly to the `InvolutiveBase.hash` adjoint law. -/
theorem action_adjoint (core : Core p K) (data : GaloisData core Delta)
    (sigma : Delta) (x y : KummerClass p K) :
    core.pairing (sigma • x) y =
      core.pairing x
        ((data.omega sigma : ZMod p).val • (sigma⁻¹ • y)) := by
  have heq := data.equivariant sigma x (sigma⁻¹ • y)
  rw [smul_inv_smul] at heq
  rw [map_nsmul]
  calc
    core.pairing (sigma • x) y =
        (data.omega sigma : ZMod p) *
          core.pairing x (sigma⁻¹ • y) := heq
    _ = (data.omega sigma : ZMod p).val •
          core.pairing x (sigma⁻¹ • y) := by
      rw [nsmul_eq_mul, ZMod.natCast_zmod_val]

end GaloisData

/-! ## Artin--Hasse calibration -/

/-- Agreement with an independently banked family of Artin--Hasse values.

The indices and class maps are intentionally generic: the 59-specific bank
belongs in the instance layer.  This predicate is a calibration receipt only;
it neither defines `bankedValue` nor re-derives any Artin--Hasse class. -/
def IsArtinHasseCalibrated (core : Core p K)
    {Left : Type uLeft} {Right : Type uRight}
    (leftClass : Left → KummerClass p K)
    (rightClass : Right → KummerClass p K)
    (bankedValue : Left → Right → ZMod p) : Prop :=
  ∀ i j, core.pairing (leftClass i) (rightClass j) = bankedValue i j

end Fermat.Conservation.WildKummerPairing
