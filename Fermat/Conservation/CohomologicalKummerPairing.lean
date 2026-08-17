/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Assemble a wild pairing from Kummer--Tate cohomology

This file joins the mechanical pieces of the cohomological route.  Given
actual left and right Kummer maps and an actual linear local invariant, it
builds a quotient-level wild Kummer pairing.  Pullback along a field map then
gives the corresponding pairing on global Kummer classes.

The inputs remain deliberately explicit: this adapter neither postulates a
Kummer map nor a local invariant, and it makes no reciprocity or calibration
claim.
-/
import Fermat.Conservation.KummerTateReadout
import Fermat.Conservation.LocalKummerTransport

noncomputable section

namespace Fermat.Conservation.CohomologicalKummerPairing

open groupCohomology
open Fermat.Conservation.TameSymbol
open Fermat.Conservation.WildKummerPairing
open Fermat.Conservation.KummerTateReadout

variable {p : ℕ} [Fact p.Prime]
variable {F K G : Type} [Field F] [Field K] [Group G]
variable (A : Rep (ZMod p) G)

/-- Assemble the local quotient pairing from the two oriented Kummer maps,
cup product, and normalized local invariant. -/
def localPairing
    (leftKummer : KummerClass p F →+
      (Additive G →+ ZMod p))
    (rightKummer : KummerClass p F →+ H1 A)
    (localInvariant : H2 A →ₗ[ZMod p] ZMod p) :
    WildKummerPairing.Pairing p F where
  toFun x :=
    (orientedReadout A localInvariant (leftKummer x)).toAddMonoidHom.comp
      rightKummer
  map_zero' := by
    ext y
    simp
  map_add' x₁ x₂ := by
    ext y
    simp

@[simp]
theorem localPairing_apply
    (leftKummer : KummerClass p F →+
      (Additive G →+ ZMod p))
    (rightKummer : KummerClass p F →+ H1 A)
    (localInvariant : H2 A →ₗ[ZMod p] ZMod p)
    (x y : KummerClass p F) :
    localPairing A leftKummer rightKummer localInvariant x y =
      localInvariant
        (KummerTateCup.orientedCupH1 A (leftKummer x) (rightKummer y)) :=
  rfl

/-- Pull the cohomologically assembled local pairing back to global Kummer
classes along a field map. -/
def globalPairing
    (localization : K →+* F)
    (leftKummer : KummerClass p F →+
      (Additive G →+ ZMod p))
    (rightKummer : KummerClass p F →+ H1 A)
    (localInvariant : H2 A →ₗ[ZMod p] ZMod p) :
    WildKummerPairing.Pairing p K :=
  LocalKummerTransport.Pairing.pullback localization
    (localPairing A leftKummer rightKummer localInvariant)

@[simp]
theorem globalPairing_apply
    (localization : K →+* F)
    (leftKummer : KummerClass p F →+
      (Additive G →+ ZMod p))
    (rightKummer : KummerClass p F →+ H1 A)
    (localInvariant : H2 A →ₗ[ZMod p] ZMod p)
    (x y : KummerClass p K) :
    globalPairing A localization leftKummer rightKummer localInvariant x y =
      localInvariant
        (KummerTateCup.orientedCupH1 A
          (leftKummer (LocalKummerTransport.map p localization x))
          (rightKummer (LocalKummerTransport.map p localization y))) :=
  rfl

@[simp]
theorem globalPairing_classOfUnit
    (localization : K →+* F)
    (leftKummer : KummerClass p F →+
      (Additive G →+ ZMod p))
    (rightKummer : KummerClass p F →+ H1 A)
    (localInvariant : H2 A →ₗ[ZMod p] ZMod p)
    (a b : Kˣ) :
    globalPairing A localization leftKummer rightKummer localInvariant
        (classOfUnit p K (Additive.ofMul a))
        (classOfUnit p K (Additive.ofMul b)) =
      localPairing A leftKummer rightKummer localInvariant
        (classOfUnit p F
          (Additive.ofMul (LocalKummerTransport.unitMap localization a)))
        (classOfUnit p F
          (Additive.ofMul (LocalKummerTransport.unitMap localization b))) :=
  rfl

end Fermat.Conservation.CohomologicalKummerPairing
