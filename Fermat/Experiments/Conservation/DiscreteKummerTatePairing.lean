/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The discrete Kummer--Tate pairing over a field containing roots of unity

This file closes the generic discrete assembly loop.  For a field `F`, a
chosen primitive `n`-th root of unity orients the genuine Kummer class in
`H¹(G_F, μ_n)`, while the un-oriented class remains the right input.  Their
cup product is then read through one explicitly supplied linear local
invariant

`H²(G_F, μ_n) →ₗ[ZMod n] ZMod n`.

The output is already defined on Kummer quotients.  No invariant, reciprocity
law, or calibration value is constructed here: those remain theorem-level
arithmetic inputs.  In particular, this is the discrete cohomological layer,
not a replacement for a later continuous/local-Tate comparison theorem.
-/
import Fermat.Experiments.Conservation.CohomologicalKummerPairing
import Fermat.Experiments.Conservation.KummerOrientation

noncomputable section

namespace Fermat.Conservation.DiscreteKummerTatePairing

open groupCohomology
open Fermat.Conservation.TameSymbol

variable {n : ℕ} [Fact n.Prime]
variable (F : Type) [Field F]

/-- The discrete local Kummer--Tate pairing attached to a primitive root and
an honest linear invariant on degree-two cohomology.

The left Kummer class is oriented by `zeta`; the right Kummer class retains
its roots-of-unity coefficients.  Cup product and scalar readout are supplied
by the generic cohomological pairing layer. -/
def localPairing
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n)
    (localInvariant :
      H2 (LocalKummerH1.rootsRepresentation n F) →ₗ[ZMod n] ZMod n) :
    WildKummerPairing.Pairing n F :=
  CohomologicalKummerPairing.localPairing
    (LocalKummerH1.rootsRepresentation n F)
    (KummerOrientation.leftKummerMap n F zeta hzeta)
    (LocalKummerH1.map n F)
    localInvariant

/-- Quotient-level readback: the assembled value is precisely the supplied
invariant evaluated on the cup of the oriented and ordinary Kummer classes. -/
@[simp]
theorem localPairing_apply
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n)
    (localInvariant :
      H2 (LocalKummerH1.rootsRepresentation n F) →ₗ[ZMod n] ZMod n)
    (x y : KummerClass n F) :
    localPairing F zeta hzeta localInvariant x y =
      localInvariant
        (KummerTateCup.orientedCupH1Classes
          (LocalKummerH1.rootsRepresentation n F)
          (KummerOrientation.leftKummerMap n F zeta hzeta x)
          (LocalKummerH1.map n F y)) :=
  rfl

/-- The same pairing pulled back to nonzero field representatives. -/
def representativePairing
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n)
    (localInvariant :
      H2 (LocalKummerH1.rootsRepresentation n F) →ₗ[ZMod n] ZMod n) :
    WildKummerPairing.RepresentativePairing n F :=
  (localPairing F zeta hzeta localInvariant).onRepresentatives

/-- Representative readback before expanding either genuine Kummer map. -/
@[simp]
theorem representativePairing_apply
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n)
    (localInvariant :
      H2 (LocalKummerH1.rootsRepresentation n F) →ₗ[ZMod n] ZMod n)
    (a b : Additive Fˣ) :
    representativePairing F zeta hzeta localInvariant a b =
      localPairing F zeta hzeta localInvariant
        (WildKummerPairing.classOfUnit n F a)
        (WildKummerPairing.classOfUnit n F b) :=
  rfl

/-- Fully expanded representative readback.  This theorem exposes the two
actual Kummer `H¹` classes and therefore gives later calibration theorems a
concrete, assumption-free rewrite target. -/
@[simp]
theorem representativePairing_ofMul
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n)
    (localInvariant :
      H2 (LocalKummerH1.rootsRepresentation n F) →ₗ[ZMod n] ZMod n)
    (a b : Fˣ) :
    representativePairing F zeta hzeta localInvariant
        (Additive.ofMul a) (Additive.ofMul b) =
      localInvariant
        (KummerTateCup.orientedCupH1Classes
          (LocalKummerH1.rootsRepresentation n F)
          (KummerOrientation.orientH1 n F zeta hzeta
            (LocalKummerH1.classOfUnit n F a))
          (LocalKummerH1.classOfUnit n F b)) :=
  rfl

end Fermat.Conservation.DiscreteKummerTatePairing
