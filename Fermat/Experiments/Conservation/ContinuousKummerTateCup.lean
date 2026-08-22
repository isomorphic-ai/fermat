/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The continuous Kummer--Tate cup product on cohomology

This file exposes the nominally descended Alexander--Whitney cup on
Mathlib's actual continuous-cohomology objects.  The substantive descent is
in `ContinuousKummerTateCupNominal`: there the raw cup is restricted to
honest cocycles, explicit primitives show that both kinds of degree-one
boundary are killed, and `LinearMap.liftQ₂` descends through both genuine
homology quotients.

The nominal carriers are linearly equivalent to the actual categorical
homology objects.  The adapter below only transports the finished bilinear
map across those equivalences.  No representative, local invariant,
Tate-duality theorem, Kummer specialization, or global lifting theorem is
introduced here.
-/
import Fermat.Experiments.Conservation.ContinuousKummerTateCupNominal

noncomputable section

namespace Fermat.Conservation.ContinuousKummerTateCup

open ContinuousCohomology
open ContinuousKummerTateCupRaw
open Nominal

universe u vM vN vP vM' vN' vP'

variable {R G : Type u} [CommRing R] [TopologicalSpace R]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]

variable {A B C : Action (TopModuleCat R) G}

/-! ## Transporting a bilinear map across linear equivalences -/

/-- Transport all three carriers of a bilinear map across linear
equivalences.  Keeping this adapter generic prevents the large continuous
cohomology carriers from being unfolded while its linearity is checked. -/
def transportBilinear
    {M : Type vM} {N : Type vN} {P : Type vP}
    {M' : Type vM'} {N' : Type vN'} {P' : Type vP'}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [AddCommGroup M'] [AddCommGroup N'] [AddCommGroup P']
    [Module R M] [Module R N] [Module R P]
    [Module R M'] [Module R N'] [Module R P']
    (f : M →ₗ[R] N →ₗ[R] P)
    (eM : M ≃ₗ[R] M') (eN : N ≃ₗ[R] N') (eP : P ≃ₗ[R] P') :
    M' →ₗ[R] N' →ₗ[R] P' :=
  (f.compl₁₂ eM.symm.toLinearMap eN.symm.toLinearMap).compr₂
    eP.toLinearMap

omit [TopologicalSpace R] in
@[simp]
theorem transportBilinear_equiv_apply
    {M : Type vM} {N : Type vN} {P : Type vP}
    {M' : Type vM'} {N' : Type vN'} {P' : Type vP'}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [AddCommGroup M'] [AddCommGroup N'] [AddCommGroup P']
    [Module R M] [Module R N] [Module R P]
    [Module R M'] [Module R N'] [Module R P']
    (f : M →ₗ[R] N →ₗ[R] P)
    (eM : M ≃ₗ[R] M') (eN : N ≃ₗ[R] N') (eP : P ≃ₗ[R] P')
    (m : M) (n : N) :
    transportBilinear f eM eN eP (eM m) (eN n) = eP (f m n) := by
  simp [transportBilinear]

/-! ## The actual continuous-cohomology cup -/

/-- The generic continuous Alexander--Whitney cup product on genuine
continuous cohomology:

`H¹_cont(G,A) × H¹_cont(G,B) → H²_cont(G,C)`.

It is available for every jointly continuous equivariant bilinear pairing
of coefficients `A.V × B.V → C.V`. -/
def cupH1
    (p : ContinuousEquivariantPairing A B C) :
    (continuousCohomology R G 1).obj A →ₗ[R]
      (continuousCohomology R G 1).obj B →ₗ[R]
        (continuousCohomology R G 2).obj C :=
  transportBilinear (nominalCupH1 p)
    (homologyLinearEquiv A 1)
    (homologyLinearEquiv B 1)
    (homologyLinearEquiv C 2)

/-- Readback of the actual cup after transporting arbitrary nominal
homology classes to Mathlib's genuine continuous-cohomology objects. -/
@[simp]
theorem cupH1_homologyLinearEquiv
    (p : ContinuousEquivariantPairing A B C)
    (x : Homology A 1) (y : Homology B 1) :
    cupH1 p (homologyLinearEquiv A 1 x) (homologyLinearEquiv B 1 y) =
      homologyLinearEquiv C 2 (nominalCupH1 p x y) := by
  exact transportBilinear_equiv_apply
    (nominalCupH1 p)
    (homologyLinearEquiv A 1)
    (homologyLinearEquiv B 1)
    (homologyLinearEquiv C 2) x y

/-- Representative-independent computation on honest nominal cocycles.
The inputs and output displayed here are Mathlib's actual continuous
cohomology classes; the wrappers occur only in the representatives. -/
@[simp]
theorem cupH1_projection
    (p : ContinuousEquivariantPairing A B C)
    (f : Cycle A 1 2) (g : Cycle B 1 2) :
    cupH1 p
        (homologyLinearEquiv A 1 (h1Projection A f))
        (homologyLinearEquiv B 1 (h1Projection B g)) =
      homologyLinearEquiv C 2 (nominalCycleCupToH2 p f g) := by
  rw [cupH1_homologyLinearEquiv, nominalCupH1_projection]

end Fermat.Conservation.ContinuousKummerTateCup
