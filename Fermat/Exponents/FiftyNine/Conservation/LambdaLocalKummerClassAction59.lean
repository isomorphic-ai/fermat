/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The genuine cyclotomic action on lambda-local Kummer classes

The cyclotomic automorphisms of the lambda-adic completion canonically act
on its quotient by `59`-th powers.  This file constructs that actual action,
proves its identity and composition laws, and proves covariance of global
lambda localization.  Applying the genuine right Kummer map after this
action gives an honest orbit map into continuous local `H¹`.

This is deliberately not advertised as an action on all of continuous
`H¹`.  Mathlib's current `continuousCohomology` functor is functorial in
the coefficient representation for a fixed acting group, but does not expose
the simultaneous group-variable/coefficient transport required by the outer
field action.  The maps below therefore stop at the strongest presently
constructible precursor instead of substituting the unrelated scalar-units
action.
-/
import Fermat.Exponents.FiftyNine.Conservation.LambdaCyclotomicCompletionAction59
import Fermat.Exponents.FiftyNine.Conservation.ContinuousKummerTateLocalization59
import Mathlib.RepresentationTheory.Basic

open scoped NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.LambdaLocalKummerClassAction59

open Fermat.Conservation
open Fermat.Conservation.ContinuousKummerOrientation
open Fermat.Conservation.LocalKummerTransport
open Fermat.Conservation.TameSymbol
open Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.LambdaCyclotomicCompletionAction59
open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

/-- Kummer classes of the actual lambda-adic completion. -/
abbrev LambdaLocalKummerClass59 :=
  KummerClass 59 (LambdaLocalField59 K)

/-- Every lambda-local Kummer class is killed by `59`. -/
theorem lambdaLocalKummerClass59_nsmul_eq_zero
    (x : LambdaLocalKummerClass59 K) : 59 • x = 0 := by
  apply Additive.toMul.injective
  change (Additive.toMul x) ^ 59 = 1
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom 59 : (LambdaLocalField59 K)ˣ →*
      (LambdaLocalField59 K)ˣ).range (Additive.toMul x)
  rw [← ha]
  exact (QuotientGroup.eq_one_iff (a ^ 59)).mpr ⟨a, rfl⟩

noncomputable local instance instLambdaLocalKummerClass59ModuleZMod :
    Module (ZMod 59) (LambdaLocalKummerClass59 K) :=
  AddCommGroup.zmodModule
    (n := 59) (G := LambdaLocalKummerClass59 K)
    (lambdaLocalKummerClass59_nsmul_eq_zero K)

/-! ## The local Kummer-class representation -/

/-- One completed cyclotomic automorphism descended to local Kummer
classes. -/
noncomputable def lambdaLocalKummerClassAddHom59
    (sigma : GaloisIndex59) :
    LambdaLocalKummerClass59 K →+ LambdaLocalKummerClass59 K :=
  LocalKummerTransport.map 59
    (cyclotomicLambdaCompletionRingEquiv59 K sigma).toRingHom

/-- The descended additive map is canonically `ZMod 59`-linear. -/
noncomputable def lambdaLocalKummerClassLinearMap59
    (sigma : GaloisIndex59) :
    LambdaLocalKummerClass59 K →ₗ[ZMod 59]
      LambdaLocalKummerClass59 K :=
  (lambdaLocalKummerClassAddHom59 K sigma).toZModLinearMap 59

@[simp]
theorem lambdaLocalKummerClassLinearMap59_one_apply
    (x : LambdaLocalKummerClass59 K) :
    lambdaLocalKummerClassLinearMap59 K 1 x = x := by
  change LocalKummerTransport.map 59
      (cyclotomicLambdaCompletionRingEquiv59 K 1).toRingHom x = x
  rw [cyclotomicLambdaCompletionRingEquiv59_one]
  exact DFunLike.congr_fun
    (LocalKummerTransport.map_id (p := 59)
      (K := LambdaLocalField59 K)) x

/-- Multiplication of cyclotomic indices acts by composition in the same
order as on the completed field. -/
theorem lambdaLocalKummerClassLinearMap59_mul_apply
    (sigma tau : GaloisIndex59)
    (x : LambdaLocalKummerClass59 K) :
    lambdaLocalKummerClassLinearMap59 K (sigma * tau) x =
      lambdaLocalKummerClassLinearMap59 K sigma
        (lambdaLocalKummerClassLinearMap59 K tau x) := by
  change LocalKummerTransport.map 59
      (cyclotomicLambdaCompletionRingEquiv59 K (sigma * tau)).toRingHom x =
    LocalKummerTransport.map 59
      (cyclotomicLambdaCompletionRingEquiv59 K sigma).toRingHom
      (LocalKummerTransport.map 59
        (cyclotomicLambdaCompletionRingEquiv59 K tau).toRingHom x)
  rw [cyclotomicLambdaCompletionRingEquiv59_mul]
  exact DFunLike.congr_fun
    (LocalKummerTransport.map_comp (p := 59)
      (cyclotomicLambdaCompletionRingEquiv59 K tau).toRingHom
      (cyclotomicLambdaCompletionRingEquiv59 K sigma).toRingHom) x

/-- The genuine cyclotomic representation on lambda-local Kummer
classes. -/
noncomputable def lambdaLocalKummerClassRepresentation59 :
    Representation (ZMod 59) GaloisIndex59
      (LambdaLocalKummerClass59 K) where
  toFun sigma := lambdaLocalKummerClassLinearMap59 K sigma
  map_one' := by
    apply LinearMap.ext
    exact lambdaLocalKummerClassLinearMap59_one_apply K
  map_mul' sigma tau := by
    apply LinearMap.ext
    exact lambdaLocalKummerClassLinearMap59_mul_apply K sigma tau

/-! ## Covariance of the actual localization map -/

/-- Global-to-local transport into the Kummer quotient of the lambda-adic
completion. -/
noncomputable def lambdaKummerLocalization59 :
    KummerClass 59 K →+ LambdaLocalKummerClass59 K :=
  LocalKummerTransport.map 59 (lambdaLocalization59 K)

/-- The global cyclotomic action on ambient Kummer classes, expressed using
the same functorial quotient transport as the local action. -/
noncomputable def globalCyclotomicKummerClassAddHom59
    (sigma : GaloisIndex59) :
    KummerClass 59 K →+ KummerClass 59 K :=
  LocalKummerTransport.map 59
    (cyclotomicFieldRingEquiv59 K sigma).toRingHom

/-- This spelling is definitionally the already-established canonical
cyclotomic action on the multiplicative Kummer quotient. -/
@[simp]
theorem globalCyclotomicKummerClassAddHom59_toMul
    (sigma : GaloisIndex59) (x : KummerClass 59 K) :
    Additive.toMul (globalCyclotomicKummerClassAddHom59 K sigma x) =
      cyclotomicKummerHom59 K sigma (Additive.toMul x) := by
  rfl

/-- The global and completed cyclotomic automorphisms commute with the
canonical lambda localization as ring homomorphisms. -/
theorem lambdaLocalization59_cyclotomicRingHom
    (sigma : GaloisIndex59) :
    (lambdaLocalization59 K).comp
        (cyclotomicFieldRingEquiv59 K sigma).toRingHom =
      (cyclotomicLambdaCompletionRingEquiv59 K sigma).toRingHom.comp
        (lambdaLocalization59 K) := by
  ext x
  exact (cyclotomicLambdaCompletionRingEquiv59_lambdaLocalization
    K sigma x).symm

/-- Lambda localization intertwines the canonical global Kummer action and
the genuine local Kummer-class representation. -/
theorem lambdaKummerLocalization59_cyclotomic
    (sigma : GaloisIndex59) (x : KummerClass 59 K) :
    lambdaKummerLocalization59 K
        (globalCyclotomicKummerClassAddHom59 K sigma x) =
      lambdaLocalKummerClassRepresentation59 K sigma
        (lambdaKummerLocalization59 K x) := by
  change LocalKummerTransport.map 59 (lambdaLocalization59 K)
      (LocalKummerTransport.map 59
        (cyclotomicFieldRingEquiv59 K sigma).toRingHom x) =
    LocalKummerTransport.map 59
      (cyclotomicLambdaCompletionRingEquiv59 K sigma).toRingHom
      (LocalKummerTransport.map 59 (lambdaLocalization59 K) x)
  rw [← AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply,
    ← LocalKummerTransport.map_comp,
    ← LocalKummerTransport.map_comp,
    lambdaLocalization59_cyclotomicRingHom]

/-- The same covariance theorem stated directly with the canonical
`cyclotomicKummerHom59` already used by the global Selmer action. -/
theorem lambdaKummerLocalization59_cyclotomicKummerHom
    (sigma : GaloisIndex59) (x : KummerClass 59 K) :
    lambdaKummerLocalization59 K
        (Additive.ofMul
          (cyclotomicKummerHom59 K sigma (Additive.toMul x))) =
      lambdaLocalKummerClassRepresentation59 K sigma
        (lambdaKummerLocalization59 K x) := by
  rw [← globalCyclotomicKummerClassAddHom59_toMul]
  exact lambdaKummerLocalization59_cyclotomic K sigma x

/-! ## The honest continuous-H¹ orbit on the Kummer image -/

/-- Apply the genuine right Kummer map after one actual local cyclotomic
Kummer-class operator.  Its codomain is genuine continuous `H¹`, but this
map is not renamed or promoted to an action on all of that codomain. -/
noncomputable def lambdaRightKummerOrbitMap59
    (sigma : GaloisIndex59) :
    LambdaLocalKummerClass59 K →+ LambdaRootsContinuousH1 K :=
  (rightKummerMap 59 (LambdaLocalField59 K)).comp
    (lambdaLocalKummerClassAddHom59 K sigma)

@[simp]
theorem lambdaRightKummerOrbitMap59_apply
    (sigma : GaloisIndex59) (x : LambdaLocalKummerClass59 K) :
    lambdaRightKummerOrbitMap59 K sigma x =
      rightKummerMap 59 (LambdaLocalField59 K)
        (lambdaLocalKummerClassRepresentation59 K sigma x) := by
  rfl

@[simp]
theorem lambdaRightKummerOrbitMap59_one_apply
    (x : LambdaLocalKummerClass59 K) :
    lambdaRightKummerOrbitMap59 K 1 x =
      rightKummerMap 59 (LambdaLocalField59 K) x := by
  rw [lambdaRightKummerOrbitMap59_apply]
  change rightKummerMap 59 (LambdaLocalField59 K)
      (lambdaLocalKummerClassLinearMap59 K 1 x) = _
  rw [lambdaLocalKummerClassLinearMap59_one_apply]

/-- The orbit maps retain the local cyclotomic composition law before the
final right-Kummer read. -/
theorem lambdaRightKummerOrbitMap59_mul_apply
    (sigma tau : GaloisIndex59)
    (x : LambdaLocalKummerClass59 K) :
    lambdaRightKummerOrbitMap59 K (sigma * tau) x =
      lambdaRightKummerOrbitMap59 K sigma
        (lambdaLocalKummerClassRepresentation59 K tau x) := by
  rw [lambdaRightKummerOrbitMap59_apply,
    lambdaRightKummerOrbitMap59_apply]
  change rightKummerMap 59 (LambdaLocalField59 K)
      (lambdaLocalKummerClassLinearMap59 K (sigma * tau) x) =
    rightKummerMap 59 (LambdaLocalField59 K)
      (lambdaLocalKummerClassLinearMap59 K sigma
        (lambdaLocalKummerClassLinearMap59 K tau x))
  rw [lambdaLocalKummerClassLinearMap59_mul_apply]

/-- On every genuine global Kummer class, applying the local orbit map
after localization is exactly the same as acting globally, localizing, and
then applying `rightKummerMap`. -/
theorem lambdaRightKummerOrbitMap59_localization
    (sigma : GaloisIndex59) (x : KummerClass 59 K) :
    lambdaRightKummerOrbitMap59 K sigma
        (lambdaKummerLocalization59 K x) =
      rightKummerMap 59 (LambdaLocalField59 K)
        (lambdaKummerLocalization59 K
          (globalCyclotomicKummerClassAddHom59 K sigma x)) := by
  rw [lambdaRightKummerOrbitMap59_apply,
    lambdaKummerLocalization59_cyclotomic]

/-- Canonical-global-action spelling of the same right-Kummer covariance. -/
theorem lambdaRightKummerOrbitMap59_localization_cyclotomicKummerHom
    (sigma : GaloisIndex59) (x : KummerClass 59 K) :
    lambdaRightKummerOrbitMap59 K sigma
        (lambdaKummerLocalization59 K x) =
      rightKummerMap 59 (LambdaLocalField59 K)
        (lambdaKummerLocalization59 K
          (Additive.ofMul
            (cyclotomicKummerHom59 K sigma (Additive.toMul x)))) := by
  rw [← globalCyclotomicKummerClassAddHom59_toMul]
  exact lambdaRightKummerOrbitMap59_localization K sigma x

/-! ## Kernel-trust audit -/

/--
info: 'Fermat.FiftyNine.Conservation.LambdaLocalKummerClassAction59.lambdaLocalKummerClassRepresentation59' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms lambdaLocalKummerClassRepresentation59

/--
info: 'Fermat.FiftyNine.Conservation.LambdaLocalKummerClassAction59.lambdaKummerLocalization59_cyclotomicKummerHom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms lambdaKummerLocalization59_cyclotomicKummerHom

/--
info: 'Fermat.FiftyNine.Conservation.LambdaLocalKummerClassAction59.lambdaRightKummerOrbitMap59_mul_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms lambdaRightKummerOrbitMap59_mul_apply

/--
info: 'Fermat.FiftyNine.Conservation.LambdaLocalKummerClassAction59.lambdaRightKummerOrbitMap59_localization_cyclotomicKummerHom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms lambdaRightKummerOrbitMap59_localization_cyclotomicKummerHom

end Fermat.FiftyNine.Conservation.LambdaLocalKummerClassAction59
