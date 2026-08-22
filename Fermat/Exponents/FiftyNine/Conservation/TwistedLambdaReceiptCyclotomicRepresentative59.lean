/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The genuine cyclotomic transform of W1's reflected representative

The reflected factor retained by `twistedLambdaCupReceipt59` is the
continuous Kummer class of the chosen local primitive root.  This file
follows that representative through the genuine cyclotomic automorphism of
the lambda-adic completion.

At representative level the result is completely explicit: the automorphism
indexed by `sigma : (ZMod 59)ˣ` sends the chosen root to its `sigma`-th power.
Consequently its Kummer class and its concrete continuous Kummer class both
transform by the power-one cyclotomic character.  This is intentionally not
advertised as an action on continuous `H¹`: constructing that action still
requires the functoriality of the absolute-Galois continuous cochain complex.
-/
import Fermat.Exponents.FiftyNine.Conservation.TwistedLambdaCupReceipt59
import Fermat.Exponents.FiftyNine.Conservation.LambdaCyclotomicCompletionAction59
import Fermat.Exponents.FiftyNine.Conservation.LambdaLocalKummerClassAction59
import Fermat.Exponents.FiftyNine.Conservation.LambdaReflectedLocalSeatAudit827
import Fermat.Experiments.Conservation.LocalKummerTransport

open scoped NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.TwistedLambdaReceiptCyclotomicRepresentative59

open Fermat.Conservation.ContinuousKummerH1
open Fermat.Conservation.KummerOrientation
open Fermat.Conservation.LocalKummerTransport
open Fermat.Conservation.TameSymbol
open Fermat.Conservation.WildKummerPairing
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.LambdaCyclotomicCompletionAction59
open Fermat.FiftyNine.Conservation.LambdaLocalKummerClassAction59
open Fermat.FiftyNine.Conservation.LambdaReflectedLocalSeatAudit827
open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

/-- The exact unit whose continuous Kummer class is W1's retained reflected
factor. -/
def reflectedPrimitiveUnit59 : (LambdaLocalField59 K)ˣ :=
  primitiveUnit 59 (LambdaLocalField59 K)
    (lambdaLocalPrimitiveRoot59 K)
    (lambdaLocalPrimitiveRoot59_isPrimitive K)

/-- Read W1's reflected factor all the way back to its explicit local unit. -/
theorem twistedLambdaCupReceipt59_reflected_eq :
    (twistedLambdaCupReceipt59 K).reflected =
      continuousClassOfUnit 59 (LambdaLocalField59 K)
        (reflectedPrimitiveUnit59 K) :=
  rfl

/-- The genuine completed-field automorphism on nonzero local elements. -/
def cyclotomicLambdaCompletionUnitEquiv59
    (sigma : GaloisIndex59) :
    (LambdaLocalField59 K)ˣ ≃* (LambdaLocalField59 K)ˣ :=
  Units.mapEquiv
    (cyclotomicLambdaCompletionRingEquiv59 K sigma).toMulEquiv

/-- The completion action sends the distinguished primitive root to the
power indexed by the cyclotomic automorphism. -/
@[simp]
theorem cyclotomicLambdaCompletionRingEquiv59_primitiveRoot
    (sigma : GaloisIndex59) :
    cyclotomicLambdaCompletionRingEquiv59 K sigma
        (lambdaLocalPrimitiveRoot59 K) =
      lambdaLocalPrimitiveRoot59 K ^ (sigma : ZMod 59).val := by
  change cyclotomicLambdaCompletionRingEquiv59 K sigma
      (lambdaLocalization59 K (globalPrimitiveRoot59 K)) =
    lambdaLocalization59 K (globalPrimitiveRoot59 K) ^
      (sigma : ZMod 59).val
  rw [cyclotomicLambdaCompletionRingEquiv59_lambdaLocalization]
  change lambdaLocalization59 K
      (KummerCriterion.cyclotomicSigmaOfUnit
        (p := 59) K sigma (globalPrimitiveRoot59 K)) = _
  rw [globalPrimitiveRoot59,
    KummerCriterion.cyclotomicSigmaOfUnit_apply_zeta]
  exact map_pow (lambdaLocalization59 K)
    (globalPrimitiveRoot59 K) (sigma : ZMod 59).val

/-- The same exact transformation bundled on units. -/
@[simp]
theorem cyclotomicLambdaCompletionUnitEquiv59_reflectedPrimitiveUnit
    (sigma : GaloisIndex59) :
    cyclotomicLambdaCompletionUnitEquiv59 K sigma
        (reflectedPrimitiveUnit59 K) =
      reflectedPrimitiveUnit59 K ^ (sigma : ZMod 59).val := by
  apply Units.ext
  simpa [cyclotomicLambdaCompletionUnitEquiv59, reflectedPrimitiveUnit59,
    primitiveUnit] using
    cyclotomicLambdaCompletionRingEquiv59_primitiveRoot K sigma

/-! ## Descent to the local Kummer quotient -/

/-- The exact quotient-level Kummer class underlying W1's reflected
continuous class. -/
def reflectedPrimitiveKummerClass59 :
    KummerClass 59 (LambdaLocalField59 K) :=
  classOfUnit 59 (LambdaLocalField59 K)
    (Additive.ofMul (reflectedPrimitiveUnit59 K))

/-- The completed automorphism transported through the quotient by
59th powers.  This is a genuine map on local Kummer classes; it is not an
action on continuous cohomology. -/
def cyclotomicLambdaCompletionKummerHom59
    (sigma : GaloisIndex59) :
    KummerClass 59 (LambdaLocalField59 K) →+
      KummerClass 59 (LambdaLocalField59 K) :=
  Fermat.Conservation.LocalKummerTransport.map 59
    (cyclotomicLambdaCompletionRingEquiv59 K sigma).toRingHom

@[simp]
theorem cyclotomicLambdaCompletionKummerHom59_one :
    cyclotomicLambdaCompletionKummerHom59 K 1 =
      AddMonoidHom.id (KummerClass 59 (LambdaLocalField59 K)) := by
  unfold cyclotomicLambdaCompletionKummerHom59
  rw [cyclotomicLambdaCompletionRingEquiv59_one]
  exact Fermat.Conservation.LocalKummerTransport.map_id

/-- The quotient maps retain the same cyclotomic composition law as the
completed field automorphisms. -/
theorem cyclotomicLambdaCompletionKummerHom59_mul
    (sigma tau : GaloisIndex59) :
    cyclotomicLambdaCompletionKummerHom59 K (sigma * tau) =
      (cyclotomicLambdaCompletionKummerHom59 K sigma).comp
        (cyclotomicLambdaCompletionKummerHom59 K tau) := by
  apply AddMonoidHom.ext
  intro x
  exact lambdaLocalKummerClassLinearMap59_mul_apply K sigma tau x

@[simp]
theorem cyclotomicLambdaCompletionKummerHom59_classOfUnit
    (sigma : GaloisIndex59) (a : (LambdaLocalField59 K)ˣ) :
    cyclotomicLambdaCompletionKummerHom59 K sigma
        (classOfUnit 59 (LambdaLocalField59 K) (Additive.ofMul a)) =
      classOfUnit 59 (LambdaLocalField59 K)
        (Additive.ofMul
          (cyclotomicLambdaCompletionUnitEquiv59 K sigma a)) := by
  rfl

/-- The honest local Kummer representative has the power-one cyclotomic
eigenlaw. -/
theorem cyclotomicLambdaCompletionKummerHom59_reflectedPrimitive
    (sigma : GaloisIndex59) :
    cyclotomicLambdaCompletionKummerHom59 K sigma
        (reflectedPrimitiveKummerClass59 K) =
      (sigma : ZMod 59).val • reflectedPrimitiveKummerClass59 K := by
  rw [reflectedPrimitiveKummerClass59,
    cyclotomicLambdaCompletionKummerHom59_classOfUnit,
    cyclotomicLambdaCompletionUnitEquiv59_reflectedPrimitiveUnit]
  change classOfUnit 59 (LambdaLocalField59 K)
      (Additive.ofMul
        (reflectedPrimitiveUnit59 K ^ (sigma : ZMod 59).val)) = _
  rw [ofMul_pow, map_nsmul]

/-! ## The same transformation on the explicit continuous class -/

/-- Powers of an explicit representative become repeated addition in its
genuine continuous Kummer class. -/
theorem continuousClassOfUnit_pow
    (a : (LambdaLocalField59 K)ˣ) (m : ℕ) :
    continuousClassOfUnit 59 (LambdaLocalField59 K) (a ^ m) =
      m • continuousClassOfUnit 59 (LambdaLocalField59 K) a := by
  change continuousRepresentativeMap 59 (LambdaLocalField59 K)
      (Additive.ofMul (a ^ m)) =
    m • continuousRepresentativeMap 59 (LambdaLocalField59 K)
      (Additive.ofMul a)
  rw [ofMul_pow, map_nsmul]

/-- Applying the genuine completion automorphism to W1's explicit unit and
then taking its continuous Kummer class gives the power-one cyclotomic
transform of the retained reflected factor.  This statement needs no action
on continuous `H¹`. -/
theorem continuousClassOfUnit_cyclotomic_reflectedPrimitive
    (sigma : GaloisIndex59) :
    continuousClassOfUnit 59 (LambdaLocalField59 K)
        (cyclotomicLambdaCompletionUnitEquiv59 K sigma
          (reflectedPrimitiveUnit59 K)) =
      (sigma : ZMod 59).val •
        (twistedLambdaCupReceipt59 K).reflected := by
  rw [cyclotomicLambdaCompletionUnitEquiv59_reflectedPrimitiveUnit,
    continuousClassOfUnit_pow,
    twistedLambdaCupReceipt59_reflected_eq]

/-- Character-valued spelling of the same result: the exponent read modulo
59 is exactly the underlying value of the cyclotomic index. -/
theorem continuousClassOfUnit_cyclotomic_reflectedPrimitive_zmod
    (sigma : GaloisIndex59) :
    continuousClassOfUnit 59 (LambdaLocalField59 K)
        (cyclotomicLambdaCompletionUnitEquiv59 K sigma
          (reflectedPrimitiveUnit59 K)) =
      (sigma : ZMod 59) •
        (twistedLambdaCupReceipt59 K).reflected := by
  rw [continuousClassOfUnit_cyclotomic_reflectedPrimitive]
  rw [← Nat.cast_smul_eq_nsmul (R := ZMod 59),
    ZMod.natCast_zmod_val]

/-! ## The compiler-visible character mismatch -/

/-- W1's retained right factor is nonzero, because its cup with the retained
left factor is the nonzero normalized W1 receipt. -/
theorem twistedLambdaCupReceipt59_reflected_ne_zero :
    (twistedLambdaCupReceipt59 K).reflected ≠ 0 := by
  intro hreflected
  apply (twistedLambdaCupReceipt59 K).cup_ne_zero
  rw [← (twistedLambdaCupReceipt59 K).cup_eq, hreflected]
  simp

/-- The quotient class above maps to exactly W1's retained continuous class;
there is no representative change hidden at the Kummer-to-cohomology
boundary. -/
@[simp]
theorem continuousMap_reflectedPrimitiveKummerClass59 :
    continuousMap 59 (LambdaLocalField59 K)
        (reflectedPrimitiveKummerClass59 K) =
      (twistedLambdaCupReceipt59 K).reflected := by
  rfl

/-- In particular, W1's quotient-level local Kummer class is itself
nonzero. -/
theorem reflectedPrimitiveKummerClass59_ne_zero :
    reflectedPrimitiveKummerClass59 K ≠ 0 := by
  intro hkummer
  apply twistedLambdaCupReceipt59_reflected_ne_zero K
  rw [← continuousMap_reflectedPrimitiveKummerClass59 K, hkummer, map_zero]

/-- At the index `2`, the genuine power-one transform and the desired
power-44 reflected coefficient act differently on W1's nonzero factor. -/
theorem receipt_powerOne_smul_ne_powerFortyFour_smul :
    (auditTwoIndex59 : ZMod 59) •
        (twistedLambdaCupReceipt59 K).reflected ≠
      ((powerCharacter59 44 auditTwoIndex59 : (ZMod 59)ˣ) : ZMod 59) •
        (twistedLambdaCupReceipt59 K).reflected := by
  intro heq
  have hcoefficient :
      (auditTwoIndex59 : ZMod 59) ≠
        ((powerCharacter59 44 auditTwoIndex59 : (ZMod 59)ˣ) : ZMod 59) := by
    decide +kernel +revert
  have hzero :
      ((auditTwoIndex59 : ZMod 59) -
        ((powerCharacter59 44 auditTwoIndex59 : (ZMod 59)ˣ) : ZMod 59)) •
          (twistedLambdaCupReceipt59 K).reflected = 0 := by
    rw [sub_smul, heq, sub_self]
  rcases smul_eq_zero.mp hzero with hscalar | hreflected
  · exact (sub_ne_zero.mpr hcoefficient) hscalar
  · exact twistedLambdaCupReceipt59_reflected_ne_zero K hreflected

/-- The same obstruction is already present before continuous cohomology:
the genuine quotient Kummer transform at index `2` is not repeated addition
by the natural representative of the power-44 coefficient. -/
theorem cyclotomicLambdaCompletionKummerHom59_reflectedPrimitive_ne_powerFortyFour
    :
    cyclotomicLambdaCompletionKummerHom59 K auditTwoIndex59
        (reflectedPrimitiveKummerClass59 K) ≠
      ((
        ((powerCharacter59 44 auditTwoIndex59 : (ZMod 59)ˣ) : ZMod 59)
      ).val) • reflectedPrimitiveKummerClass59 K := by
  intro heq
  have hmap := congrArg
    (continuousMap 59 (LambdaLocalField59 K)) heq
  rw [cyclotomicLambdaCompletionKummerHom59_reflectedPrimitive,
    map_nsmul, map_nsmul,
    continuousMap_reflectedPrimitiveKummerClass59] at hmap
  apply receipt_powerOne_smul_ne_powerFortyFour_smul K
  simpa only [← Nat.cast_smul_eq_nsmul (R := ZMod 59),
    ZMod.natCast_zmod_val] using hmap

/-- Therefore the explicit continuous Kummer transform of W1's
representative is not the power-44 reflected transform.  This is a negative
theorem about the concrete representative map, not a claim that an outer
action on continuous `H¹` has already been constructed. -/
theorem continuousClassOfUnit_cyclotomic_reflectedPrimitive_ne_powerFortyFour
    :
    continuousClassOfUnit 59 (LambdaLocalField59 K)
        (cyclotomicLambdaCompletionUnitEquiv59 K auditTwoIndex59
          (reflectedPrimitiveUnit59 K)) ≠
      ((powerCharacter59 44 auditTwoIndex59 : (ZMod 59)ˣ) : ZMod 59) •
        (twistedLambdaCupReceipt59 K).reflected := by
  rw [continuousClassOfUnit_cyclotomic_reflectedPrimitive_zmod]
  exact receipt_powerOne_smul_ne_powerFortyFour_smul K

/-- If a future genuine outer action on continuous local `H¹` satisfies the
expected Kummer naturality equation on W1's explicit representative, W1's
current factor cannot inhabit the power-44 reflected seat.  The hypothesis
is the single missing functoriality equation; no action or provider is
created here. -/
theorem not_twistedLambdaReceiptReflectedSeating827_of_naturality
    (rhoLocal : LambdaLocalDeltaRepresentation59 K)
    (hnatural : ∀ sigma : GaloisIndex59,
      rhoLocal sigma (twistedLambdaCupReceipt59 K).reflected =
        continuousClassOfUnit 59 (LambdaLocalField59 K)
          (cyclotomicLambdaCompletionUnitEquiv59 K sigma
            (reflectedPrimitiveUnit59 K))) :
    ¬ TwistedLambdaReceiptReflectedSeating827 (K := K) rhoLocal := by
  intro hseat
  have hreflected :=
    (twistedLambdaReceiptReflectedSeating827_iff
      (K := K) rhoLocal).mp hseat auditTwoIndex59
  rw [Fermat.FiftyNine.Conservation.CanonicalIrregularMode827.orientedPrimalMode827_canonical_irregular]
    at hreflected
  have hpowerOne := hnatural auditTwoIndex59
  rw [continuousClassOfUnit_cyclotomic_reflectedPrimitive_zmod] at hpowerOne
  exact receipt_powerOne_smul_ne_powerFortyFour_smul K
    (hpowerOne.symm.trans hreflected)

/-! ## Kernel-trust audit -/

/--
info: 'Fermat.FiftyNine.Conservation.TwistedLambdaReceiptCyclotomicRepresentative59.cyclotomicLambdaCompletionRingEquiv59_primitiveRoot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cyclotomicLambdaCompletionRingEquiv59_primitiveRoot

/--
info: 'Fermat.FiftyNine.Conservation.TwistedLambdaReceiptCyclotomicRepresentative59.cyclotomicLambdaCompletionKummerHom59_reflectedPrimitive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cyclotomicLambdaCompletionKummerHom59_reflectedPrimitive

/--
info: 'Fermat.FiftyNine.Conservation.TwistedLambdaReceiptCyclotomicRepresentative59.continuousClassOfUnit_cyclotomic_reflectedPrimitive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms continuousClassOfUnit_cyclotomic_reflectedPrimitive

/--
info: 'Fermat.FiftyNine.Conservation.TwistedLambdaReceiptCyclotomicRepresentative59.cyclotomicLambdaCompletionKummerHom59_reflectedPrimitive_ne_powerFortyFour' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cyclotomicLambdaCompletionKummerHom59_reflectedPrimitive_ne_powerFortyFour

/--
info: 'Fermat.FiftyNine.Conservation.TwistedLambdaReceiptCyclotomicRepresentative59.not_twistedLambdaReceiptReflectedSeating827_of_naturality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms not_twistedLambdaReceiptReflectedSeating827_of_naturality

end Fermat.FiftyNine.Conservation.TwistedLambdaReceiptCyclotomicRepresentative59
