/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Literal character seats on the lambda-local Kummer quotient

The completed cyclotomic action already constructed on the genuine local
Kummer quotient admits the ordinary group-algebra character projectors.  This
file installs those projectors directly on that quotient, rather than on a
scalar proxy for continuous `H¹`.

The distinguished primitive class retained by W1 lies in the power-one seat.
The power-one and power-44 seats meet only at zero, so the honest power-44
idempotent kills that class.  This is a positive projector theorem on the
genuine Kummer representation and the precise character correction suggested
by the Artin-route audit.
-/
import Fermat.FiftyNine.Conservation.LambdaLocalKummerClassAction59
import Fermat.FiftyNine.Conservation.TwistedLambdaReceiptCyclotomicRepresentative59

open scoped BigOperators NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.LambdaLocalKummerCharacterSeat59

set_option maxRecDepth 100000

open Fermat.Conservation.InvolutiveBase
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.LambdaLocalKummerClassAction59
open Fermat.FiftyNine.Conservation.LambdaReflectedLocalSeatAudit827
open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.TwistedLambdaReceiptCyclotomicRepresentative59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

/-- The scalar structure canonically induced by the exponent-59 law on the
local Kummer quotient. -/
noncomputable local instance instLambdaLocalKummerClass59ModuleZMod :
    Module (ZMod 59) (LambdaLocalKummerClass59 K) :=
  AddCommGroup.zmodModule
    (n := 59) (G := LambdaLocalKummerClass59 K)
    (lambdaLocalKummerClass59_nsmul_eq_zero K)

/-- The order `58` of the cyclotomic index group is invertible modulo `59`,
so its normalized character idempotents are defined. -/
noncomputable local instance instGaloisIndex59CardInvertibleZMod :
    Invertible (Fintype.card GaloisIndex59 : ZMod 59) :=
  invertibleOfNonzero (by
    rw [galoisIndex59_card]
    decide)

/-! ## Literal simultaneous character seats -/

/-- The simultaneous power-`t` eigenspace inside the actual lambda-local
Kummer quotient. -/
def lambdaLocalKummerPowerSeat59 (t : ZMod 58) :
    Submodule (ZMod 59) (LambdaLocalKummerClass59 K) where
  carrier := {x | ∀ sigma : GaloisIndex59,
    lambdaLocalKummerClassRepresentation59 K sigma x =
      ((powerCharacter59 t sigma : (ZMod 59)ˣ) : ZMod 59) • x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy sigma
    calc
      lambdaLocalKummerClassRepresentation59 K sigma (x + y) =
          lambdaLocalKummerClassRepresentation59 K sigma x +
            lambdaLocalKummerClassRepresentation59 K sigma y :=
        map_add _ x y
      _ = ((powerCharacter59 t sigma : (ZMod 59)ˣ) : ZMod 59) • x +
          ((powerCharacter59 t sigma : (ZMod 59)ˣ) : ZMod 59) • y := by
        rw [hx sigma, hy sigma]
      _ = ((powerCharacter59 t sigma : (ZMod 59)ˣ) : ZMod 59) • (x + y) :=
        (smul_add _ _ _).symm
  smul_mem' := by
    intro a x hx sigma
    calc
      lambdaLocalKummerClassRepresentation59 K sigma (a • x) =
          a • lambdaLocalKummerClassRepresentation59 K sigma x :=
        map_smul _ a x
      _ = a •
          (((powerCharacter59 t sigma : (ZMod 59)ˣ) : ZMod 59) • x) := by
        rw [hx sigma]
      _ = ((powerCharacter59 t sigma : (ZMod 59)ˣ) : ZMod 59) • (a • x) := by
        simp only [smul_smul]
        rw [mul_comm]

/-- Membership is exactly the displayed simultaneous eigenvalue law. -/
@[simp]
theorem mem_lambdaLocalKummerPowerSeat59_iff
    (t : ZMod 58) (x : LambdaLocalKummerClass59 K) :
    x ∈ lambdaLocalKummerPowerSeat59 K t ↔
      ∀ sigma : GaloisIndex59,
        lambdaLocalKummerClassRepresentation59 K sigma x =
          ((powerCharacter59 t sigma : (ZMod 59)ˣ) : ZMod 59) • x :=
  Iff.rfl

/-- The literal power-one local Kummer seat. -/
abbrev lambdaLocalKummerPowerOneSeat59 :=
  lambdaLocalKummerPowerSeat59 K (1 : ZMod 58)

/-- The literal power-44 local Kummer seat required by the old reflected
seating convention. -/
abbrev lambdaLocalKummerPowerFortyFourSeat59 :=
  lambdaLocalKummerPowerSeat59 K (44 : ZMod 58)

/-! ## The genuine normalized character projector -/

/-- The group idempotent for power `t` lands in its literal Kummer seat. -/
theorem lambdaLocalKummerCharacterIdempotent_mem_powerSeat59
    (t : ZMod 58) (x : LambdaLocalKummerClass59 K) :
    (lambdaLocalKummerClassRepresentation59 K).asAlgebraHom
        (characterIdempotent (powerCharacter59 t)) x ∈
      lambdaLocalKummerPowerSeat59 K t := by
  rw [mem_lambdaLocalKummerPowerSeat59_iff]
  intro sigma
  calc
    lambdaLocalKummerClassRepresentation59 K sigma
        ((lambdaLocalKummerClassRepresentation59 K).asAlgebraHom
          (characterIdempotent (powerCharacter59 t)) x) =
      (lambdaLocalKummerClassRepresentation59 K).asAlgebraHom
          (MonoidAlgebra.of (ZMod 59) GaloisIndex59 sigma)
          ((lambdaLocalKummerClassRepresentation59 K).asAlgebraHom
            (characterIdempotent (powerCharacter59 t)) x) := by
        rw [Representation.asAlgebraHom_of]
    _ = (lambdaLocalKummerClassRepresentation59 K).asAlgebraHom
          (MonoidAlgebra.of (ZMod 59) GaloisIndex59 sigma *
            characterIdempotent (powerCharacter59 t)) x := by
        rw [map_mul]
        rfl
    _ = (lambdaLocalKummerClassRepresentation59 K).asAlgebraHom
          (((powerCharacter59 t sigma : (ZMod 59)ˣ) : ZMod 59) •
            characterIdempotent (powerCharacter59 t)) x := by
        rw [groupElement_mul_characterIdempotent]
    _ = ((powerCharacter59 t sigma : (ZMod 59)ˣ) : ZMod 59) •
        (lambdaLocalKummerClassRepresentation59 K).asAlgebraHom
          (characterIdempotent (powerCharacter59 t)) x := by
        rw [map_smul]
        rfl

/-- The honest power-`t` projector on the actual local Kummer quotient. -/
noncomputable def lambdaLocalKummerPowerProjector59 (t : ZMod 58) :
    LambdaLocalKummerClass59 K →ₗ[ZMod 59]
      lambdaLocalKummerPowerSeat59 K t :=
  LinearMap.codRestrict (lambdaLocalKummerPowerSeat59 K t)
    ((lambdaLocalKummerClassRepresentation59 K).asAlgebraHom
      (characterIdempotent (powerCharacter59 t)))
    (lambdaLocalKummerCharacterIdempotent_mem_powerSeat59 K t)

@[simp]
theorem lambdaLocalKummerPowerProjector59_apply
    (t : ZMod 58) (x : LambdaLocalKummerClass59 K) :
    (lambdaLocalKummerPowerProjector59 K t x :
        LambdaLocalKummerClass59 K) =
      (lambdaLocalKummerClassRepresentation59 K).asAlgebraHom
        (characterIdempotent (powerCharacter59 t)) x :=
  rfl

/-- The character projector fixes every class already in its target seat. -/
theorem lambdaLocalKummerPowerProjector59_eq_self_of_mem
    (t : ZMod 58) (x : LambdaLocalKummerClass59 K)
    (hx : x ∈ lambdaLocalKummerPowerSeat59 K t) :
    (lambdaLocalKummerPowerProjector59 K t x :
        LambdaLocalKummerClass59 K) = x := by
  change (lambdaLocalKummerClassRepresentation59 K).asAlgebraHom
      (characterIdempotent (powerCharacter59 t)) x = x
  rw [characterIdempotent, map_smul, map_sum]
  simp only [LinearMap.smul_apply, Representation.asAlgebraHom_single]
  rw [mem_lambdaLocalKummerPowerSeat59_iff] at hx
  have heach (sigma : GaloisIndex59) :
      (((↑((powerCharacter59 t sigma)⁻¹) : ZMod 59) •
          lambdaLocalKummerClassRepresentation59 K sigma) :
          Module.End (ZMod 59) (LambdaLocalKummerClass59 K)) x = x := by
    change (↑((powerCharacter59 t sigma)⁻¹) : ZMod 59) •
        lambdaLocalKummerClassRepresentation59 K sigma x = x
    rw [hx sigma, ← mul_smul]
    simp
  change ⅟(Fintype.card GaloisIndex59 : ZMod 59) •
      ((∑ sigma ∈ Finset.univ,
        (↑((powerCharacter59 t sigma)⁻¹) : ZMod 59) •
          lambdaLocalKummerClassRepresentation59 K sigma) x) = x
  rw [LinearMap.sum_apply]
  simp_rw [heach]
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul (ZMod 59), smul_smul,
    invOf_mul_self, one_smul]

/-- Applying the genuine Kummer character projector twice changes nothing. -/
theorem lambdaLocalKummerPowerProjector59_idempotent
    (t : ZMod 58) (x : LambdaLocalKummerClass59 K) :
    lambdaLocalKummerPowerProjector59 K t
        (lambdaLocalKummerPowerProjector59 K t x).1 =
      lambdaLocalKummerPowerProjector59 K t x := by
  apply Subtype.ext
  change (lambdaLocalKummerClassRepresentation59 K).asAlgebraHom
      (characterIdempotent (powerCharacter59 t))
        ((lambdaLocalKummerClassRepresentation59 K).asAlgebraHom
          (characterIdempotent (powerCharacter59 t)) x) =
    (lambdaLocalKummerClassRepresentation59 K).asAlgebraHom
      (characterIdempotent (powerCharacter59 t)) x
  rw [← Module.End.mul_apply, ← map_mul,
    isIdempotentElem_iff.mp
      (characterIdempotent_isIdempotent (powerCharacter59 t))]

/-- Every character projector preserves every other power seat.  This is
the commutativity needed to turn a one-index character mismatch into exact
projector vanishing. -/
theorem lambdaLocalKummerPowerProjector59_preserves_powerSeat
    (s t : ZMod 58) (x : LambdaLocalKummerClass59 K)
    (hx : x ∈ lambdaLocalKummerPowerSeat59 K s) :
    (lambdaLocalKummerPowerProjector59 K t x :
        LambdaLocalKummerClass59 K) ∈
      lambdaLocalKummerPowerSeat59 K s := by
  rw [mem_lambdaLocalKummerPowerSeat59_iff] at hx ⊢
  intro sigma
  calc
    lambdaLocalKummerClassRepresentation59 K sigma
        ((lambdaLocalKummerClassRepresentation59 K).asAlgebraHom
          (characterIdempotent (powerCharacter59 t)) x) =
      (lambdaLocalKummerClassRepresentation59 K).asAlgebraHom
          (MonoidAlgebra.of (ZMod 59) GaloisIndex59 sigma)
          ((lambdaLocalKummerClassRepresentation59 K).asAlgebraHom
            (characterIdempotent (powerCharacter59 t)) x) := by
        rw [Representation.asAlgebraHom_of]
    _ = (lambdaLocalKummerClassRepresentation59 K).asAlgebraHom
          (MonoidAlgebra.of (ZMod 59) GaloisIndex59 sigma *
            characterIdempotent (powerCharacter59 t)) x := by
        rw [map_mul]
        rfl
    _ = (lambdaLocalKummerClassRepresentation59 K).asAlgebraHom
          (characterIdempotent (powerCharacter59 t) *
            MonoidAlgebra.of (ZMod 59) GaloisIndex59 sigma) x := by
        rw [mul_comm]
    _ = (lambdaLocalKummerClassRepresentation59 K).asAlgebraHom
          (characterIdempotent (powerCharacter59 t))
          ((lambdaLocalKummerClassRepresentation59 K).asAlgebraHom
            (MonoidAlgebra.of (ZMod 59) GaloisIndex59 sigma) x) := by
        rw [map_mul]
        rfl
    _ = (lambdaLocalKummerClassRepresentation59 K).asAlgebraHom
          (characterIdempotent (powerCharacter59 t))
          (lambdaLocalKummerClassRepresentation59 K sigma x) := by
        rw [Representation.asAlgebraHom_of]
    _ = (lambdaLocalKummerClassRepresentation59 K).asAlgebraHom
          (characterIdempotent (powerCharacter59 t))
          (((powerCharacter59 s sigma : (ZMod 59)ˣ) : ZMod 59) • x) := by
        rw [hx sigma]
    _ = ((powerCharacter59 s sigma : (ZMod 59)ˣ) : ZMod 59) •
        (lambdaLocalKummerClassRepresentation59 K).asAlgebraHom
          (characterIdempotent (powerCharacter59 t)) x := by
        rw [map_smul]

/-! ## W1's exact seat and the power-44 exclusion -/

/-- W1's explicit primitive local Kummer class lies in the genuine
power-one cyclotomic seat. -/
theorem reflectedPrimitiveKummerClass59_mem_powerOneSeat :
    reflectedPrimitiveKummerClass59 K ∈
      lambdaLocalKummerPowerOneSeat59 K := by
  rw [mem_lambdaLocalKummerPowerSeat59_iff]
  intro sigma
  change cyclotomicLambdaCompletionKummerHom59 K sigma
      (reflectedPrimitiveKummerClass59 K) = _
  calc
    cyclotomicLambdaCompletionKummerHom59 K sigma
        (reflectedPrimitiveKummerClass59 K) =
      (sigma : ZMod 59).val • reflectedPrimitiveKummerClass59 K :=
        cyclotomicLambdaCompletionKummerHom59_reflectedPrimitive K sigma
    _ = (sigma : ZMod 59) • reflectedPrimitiveKummerClass59 K := by
      calc
        (sigma : ZMod 59).val • reflectedPrimitiveKummerClass59 K =
            ((sigma : ZMod 59).val : ZMod 59) •
              reflectedPrimitiveKummerClass59 K :=
          (Nat.cast_smul_eq_nsmul (R := ZMod 59)
            (sigma : ZMod 59).val
            (reflectedPrimitiveKummerClass59 K)).symm
        _ = (sigma : ZMod 59) • reflectedPrimitiveKummerClass59 K := by
          rw [ZMod.natCast_zmod_val]
    _ = ((powerCharacter59 1 sigma : (ZMod 59)ˣ) : ZMod 59) •
        reflectedPrimitiveKummerClass59 K := by
      have hone : (1 : ZMod 58).val = 1 := by decide
      rw [powerCharacter59_apply, hone, pow_one]

/-- A class simultaneously seated in powers one and 44 is zero.  The
coefficient mismatch is witnessed already by the cyclotomic index `2`. -/
theorem eq_zero_of_mem_powerOneSeat_and_powerFortyFourSeat
    (x : LambdaLocalKummerClass59 K)
    (hone : x ∈ lambdaLocalKummerPowerOneSeat59 K)
    (hfortyFour : x ∈ lambdaLocalKummerPowerFortyFourSeat59 K) :
    x = 0 := by
  have honeTwo :=
    (mem_lambdaLocalKummerPowerSeat59_iff K 1 x).mp hone auditTwoIndex59
  have hfortyFourTwo :=
    (mem_lambdaLocalKummerPowerSeat59_iff K 44 x).mp hfortyFour auditTwoIndex59
  have hcoeff :
      ((powerCharacter59 1 auditTwoIndex59 : (ZMod 59)ˣ) : ZMod 59) ≠
        ((powerCharacter59 44 auditTwoIndex59 : (ZMod 59)ˣ) : ZMod 59) := by
    decide +kernel +revert
  have heq :
      ((powerCharacter59 1 auditTwoIndex59 : (ZMod 59)ˣ) : ZMod 59) • x =
        ((powerCharacter59 44 auditTwoIndex59 : (ZMod 59)ˣ) : ZMod 59) • x :=
    honeTwo.symm.trans hfortyFourTwo
  have hzero :
      (((powerCharacter59 1 auditTwoIndex59 : (ZMod 59)ˣ) : ZMod 59) -
        ((powerCharacter59 44 auditTwoIndex59 : (ZMod 59)ˣ) : ZMod 59)) • x = 0 := by
    calc
      (((powerCharacter59 1 auditTwoIndex59 : (ZMod 59)ˣ) : ZMod 59) -
          ((powerCharacter59 44 auditTwoIndex59 : (ZMod 59)ˣ) : ZMod 59)) • x =
        ((powerCharacter59 1 auditTwoIndex59 : (ZMod 59)ˣ) : ZMod 59) • x -
          ((powerCharacter59 44 auditTwoIndex59 : (ZMod 59)ˣ) : ZMod 59) • x :=
        sub_smul _ _ x
      _ = 0 := sub_eq_zero.mpr heq
  exact (smul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hcoeff)

/-- The two literal Kummer seats have zero intersection. -/
theorem powerOneSeat_inf_powerFortyFourSeat_eq_bot :
    lambdaLocalKummerPowerOneSeat59 K ⊓
        lambdaLocalKummerPowerFortyFourSeat59 K = ⊥ := by
  ext x
  constructor
  · intro hx
    rw [Submodule.mem_inf] at hx
    rw [Submodule.mem_bot]
    exact eq_zero_of_mem_powerOneSeat_and_powerFortyFourSeat K x hx.1 hx.2
  · intro hx
    rw [Submodule.mem_bot] at hx
    subst x
    simp

/-- W1's nonzero primitive class cannot inhabit the power-44 seat. -/
theorem reflectedPrimitiveKummerClass59_not_mem_powerFortyFourSeat :
    reflectedPrimitiveKummerClass59 K ∉
      lambdaLocalKummerPowerFortyFourSeat59 K := by
  intro hfortyFour
  exact reflectedPrimitiveKummerClass59_ne_zero K
    (eq_zero_of_mem_powerOneSeat_and_powerFortyFourSeat K
      (reflectedPrimitiveKummerClass59 K)
      (reflectedPrimitiveKummerClass59_mem_powerOneSeat K)
      hfortyFour)

/-- The honest power-one projector fixes W1's primitive Kummer class. -/
theorem powerOneProjector_reflectedPrimitiveKummerClass59_eq_self :
    (lambdaLocalKummerPowerProjector59 K 1
        (reflectedPrimitiveKummerClass59 K) :
      LambdaLocalKummerClass59 K) = reflectedPrimitiveKummerClass59 K :=
  lambdaLocalKummerPowerProjector59_eq_self_of_mem K 1
    (reflectedPrimitiveKummerClass59 K)
    (reflectedPrimitiveKummerClass59_mem_powerOneSeat K)

/-- The honest power-44 projector kills W1's primitive Kummer class. -/
theorem powerFortyFourProjector_reflectedPrimitiveKummerClass59_eq_zero :
    (lambdaLocalKummerPowerProjector59 K 44
        (reflectedPrimitiveKummerClass59 K) :
      LambdaLocalKummerClass59 K) = 0 := by
  apply eq_zero_of_mem_powerOneSeat_and_powerFortyFourSeat K
  · exact lambdaLocalKummerPowerProjector59_preserves_powerSeat K 1 44
      (reflectedPrimitiveKummerClass59 K)
      (reflectedPrimitiveKummerClass59_mem_powerOneSeat K)
  · exact (lambdaLocalKummerPowerProjector59 K 44
      (reflectedPrimitiveKummerClass59 K)).property

/-! ## Kernel-trust audit -/

/--
info: 'Fermat.FiftyNine.Conservation.LambdaLocalKummerCharacterSeat59.reflectedPrimitiveKummerClass59_mem_powerOneSeat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms reflectedPrimitiveKummerClass59_mem_powerOneSeat

/--
info: 'Fermat.FiftyNine.Conservation.LambdaLocalKummerCharacterSeat59.lambdaLocalKummerPowerProjector59_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms lambdaLocalKummerPowerProjector59_idempotent

/--
info: 'Fermat.FiftyNine.Conservation.LambdaLocalKummerCharacterSeat59.powerFortyFourProjector_reflectedPrimitiveKummerClass59_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms powerFortyFourProjector_reflectedPrimitiveKummerClass59_eq_zero

end Fermat.FiftyNine.Conservation.LambdaLocalKummerCharacterSeat59
