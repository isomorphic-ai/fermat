/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Auditing the reflected lambda-local character seat

`7A-ARTIN-READ.md` asks for the reflected character quotient/seat inside
the lambda-local continuous `H¹`.  The current local cohomology API exposes
the honest module `LambdaRootsContinuousH1 K`, but it does not yet expose the
outer cyclotomic `GaloisIndex59` action on that cohomology group.

There is a dangerous near miss: because `GaloisIndex59` is definitionally
`(ZMod 59)ˣ`, typeclass search finds its ordinary scalar action on every
`ZMod 59`-module.  That is not the cyclotomic action on the local field or
on continuous cohomology.  The scalar action has power-one character and,
if mistakenly used as the local action, its power-44 reflected eigenspace
is zero.  This file proves that failure explicitly.

The rest of the file gives the strongest honest current interface.  For an
actual local representation it defines the reflected character submodule,
states localization covariance as a plain proposition, and proves that this
proposition is exactly the landing theorem required for all genuine global
reflected localizations.  A second explicit condition seats W1's retained
local receipt.  Their conjunction is equivalent to containment of the
smallest currently constructible required carrier.

No local action, covariance theorem, provider, certificate, or arithmetic
postulate is manufactured here.
-/
import Fermat.Exponents.FiftyNine.Conservation.CanonicalW1PointedIncidenceBridge827

open scoped NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.LambdaReflectedLocalSeatAudit827

open Fermat.Conservation
open Fermat.Conservation.InvolutiveBase
open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.CanonicalW1PointedIncidenceBridge827
open Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827
open Fermat.FiftyNine.Conservation.LambdaOrbitAffineKernelCriterion827
open Fermat.FiftyNine.Conservation.PointedTateIncidence
open Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

noncomputable local instance instQRelaxedReflectedDual827ModuleZMod :
    Module (ZMod 59)
      (QRelaxedReflectedDual827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59) :=
  AddCommGroup.zmodModule
    (qRelaxedReflectedDual827_nsmul_eq_zero
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59)

/-! ## The scalar-action trap -/

/-- The unit `2`, used to distinguish the tautological scalar action from
the required reflected power-44 cyclotomic action. -/
def auditTwoIndex59 : GaloisIndex59 :=
  Units.mk0 (2 : ZMod 59) (by decide)

/-- The representation obtained from the automatically available action of
`(ZMod 59)ˣ` by scalar multiplication.  It is a lawful representation, but
it is not an action induced from automorphisms of the lambda-local field. -/
def scalarUnitsRepresentationOnLambdaH1827 :
    Representation (ZMod 59) GaloisIndex59
      (LambdaRootsContinuousH1 K) where
  toFun sigma := (sigma : ZMod 59) • LinearMap.id
  map_one' := by
    ext x
    simp
  map_mul' sigma tau := by
    ext x
    simp only [LinearMap.smul_apply, LinearMap.id_apply,
      Module.End.mul_apply]
    rw [Units.val_mul, mul_smul]

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
@[simp]
theorem scalarUnitsRepresentationOnLambdaH1827_apply
    (sigma : GaloisIndex59) (x : LambdaRootsContinuousH1 K) :
    scalarUnitsRepresentationOnLambdaH1827 (K := K) sigma x =
      (sigma : ZMod 59) • x := by
  rfl

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- A vector satisfying the reflected power-44 eigencondition for the
tautological scalar-units representation must vanish.  Thus the inferred
units action cannot be reused as the sought outer cyclotomic action. -/
theorem eq_zero_of_scalarUnits_reflected_eigen
    (x : LambdaRootsContinuousH1 K)
    (hx : ∀ sigma : GaloisIndex59,
      scalarUnitsRepresentationOnLambdaH1827 (K := K) sigma x =
        ((orientedPrimalMode827 canonicalTeichmullerCharacter59
          irregularCharacter59 sigma : (ZMod 59)ˣ) : ZMod 59) • x) :
    x = 0 := by
  have htwo := hx auditTwoIndex59
  rw [scalarUnitsRepresentationOnLambdaH1827_apply,
    orientedPrimalMode827_canonical_irregular] at htwo
  have hcoeff :
      (auditTwoIndex59 : ZMod 59) ≠
        ((powerCharacter59 44 auditTwoIndex59 : (ZMod 59)ˣ) : ZMod 59) := by
    decide +kernel +revert
  have hzero :
      ((auditTwoIndex59 : ZMod 59) -
        ((powerCharacter59 44 auditTwoIndex59 : (ZMod 59)ˣ) : ZMod 59)) • x = 0 := by
    rw [sub_smul, htwo, sub_self]
  exact (smul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hcoeff)

/-! ## The honest action-parametric seat -/

/-- The exact type of an outer cyclotomic action still needed on lambda-local
continuous `H¹`.  This is a type alias, not an installed action or provider. -/
abbrev LambdaLocalDeltaRepresentation59 (K : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {59} ℚ K] :=
  Representation (ZMod 59) GaloisIndex59 (LambdaRootsContinuousH1 K)

/-- Given an actual outer local action, its reflected power-44 character
seat is the simultaneous eigenspace inside genuine continuous local `H¹`. -/
def lambdaReflectedLocalCharacterSeat827
    (rhoLocal : LambdaLocalDeltaRepresentation59 K) :
    Submodule (ZMod 59) (LambdaRootsContinuousH1 K) where
  carrier := {r | ∀ sigma : GaloisIndex59,
    rhoLocal sigma r =
      ((orientedPrimalMode827 canonicalTeichmullerCharacter59
        irregularCharacter59 sigma : (ZMod 59)ˣ) : ZMod 59) • r}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy sigma
    rw [map_add, hx sigma, hy sigma, smul_add]
  smul_mem' := by
    intro a x hx sigma
    rw [map_smul, hx sigma, smul_smul, smul_smul, mul_comm]

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
@[simp]
theorem mem_lambdaReflectedLocalCharacterSeat827_iff
    (rhoLocal : LambdaLocalDeltaRepresentation59 K)
    (r : LambdaRootsContinuousH1 K) :
    r ∈ lambdaReflectedLocalCharacterSeat827 (K := K) rhoLocal ↔
      ∀ sigma : GaloisIndex59,
        rhoLocal sigma r =
          ((orientedPrimalMode827 canonicalTeichmullerCharacter59
            irregularCharacter59 sigma : (ZMod 59)ˣ) : ZMod 59) • r :=
  Iff.rfl

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- The reflected character seat cut out using the accidental scalar-units
representation is literally zero.  This prevents the typeclass-generated
action from masquerading as the missing outer cyclotomic action. -/
theorem lambdaReflectedLocalCharacterSeat827_scalarUnits_eq_bot :
    lambdaReflectedLocalCharacterSeat827 (K := K)
        (scalarUnitsRepresentationOnLambdaH1827 (K := K)) = ⊥ := by
  ext x
  constructor
  · intro hx
    rw [Submodule.mem_bot]
    exact eq_zero_of_scalarUnits_reflected_eigen x
      ((mem_lambdaReflectedLocalCharacterSeat827_iff
        (K := K) _ x).mp hx)
  · intro hx
    rw [Submodule.mem_bot] at hx
    subst x
    exact Submodule.zero_mem _

/-- The exact missing global-to-local covariance statement.  It asserts
that localization intertwines the actual reflected global action with the
supplied outer action on continuous local `H¹`, after reducing the reflected
character to `ZMod 59`.  No inhabitant is supplied by the current API. -/
abbrev LambdaReflectedLocalizationCovariance827
    (rhoLocal : LambdaLocalDeltaRepresentation59 K) : Prop :=
  ∀ sigma : GaloisIndex59,
    ∀ y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59,
      rhoLocal sigma
          (lambdaReflectedLocalizationLinear827 (K := K)
            canonicalTeichmullerCharacter59 irregularCharacter59 y) =
        ((orientedPrimalMode827 canonicalTeichmullerCharacter59
          irregularCharacter59 sigma : (ZMod 59)ˣ) : ZMod 59) •
          lambdaReflectedLocalizationLinear827 (K := K)
            canonicalTeichmullerCharacter59 irregularCharacter59 y

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- Covariance is literally equivalent to the desired landing of every
actual reflected q-relaxed global class in the local reflected seat. -/
theorem lambdaReflectedLocalization_lands_iff_covariance
    (rhoLocal : LambdaLocalDeltaRepresentation59 K) :
    (∀ y : QRelaxedReflectedDual827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59,
      lambdaReflectedLocalizationLinear827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 y ∈
        lambdaReflectedLocalCharacterSeat827 (K := K) rhoLocal) ↔
      LambdaReflectedLocalizationCovariance827 (K := K) rhoLocal := by
  constructor
  · intro h sigma y
    exact (mem_lambdaReflectedLocalCharacterSeat827_iff
      (K := K) rhoLocal _).mp (h y) sigma
  · intro h y
    exact (mem_lambdaReflectedLocalCharacterSeat827_iff
      (K := K) rhoLocal _).mpr (fun sigma ↦ h sigma y)

/-- The independent local seating condition for W1's retained reflected
factor.  It is separate from localization covariance because the current
global reflected Selmer API does not exhibit that receipt as the
localization of a reflected eigenspace class. -/
abbrev TwistedLambdaReceiptReflectedSeating827
    (rhoLocal : LambdaLocalDeltaRepresentation59 K) : Prop :=
  (twistedLambdaCupReceipt59 K).reflected ∈
    lambdaReflectedLocalCharacterSeat827 (K := K) rhoLocal

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
theorem twistedLambdaReceiptReflectedSeating827_iff
    (rhoLocal : LambdaLocalDeltaRepresentation59 K) :
    TwistedLambdaReceiptReflectedSeating827 (K := K) rhoLocal ↔
      ∀ sigma : GaloisIndex59,
        rhoLocal sigma (twistedLambdaCupReceipt59 K).reflected =
          ((orientedPrimalMode827 canonicalTeichmullerCharacter59
            irregularCharacter59 sigma : (ZMod 59)ˣ) : ZMod 59) •
            (twistedLambdaCupReceipt59 K).reflected :=
  mem_lambdaReflectedLocalCharacterSeat827_iff
    (K := K) rhoLocal (twistedLambdaCupReceipt59 K).reflected

/-! ## The smallest carrier justified by current constructions -/

/-- Without an outer local action, the smallest honest submodule known to
contain both every genuine reflected global localization and W1's retained
reflected factor.  It is deliberately called a required carrier, not a
character seat. -/
def lambdaReflectedRequiredCarrier827 :
    Submodule (ZMod 59) (LambdaRootsContinuousH1 K) :=
  LinearMap.range
      (lambdaReflectedLocalizationLinear827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59) ⊔
    Submodule.span (ZMod 59) {(twistedLambdaCupReceipt59 K).reflected}

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- The required carrier is minimal: a candidate local submodule contains
it exactly when it contains every genuine reflected localization and the W1
receipt factor. -/
theorem lambdaReflectedRequiredCarrier827_le_iff
    (W : Submodule (ZMod 59) (LambdaRootsContinuousH1 K)) :
    lambdaReflectedRequiredCarrier827 (K := K) ≤ W ↔
      (∀ y : QRelaxedReflectedDual827
          (cyclotomicQRelaxedSelmerRepresentation827 K)
          canonicalTeichmullerCharacter59 irregularCharacter59,
        lambdaReflectedLocalizationLinear827 (K := K)
            canonicalTeichmullerCharacter59 irregularCharacter59 y ∈ W) ∧
      (twistedLambdaCupReceipt59 K).reflected ∈ W := by
  constructor
  · intro h
    constructor
    · intro y
      apply h
      unfold lambdaReflectedRequiredCarrier827
      apply (le_sup_left :
        LinearMap.range
            (lambdaReflectedLocalizationLinear827 (K := K)
              canonicalTeichmullerCharacter59 irregularCharacter59) ≤ _)
      exact ⟨y, rfl⟩
    · apply h
      unfold lambdaReflectedRequiredCarrier827
      apply (le_sup_right :
        Submodule.span (ZMod 59)
          {(twistedLambdaCupReceipt59 K).reflected} ≤ _)
      exact Submodule.subset_span (Set.mem_singleton _)
  · rintro ⟨hloc, hreceipt⟩
    apply sup_le
    · rintro _ ⟨y, rfl⟩
      exact hloc y
    · exact Submodule.span_le.mpr
        (Set.singleton_subset_iff.mpr hreceipt)

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- Consequently, an actual outer action seats every local object needed by
the W1/PT construction exactly when both compiler-visible covariance
obligations hold.  This is the strongest current landing criterion; proving
either obligation requires new local-action naturality, not more linear
algebra on the existing ambient module. -/
theorem lambdaReflectedRequiredCarrier827_le_characterSeat_iff
    (rhoLocal : LambdaLocalDeltaRepresentation59 K) :
    lambdaReflectedRequiredCarrier827 (K := K) ≤
        lambdaReflectedLocalCharacterSeat827 (K := K) rhoLocal ↔
      LambdaReflectedLocalizationCovariance827 (K := K) rhoLocal ∧
        TwistedLambdaReceiptReflectedSeating827 (K := K) rhoLocal := by
  rw [lambdaReflectedRequiredCarrier827_le_iff]
  exact and_congr
    (lambdaReflectedLocalization_lands_iff_covariance
      (K := K) rhoLocal)
    Iff.rfl

/-! ## Axiom guards -/

/--
info: 'Fermat.FiftyNine.Conservation.LambdaReflectedLocalSeatAudit827.lambdaReflectedLocalCharacterSeat827_scalarUnits_eq_bot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms lambdaReflectedLocalCharacterSeat827_scalarUnits_eq_bot

/--
info: 'Fermat.FiftyNine.Conservation.LambdaReflectedLocalSeatAudit827.lambdaReflectedLocalization_lands_iff_covariance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms lambdaReflectedLocalization_lands_iff_covariance

/--
info: 'Fermat.FiftyNine.Conservation.LambdaReflectedLocalSeatAudit827.lambdaReflectedRequiredCarrier827_le_characterSeat_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms lambdaReflectedRequiredCarrier827_le_characterSeat_iff

end Fermat.FiftyNine.Conservation.LambdaReflectedLocalSeatAudit827
