/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The compatible Kummer lift at 59

This module constructs the actual continuous `C_(59²)` coordinate of a
chosen `59²`-th Kummer root.  Its reduction is the genuine oriented Kummer
character, and its Galois multiplication law has exactly the cyclotomic
twist required by the concrete second-digit bridge.

Consequently the bridge's two explicit producer inputs are discharged from
root data, giving the actual `H²` equality between the pulled carry class and
the genuine oriented Kummer cup without a per-prime certificate or an added
assumption.
-/
import Fermat.Experiments.Conservation.OrientedKummerRepresentative59
import Fermat.Experiments.Conservation.ContinuousCarryLiftObstruction59
import Fermat.Experiments.Conservation.IntegratedTwistedKummerCup59

noncomputable section

namespace Fermat.Conservation.CompatibleKummerLift59

open CategoryTheory ContinuousCohomology
open Fermat.Conservation.LocalKummerH1
open Fermat.Conservation.KummerOrientation
open Fermat.Conservation.ContinuousKummerOrientation
open Fermat.Conservation.ContinuousKummerH1
open Fermat.Conservation.ContinuousKummerTateCupRaw
open Fermat.Conservation.ContinuousKummerTateCup.Nominal
open Fermat.Conservation.ContinuousKummerTateAlgebra
open Fermat.Conservation.ContinuousCarryLiftObstruction59
open Fermat.Conservation.OrientedKummerRepresentative59

open scoped LocalKummerH1.KummerRootsDiscrete Pointwise

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (F : Type) [Field F]

/-- A unit-valued `n`-th root in the chosen algebraic closure. -/
theorem exists_rootUnit_of_baseUnit
    (n : ℕ) [NeZero n] (a : Fˣ) :
    ∃ r : (AlgebraicClosure F)ˣ,
      r ^ n = Units.map
        (algebraMap F (AlgebraicClosure F)).toMonoidHom a := by
  obtain ⟨r, hr⟩ :=
    IsAlgClosed.exists_pow_nat_eq
      (algebraMap F (AlgebraicClosure F) (a : F)) (NeZero.pos n)
  have ha : algebraMap F (AlgebraicClosure F) (a : F) ≠ 0 := by
    simpa only [map_zero] using
      (algebraMap F (AlgebraicClosure F)).injective.ne (Units.ne_zero a)
  have hr0 : r ≠ 0 := by
    intro h
    apply ha
    rw [← hr, h, zero_pow (NeZero.ne n)]
  refine ⟨Units.mk0 r hr0, ?_⟩
  apply Units.ext
  exact hr

/-- A chosen 59-th root of the embedded primitive 59-th root. -/
def cyclotomicRoot3481
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) :
    (AlgebraicClosure F)ˣ :=
  (exists_rootUnit_of_baseUnit F 59
    (primitiveUnit 59 F zeta hzeta)).choose

@[simp]
theorem cyclotomicRoot3481_pow59
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) :
    cyclotomicRoot3481 F zeta hzeta ^ 59 =
      algebraicPrimitiveUnit 59 F zeta hzeta :=
  (exists_rootUnit_of_baseUnit F 59
    (primitiveUnit 59 F zeta hzeta)).choose_spec

/-- The compatible cyclotomic root has exact order `59²`. -/
theorem cyclotomicRoot3481_isPrimitive
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) :
    IsPrimitiveRoot (cyclotomicRoot3481 F zeta hzeta) (59 ^ 2) := by
  let xi := cyclotomicRoot3481 F zeta hzeta
  let zetaA := algebraicPrimitiveUnit 59 F zeta hzeta
  have hpow : xi ^ 59 = zetaA := cyclotomicRoot3481_pow59 F zeta hzeta
  have hzetaA : IsPrimitiveRoot zetaA 59 :=
    algebraicPrimitiveUnit_isPrimitive 59 F zeta hzeta
  refine ⟨?_, ?_⟩
  · rw [show 59 ^ 2 = 59 * 59 by norm_num, pow_mul, hpow]
    exact hzetaA.pow_eq_one
  · intro l hl
    have hzpow : zetaA ^ l = 1 := by
      calc
        zetaA ^ l = (xi ^ 59) ^ l := by rw [hpow]
        _ = xi ^ (59 * l) := by rw [pow_mul]
        _ = xi ^ (l * 59) := by rw [Nat.mul_comm]
        _ = (xi ^ l) ^ 59 := by rw [pow_mul]
        _ = 1 := by rw [hl, one_pow]
    obtain ⟨k, rfl⟩ := hzetaA.dvd_of_pow_eq_one l hzpow
    have hxpow : xi ^ (59 * k) = 1 := hl
    have hkpow : zetaA ^ k = 1 := by
      rw [← hpow, ← pow_mul]
      exact hxpow
    obtain ⟨m, rfl⟩ := hzetaA.dvd_of_pow_eq_one k hkpow
    use m
    ring

/-- A chosen compatible `59²`-th root of a base-field unit. -/
def kummerRoot3481 (a : Fˣ) : (AlgebraicClosure F)ˣ :=
  (exists_rootUnit_of_baseUnit F (59 ^ 2) a).choose

@[simp]
theorem kummerRoot3481_pow (a : Fˣ) :
    kummerRoot3481 F a ^ (59 ^ 2) =
      Units.map (algebraMap F (AlgebraicClosure F)).toMonoidHom a :=
  (exists_rootUnit_of_baseUnit F (59 ^ 2) a).choose_spec

/-- The compatible root's Kummer ratio as a `59²`-th root of unity. -/
def compatibleCocycleValue3481
    (a : Fˣ) (g : AbsoluteGalois F) : KummerRoots (59 ^ 2) F :=
  ⟨g • kummerRoot3481 F a / kummerRoot3481 F a, by
    rw [mem_rootsOfUnity, div_pow, ← smul_pow', kummerRoot3481_pow]
    have hfix :
        g • Units.map (algebraMap F (AlgebraicClosure F)).toMonoidHom a =
          Units.map (algebraMap F (AlgebraicClosure F)).toMonoidHom a := by
      apply Units.ext
      exact g.commutes (a : F)
    rw [hfix]
    simp⟩

@[simp]
theorem compatibleCocycleValue3481_coe
    (a : Fˣ) (g : AbsoluteGalois F) :
    (compatibleCocycleValue3481 F a g : (AlgebraicClosure F)ˣ) =
      g • kummerRoot3481 F a / kummerRoot3481 F a :=
  rfl

/-- The compatible chosen-root cocycle is continuous for the Krull topology
and the discrete topology on roots of unity. -/
theorem continuous_compatibleCocycleValue3481 (a : Fˣ) :
    Continuous (compatibleCocycleValue3481 F a) := by
  rw [continuous_discrete_rng]
  intro theta
  by_cases hfiber : ∃ tau, compatibleCocycleValue3481 F a tau = theta
  · obtain ⟨tau, htau⟩ := hfiber
    let r : (AlgebraicClosure F)ˣ := kummerRoot3481 F a
    have hopen :
        IsOpen (MulAction.stabilizer (AbsoluteGalois F)
          (r : AlgebraicClosure F) : Set (AbsoluteGalois F)) := by
      convert stabilizer_isOpen_of_isIntegral
        (K := F) (L := AlgebraicClosure F) r using 1
    have hfiber_eq :
        compatibleCocycleValue3481 F a ⁻¹' {theta} =
          tau • (MulAction.stabilizer (AbsoluteGalois F)
            (r : AlgebraicClosure F) : Set (AbsoluteGalois F)) := by
      ext sigma
      rw [Set.mem_preimage, Set.mem_singleton_iff, ← htau,
        mem_leftCoset_iff, SetLike.mem_coe, MulAction.mem_stabilizer_iff]
      constructor
      · intro heq
        have hunit : sigma • r = tau • r := by
          apply div_left_injective
          exact congrArg Subtype.val heq
        have hval : sigma • (r : AlgebraicClosure F) =
            tau • (r : AlgebraicClosure F) := by
          simpa only [coe_absoluteGalois_smul_unit] using
            congrArg Units.val hunit
        rw [mul_smul, inv_smul_eq_iff]
        exact hval
      · intro hfix
        rw [mul_smul, inv_smul_eq_iff] at hfix
        apply Subtype.ext
        change sigma • r / r = tau • r / r
        rw [div_left_inj]
        apply Units.ext
        simpa only [coe_absoluteGalois_smul_unit] using hfix
    rw [hfiber_eq]
    exact hopen.leftCoset tau
  · have hfiber_eq : compatibleCocycleValue3481 F a ⁻¹' {theta} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro sigma hsigma
      apply hfiber
      exact ⟨sigma, by simpa using hsigma⟩
    rw [hfiber_eq]
    exact isOpen_empty

/-! ## Compatible primitive-root coordinates -/

/-- All `59²`-th roots of unity identified with powers of the chosen root
whose 59-th power is the supplied base-field primitive root. -/
def rootsEquivZPowers3481
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) :
    KummerRoots (59 ^ 2) F ≃*
      Subgroup.zpowers (cyclotomicRoot3481 F zeta hzeta) :=
  MulEquiv.subgroupCongr
    (cyclotomicRoot3481_isPrimitive F zeta hzeta).zpowers_eq.symm

/-- Additive coordinates on `mu_(59²)`, compatible with the supplied
orientation on `mu_59`. -/
def coordinateAddEquiv3481
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) :
    Additive (KummerRoots (59 ^ 2) F) ≃+ ZMod (59 ^ 2) :=
  (MulEquiv.toAdditive (rootsEquivZPowers3481 F zeta hzeta)).trans
    (cyclotomicRoot3481_isPrimitive F zeta hzeta).zmodEquivZPowers.symm

/-- The coordinate of the compatible chosen-root Kummer cocycle. -/
def compatibleKummerCoordinate3481Value
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) (a : Fˣ) :
    C(AbsoluteGalois F, ZMod (59 ^ 2)) where
  toFun g := coordinateAddEquiv3481 F zeta hzeta
    (Additive.ofMul (compatibleCocycleValue3481 F a g))
  continuous_toFun := by
    have hcoordinate : Continuous
        (fun theta : Additive (KummerRoots (59 ^ 2) F) ↦
          coordinateAddEquiv3481 F zeta hzeta theta) :=
      continuous_of_discreteTopology
    exact hcoordinate.comp (continuous_compatibleCocycleValue3481 F a)

/-- The actual continuous `C_(59²)` cochain to be fed to the second-digit
bridge. -/
def compatibleKummerCoordinate3481
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) (a : Fˣ) :
    C(AbsoluteGalois F, CyclicGroup59Squared) where
  toFun g := Multiplicative.ofAdd
    (compatibleKummerCoordinate3481Value F zeta hzeta a g)
  continuous_toFun :=
    (compatibleKummerCoordinate3481Value F zeta hzeta a).continuous

@[simp]
theorem coordinateAddEquiv3481_symm_intCast_coe
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) (i : ℤ) :
    (((coordinateAddEquiv3481 F zeta hzeta).symm
          (i : ZMod (59 ^ 2))).toMul : (AlgebraicClosure F)ˣ) =
      cyclotomicRoot3481 F zeta hzeta ^ i := by
  change
    (((rootsEquivZPowers3481 F zeta hzeta).symm
      (((cyclotomicRoot3481_isPrimitive F zeta hzeta).zmodEquivZPowers
        (i : ZMod (59 ^ 2))).toMul) :
        KummerRoots (59 ^ 2) F) : (AlgebraicClosure F)ˣ) = _
  rw [IsPrimitiveRoot.zmodEquivZPowers_apply_coe_int]
  rfl

set_option maxHeartbeats 10000 in
@[simp]
theorem coordinateAddEquiv3481_symm_natCast_coe
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) (i : ℕ) :
    (((coordinateAddEquiv3481 F zeta hzeta).symm
          (i : ZMod (59 ^ 2))).toMul : (AlgebraicClosure F)ˣ) =
      cyclotomicRoot3481 F zeta hzeta ^ i := by
  rw [show (i : ZMod (59 ^ 2)) = ((i : ℤ) : ZMod (59 ^ 2)) by
    norm_num]
  rw [coordinateAddEquiv3481_symm_intCast_coe, zpow_natCast]

@[simp]
theorem coordinateAddEquiv59_symm_intCast_coe
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) (i : ℤ) :
    (((coordinateAddEquiv 59 F zeta hzeta).symm
          (i : ZMod 59)).toMul : (AlgebraicClosure F)ˣ) =
      algebraicPrimitiveUnit 59 F zeta hzeta ^ i := by
  change
    (((rootsEquivZPowers 59 F zeta hzeta).symm
      (((algebraicPrimitiveUnit_isPrimitive 59 F zeta hzeta).zmodEquivZPowers
        (i : ZMod 59)).toMul) : KummerRoots 59 F) :
        (AlgebraicClosure F)ˣ) = _
  rw [IsPrimitiveRoot.zmodEquivZPowers_apply_coe_int]
  rfl

@[simp]
theorem coordinateAddEquiv59_symm_natCast_coe
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) (i : ℕ) :
    (((coordinateAddEquiv 59 F zeta hzeta).symm
          (i : ZMod 59)).toMul : (AlgebraicClosure F)ˣ) =
      algebraicPrimitiveUnit 59 F zeta hzeta ^ i := by
  rw [show (i : ZMod 59) = ((i : ℤ) : ZMod 59) by norm_num]
  rw [coordinateAddEquiv59_symm_intCast_coe, zpow_natCast]

/-- Raising a `59²`-th root of unity to the 59-th power lands in
`mu_59`. -/
def pow59Root
    (theta : KummerRoots (59 ^ 2) F) : KummerRoots 59 F :=
  ⟨(theta : (AlgebraicClosure F)ˣ) ^ 59, by
    rw [mem_rootsOfUnity, ← pow_mul]
    norm_num [pow_two]
    exact theta.prop⟩

@[simp]
theorem pow59Root_coe (theta : KummerRoots (59 ^ 2) F) :
    (pow59Root F theta : (AlgebraicClosure F)ˣ) =
      (theta : (AlgebraicClosure F)ˣ) ^ 59 :=
  rfl

/-- The compatible coordinates commute with 59-th powering and reduction
from `ZMod (59²)` to `ZMod 59`. -/
theorem coordinateAddEquiv_pow59Root
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (theta : KummerRoots (59 ^ 2) F) :
    coordinateAddEquiv 59 F zeta hzeta
        (Additive.ofMul (pow59Root F theta)) =
      ZMod.castHom (by norm_num : 59 ∣ 59 ^ 2) (ZMod 59)
        (coordinateAddEquiv3481 F zeta hzeta (Additive.ofMul theta)) := by
  obtain ⟨i, hi⟩ := ZMod.intCast_surjective
    (coordinateAddEquiv3481 F zeta hzeta (Additive.ofMul theta))
  apply (coordinateAddEquiv 59 F zeta hzeta).symm.injective
  rw [AddEquiv.symm_apply_apply]
  rw [← hi, map_intCast]
  apply Additive.toMul.injective
  apply Subtype.ext
  change (theta : (AlgebraicClosure F)ˣ) ^ 59 =
    (((coordinateAddEquiv 59 F zeta hzeta).symm
      (i : ZMod 59)).toMul : (AlgebraicClosure F)ˣ)
  rw [coordinateAddEquiv59_symm_intCast_coe]
  have htheta := congrArg
    (fun x : Additive (KummerRoots (59 ^ 2) F) ↦
      (x.toMul : (AlgebraicClosure F)ˣ))
    ((coordinateAddEquiv3481 F zeta hzeta).symm_apply_apply
      (Additive.ofMul theta))
  rw [← hi, coordinateAddEquiv3481_symm_intCast_coe] at htheta
  have htheta' : (theta : (AlgebraicClosure F)ˣ) =
      cyclotomicRoot3481 F zeta hzeta ^ i := by
    simpa using htheta.symm
  rw [htheta', ← zpow_natCast, ← zpow_mul]
  rw [mul_comm, zpow_mul]
  rw [zpow_natCast, cyclotomicRoot3481_pow59]

/-! ## Reduction to the genuine oriented Kummer character -/

/-- The 59-th power of the compatible `mu_(59²)` cocycle is the public
chosen-root `mu_59` Kummer cocycle.  Root-choice independence is valid here
because the chosen primitive root lies in the base field. -/
theorem pow59_compatibleCocycleValue3481_eq_continuousCocycle
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (a : Fˣ) (g : AbsoluteGalois F) :
    Additive.ofMul
        (pow59Root F (compatibleCocycleValue3481 F a g)) =
      Fermat.Conservation.ContinuousKummerH1.continuousCocycle 59 F a g := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change
    (g • kummerRoot3481 F a / kummerRoot3481 F a) ^ 59 =
      (cocycleValue 59 F a g : (AlgebraicClosure F)ˣ)
  rw [div_pow, ← smul_pow']
  symm
  apply cocycleValue_coe_eq_of_root 59 F a g
      (kummerRoot3481 F a ^ 59)
  · rw [← pow_mul]
    norm_num [pow_two]
    exact kummerRoot3481_pow F a
  · intro theta
    change g.toMulEquiv.restrictRootsOfUnity 59 theta = theta
    exact congrArg Additive.toMul
      (absoluteGalois_smul_root_eq 59 F zeta hzeta g
        (Additive.ofMul theta))

/-- The actual compatible `C_(59²)` coordinate reduces pointwise to the
genuine oriented Kummer character. -/
theorem reduction59_compatibleKummerCoordinate3481
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (a : Fˣ) (g : AbsoluteGalois F) :
    reduction59 (compatibleKummerCoordinate3481 F zeta hzeta a g) =
      orientedKummerCharacter F zeta hzeta a g := by
  apply Multiplicative.toAdd.injective
  change
    ZMod.castHom (by norm_num : 59 ∣ 59 ^ 2) (ZMod 59)
        (coordinateAddEquiv3481 F zeta hzeta
          (Additive.ofMul (compatibleCocycleValue3481 F a g))) =
      coordinateContinuousLinearEquiv 59 F zeta hzeta
        (Fermat.Conservation.ContinuousKummerH1.continuousCocycle 59 F a g)
  rw [← coordinateAddEquiv_pow59Root F zeta hzeta
    (compatibleCocycleValue3481 F a g)]
  rw [pow59_compatibleCocycleValue3481_eq_continuousCocycle
    F zeta hzeta a g]
  rfl

/-! ## The cyclotomic action in compatible coordinates -/

/-- Regard a 59-th root of unity as a `59²`-th root of unity. -/
def includeRoot59MulHom :
    KummerRoots 59 F →* KummerRoots (59 ^ 2) F :=
  Subgroup.inclusion (rootsOfUnity_le_of_dvd (by norm_num : 59 ∣ 59 ^ 2))

/-- Regard a 59-th root of unity as a `59²`-th root of unity. -/
def includeRoot59 (theta : KummerRoots 59 F) :
    KummerRoots (59 ^ 2) F :=
  includeRoot59MulHom F theta

theorem includeRoot59_coe (theta : KummerRoots 59 F) :
    (includeRoot59 F theta : (AlgebraicClosure F)ˣ) = theta :=
  Subgroup.coe_inclusion
    (rootsOfUnity_le_of_dvd (by norm_num : 59 ∣ 59 ^ 2)) theta

/-- Inclusion of `mu_59` into `mu_(59²)` as an additive homomorphism. -/
def includeRoot59AddHom :
    Additive (KummerRoots 59 F) →+ Additive (KummerRoots (59 ^ 2) F) :=
  (includeRoot59MulHom F).toAdditive

/-- Inclusion transported to the compatible cyclic coordinates. -/
def inclusionCoordinateHom
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) :
    ZMod 59 →+ ZMod (59 ^ 2) :=
  (coordinateAddEquiv3481 F zeta hzeta).toAddMonoidHom.comp
    ((includeRoot59AddHom F).comp
      (coordinateAddEquiv 59 F zeta hzeta).symm.toAddMonoidHom)

/-- Multiplication by 59, regarded as the canonical additive inclusion
`ZMod 59 → ZMod (59²)`. -/
def times59Hom : ZMod 59 →+ ZMod (59 ^ 2) :=
  ZMod.lift 59 ⟨
    (AddMonoidHom.mulLeft (59 : ZMod (59 ^ 2))).comp
      (Int.castAddHom (ZMod (59 ^ 2))),
    by
      change (59 : ZMod (59 ^ 2)) * (59 : ZMod (59 ^ 2)) = 0
      decide⟩

@[simp]
theorem times59Hom_intCast (i : ℤ) :
    times59Hom (i : ZMod 59) =
      (59 : ZMod (59 ^ 2)) * (i : ZMod (59 ^ 2)) := by
  rw [times59Hom, ZMod.lift_coe]
  rfl

/-- The oriented `mu_59` coordinate generator is the embedded primitive
root. -/
theorem coordinateAddEquiv59_symm_one_coe
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) :
    (((coordinateAddEquiv 59 F zeta hzeta).symm 1).toMul :
        (AlgebraicClosure F)ˣ) =
      algebraicPrimitiveUnit 59 F zeta hzeta := by
  simpa using coordinateAddEquiv59_symm_natCast_coe F zeta hzeta 1

/-- The compatible `mu_(59²)` coordinate 59 is the 59-th power of its
primitive generator. -/
theorem coordinateAddEquiv3481_symm_59_coe
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) :
    (((coordinateAddEquiv3481 F zeta hzeta).symm
      (59 : ZMod (59 ^ 2))).toMul : (AlgebraicClosure F)ˣ) =
      cyclotomicRoot3481 F zeta hzeta ^ 59 := by
  simpa using coordinateAddEquiv3481_symm_natCast_coe F zeta hzeta 59

/-- Unit-level generator compatibility.  Keeping this equality outside the
subtype extensionality step gives the kernel a small opaque boundary. -/
theorem coordinateGenerator_unit_eq
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) :
    (((coordinateAddEquiv 59 F zeta hzeta).symm 1).toMul :
        (AlgebraicClosure F)ˣ) =
      (((coordinateAddEquiv3481 F zeta hzeta).symm
        (59 : ZMod (59 ^ 2))).toMul : (AlgebraicClosure F)ˣ) := by
  rw [coordinateAddEquiv59_symm_one_coe F zeta hzeta]
  rw [coordinateAddEquiv3481_symm_59_coe F zeta hzeta]
  exact (cyclotomicRoot3481_pow59 F zeta hzeta).symm

/-- Multiplicative root-level generator compatibility for the inclusion. -/
theorem includeRoot59_coordinateGenerator_mul
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) :
    includeRoot59 F
        ((coordinateAddEquiv 59 F zeta hzeta).symm 1).toMul =
      ((coordinateAddEquiv3481 F zeta hzeta).symm
        (59 : ZMod (59 ^ 2))).toMul := by
  apply Subtype.ext
  rw [includeRoot59_coe F]
  exact coordinateGenerator_unit_eq F zeta hzeta

/-- Additive root-level generator compatibility for the inclusion. -/
theorem includeRoot59_coordinateGenerator
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) :
    Additive.ofMul
        (includeRoot59 F
          ((coordinateAddEquiv 59 F zeta hzeta).symm 1).toMul) =
      (coordinateAddEquiv3481 F zeta hzeta).symm
        (59 : ZMod (59 ^ 2)) :=
  congrArg Additive.ofMul
    (includeRoot59_coordinateGenerator_mul F zeta hzeta)

/-- The coordinate inclusion sends the primitive generator to 59. -/
theorem inclusionCoordinateHom_one
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) :
    inclusionCoordinateHom F zeta hzeta 1 = (59 : ZMod (59 ^ 2)) := by
  change coordinateAddEquiv3481 F zeta hzeta
      (Additive.ofMul
        (includeRoot59 F
          ((coordinateAddEquiv 59 F zeta hzeta).symm 1).toMul)) = 59
  rw [includeRoot59_coordinateGenerator F zeta hzeta]
  exact (coordinateAddEquiv3481 F zeta hzeta).apply_symm_apply _

/-- In compatible coordinates, inclusion is the canonical multiplication by
59 homomorphism. -/
theorem inclusionCoordinateHom_eq_times59
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) :
    inclusionCoordinateHom F zeta hzeta = times59Hom := by
  ext x
  obtain ⟨i, rfl⟩ := ZMod.intCast_surjective x
  rw [show (i : ZMod 59) = i • (1 : ZMod 59) by simp]
  rw [map_zsmul, map_zsmul, inclusionCoordinateHom_one F zeta hzeta]
  have ht : times59Hom (1 : ZMod 59) = (59 : ZMod (59 ^ 2)) := by
    simpa using times59Hom_intCast (1 : ℤ)
  rw [ht]

@[simp]
theorem inclusionCoordinateHom_apply_coordinate
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (theta : KummerRoots 59 F) :
    inclusionCoordinateHom F zeta hzeta
        (coordinateAddEquiv 59 F zeta hzeta (Additive.ofMul theta)) =
      coordinateAddEquiv3481 F zeta hzeta
        (Additive.ofMul (includeRoot59 F theta)) := by
  change coordinateAddEquiv3481 F zeta hzeta
      (includeRoot59AddHom F
        ((coordinateAddEquiv 59 F zeta hzeta).symm
          (coordinateAddEquiv 59 F zeta hzeta
            (Additive.ofMul theta)))) = _
  rw [(coordinateAddEquiv 59 F zeta hzeta).symm_apply_apply]
  rfl

/-- Inclusion of `mu_59` is multiplication by 59 in the compatible
`ZMod (59²)` coordinate. -/
theorem coordinateAddEquiv3481_includeRoot59
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (theta : KummerRoots 59 F) :
    coordinateAddEquiv3481 F zeta hzeta
        (Additive.ofMul (includeRoot59 F theta)) =
      ((59 * (coordinateAddEquiv 59 F zeta hzeta
        (Additive.ofMul theta)).val : ℕ) : ZMod (59 ^ 2)) := by
  rw [← inclusionCoordinateHom_apply_coordinate F zeta hzeta theta]
  rw [inclusionCoordinateHom_eq_times59 F zeta hzeta]
  let e := coordinateAddEquiv 59 F zeta hzeta (Additive.ofMul theta)
  change times59Hom e = ((59 * e.val : ℕ) : ZMod (59 ^ 2))
  calc
    times59Hom e = times59Hom (e.val : ZMod 59) := by
      rw [ZMod.natCast_zmod_val]
    _ = (59 : ZMod (59 ^ 2)) * (e.val : ZMod (59 ^ 2)) := by
      rw [show (e.val : ZMod 59) = ((e.val : ℤ) : ZMod 59) by norm_num]
      rw [times59Hom_intCast]
      norm_num
    _ = ((59 * e.val : ℕ) : ZMod (59 ^ 2)) := by norm_num

/-! ## Cyclotomic action and the twisted cocycle law -/

/-- The action ratio of the compatible cyclotomic root, as a 59-th root of
unity. -/
def cyclotomicActionRoot59
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (g : AbsoluteGalois F) : KummerRoots 59 F :=
  ⟨g • cyclotomicRoot3481 F zeta hzeta /
      cyclotomicRoot3481 F zeta hzeta, by
    rw [mem_rootsOfUnity, div_pow, ← smul_pow',
      cyclotomicRoot3481_pow59]
    have hfix :
        g • algebraicPrimitiveUnit 59 F zeta hzeta =
          algebraicPrimitiveUnit 59 F zeta hzeta := by
      apply Units.ext
      exact g.commutes ((primitiveUnit 59 F zeta hzeta : F))
    rw [hfix]
    simp⟩

@[simp]
theorem cyclotomicActionRoot59_coe
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (g : AbsoluteGalois F) :
    (cyclotomicActionRoot59 F zeta hzeta g :
      (AlgebraicClosure F)ˣ) =
      g • cyclotomicRoot3481 F zeta hzeta /
        cyclotomicRoot3481 F zeta hzeta :=
  rfl

/-- The compatible cyclotomic action ratio is exactly the public oriented
Kummer character of the primitive root. -/
theorem coordinate_cyclotomicActionRoot59
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (g : AbsoluteGalois F) :
    coordinateAddEquiv 59 F zeta hzeta
        (Additive.ofMul (cyclotomicActionRoot59 F zeta hzeta g)) =
      orientedKummerValue F zeta hzeta
        (primitiveUnit 59 F zeta hzeta) g := by
  change coordinateAddEquiv 59 F zeta hzeta
      (Additive.ofMul (cyclotomicActionRoot59 F zeta hzeta g)) =
    coordinateAddEquiv 59 F zeta hzeta
      (Fermat.Conservation.ContinuousKummerH1.continuousCocycle 59 F
        (primitiveUnit 59 F zeta hzeta) g)
  congr 1

/-- The chosen compatible Kummer ratio obeys the genuine crossed-cocycle
law before coordinates are applied. -/
theorem compatibleCocycleValue3481_mul
    (a : Fˣ) (g h : AbsoluteGalois F) :
    compatibleCocycleValue3481 F a (g * h) =
      g • compatibleCocycleValue3481 F a h *
        compatibleCocycleValue3481 F a g := by
  apply Subtype.ext
  change
    (g * h) • kummerRoot3481 F a / kummerRoot3481 F a =
      g • (h • kummerRoot3481 F a / kummerRoot3481 F a) *
        (g • kummerRoot3481 F a / kummerRoot3481 F a)
  rw [mul_smul, smul_div']
  simp only [div_eq_mul_inv]
  group

/-- Recover a compatible root of unity from the natural representative of
its coordinate. -/
theorem root3481_eq_cyclotomicRoot_pow_coordinateVal
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (theta : KummerRoots (59 ^ 2) F) :
    (theta : (AlgebraicClosure F)ˣ) =
      cyclotomicRoot3481 F zeta hzeta ^
        (coordinateAddEquiv3481 F zeta hzeta
          (Additive.ofMul theta)).val := by
  let e := coordinateAddEquiv3481 F zeta hzeta (Additive.ofMul theta)
  have htheta := congrArg
    (fun x : Additive (KummerRoots (59 ^ 2) F) ↦
      (x.toMul : (AlgebraicClosure F)ˣ))
    ((coordinateAddEquiv3481 F zeta hzeta).symm_apply_apply
      (Additive.ofMul theta))
  change (((coordinateAddEquiv3481 F zeta hzeta).symm e).toMul :
      (AlgebraicClosure F)ˣ) = theta at htheta
  have he : (e.val : ZMod (59 ^ 2)) = e := ZMod.natCast_zmod_val e
  rw [← he] at htheta
  rw [coordinateAddEquiv3481_symm_natCast_coe F zeta hzeta e.val]
    at htheta
  exact htheta.symm

/-- Galois action on a compatible root is multiplication by the appropriate
power of the cyclotomic action ratio. -/
theorem smul_root3481_unit
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (g : AbsoluteGalois F) (theta : KummerRoots (59 ^ 2) F) :
    g • (theta : (AlgebraicClosure F)ˣ) =
      (cyclotomicActionRoot59 F zeta hzeta g :
          (AlgebraicClosure F)ˣ) ^
          (coordinateAddEquiv3481 F zeta hzeta
            (Additive.ofMul theta)).val *
        (theta : (AlgebraicClosure F)ˣ) := by
  rw [root3481_eq_cyclotomicRoot_pow_coordinateVal F zeta hzeta theta]
  rw [smul_pow']
  rw [cyclotomicActionRoot59_coe, div_pow]
  simp only [div_eq_mul_inv]
  group

/-- The same action formula inside the `mu_(59²)` subgroup. -/
theorem smul_root3481
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (g : AbsoluteGalois F) (theta : KummerRoots (59 ^ 2) F) :
    g • theta =
      includeRoot59 F
          (cyclotomicActionRoot59 F zeta hzeta g ^
            (coordinateAddEquiv3481 F zeta hzeta
              (Additive.ofMul theta)).val) *
        theta := by
  apply Subtype.ext
  change g • (theta : (AlgebraicClosure F)ˣ) =
    (includeRoot59 F
      (cyclotomicActionRoot59 F zeta hzeta g ^
        (coordinateAddEquiv3481 F zeta hzeta
          (Additive.ofMul theta)).val) : (AlgebraicClosure F)ˣ) * theta
  rw [includeRoot59_coe]
  exact smul_root3481_unit F zeta hzeta g theta

/-- In compatible coordinates the Galois action separates into the original
coordinate and the included cyclotomic correction. -/
theorem coordinateAddEquiv3481_smul
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (g : AbsoluteGalois F) (theta : KummerRoots (59 ^ 2) F) :
    coordinateAddEquiv3481 F zeta hzeta (Additive.ofMul (g • theta)) =
      coordinateAddEquiv3481 F zeta hzeta
          (Additive.ofMul
            (includeRoot59 F
              (cyclotomicActionRoot59 F zeta hzeta g ^
                (coordinateAddEquiv3481 F zeta hzeta
                  (Additive.ofMul theta)).val))) +
        coordinateAddEquiv3481 F zeta hzeta (Additive.ofMul theta) := by
  rw [smul_root3481 F zeta hzeta g theta]
  exact map_add (coordinateAddEquiv3481 F zeta hzeta) _ _

/-- The 59-coordinate of the cyclotomic correction power is the product of
the cyclotomic coordinate and the reduced compatible coordinate. -/
theorem coordinate_cyclotomicActionRoot59_pow
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (g : AbsoluteGalois F) (theta : KummerRoots (59 ^ 2) F) :
    coordinateAddEquiv 59 F zeta hzeta
        (Additive.ofMul
          (cyclotomicActionRoot59 F zeta hzeta g ^
            (coordinateAddEquiv3481 F zeta hzeta
              (Additive.ofMul theta)).val)) =
      coordinateAddEquiv 59 F zeta hzeta
          (Additive.ofMul (cyclotomicActionRoot59 F zeta hzeta g)) *
        ZMod.castHom (by norm_num : 59 ∣ 59 ^ 2) (ZMod 59)
          (coordinateAddEquiv3481 F zeta hzeta
            (Additive.ofMul theta)) := by
  let e := coordinateAddEquiv3481 F zeta hzeta (Additive.ofMul theta)
  let r := coordinateAddEquiv 59 F zeta hzeta
    (Additive.ofMul (cyclotomicActionRoot59 F zeta hzeta g))
  have hcast :
      ZMod.castHom (by norm_num : 59 ∣ 59 ^ 2) (ZMod 59) e =
        (e.val : ZMod 59) := by
    calc
      ZMod.castHom (by norm_num : 59 ∣ 59 ^ 2) (ZMod 59) e =
          ZMod.castHom (by norm_num : 59 ∣ 59 ^ 2) (ZMod 59)
            (e.val : ZMod (59 ^ 2)) := by
              congr 1
              exact (ZMod.natCast_zmod_val e).symm
      _ = (e.val : ZMod 59) := by norm_num
  change coordinateAddEquiv 59 F zeta hzeta
      (e.val • Additive.ofMul
        (cyclotomicActionRoot59 F zeta hzeta g)) = r * _
  rw [map_nsmul, hcast]
  rw [nsmul_eq_mul]
  exact mul_comm _ _

/-- For the actual compatible Kummer cocycle, the correction power has
coordinate `eta(g) * chi(h)`. -/
theorem coordinate_cyclotomicPower_compatibleCocycle
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (a : Fˣ) (g h : AbsoluteGalois F) :
    coordinateAddEquiv 59 F zeta hzeta
        (Additive.ofMul
          (cyclotomicActionRoot59 F zeta hzeta g ^
            (coordinateAddEquiv3481 F zeta hzeta
              (Additive.ofMul
                (compatibleCocycleValue3481 F a h))).val)) =
      (orientedKummerCharacter F zeta hzeta
          (primitiveUnit 59 F zeta hzeta) g).toAdd *
        (orientedKummerCharacter F zeta hzeta a h).toAdd := by
  rw [coordinate_cyclotomicActionRoot59_pow F zeta hzeta]
  rw [coordinate_cyclotomicActionRoot59 F zeta hzeta g]
  have hred := congrArg Multiplicative.toAdd
    (reduction59_compatibleKummerCoordinate3481 F zeta hzeta a h)
  change
    ZMod.castHom (by norm_num : 59 ∣ 59 ^ 2) (ZMod 59)
        (coordinateAddEquiv3481 F zeta hzeta
          (Additive.ofMul (compatibleCocycleValue3481 F a h))) =
      (orientedKummerCharacter F zeta hzeta a h).toAdd at hred
  rw [hred]
  rfl

/-- The included correction power is exactly the root-coordinate image of
the concrete `kernelEmbed59` correction. -/
theorem coordinate_included_cyclotomicPower
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (a : Fˣ) (g h : AbsoluteGalois F) :
    coordinateAddEquiv3481 F zeta hzeta
        (Additive.ofMul
          (includeRoot59 F
            (cyclotomicActionRoot59 F zeta hzeta g ^
              (coordinateAddEquiv3481 F zeta hzeta
                (Additive.ofMul
                  (compatibleCocycleValue3481 F a h))).val))) =
      (kernelEmbed59 (Multiplicative.ofAdd
        ((orientedKummerCharacter F zeta hzeta
            (primitiveUnit 59 F zeta hzeta) g).toAdd *
          (orientedKummerCharacter F zeta hzeta a h).toAdd))).toAdd := by
  rw [coordinateAddEquiv3481_includeRoot59 F zeta hzeta]
  rw [coordinate_cyclotomicPower_compatibleCocycle F zeta hzeta a g h]
  rfl

/-- Galois action on the actual compatible cocycle contributes precisely
the cyclotomic Kummer correction expected by the second-digit bridge. -/
theorem coordinate_smul_compatibleCocycle
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (a : Fˣ) (g h : AbsoluteGalois F) :
    coordinateAddEquiv3481 F zeta hzeta
        (Additive.ofMul (g • compatibleCocycleValue3481 F a h)) =
      coordinateAddEquiv3481 F zeta hzeta
          (Additive.ofMul (compatibleCocycleValue3481 F a h)) +
        (kernelEmbed59 (Multiplicative.ofAdd
          ((orientedKummerCharacter F zeta hzeta
              (primitiveUnit 59 F zeta hzeta) g).toAdd *
            (orientedKummerCharacter F zeta hzeta a h).toAdd))).toAdd := by
  rw [coordinateAddEquiv3481_smul F zeta hzeta g
    (compatibleCocycleValue3481 F a h)]
  rw [coordinate_included_cyclotomicPower F zeta hzeta a g h]
  ac_rfl

/-- The actual compatible Kummer coordinate satisfies the exact twisted
multiplication law required by the concrete second-digit bridge. -/
theorem compatibleKummerCoordinate3481_twisted
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (a : Fˣ) (g h : AbsoluteGalois F) :
    compatibleKummerCoordinate3481 F zeta hzeta a (g * h) =
      compatibleKummerCoordinate3481 F zeta hzeta a g *
        compatibleKummerCoordinate3481 F zeta hzeta a h *
          kernelEmbed59 (Multiplicative.ofAdd
            ((orientedKummerCharacter F zeta hzeta
                (primitiveUnit 59 F zeta hzeta) g).toAdd *
              (orientedKummerCharacter F zeta hzeta a h).toAdd)) := by
  apply Multiplicative.toAdd.injective
  change coordinateAddEquiv3481 F zeta hzeta
      (Additive.ofMul (compatibleCocycleValue3481 F a (g * h))) =
    (coordinateAddEquiv3481 F zeta hzeta
        (Additive.ofMul (compatibleCocycleValue3481 F a g)) +
      coordinateAddEquiv3481 F zeta hzeta
        (Additive.ofMul (compatibleCocycleValue3481 F a h))) +
      (kernelEmbed59 (Multiplicative.ofAdd
        ((orientedKummerCharacter F zeta hzeta
            (primitiveUnit 59 F zeta hzeta) g).toAdd *
          (orientedKummerCharacter F zeta hzeta a h).toAdd))).toAdd
  rw [compatibleCocycleValue3481_mul F a g h]
  rw [show Additive.ofMul
      (g • compatibleCocycleValue3481 F a h *
        compatibleCocycleValue3481 F a g) =
      Additive.ofMul (g • compatibleCocycleValue3481 F a h) +
        Additive.ofMul (compatibleCocycleValue3481 F a g) by rfl]
  rw [map_add]
  rw [coordinate_smul_compatibleCocycle F zeta hzeta a g h]
  ac_rfl

/-! ## Unconditional actual-cohomology bridge -/

variable [CharZero F]

/- The actual compatible root construction discharges both visible inputs
of the twisted-lift bridge.  Thus this proof definition has, by inference,
the unconditional genuine oriented Kummer-cup equality as its exact type.
Keeping the already-checked bridge type inferred avoids elaborating that
large cohomology expression twice. -/
def pulledCarry_actualH2_eq_orientedKummerCup
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) (a : Fˣ) :=
  Fermat.Conservation.IntegratedTwistedKummerCup59.pulledCarry_actualH2_eq_orientedKummerCup_of_twistedLift
      F zeta hzeta a
      (compatibleKummerCoordinate3481 F zeta hzeta a)
      (reduction59_compatibleKummerCoordinate3481 F zeta hzeta a)
      (compatibleKummerCoordinate3481_twisted F zeta hzeta a)

end Fermat.Conservation.CompatibleKummerLift59
