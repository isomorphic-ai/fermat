/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The prime-parametric compatible Kummer lift

This module constructs the actual continuous `C_(p²)` coordinate of a
chosen `p²`-th Kummer root.  Its reduction is the genuine oriented Kummer
character, and its Galois multiplication law has exactly the cyclotomic
twist required by the concrete second-digit bridge.

Consequently the bridge's two explicit producer inputs are discharged from
root data, giving the actual `H²` equality between the pulled carry class and
the genuine oriented Kummer cup without a per-prime certificate or an added
assumption.
-/
import Fermat.Experiments.Conservation.PrimeKummerCharacterComparison
import Fermat.Experiments.Conservation.PrimeContinuousCarryLift
import Fermat.Experiments.Conservation.PrimeIntegratedTwistedKummerCup

noncomputable section

namespace Fermat.Conservation.PrimeCompatibleKummerLift

open CategoryTheory ContinuousCohomology
open Fermat.Conservation.LocalKummerH1
open Fermat.Conservation.KummerOrientation
open Fermat.Conservation.ContinuousKummerOrientation
open Fermat.Conservation.ContinuousKummerH1
open Fermat.Conservation.ContinuousKummerTateCupRaw
open Fermat.Conservation.ContinuousKummerTateCup.Nominal
open Fermat.Conservation.ContinuousKummerTateAlgebra
open Fermat.Conservation.PrimeContinuousCarryLift
open Fermat.Conservation.PrimeKummerCharacterComparison
open Fermat.Conservation.PrimeCyclicExtension

open scoped LocalKummerH1.KummerRootsDiscrete Pointwise

attribute [local instance]
  PrimeCyclicExtension.instTopologicalSpaceCyclicGroup
  PrimeCyclicExtension.instDiscreteTopologyCyclicGroup
  PrimeCyclicExtension.instTopologicalSpaceCyclicGroupSquared
  PrimeCyclicExtension.instDiscreteTopologyCyclicGroupSquared

variable {p : ℕ} [Fact p.Prime]
local instance : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
local instance : NeZero (p ^ 2) :=
  ⟨pow_ne_zero 2 (Fact.out : Nat.Prime p).ne_zero⟩

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

/-- A chosen p-th root of the embedded primitive p-th root. -/
def cyclotomicRootSquared
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) :
    (AlgebraicClosure F)ˣ :=
  (exists_rootUnit_of_baseUnit F p
    (primitiveUnit p F zeta hzeta)).choose

@[simp]
theorem cyclotomicRootSquared_pow
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) :
    cyclotomicRootSquared F zeta hzeta ^ p =
      algebraicPrimitiveUnit p F zeta hzeta :=
  (exists_rootUnit_of_baseUnit F p
    (primitiveUnit p F zeta hzeta)).choose_spec

/-- The compatible cyclotomic root has exact order `p²`. -/
theorem cyclotomicRootSquared_isPrimitive
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) :
    IsPrimitiveRoot (cyclotomicRootSquared F zeta hzeta) (p ^ 2) := by
  let xi := cyclotomicRootSquared F zeta hzeta
  let zetaA := algebraicPrimitiveUnit p F zeta hzeta
  have hpow : xi ^ p = zetaA := cyclotomicRootSquared_pow F zeta hzeta
  have hzetaA : IsPrimitiveRoot zetaA p :=
    algebraicPrimitiveUnit_isPrimitive p F zeta hzeta
  refine ⟨?_, ?_⟩
  · rw [show p ^ 2 = p * p by simp [pow_two], pow_mul, hpow]
    exact hzetaA.pow_eq_one
  · intro l hl
    have hzpow : zetaA ^ l = 1 := by
      calc
        zetaA ^ l = (xi ^ p) ^ l := by rw [hpow]
        _ = xi ^ (p * l) := by rw [pow_mul]
        _ = xi ^ (l * p) := by rw [Nat.mul_comm]
        _ = (xi ^ l) ^ p := by rw [pow_mul]
        _ = 1 := by rw [hl, one_pow]
    obtain ⟨k, rfl⟩ := hzetaA.dvd_of_pow_eq_one l hzpow
    have hxpow : xi ^ (p * k) = 1 := hl
    have hkpow : zetaA ^ k = 1 := by
      rw [← hpow, ← pow_mul]
      exact hxpow
    obtain ⟨m, rfl⟩ := hzetaA.dvd_of_pow_eq_one k hkpow
    use m
    ring

/-- A chosen compatible `p²`-th root of a base-field unit. -/
def kummerRootSquared (a : Fˣ) : (AlgebraicClosure F)ˣ :=
  (exists_rootUnit_of_baseUnit F (p ^ 2) a).choose

@[simp]
theorem kummerRootSquared_pow (a : Fˣ) :
    kummerRootSquared (p := p) F a ^ (p ^ 2) =
      Units.map (algebraMap F (AlgebraicClosure F)).toMonoidHom a :=
  (exists_rootUnit_of_baseUnit F (p ^ 2) a).choose_spec

/-- The compatible root's Kummer ratio as a `p²`-th root of unity. -/
def compatibleCocycleValueSquared
    (a : Fˣ) (g : AbsoluteGalois F) : KummerRoots (p ^ 2) F :=
  ⟨g • kummerRootSquared (p := p) F a / kummerRootSquared (p := p) F a, by
    rw [mem_rootsOfUnity, div_pow, ← smul_pow', kummerRootSquared_pow]
    have hfix :
        g • Units.map (algebraMap F (AlgebraicClosure F)).toMonoidHom a =
          Units.map (algebraMap F (AlgebraicClosure F)).toMonoidHom a := by
      apply Units.ext
      exact g.commutes (a : F)
    rw [hfix]
    simp⟩

@[simp]
theorem compatibleCocycleValueSquared_coe
    (a : Fˣ) (g : AbsoluteGalois F) :
    (compatibleCocycleValueSquared (p := p) F a g : (AlgebraicClosure F)ˣ) =
      g • kummerRootSquared (p := p) F a / kummerRootSquared (p := p) F a :=
  rfl

/-- The compatible chosen-root cocycle is continuous for the Krull topology
and the discrete topology on roots of unity. -/
theorem continuous_compatibleCocycleValueSquared (a : Fˣ) :
    Continuous (compatibleCocycleValueSquared (p := p) F a) := by
  rw [continuous_discrete_rng]
  intro theta
  by_cases hfiber : ∃ tau, compatibleCocycleValueSquared (p := p) F a tau = theta
  · obtain ⟨tau, htau⟩ := hfiber
    let r : (AlgebraicClosure F)ˣ := kummerRootSquared (p := p) F a
    have hopen :
        IsOpen (MulAction.stabilizer (AbsoluteGalois F)
          (r : AlgebraicClosure F) : Set (AbsoluteGalois F)) := by
      convert stabilizer_isOpen_of_isIntegral
        (K := F) (L := AlgebraicClosure F) r using 1
    have hfiber_eq :
        compatibleCocycleValueSquared (p := p) F a ⁻¹' {theta} =
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
  · have hfiber_eq : compatibleCocycleValueSquared (p := p) F a ⁻¹' {theta} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro sigma hsigma
      apply hfiber
      exact ⟨sigma, by simpa using hsigma⟩
    rw [hfiber_eq]
    exact isOpen_empty

/-! ## Compatible primitive-root coordinates -/

/-- All `p²`-th roots of unity identified with powers of the chosen root
whose p-th power is the supplied base-field primitive root. -/
def rootsEquivZPowersSquared
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) :
    KummerRoots (p ^ 2) F ≃*
      Subgroup.zpowers (cyclotomicRootSquared F zeta hzeta) :=
  MulEquiv.subgroupCongr
    (cyclotomicRootSquared_isPrimitive F zeta hzeta).zpowers_eq.symm

/-- Additive coordinates on `mu_(p²)`, compatible with the supplied
orientation on `mu_p`. -/
def coordinateAddEquivSquared
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) :
    Additive (KummerRoots (p ^ 2) F) ≃+ ZMod (p ^ 2) :=
  (MulEquiv.toAdditive (rootsEquivZPowersSquared F zeta hzeta)).trans
    (cyclotomicRootSquared_isPrimitive F zeta hzeta).zmodEquivZPowers.symm

/-- The coordinate of the compatible chosen-root Kummer cocycle. -/
def compatibleKummerCoordinateSquaredValue
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) (a : Fˣ) :
    C(AbsoluteGalois F, ZMod (p ^ 2)) where
  toFun g := coordinateAddEquivSquared F zeta hzeta
    (Additive.ofMul (compatibleCocycleValueSquared (p := p) F a g))
  continuous_toFun := by
    have hcoordinate : Continuous
        (fun theta : Additive (KummerRoots (p ^ 2) F) ↦
          coordinateAddEquivSquared F zeta hzeta theta) :=
      continuous_of_discreteTopology
    exact hcoordinate.comp (continuous_compatibleCocycleValueSquared (p := p) F a)

/-- The actual continuous `C_(p²)` cochain to be fed to the second-digit
bridge. -/
def compatibleKummerCoordinateSquared
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) (a : Fˣ) :
    C(AbsoluteGalois F, CyclicGroupSquared p) where
  toFun g := Multiplicative.ofAdd
    (compatibleKummerCoordinateSquaredValue F zeta hzeta a g)
  continuous_toFun :=
    (compatibleKummerCoordinateSquaredValue F zeta hzeta a).continuous

@[simp]
theorem coordinateAddEquivSquared_symm_intCast_coe
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) (i : ℤ) :
    (((coordinateAddEquivSquared F zeta hzeta).symm
          (i : ZMod (p ^ 2))).toMul : (AlgebraicClosure F)ˣ) =
      cyclotomicRootSquared F zeta hzeta ^ i := by
  change
    (((rootsEquivZPowersSquared F zeta hzeta).symm
      (((cyclotomicRootSquared_isPrimitive F zeta hzeta).zmodEquivZPowers
        (i : ZMod (p ^ 2))).toMul) :
        KummerRoots (p ^ 2) F) : (AlgebraicClosure F)ˣ) = _
  rw [IsPrimitiveRoot.zmodEquivZPowers_apply_coe_int]
  rfl

set_option maxHeartbeats 10000 in
@[simp]
theorem coordinateAddEquivSquared_symm_natCast_coe
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) (i : ℕ) :
    (((coordinateAddEquivSquared F zeta hzeta).symm
          (i : ZMod (p ^ 2))).toMul : (AlgebraicClosure F)ˣ) =
      cyclotomicRootSquared F zeta hzeta ^ i := by
  rw [show (i : ZMod (p ^ 2)) = ((i : ℤ) : ZMod (p ^ 2)) by
    norm_num]
  rw [coordinateAddEquivSquared_symm_intCast_coe, zpow_natCast]

@[simp]
theorem coordinateAddEquivPrime_symm_intCast_coe
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) (i : ℤ) :
    (((coordinateAddEquiv p F zeta hzeta).symm
          (i : ZMod p)).toMul : (AlgebraicClosure F)ˣ) =
      algebraicPrimitiveUnit p F zeta hzeta ^ i := by
  change
    (((rootsEquivZPowers p F zeta hzeta).symm
      (((algebraicPrimitiveUnit_isPrimitive p F zeta hzeta).zmodEquivZPowers
        (i : ZMod p)).toMul) : KummerRoots p F) :
        (AlgebraicClosure F)ˣ) = _
  rw [IsPrimitiveRoot.zmodEquivZPowers_apply_coe_int]
  rfl

@[simp]
theorem coordinateAddEquivPrime_symm_natCast_coe
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) (i : ℕ) :
    (((coordinateAddEquiv p F zeta hzeta).symm
          (i : ZMod p)).toMul : (AlgebraicClosure F)ˣ) =
      algebraicPrimitiveUnit p F zeta hzeta ^ i := by
  rw [show (i : ZMod p) = ((i : ℤ) : ZMod p) by norm_num]
  rw [coordinateAddEquivPrime_symm_intCast_coe, zpow_natCast]

/-- Raising a `p²`-th root of unity to the p-th power lands in
`mu_p`. -/
def powPRoot
    (theta : KummerRoots (p ^ 2) F) : KummerRoots p F :=
  ⟨(theta : (AlgebraicClosure F)ˣ) ^ p, by
    rw [mem_rootsOfUnity, ← pow_mul]
    simpa [pow_two] using theta.prop⟩

omit [Fact (Nat.Prime p)] in
@[simp]
theorem powPRoot_coe (theta : KummerRoots (p ^ 2) F) :
    (powPRoot F theta : (AlgebraicClosure F)ˣ) =
      (theta : (AlgebraicClosure F)ˣ) ^ p :=
  rfl

/-- The compatible coordinates commute with p-th powering and reduction
from `ZMod (p²)` to `ZMod p`. -/
theorem coordinateAddEquiv_powPRoot
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (theta : KummerRoots (p ^ 2) F) :
    coordinateAddEquiv p F zeta hzeta
        (Additive.ofMul (powPRoot F theta)) =
      ZMod.castHom (PrimeCyclicExtension.p_dvd_p_sq p) (ZMod p)
        (coordinateAddEquivSquared F zeta hzeta (Additive.ofMul theta)) := by
  obtain ⟨i, hi⟩ := ZMod.intCast_surjective
    (coordinateAddEquivSquared F zeta hzeta (Additive.ofMul theta))
  apply (coordinateAddEquiv p F zeta hzeta).symm.injective
  rw [AddEquiv.symm_apply_apply]
  rw [← hi, map_intCast]
  apply Additive.toMul.injective
  apply Subtype.ext
  change (theta : (AlgebraicClosure F)ˣ) ^ p =
    (((coordinateAddEquiv p F zeta hzeta).symm
      (i : ZMod p)).toMul : (AlgebraicClosure F)ˣ)
  rw [coordinateAddEquivPrime_symm_intCast_coe]
  have htheta := congrArg
    (fun x : Additive (KummerRoots (p ^ 2) F) ↦
      (x.toMul : (AlgebraicClosure F)ˣ))
    ((coordinateAddEquivSquared F zeta hzeta).symm_apply_apply
      (Additive.ofMul theta))
  rw [← hi, coordinateAddEquivSquared_symm_intCast_coe] at htheta
  have htheta' : (theta : (AlgebraicClosure F)ˣ) =
      cyclotomicRootSquared F zeta hzeta ^ i := by
    simpa using htheta.symm
  rw [htheta', ← zpow_natCast, ← zpow_mul]
  rw [mul_comm, zpow_mul]
  rw [zpow_natCast, cyclotomicRootSquared_pow]

/-! ## Reduction to the genuine oriented Kummer character -/

/-- The p-th power of the compatible `mu_(p²)` cocycle is the public
chosen-root `mu_p` Kummer cocycle.  Root-choice independence is valid here
because the chosen primitive root lies in the base field. -/
theorem powP_compatibleCocycleValueSquared_eq_continuousCocycle
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (a : Fˣ) (g : AbsoluteGalois F) :
    Additive.ofMul
        (powPRoot F (compatibleCocycleValueSquared (p := p) F a g)) =
      Fermat.Conservation.ContinuousKummerH1.continuousCocycle p F a g := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change
    (g • kummerRootSquared (p := p) F a / kummerRootSquared (p := p) F a) ^ p =
      (cocycleValue p F a g : (AlgebraicClosure F)ˣ)
  rw [div_pow, ← smul_pow']
  symm
  apply cocycleValue_coe_eq_of_root p F a g
      (kummerRootSquared (p := p) F a ^ p)
  · rw [← pow_mul]
    simpa [pow_two] using kummerRootSquared_pow (p := p) F a
  · intro theta
    change g.toMulEquiv.restrictRootsOfUnity p theta = theta
    exact congrArg Additive.toMul
      (absoluteGalois_smul_root_eq p F zeta hzeta g
        (Additive.ofMul theta))

/-- The actual compatible `C_(p²)` coordinate reduces pointwise to the
genuine oriented Kummer character. -/
theorem reduction_compatibleKummerCoordinateSquared
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (a : Fˣ) (g : AbsoluteGalois F) :
    reduction p (compatibleKummerCoordinateSquared F zeta hzeta a g) =
      orientedKummerCharacter p F zeta hzeta a g := by
  apply Multiplicative.toAdd.injective
  change
    ZMod.castHom (PrimeCyclicExtension.p_dvd_p_sq p) (ZMod p)
        (coordinateAddEquivSquared F zeta hzeta
          (Additive.ofMul (compatibleCocycleValueSquared (p := p) F a g))) =
      coordinateContinuousLinearEquiv p F zeta hzeta
        (Fermat.Conservation.ContinuousKummerH1.continuousCocycle p F a g)
  rw [← coordinateAddEquiv_powPRoot F zeta hzeta
    (compatibleCocycleValueSquared (p := p) F a g)]
  rw [powP_compatibleCocycleValueSquared_eq_continuousCocycle
    F zeta hzeta a g]
  rfl

/-! ## The cyclotomic action in compatible coordinates -/

/-- Regard a p-th root of unity as a `p²`-th root of unity. -/
def includeRootMulHom :
    KummerRoots p F →* KummerRoots (p ^ 2) F :=
  Subgroup.inclusion (rootsOfUnity_le_of_dvd (PrimeCyclicExtension.p_dvd_p_sq p))

/-- Regard a p-th root of unity as a `p²`-th root of unity. -/
def includeRoot (theta : KummerRoots p F) :
    KummerRoots (p ^ 2) F :=
  includeRootMulHom F theta

omit [Fact (Nat.Prime p)] in
theorem includeRoot_coe (theta : KummerRoots p F) :
    (includeRoot F theta : (AlgebraicClosure F)ˣ) = theta :=
  Subgroup.coe_inclusion
    (rootsOfUnity_le_of_dvd (PrimeCyclicExtension.p_dvd_p_sq p)) theta

/-- Inclusion of `mu_p` into `mu_(p²)` as an additive homomorphism. -/
def includeRootAddHom :
    Additive (KummerRoots p F) →+ Additive (KummerRoots (p ^ 2) F) :=
  (includeRootMulHom F).toAdditive

/-- Inclusion transported to the compatible cyclic coordinates. -/
def inclusionCoordinateHom
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) :
    ZMod p →+ ZMod (p ^ 2) :=
  (coordinateAddEquivSquared F zeta hzeta).toAddMonoidHom.comp
    ((includeRootAddHom F).comp
      (coordinateAddEquiv p F zeta hzeta).symm.toAddMonoidHom)

/-- Multiplication by p, regarded as the canonical additive inclusion
`ZMod p → ZMod (p²)`. -/
def timesPHom : ZMod p →+ ZMod (p ^ 2) :=
  ZMod.lift p ⟨
    (AddMonoidHom.mulLeft (p : ZMod (p ^ 2))).comp
      (Int.castAddHom (ZMod (p ^ 2))),
    by
      simp only [AddMonoidHom.comp_apply, Int.coe_castAddHom,
        AddMonoidHom.mulLeft]
      change (p : ZMod (p ^ 2)) * ((p : ℤ) : ZMod (p ^ 2)) = 0
      rw [show ((p : ℤ) : ZMod (p ^ 2)) = (p : ZMod (p ^ 2)) by
        norm_num]
      rw [← Nat.cast_mul, ← pow_two, ZMod.natCast_self]⟩

@[simp]
theorem timesPHom_intCast (i : ℤ) :
    timesPHom (i : ZMod p) =
      (p : ZMod (p ^ 2)) * (i : ZMod (p ^ 2)) := by
  rw [timesPHom, ZMod.lift_coe]
  rfl

/-- The oriented `mu_p` coordinate generator is the embedded primitive
root. -/
theorem coordinateAddEquivPrime_symm_one_coe
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) :
    (((coordinateAddEquiv p F zeta hzeta).symm 1).toMul :
        (AlgebraicClosure F)ˣ) =
      algebraicPrimitiveUnit p F zeta hzeta := by
  simpa using coordinateAddEquivPrime_symm_natCast_coe F zeta hzeta 1

/-- The compatible `mu_(p²)` coordinate p is the p-th power of its
primitive generator. -/
theorem coordinateAddEquivSquared_symm_p_coe
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) :
    (((coordinateAddEquivSquared F zeta hzeta).symm
      (p : ZMod (p ^ 2))).toMul : (AlgebraicClosure F)ˣ) =
      cyclotomicRootSquared F zeta hzeta ^ p := by
  exact coordinateAddEquivSquared_symm_natCast_coe F zeta hzeta p

/-- Unit-level generator compatibility.  Keeping this equality outside the
subtype extensionality step gives the kernel a small opaque boundary. -/
theorem coordinateGenerator_unit_eq
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) :
    (((coordinateAddEquiv p F zeta hzeta).symm 1).toMul :
        (AlgebraicClosure F)ˣ) =
      (((coordinateAddEquivSquared F zeta hzeta).symm
        (p : ZMod (p ^ 2))).toMul : (AlgebraicClosure F)ˣ) := by
  rw [coordinateAddEquivPrime_symm_one_coe F zeta hzeta]
  rw [coordinateAddEquivSquared_symm_p_coe F zeta hzeta]
  exact (cyclotomicRootSquared_pow F zeta hzeta).symm

/-- Multiplicative root-level generator compatibility for the inclusion. -/
theorem includeRoot_coordinateGenerator_mul
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) :
    includeRoot F
        ((coordinateAddEquiv p F zeta hzeta).symm 1).toMul =
      ((coordinateAddEquivSquared F zeta hzeta).symm
        (p : ZMod (p ^ 2))).toMul := by
  apply Subtype.ext
  rw [includeRoot_coe F]
  exact coordinateGenerator_unit_eq F zeta hzeta

/-- Additive root-level generator compatibility for the inclusion. -/
theorem includeRoot_coordinateGenerator
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) :
    Additive.ofMul
        (includeRoot F
          ((coordinateAddEquiv p F zeta hzeta).symm 1).toMul) =
      (coordinateAddEquivSquared F zeta hzeta).symm
        (p : ZMod (p ^ 2)) :=
  congrArg Additive.ofMul
    (includeRoot_coordinateGenerator_mul F zeta hzeta)

/-- The coordinate inclusion sends the primitive generator to p. -/
theorem inclusionCoordinateHom_one
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) :
    inclusionCoordinateHom F zeta hzeta 1 = (p : ZMod (p ^ 2)) := by
  change coordinateAddEquivSquared F zeta hzeta
      (Additive.ofMul
        (includeRoot F
          ((coordinateAddEquiv p F zeta hzeta).symm 1).toMul)) = p
  rw [includeRoot_coordinateGenerator F zeta hzeta]
  exact (coordinateAddEquivSquared F zeta hzeta).apply_symm_apply _

/-- In compatible coordinates, inclusion is the canonical multiplication by
p homomorphism. -/
theorem inclusionCoordinateHom_eq_timesP
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) :
    inclusionCoordinateHom F zeta hzeta = timesPHom := by
  ext x
  obtain ⟨i, rfl⟩ := ZMod.intCast_surjective x
  rw [show (i : ZMod p) = i • (1 : ZMod p) by simp]
  rw [map_zsmul, map_zsmul, inclusionCoordinateHom_one F zeta hzeta]
  have ht : timesPHom (1 : ZMod p) = (p : ZMod (p ^ 2)) := by
    simpa using timesPHom_intCast (1 : ℤ)
  rw [ht]

@[simp]
theorem inclusionCoordinateHom_apply_coordinate
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (theta : KummerRoots p F) :
    inclusionCoordinateHom F zeta hzeta
        (coordinateAddEquiv p F zeta hzeta (Additive.ofMul theta)) =
      coordinateAddEquivSquared F zeta hzeta
        (Additive.ofMul (includeRoot F theta)) := by
  change coordinateAddEquivSquared F zeta hzeta
      (includeRootAddHom F
        ((coordinateAddEquiv p F zeta hzeta).symm
          (coordinateAddEquiv p F zeta hzeta
            (Additive.ofMul theta)))) = _
  rw [(coordinateAddEquiv p F zeta hzeta).symm_apply_apply]
  rfl

/-- Inclusion of `mu_p` is multiplication by p in the compatible
`ZMod (p²)` coordinate. -/
theorem coordinateAddEquivSquared_includeRoot
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (theta : KummerRoots p F) :
    coordinateAddEquivSquared F zeta hzeta
        (Additive.ofMul (includeRoot F theta)) =
      ((p * (coordinateAddEquiv p F zeta hzeta
        (Additive.ofMul theta)).val : ℕ) : ZMod (p ^ 2)) := by
  rw [← inclusionCoordinateHom_apply_coordinate F zeta hzeta theta]
  rw [inclusionCoordinateHom_eq_timesP F zeta hzeta]
  let e := coordinateAddEquiv p F zeta hzeta (Additive.ofMul theta)
  change timesPHom e = ((p * e.val : ℕ) : ZMod (p ^ 2))
  calc
    timesPHom e = timesPHom (e.val : ZMod p) := by
      rw [ZMod.natCast_zmod_val]
    _ = (p : ZMod (p ^ 2)) * (e.val : ZMod (p ^ 2)) := by
      rw [show (e.val : ZMod p) = ((e.val : ℤ) : ZMod p) by norm_num]
      rw [timesPHom_intCast]
      norm_num
    _ = ((p * e.val : ℕ) : ZMod (p ^ 2)) := by norm_num

/-! ## Cyclotomic action and the twisted cocycle law -/

/-- The action ratio of the compatible cyclotomic root, as a p-th root of
unity. -/
def cyclotomicActionRoot
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (g : AbsoluteGalois F) : KummerRoots p F :=
  ⟨g • cyclotomicRootSquared F zeta hzeta /
      cyclotomicRootSquared F zeta hzeta, by
    rw [mem_rootsOfUnity, div_pow, ← smul_pow',
      cyclotomicRootSquared_pow]
    have hfix :
        g • algebraicPrimitiveUnit p F zeta hzeta =
          algebraicPrimitiveUnit p F zeta hzeta := by
      apply Units.ext
      exact g.commutes ((primitiveUnit p F zeta hzeta : F))
    rw [hfix]
    simp⟩

@[simp]
theorem cyclotomicActionRoot_coe
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (g : AbsoluteGalois F) :
    (cyclotomicActionRoot F zeta hzeta g :
      (AlgebraicClosure F)ˣ) =
      g • cyclotomicRootSquared F zeta hzeta /
        cyclotomicRootSquared F zeta hzeta :=
  rfl

/-- The compatible cyclotomic action ratio is exactly the public oriented
Kummer character of the primitive root. -/
theorem coordinate_cyclotomicActionRoot
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (g : AbsoluteGalois F) :
    coordinateAddEquiv p F zeta hzeta
        (Additive.ofMul (cyclotomicActionRoot F zeta hzeta g)) =
      orientedKummerValue p F zeta hzeta
        (primitiveUnit p F zeta hzeta) g := by
  change coordinateAddEquiv p F zeta hzeta
      (Additive.ofMul (cyclotomicActionRoot F zeta hzeta g)) =
    coordinateAddEquiv p F zeta hzeta
      (Fermat.Conservation.ContinuousKummerH1.continuousCocycle p F
        (primitiveUnit p F zeta hzeta) g)
  congr 1

/-- The chosen compatible Kummer ratio obeys the genuine crossed-cocycle
law before coordinates are applied. -/
theorem compatibleCocycleValueSquared_mul
    (a : Fˣ) (g h : AbsoluteGalois F) :
    compatibleCocycleValueSquared (p := p) F a (g * h) =
      g • compatibleCocycleValueSquared (p := p) F a h *
        compatibleCocycleValueSquared (p := p) F a g := by
  apply Subtype.ext
  change
    (g * h) • kummerRootSquared (p := p) F a / kummerRootSquared (p := p) F a =
      g • (h • kummerRootSquared (p := p) F a / kummerRootSquared (p := p) F a) *
        (g • kummerRootSquared (p := p) F a / kummerRootSquared (p := p) F a)
  rw [mul_smul, smul_div']
  simp only [div_eq_mul_inv]
  group

/-- Recover a compatible root of unity from the natural representative of
its coordinate. -/
theorem rootSquared_eq_cyclotomicRoot_pow_coordinateVal
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (theta : KummerRoots (p ^ 2) F) :
    (theta : (AlgebraicClosure F)ˣ) =
      cyclotomicRootSquared F zeta hzeta ^
        (coordinateAddEquivSquared F zeta hzeta
          (Additive.ofMul theta)).val := by
  let e := coordinateAddEquivSquared F zeta hzeta (Additive.ofMul theta)
  have htheta := congrArg
    (fun x : Additive (KummerRoots (p ^ 2) F) ↦
      (x.toMul : (AlgebraicClosure F)ˣ))
    ((coordinateAddEquivSquared F zeta hzeta).symm_apply_apply
      (Additive.ofMul theta))
  change (((coordinateAddEquivSquared F zeta hzeta).symm e).toMul :
      (AlgebraicClosure F)ˣ) = theta at htheta
  have he : (e.val : ZMod (p ^ 2)) = e := ZMod.natCast_zmod_val e
  rw [← he] at htheta
  rw [coordinateAddEquivSquared_symm_natCast_coe F zeta hzeta e.val]
    at htheta
  exact htheta.symm

/-- Galois action on a compatible root is multiplication by the appropriate
power of the cyclotomic action ratio. -/
theorem smul_rootSquared_unit
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (g : AbsoluteGalois F) (theta : KummerRoots (p ^ 2) F) :
    g • (theta : (AlgebraicClosure F)ˣ) =
      (cyclotomicActionRoot F zeta hzeta g :
          (AlgebraicClosure F)ˣ) ^
          (coordinateAddEquivSquared F zeta hzeta
            (Additive.ofMul theta)).val *
        (theta : (AlgebraicClosure F)ˣ) := by
  rw [rootSquared_eq_cyclotomicRoot_pow_coordinateVal F zeta hzeta theta]
  rw [smul_pow']
  rw [cyclotomicActionRoot_coe, div_pow]
  simp only [div_eq_mul_inv]
  group

/-- The same action formula inside the `mu_(p²)` subgroup. -/
theorem smul_rootSquared
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (g : AbsoluteGalois F) (theta : KummerRoots (p ^ 2) F) :
    g • theta =
      includeRoot F
          (cyclotomicActionRoot F zeta hzeta g ^
            (coordinateAddEquivSquared F zeta hzeta
              (Additive.ofMul theta)).val) *
        theta := by
  apply Subtype.ext
  change g • (theta : (AlgebraicClosure F)ˣ) =
    (includeRoot F
      (cyclotomicActionRoot F zeta hzeta g ^
        (coordinateAddEquivSquared F zeta hzeta
          (Additive.ofMul theta)).val) : (AlgebraicClosure F)ˣ) * theta
  rw [includeRoot_coe]
  exact smul_rootSquared_unit F zeta hzeta g theta

/-- In compatible coordinates the Galois action separates into the original
coordinate and the included cyclotomic correction. -/
theorem coordinateAddEquivSquared_smul
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (g : AbsoluteGalois F) (theta : KummerRoots (p ^ 2) F) :
    coordinateAddEquivSquared F zeta hzeta (Additive.ofMul (g • theta)) =
      coordinateAddEquivSquared F zeta hzeta
          (Additive.ofMul
            (includeRoot F
              (cyclotomicActionRoot F zeta hzeta g ^
                (coordinateAddEquivSquared F zeta hzeta
                  (Additive.ofMul theta)).val))) +
        coordinateAddEquivSquared F zeta hzeta (Additive.ofMul theta) := by
  rw [smul_rootSquared F zeta hzeta g theta]
  exact map_add (coordinateAddEquivSquared F zeta hzeta) _ _

/-- The p-coordinate of the cyclotomic correction power is the product of
the cyclotomic coordinate and the reduced compatible coordinate. -/
theorem coordinate_cyclotomicActionRoot_pow
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (g : AbsoluteGalois F) (theta : KummerRoots (p ^ 2) F) :
    coordinateAddEquiv p F zeta hzeta
        (Additive.ofMul
          (cyclotomicActionRoot F zeta hzeta g ^
            (coordinateAddEquivSquared F zeta hzeta
              (Additive.ofMul theta)).val)) =
      coordinateAddEquiv p F zeta hzeta
          (Additive.ofMul (cyclotomicActionRoot F zeta hzeta g)) *
        ZMod.castHom (PrimeCyclicExtension.p_dvd_p_sq p) (ZMod p)
          (coordinateAddEquivSquared F zeta hzeta
            (Additive.ofMul theta)) := by
  let e := coordinateAddEquivSquared F zeta hzeta (Additive.ofMul theta)
  let r := coordinateAddEquiv p F zeta hzeta
    (Additive.ofMul (cyclotomicActionRoot F zeta hzeta g))
  have hcast :
      ZMod.castHom (PrimeCyclicExtension.p_dvd_p_sq p) (ZMod p) e =
        (e.val : ZMod p) := by
    calc
      ZMod.castHom (PrimeCyclicExtension.p_dvd_p_sq p) (ZMod p) e =
          ZMod.castHom (PrimeCyclicExtension.p_dvd_p_sq p) (ZMod p)
            (e.val : ZMod (p ^ 2)) := by
              congr 1
              exact (ZMod.natCast_zmod_val e).symm
      _ = (e.val : ZMod p) := by norm_num
  change coordinateAddEquiv p F zeta hzeta
      (e.val • Additive.ofMul
        (cyclotomicActionRoot F zeta hzeta g)) = r * _
  rw [map_nsmul, hcast]
  rw [nsmul_eq_mul]
  exact mul_comm _ _

/-- For the actual compatible Kummer cocycle, the correction power has
coordinate `eta(g) * chi(h)`. -/
theorem coordinate_cyclotomicPower_compatibleCocycle
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (a : Fˣ) (g h : AbsoluteGalois F) :
    coordinateAddEquiv p F zeta hzeta
        (Additive.ofMul
          (cyclotomicActionRoot F zeta hzeta g ^
            (coordinateAddEquivSquared F zeta hzeta
              (Additive.ofMul
                (compatibleCocycleValueSquared (p := p) F a h))).val)) =
      (orientedKummerCharacter p F zeta hzeta
          (primitiveUnit p F zeta hzeta) g).toAdd *
        (orientedKummerCharacter p F zeta hzeta a h).toAdd := by
  rw [coordinate_cyclotomicActionRoot_pow F zeta hzeta]
  rw [coordinate_cyclotomicActionRoot F zeta hzeta g]
  have hred := congrArg Multiplicative.toAdd
    (reduction_compatibleKummerCoordinateSquared F zeta hzeta a h)
  change
    ZMod.castHom (PrimeCyclicExtension.p_dvd_p_sq p) (ZMod p)
        (coordinateAddEquivSquared F zeta hzeta
          (Additive.ofMul (compatibleCocycleValueSquared (p := p) F a h))) =
      (orientedKummerCharacter p F zeta hzeta a h).toAdd at hred
  rw [hred]
  rfl

/-- The included correction power is exactly the root-coordinate image of
the concrete `kernelEmbed p` correction. -/
theorem coordinate_included_cyclotomicPower
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (a : Fˣ) (g h : AbsoluteGalois F) :
    coordinateAddEquivSquared F zeta hzeta
        (Additive.ofMul
          (includeRoot F
            (cyclotomicActionRoot F zeta hzeta g ^
              (coordinateAddEquivSquared F zeta hzeta
                (Additive.ofMul
                  (compatibleCocycleValueSquared (p := p) F a h))).val))) =
      (kernelEmbed p (Multiplicative.ofAdd
        ((orientedKummerCharacter p F zeta hzeta
            (primitiveUnit p F zeta hzeta) g).toAdd *
          (orientedKummerCharacter p F zeta hzeta a h).toAdd))).toAdd := by
  rw [coordinateAddEquivSquared_includeRoot F zeta hzeta]
  rw [coordinate_cyclotomicPower_compatibleCocycle F zeta hzeta a g h]
  rfl

/-- Galois action on the actual compatible cocycle contributes precisely
the cyclotomic Kummer correction expected by the second-digit bridge. -/
theorem coordinate_smul_compatibleCocycle
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (a : Fˣ) (g h : AbsoluteGalois F) :
    coordinateAddEquivSquared F zeta hzeta
        (Additive.ofMul (g • compatibleCocycleValueSquared (p := p) F a h)) =
      coordinateAddEquivSquared F zeta hzeta
          (Additive.ofMul (compatibleCocycleValueSquared (p := p) F a h)) +
        (kernelEmbed p (Multiplicative.ofAdd
          ((orientedKummerCharacter p F zeta hzeta
              (primitiveUnit p F zeta hzeta) g).toAdd *
            (orientedKummerCharacter p F zeta hzeta a h).toAdd))).toAdd := by
  rw [coordinateAddEquivSquared_smul F zeta hzeta g
    (compatibleCocycleValueSquared (p := p) F a h)]
  rw [coordinate_included_cyclotomicPower F zeta hzeta a g h]
  ac_rfl

/-- The actual compatible Kummer coordinate satisfies the exact twisted
multiplication law required by the concrete second-digit bridge. -/
theorem compatibleKummerCoordinateSquared_twisted
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (a : Fˣ) (g h : AbsoluteGalois F) :
    compatibleKummerCoordinateSquared F zeta hzeta a (g * h) =
      compatibleKummerCoordinateSquared F zeta hzeta a g *
        compatibleKummerCoordinateSquared F zeta hzeta a h *
          kernelEmbed p (Multiplicative.ofAdd
            ((orientedKummerCharacter p F zeta hzeta
                (primitiveUnit p F zeta hzeta) g).toAdd *
              (orientedKummerCharacter p F zeta hzeta a h).toAdd)) := by
  apply Multiplicative.toAdd.injective
  change coordinateAddEquivSquared F zeta hzeta
      (Additive.ofMul (compatibleCocycleValueSquared (p := p) F a (g * h))) =
    (coordinateAddEquivSquared F zeta hzeta
        (Additive.ofMul (compatibleCocycleValueSquared (p := p) F a g)) +
      coordinateAddEquivSquared F zeta hzeta
        (Additive.ofMul (compatibleCocycleValueSquared (p := p) F a h))) +
      (kernelEmbed p (Multiplicative.ofAdd
        ((orientedKummerCharacter p F zeta hzeta
            (primitiveUnit p F zeta hzeta) g).toAdd *
          (orientedKummerCharacter p F zeta hzeta a h).toAdd))).toAdd
  rw [compatibleCocycleValueSquared_mul (p := p) F a g h]
  rw [show Additive.ofMul
      (g • compatibleCocycleValueSquared (p := p) F a h *
        compatibleCocycleValueSquared (p := p) F a g) =
      Additive.ofMul (g • compatibleCocycleValueSquared (p := p) F a h) +
        Additive.ofMul (compatibleCocycleValueSquared (p := p) F a g) by rfl]
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
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p) (a : Fˣ) :=
  Fermat.Conservation.PrimeIntegratedTwistedKummerCup.pulledCarry_actualH2_eq_orientedKummerCup_of_twistedLift
      F zeta hzeta a
      (compatibleKummerCoordinateSquared F zeta hzeta a)
      (reduction_compatibleKummerCoordinateSquared F zeta hzeta a)
      (compatibleKummerCoordinateSquared_twisted F zeta hzeta a)

end Fermat.Conservation.PrimeCompatibleKummerLift
