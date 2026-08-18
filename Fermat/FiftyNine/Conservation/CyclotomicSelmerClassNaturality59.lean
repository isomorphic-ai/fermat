/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Cyclotomic naturality of the strict 59-Selmer class map

The cyclotomic ring automorphisms transport nonzero fractional ideals and
preserve principal ideals.  They therefore induce an honest action on the
ideal class group.  This file proves that Mathlib's strict Selmer class map
intertwines that action with the already constructed action on the Kummer
quotient.

The proof works for every strict Selmer class.  It chooses only the
canonical fractional-ideal root supplied by the Dedekind factorization
equivalence; no class representative or arithmetic premise is added.
-/
import Fermat.FiftyNine.Conservation.FermatFactorSelmerSource59
import Mathlib.RepresentationTheory.Intertwining

open scoped MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Fermat.FiftyNine.Conservation.CyclotomicSelmerClassNaturality59

open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.IdealPowerSelmer
open Fermat.Conservation.InvolutiveBase
open Fermat.Conservation.SelmerEigenspace
open CanonicalIrregularMode827
open CyclotomicSelmerAction59
open DetectorWitness827
open FermatFactorSelmerSource59
open SplitPrimeFourier827
open StateFactorPair
open VostokovLocalization59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

/-! ## The actual class-group action -/

/-- Transport of fractional ideals along the cyclotomic automorphism of the
ring of integers, using the corresponding induced fraction-field map. -/
noncomputable def cyclotomicFractionalIdealEquiv59
    (sigma : GaloisIndex59) :
    FractionalIdeal (NumberField.RingOfIntegers K)⁰ K ≃+*
      FractionalIdeal (NumberField.RingOfIntegers K)⁰ K :=
  FractionalIdeal.ringEquivOfRingEquiv K K
    (KummerCriterion.cyclotomicRingOfIntegersEquiv
      (p := 59) K sigma)

/-- The induced equivalence on nonzero fractional ideals.  Keeping this as
an opaque, fully typed declaration prevents quotient construction from
repeatedly unfolding the underlying fraction-field equivalence. -/
noncomputable def cyclotomicFractionalIdealUnitMulEquiv59
    (sigma : GaloisIndex59) :
    (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ ≃*
      (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ :=
  Units.mapEquiv (cyclotomicFractionalIdealEquiv59 K sigma).toMulEquiv

/-- The induced class-group equivalence.  It is constructed directly by
mapping nonzero fractional ideals and descending through the subgroup of
principal ideals. -/
noncomputable def cyclotomicClassGroupMulEquiv59
    (sigma : GaloisIndex59) :
    ClassGroup (NumberField.RingOfIntegers K) ≃*
      ClassGroup (NumberField.RingOfIntegers K) :=
  ClassGroup.mulEquiv
    (KummerCriterion.cyclotomicRingOfIntegersEquiv
      (p := 59) K sigma)

/-- The same fractional-ideal action in Mathlib's canonical fraction-field
model of the class group. -/
private noncomputable def cyclotomicCanonicalFractionalIdealUnitMulEquiv59
    (sigma : GaloisIndex59) :
    (FractionalIdeal (NumberField.RingOfIntegers K)⁰
        (FractionRing (NumberField.RingOfIntegers K)))ˣ ≃*
      (FractionalIdeal (NumberField.RingOfIntegers K)⁰
        (FractionRing (NumberField.RingOfIntegers K)))ˣ :=
  Units.mapEquiv
    (FractionalIdeal.ringEquivOfRingEquiv
      (FractionRing (NumberField.RingOfIntegers K))
      (FractionRing (NumberField.RingOfIntegers K))
      (KummerCriterion.cyclotomicRingOfIntegersEquiv
        (p := 59) K sigma)).toMulEquiv

/-- Mathlib's canonical equivalence of fractional ideals is the transport
induced by the identity equivalence of the base ring. -/
private theorem canonicalEquiv_eq_ringEquivOfRingEquiv_refl59 :
    FractionalIdeal.canonicalEquiv
        (NumberField.RingOfIntegers K)⁰ K
        (FractionRing (NumberField.RingOfIntegers K)) =
      FractionalIdeal.ringEquivOfRingEquiv K
        (FractionRing (NumberField.RingOfIntegers K))
        (RingEquiv.refl (NumberField.RingOfIntegers K)) := by
  rw [FractionalIdeal.canonicalEquiv]
  rfl

/-- Canonical change of fraction-field model commutes with cyclotomic
transport of fractional ideals. -/
private theorem canonicalEquiv_cyclotomic_commute59
    (sigma : GaloisIndex59)
    (I : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ) :
    Units.mapEquiv
        (FractionalIdeal.canonicalEquiv
          (NumberField.RingOfIntegers K)⁰ K
          (FractionRing (NumberField.RingOfIntegers K))).toMulEquiv
        (cyclotomicFractionalIdealUnitMulEquiv59 K sigma I) =
      cyclotomicCanonicalFractionalIdealUnitMulEquiv59 K sigma
        (Units.mapEquiv
          (FractionalIdeal.canonicalEquiv
            (NumberField.RingOfIntegers K)⁰ K
            (FractionRing (NumberField.RingOfIntegers K))).toMulEquiv I) := by
  apply Units.ext
  simp only [Units.coe_mapEquiv]
  rw [canonicalEquiv_eq_ringEquivOfRingEquiv_refl59 K]
  change FractionalIdeal.ringEquivOfRingEquiv K
        (FractionRing (NumberField.RingOfIntegers K))
        (RingEquiv.refl (NumberField.RingOfIntegers K))
        (FractionalIdeal.ringEquivOfRingEquiv K K
          (KummerCriterion.cyclotomicRingOfIntegersEquiv
            (p := 59) K sigma) I) =
      FractionalIdeal.ringEquivOfRingEquiv
        (FractionRing (NumberField.RingOfIntegers K))
        (FractionRing (NumberField.RingOfIntegers K))
        (KummerCriterion.cyclotomicRingOfIntegersEquiv
          (p := 59) K sigma)
        (FractionalIdeal.ringEquivOfRingEquiv K
          (FractionRing (NumberField.RingOfIntegers K))
          (RingEquiv.refl (NumberField.RingOfIntegers K)) I)
  rw [← FractionalIdeal.ringEquivOfRingEquiv_trans_apply K K
      (FractionRing (NumberField.RingOfIntegers K)),
    ← FractionalIdeal.ringEquivOfRingEquiv_trans_apply K
      (FractionRing (NumberField.RingOfIntegers K))
      (FractionRing (NumberField.RingOfIntegers K))]
  rfl

/-- Computation of the class action on a fractional ideal already expressed
in Mathlib's canonical fraction-field model. -/
private theorem cyclotomicClassGroupMulEquiv59_mk_fractionRing
    (sigma : GaloisIndex59)
    (I : (FractionalIdeal (NumberField.RingOfIntegers K)⁰
      (FractionRing (NumberField.RingOfIntegers K)))ˣ) :
    cyclotomicClassGroupMulEquiv59 K sigma
        (ClassGroup.mk (FractionRing (NumberField.RingOfIntegers K)) I) =
      ClassGroup.mk (FractionRing (NumberField.RingOfIntegers K))
        (cyclotomicCanonicalFractionalIdealUnitMulEquiv59 K sigma I) := by
  apply (ClassGroup.equiv
    (FractionRing (NumberField.RingOfIntegers K))).injective
  simp only [cyclotomicClassGroupMulEquiv59, ClassGroup.mulEquiv_apply,
    ClassGroup.equiv_mk, QuotientGroup.congr_mk',
    MulEquiv.apply_symm_apply, FractionalIdeal.canonicalEquiv_self,
    RingEquiv.coe_mulEquiv_refl]
  rfl

/-- Computation of the class action on a represented fractional ideal. -/
theorem cyclotomicClassGroupMulEquiv59_mk
    (sigma : GaloisIndex59)
    (I : (FractionalIdeal
      (NumberField.RingOfIntegers K)⁰ K)ˣ) :
    cyclotomicClassGroupMulEquiv59 K sigma (ClassGroup.mk K I) =
      ClassGroup.mk K
        (cyclotomicFractionalIdealUnitMulEquiv59 K sigma I) := by
  let F := FractionRing (NumberField.RingOfIntegers K)
  let C := FractionalIdeal.canonicalEquiv
    (NumberField.RingOfIntegers K)⁰ K F
  calc
    cyclotomicClassGroupMulEquiv59 K sigma (ClassGroup.mk K I) =
        cyclotomicClassGroupMulEquiv59 K sigma
          (ClassGroup.mk F (Units.mapEquiv C.toMulEquiv I)) :=
      congrArg (cyclotomicClassGroupMulEquiv59 K sigma)
        (ClassGroup.mk_canonicalEquiv
          (R := NumberField.RingOfIntegers K) (K := K) F I).symm
    _ = ClassGroup.mk F
          (cyclotomicCanonicalFractionalIdealUnitMulEquiv59 K sigma
            (Units.mapEquiv C.toMulEquiv I)) :=
      cyclotomicClassGroupMulEquiv59_mk_fractionRing K sigma _
    _ = ClassGroup.mk F
          (Units.mapEquiv C.toMulEquiv
            (cyclotomicFractionalIdealUnitMulEquiv59 K sigma I)) :=
      congrArg (ClassGroup.mk F)
        (canonicalEquiv_cyclotomic_commute59 K sigma I).symm
    _ = ClassGroup.mk K
          (cyclotomicFractionalIdealUnitMulEquiv59 K sigma I) :=
      ClassGroup.mk_canonicalEquiv
        (R := NumberField.RingOfIntegers K) (K := K) F _

/-- The class action at the identity is the identity. -/
@[simp]
theorem cyclotomicClassGroupMulEquiv59_one_apply
    (c : ClassGroup (NumberField.RingOfIntegers K)) :
    cyclotomicClassGroupMulEquiv59 K 1 c = c := by
  have he :
      KummerCriterion.cyclotomicRingOfIntegersEquiv
          (p := 59) K 1 =
        RingEquiv.refl (NumberField.RingOfIntegers K) := by
    ext x
    exact congrArg Subtype.val
      (KummerCriterion.cyclotomicRingOfIntegersEquiv_one_apply
        (p := 59) (K := K) x)
  rw [cyclotomicClassGroupMulEquiv59, he]
  apply (ClassGroup.equiv (FractionRing
    (NumberField.RingOfIntegers K))).injective
  simp only [ClassGroup.mulEquiv, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply]
  induction (ClassGroup.equiv (FractionRing
    (NumberField.RingOfIntegers K)) c) using QuotientGroup.induction_on with
  | _ I =>
      change QuotientGroup.mk' _
          (Units.mapEquiv
            (FractionalIdeal.ringEquivOfRingEquiv
              (FractionRing (NumberField.RingOfIntegers K))
              (FractionRing (NumberField.RingOfIntegers K))
              (RingEquiv.refl (NumberField.RingOfIntegers K))).toMulEquiv I) =
        QuotientGroup.mk' _ I
      rw [FractionalIdeal.ringEquivOfRingEquiv_refl]
      congr 1

/-- Cyclotomic multiplication is composition of the induced class maps in
the same order as the field and strict Selmer actions. -/
theorem cyclotomicClassGroupMulEquiv59_mul_apply
    (sigma tau : GaloisIndex59)
    (c : ClassGroup (NumberField.RingOfIntegers K)) :
    cyclotomicClassGroupMulEquiv59 K (sigma * tau) c =
      cyclotomicClassGroupMulEquiv59 K sigma
        (cyclotomicClassGroupMulEquiv59 K tau c) := by
  have he :
      KummerCriterion.cyclotomicRingOfIntegersEquiv
          (p := 59) K (sigma * tau) =
        (KummerCriterion.cyclotomicRingOfIntegersEquiv
          (p := 59) K tau).trans
        (KummerCriterion.cyclotomicRingOfIntegersEquiv
          (p := 59) K sigma) := by
    ext x
    exact congrArg Subtype.val
      (KummerCriterion.cyclotomicRingOfIntegersEquiv_mul_apply
        (p := 59) (K := K) sigma tau x)
  rw [cyclotomicClassGroupMulEquiv59, he,
    cyclotomicClassGroupMulEquiv59, cyclotomicClassGroupMulEquiv59]
  apply (ClassGroup.equiv (FractionRing
    (NumberField.RingOfIntegers K))).injective
  simp only [ClassGroup.mulEquiv, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply]
  induction (ClassGroup.equiv (FractionRing
    (NumberField.RingOfIntegers K)) c) using QuotientGroup.induction_on with
  | _ I =>
      change QuotientGroup.mk' _
          (Units.mapEquiv
            (FractionalIdeal.ringEquivOfRingEquiv
              (FractionRing (NumberField.RingOfIntegers K))
              (FractionRing (NumberField.RingOfIntegers K))
              ((KummerCriterion.cyclotomicRingOfIntegersEquiv
                (p := 59) K tau).trans
               (KummerCriterion.cyclotomicRingOfIntegersEquiv
                (p := 59) K sigma))).toMulEquiv I) =
        QuotientGroup.mk' _
          (Units.mapEquiv
            (FractionalIdeal.ringEquivOfRingEquiv
              (FractionRing (NumberField.RingOfIntegers K))
              (FractionRing (NumberField.RingOfIntegers K))
              (KummerCriterion.cyclotomicRingOfIntegersEquiv
                (p := 59) K sigma)).toMulEquiv
            (Units.mapEquiv
              (FractionalIdeal.ringEquivOfRingEquiv
                (FractionRing (NumberField.RingOfIntegers K))
                (FractionRing (NumberField.RingOfIntegers K))
                (KummerCriterion.cyclotomicRingOfIntegersEquiv
                  (p := 59) K tau)).toMulEquiv I))
      rw [FractionalIdeal.ringEquivOfRingEquiv_trans
        (FractionRing (NumberField.RingOfIntegers K))
        (FractionRing (NumberField.RingOfIntegers K))
        (FractionRing (NumberField.RingOfIntegers K))]
      congr 1

/-- The genuine cyclotomic representation on the additive class group. -/
noncomputable def cyclotomicAdditiveClassGroupRepresentation59 :
    Representation ℤ GaloisIndex59
      (Additive (ClassGroup (NumberField.RingOfIntegers K))) where
  toFun sigma :=
    (cyclotomicClassGroupMulEquiv59 K sigma).toAdditive.toIntLinearEquiv
  map_one' := by
    apply LinearMap.ext
    intro c
    exact congrArg Additive.ofMul
      (cyclotomicClassGroupMulEquiv59_one_apply K (Additive.toMul c))
  map_mul' sigma tau := by
    apply LinearMap.ext
    intro c
    exact congrArg Additive.ofMul
      (cyclotomicClassGroupMulEquiv59_mul_apply K sigma tau
        (Additive.toMul c))

/-! ## Naturality of the strict Selmer class map -/

/-- The fraction-field automorphism induced by the cyclotomic action on the
ring of integers is the original cyclotomic field automorphism. -/
theorem cyclotomicFractionEquiv59_eq (sigma : GaloisIndex59) :
    IsFractionRing.ringEquivOfRingEquiv
        (KummerCriterion.cyclotomicRingOfIntegersEquiv
          (p := 59) K sigma) =
      (KummerCriterion.cyclotomicSigmaOfUnit
        (p := 59) K sigma).toRingEquiv := by
  apply RingEquiv.toRingHom_injective
  apply IsLocalization.ringHom_ext
    (nonZeroDivisors (NumberField.RingOfIntegers K))
  ext x
  change IsFractionRing.ringEquivOfRingEquiv
      (KummerCriterion.cyclotomicRingOfIntegersEquiv
        (p := 59) K sigma)
        (algebraMap (NumberField.RingOfIntegers K) K x) =
    KummerCriterion.cyclotomicSigmaOfUnit (p := 59) K sigma
      (algebraMap (NumberField.RingOfIntegers K) K x)
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  change ((KummerCriterion.cyclotomicSigmaOfUnit
      (p := 59) K sigma • x : NumberField.RingOfIntegers K) : K) =
    KummerCriterion.cyclotomicSigmaOfUnit
      (p := 59) K sigma • (x : K)
  exact algebraMap.coe_smul'
    (KummerCriterion.cyclotomicSigmaOfUnit
      (p := 59) K sigma) x K

/-- Transport of a principal fractional ideal is the principal fractional
ideal of the transported field unit. -/
theorem cyclotomicFractionalIdealEquiv59_toPrincipalIdeal
    (sigma : GaloisIndex59) (x : Kˣ) :
    cyclotomicFractionalIdealUnitMulEquiv59 K sigma
        (toPrincipalIdeal (NumberField.RingOfIntegers K) K x) =
      toPrincipalIdeal (NumberField.RingOfIntegers K) K
        (cyclotomicUnitEquiv59 K sigma x) := by
  apply Units.ext
  rw [cyclotomicFractionalIdealUnitMulEquiv59]
  simp only [Units.coe_mapEquiv, coe_toPrincipalIdeal]
  change FractionalIdeal.ringEquivOfRingEquiv K K
      (KummerCriterion.cyclotomicRingOfIntegersEquiv
        (p := 59) K sigma)
      (FractionalIdeal.spanSingleton
        (NumberField.RingOfIntegers K)⁰ (x : K)) = _
  rw [FractionalIdeal.ringEquivOfRingEquiv_spanSingleton]
  apply congrArg (FractionalIdeal.spanSingleton
    (nonZeroDivisors (NumberField.RingOfIntegers K)))
  exact congrArg (fun e : K ≃+* K => e (x : K))
    (cyclotomicFractionEquiv59_eq K sigma)

/-- Every strict Selmer class has a canonical nonzero fractional-ideal root
of the principal ideal of any chosen Kummer representative. -/
private theorem exists_strictSelmerRepresentativeRoot59
    (q : SelmerCarrier (NumberField.RingOfIntegers K) K 59) :
    ∃ (x : Kˣ) (I : (FractionalIdeal
        (NumberField.RingOfIntegers K)⁰ K)ˣ),
      (Additive.toMul q).1 = QuotientGroup.mk x ∧
      I ^ 59 =
        toPrincipalIdeal (NumberField.RingOfIntegers K) K x := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom 59 : Kˣ →* Kˣ).range (Additive.toMul q).1
  let f := toPrincipalIdeal (NumberField.RingOfIntegers K) K
  let geometry :=
    IsDedekindDomain.selmerGroup.fractionalIdealFactorization
      (R := NumberField.RingOfIntegers K) (K := K)
  have hdiv : x ∈ PowerRoot.divisibleElements f 59 := by
    rw [geometry.mem_divisibleElements_iff]
    intro v
    change (59 : ℤ) ∣
      (geometry (toPrincipalIdeal
        (NumberField.RingOfIntegers K) K x)).toAdd v
    rw [IsDedekindDomain.selmerGroup.fractionalIdealFactorization_apply,
      coe_toPrincipalIdeal, count_spanSingleton_eq_neg_valuation]
    apply Int.dvd_neg.mpr
    apply (valuationOfNeZeroMod_mk_eq_one_iff_dvd
      (p := 59) v x).mp
    have hy :
        (x : Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) =
          (Additive.toMul q).1 := hx
    rw [hy]
    exact (Additive.toMul q).2 v (Set.notMem_empty v)
  let divisible : PowerRoot.divisibleElements f 59 := ⟨x, hdiv⟩
  refine ⟨x, PowerRoot.root f 59 geometry divisible, hx.symm, ?_⟩
  exact PowerRoot.root_power f 59 geometry divisible

/-- The strict Selmer class map intertwines each actual cyclotomic Kummer
action with the induced action on the actual ideal class group. -/
theorem strictSelmerIdealClass59_cyclotomic
    (sigma : GaloisIndex59)
    (q : SelmerCarrier (NumberField.RingOfIntegers K) K 59) :
    strictSelmerIdealClass59 (K := K)
        (cyclotomicStrictSelmerRepresentation59 K sigma q) =
      cyclotomicAdditiveClassGroupRepresentation59 K sigma
        (strictSelmerIdealClass59 (K := K) q) := by
  obtain ⟨x, I, hx, hI⟩ := exists_strictSelmerRepresentativeRoot59 K q
  have htransport :
      cyclotomicFractionalIdealUnitMulEquiv59 K sigma I ^ 59 =
        toPrincipalIdeal (NumberField.RingOfIntegers K) K
          (cyclotomicUnitEquiv59 K sigma x) := by
    calc
      cyclotomicFractionalIdealUnitMulEquiv59 K sigma I ^ 59 =
          cyclotomicFractionalIdealUnitMulEquiv59 K sigma
            (I ^ 59) := (map_pow _ I 59).symm
      _ = cyclotomicFractionalIdealUnitMulEquiv59 K sigma
            (toPrincipalIdeal
              (NumberField.RingOfIntegers K) K x) := by rw [hI]
      _ = toPrincipalIdeal (NumberField.RingOfIntegers K) K
            (cyclotomicUnitEquiv59 K sigma x) :=
        cyclotomicFractionalIdealEquiv59_toPrincipalIdeal K sigma x
  have hqAction :
      (Additive.toMul
        (cyclotomicStrictSelmerRepresentation59 K sigma q)).1 =
        QuotientGroup.mk (cyclotomicUnitEquiv59 K sigma x) := by
    change cyclotomicKummerHom59 K sigma (Additive.toMul q).1 = _
    rw [hx]
    exact cyclotomicKummerHom59_mk K sigma x
  apply Additive.toMul.injective
  change IsDedekindDomain.selmerGroup.toClass
      (R := NumberField.RingOfIntegers K) (K := K) (n := 59)
      (Additive.toMul
        (cyclotomicStrictSelmerRepresentation59 K sigma q)) =
    cyclotomicClassGroupMulEquiv59 K sigma
      (IsDedekindDomain.selmerGroup.toClass
        (R := NumberField.RingOfIntegers K) (K := K) (n := 59)
        (Additive.toMul q))
  rw [IsDedekindDomain.selmerGroup.toClass_eq_mk_of_representative_root
      (q := Additive.toMul q) (x := x) (hx := hx)
      (I := I) (hI := hI),
    IsDedekindDomain.selmerGroup.toClass_eq_mk_of_representative_root
      (q := Additive.toMul
        (cyclotomicStrictSelmerRepresentation59 K sigma q))
      (x := cyclotomicUnitEquiv59 K sigma x) (hx := hqAction)
      (I := cyclotomicFractionalIdealUnitMulEquiv59 K sigma I)
      (hI := htransport),
    cyclotomicClassGroupMulEquiv59_mk]

/-! ## The 59-torsion representation and character projector -/

/-- The actual 59-torsion subgroup of the class group, which is exactly the
range of the strict Selmer class map. -/
abbrev ClassTorsion59 :=
  ClassPTorsion (NumberField.RingOfIntegers K) 59

local instance instClassTorsion59ModuleZMod :
    Module (ZMod 59) (ClassTorsion59 K) :=
  AddSubgroup.torsionBy.zmodModule

local instance instClassTorsion59ModulePadicInt :
    Module (PadicInt 59) (ClassTorsion59 K) :=
  Module.compHom (ClassTorsion59 K) PadicInt.toZMod

/-- Restriction of one genuine class-group automorphism to its stable
59-torsion subgroup. -/
noncomputable def cyclotomicClassTorsionAddHom59
    (sigma : GaloisIndex59) :
    ClassTorsion59 K →+ ClassTorsion59 K where
  toFun c := ⟨
    cyclotomicAdditiveClassGroupRepresentation59 K sigma c,
    by
      apply AddSubgroup.torsionBy.nsmul_iff.mpr
      have hc := AddSubgroup.torsionBy.nsmul_iff.mp c.property
      change 59 • cyclotomicAdditiveClassGroupRepresentation59 K sigma
          (c : Additive (ClassGroup
            (NumberField.RingOfIntegers K))) = 0
      calc
        59 • cyclotomicAdditiveClassGroupRepresentation59 K sigma
            (c : Additive (ClassGroup
              (NumberField.RingOfIntegers K))) =
            cyclotomicAdditiveClassGroupRepresentation59 K sigma
              (59 • (c : Additive (ClassGroup
                (NumberField.RingOfIntegers K)))) :=
          (map_nsmul
            (cyclotomicAdditiveClassGroupRepresentation59 K sigma) 59
            (c : Additive (ClassGroup
              (NumberField.RingOfIntegers K)))).symm
        _ = 0 := by rw [hc, map_zero]⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero (cyclotomicAdditiveClassGroupRepresentation59 K sigma)
  map_add' x y := by
    apply Subtype.ext
    exact map_add (cyclotomicAdditiveClassGroupRepresentation59 K sigma)
      (x : Additive (ClassGroup (NumberField.RingOfIntegers K)))
      (y : Additive (ClassGroup (NumberField.RingOfIntegers K)))

/-- The restricted action is linear over integral 59-adic coefficients,
whose action on this carrier factors through `ZMod 59`. -/
noncomputable def cyclotomicClassTorsionLinearMap59
    (sigma : GaloisIndex59) :
    ClassTorsion59 K →ₗ[PadicInt 59] ClassTorsion59 K where
  toFun := cyclotomicClassTorsionAddHom59 K sigma
  map_add' := map_add _
  map_smul' a c := by
    change cyclotomicClassTorsionAddHom59 K sigma
        (PadicInt.toZMod a • c) =
      PadicInt.toZMod a • cyclotomicClassTorsionAddHom59 K sigma c
    exact ZMod.map_smul (cyclotomicClassTorsionAddHom59 K sigma)
      (PadicInt.toZMod a) c

/-- The induced cyclotomic representation on the actual 59-torsion class
group. -/
noncomputable def cyclotomicClassTorsionRepresentation59 :
    Representation (PadicInt 59) GaloisIndex59 (ClassTorsion59 K) where
  toFun sigma := cyclotomicClassTorsionLinearMap59 K sigma
  map_one' := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact congrArg Additive.ofMul
      (cyclotomicClassGroupMulEquiv59_one_apply K
        (Additive.toMul (c : Additive
          (ClassGroup (NumberField.RingOfIntegers K)))))
  map_mul' sigma tau := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact congrArg Additive.ofMul
      (cyclotomicClassGroupMulEquiv59_mul_apply K sigma tau
        (Additive.toMul (c : Additive
          (ClassGroup (NumberField.RingOfIntegers K)))))

/-- The strict Selmer class map with its genuine 59-torsion codomain. -/
noncomputable def strictSelmerClassLinearMap59 :
    SelmerCarrier (NumberField.RingOfIntegers K) K 59 →ₗ[PadicInt 59]
      ClassTorsion59 K where
  toFun := selmerClassProjection
    (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
  map_add' := map_add _
  map_smul' a q := by
    change selmerClassProjection
        (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
        (PadicInt.toZMod a • q) =
      PadicInt.toZMod a •
        selmerClassProjection
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59) q
    exact ZMod.map_smul
      (selmerClassProjection
        (R := NumberField.RingOfIntegers K) (K := K) (p := 59))
      (PadicInt.toZMod a) q

/-- Forgetting the torsion proof recovers the previously exposed full
class-group map definitionally. -/
@[simp]
theorem strictSelmerClassLinearMap59_value
    (q : SelmerCarrier (NumberField.RingOfIntegers K) K 59) :
    (strictSelmerClassLinearMap59 K q :
      Additive (ClassGroup (NumberField.RingOfIntegers K))) =
      strictSelmerIdealClass59 (K := K) q :=
  rfl

/-- The restricted class map is an honest intertwiner of the two
cyclotomic representations. -/
noncomputable def strictSelmerClassIntertwiner59 :
    Representation.IntertwiningMap
      (cyclotomicStrictSelmerRepresentation59 K)
      (cyclotomicClassTorsionRepresentation59 K) :=
  (strictSelmerClassLinearMap59 K).intertwiningMap_of_isIntertwiningMap
    (cyclotomicStrictSelmerRepresentation59 K)
    (cyclotomicClassTorsionRepresentation59 K) <| by
      intro sigma q
      apply Subtype.ext
      exact strictSelmerIdealClass59_cyclotomic K sigma q

/-- The character-idempotent action on the genuine class-group
59-torsion. -/
noncomputable def cyclotomicClassProjector59
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (eta : Character (PadicInt 59) GaloisIndex59) :
    ClassTorsion59 K →ₗ[PadicInt 59] ClassTorsion59 K :=
  (cyclotomicClassTorsionRepresentation59 K).asAlgebraHom
    (characterIdempotent eta)

/-- Strong projector naturality: class projection after any Selmer
character projector is the same character projector applied to the actual
59-torsion ideal class. -/
theorem strictSelmerClassLinearMap59_characterProjector
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (eta : Character (PadicInt 59) GaloisIndex59)
    (q : SelmerCarrier (NumberField.RingOfIntegers K) K 59) :
    strictSelmerClassLinearMap59 K
        ((characterProjectorAt
          (cyclotomicStrictSelmerRepresentation59 K) eta q).1) =
      cyclotomicClassProjector59 K eta
        (strictSelmerClassLinearMap59 K q) := by
  change strictSelmerClassLinearMap59 K
      ((cyclotomicStrictSelmerRepresentation59 K).asAlgebraHom
        (characterIdempotent eta) q) =
    (cyclotomicClassTorsionRepresentation59 K).asAlgebraHom
      (characterIdempotent eta) (strictSelmerClassLinearMap59 K q)
  let F :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      (cyclotomicStrictSelmerRepresentation59 K)
      (cyclotomicClassTorsionRepresentation59 K))
      (strictSelmerClassIntertwiner59 K)
  exact F.map_smul (characterIdempotent eta) q

variable {K}
  {zeta : K} {hZeta : IsPrimitiveRoot zeta 59}
  {S : Fermat.FiftyNine.Conservation.FermatState.PrimitiveSecondCaseSolution}
  {hz : (59 : ℤ) ∣ S.z}

/-- The projected plus Fermat factor has exactly the chi=15 projection of
the allocated plus root class as its class-group obstruction. -/
theorem fermatPlusPrimalMode59_classProjection
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (pair : StateLinkedIdealPair hZeta S hz) :
    strictSelmerClassLinearMap59 K (fermatPlusPrimalMode59 pair).1 =
      cyclotomicClassProjector59 K irregularCharacter59
        (allocatedRootClassPTorsion pair.ledger 0) := by
  rw [fermatPlusPrimalMode59,
    strictSelmerClassLinearMap59_characterProjector]
  apply congrArg (cyclotomicClassProjector59 K irregularCharacter59)
  apply Subtype.ext
  exact fermatPlusStrictSelmer59_idealClass pair

/-- The analogous exact identification for the projected minus Fermat
factor. -/
theorem fermatMinusPrimalMode59_classProjection
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (pair : StateLinkedIdealPair hZeta S hz) :
    strictSelmerClassLinearMap59 K (fermatMinusPrimalMode59 pair).1 =
      cyclotomicClassProjector59 K irregularCharacter59
        (allocatedRootClassPTorsion pair.ledger 1) := by
  rw [fermatMinusPrimalMode59,
    strictSelmerClassLinearMap59_characterProjector]
  apply congrArg (cyclotomicClassProjector59 K irregularCharacter59)
  apply Subtype.ext
  exact fermatMinusStrictSelmer59_idealClass pair

end Fermat.FiftyNine.Conservation.CyclotomicSelmerClassNaturality59
