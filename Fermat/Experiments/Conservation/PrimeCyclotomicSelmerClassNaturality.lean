/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Cyclotomic naturality of the strict p-Selmer class map

The cyclotomic ring automorphisms transport nonzero fractional ideals and
preserve principal ideals.  They therefore induce an honest action on the
ideal class group.  This file proves that the vendored generic strict Selmer
class map, built on Mathlib's actual Selmer carrier, intertwines that action
with the already constructed action on the Kummer quotient.

The proof works for every strict Selmer class.  It chooses only the
canonical fractional-ideal root supplied by the Dedekind factorization
equivalence; no class representative or arithmetic premise is added.
-/
import Fermat.Experiments.Conservation.CommonActionSelmerCore
import Fermat.Experiments.Conservation.IdealPowerSelmer
import Fermat.Experiments.Conservation.PrimeCyclotomicSelmerAction
import Mathlib.RepresentationTheory.Intertwining

open scoped MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Fermat.Conservation.PrimeCyclotomicSelmerClassNaturality

open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.IdealPowerSelmer
open Fermat.Conservation.InvolutiveBase
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.PrimeCyclotomicSelmerAction

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]

local instance : Fact (0 < p) := ⟨(Fact.out : Nat.Prime p).pos⟩

/-! ## The actual class-group action -/

/-- Transport of fractional ideals along the cyclotomic automorphism of the
ring of integers, using the corresponding induced fraction-field map. -/
noncomputable def cyclotomicFractionalIdealEquiv
    (sigma : (KummerCriterion.CyclotomicUnitDelta p)) :
    FractionalIdeal (NumberField.RingOfIntegers K)⁰ K ≃+*
      FractionalIdeal (NumberField.RingOfIntegers K)⁰ K :=
  FractionalIdeal.ringEquivOfRingEquiv K K
    (KummerCriterion.cyclotomicRingOfIntegersEquiv
      (p := p) K sigma)

/-- The induced equivalence on nonzero fractional ideals.  Keeping this as
an opaque, fully typed declaration prevents quotient construction from
repeatedly unfolding the underlying fraction-field equivalence. -/
noncomputable def cyclotomicFractionalIdealUnitMulEquiv
    (sigma : (KummerCriterion.CyclotomicUnitDelta p)) :
    (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ ≃*
      (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ :=
  Units.mapEquiv (cyclotomicFractionalIdealEquiv p K sigma).toMulEquiv

/-- The induced class-group equivalence.  It is constructed directly by
mapping nonzero fractional ideals and descending through the subgroup of
principal ideals. -/
noncomputable def cyclotomicClassGroupMulEquiv
    (sigma : (KummerCriterion.CyclotomicUnitDelta p)) :
    ClassGroup (NumberField.RingOfIntegers K) ≃*
      ClassGroup (NumberField.RingOfIntegers K) :=
  ClassGroup.mulEquiv
    (KummerCriterion.cyclotomicRingOfIntegersEquiv
      (p := p) K sigma)

/-- The same fractional-ideal action in Mathlib's canonical fraction-field
model of the class group. -/
private noncomputable def cyclotomicCanonicalFractionalIdealUnitMulEquiv
    (sigma : (KummerCriterion.CyclotomicUnitDelta p)) :
    (FractionalIdeal (NumberField.RingOfIntegers K)⁰
        (FractionRing (NumberField.RingOfIntegers K)))ˣ ≃*
      (FractionalIdeal (NumberField.RingOfIntegers K)⁰
        (FractionRing (NumberField.RingOfIntegers K)))ˣ :=
  Units.mapEquiv
    (FractionalIdeal.ringEquivOfRingEquiv
      (FractionRing (NumberField.RingOfIntegers K))
      (FractionRing (NumberField.RingOfIntegers K))
      (KummerCriterion.cyclotomicRingOfIntegersEquiv
        (p := p) K sigma)).toMulEquiv

/-- Mathlib's canonical equivalence of fractional ideals is the transport
induced by the identity equivalence of the base ring. -/
private theorem canonicalEquiv_eq_ringEquivOfRingEquiv_refl :
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
private theorem canonicalEquiv_cyclotomic_commute
    (sigma : (KummerCriterion.CyclotomicUnitDelta p))
    (I : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ) :
    Units.mapEquiv
        (FractionalIdeal.canonicalEquiv
          (NumberField.RingOfIntegers K)⁰ K
          (FractionRing (NumberField.RingOfIntegers K))).toMulEquiv
        (cyclotomicFractionalIdealUnitMulEquiv p K sigma I) =
      cyclotomicCanonicalFractionalIdealUnitMulEquiv p K sigma
        (Units.mapEquiv
          (FractionalIdeal.canonicalEquiv
            (NumberField.RingOfIntegers K)⁰ K
            (FractionRing (NumberField.RingOfIntegers K))).toMulEquiv I) := by
  apply Units.ext
  simp only [Units.coe_mapEquiv]
  rw [canonicalEquiv_eq_ringEquivOfRingEquiv_refl K]
  change FractionalIdeal.ringEquivOfRingEquiv K
        (FractionRing (NumberField.RingOfIntegers K))
        (RingEquiv.refl (NumberField.RingOfIntegers K))
        (FractionalIdeal.ringEquivOfRingEquiv K K
          (KummerCriterion.cyclotomicRingOfIntegersEquiv
            (p := p) K sigma) I) =
      FractionalIdeal.ringEquivOfRingEquiv
        (FractionRing (NumberField.RingOfIntegers K))
        (FractionRing (NumberField.RingOfIntegers K))
        (KummerCriterion.cyclotomicRingOfIntegersEquiv
          (p := p) K sigma)
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
private theorem cyclotomicClassGroupMulEquiv_mk_fractionRing
    (sigma : (KummerCriterion.CyclotomicUnitDelta p))
    (I : (FractionalIdeal (NumberField.RingOfIntegers K)⁰
      (FractionRing (NumberField.RingOfIntegers K)))ˣ) :
    cyclotomicClassGroupMulEquiv p K sigma
        (ClassGroup.mk (FractionRing (NumberField.RingOfIntegers K)) I) =
      ClassGroup.mk (FractionRing (NumberField.RingOfIntegers K))
        (cyclotomicCanonicalFractionalIdealUnitMulEquiv p K sigma I) := by
  apply (ClassGroup.equiv
    (FractionRing (NumberField.RingOfIntegers K))).injective
  simp only [cyclotomicClassGroupMulEquiv, ClassGroup.mulEquiv_apply,
    ClassGroup.equiv_mk, QuotientGroup.congr_mk',
    MulEquiv.apply_symm_apply, FractionalIdeal.canonicalEquiv_self,
    RingEquiv.coe_mulEquiv_refl]
  rfl

/-- Computation of the class action on a represented fractional ideal. -/
theorem cyclotomicClassGroupMulEquiv_mk
    (sigma : (KummerCriterion.CyclotomicUnitDelta p))
    (I : (FractionalIdeal
      (NumberField.RingOfIntegers K)⁰ K)ˣ) :
    cyclotomicClassGroupMulEquiv p K sigma (ClassGroup.mk K I) =
      ClassGroup.mk K
        (cyclotomicFractionalIdealUnitMulEquiv p K sigma I) := by
  let F := FractionRing (NumberField.RingOfIntegers K)
  let C := FractionalIdeal.canonicalEquiv
    (NumberField.RingOfIntegers K)⁰ K F
  calc
    cyclotomicClassGroupMulEquiv p K sigma (ClassGroup.mk K I) =
        cyclotomicClassGroupMulEquiv p K sigma
          (ClassGroup.mk F (Units.mapEquiv C.toMulEquiv I)) :=
      congrArg (cyclotomicClassGroupMulEquiv p K sigma)
        (ClassGroup.mk_canonicalEquiv
          (R := NumberField.RingOfIntegers K) (K := K) F I).symm
    _ = ClassGroup.mk F
          (cyclotomicCanonicalFractionalIdealUnitMulEquiv p K sigma
            (Units.mapEquiv C.toMulEquiv I)) :=
      cyclotomicClassGroupMulEquiv_mk_fractionRing p K sigma _
    _ = ClassGroup.mk F
          (Units.mapEquiv C.toMulEquiv
            (cyclotomicFractionalIdealUnitMulEquiv p K sigma I)) :=
      congrArg (ClassGroup.mk F)
        (canonicalEquiv_cyclotomic_commute p K sigma I).symm
    _ = ClassGroup.mk K
          (cyclotomicFractionalIdealUnitMulEquiv p K sigma I) :=
      ClassGroup.mk_canonicalEquiv
        (R := NumberField.RingOfIntegers K) (K := K) F _

/-- The class action at the identity is the identity. -/
@[simp]
theorem cyclotomicClassGroupMulEquiv_one_apply
    (c : ClassGroup (NumberField.RingOfIntegers K)) :
    cyclotomicClassGroupMulEquiv p K 1 c = c := by
  have he :
      KummerCriterion.cyclotomicRingOfIntegersEquiv
          (p := p) K 1 =
        RingEquiv.refl (NumberField.RingOfIntegers K) := by
    ext x
    exact congrArg Subtype.val
      (KummerCriterion.cyclotomicRingOfIntegersEquiv_one_apply
        (p := p) (K := K) x)
  rw [cyclotomicClassGroupMulEquiv, he]
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
theorem cyclotomicClassGroupMulEquiv_mul_apply
    (sigma tau : (KummerCriterion.CyclotomicUnitDelta p))
    (c : ClassGroup (NumberField.RingOfIntegers K)) :
    cyclotomicClassGroupMulEquiv p K (sigma * tau) c =
      cyclotomicClassGroupMulEquiv p K sigma
        (cyclotomicClassGroupMulEquiv p K tau c) := by
  have he :
      KummerCriterion.cyclotomicRingOfIntegersEquiv
          (p := p) K (sigma * tau) =
        (KummerCriterion.cyclotomicRingOfIntegersEquiv
          (p := p) K tau).trans
        (KummerCriterion.cyclotomicRingOfIntegersEquiv
          (p := p) K sigma) := by
    ext x
    exact congrArg Subtype.val
      (KummerCriterion.cyclotomicRingOfIntegersEquiv_mul_apply
        (p := p) (K := K) sigma tau x)
  rw [cyclotomicClassGroupMulEquiv, he,
    cyclotomicClassGroupMulEquiv, cyclotomicClassGroupMulEquiv]
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
                (p := p) K tau).trans
               (KummerCriterion.cyclotomicRingOfIntegersEquiv
                (p := p) K sigma))).toMulEquiv I) =
        QuotientGroup.mk' _
          (Units.mapEquiv
            (FractionalIdeal.ringEquivOfRingEquiv
              (FractionRing (NumberField.RingOfIntegers K))
              (FractionRing (NumberField.RingOfIntegers K))
              (KummerCriterion.cyclotomicRingOfIntegersEquiv
                (p := p) K sigma)).toMulEquiv
            (Units.mapEquiv
              (FractionalIdeal.ringEquivOfRingEquiv
                (FractionRing (NumberField.RingOfIntegers K))
                (FractionRing (NumberField.RingOfIntegers K))
                (KummerCriterion.cyclotomicRingOfIntegersEquiv
                  (p := p) K tau)).toMulEquiv I))
      rw [FractionalIdeal.ringEquivOfRingEquiv_trans
        (FractionRing (NumberField.RingOfIntegers K))
        (FractionRing (NumberField.RingOfIntegers K))
        (FractionRing (NumberField.RingOfIntegers K))]
      congr 1

/-- The genuine cyclotomic representation on the additive class group. -/
noncomputable def cyclotomicAdditiveClassGroupRepresentation :
    Representation ℤ (KummerCriterion.CyclotomicUnitDelta p)
      (Additive (ClassGroup (NumberField.RingOfIntegers K))) where
  toFun sigma :=
    (cyclotomicClassGroupMulEquiv p K sigma).toAdditive.toIntLinearEquiv
  map_one' := by
    apply LinearMap.ext
    intro c
    exact congrArg Additive.ofMul
      (cyclotomicClassGroupMulEquiv_one_apply p K (Additive.toMul c))
  map_mul' sigma tau := by
    apply LinearMap.ext
    intro c
    exact congrArg Additive.ofMul
      (cyclotomicClassGroupMulEquiv_mul_apply p K sigma tau
        (Additive.toMul c))

/-! ## Naturality of the strict Selmer class map -/

/-- The strict Selmer ideal-class map before restricting its codomain to
`p`-torsion. -/
noncomputable def strictSelmerIdealClass :
    SelmerCarrier (NumberField.RingOfIntegers K) K p →+
      Additive (ClassGroup (NumberField.RingOfIntegers K)) :=
  MonoidHom.toAdditive <|
    IsDedekindDomain.selmerGroup.toClass
      (R := NumberField.RingOfIntegers K) (K := K) (n := p)

/-- The fraction-field automorphism induced by the cyclotomic action on the
ring of integers is the original cyclotomic field automorphism. -/
theorem cyclotomicFractionEquiv_eq (sigma : (KummerCriterion.CyclotomicUnitDelta p)) :
    IsFractionRing.ringEquivOfRingEquiv
        (KummerCriterion.cyclotomicRingOfIntegersEquiv
          (p := p) K sigma) =
      (KummerCriterion.cyclotomicSigmaOfUnit
        (p := p) K sigma).toRingEquiv := by
  apply RingEquiv.toRingHom_injective
  apply IsLocalization.ringHom_ext
    (nonZeroDivisors (NumberField.RingOfIntegers K))
  ext x
  change IsFractionRing.ringEquivOfRingEquiv
      (KummerCriterion.cyclotomicRingOfIntegersEquiv
        (p := p) K sigma)
        (algebraMap (NumberField.RingOfIntegers K) K x) =
    KummerCriterion.cyclotomicSigmaOfUnit (p := p) K sigma
      (algebraMap (NumberField.RingOfIntegers K) K x)
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  change ((KummerCriterion.cyclotomicSigmaOfUnit
      (p := p) K sigma • x : NumberField.RingOfIntegers K) : K) =
    KummerCriterion.cyclotomicSigmaOfUnit
      (p := p) K sigma • (x : K)
  exact algebraMap.coe_smul'
    (KummerCriterion.cyclotomicSigmaOfUnit
      (p := p) K sigma) x K

/-- Transport of a principal fractional ideal is the principal fractional
ideal of the transported field unit. -/
theorem cyclotomicFractionalIdealEquiv_toPrincipalIdeal
    (sigma : (KummerCriterion.CyclotomicUnitDelta p)) (x : Kˣ) :
    cyclotomicFractionalIdealUnitMulEquiv p K sigma
        (toPrincipalIdeal (NumberField.RingOfIntegers K) K x) =
      toPrincipalIdeal (NumberField.RingOfIntegers K) K
        (cyclotomicUnitEquiv p K sigma x) := by
  apply Units.ext
  rw [cyclotomicFractionalIdealUnitMulEquiv]
  simp only [Units.coe_mapEquiv, coe_toPrincipalIdeal]
  change FractionalIdeal.ringEquivOfRingEquiv K K
      (KummerCriterion.cyclotomicRingOfIntegersEquiv
        (p := p) K sigma)
      (FractionalIdeal.spanSingleton
        (NumberField.RingOfIntegers K)⁰ (x : K)) = _
  rw [FractionalIdeal.ringEquivOfRingEquiv_spanSingleton]
  apply congrArg (FractionalIdeal.spanSingleton
    (nonZeroDivisors (NumberField.RingOfIntegers K)))
  exact congrArg (fun e : K ≃+* K => e (x : K))
    (cyclotomicFractionEquiv_eq p K sigma)

omit [IsCyclotomicExtension {p} ℚ K] in
/-- Every strict Selmer class has a canonical nonzero fractional-ideal root
of the principal ideal of any chosen Kummer representative. -/
private theorem exists_strictSelmerRepresentativeRoot
    (q : SelmerCarrier (NumberField.RingOfIntegers K) K p) :
    ∃ (x : Kˣ) (I : (FractionalIdeal
        (NumberField.RingOfIntegers K)⁰ K)ˣ),
      (Additive.toMul q).1 = QuotientGroup.mk x ∧
      I ^ p =
        toPrincipalIdeal (NumberField.RingOfIntegers K) K x := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom p : Kˣ →* Kˣ).range (Additive.toMul q).1
  let f := toPrincipalIdeal (NumberField.RingOfIntegers K) K
  let geometry :=
    IsDedekindDomain.selmerGroup.fractionalIdealFactorization
      (R := NumberField.RingOfIntegers K) (K := K)
  have hdiv : x ∈ PowerRoot.divisibleElements f p := by
    rw [geometry.mem_divisibleElements_iff]
    intro v
    change (p : ℤ) ∣
      (geometry (toPrincipalIdeal
        (NumberField.RingOfIntegers K) K x)).toAdd v
    rw [IsDedekindDomain.selmerGroup.fractionalIdealFactorization_apply,
      coe_toPrincipalIdeal, count_spanSingleton_eq_neg_valuation]
    apply Int.dvd_neg.mpr
    apply (valuationOfNeZeroMod_mk_eq_one_iff_dvd
      (p := p) v x).mp
    have hy :
        (x : Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) =
          (Additive.toMul q).1 := hx
    rw [hy]
    exact (Additive.toMul q).2 v (Set.notMem_empty v)
  let divisible : PowerRoot.divisibleElements f p := ⟨x, hdiv⟩
  refine ⟨x, PowerRoot.root f p geometry divisible, hx.symm, ?_⟩
  exact PowerRoot.root_power f p geometry divisible

/-- The strict Selmer class map intertwines each actual cyclotomic Kummer
action with the induced action on the actual ideal class group. -/
theorem strictSelmerIdealClass_cyclotomic
    (sigma : (KummerCriterion.CyclotomicUnitDelta p))
    (q : SelmerCarrier (NumberField.RingOfIntegers K) K p) :
    strictSelmerIdealClass (p := p) (K := K)
        (cyclotomicStrictSelmerRepresentation p K sigma q) =
      cyclotomicAdditiveClassGroupRepresentation p K sigma
        (strictSelmerIdealClass (p := p) (K := K) q) := by
  obtain ⟨x, I, hx, hI⟩ := exists_strictSelmerRepresentativeRoot p K q
  have htransport :
      cyclotomicFractionalIdealUnitMulEquiv p K sigma I ^ p =
        toPrincipalIdeal (NumberField.RingOfIntegers K) K
          (cyclotomicUnitEquiv p K sigma x) := by
    calc
      cyclotomicFractionalIdealUnitMulEquiv p K sigma I ^ p =
          cyclotomicFractionalIdealUnitMulEquiv p K sigma
            (I ^ p) := (map_pow _ I p).symm
      _ = cyclotomicFractionalIdealUnitMulEquiv p K sigma
            (toPrincipalIdeal
              (NumberField.RingOfIntegers K) K x) := by rw [hI]
      _ = toPrincipalIdeal (NumberField.RingOfIntegers K) K
            (cyclotomicUnitEquiv p K sigma x) :=
        cyclotomicFractionalIdealEquiv_toPrincipalIdeal p K sigma x
  have hqAction :
      (Additive.toMul
        (cyclotomicStrictSelmerRepresentation p K sigma q)).1 =
        QuotientGroup.mk (cyclotomicUnitEquiv p K sigma x) := by
    change cyclotomicKummerHom p K sigma (Additive.toMul q).1 = _
    rw [hx]
    exact cyclotomicKummerHom_mk p K sigma x
  apply Additive.toMul.injective
  change IsDedekindDomain.selmerGroup.toClass
      (R := NumberField.RingOfIntegers K) (K := K) (n := p)
      (Additive.toMul
        (cyclotomicStrictSelmerRepresentation p K sigma q)) =
    cyclotomicClassGroupMulEquiv p K sigma
      (IsDedekindDomain.selmerGroup.toClass
        (R := NumberField.RingOfIntegers K) (K := K) (n := p)
        (Additive.toMul q))
  rw [IsDedekindDomain.selmerGroup.toClass_eq_mk_of_representative_root
      (q := Additive.toMul q) (x := x) (hx := hx)
      (I := I) (hI := hI),
    IsDedekindDomain.selmerGroup.toClass_eq_mk_of_representative_root
      (q := Additive.toMul
        (cyclotomicStrictSelmerRepresentation p K sigma q))
      (x := cyclotomicUnitEquiv p K sigma x) (hx := hqAction)
      (I := cyclotomicFractionalIdealUnitMulEquiv p K sigma I)
      (hI := htransport),
    cyclotomicClassGroupMulEquiv_mk]

/-! ## The p-torsion representation and character projector -/

/-- The actual p-torsion subgroup of the class group, which is exactly the
range of the strict Selmer class map. -/
abbrev ClassTorsion :=
  ClassPTorsion (NumberField.RingOfIntegers K) p

local instance instClassTorsionModuleZMod :
    Module (ZMod p) (ClassTorsion p K) :=
  AddSubgroup.torsionBy.zmodModule

local instance instClassTorsionModulePadicInt :
    Module (PadicInt p) (ClassTorsion p K) :=
  Module.compHom (ClassTorsion p K) PadicInt.toZMod

/-- Restriction of one genuine class-group automorphism to its stable
p-torsion subgroup. -/
noncomputable def cyclotomicClassTorsionAddHom
    (sigma : (KummerCriterion.CyclotomicUnitDelta p)) :
    ClassTorsion p K →+ ClassTorsion p K where
  toFun c := ⟨
    cyclotomicAdditiveClassGroupRepresentation p K sigma c,
    by
      apply AddSubgroup.torsionBy.nsmul_iff.mpr
      have hc := AddSubgroup.torsionBy.nsmul_iff.mp c.property
      change p • cyclotomicAdditiveClassGroupRepresentation p K sigma
          (c : Additive (ClassGroup
            (NumberField.RingOfIntegers K))) = 0
      calc
        p • cyclotomicAdditiveClassGroupRepresentation p K sigma
            (c : Additive (ClassGroup
              (NumberField.RingOfIntegers K))) =
            cyclotomicAdditiveClassGroupRepresentation p K sigma
              (p • (c : Additive (ClassGroup
                (NumberField.RingOfIntegers K)))) :=
          (map_nsmul
            (cyclotomicAdditiveClassGroupRepresentation p K sigma) p
            (c : Additive (ClassGroup
              (NumberField.RingOfIntegers K)))).symm
        _ = 0 := by rw [hc, map_zero]⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero (cyclotomicAdditiveClassGroupRepresentation p K sigma)
  map_add' x y := by
    apply Subtype.ext
    exact map_add (cyclotomicAdditiveClassGroupRepresentation p K sigma)
      (x : Additive (ClassGroup (NumberField.RingOfIntegers K)))
      (y : Additive (ClassGroup (NumberField.RingOfIntegers K)))

/-- The restricted action is linear over integral p-adic coefficients,
whose action on this carrier factors through `ZMod p`. -/
noncomputable def cyclotomicClassTorsionLinearMap
    (sigma : (KummerCriterion.CyclotomicUnitDelta p)) :
    ClassTorsion p K →ₗ[PadicInt p] ClassTorsion p K where
  toFun := cyclotomicClassTorsionAddHom p K sigma
  map_add' := map_add _
  map_smul' a c := by
    change cyclotomicClassTorsionAddHom p K sigma
        (PadicInt.toZMod a • c) =
      PadicInt.toZMod a • cyclotomicClassTorsionAddHom p K sigma c
    exact ZMod.map_smul (cyclotomicClassTorsionAddHom p K sigma)
      (PadicInt.toZMod a) c

/-- The induced cyclotomic representation on the actual p-torsion class
group. -/
noncomputable def cyclotomicClassTorsionRepresentation :
    Representation (PadicInt p) (KummerCriterion.CyclotomicUnitDelta p) (ClassTorsion p K) where
  toFun sigma := cyclotomicClassTorsionLinearMap p K sigma
  map_one' := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact congrArg Additive.ofMul
      (cyclotomicClassGroupMulEquiv_one_apply p K
        (Additive.toMul (c : Additive
          (ClassGroup (NumberField.RingOfIntegers K)))))
  map_mul' sigma tau := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact congrArg Additive.ofMul
      (cyclotomicClassGroupMulEquiv_mul_apply p K sigma tau
        (Additive.toMul (c : Additive
          (ClassGroup (NumberField.RingOfIntegers K)))))

/-- The strict Selmer class map with its genuine p-torsion codomain. -/
noncomputable def strictSelmerClassLinearMap :
    SelmerCarrier (NumberField.RingOfIntegers K) K p →ₗ[PadicInt p]
      ClassTorsion p K where
  toFun := selmerClassProjection
    (R := NumberField.RingOfIntegers K) (K := K) (p := p)
  map_add' := map_add _
  map_smul' a q := by
    change selmerClassProjection
        (R := NumberField.RingOfIntegers K) (K := K) (p := p)
        (PadicInt.toZMod a • q) =
      PadicInt.toZMod a •
        selmerClassProjection
          (R := NumberField.RingOfIntegers K) (K := K) (p := p) q
    exact ZMod.map_smul
      (selmerClassProjection
        (R := NumberField.RingOfIntegers K) (K := K) (p := p))
      (PadicInt.toZMod a) q

omit [IsCyclotomicExtension {p} ℚ K] in
/-- Forgetting the torsion proof recovers the previously exposed full
class-group map definitionally. -/
@[simp]
theorem strictSelmerClassLinearMap_value
    (q : SelmerCarrier (NumberField.RingOfIntegers K) K p) :
    (strictSelmerClassLinearMap p K q :
      Additive (ClassGroup (NumberField.RingOfIntegers K))) =
      strictSelmerIdealClass (p := p) (K := K) q :=
  rfl

/-- The restricted class map is an honest intertwiner of the two
cyclotomic representations. -/
noncomputable def strictSelmerClassIntertwiner :
    Representation.IntertwiningMap
      (cyclotomicStrictSelmerRepresentation p K)
      (cyclotomicClassTorsionRepresentation p K) :=
  (strictSelmerClassLinearMap p K).intertwiningMap_of_isIntertwiningMap
    (cyclotomicStrictSelmerRepresentation p K)
    (cyclotomicClassTorsionRepresentation p K) <| by
      intro sigma q
      apply Subtype.ext
      exact strictSelmerIdealClass_cyclotomic p K sigma q

/-- The character-idempotent action on the genuine class-group
p-torsion. -/
noncomputable def cyclotomicClassProjector
    [Invertible (Fintype.card (KummerCriterion.CyclotomicUnitDelta p) : PadicInt p)]
    (eta : Character (PadicInt p) (KummerCriterion.CyclotomicUnitDelta p)) :
    ClassTorsion p K →ₗ[PadicInt p] ClassTorsion p K :=
  (cyclotomicClassTorsionRepresentation p K).asAlgebraHom
    (characterIdempotent eta)

/-- Strong projector naturality: class projection after any Selmer
character projector is the same character projector applied to the actual
p-torsion ideal class. -/
theorem strictSelmerClassLinearMap_characterProjector
    [Invertible (Fintype.card (KummerCriterion.CyclotomicUnitDelta p) : PadicInt p)]
    (eta : Character (PadicInt p) (KummerCriterion.CyclotomicUnitDelta p))
    (q : SelmerCarrier (NumberField.RingOfIntegers K) K p) :
    strictSelmerClassLinearMap p K
        ((characterProjectorAt
          (cyclotomicStrictSelmerRepresentation p K) eta q).1) =
      cyclotomicClassProjector p K eta
        (strictSelmerClassLinearMap p K q) := by
  change strictSelmerClassLinearMap p K
      ((cyclotomicStrictSelmerRepresentation p K).asAlgebraHom
        (characterIdempotent eta) q) =
    (cyclotomicClassTorsionRepresentation p K).asAlgebraHom
      (characterIdempotent eta) (strictSelmerClassLinearMap p K q)
  let F :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      (cyclotomicStrictSelmerRepresentation p K)
      (cyclotomicClassTorsionRepresentation p K))
      (strictSelmerClassIntertwiner p K)
  exact F.map_smul (characterIdempotent eta) q

end Fermat.Conservation.PrimeCyclotomicSelmerClassNaturality
