/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Class silence of the canonical conjugate-pair source

The conjugate-pair construction retains a literal 827-unit in the same
Kummer class as its q-relaxed source.  This file proves that the canonical
cyclotomic action preserves that finite-S unit range, hence so does the
genuine reflected character idempotent.  Promoting the resulting 827-unit
to the two-prime detector support and applying the finite-S kernel theorem
then proves the projected class obstruction is the identity.

No class certificate, action provider, splitting, or new premise is used.
-/
import Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
import Fermat.FiftyNine.Conservation.GaugeSteering827
import Fermat.FiftyNine.Conservation.ConjugatePairSource827

open scoped BigOperators MonoidAlgebra nonZeroDivisors NumberField Pointwise

noncomputable section

namespace Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827

open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.ConjugatePairSource827
open Fermat.FiftyNine.Conservation.GaugeSteering827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

/-- Cyclotomic transport of a literal 827-unit. -/
noncomputable def cyclotomicSUnit827
    (sigma : GaloisIndex59) (u : (placesOver827 K).unit K) :
    (placesOver827 K).unit K :=
  ⟨cyclotomicUnitEquiv59 K sigma (u : Kˣ), by
    intro v hv
    have htransport : cyclotomicPlaceEquiv59 K sigma⁻¹ v ∉ placesOver827 K := by
      intro hmem
      exact hv ((cyclotomicPlaceEquiv59_mem_placesOver827_iff
        K sigma⁻¹ v).mp hmem)
    rw [← v.valuationOfNeZero_eq,
      valuationOfNeZero_cyclotomic59,
      IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq]
    exact Set.unit_valuation_eq_one
      (placesOver827 K) K u htransport⟩

/-- The finite-S lift intertwines the literal S-unit action and the
canonical q-relaxed Selmer action. -/
theorem fromSUnitLift_cyclotomicSUnit827
    (sigma : GaloisIndex59) (u : (placesOver827 K).unit K) :
    (cyclotomicQRelaxedSelmerRepresentation827 K) sigma
        (Additive.ofMul
          (IsDedekindDomain.selmerGroup.fromSUnitLift
            (R := NumberField.RingOfIntegers K) (K := K) (n := 59)
            (placesOver827 K) (QuotientGroup.mk u))) =
      Additive.ofMul
        (IsDedekindDomain.selmerGroup.fromSUnitLift
          (R := NumberField.RingOfIntegers K) (K := K) (n := 59)
          (placesOver827 K)
          (QuotientGroup.mk (cyclotomicSUnit827 sigma u))) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change cyclotomicKummerHom59 K sigma
      (QuotientGroup.mk (u : Kˣ)) =
    QuotientGroup.mk (cyclotomicUnitEquiv59 K sigma (u : Kˣ))
  exact cyclotomicKummerHom59_mk K sigma (u : Kˣ)

/-- The additive subgroup consisting exactly of literal 827-unit classes
inside the q-relaxed carrier. -/
abbrev QRelaxedSUnitRange827 :
    AddSubgroup (QRelaxedSelmerCarrier827 K) :=
  (IsDedekindDomain.selmerGroup.fromSUnitLift
    (R := NumberField.RingOfIntegers K) (K := K) (n := 59)
    (placesOver827 K)).range.toAddSubgroup

/-- The retained conjugate-pair source lies in the literal 827-unit range. -/
theorem conjugatePairSource827_mem_sUnitRange
    (place : Place827 K) :
    conjugatePairSource827 place ∈ QRelaxedSUnitRange827 (K := K) := by
  change Additive.toMul (conjugatePairSource827 place) ∈
    (IsDedekindDomain.selmerGroup.fromSUnitLift
      (R := NumberField.RingOfIntegers K) (K := K) (n := 59)
      (placesOver827 K)).range
  exact ⟨QuotientGroup.mk (conjugatePairSUnit827 place),
    fromSUnitLift_conjugatePairSUnit827 place⟩

/-- Every cyclotomic translate of the conjugate-pair source remains a
literal 827-unit class. -/
theorem cyclotomic_conjugatePairSource827_mem_sUnitRange
    (place : Place827 K) (sigma : GaloisIndex59) :
    (cyclotomicQRelaxedSelmerRepresentation827 K) sigma
        (conjugatePairSource827 place) ∈
      QRelaxedSUnitRange827 (K := K) := by
  change Additive.toMul
      ((cyclotomicQRelaxedSelmerRepresentation827 K) sigma
        (conjugatePairSource827 place)) ∈
    (IsDedekindDomain.selmerGroup.fromSUnitLift
      (R := NumberField.RingOfIntegers K) (K := K) (n := 59)
      (placesOver827 K)).range
  refine ⟨QuotientGroup.mk
    (cyclotomicSUnit827 sigma (conjugatePairSUnit827 place)), ?_⟩
  apply Additive.ofMul.injective
  rw [← fromSUnitLift_cyclotomicSUnit827]
  exact congrArg
    ((cyclotomicQRelaxedSelmerRepresentation827 K) sigma)
    (Additive.toMul.injective
      (fromSUnitLift_conjugatePairSUnit827 place))

omit [IsCyclotomicExtension {59} ℚ K] in
/-- The literal S-unit range is closed under the p-adic coefficient action,
which factors through an ordinary repeated sum modulo 59. -/
theorem padicInt_smul_mem_sUnitRange
    (a : PadicInt 59) {source : QRelaxedSelmerCarrier827 K}
    (hsource : source ∈ QRelaxedSUnitRange827 (K := K)) :
    a • source ∈ QRelaxedSUnitRange827 (K := K) := by
  rw [SelmerEigenspace.padicInt_smul_eq_toZMod_smul]
  change (PadicInt.toZMod a).val • source ∈
    QRelaxedSUnitRange827 (K := K)
  exact (QRelaxedSUnitRange827 (K := K)).nsmul_mem
    hsource (PadicInt.toZMod a).val

variable [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

/-- The genuine character idempotent preserves the finite-S unit range of
the conjugate-pair source. -/
theorem characterProjector_conjugatePairSource827_mem_sUnitRange
    (eta : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (place : Place827 K) :
    (SelmerEigenspace.characterProjectorAt
      (cyclotomicQRelaxedSelmerRepresentation827 K) eta
      (conjugatePairSource827 place)).1 ∈
        QRelaxedSUnitRange827 (K := K) := by
  change (cyclotomicQRelaxedSelmerRepresentation827 K).asAlgebraHom
      (InvolutiveBase.characterIdempotent eta)
      (conjugatePairSource827 place) ∈
    QRelaxedSUnitRange827 (K := K)
  rw [InvolutiveBase.characterIdempotent, map_smul, map_sum]
  simp only [LinearMap.smul_apply,
    Representation.asAlgebraHom_single]
  apply padicInt_smul_mem_sUnitRange
  rw [LinearMap.sum_apply]
  change (∑ sigma ∈ Finset.univ,
      ((↑((eta sigma)⁻¹) : PadicInt 59) •
        (cyclotomicQRelaxedSelmerRepresentation827 K) sigma)
          (conjugatePairSource827 place)) ∈
    QRelaxedSUnitRange827 (K := K)
  have hsum := (QRelaxedSUnitRange827 (K := K)).sum_mem
    (t := Finset.univ)
    (f := fun sigma : GaloisIndex59 =>
      ((↑((eta sigma)⁻¹) : PadicInt 59) •
        (cyclotomicQRelaxedSelmerRepresentation827 K) sigma)
          (conjugatePairSource827 place)) (by
      intro sigma _
      apply padicInt_smul_mem_sUnitRange
      exact cyclotomic_conjugatePairSource827_mem_sUnitRange place sigma)
  exact hsum

/-- A literal 827-unit is also a unit for the larger two-prime detector
support. -/
noncomputable def conjugatePairDetectorSUnit827
    (u : (placesOver827 K).unit K) :
    (detectorSupport827 K).unit K :=
  ⟨(u : Kˣ), by
    intro v hv
    exact Set.unit_valuation_eq_one (placesOver827 K) K u
      (fun hq => hv (Or.inr hq))⟩

/-- The canonical reflected projection of the actual conjugate-pair source
has identity finite-S class obstruction. -/
theorem projectedCandidateSClassObstruction827_conjugatePair_canonical_eq_one
    (place : Place827 K) :
    projectedCandidateSClassObstruction827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59
        (conjugatePairSource827 place) = 1 := by
  have hprojected :=
    characterProjector_conjugatePairSource827_mem_sUnitRange
      (K := K)
      (InvolutiveBase.reflectedCharacter
        canonicalTeichmullerCharacter59 irregularCharacter59) place
  change Additive.toMul
      (qRelaxedReflectedProjector827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59
        (conjugatePairSource827 place)).1 ∈
    (IsDedekindDomain.selmerGroup.fromSUnitLift
      (R := NumberField.RingOfIntegers K) (K := K) (n := 59)
      (placesOver827 K)).range at hprojected
  obtain ⟨qclass, hqclass⟩ := hprojected
  let u : (placesOver827 K).unit K := qclass.out
  have hu : QuotientGroup.mk u = qclass := QuotientGroup.out_eq' qclass
  have hlift :
      IsDedekindDomain.selmerGroup.fromSUnitLift
          (R := NumberField.RingOfIntegers K) (K := K) (n := 59)
          (placesOver827 K) (QuotientGroup.mk u) =
        Additive.toMul
          (qRelaxedReflectedProjector827
            (cyclotomicQRelaxedSelmerRepresentation827 K)
            canonicalTeichmullerCharacter59 irregularCharacter59
            (conjugatePairSource827 place)).1 := by
    rw [hu]
    exact hqclass
  have hrange :
      projectedCandidateAtDetectorSupport827
          (cyclotomicQRelaxedSelmerRepresentation827 K)
          canonicalTeichmullerCharacter59 irregularCharacter59
          (conjugatePairSource827 place) ∈
        (IsDedekindDomain.selmerGroup.fromSUnitLift
          (R := NumberField.RingOfIntegers K) (K := K) (n := 59)
          (detectorSupport827 K)).range := by
    refine ⟨QuotientGroup.mk
      (conjugatePairDetectorSUnit827 u), ?_⟩
    apply Subtype.ext
    change (QuotientGroup.mk (u : Kˣ) :
        Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) =
      (Additive.toMul
        (qRelaxedReflectedProjector827
          (cyclotomicQRelaxedSelmerRepresentation827 K)
          canonicalTeichmullerCharacter59 irregularCharacter59
          (conjugatePairSource827 place)).1).1
    exact congrArg
      (fun q : IsDedekindDomain.selmerGroup
        (R := NumberField.RingOfIntegers K) (K := K)
        (S := placesOver827 K) (n := 59) => q.1) hlift
  rw [← IsDedekindDomain.selmerGroup.toSClass_ker
    (R := NumberField.RingOfIntegers K) (K := K) (n := 59)] at hrange
  exact hrange

/-- Additive kernel spelling of the same canonical class-silence result. -/
theorem relaxedClassProjection827_conjugatePair_canonical_eq_zero
    (place : Place827 K) :
    relaxedClassProjection827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59
        (conjugatePairSource827 place) = 0 := by
  exact (relaxedClassProjection827_eq_zero_iff
    (cyclotomicQRelaxedSelmerRepresentation827 K)
    canonicalTeichmullerCharacter59 irregularCharacter59 _).2
      (projectedCandidateSClassObstruction827_conjugatePair_canonical_eq_one
        place)

end Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827
