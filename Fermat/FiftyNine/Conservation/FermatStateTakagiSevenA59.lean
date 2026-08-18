/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Takagi--Furtwängler relation (7a) for the allocated Fermat state

The historical exponent-59 development proves the Takagi--Furtwängler
principalization theorem for a conjugate Kummer-primary pair.  The newer
conservation development independently constructs the two ideal roots of a
literal primitive second-case Fermat state.  This file connects those two
implementations.

The bridge first derives the required depth-60 primary congruence directly
from the oriented Fermat equation.  It then applies the existing global
Takagi reflection theorem to the actual allocated ideals.  Thus relation
(7a) is obtained for the state ledger itself; it is not inserted as a
provider field or a per-ledger certificate.
-/
import Fermat.Irregular.TakagiReflection59
import Fermat.FiftyNine.VandiverHistorical
import Fermat.FiftyNine.Conservation.StateFactorConjugation

open scoped NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Fermat.FiftyNine.Conservation.FermatStateTakagiSevenA59

open Fermat.Conservation.Credit.Fold
open Fermat.Irregular.TakagiReflection59
open Fermat.Irregular.VandiverCriterion
open Fermat.Irregular.VandiverLemmaOne
open Fermat.FiftyNine.Conservation.FermatState
open Fermat.FiftyNine.Conservation.StateFactorConjugation
open Fermat.FiftyNine.Conservation.StateFactorPair
open Fermat.FiftyNine.VandiverHistorical

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 59) K (by norm_num)

variable {zeta : K} {hZeta : IsPrimitiveRoot zeta 59}
  {S : PrimitiveSecondCaseSolution} {hz : (59 : ℤ) ∣ S.z}

/-! ## The literal Fermat factor is Kummer-primary -/

/-- The conjugate-pair radicand built from the conservation layer's
normalized plus factor is Kummer-primary.  The proof reconstructs the
class-number-free local part of Vandiver's argument directly from the
oriented Fermat state. -/
theorem normalizedPlus_conjugatePair_isKummerPrimary59
    (hZeta : IsPrimitiveRoot zeta 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) :
    IsKummerPrimary hZeta
      (normalizedPlusFactor hZeta S hz *
        (NumberField.IsCMField.ringOfIntegersComplexConj K
          (normalizedPlusFactor hZeta S hz)) ^ 58) := by
  obtain ⟨t, ht⟩ := hz
  have hz' : (59 : ℤ) ∣ S.z := ⟨t, ht⟩
  obtain ⟨u, hu⟩ := associated_zeta_sub_one_pow_prime hZeta
  let xi : 𝓞 K := (u : 𝓞 K) * (t : 𝓞 K)
  let epsilon : (𝓞 K)ˣ := 1
  have hcast59 : (((59 : ℤ) : 𝓞 K)) = (59 : 𝓞 K) := by
    norm_num
  have hequation :
      (S.x : 𝓞 K) ^ 59 + (S.y : 𝓞 K) ^ 59 =
        epsilon *
          (((hZeta.unit' : 𝓞 K) - 1) ^ (57 + 1) * xi) ^ 59 := by
    simp only [epsilon, Units.val_one, one_mul]
    calc
      (S.x : 𝓞 K) ^ 59 + (S.y : 𝓞 K) ^ 59 =
          (S.z : 𝓞 K) ^ 59 := stateEquation S
      _ = ((((59 : ℤ) : 𝓞 K) * (t : 𝓞 K))) ^ 59 := by
        rw [ht, Int.cast_mul]
      _ = ((59 : 𝓞 K) * (t : 𝓞 K)) ^ 59 := by
        exact congrArg (fun a : 𝓞 K ↦ (a * (t : 𝓞 K)) ^ 59) hcast59
      _ = (((hZeta.unit' : 𝓞 K) - 1) ^ 58 *
          ((u : 𝓞 K) * (t : 𝓞 K))) ^ 59 := by
        congr 1
        rw [← mul_assoc, hu]
        norm_num
      _ = (((hZeta.unit' : 𝓞 K) - 1) ^ (57 + 1) * xi) ^ 59 := by
        norm_num [xi]

  have hxy : IsCoprime (S.x : 𝓞 K) (S.y : 𝓞 K) := by
    simpa using (state_isCoprime_x_y S).map (Int.castRingHom (𝓞 K))
  have hy : ¬ (hZeta.unit' : 𝓞 K) - 1 ∣ (S.y : 𝓞 K) := by
    intro hy
    have hsum : (hZeta.unit' : 𝓞 K) - 1 ∣
        (S.x : 𝓞 K) ^ 59 + (S.y : 𝓞 K) ^ 59 :=
      zeta_sub_one_dvd (K := K) (p := 59)
        (x := (S.x : 𝓞 K)) (y := (S.y : 𝓞 K))
        (z := xi) (ε := epsilon) (m := 57) hZeta hequation
    have hxpow : (hZeta.unit' : 𝓞 K) - 1 ∣
        (S.x : 𝓞 K) ^ 59 := by
      simpa using dvd_sub hsum (dvd_pow hy (by norm_num : 59 ≠ 0))
    have hx : (hZeta.unit' : 𝓞 K) - 1 ∣ (S.x : 𝓞 K) :=
      hZeta.zeta_sub_one_prime'.dvd_of_dvd_pow hxpow
    exact hZeta.zeta_sub_one_prime'.not_unit
      (hxy.isUnit_of_dvd' hx hy)

  have hxreal :
      NumberField.IsCMField.ringOfIntegersComplexConj K (S.x : 𝓞 K) =
        (S.x : 𝓞 K) := by simp
  have hyreal :
      NumberField.IsCMField.ringOfIntegersComplexConj K (S.y : 𝓞 K) =
        (S.y : 𝓞 K) := by simp
  have hroot := distinguishedRoot_eq_one_of_real59
    (K := K) (x := (S.x : 𝓞 K)) (y := (S.y : 𝓞 K))
    (z := xi) (ε := epsilon) (m := 57)
    hZeta hequation hy hxreal hyreal
  have hhigh := distinguishedFactor_highDivisibility
    (K := K) (p := 59) (x := (S.x : 𝓞 K))
    (y := (S.y : 𝓞 K)) (z := xi) (ε := epsilon) (m := 57)
    (by norm_num : 59 ≠ 2) hZeta hequation hy
  rw [hroot] at hhigh
  simp only [oneNthRoot, mul_one] at hhigh
  have hsixty :
      ((hZeta.unit' : 𝓞 K) - 1) ^ 60 ∣
        (S.x : 𝓞 K) + (S.y : 𝓞 K) := by
    exact (pow_dvd_pow_of_dvd_of_le dvd_rfl (by norm_num : 60 ≤ 57 * 59 + 1)).trans
      hhigh

  let qplus : 𝓞 K :=
    div_zeta_sub_one (by norm_num : 59 ≠ 2) hZeta hequation
      (zetaNthRoot (K := K) (p := 59) hZeta)
  let qminus : 𝓞 K :=
    div_zeta_sub_one (by norm_num : 59 ≠ 2) hZeta hequation
      (inverseZetaNthRoot (K := K) (p := 59) hZeta)
  have hdenominator : (hZeta.unit' : 𝓞 K) - 1 ≠ 0 :=
    hZeta.unit'_coe.sub_one_ne_zero (by norm_num)
  have hunitVal : (hZeta.unit' : 𝓞 K) = hZeta.toInteger := rfl
  have hzetaUnit : zetaUnit hZeta = hZeta.unit' := by
    apply Units.ext
    exact zetaUnit_val hZeta
  have hqplus : qplus = normalizedPlusFactor hZeta S hz' := by
    apply mul_right_cancel₀ hdenominator
    calc
      qplus * ((hZeta.unit' : 𝓞 K) - 1) =
          (S.x : 𝓞 K) + (S.y : 𝓞 K) * (hZeta.unit' : 𝓞 K) := by
        exact div_zeta_sub_one_mul_zeta_sub_one
          (by norm_num : 59 ≠ 2) hZeta hequation
            (zetaNthRoot (K := K) (p := 59) hZeta)
      _ = normalizedPlusFactor hZeta S hz' *
          ((hZeta.unit' : 𝓞 K) - 1) := by
        simpa only [Fermat.Conservation.KummerDrain.factorNode,
          fixedDenominator, hunitVal, mul_comm] using
            (normalizedPlusFactor_spec hZeta S hz').symm
  have hqminus : qminus = normalizedMinusFactor hZeta S hz' := by
    apply mul_right_cancel₀ hdenominator
    calc
      qminus * ((hZeta.unit' : 𝓞 K) - 1) =
          (S.x : 𝓞 K) + (S.y : 𝓞 K) *
            (hZeta.unit'⁻¹ : (𝓞 K)ˣ) := by
        exact div_zeta_sub_one_mul_zeta_sub_one
          (by norm_num : 59 ≠ 2) hZeta hequation
            (inverseZetaNthRoot (K := K) (p := 59) hZeta)
      _ = normalizedMinusFactor hZeta S hz' *
          ((hZeta.unit' : 𝓞 K) - 1) := by
        simpa only [Fermat.Conservation.KummerDrain.factorNode,
          fixedDenominator, hunitVal, hzetaUnit, mul_comm] using
            (normalizedMinusFactor_spec hZeta S hz').symm

  have hconjugate :
      (((-hZeta.unit' : (𝓞 K)ˣ) : 𝓞 K) *
          normalizedMinusFactor hZeta S hz') =
        NumberField.IsCMField.ringOfIntegersComplexConj K
          (normalizedPlusFactor hZeta S hz') := by
    rw [normalizedMinusFactor_eq_unit_mul_conj]
    rw [hzetaUnit]
    simp

  have hprimary := normalizedConjugateLinearFactor_isKummerPrimary
    (by norm_num : 59 ≠ 2) hZeta hequation hy hsixty
  change IsKummerPrimary hZeta
      (qplus * ((((-hZeta.unit' : (𝓞 K)ˣ) : 𝓞 K) * qminus) ^ 58))
    at hprimary
  rw [hqplus, hqminus, hconjugate] at hprimary
  exact hprimary

/-! ## Takagi principalization on the allocated pair -/

/-- Powers of a nonzero fractional ideal become natural multiples of its
additive ideal class.  This small public-independent helper lets the literal
principal product returned by Takagi be read in the conservation ledger. -/
private theorem fractionalIdealClass_pow
    {A L : Type*} [CommRing A] [IsDedekindDomain A]
    [Field L] [Algebra A L] [IsFractionRing A L]
    (I : FractionalIdeal A⁰ L) (hI : I ≠ 0) (n : ℕ) :
    fractionalIdealClass (I ^ n) (pow_ne_zero n hI) =
      n • fractionalIdealClass I hI := by
  change ClassGroup.mk L (Units.mk0 (I ^ n) (pow_ne_zero n hI)) =
    (ClassGroup.mk L (Units.mk0 I hI)) ^ n
  rw [← map_pow]
  apply congrArg (ClassGroup.mk L)
  ext
  rfl

/-- The fully constructed Takagi--Furtwängler generator for the two ideals
allocated by the literal Fermat state. -/
theorem exists_takagiSevenAGenerator
    (pair : StateLinkedIdealPair hZeta S hz) :
    ∃ r : 𝓞 K,
      pair.plusIdeal * pair.minusIdeal ^ 58 = Ideal.span {r} := by
  have hminusPow :
      pair.minusIdeal ^ 59 =
        Ideal.span
          {NumberField.IsCMField.ringOfIntegersComplexConj K
            (normalizedPlusFactor hZeta S hz)} := by
    calc
      pair.minusIdeal ^ 59 =
          Ideal.span {normalizedMinusFactor hZeta S hz} := pair.minus_pow
      _ = Ideal.map
          (NumberField.IsCMField.ringOfIntegersComplexConj K)
          (Ideal.span {normalizedPlusFactor hZeta S hz}) :=
        span_normalizedMinusFactor_eq_map_conj hZeta S hz
      _ = Ideal.span
          {NumberField.IsCMField.ringOfIntegersComplexConj K
            (normalizedPlusFactor hZeta S hz)} := by
        rw [Ideal.map_span, Set.image_singleton]
  exact exists_conjugatePairEquationSevenAGenerator59 hZeta
    pair.plusIdeal pair.minusIdeal
    (normalizedPlusFactor hZeta S hz)
    (NumberField.IsCMField.ringOfIntegersComplexConj K
      (normalizedPlusFactor hZeta S hz))
    pair.plus_pow hminusPow rfl
    (normalizedPlus_conjugatePair_isKummerPrimary59 hZeta S hz)

/-- **Actual relation (7a).**  Takagi's principal product is exactly the
Vandiver word in the two-node allocated class ledger. -/
theorem vandiverSevenA_takagi
    (pair : StateLinkedIdealPair hZeta S hz) :
    pair.ledger.VandiverSevenA 0 1 := by
  obtain ⟨r, hr⟩ := exists_takagiSevenAGenerator pair
  let IF : FractionalIdeal (𝓞 K)⁰ K := pair.plusIdeal
  let JF : FractionalIdeal (𝓞 K)⁰ K := pair.minusIdeal
  have hIF : IF ≠ 0 := by
    exact FractionalIdeal.coeIdeal_ne_zero.mpr pair.plusIdeal_ne_zero
  have hJF : JF ≠ 0 := by
    exact FractionalIdeal.coeIdeal_ne_zero.mpr pair.minusIdeal_ne_zero
  have hprincipal : Submodule.IsPrincipal
      ((IF * JF ^ 58 : FractionalIdeal (𝓞 K)⁰ K) :
        Submodule (𝓞 K) K) := by
    rw [FractionalIdeal.isPrincipal_iff]
    refine ⟨(r : K), ?_⟩
    dsimp [IF, JF]
    rw [← FractionalIdeal.coeIdeal_span_singleton, ← hr,
      FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_pow]
  unfold Fermat.Conservation.KummerDrain.AllocatedFactorLedger.VandiverSevenA
  change
    fractionalIdealClass IF hIF + 58 • fractionalIdealClass JF hJF = 0
  rw [← fractionalIdealClass_pow]
  rw [← fractionalIdealClass_mul]
  exact (fractionalIdealClass_eq_zero_iff _ _).mpr hprincipal

/-! ## Net the two actual state classes -/

/-- Relations (7a) and (7d) now kill both allocated state classes.  This is
strictly statewise: it does not assert that the whole class-group character
component vanishes. -/
theorem rootClasses_eq_zero_takagi
    (pair : StateLinkedIdealPair hZeta S hz) :
    pair.ledger.rootClass 0 = 0 ∧ pair.ledger.rootClass 1 = 0 :=
  odd_torsion_netting (by norm_num)
    (pair.ledger.rootClass 0) (pair.ledger.rootClass 1)
    (pair.ledger.rootClass_torsion 1)
    (vandiverSevenA_takagi pair)
    (StateFactorConjugation.StateLinkedIdealPair.vandiverSevenD pair)

/-- The Takagi relation and the already-proved relative-norm relation
therefore discharge the complete two-node factor-principalization permit. -/
theorem factorPrincipalizationPermit_takagi
    (pair : StateLinkedIdealPair hZeta S hz) :
    Fermat.Conservation.KummerDrain.FactorPrincipalizationPermit
      pair.ledger :=
  StateFactorConjugation.StateLinkedIdealPair.factorPrincipalizationPermit_of_sevenA
    pair (vandiverSevenA_takagi pair)

end Fermat.FiftyNine.Conservation.FermatStateTakagiSevenA59
