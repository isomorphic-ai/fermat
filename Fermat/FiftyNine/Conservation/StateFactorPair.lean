/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# The normalized two-factor Fermat state

An oriented integral state supplies the raw cyclotomic factorization.  The
two factors at `ζ` and `ζ⁻¹` are then divided by their common ramified
factor `ζ - 1`.  Pairwise coprimality of the complete normalized
factorization extracts ideal roots for every node and hence supplies the
selected allocated pair.

The allocation package contains neither Vandiver relation and does not
assume principalization of either selected root.
-/
import Fermat.Conservation.KummerDrain
import Fermat.FiftyNine.Conservation.FermatState
import Mathlib.NumberTheory.FLT.Basic
import Mathlib.Tactic

open scoped BigOperators NumberField

namespace Fermat.FiftyNine.Conservation.StateFactorPair

open Fermat.FiftyNine.Conservation.FermatState

noncomputable section

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

omit [NumberField K] [IsCyclotomicExtension {59} ℚ K] in
/-- The integer Fermat equation transported to the cyclotomic integers. -/
theorem stateEquation (S : PrimitiveSecondCaseSolution) :
    (S.x : 𝓞 K) ^ 59 + (S.y : 𝓞 K) ^ 59 =
      (S.z : 𝓞 K) ^ 59 := by
  have h := congrArg (Int.castRingHom (𝓞 K)) S.equation
  simp only [map_add, map_pow] at h
  change (S.x : 𝓞 K) ^ 59 + (S.y : 𝓞 K) ^ 59 =
    (S.z : 𝓞 K) ^ 59 at h
  exact h

/-- In second-case orientation, Fermat's congruence gives `59 ∣ x + y`. -/
theorem prime_dvd_x_add_y
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) :
    (59 : ℤ) ∣ S.x + S.y := by
  have heqmod :
      (S.x : ZMod 59) ^ 59 + (S.y : ZMod 59) ^ 59 =
        (S.z : ZMod 59) ^ 59 := by
    have h := congrArg (Int.castRingHom (ZMod 59)) S.equation
    simp only [map_add, map_pow] at h
    change (S.x : ZMod 59) ^ 59 + (S.y : ZMod 59) ^ 59 =
      (S.z : ZMod 59) ^ 59 at h
    exact h
  have hzmod : (S.z : ZMod 59) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd S.z 59).2 hz
  rw [ZMod.pow_card, ZMod.pow_card, ZMod.pow_card, hzmod] at heqmod
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (S.x + S.y) 59).1
  simpa using heqmod

/-- Primitivity and the Fermat equation make the two legs coprime. -/
theorem state_isCoprime_x_y (S : PrimitiveSecondCaseSolution) :
    IsCoprime S.x S.y := by
  apply isCoprime_of_gcd_eq_one_of_FLT
    (n := 59) (c := -S.z) ?_ ?_
  · simpa only [Finset.gcd_insert, id_eq, ← Int.coe_gcd,
      Int.neg_gcd, ← LawfulSingleton.insert_empty_eq,
      Finset.gcd_empty] using S.primitive
  · rw [(by norm_num : Odd 59).neg_pow]
    linear_combination S.equation

variable {ζ : K}

/-- The integral root-of-unity unit selected by `ζ`. -/
noncomputable def zetaUnit (hζ : IsPrimitiveRoot ζ 59) :
    (𝓞 K)ˣ :=
  (hζ.toInteger_isPrimitiveRoot.isUnit (by norm_num : 59 ≠ 0)).unit

/-- The fixed denominator used for both members of the conjugate pair. -/
def fixedDenominator (hζ : IsPrimitiveRoot ζ 59) : 𝓞 K :=
  hζ.toInteger - 1

omit [NumberField K] [IsCyclotomicExtension {59} ℚ K] in
theorem zetaUnit_val (hζ : IsPrimitiveRoot ζ 59) :
    (zetaUnit hζ : 𝓞 K) = hζ.toInteger :=
  (hζ.toInteger_isPrimitiveRoot.isUnit
    (by norm_num : 59 ≠ 0)).unit_spec

omit [NumberField K] [IsCyclotomicExtension {59} ℚ K] in
theorem zetaUnit_isPrimitiveRoot (hζ : IsPrimitiveRoot ζ 59) :
    IsPrimitiveRoot (zetaUnit hζ) 59 :=
  hζ.toInteger_isPrimitiveRoot.isUnit_unit (by norm_num : 59 ≠ 0)

/-- The selected node at `ζ`. -/
noncomputable def plusNode (hζ : IsPrimitiveRoot ζ 59) :
    Fermat.Conservation.KummerDrain.RootNode (p := 59) (K := K) :=
  ⟨hζ.toInteger,
    hζ.toInteger_isPrimitiveRoot.mem_nthRootsFinset (by norm_num)⟩

/-- The selected node at `ζ⁻¹`. -/
noncomputable def minusNode (hζ : IsPrimitiveRoot ζ 59) :
    Fermat.Conservation.KummerDrain.RootNode (p := 59) (K := K) := by
  refine ⟨(↑((zetaUnit hζ)⁻¹) : 𝓞 K), ?_⟩
  rw [Polynomial.mem_nthRootsFinset (by norm_num : 0 < 59)]
  change (↑(((zetaUnit hζ)⁻¹) ^ 59) : 𝓞 K) = 1
  rw [(zetaUnit_isPrimitiveRoot hζ).inv.pow_eq_one]
  rfl

omit [NumberField K] [IsCyclotomicExtension {59} ℚ K] in
/-- The raw factor product attached to an integer Fermat state. -/
theorem rawFactorIdeal_product
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) :
    Ideal.span ({(S.z : 𝓞 K) ^ 59} : Set (𝓞 K)) =
      ∏ η ∈ Polynomial.nthRootsFinset 59 (1 : 𝓞 K),
        Fermat.Conservation.KummerDrain.factorIdeal
          (S.x : 𝓞 K) (S.y : 𝓞 K) η := by
  rw [← stateEquation (K := K) S]
  exact Fermat.Conservation.KummerDrain.factorIdeal_product
    hζ (by norm_num : Odd 59) (S.x : 𝓞 K) (S.y : 𝓞 K)

omit [IsCyclotomicExtension {59} ℚ K] in
/-- No raw factor at a 59th root can vanish in a nonzero Fermat state. -/
theorem stateFactor_ne_zero
    (S : PrimitiveSecondCaseSolution)
    (η : Fermat.Conservation.KummerDrain.RootNode
      (p := 59) (K := K)) :
    Fermat.Conservation.KummerDrain.factorNode
      (S.x : 𝓞 K) (S.y : 𝓞 K) η ≠ 0 := by
  intro hfactor
  have hηpow : (η : 𝓞 K) ^ 59 = 1 :=
    (Polynomial.mem_nthRootsFinset (by norm_num : 0 < 59) 1).1 η.property
  have hxy : (S.x : 𝓞 K) = -(η : 𝓞 K) * (S.y : 𝓞 K) := by
    unfold Fermat.Conservation.KummerDrain.factorNode at hfactor
    linear_combination hfactor
  have heq := stateEquation (K := K) S
  rw [hxy, mul_pow, (by norm_num : Odd 59).neg_pow, hηpow,
    neg_one_mul, neg_add_cancel] at heq
  have hzpow : (S.z : 𝓞 K) ^ 59 = 0 := heq.symm
  have hzcast : (S.z : 𝓞 K) = 0 :=
    (pow_eq_zero_iff (by norm_num : 59 ≠ 0)).mp hzpow
  apply S.z_ne_zero
  exact_mod_cast hzcast

omit [NumberField K] [IsCyclotomicExtension {59} ℚ K] in
private theorem fixedDenominator_dvd_node_sub_one
    (hζ : IsPrimitiveRoot ζ 59)
    (η : Fermat.Conservation.KummerDrain.RootNode
      (p := 59) (K := K)) :
    fixedDenominator hζ ∣ (η : 𝓞 K) - 1 := by
  have hηpow : (η : 𝓞 K) ^ 59 = 1 :=
    (Polynomial.mem_nthRootsFinset (by norm_num : 0 < 59) 1).1 η.property
  obtain ⟨i, -, hi⟩ :=
    hζ.toInteger_isPrimitiveRoot.eq_pow_of_pow_eq_one hηpow
  rw [← hi]
  exact sub_one_dvd_pow_sub_one hζ.toInteger i

private theorem fixedDenominator_dvd_stateFactor
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z)
    (η : Fermat.Conservation.KummerDrain.RootNode
      (p := 59) (K := K)) :
    fixedDenominator hζ ∣
      Fermat.Conservation.KummerDrain.factorNode
        (S.x : 𝓞 K) (S.y : 𝓞 K) η := by
  have h59sum : (59 : 𝓞 K) ∣
      (S.x : 𝓞 K) + (S.y : 𝓞 K) := by
    simpa using
      map_dvd (Int.castRingHom (𝓞 K)) (prime_dvd_x_add_y S hz)
  have hπsum : fixedDenominator hζ ∣
      (S.x : 𝓞 K) + (S.y : 𝓞 K) :=
    hζ.toInteger_sub_one_dvd_prime'.trans h59sum
  have hπtail : fixedDenominator hζ ∣
      ((η : 𝓞 K) - 1) * (S.y : 𝓞 K) :=
    dvd_mul_of_dvd_left (fixedDenominator_dvd_node_sub_one hζ η) _
  rw [show Fermat.Conservation.KummerDrain.factorNode
      (S.x : 𝓞 K) (S.y : 𝓞 K) η =
        ((S.x : 𝓞 K) + (S.y : 𝓞 K)) +
          ((η : 𝓞 K) - 1) * (S.y : 𝓞 K) by
    simp only [Fermat.Conservation.KummerDrain.factorNode]
    ring]
  exact dvd_add hπsum hπtail

/-- The normalized factor at an arbitrary root node. -/
noncomputable def normalizedFactor
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z)
    (η : Fermat.Conservation.KummerDrain.RootNode
      (p := 59) (K := K)) :
    𝓞 K :=
  (fixedDenominator_dvd_stateFactor hζ S hz η).choose

theorem normalizedFactor_spec
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z)
    (η : Fermat.Conservation.KummerDrain.RootNode
      (p := 59) (K := K)) :
    normalizedFactor hζ S hz η * fixedDenominator hζ =
      Fermat.Conservation.KummerDrain.factorNode
        (S.x : 𝓞 K) (S.y : 𝓞 K) η := by
  rw [mul_comm]
  exact (fixedDenominator_dvd_stateFactor hζ S hz η).choose_spec.symm

theorem normalizedFactor_ne_zero
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z)
    (η : Fermat.Conservation.KummerDrain.RootNode
      (p := 59) (K := K)) :
    normalizedFactor hζ S hz η ≠ 0 := by
  intro hzero
  apply stateFactor_ne_zero (K := K) S η
  rw [← normalizedFactor_spec hζ S hz η, hzero, zero_mul]

omit [NumberField K] [IsCyclotomicExtension {59} ℚ K] in
theorem fixedDenominator_ne_zero
    (hζ : IsPrimitiveRoot ζ 59) :
    fixedDenominator hζ ≠ 0 :=
  hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero (by norm_num)

private theorem fixedDenominator_dvd_z
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) :
    fixedDenominator hζ ∣ (S.z : 𝓞 K) := by
  have h59z : (59 : 𝓞 K) ∣ (S.z : 𝓞 K) := by
    simpa using map_dvd (Int.castRingHom (𝓞 K)) hz
  exact hζ.toInteger_sub_one_dvd_prime'.trans h59z

private noncomputable def normalizedZ
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) :
    𝓞 K :=
  (fixedDenominator_dvd_z hζ S hz).choose

private theorem normalizedZ_spec
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) :
    normalizedZ hζ S hz * fixedDenominator hζ = (S.z : 𝓞 K) := by
  rw [mul_comm]
  exact (fixedDenominator_dvd_z hζ S hz).choose_spec.symm

private theorem normalizedFactor_product_eq_pow
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) :
    (∏ η ∈
        (Polynomial.nthRootsFinset 59 (1 : 𝓞 K)).attach,
        normalizedFactor hζ S hz η) =
      normalizedZ hζ S hz ^ 59 := by
  have hprod :=
    Fermat.Conservation.KummerDrain.factorNode_product
      hζ (by norm_num : Odd 59) (S.x : 𝓞 K) (S.y : 𝓞 K)
  rw [← Finset.prod_attach] at hprod
  have hzprod :
      (S.z : 𝓞 K) ^ 59 =
        ∏ η ∈ (Polynomial.nthRootsFinset 59 (1 : 𝓞 K)).attach,
          Fermat.Conservation.KummerDrain.factorNode
            (S.x : 𝓞 K) (S.y : 𝓞 K) η := by
    rw [← stateEquation (K := K) S]
    exact hprod
  simp_rw [← normalizedFactor_spec hζ S hz] at hzprod
  rw [Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_attach,
    hζ.toInteger_isPrimitiveRoot.card_nthRootsFinset] at hzprod
  apply mul_right_cancel₀
    (pow_ne_zero 59 (fixedDenominator_ne_zero hζ))
  calc
    (∏ η ∈ (Polynomial.nthRootsFinset 59 (1 : 𝓞 K)).attach,
          normalizedFactor hζ S hz η) *
        fixedDenominator hζ ^ 59 =
      (S.z : 𝓞 K) ^ 59 := hzprod.symm
    _ = (normalizedZ hζ S hz * fixedDenominator hζ) ^ 59 := by
      rw [normalizedZ_spec]
    _ = normalizedZ hζ S hz ^ 59 *
        fixedDenominator hζ ^ 59 := by rw [mul_pow]

private theorem normalizedFactorIdeal_product_eq_pow
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) :
    (∏ η ∈
        (Polynomial.nthRootsFinset 59 (1 : 𝓞 K)).attach,
        Ideal.span ({normalizedFactor hζ S hz η} : Set (𝓞 K))) =
      (Ideal.span ({normalizedZ hζ S hz} : Set (𝓞 K))) ^ 59 := by
  rw [Ideal.prod_span_singleton, normalizedFactor_product_eq_pow]
  rw [← Ideal.span_singleton_pow]

private theorem normalizedFactor_sub_associated
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z)
    (η₁ η₂ : Fermat.Conservation.KummerDrain.RootNode
      (p := 59) (K := K)) (hη : η₁ ≠ η₂) :
    Associated (S.y : 𝓞 K)
      (normalizedFactor hζ S hz η₁ -
        normalizedFactor hζ S hz η₂) := by
  symm
  refine Associated.of_mul_right
    (a := normalizedFactor hζ S hz η₁ -
      normalizedFactor hζ S hz η₂)
    (b := fixedDenominator hζ)
    (c := (S.y : 𝓞 K))
    (d := (η₁ : 𝓞 K) - (η₂ : 𝓞 K)) ?_ ?_
    (fixedDenominator_ne_zero hζ)
  · apply Associated.of_eq
    rw [sub_mul, normalizedFactor_spec, normalizedFactor_spec]
    simp only [Fermat.Conservation.KummerDrain.factorNode]
    ring
  · exact
      IsPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
        hζ.toInteger_isPrimitiveRoot (by norm_num : Nat.Prime 59)
        η₁.property η₂.property (Subtype.coe_ne_coe.mpr hη)

private theorem normalizedFactors_isCoprime
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z)
    (η₁ η₂ : Fermat.Conservation.KummerDrain.RootNode
      (p := 59) (K := K)) (hη : η₁ ≠ η₂) :
    IsCoprime (normalizedFactor hζ S hz η₁)
      (normalizedFactor hζ S hz η₂) := by
  have hxy :=
    (state_isCoprime_x_y S).map (Int.castRingHom (𝓞 K))
  change IsCoprime (S.x : 𝓞 K) (S.y : 𝓞 K) at hxy
  have hqπy :
      IsCoprime
        (normalizedFactor hζ S hz η₁ * fixedDenominator hζ)
        (S.y : 𝓞 K) := by
    rw [normalizedFactor_spec]
    simpa only [Fermat.Conservation.KummerDrain.factorNode] using
      hxy.add_mul_right_left (η₁ : 𝓞 K)
  have hqy :
      IsCoprime (normalizedFactor hζ S hz η₁) (S.y : 𝓞 K) :=
    hqπy.of_mul_left_left
  have hqdiff :
      IsCoprime (normalizedFactor hζ S hz η₁)
        (normalizedFactor hζ S hz η₁ -
          normalizedFactor hζ S hz η₂) :=
    hqy.of_isCoprime_of_dvd_right
      (normalizedFactor_sub_associated hζ S hz η₁ η₂ hη).dvd'
  have hqneg :
      IsCoprime (normalizedFactor hζ S hz η₁)
        (-normalizedFactor hζ S hz η₂) := by
    convert hqdiff.add_mul_left_right (-1) using 1
    all_goals ring
  simpa only [neg_neg] using hqneg.neg_right

private theorem normalizedFactorIdeals_isCoprime
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z)
    (η₁ η₂ : Fermat.Conservation.KummerDrain.RootNode
      (p := 59) (K := K)) (hη : η₁ ≠ η₂) :
    IsCoprime
      (Ideal.span ({normalizedFactor hζ S hz η₁} : Set (𝓞 K)))
      (Ideal.span ({normalizedFactor hζ S hz η₂} : Set (𝓞 K))) := by
  rw [Ideal.isCoprime_span_singleton_iff]
  exact normalizedFactors_isCoprime hζ S hz η₁ η₂ hη

/-- The normalized factor at the selected `ζ` node. -/
noncomputable def normalizedPlusFactor
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) :
    𝓞 K :=
  normalizedFactor hζ S hz (plusNode hζ)

theorem normalizedPlusFactor_spec
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) :
    normalizedPlusFactor hζ S hz * fixedDenominator hζ =
      Fermat.Conservation.KummerDrain.factorNode
        (S.x : 𝓞 K) (S.y : 𝓞 K) hζ.toInteger := by
  simpa only [normalizedPlusFactor, plusNode] using
    normalizedFactor_spec hζ S hz (plusNode hζ)

/-- The normalized factor at the selected `ζ⁻¹` node. -/
noncomputable def normalizedMinusFactor
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) :
    𝓞 K :=
  normalizedFactor hζ S hz (minusNode hζ)

theorem normalizedMinusFactor_spec
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) :
    normalizedMinusFactor hζ S hz * fixedDenominator hζ =
      Fermat.Conservation.KummerDrain.factorNode
        (S.x : 𝓞 K) (S.y : 𝓞 K)
          (↑((zetaUnit hζ)⁻¹) : 𝓞 K) := by
  change normalizedFactor hζ S hz (minusNode hζ) *
      fixedDenominator hζ =
    Fermat.Conservation.KummerDrain.factorNode
      (S.x : 𝓞 K) (S.y : 𝓞 K) (minusNode hζ)
  exact normalizedFactor_spec hζ S hz (minusNode hζ)

theorem normalizedPlusFactor_ne_zero
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) :
    normalizedPlusFactor hζ S hz ≠ 0 := by
  intro hzero
  apply stateFactor_ne_zero (K := K) S (plusNode hζ)
  change Fermat.Conservation.KummerDrain.factorNode
    (S.x : 𝓞 K) (S.y : 𝓞 K) hζ.toInteger = 0
  rw [← normalizedPlusFactor_spec hζ S hz, hzero, zero_mul]

theorem normalizedMinusFactor_ne_zero
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) :
    normalizedMinusFactor hζ S hz ≠ 0 := by
  intro hzero
  apply stateFactor_ne_zero (K := K) S (minusNode hζ)
  change Fermat.Conservation.KummerDrain.factorNode
    (S.x : 𝓞 K) (S.y : 𝓞 K)
      (↑((zetaUnit hζ)⁻¹) : 𝓞 K) = 0
  rw [← normalizedMinusFactor_spec hζ S hz, hzero, zero_mul]

/-- The minimal missing allocation package for the selected normalized
conjugate pair.  It contains no class relation and no redundant nonzero
fields. -/
structure StateLinkedIdealPair
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) where
  plusIdeal : Ideal (𝓞 K)
  minusIdeal : Ideal (𝓞 K)
  plus_pow :
    plusIdeal ^ 59 = Ideal.span {normalizedPlusFactor hζ S hz}
  minus_pow :
    minusIdeal ^ 59 = Ideal.span {normalizedMinusFactor hζ S hz}

/-- The oriented Fermat state supplies the selected normalized pair by
extracting 59th roots from the pairwise-coprime full factor product. -/
theorem stateLinkedIdealPair_exists
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) :
    Nonempty (StateLinkedIdealPair hζ S hz) := by
  let roots :=
    (Polynomial.nthRootsFinset 59 (1 : 𝓞 K)).attach
  have hextract :
      ∀ η ∈ roots,
        ∃ I : Ideal (𝓞 K),
          Ideal.span ({normalizedFactor hζ S hz η} : Set (𝓞 K)) =
            I ^ 59 := by
    apply Finset.exists_eq_pow_of_mul_eq_pow_of_coprime
      (c := Ideal.span ({normalizedZ hζ S hz} : Set (𝓞 K)))
    · intro η₁ _ η₂ _ hη
      exact normalizedFactorIdeals_isCoprime hζ S hz η₁ η₂ hη
    · simpa only [roots] using
        normalizedFactorIdeal_product_eq_pow hζ S hz
  obtain ⟨Iplus, hIplus⟩ :=
    hextract (plusNode hζ)
      (Finset.mem_attach _ (plusNode hζ))
  obtain ⟨Iminus, hIminus⟩ :=
    hextract (minusNode hζ)
      (Finset.mem_attach _ (minusNode hζ))
  refine ⟨{
    plusIdeal := Iplus
    minusIdeal := Iminus
    plus_pow := ?_
    minus_pow := ?_ }⟩
  · simpa only [normalizedPlusFactor] using hIplus.symm
  · simpa only [normalizedMinusFactor] using hIminus.symm

/-- A canonical allocated pair selected from the statewise existence
theorem.  It carries no Vandiver relation or principalization premise. -/
noncomputable def allocatedPair
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) :
    StateLinkedIdealPair hζ S hz :=
  (stateLinkedIdealPair_exists hζ S hz).some

omit [NumberField K] [IsCyclotomicExtension {59} ℚ K] in
private theorem ideal_ne_zero_of_pow_eq_span
    {q : 𝓞 K} (hq : q ≠ 0) (I : Ideal (𝓞 K))
    (hpow : I ^ 59 = Ideal.span {q}) :
    I ≠ 0 := by
  intro hzero
  have hspan : Ideal.span {q} = 0 := by
    rw [← hpow, hzero, zero_pow (by norm_num : 59 ≠ 0)]
  change Ideal.span {q} = ⊥ at hspan
  rw [Ideal.span_singleton_eq_bot] at hspan
  exact hq hspan

theorem StateLinkedIdealPair.plusIdeal_ne_zero
    {hζ : IsPrimitiveRoot ζ 59}
    {S : PrimitiveSecondCaseSolution} {hz : (59 : ℤ) ∣ S.z}
    (pair : StateLinkedIdealPair hζ S hz) :
    pair.plusIdeal ≠ 0 :=
  ideal_ne_zero_of_pow_eq_span
    (normalizedPlusFactor_ne_zero hζ S hz)
    pair.plusIdeal pair.plus_pow

theorem StateLinkedIdealPair.minusIdeal_ne_zero
    {hζ : IsPrimitiveRoot ζ 59}
    {S : PrimitiveSecondCaseSolution} {hz : (59 : ℤ) ∣ S.z}
    (pair : StateLinkedIdealPair hζ S hz) :
    pair.minusIdeal ≠ 0 :=
  ideal_ne_zero_of_pow_eq_span
    (normalizedMinusFactor_ne_zero hζ S hz)
    pair.minusIdeal pair.minus_pow

set_option maxRecDepth 2000 in
/-- The selected pair as the exact two-node generic allocation ledger. -/
noncomputable def StateLinkedIdealPair.ledger
    {hζ : IsPrimitiveRoot ζ 59}
    {S : PrimitiveSecondCaseSolution} {hz : (59 : ℤ) ∣ S.z}
    (pair : StateLinkedIdealPair hζ S hz) :
    Fermat.Conservation.KummerDrain.AllocatedFactorLedger
      (p := 59) (K := K) (Fin 2) where
  factor := fun i =>
    if i = 0 then normalizedPlusFactor hζ S hz
    else normalizedMinusFactor hζ S hz
  rootIdeal := fun i =>
    if i = 0 then pair.plusIdeal else pair.minusIdeal
  root_ne_zero := by
    intro i
    fin_cases i
    · simpa using pair.plusIdeal_ne_zero
    · simpa using pair.minusIdeal_ne_zero
  root_pow := by
    intro i
    fin_cases i
    · simpa using pair.plus_pow
    · simpa using pair.minus_pow

@[simp]
theorem StateLinkedIdealPair.ledger_rootIdeal_zero
    {hζ : IsPrimitiveRoot ζ 59}
    {S : PrimitiveSecondCaseSolution} {hz : (59 : ℤ) ∣ S.z}
    (pair : StateLinkedIdealPair hζ S hz) :
    pair.ledger.rootIdeal 0 = pair.plusIdeal := by
  rfl

@[simp]
theorem StateLinkedIdealPair.ledger_rootIdeal_one
    {hζ : IsPrimitiveRoot ζ 59}
    {S : PrimitiveSecondCaseSolution} {hz : (59 : ℤ) ∣ S.z}
    (pair : StateLinkedIdealPair hζ S hz) :
    pair.ledger.rootIdeal 1 = pair.minusIdeal := by
  rfl

end

end Fermat.FiftyNine.Conservation.StateFactorPair
