/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# The normalized two-factor Fermat state

An oriented integral state supplies the raw cyclotomic factorization.  The
two factors at `ζ` and `ζ⁻¹` are then divided by their common ramified
factor `ζ - 1`.  This file carries that construction through nonvanishing
and exposes the first missing allocation theorem: choosing ideal roots of
the two normalized principal ideals.

The allocation package contains neither Vandiver relation and does not
assume principalization of either selected root.
-/
import Fermat.Conservation.KummerDrain
import Fermat.FiftyNine.Conservation.FermatState
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

private theorem fixedDenominator_dvd_plusFactor
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) :
    fixedDenominator hζ ∣
      Fermat.Conservation.KummerDrain.factorNode
        (S.x : 𝓞 K) (S.y : 𝓞 K) hζ.toInteger := by
  have h59sum : (59 : 𝓞 K) ∣
      (S.x : 𝓞 K) + (S.y : 𝓞 K) := by
    simpa using
      map_dvd (Int.castRingHom (𝓞 K)) (prime_dvd_x_add_y S hz)
  have hπsum : fixedDenominator hζ ∣
      (S.x : 𝓞 K) + (S.y : 𝓞 K) :=
    hζ.toInteger_sub_one_dvd_prime'.trans h59sum
  have hπtail :
      fixedDenominator hζ ∣
        (hζ.toInteger - 1) * (S.y : 𝓞 K) :=
    dvd_mul_right _ _
  rw [show Fermat.Conservation.KummerDrain.factorNode
      (S.x : 𝓞 K) (S.y : 𝓞 K) hζ.toInteger =
        ((S.x : 𝓞 K) + (S.y : 𝓞 K)) +
          (hζ.toInteger - 1) * (S.y : 𝓞 K) by
    simp only [Fermat.Conservation.KummerDrain.factorNode]
    ring]
  exact dvd_add hπsum hπtail

omit [NumberField K] [IsCyclotomicExtension {59} ℚ K] in
private theorem fixedDenominator_dvd_inverse_sub_one
    (hζ : IsPrimitiveRoot ζ 59) :
    fixedDenominator hζ ∣
      (↑((zetaUnit hζ)⁻¹) : 𝓞 K) - 1 := by
  let u : (𝓞 K)ˣ := zetaUnit hζ
  have huval : (u : 𝓞 K) = hζ.toInteger := zetaUnit_val hζ
  refine ⟨(↑(-(u⁻¹)) : 𝓞 K), ?_⟩
  change (↑(u⁻¹) : 𝓞 K) - 1 =
    fixedDenominator hζ * (↑(-(u⁻¹)) : 𝓞 K)
  rw [show (1 : 𝓞 K) = (↑(u⁻¹) : 𝓞 K) * (u : 𝓞 K) by
    rw [← Units.val_mul]
    simp]
  simp only [fixedDenominator, ← huval]
  rw [Units.val_neg]
  ring

private theorem fixedDenominator_dvd_minusFactor
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) :
    fixedDenominator hζ ∣
      Fermat.Conservation.KummerDrain.factorNode
        (S.x : 𝓞 K) (S.y : 𝓞 K)
        (↑((zetaUnit hζ)⁻¹) : 𝓞 K) := by
  have h59sum : (59 : 𝓞 K) ∣
      (S.x : 𝓞 K) + (S.y : 𝓞 K) := by
    simpa using
      map_dvd (Int.castRingHom (𝓞 K)) (prime_dvd_x_add_y S hz)
  have hπsum : fixedDenominator hζ ∣
      (S.x : 𝓞 K) + (S.y : 𝓞 K) :=
    hζ.toInteger_sub_one_dvd_prime'.trans h59sum
  have hπtail :
      fixedDenominator hζ ∣
        ((↑((zetaUnit hζ)⁻¹) : 𝓞 K) - 1) * (S.y : 𝓞 K) :=
    dvd_mul_of_dvd_left (fixedDenominator_dvd_inverse_sub_one hζ) _
  rw [show Fermat.Conservation.KummerDrain.factorNode
      (S.x : 𝓞 K) (S.y : 𝓞 K)
          (↑((zetaUnit hζ)⁻¹) : 𝓞 K) =
        ((S.x : 𝓞 K) + (S.y : 𝓞 K)) +
          ((↑((zetaUnit hζ)⁻¹) : 𝓞 K) - 1) *
            (S.y : 𝓞 K) by
    simp only [Fermat.Conservation.KummerDrain.factorNode]
    ring]
  exact dvd_add hπsum hπtail

/-- The normalized factor at the selected `ζ` node. -/
noncomputable def normalizedPlusFactor
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) :
    𝓞 K :=
  (fixedDenominator_dvd_plusFactor hζ S hz).choose

theorem normalizedPlusFactor_spec
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) :
    normalizedPlusFactor hζ S hz * fixedDenominator hζ =
      Fermat.Conservation.KummerDrain.factorNode
        (S.x : 𝓞 K) (S.y : 𝓞 K) hζ.toInteger := by
  rw [mul_comm]
  exact (fixedDenominator_dvd_plusFactor hζ S hz).choose_spec.symm

/-- The normalized factor at the selected `ζ⁻¹` node. -/
noncomputable def normalizedMinusFactor
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) :
    𝓞 K :=
  (fixedDenominator_dvd_minusFactor hζ S hz).choose

theorem normalizedMinusFactor_spec
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) :
    normalizedMinusFactor hζ S hz * fixedDenominator hζ =
      Fermat.Conservation.KummerDrain.factorNode
        (S.x : 𝓞 K) (S.y : 𝓞 K)
          (↑((zetaUnit hζ)⁻¹) : 𝓞 K) := by
  rw [mul_comm]
  exact (fixedDenominator_dvd_minusFactor hζ S hz).choose_spec.symm

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

/--
error: Type mismatch
  rawFactorIdeal_product hζ S
has type
  Ideal.span {↑S.z ^ 59} = ∏ η ∈ Polynomial.nthRootsFinset 59 1, Conservation.KummerDrain.factorIdeal (↑S.x) (↑S.y) η
but is expected to have type
  Nonempty (StateLinkedIdealPair hζ S hz)
-/
#guard_msgs in
example (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) :
    Nonempty (StateLinkedIdealPair hζ S hz) := by
  exact rawFactorIdeal_product hζ S

end

end Fermat.FiftyNine.Conservation.StateFactorPair
