import Fermat.Irregular.VandiverHistoricalDescent
import Fermat.Irregular.CircularUnitIndex
import Fermat.ThirtySeven.DirectVandiverData
import FltRegular.NumberTheory.Cyclotomic.MoreLemmas

/-!
# Vandiver's historical descent at exponent 37

This file instantiates the source-faithful historical descent with the
concrete real-subfield invariant at exponent `37`. It first proves the
passage from a primitive rational second-case solution to Vandiver's
equation (6), using

`37 ~ (1 - ζ) ^ 36 ~ ((1 - ζ) * (1 - ζ⁻¹)) ^ 18`.

The subsequent sections expose the actual algebraic data in equations
(7b)--(10), reusing the repository's ideal-principalization interface and
leaving only the smallest unavailable real-ideal descent lemma explicit.
-/

namespace Fermat.ThirtySeven.VandiverHistorical

open scoped NumberField

open Fermat.Irregular.VandiverHistoricalDescent
open Fermat.Irregular.VandiverCriterion

noncomputable section

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {37} ℚ K]

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 37) K (by norm_num)

/-- The concrete source invariant: all three entries and the coefficient
unit lie in the maximal real subfield. The remaining equation, nonvanishing,
and pairwise-coprimality conditions are fields of `HistoricalState` itself. -/
def RealSourceAdmissible {ζ : K} (hζ : IsPrimitiveRoot ζ 37) :
    HistoricalAdmissibility hζ :=
  fun s ↦
    NumberField.IsCMField.ringOfIntegersComplexConj K s.omega = s.omega ∧
    NumberField.IsCMField.ringOfIntegersComplexConj K s.theta = s.theta ∧
    NumberField.IsCMField.ringOfIntegersComplexConj K s.xi = s.xi ∧
    NumberField.IsCMField.unitsComplexConj K s.eta = s.eta

/-- Vandiver's `κ = (1 - ζ)(1 - ζ⁻¹)` is fixed by complex
conjugation. -/
lemma ringOfIntegersComplexConj_kappa {ζ : K}
    (hζ : IsPrimitiveRoot ζ 37) :
    NumberField.IsCMField.ringOfIntegersComplexConj K (kappa hζ) =
      kappa hζ := by
  apply NumberField.RingOfIntegers.ext
  change NumberField.IsCMField.complexConj K
      (((kappa hζ : 𝓞 K) : K)) = ((kappa hζ : 𝓞 K) : K)
  simp only [kappa, map_mul, map_sub, map_one]
  change (1 - NumberField.IsCMField.complexConj K ζ) *
      (1 - NumberField.IsCMField.complexConj K ζ⁻¹) =
    (1 - ζ) * (1 - ζ⁻¹)
  rw [Fermat.Irregular.CircularUnitIndex.complexConj_zeta37_inv hζ]
  simp only [map_inv₀]
  rw [Fermat.Irregular.CircularUnitIndex.complexConj_zeta37_inv hζ, inv_inv]
  ring

/-- Complex conjugation sends the integral unit attached to `ζ` to its
inverse. -/
lemma unitsComplexConj_zeta37 {ζ : K} (hζ : IsPrimitiveRoot ζ 37) :
    NumberField.IsCMField.unitsComplexConj K hζ.unit' = (hζ.unit')⁻¹ := by
  apply Units.ext
  apply NumberField.RingOfIntegers.ext
  change NumberField.IsCMField.complexConj K ζ = ζ⁻¹
  exact Fermat.Irregular.CircularUnitIndex.complexConj_zeta37_inv hζ

/-! ## Conjugation-compatible principal generators -/

/-- The inverse of 2 modulo 37, used to make a generator real. -/
def realGeneratorHalfExponent37 : ℕ := 19

theorem two_mul_realGeneratorHalfExponent37_mod :
    2 * realGeneratorHalfExponent37 % 37 = 1 := by
  decide

/-- The explicit adjustment of a principal generator by the half-power of
its cyclotomic conjugation quotient. -/
def realAdjustedGenerator37 {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    (a : 𝓞 K) (j : ℕ) : 𝓞 K :=
  (hζ.unit' ^ (realGeneratorHalfExponent37 * j) : (𝓞 K)ˣ) * a

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K] in
lemma realAdjustedGenerator37_associated {ζ : K}
    (hζ : IsPrimitiveRoot ζ 37) (a : 𝓞 K) (j : ℕ) :
    Associated (realAdjustedGenerator37 hζ a j) a := by
  let v : (𝓞 K)ˣ := hζ.unit' ^ (realGeneratorHalfExponent37 * j)
  refine ⟨v⁻¹, ?_⟩
  change (v : 𝓞 K) * a * (v⁻¹ : (𝓞 K)ˣ) = a
  calc
    (v : 𝓞 K) * a * (v⁻¹ : (𝓞 K)ˣ) =
        a * ((v : 𝓞 K) * (v⁻¹ : (𝓞 K)ˣ)) := by ac_rfl
    _ = a := by rw [← Units.val_mul]; simp

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K] in
lemma realAdjustedGenerator37_pow_thirtySeven {ζ : K}
    (hζ : IsPrimitiveRoot ζ 37) (a : 𝓞 K) (j : ℕ) :
    realAdjustedGenerator37 hζ a j ^ 37 = a ^ 37 := by
  rw [realAdjustedGenerator37, mul_pow]
  have hzpow : hζ.unit' ^ 37 = 1 := by
    ext
    exact hζ.pow_eq_one
  have hvpow :
      (hζ.unit' ^ (realGeneratorHalfExponent37 * j)) ^ 37 = 1 := by
    rw [← pow_mul]
    rw [show (realGeneratorHalfExponent37 * j) * 37 =
      37 * (realGeneratorHalfExponent37 * j) by omega]
    rw [pow_mul, hzpow, one_pow]
  rw [← Units.val_pow_eq_pow_val, hvpow]
  simp

lemma realAdjustedGenerator37_real
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37) (a : 𝓞 K) (j : ℕ)
    (ha : NumberField.IsCMField.ringOfIntegersComplexConj K a =
      (hζ.unit' ^ j : (𝓞 K)ˣ) * a) :
    NumberField.IsCMField.ringOfIntegersComplexConj K
      (realAdjustedGenerator37 hζ a j) =
        realAdjustedGenerator37 hζ a j := by
  let k := realGeneratorHalfExponent37 * j
  let v : (𝓞 K)ˣ := hζ.unit' ^ k
  have hzpow : hζ.unit' ^ 37 = 1 := by
    ext
    exact hζ.pow_eq_one
  have hv_sq : v ^ 2 = hζ.unit' ^ j := by
    dsimp [v, k, realGeneratorHalfExponent37]
    rw [← pow_mul]
    have hexp : (19 * j) * 2 = j + 37 * j := by omega
    rw [hexp, pow_add, pow_mul, hzpow, one_pow, mul_one]
  change NumberField.IsCMField.ringOfIntegersComplexConj K
      ((v : 𝓞 K) * a) = (v : 𝓞 K) * a
  rw [map_mul]
  have hvconj : NumberField.IsCMField.ringOfIntegersComplexConj K (v : 𝓞 K) =
      (v⁻¹ : (𝓞 K)ˣ) := by
    have hvconjU :
        NumberField.IsCMField.unitsComplexConj K v = v⁻¹ := by
      dsimp [v]
      rw [map_pow, unitsComplexConj_zeta37 hζ, inv_pow]
    exact congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) hvconjU
  rw [hvconj, ha]
  rw [← mul_assoc, ← Units.val_mul, ← hv_sq]
  congr 1
  rw [pow_two, ← mul_assoc]
  simp

/-- If complex conjugation changes a principal generator by a power
ζ ^ j, multiplying the generator by ζ ^ (19 * j) makes it real.

This is the explicit odd-order normalization in the real-generator step
behind Vandiver's equations (7b)--(10a): 19 is the inverse of 2 modulo
37, so

conj (ζ ^ (19*j) * a) = ζ ^ (j-19*j) * a = ζ ^ (19*j) * a.

The resulting generator is associated to the original one, hence generates
the same principal ideal. What remains in
RealPrincipalGeneratorElimination37 is to prove that the conjugation
quotients supplied by the relevant ideal calculation have precisely this
ζ ^ j form and then to carry out Vandiver's eliminations. -/
lemma exists_real_associated_generator_of_conj_eq_zeta_pow
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37) (a : 𝓞 K) (j : ℕ)
    (ha : NumberField.IsCMField.ringOfIntegersComplexConj K a =
      (hζ.unit' ^ j : (𝓞 K)ˣ) * a) :
    ∃ b : 𝓞 K, Associated b a ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K b = b := by
  exact ⟨realAdjustedGenerator37 hζ a j,
    realAdjustedGenerator37_associated hζ a j,
    realAdjustedGenerator37_real hζ a j ha⟩

/-- A `37`th root of a real unit can be adjusted by a power of `ζ`
without changing its `37`th power so that the root itself is real. This is
the real-root normalization used implicitly between Vandiver's equations
(10) and (10b). -/
lemma exists_real_unit_root_37 {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    (a v : (𝓞 K)ˣ)
    (hv : a = v ^ 37) :
    ∃ w : (𝓞 K)ˣ, a = w ^ 37 ∧
      NumberField.IsCMField.unitsComplexConj K w = w := by
  obtain ⟨j, hj⟩ := unit_inv_conj_is_root_of_unity hζ v (by norm_num)
  let w : (𝓞 K)ˣ := v / hζ.unit' ^ j
  refine ⟨w, ?_, ?_⟩
  · dsimp [w]
    rw [div_pow, ← hv]
    have hzpow : hζ.unit' ^ 37 = 1 := by
      ext
      exact hζ.pow_eq_one
    rw [← pow_mul, show j * 37 = 37 * j by omega, pow_mul, hzpow, one_pow,
      div_one]
  · dsimp [w]
    rw [map_div, map_pow, unitsComplexConj_zeta37 hζ]
    rw [← div_eq_mul_inv] at hj
    have hmul : v = (hζ.unit' ^ j) ^ 2 *
        NumberField.IsCMField.unitsComplexConj K v :=
      div_eq_iff_eq_mul.mp hj
    rw [inv_pow, div_inv_eq_mul]
    calc
      NumberField.IsCMField.unitsComplexConj K v * hζ.unit' ^ j =
          (hζ.unit' ^ j) ^ 2 *
              NumberField.IsCMField.unitsComplexConj K v / hζ.unit' ^ j := by
        symm
        rw [pow_two]
        calc
          (hζ.unit' ^ j * hζ.unit' ^ j) *
                NumberField.IsCMField.unitsComplexConj K v / hζ.unit' ^ j =
              (NumberField.IsCMField.unitsComplexConj K v * hζ.unit' ^ j) *
                hζ.unit' ^ j / hζ.unit' ^ j := by ac_rfl
          _ = NumberField.IsCMField.unitsComplexConj K v * hζ.unit' ^ j :=
            mul_div_cancel_right _ _
      _ = v / hζ.unit' ^ j := by rw [← hmul]

/-- At exponent `37`, Vandiver's `κ^18` is associated to the rational
prime `37`. -/
lemma kappa_pow_eighteen_associated_37 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 37) :
    Associated (kappa hζ ^ 18) (37 : 𝓞 K) := by
  have hleft : Associated
      ((1 : 𝓞 K) - hζ.unit') ((hζ.unit' : 𝓞 K) - 1) := by
    refine ⟨-1, ?_⟩
    simp
  have hright : Associated
      ((1 : 𝓞 K) - (hζ.unit')⁻¹) ((hζ.unit' : 𝓞 K) - 1) := by
    refine ⟨hζ.unit', ?_⟩
    simp [sub_mul]
  have hkappa : Associated (kappa hζ)
      (((hζ.unit' : 𝓞 K) - 1) ^ 2) := by
    simpa [kappa, pow_two] using hleft.mul_mul hright
  have hkappaPow := hkappa.pow_pow (n := 18)
  rw [← pow_mul] at hkappaPow
  norm_num at hkappaPow
  have hprime := associated_zeta_sub_one_pow_prime hζ
  norm_num at hprime
  exact hkappaPow.trans hprime

/-- A primitive rational second-case solution at exponent `37` gives
Vandiver's equation (6) with `m = 18`. This discharges the first abstract
boundary of `VandiverHistoricalDescent` for the concrete real invariant. -/
theorem secondCaseStartsHistoricalDescent_37 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 37) :
    SecondCaseStartsHistoricalDescent hζ (RealSourceAdmissible hζ) := by
  intro x y z hgcd hz hz0 e
  have hx : x ≠ 0 := by
    intro hx0
    have hyz : y = z := (show Odd 37 by norm_num).pow_injective (by simpa [hx0] using e)
    have h37one : (37 : ℤ) ∣ 1 := by
      rw [← hgcd, Finset.dvd_gcd_iff]
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · rw [hx0]
        exact dvd_zero _
      · rw [hyz]
        exact hz
      · exact hz
    norm_num at h37one
  have hy : y ≠ 0 := by
    intro hy0
    have hxz : x = z := (show Odd 37 by norm_num).pow_injective (by simpa [hy0] using e)
    have h37one : (37 : ℤ) ∣ 1 := by
      rw [← hgcd, Finset.dvd_gcd_iff]
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · rw [hxz]
        exact hz
      · rw [hy0]
        exact dvd_zero _
      · exact hz
    norm_num at h37one
  obtain ⟨hxy, hyz, hxz⟩ :=
    Fermat.pairwiseCoprime_of_primitive_solution (by norm_num) hx hy hz0 hgcd e
  obtain ⟨t, rfl⟩ := hz
  have ht0 : t ≠ 0 := by
    intro ht
    apply hz0
    simp [ht]
  obtain ⟨u, hu⟩ := kappa_pow_eighteen_associated_37 hζ
  have hkappa0 : kappa hζ ^ 18 ≠ 0 :=
    (kappa_pow_eighteen_associated_37 hζ).ne_zero_iff.mpr (by norm_num)
  have huReal :
      NumberField.IsCMField.ringOfIntegersComplexConj K (u : 𝓞 K) = u := by
    have hconj := congrArg
      (NumberField.IsCMField.ringOfIntegersComplexConj K) hu
    simp only [map_mul, map_pow, ringOfIntegersComplexConj_kappa hζ,
      map_ofNat] at hconj
    exact mul_left_cancel₀ hkappa0 (hconj.trans hu.symm)
  let ξ : 𝓞 K := (u : 𝓞 K) * (t : 𝓞 K)
  have hyt : IsCoprime (y : 𝓞 K) (t : 𝓞 K) := by
    have hcast := hyz.intCast (R := 𝓞 K)
    have hcast' : IsCoprime (y : 𝓞 K) (((37 : ℤ) : 𝓞 K) * (t : 𝓞 K)) := by
      simpa only [Int.cast_mul] using hcast
    exact hcast'.of_mul_right_right
  have hxt : IsCoprime (x : 𝓞 K) (t : 𝓞 K) := by
    have hcast := hxz.intCast (R := 𝓞 K)
    have hcast' : IsCoprime (x : 𝓞 K) (((37 : ℤ) : 𝓞 K) * (t : 𝓞 K)) := by
      simpa only [Int.cast_mul] using hcast
    exact hcast'.of_mul_right_right
  let s : HistoricalState hζ :=
    { omega := x
      theta := y
      xi := ξ
      eta := 1
      m := 18
      one_lt_m := by norm_num
      xi_ne_zero := by
        dsimp [ξ]
        exact mul_ne_zero u.isUnit.ne_zero (Int.cast_ne_zero.mpr ht0)
      coprime_omega_theta := hxy.intCast
      coprime_theta_xi := by
        dsimp [ξ]
        exact (isCoprime_mul_unit_left_right u.isUnit (y : 𝓞 K) (t : 𝓞 K)).mpr hyt
      coprime_omega_xi := by
        dsimp [ξ]
        exact (isCoprime_mul_unit_left_right u.isUnit (x : 𝓞 K) (t : 𝓞 K)).mpr hxt
      equation := by
        simp only [Units.val_one, one_mul]
        calc
          (x : 𝓞 K) ^ 37 + (y : 𝓞 K) ^ 37 =
              ((((37 : ℤ) * t : ℤ) : 𝓞 K)) ^ 37 := by exact_mod_cast e
          _ = ((37 : 𝓞 K) * (t : 𝓞 K)) ^ 37 := by norm_num
          _ = (kappa hζ ^ 18 * ((u : 𝓞 K) * (t : 𝓞 K))) ^ 37 := by
            congr 1
            rw [← mul_assoc, hu]
          _ = (kappa hζ ^ 18 * ξ) ^ 37 := rfl }
  refine ⟨s, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [s]
    simp
  · dsimp [s]
    simp
  · dsimp [s, ξ]
    simp [huReal]
  · dsimp [s]
    simp

/-! ## The algebraic passage from equation (10) to equation (10b) -/

/-- The actual finite support of the distinct prime-ideal factors of the
principal ideal `(x)`. -/
def primeIdealFactorSupport37 (x : 𝓞 K) : Finset (Ideal (𝓞 K)) :=
  (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {x})).toFinset

/-- The concrete output of Vandiver's ideal calculation through equation
(10a), before applying Lemma 2. It records the weighted Fermat equation,
the high-depth quotient-unit congruence, the real and coprimality invariants,
and the strict deletion of a prime-ideal factor from `ξ`.

The theorem below turns exactly this data into the abstract
`EquationSevenToTenData`; in particular, neither the Kummer conclusion nor
the rescaling to equation (10b) is assumed here. -/
structure WeightedReductionData37 {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    (s : HistoricalState hζ) where
  x : 𝓞 K
  y : 𝓞 K
  z : 𝓞 K
  epsilon₁ : (𝓞 K)ˣ
  epsilon₂ : (𝓞 K)ˣ
  epsilon₃ : (𝓞 K)ˣ
  rationalBase : ℤ
  highCongruence :
    ((1 : 𝓞 K) - hζ.unit') ^ ((2 * s.m - 2) * 37) ∣
      (((epsilon₁ / epsilon₂ : (𝓞 K)ˣ) : 𝓞 K) -
        (rationalBase : 𝓞 K) ^ 37)
  weightedEquation :
    epsilon₁ * x ^ 37 + epsilon₂ * y ^ 37 =
      epsilon₃ * (kappa hζ ^ (2 * s.m - 1) * z) ^ 37
  z_ne_zero : z ≠ 0
  coprime_xy : IsCoprime x y
  coprime_yz : IsCoprime y z
  coprime_xz : IsCoprime x z
  real_x : NumberField.IsCMField.ringOfIntegersComplexConj K x = x
  real_y : NumberField.IsCMField.ringOfIntegersComplexConj K y = y
  real_z : NumberField.IsCMField.ringOfIntegersComplexConj K z = z
  real_eta : NumberField.IsCMField.unitsComplexConj K (epsilon₃ / epsilon₂) =
    epsilon₃ / epsilon₂
  factorSupport_strict : primeIdealFactorSupport37 z ⊂ primeIdealFactorSupport37 s.xi

/-- The output of Vandiver's elimination before its three principal
generators have been made literally real.

Compared with WeightedReductionData37, this structure asks for the exact
cyclotomic conjugation quotients of x, y, and z. The theorem
weightedReductionData_of_conjugationPowers37 below performs the explicit
ζ^(19*j) adjustment and proves that it preserves the weighted equation,
coprimality, nonvanishing, and the strict prime-support descent. -/
structure ConjugationPowerReductionData37 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 37) (s : HistoricalState hζ) where
  x : 𝓞 K
  y : 𝓞 K
  z : 𝓞 K
  epsilon₁ : (𝓞 K)ˣ
  epsilon₂ : (𝓞 K)ˣ
  epsilon₃ : (𝓞 K)ˣ
  rationalBase : ℤ
  highCongruence :
    ((1 : 𝓞 K) - hζ.unit') ^ ((2 * s.m - 2) * 37) ∣
      (((epsilon₁ / epsilon₂ : (𝓞 K)ˣ) : 𝓞 K) -
        (rationalBase : 𝓞 K) ^ 37)
  weightedEquation :
    epsilon₁ * x ^ 37 + epsilon₂ * y ^ 37 =
      epsilon₃ * (kappa hζ ^ (2 * s.m - 1) * z) ^ 37
  z_ne_zero : z ≠ 0
  coprime_xy : IsCoprime x y
  coprime_yz : IsCoprime y z
  coprime_xz : IsCoprime x z
  conjugationExponent_x : ℕ
  conjugationExponent_y : ℕ
  conjugationExponent_z : ℕ
  conjugation_x :
    NumberField.IsCMField.ringOfIntegersComplexConj K x =
      (hζ.unit' ^ conjugationExponent_x : (𝓞 K)ˣ) * x
  conjugation_y :
    NumberField.IsCMField.ringOfIntegersComplexConj K y =
      (hζ.unit' ^ conjugationExponent_y : (𝓞 K)ˣ) * y
  conjugation_z :
    NumberField.IsCMField.ringOfIntegersComplexConj K z =
      (hζ.unit' ^ conjugationExponent_z : (𝓞 K)ˣ) * z
  real_eta : NumberField.IsCMField.unitsComplexConj K (epsilon₃ / epsilon₂) =
    epsilon₃ / epsilon₂
  factorSupport_strict : primeIdealFactorSupport37 z ⊂ primeIdealFactorSupport37 s.xi

/-- Normalize all three weighted generators by the explicit half powers of
their conjugation quotients. Since those multipliers are 37th roots of
unity, every 37th power in Vandiver's equation is unchanged. -/
noncomputable def weightedReductionData_of_conjugationPowers37
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37) {s : HistoricalState hζ}
    (d : ConjugationPowerReductionData37 hζ s) :
    WeightedReductionData37 hζ s where
  x := realAdjustedGenerator37 hζ d.x d.conjugationExponent_x
  y := realAdjustedGenerator37 hζ d.y d.conjugationExponent_y
  z := realAdjustedGenerator37 hζ d.z d.conjugationExponent_z
  epsilon₁ := d.epsilon₁
  epsilon₂ := d.epsilon₂
  epsilon₃ := d.epsilon₃
  rationalBase := d.rationalBase
  highCongruence := d.highCongruence
  weightedEquation := by
    simpa only [mul_pow, realAdjustedGenerator37_pow_thirtySeven] using
      d.weightedEquation
  z_ne_zero := by
    dsimp [realAdjustedGenerator37]
    exact mul_ne_zero
      (hζ.unit' ^ (realGeneratorHalfExponent37 *
        d.conjugationExponent_z)).isUnit.ne_zero d.z_ne_zero
  coprime_xy :=
    (isCoprime_mul_unit_left_left
      (hζ.unit' ^ (realGeneratorHalfExponent37 * d.conjugationExponent_x)).isUnit
      d.x
      (realAdjustedGenerator37 hζ d.y d.conjugationExponent_y)).mpr
      ((isCoprime_mul_unit_left_right
        (hζ.unit' ^ (realGeneratorHalfExponent37 * d.conjugationExponent_y)).isUnit
        d.x d.y).mpr d.coprime_xy)
  coprime_yz :=
    (isCoprime_mul_unit_left_left
      (hζ.unit' ^ (realGeneratorHalfExponent37 * d.conjugationExponent_y)).isUnit
      d.y
      (realAdjustedGenerator37 hζ d.z d.conjugationExponent_z)).mpr
      ((isCoprime_mul_unit_left_right
        (hζ.unit' ^ (realGeneratorHalfExponent37 * d.conjugationExponent_z)).isUnit
        d.y d.z).mpr d.coprime_yz)
  coprime_xz :=
    (isCoprime_mul_unit_left_left
      (hζ.unit' ^ (realGeneratorHalfExponent37 * d.conjugationExponent_x)).isUnit
      d.x
      (realAdjustedGenerator37 hζ d.z d.conjugationExponent_z)).mpr
      ((isCoprime_mul_unit_left_right
        (hζ.unit' ^ (realGeneratorHalfExponent37 * d.conjugationExponent_z)).isUnit
        d.x d.z).mpr d.coprime_xz)
  real_x :=
    realAdjustedGenerator37_real hζ d.x d.conjugationExponent_x d.conjugation_x
  real_y :=
    realAdjustedGenerator37_real hζ d.y d.conjugationExponent_y d.conjugation_y
  real_z :=
    realAdjustedGenerator37_real hζ d.z d.conjugationExponent_z d.conjugation_z
  real_eta := d.real_eta
  factorSupport_strict := by
    have hsupp :
        primeIdealFactorSupport37
            (realAdjustedGenerator37 hζ d.z d.conjugationExponent_z) =
          primeIdealFactorSupport37 d.z := by
      unfold primeIdealFactorSupport37
      rw [Ideal.span_singleton_eq_span_singleton.mpr
        (realAdjustedGenerator37_associated hζ d.z d.conjugationExponent_z)]
    rw [hsupp]
    exact d.factorSupport_strict

private noncomputable def adjustedRoot37 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 37) (a v : (𝓞 K)ˣ)
    (hv : a = v ^ 37) : (𝓞 K)ˣ :=
  (exists_real_unit_root_37 hζ a v hv).choose

private lemma adjustedRoot37_pow {ζ : K}
    (hζ : IsPrimitiveRoot ζ 37) (a v : (𝓞 K)ˣ)
    (hv : a = v ^ 37) :
    a = adjustedRoot37 hζ a v hv ^ 37 :=
  (exists_real_unit_root_37 hζ a v hv).choose_spec.1

private lemma adjustedRoot37_real {ζ : K}
    (hζ : IsPrimitiveRoot ζ 37) (a v : (𝓞 K)ˣ)
    (hv : a = v ^ 37) :
    NumberField.IsCMField.unitsComplexConj K (adjustedRoot37 hζ a v hv) =
      adjustedRoot37 hζ a v hv :=
  (exists_real_unit_root_37 hζ a v hv).choose_spec.2

private noncomputable def weightedNextState37 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 37) {s : HistoricalState hζ}
    (d : WeightedReductionData37 hζ s)
    (v : (𝓞 K)ˣ) (hv : d.epsilon₁ / d.epsilon₂ = v ^ 37) :
    HistoricalState hζ :=
  let w := adjustedRoot37 hζ (d.epsilon₁ / d.epsilon₂) v hv
  { omega := w * d.x
    theta := d.y
    xi := d.z
    eta := d.epsilon₃ / d.epsilon₂
    m := 2 * s.m - 1
    one_lt_m := by
      have hm := s.one_lt_m
      omega
    xi_ne_zero := d.z_ne_zero
    coprime_omega_theta :=
      (isCoprime_mul_unit_left_left w.isUnit d.x d.y).mpr d.coprime_xy
    coprime_theta_xi := d.coprime_yz
    coprime_omega_xi :=
      (isCoprime_mul_unit_left_left w.isUnit d.x d.z).mpr d.coprime_xz
    equation := by
      rw [mul_pow, ← Units.val_pow_eq_pow_val,
        ← adjustedRoot37_pow hζ (d.epsilon₁ / d.epsilon₂) v hv,
        ← mul_right_inj' d.epsilon₂.isUnit.ne_zero, mul_add, ← mul_assoc,
        ← Units.val_mul, mul_div_cancel, ← mul_assoc,
        ← Units.val_mul, mul_div_cancel]
      exact d.weightedEquation }

private lemma weightedNextState37_admissible {ζ : K}
    (hζ : IsPrimitiveRoot ζ 37) {s : HistoricalState hζ}
    (d : WeightedReductionData37 hζ s)
    (v : (𝓞 K)ˣ) (hv : d.epsilon₁ / d.epsilon₂ = v ^ 37) :
    RealSourceAdmissible hζ (weightedNextState37 hζ d v hv) := by
  let w := adjustedRoot37 hζ (d.epsilon₁ / d.epsilon₂) v hv
  have hwUnits : NumberField.IsCMField.unitsComplexConj K w = w :=
    adjustedRoot37_real hζ (d.epsilon₁ / d.epsilon₂) v hv
  have hw : NumberField.IsCMField.ringOfIntegersComplexConj K (w : 𝓞 K) = w := by
    have := congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) hwUnits
    exact this
  refine ⟨?_, d.real_y, d.real_z, d.real_eta⟩
  change NumberField.IsCMField.ringOfIntegersComplexConj K
      ((w : 𝓞 K) * d.x) = (w : 𝓞 K) * d.x
  rw [map_mul, hw, d.real_x]

/-- Equations (10) and (10a) imply the abstract historical reduction data.
The proof performs the nontrivial source step after Lemma 2: it normalizes a
`37`th root to be real, absorbs it into the first summand, divides out the
second coefficient unit, and verifies every invariant of equation (10b). -/
noncomputable def equationSevenToTenData_of_weighted37 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 37) {s : HistoricalState hζ}
    (d : WeightedReductionData37 hζ s) :
    EquationSevenToTenData hζ (RealSourceAdmissible hζ) s where
  quotientUnit := d.epsilon₁ / d.epsilon₂
  rationalBase := d.rationalBase
  highCongruence := d.highCongruence
  nextState := weightedNextState37 hζ d
  next_admissible := weightedNextState37_admissible hζ d
  next_exponent := by intros; rfl
  factorCount_decreases := by
    intro v hv
    exact Finset.card_lt_card d.factorSupport_strict

/-! ## The remaining real-principal-generator seam -/

/-- The one ideal-theoretic lemma still absent from Mathlib for Vandiver's
historical calculation.

`RelevantIdealQuotientsPrincipal` supplies the principal ideals used in
(7b). What is additionally needed is to show that the conjugation quotient
of each selected generator is a power of `ζ`. The explicit
`ζ^(19*j)` normalization above then makes all three generators real
without changing their 37th powers. Substituting those generators into (8),
subtracting the `a` and `-a` equations as in (9a), and eliminating
`ω² + θ²` and `ωθ` in (10a) must produce the explicit
`ConjugationPowerReductionData37` above.

This boundary is deliberately below the level of the descent conclusion:
the high local congruence, weighted equation, exact conjugation quotients,
coprimality, and the strict inclusion of prime-ideal supports are all
concrete fields which a future proof must construct. Making the generators
real, preserving their equation and supports, the Kummer step, real-root
normalization, equation (10b), invariant preservation, and infinite descent
are not part of this hypothesis. -/
def RealPrincipalGeneratorElimination37 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 37) : Prop :=
  RelevantIdealQuotientsPrincipal (K := K) (p := 37) (by norm_num) →
    ∀ s : HistoricalState hζ, RealSourceAdmissible hζ s →
      Nonempty (ConjugationPowerReductionData37 hζ s)

/-- The concrete real-generator elimination supplies the full historical
reduction relation required by the abstract well-founded descent. -/
theorem equationsSevenToTenReduction_37
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    (hprincipal : RelevantIdealQuotientsPrincipal (K := K) (p := 37) (by norm_num))
    (heliminate : RealPrincipalGeneratorElimination37 hζ) :
    EquationsSevenToTenReduction hζ (RealSourceAdmissible hζ) := by
  intro s hs
  exact (heliminate hprincipal s hs).map fun d ↦
    equationSevenToTenData_of_weighted37 hζ
      (weightedReductionData_of_conjugationPowers37 hζ d)

/-- The exponent-`37` historical second case, conditional only on the exact
deep unit conclusion, relevant principalization, and the remaining
conjugation-compatible real-generator elimination. -/
theorem secondCaseExcluded_37_of_historical
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    (hprincipal : RelevantIdealQuotientsPrincipal (K := K) (p := 37) (by norm_num))
    (heliminate : RealPrincipalGeneratorElimination37 hζ)
    (hkummer : KummerUnitPowerConclusion K 37) :
    Fermat.SecondCaseExcluded 37 :=
  secondCaseExcluded_of_historical_descent (by norm_num) hζ
    (RealSourceAdmissible hζ) (secondCaseStartsHistoricalDescent_37 hζ)
    (equationsSevenToTenReduction_37 hζ hprincipal heliminate) hkummer

/-- Assemble the exact source statement of Vandiver's Lemma 2 with the
directly checked exponent-`37` Bernoulli cube data. No semiprimary deepening
hypothesis is used on this historical route. -/
theorem secondCaseExcluded_37_of_vandiverLemmaTwo
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    (hprincipal : RelevantIdealQuotientsPrincipal (K := K) (p := 37) (by norm_num))
    (heliminate : RealPrincipalGeneratorElimination37 hζ)
    (hLemmaTwo : Fermat.Irregular.VandiverUnitLemma.VandiverLemmaTwo K 37) :
    Fermat.SecondCaseExcluded 37 :=
  secondCaseExcluded_37_of_historical hζ hprincipal heliminate
    (Fermat.Irregular.VandiverUnitLemma.kummerUnitPowerConclusion_of_lemmaTwo
      (by norm_num) hLemmaTwo
      Fermat.ThirtySeven.DirectVandiverData.bernoulliCubeCondition_thirtySeven_direct)

end

end Fermat.ThirtySeven.VandiverHistorical
