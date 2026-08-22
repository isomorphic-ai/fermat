import Fermat.Descent.Irregular.VandiverRealNormalizationPrime

/-!
# Prime-generic normalization of Vandiver's historical state

This module writes Vandiver's historical equation

`ω^p + θ^p = η * (κ^m * ξ)^p`

in the `(ζ - 1)`-adic form consumed by the generic factor-allocation
machinery.  For real `ω` and `θ`, complex conjugation then identifies the
unique distinguished root with `1`.  Consequently the full excess power

`(ζ - 1)^((2*m - 1)*p + 1)`

divides the real factor `ω + θ`.

The argument is independent of the numerical value of the odd prime.  It
is the common core previously repeated in the exponent-587 and exponent-691
historical developments.
-/

namespace Fermat.Irregular.VandiverHistoricalStatePrime

open scoped NumberField nonZeroDivisors

open Fermat.Irregular.VandiverCriterion
open Fermat.Irregular.VandiverLemmaOne
open Fermat.Irregular.VandiverHistoricalDescent
open Fermat.Irregular.VandiverHistoricalPrime

noncomputable section

variable {K : Type} {p : ℕ} [Fact p.Prime]
  [Field K] [NumberField K] [NumberField.IsCMField K]
  [IsCyclotomicExtension {p} ℚ K]

/-- The cyclotomic unit in
`κ = (-ζ⁻¹) * (ζ - 1)²`. -/
def kappaUnit {ζ : K} (hζ : IsPrimitiveRoot ζ p) : (𝓞 K)ˣ :=
  -hζ.unit'⁻¹

omit [NumberField K] [NumberField.IsCMField K]
    [IsCyclotomicExtension {p} ℚ K] in
/-- The literal unit identity relating Vandiver's real uniformizer `κ`
to `(ζ - 1)²`. -/
lemma kappa_eq_kappaUnit_mul_sq {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) :
    kappa hζ = (kappaUnit hζ : 𝓞 K) *
      ((hζ.unit' : 𝓞 K) - 1) ^ 2 := by
  simp only [kappa, kappaUnit, Units.val_neg, neg_mul, pow_two]
  have hz : ((hζ.unit'⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
      (hζ.unit' : 𝓞 K) = 1 := by
    rw [← Units.val_mul]
    simp
  have hinv : (1 : 𝓞 K) - (hζ.unit'⁻¹ : (𝓞 K)ˣ) =
      (hζ.unit'⁻¹ : (𝓞 K)ˣ) * ((hζ.unit' : 𝓞 K) - 1) := by
    rw [mul_sub, mul_one, hz]
  rw [hinv]
  ring

omit [NumberField K] [NumberField.IsCMField K]
    [IsCyclotomicExtension {p} ℚ K] in
/-- Power form of `kappa_eq_kappaUnit_mul_sq`. -/
lemma kappa_pow_eq_kappaUnit_pow_mul {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (m : ℕ) :
    kappa hζ ^ m = ((kappaUnit hζ ^ m : (𝓞 K)ˣ) : 𝓞 K) *
      ((hζ.unit' : 𝓞 K) - 1) ^ (2 * m) := by
  rw [kappa_eq_kappaUnit_mul_sq, mul_pow, ← Units.val_pow_eq_pow_val,
    ← pow_mul]

/-- The coefficient unit obtained after rewriting a historical state in
the `(ζ - 1)`-adic normalization. -/
def historicalRegularUnit {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (s : HistoricalState hζ) : (𝓞 K)ˣ :=
  s.eta * kappaUnit hζ ^ (s.m * p)

/-- Every historical state is an input to the generic factor-allocation
construction with upstream depth `2*m - 1`. -/
lemma historicalState_regularEquation {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (s : HistoricalState hζ) :
    s.omega ^ p + s.theta ^ p = historicalRegularUnit hζ s *
      (((hζ.unit' : 𝓞 K) - 1) ^ ((2 * s.m - 1) + 1) * s.xi) ^ p := by
  have hm : 1 ≤ 2 * s.m := by
    have := s.one_lt_m
    omega
  rw [Nat.sub_add_cancel hm]
  rw [s.equation, kappa_pow_eq_kappaUnit_pow_mul]
  simp only [historicalRegularUnit, mul_pow, ← Units.val_pow_eq_pow_val,
    Units.val_mul]
  rw [← pow_mul]
  ac_rfl

/-- In every historical state, `θ` is prime to the ramified uniformizer
`ζ - 1`. -/
lemma historicalState_theta_not_dvd {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (s : HistoricalState hζ) :
    ¬ (hζ.unit' : 𝓞 K) - 1 ∣ s.theta := by
  intro htheta
  have hsum : (hζ.unit' : 𝓞 K) - 1 ∣
      s.omega ^ p + s.theta ^ p :=
    zeta_sub_one_dvd (p := p) hζ
      (historicalState_regularEquation hζ s)
  have homegaPow : (hζ.unit' : 𝓞 K) - 1 ∣ s.omega ^ p := by
    simpa using dvd_sub hsum
      (dvd_pow (n := p) htheta (Fact.out : Nat.Prime p).ne_zero)
  have homega : (hζ.unit' : 𝓞 K) - 1 ∣ s.omega :=
    hζ.zeta_sub_one_prime'.dvd_of_dvd_pow homegaPow
  exact hζ.zeta_sub_one_prime'.not_unit
    (s.coprime_omega_theta.isUnit_of_dvd' homega htheta)

/-- For an odd cyclotomic prime, a factorization with real entries assigns
the unique excess `(ζ - 1)`-power to the factor at the root `1`. -/
theorem distinguishedRoot_eq_one_of_real
    (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {x y z : 𝓞 K} {ε : (𝓞 K)ˣ} {m : ℕ}
    (e : x ^ p + y ^ p = ε *
      ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ y)
    (hxreal : NumberField.IsCMField.ringOfIntegersComplexConj K x = x)
    (hyreal : NumberField.IsCMField.ringOfIntegersComplexConj K y = y) :
    zeta_sub_one_dvd_root hp2 hζ e hy =
      (oneNthRoot :
        Polynomial.nthRootsFinset p (1 : 𝓞 K)) := by
  let π : 𝓞 K := (hζ.unit' : 𝓞 K) - 1
  let η0 := zeta_sub_one_dvd_root hp2 hζ e hy
  let q0 : 𝓞 K :=
    div_zeta_sub_one hp2 hζ e η0
  have hπ0 : π ≠ 0 :=
    hζ.unit'_coe.sub_one_ne_zero (Fact.out : Nat.Prime p).one_lt
  have hq0 : π ∣ q0 := by
    simpa only [π, q0, η0] using
      (Ideal.Quotient.eq_zero_iff_dvd
        ((hζ.unit' : 𝓞 K) - 1)
        (div_zeta_sub_one hp2 hζ e
          (zeta_sub_one_dvd_root hp2 hζ e hy))).mp
        (zeta_sub_one_dvd_root_spec hp2 hζ e hy)
  have hetaPow : (η0 : 𝓞 K) ^ p = 1 := by
    exact (Polynomial.mem_nthRootsFinset
      (Fact.out : Nat.Prime p).pos (1 : 𝓞 K)).mp η0.prop
  obtain ⟨i, hi, heta⟩ :=
    hζ.unit'_coe.eq_pow_of_pow_eq_one hetaPow
  by_cases hi0 : i = 0
  · apply Subtype.ext
    change (η0 : 𝓞 K) = 1
    rw [← heta, hi0, pow_zero]
  · have hiPos : 0 < i := Nat.pos_of_ne_zero hi0
    let j : ℕ := p - i
    have hj : j < p := by
      dsimp [j]
      omega
    let ηj : Polynomial.nthRootsFinset p (1 : 𝓞 K) :=
      ⟨(hζ.unit' : 𝓞 K) ^ j, by
        rw [Polynomial.mem_nthRootsFinset
          (Fact.out : Nat.Prime p).pos]
        rw [← pow_mul, Nat.mul_comm j p, pow_mul,
          hζ.unit'_coe.pow_eq_one, one_pow]⟩
    let qj : 𝓞 K :=
      div_zeta_sub_one hp2 hζ e ηj
    have hzpowU : hζ.unit' ^ p = 1 := by
      apply Units.ext
      apply NumberField.RingOfIntegers.ext
      change ζ ^ p = 1
      exact hζ.pow_eq_one
    have hinvpowU : (hζ.unit'⁻¹) ^ i = hζ.unit' ^ j := by
      apply mul_left_cancel (a := hζ.unit' ^ i)
      calc
        hζ.unit' ^ i * (hζ.unit'⁻¹) ^ i = 1 := by
          rw [← mul_pow]
          simp
        _ = hζ.unit' ^ (i + j) := by
          rw [show i + j = p by dsimp [j]; omega, hzpowU]
        _ = hζ.unit' ^ i * hζ.unit' ^ j := by rw [pow_add]
    have hconjζ :
        NumberField.IsCMField.ringOfIntegersComplexConj K
          (hζ.unit' : 𝓞 K) = (hζ.unit'⁻¹ : (𝓞 K)ˣ) := by
      exact congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K)
        (Fermat.Irregular.VandiverRealNormalizationPrime.unitsComplexConj_zeta
          hζ)
    let u : (𝓞 K)ˣ := -hζ.unit'⁻¹
    have hconjπ :
        NumberField.IsCMField.ringOfIntegersComplexConj K π =
          (u : 𝓞 K) * π := by
      dsimp [π, u]
      rw [map_sub, map_one, hconjζ]
      have hinv :
          (hζ.unit'⁻¹ : (𝓞 K)ˣ) * (hζ.unit' : 𝓞 K) = 1 := by
        rw [← Units.val_mul]
        simp
      simp only [neg_mul, mul_sub, hinv]
      ring
    have hconjη0 :
        NumberField.IsCMField.ringOfIntegersComplexConj K (η0 : 𝓞 K) =
          (ηj : 𝓞 K) := by
      rw [← heta, map_pow, hconjζ]
      exact congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) hinvpowU
    obtain ⟨k, hk⟩ := hq0
    have hCq0 :
        NumberField.IsCMField.ringOfIntegersComplexConj K q0 =
          NumberField.IsCMField.ringOfIntegersComplexConj K π *
            NumberField.IsCMField.ringOfIntegersComplexConj K k := by
      rw [hk, map_mul]
    have hq0mul : q0 * π = x + y * (η0 : 𝓞 K) := by
      exact div_zeta_sub_one_mul_zeta_sub_one hp2 hζ e η0
    have hconjfactor := congrArg
      (NumberField.IsCMField.ringOfIntegersComplexConj K) hq0mul
    rw [map_mul, map_add, map_mul, hxreal, hyreal,
      hconjπ, hconjη0] at hconjfactor
    have hqjmul : qj * π = x + y * (ηj : 𝓞 K) := by
      exact div_zeta_sub_one_mul_zeta_sub_one hp2 hζ e ηj
    have hqjEq : qj = π * ((u : 𝓞 K) ^ 2 *
        NumberField.IsCMField.ringOfIntegersComplexConj K k) := by
      apply mul_right_cancel₀ hπ0
      calc
        qj * π = x + y * (ηj : 𝓞 K) := hqjmul
        _ = NumberField.IsCMField.ringOfIntegersComplexConj K q0 *
            ((u : 𝓞 K) * π) := hconjfactor.symm
        _ = ((u : 𝓞 K) * π *
              NumberField.IsCMField.ringOfIntegersComplexConj K k) *
            ((u : 𝓞 K) * π) := by rw [hCq0, hconjπ]
        _ = (π * ((u : 𝓞 K) ^ 2 *
              NumberField.IsCMField.ringOfIntegersComplexConj K k)) * π := by
            ring
    have hqj : π ∣ qj := ⟨_, hqjEq⟩
    have hηeq : η0 = ηj := by
      apply div_zeta_sub_one_Injective hp2 hζ e hy
      calc
        Ideal.Quotient.mk (Ideal.span {π}) q0 = 0 :=
          (Ideal.Quotient.eq_zero_iff_dvd π q0).2 ⟨k, hk⟩
        _ = Ideal.Quotient.mk (Ideal.span {π}) qj :=
          ((Ideal.Quotient.eq_zero_iff_dvd π qj).2 hqj).symm
    have hpows : (hζ.unit' : 𝓞 K) ^ i =
        (hζ.unit' : 𝓞 K) ^ j := by
      calc
        (hζ.unit' : 𝓞 K) ^ i = (η0 : 𝓞 K) := heta
        _ = (ηj : 𝓞 K) := congrArg Subtype.val hηeq
        _ = (hζ.unit' : 𝓞 K) ^ j := rfl
    have hij : i = j := hζ.unit'_coe.pow_inj hi hj hpows
    have hpOdd : Odd p :=
      (Fact.out : Nat.Prime p).odd_of_ne_two hp2
    obtain ⟨t, ht⟩ := hpOdd
    dsimp [j] at hij
    omega

/-- In a real historical state, the distinguished factor is `ω + θ` and
carries the complete depth supplied by the source equation. -/
theorem historicalState_omega_add_theta_fullHighDivisibility
    (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    ((hζ.unit' : 𝓞 K) - 1) ^ ((2 * s.m - 1) * p + 1) ∣
      s.omega + s.theta := by
  let e := historicalState_regularEquation hζ s
  let hy := historicalState_theta_not_dvd hζ s
  have hroot :=
    distinguishedRoot_eq_one_of_real hp2 hζ e hy hs.1 hs.2.1
  have hhigh :=
    distinguishedFactor_highDivisibility hp2 hζ e hy
  rw [hroot] at hhigh
  simpa only [oneNthRoot, mul_one] using hhigh

end

end Fermat.Irregular.VandiverHistoricalStatePrime
