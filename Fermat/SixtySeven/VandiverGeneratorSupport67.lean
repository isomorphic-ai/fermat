import Fermat.SixtySeven.VandiverHistoricalSupport

/-!
# Generator coprimality and support in Vandiver's exponent-67 reduction

This file isolates the elementary commutative-algebra facts needed when the
four generators from equation (8) and the generator from equation (8a) are
assembled into the three generators occurring in equation (10).

The equation-level lemmas deliberately use only the displayed linear
equations, the source coprimality of `ω` and `θ`, and the fact that all
differences of distinct 67th roots are associated to the standard
uniformizer.  The final packaging theorem then proves the three pairwise
coprimalities for

`x = r₁ * r₋₁`, `y = r₂ * r₋₂`, and `z = r₀ ^ 2`.

The last section records that multiplying a generator by a unit, and taking a
nonzero power, does not change the finite support of its principal ideal.
-/

namespace Fermat.SixtySeven.VandiverHistorical

open scoped NumberField nonZeroDivisors

noncomputable section

section ElementaryCoprimality

variable {R : Type*} [CommRing R]

/-- A linear factor `ω + t*θ` which is a coefficient times a positive power
of `r` forces `r` to be coprime to `θ`, provided `ω` and `θ` are coprime.

No property of the coefficient is needed: coprimality of the whole product
implies coprimality of each factor. -/
lemma isCoprime_linearRoot_theta67
    {ω θ t c r : R}
    (hωθ : IsCoprime ω θ)
    (heq : ω + t * θ = c * r ^ 67) :
    IsCoprime r θ := by
  have hlinear : IsCoprime (ω + t * θ) θ :=
    hωθ.add_mul_right_left t
  rw [heq] at hlinear
  exact (IsCoprime.pow_left_iff (by norm_num : 0 < 67)).mp
    hlinear.of_mul_left_right

/-- Two distinct linear equations whose coefficients and root difference are
all associated to the same nonzero uniformizer have coprime 67th-power
generators.

After replacing the three associated elements by a uniformizer times a unit,
subtracting the equations and cancelling the uniformizer gives

`v*θ = u₁*r₁^67 - u₂*r₂^67`.

The source coprimality of `ω` and `θ` first gives `IsCoprime r₁ θ`; the last
identity then gives `IsCoprime r₁ r₂`. -/
theorem coprime_generators_of_distinct_linearEquations67
    [IsDomain R]
    {ω θ π t₁ t₂ c₁ c₂ r₁ r₂ : R}
    (hπ0 : π ≠ 0)
    (hωθ : IsCoprime ω θ)
    (hc₁ : Associated c₁ π)
    (hc₂ : Associated c₂ π)
    (ht : Associated (t₁ - t₂) π)
    (heq₁ : ω + t₁ * θ = c₁ * r₁ ^ 67)
    (heq₂ : ω + t₂ * θ = c₂ * r₂ ^ 67) :
    IsCoprime r₁ r₂ := by
  obtain ⟨u₁, hu₁⟩ := hc₁.symm
  obtain ⟨u₂, hu₂⟩ := hc₂.symm
  obtain ⟨v, hv⟩ := ht.symm
  have heq₁' :
      ω + t₁ * θ = π * (u₁ : R) * r₁ ^ 67 := by
    calc
      ω + t₁ * θ = c₁ * r₁ ^ 67 := heq₁
      _ = π * (u₁ : R) * r₁ ^ 67 := by rw [hu₁]
  have heq₂' :
      ω + t₂ * θ = π * (u₂ : R) * r₂ ^ 67 := by
    calc
      ω + t₂ * θ = c₂ * r₂ ^ 67 := heq₂
      _ = π * (u₂ : R) * r₂ ^ 67 := by rw [hu₂]
  have hdiff :
      (v : R) * θ =
        (u₁ : R) * r₁ ^ 67 - (u₂ : R) * r₂ ^ 67 := by
    apply mul_left_cancel₀ hπ0
    calc
      π * ((v : R) * θ) = (t₁ - t₂) * θ := by rw [← hv]; ring
      _ = (ω + t₁ * θ) - (ω + t₂ * θ) := by ring
      _ = (π * (u₁ : R) * r₁ ^ 67) -
          (π * (u₂ : R) * r₂ ^ 67) := by rw [heq₁', heq₂']
      _ = π * ((u₁ : R) * r₁ ^ 67 -
          (u₂ : R) * r₂ ^ 67) := by ring
  have hr₁θ : IsCoprime r₁ θ :=
    isCoprime_linearRoot_theta67 hωθ heq₁
  have hcop :
      IsCoprime r₁
        ((u₁ : R) * r₁ ^ 67 - (u₂ : R) * r₂ ^ 67) := by
    rw [← hdiff]
    exact (isCoprime_mul_unit_left_right v.isUnit r₁ θ).mpr hr₁θ
  have hcop' : IsCoprime r₁ ((u₂ : R) * r₂ ^ 67) := by
    rw [show (u₁ : R) * r₁ ^ 67 =
      r₁ * ((u₁ : R) * r₁ ^ 66) by ring] at hcop
    exact IsCoprime.mul_sub_left_right_iff.mp hcop
  have hpow : IsCoprime r₁ (r₂ ^ 67) :=
    (isCoprime_mul_unit_left_right u₂.isUnit r₁ (r₂ ^ 67)).mp hcop'
  exact (IsCoprime.pow_right_iff (by norm_num : 0 < 67)).mp hpow

/-- In a one-dimensional domain, a prime element is coprime to every element
it does not divide.  This is the ideal-theoretic replacement for the usual
gcd-domain lemma: the nonzero principal prime ideal is maximal. -/
theorem isCoprime_prime_of_not_dvd_dimensionOne67
    [IsDomain R] [Ring.DimensionLEOne R]
    {π r : R} (hπ : Prime π) (hr : ¬ π ∣ r) :
    IsCoprime π r := by
  apply (Ideal.sup_eq_top_iff_isCoprime π r).mp
  by_contra hsup
  have hPprime : (Ideal.span ({π} : Set R)).IsPrime :=
    (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  have hPbot : Ideal.span ({π} : Set R) ≠ ⊥ := by
    intro hbot
    apply hπ.ne_zero
    have hmem : π ∈ (⊥ : Ideal R) := by
      rw [← hbot]
      exact Ideal.mem_span_singleton_self π
    simpa only [Ideal.mem_bot] using hmem
  have hPmax : (Ideal.span ({π} : Set R)).IsMaximal :=
    hPprime.isMaximal hPbot
  have heq :
      Ideal.span ({π} : Set R) =
        Ideal.span ({π} : Set R) ⊔ Ideal.span ({r} : Set R) :=
    hPmax.eq_of_le hsup le_sup_left
  apply hr
  rw [← Ideal.mem_span_singleton]
  have hle :
      Ideal.span ({r} : Set R) ≤ Ideal.span ({π} : Set R) := by
    rw [heq]
    exact le_sup_right
  exact hle (Ideal.mem_span_singleton_self r)

/-- A generator from a nonzero linear root is coprime to the generator from
the zero-root equation.

The hypothesis `π ∤ r` makes `r` coprime to the uniformizer.  Association of
`t-1` with `π`, together with `IsCoprime r θ`, makes `r` coprime to
`(t-1)*θ`.  Since

`ω + θ = (ω + t*θ) - (t-1)*θ`,

and the first term is divisible by `r`, the zero-root equation finishes the
argument. -/
theorem coprime_generator_zero_of_linearEquations67
    [IsDomain R] [Ring.DimensionLEOne R]
    {ω θ π t c r d r₀ : R}
    (hπ : Prime π)
    (hrπ : ¬ π ∣ r)
    (hωθ : IsCoprime ω θ)
    (hc : Associated c π)
    (ht : Associated (t - 1) π)
    (heq : ω + t * θ = c * r ^ 67)
    (hzero : ω + θ = d * r₀ ^ 67) :
    IsCoprime r r₀ := by
  obtain ⟨u, hu⟩ := hc.symm
  have heq' : ω + t * θ = π * (u : R) * r ^ 67 := by
    calc
      ω + t * θ = c * r ^ 67 := heq
      _ = π * (u : R) * r ^ 67 := by rw [hu]
  have hπr : IsCoprime π r :=
    isCoprime_prime_of_not_dvd_dimensionOne67 hπ hrπ
  obtain ⟨v, hv⟩ := ht.symm
  have hrt : IsCoprime r (t - 1) := by
    rw [← hv]
    exact (isCoprime_mul_unit_right_right v.isUnit r π).mpr hπr.symm
  have hrθ : IsCoprime r θ :=
    isCoprime_linearRoot_theta67 hωθ heq
  have hrprod : IsCoprime r ((t - 1) * θ) :=
    hrt.mul_right hrθ
  have hrewrite :
      ω + θ =
        r * (π * (u : R) * r ^ 66) - (t - 1) * θ := by
    calc
      ω + θ = (ω + t * θ) - (t - 1) * θ := by ring
      _ = (π * (u : R) * r ^ 67) - (t - 1) * θ := by rw [heq']
      _ = r * (π * (u : R) * r ^ 66) - (t - 1) * θ := by ring
  have hrsum : IsCoprime r (ω + θ) := by
    rw [hrewrite]
    exact IsCoprime.mul_sub_left_right_iff.mpr hrprod
  rw [hzero] at hrsum
  exact (IsCoprime.pow_right_iff (by norm_num : 0 < 67)).mp
    hrsum.of_mul_right_right

/-- Package the eight atomic generator coprimalities into the exact
nonvanishing and pairwise-coprimality fields needed for
`ConjugationPowerReductionData67` with

`x = r₁*r₋₁`, `y = r₂*r₋₂`, and `z = r₀^2`. -/
theorem products_and_square_coprimality67
    [IsDomain R]
    {r₁ rminus₁ r₂ rminus₂ r₀ : R}
    (hr₀ : r₀ ≠ 0)
    (h₁₂ : IsCoprime r₁ r₂)
    (h₁minus₂ : IsCoprime r₁ rminus₂)
    (hminus₁₂ : IsCoprime rminus₁ r₂)
    (hminus₁minus₂ : IsCoprime rminus₁ rminus₂)
    (h₁₀ : IsCoprime r₁ r₀)
    (hminus₁₀ : IsCoprime rminus₁ r₀)
    (h₂₀ : IsCoprime r₂ r₀)
    (hminus₂₀ : IsCoprime rminus₂ r₀) :
    r₀ ^ 2 ≠ 0 ∧
      IsCoprime (r₁ * rminus₁) (r₂ * rminus₂) ∧
      IsCoprime (r₂ * rminus₂) (r₀ ^ 2) ∧
      IsCoprime (r₁ * rminus₁) (r₀ ^ 2) := by
  refine ⟨pow_ne_zero 2 hr₀, ?_, ?_, ?_⟩
  · exact (h₁₂.mul_right h₁minus₂).mul_left
      (hminus₁₂.mul_right hminus₁minus₂)
  · exact (h₂₀.mul_left hminus₂₀).pow_right
  · exact (h₁₀.mul_left hminus₁₀).pow_right

end ElementaryCoprimality

section CyclotomicSpecialization

variable {K : Type} [Field K] [NumberField K]

local instance : Fact (Nat.Prime 67) := ⟨by norm_num⟩

/-- Distinct powers, with exponents in the standard range, differ by an
associate of the cyclotomic uniformizer.  This is the convenient
element-level form of pairwise association for the finite set of 67th roots
of unity. -/
lemma associated_zetaPowers_sub67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    {a b : ℕ} (ha : a < 67) (hb : b < 67) (hab : a ≠ b) :
    Associated
      ((hζ.unit' : 𝓞 K) ^ a - (hζ.unit' : 𝓞 K) ^ b)
      ((hζ.unit' : 𝓞 K) - 1) := by
  have hroot (j : ℕ) :
      (hζ.unit' : 𝓞 K) ^ j ∈
        Polynomial.nthRootsFinset 67 (1 : 𝓞 K) := by
    rw [Polynomial.mem_nthRootsFinset (by norm_num : 0 < 67)]
    rw [← pow_mul, Nat.mul_comm j 67, pow_mul,
      hζ.unit'_coe.pow_eq_one, one_pow]
  have hne :
      (hζ.unit' : 𝓞 K) ^ a ≠ (hζ.unit' : 𝓞 K) ^ b := by
    intro heq
    exact hab (hζ.unit'_coe.pow_inj ha hb heq)
  exact
    (hζ.unit'_coe.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
      (by norm_num : Nat.Prime 67) (hroot a) (hroot b) hne).symm

/-- The coefficient `(1-ζ^a)ε` in equation (8) is associated to the
standard uniformizer whenever `0 < a < 67`. -/
lemma associated_one_sub_zetaPow_mul_unit67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    (a : ℕ) (ha0 : a ≠ 0) (ha67 : a < 67)
    (ε : (𝓞 K)ˣ) :
    Associated
      ((1 - (hζ.unit' : 𝓞 K) ^ a) * (ε : 𝓞 K))
      ((hζ.unit' : 𝓞 K) - 1) := by
  have hsub :
      Associated ((hζ.unit' : 𝓞 K) ^ a - 1)
        ((hζ.unit' : 𝓞 K) - 1) := by
    simpa only [pow_zero] using
      associated_zetaPowers_sub67 hζ ha67 (by norm_num) ha0
  have honeSub :
      Associated (1 - (hζ.unit' : 𝓞 K) ^ a)
        ((hζ.unit' : 𝓞 K) - 1) := by
    have hneg :
        Associated (-((hζ.unit' : 𝓞 K) ^ a - 1))
          ((hζ.unit' : 𝓞 K) ^ a - 1) := by
      simpa only [Units.val_neg, Units.val_one, neg_mul, one_mul] using
        associated_unit_mul_left
        ((hζ.unit' : 𝓞 K) ^ a - 1)
        ((-1 : (𝓞 K)ˣ) : 𝓞 K) (-1 : (𝓞 K)ˣ).isUnit
    simpa only [neg_sub] using hneg.trans hsub
  exact associated_mul_unit_left_iff.mpr honeSub

/-- In the group of integral cyclotomic units, the inverse of `ζ` is
`ζ^66`. -/
lemma zetaUnit_inv_eq_pow_sixtySix67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67) :
    hζ.unit'⁻¹ = hζ.unit' ^ 66 := by
  symm
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ]
  apply Units.ext
  exact hζ.unit'_coe.pow_eq_one

/-- Likewise, the inverse of `ζ²` is `ζ^65`. -/
lemma zetaUnit_sq_inv_eq_pow_sixtyFive67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67) :
    (hζ.unit' ^ 2)⁻¹ = hζ.unit' ^ 65 := by
  symm
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_add]
  norm_num
  apply Units.ext
  exact hζ.unit'_coe.pow_eq_one

variable [IsCyclotomicExtension {67} ℚ K]

/-- Power-form specialization of the four equation-(8) generators.

The four roots are represented by the standard exponents `1, 66, 2, 65`.
The coefficient units are intentionally independent: this lets the theorem
apply unchanged after any unit rescaling of the four generators.  All eight
atomic coprimalities are derived internally, and the conclusion is already
in the exact product/square form required by
`ConjugationPowerReductionData67`. -/
theorem equationEight_generators_products_coprime_powForms67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    {ω θ r₁ rminus₁ r₂ rminus₂ r₀ : 𝓞 K}
    (ε₁ εminus₁ ε₂ εminus₂ : (𝓞 K)ˣ) (d : 𝓞 K)
    (hr₀ : r₀ ≠ 0)
    (hωθ : IsCoprime ω θ)
    (heq₁ :
      ω + (hζ.unit' : 𝓞 K) * θ =
        (1 - (hζ.unit' : 𝓞 K)) * ε₁ * r₁ ^ 67)
    (heqminus₁ :
      ω + (hζ.unit' : 𝓞 K) ^ 66 * θ =
        (1 - (hζ.unit' : 𝓞 K) ^ 66) * εminus₁ *
          rminus₁ ^ 67)
    (heq₂ :
      ω + (hζ.unit' : 𝓞 K) ^ 2 * θ =
        (1 - (hζ.unit' : 𝓞 K) ^ 2) * ε₂ * r₂ ^ 67)
    (heqminus₂ :
      ω + (hζ.unit' : 𝓞 K) ^ 65 * θ =
        (1 - (hζ.unit' : 𝓞 K) ^ 65) * εminus₂ *
          rminus₂ ^ 67)
    (hzero : ω + θ = d * r₀ ^ 67)
    (hr₁π : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ r₁)
    (hrminus₁π : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ rminus₁)
    (hr₂π : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ r₂)
    (hrminus₂π : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ rminus₂) :
    r₀ ^ 2 ≠ 0 ∧
      IsCoprime (r₁ * rminus₁) (r₂ * rminus₂) ∧
      IsCoprime (r₂ * rminus₂) (r₀ ^ 2) ∧
      IsCoprime (r₁ * rminus₁) (r₀ ^ 2) := by
  let π : 𝓞 K := (hζ.unit' : 𝓞 K) - 1
  have hπ0 : π ≠ 0 := by
    exact hζ.unit'_coe.sub_one_ne_zero (by norm_num)
  have hc₁ :
      Associated
        ((1 - (hζ.unit' : 𝓞 K)) * (ε₁ : 𝓞 K)) π := by
    simpa only [π, pow_one] using
      associated_one_sub_zetaPow_mul_unit67 hζ 1
        (by norm_num) (by norm_num) ε₁
  have hcminus₁ :
      Associated
        ((1 - (hζ.unit' : 𝓞 K) ^ 66) * (εminus₁ : 𝓞 K)) π := by
    simpa only [π] using
      associated_one_sub_zetaPow_mul_unit67 hζ 66
        (by norm_num) (by norm_num) εminus₁
  have hc₂ :
      Associated
        ((1 - (hζ.unit' : 𝓞 K) ^ 2) * (ε₂ : 𝓞 K)) π := by
    simpa only [π] using
      associated_one_sub_zetaPow_mul_unit67 hζ 2
        (by norm_num) (by norm_num) ε₂
  have hcminus₂ :
      Associated
        ((1 - (hζ.unit' : 𝓞 K) ^ 65) * (εminus₂ : 𝓞 K)) π := by
    simpa only [π] using
      associated_one_sub_zetaPow_mul_unit67 hζ 65
        (by norm_num) (by norm_num) εminus₂
  have ht₁₂ :
      Associated
        ((hζ.unit' : 𝓞 K) - (hζ.unit' : 𝓞 K) ^ 2) π := by
    simpa only [π, pow_one] using
      associated_zetaPowers_sub67 hζ
        (a := 1) (b := 2) (by norm_num) (by norm_num) (by norm_num)
  have ht₁minus₂ :
      Associated
        ((hζ.unit' : 𝓞 K) - (hζ.unit' : 𝓞 K) ^ 65) π := by
    simpa only [π, pow_one] using
      associated_zetaPowers_sub67 hζ
        (a := 1) (b := 65) (by norm_num) (by norm_num) (by norm_num)
  have htminus₁₂ :
      Associated
        ((hζ.unit' : 𝓞 K) ^ 66 - (hζ.unit' : 𝓞 K) ^ 2) π := by
    simpa only [π] using
      associated_zetaPowers_sub67 hζ
        (a := 66) (b := 2) (by norm_num) (by norm_num) (by norm_num)
  have htminus₁minus₂ :
      Associated
        ((hζ.unit' : 𝓞 K) ^ 66 - (hζ.unit' : 𝓞 K) ^ 65) π := by
    simpa only [π] using
      associated_zetaPowers_sub67 hζ
        (a := 66) (b := 65) (by norm_num) (by norm_num) (by norm_num)
  have ht₁zero :
      Associated ((hζ.unit' : 𝓞 K) - 1) π :=
    Associated.refl π
  have htminus₁zero :
      Associated ((hζ.unit' : 𝓞 K) ^ 66 - 1) π := by
    simpa only [π, pow_zero] using
      associated_zetaPowers_sub67 hζ
        (a := 66) (b := 0) (by norm_num) (by norm_num) (by norm_num)
  have ht₂zero :
      Associated ((hζ.unit' : 𝓞 K) ^ 2 - 1) π := by
    simpa only [π, pow_zero] using
      associated_zetaPowers_sub67 hζ
        (a := 2) (b := 0) (by norm_num) (by norm_num) (by norm_num)
  have htminus₂zero :
      Associated ((hζ.unit' : 𝓞 K) ^ 65 - 1) π := by
    simpa only [π, pow_zero] using
      associated_zetaPowers_sub67 hζ
        (a := 65) (b := 0) (by norm_num) (by norm_num) (by norm_num)
  have h₁₂ : IsCoprime r₁ r₂ :=
    coprime_generators_of_distinct_linearEquations67 hπ0 hωθ
      hc₁ hc₂ ht₁₂ heq₁ heq₂
  have h₁minus₂ : IsCoprime r₁ rminus₂ :=
    coprime_generators_of_distinct_linearEquations67 hπ0 hωθ
      hc₁ hcminus₂ ht₁minus₂ heq₁ heqminus₂
  have hminus₁₂ : IsCoprime rminus₁ r₂ :=
    coprime_generators_of_distinct_linearEquations67 hπ0 hωθ
      hcminus₁ hc₂ htminus₁₂ heqminus₁ heq₂
  have hminus₁minus₂ : IsCoprime rminus₁ rminus₂ :=
    coprime_generators_of_distinct_linearEquations67 hπ0 hωθ
      hcminus₁ hcminus₂ htminus₁minus₂ heqminus₁ heqminus₂
  have h₁zero : IsCoprime r₁ r₀ :=
    coprime_generator_zero_of_linearEquations67
      hζ.zeta_sub_one_prime' hr₁π hωθ hc₁ ht₁zero heq₁ hzero
  have hminus₁zero : IsCoprime rminus₁ r₀ :=
    coprime_generator_zero_of_linearEquations67
      hζ.zeta_sub_one_prime' hrminus₁π hωθ hcminus₁
        htminus₁zero heqminus₁ hzero
  have h₂zero : IsCoprime r₂ r₀ :=
    coprime_generator_zero_of_linearEquations67
      hζ.zeta_sub_one_prime' hr₂π hωθ hc₂ ht₂zero heq₂ hzero
  have hminus₂zero : IsCoprime rminus₂ r₀ :=
    coprime_generator_zero_of_linearEquations67
      hζ.zeta_sub_one_prime' hrminus₂π hωθ hcminus₂
        htminus₂zero heqminus₂ hzero
  exact products_and_square_coprimality67 hr₀
    h₁₂ h₁minus₂ hminus₁₂ hminus₁minus₂
    h₁zero hminus₁zero h₂zero hminus₂zero

/-- Direct equation-(8) specialization with the inverse-root notation used
in the historical paired equations.  It rewrites `ζ⁻¹` and `(ζ²)⁻¹` to the
standard exponents and delegates all eight atomic coprimalities to
`equationEight_generators_products_coprime_powForms67`. -/
theorem equationEight_generators_products_coprime67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    {ω θ r₁ rminus₁ r₂ rminus₂ r₀ : 𝓞 K}
    (ε₁ εminus₁ ε₂ εminus₂ : (𝓞 K)ˣ) (d : 𝓞 K)
    (hr₀ : r₀ ≠ 0)
    (hωθ : IsCoprime ω θ)
    (heq₁ :
      ω + (hζ.unit' : 𝓞 K) * θ =
        (1 - (hζ.unit' : 𝓞 K)) * ε₁ * r₁ ^ 67)
    (heqminus₁ :
      ω + (hζ.unit'⁻¹ : (𝓞 K)ˣ) * θ =
        (1 - (hζ.unit'⁻¹ : (𝓞 K)ˣ)) * εminus₁ *
          rminus₁ ^ 67)
    (heq₂ :
      ω + (hζ.unit' ^ 2 : (𝓞 K)ˣ) * θ =
        (1 - (hζ.unit' ^ 2 : (𝓞 K)ˣ)) * ε₂ * r₂ ^ 67)
    (heqminus₂ :
      ω + ((hζ.unit' ^ 2)⁻¹ : (𝓞 K)ˣ) * θ =
        (1 - ((hζ.unit' ^ 2)⁻¹ : (𝓞 K)ˣ)) * εminus₂ *
          rminus₂ ^ 67)
    (hzero : ω + θ = d * r₀ ^ 67)
    (hr₁π : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ r₁)
    (hrminus₁π : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ rminus₁)
    (hr₂π : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ r₂)
    (hrminus₂π : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ rminus₂) :
    r₀ ^ 2 ≠ 0 ∧
      IsCoprime (r₁ * rminus₁) (r₂ * rminus₂) ∧
      IsCoprime (r₂ * rminus₂) (r₀ ^ 2) ∧
      IsCoprime (r₁ * rminus₁) (r₀ ^ 2) := by
  have heqminus₁' :
      ω + (hζ.unit' : 𝓞 K) ^ 66 * θ =
        (1 - (hζ.unit' : 𝓞 K) ^ 66) * εminus₁ *
          rminus₁ ^ 67 := by
    rw [← Units.val_pow_eq_pow_val,
      ← zetaUnit_inv_eq_pow_sixtySix67 hζ]
    exact heqminus₁
  have heq₂' :
      ω + (hζ.unit' : 𝓞 K) ^ 2 * θ =
        (1 - (hζ.unit' : 𝓞 K) ^ 2) * ε₂ * r₂ ^ 67 := by
    simpa only [Units.val_pow_eq_pow_val] using heq₂
  have heqminus₂' :
      ω + (hζ.unit' : 𝓞 K) ^ 65 * θ =
        (1 - (hζ.unit' : 𝓞 K) ^ 65) * εminus₂ *
          rminus₂ ^ 67 := by
    rw [← Units.val_pow_eq_pow_val,
      ← zetaUnit_sq_inv_eq_pow_sixtyFive67 hζ]
    exact heqminus₂
  exact equationEight_generators_products_coprime_powForms67
    hζ ε₁ εminus₁ ε₂ εminus₂ d hr₀ hωθ
    heq₁ heqminus₁' heq₂' heqminus₂' hzero
    hr₁π hrminus₁π hr₂π hrminus₂π

end CyclotomicSpecialization

section PrincipalIdealSupport

variable {K : Type} [Field K] [NumberField K]

/-- Associated generators have identical finite prime-ideal support. -/
theorem primeIdealFactorSupport67_eq_of_associated
    {x y : 𝓞 K} (hxy : Associated x y) :
    primeIdealFactorSupport67 x = primeIdealFactorSupport67 y := by
  unfold primeIdealFactorSupport67
  rw [Ideal.span_singleton_eq_span_singleton.mpr hxy]

/-- Multiplication by a unit followed by a nonzero power preserves the
finite prime-ideal support of a generator. -/
theorem primeIdealFactorSupport67_unit_mul_pow
    (u : (𝓞 K)ˣ) (x : 𝓞 K) {n : ℕ} (hn : n ≠ 0) :
    primeIdealFactorSupport67 ((u : 𝓞 K) * x ^ n) =
      primeIdealFactorSupport67 x := by
  calc
    primeIdealFactorSupport67 ((u : 𝓞 K) * x ^ n) =
        primeIdealFactorSupport67 (x ^ n) :=
      primeIdealFactorSupport67_eq_of_associated
        (associated_unit_mul_left (x ^ n) (u : 𝓞 K) u.isUnit)
    _ = primeIdealFactorSupport67 x :=
      primeIdealFactorSupport67_pow x hn

/-- In particular, the zero-root normalization used after equation (10)
does not alter the support of the equation-(8a) generator. -/
theorem primeIdealFactorSupport67_unit_mul_square
    (u : (𝓞 K)ˣ) (r₀ : 𝓞 K) :
    primeIdealFactorSupport67 ((u : 𝓞 K) * r₀ ^ 2) =
      primeIdealFactorSupport67 r₀ :=
  primeIdealFactorSupport67_unit_mul_pow u r₀ (by norm_num)

/-- Strict support descent is unchanged by the unit-times-square
normalization of the equation-(8a) generator. -/
theorem primeIdealFactorSupport67_unit_mul_square_ssubset_iff
    (u : (𝓞 K)ˣ) (r₀ ξ : 𝓞 K) :
    primeIdealFactorSupport67 ((u : 𝓞 K) * r₀ ^ 2) ⊂
        primeIdealFactorSupport67 ξ ↔
      primeIdealFactorSupport67 r₀ ⊂ primeIdealFactorSupport67 ξ := by
  rw [primeIdealFactorSupport67_unit_mul_square]

end PrincipalIdealSupport

end

end Fermat.SixtySeven.VandiverHistorical
