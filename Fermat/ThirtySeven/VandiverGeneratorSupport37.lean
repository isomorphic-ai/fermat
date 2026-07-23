import Fermat.ThirtySeven.VandiverHistoricalSupport

/-!
# Generator coprimality and support in Vandiver's exponent-37 reduction

This file isolates the elementary commutative-algebra facts needed when the
four generators from equation (8) and the generator from equation (8a) are
assembled into the three generators occurring in equation (10).

The equation-level lemmas deliberately use only the displayed linear
equations, the source coprimality of `ω` and `θ`, and the fact that all
differences of distinct 37th roots are associated to the standard
uniformizer.  The final packaging theorem then proves the three pairwise
coprimalities for

`x = r₁ * r₋₁`, `y = r₂ * r₋₂`, and `z = r₀ ^ 2`.

The last section records that multiplying a generator by a unit, and taking a
nonzero power, does not change the finite support of its principal ideal.
-/

namespace Fermat.ThirtySeven.VandiverHistorical

open scoped NumberField nonZeroDivisors

noncomputable section

section ElementaryCoprimality

variable {R : Type*} [CommRing R]

/-- A linear factor `ω + t*θ` which is a coefficient times a positive power
of `r` forces `r` to be coprime to `θ`, provided `ω` and `θ` are coprime.

No property of the coefficient is needed: coprimality of the whole product
implies coprimality of each factor. -/
lemma isCoprime_linearRoot_theta37
    {ω θ t c r : R}
    (hωθ : IsCoprime ω θ)
    (heq : ω + t * θ = c * r ^ 37) :
    IsCoprime r θ := by
  have hlinear : IsCoprime (ω + t * θ) θ :=
    hωθ.add_mul_right_left t
  rw [heq] at hlinear
  exact (IsCoprime.pow_left_iff (by norm_num : 0 < 37)).mp
    hlinear.of_mul_left_right

/-- Two distinct linear equations whose coefficients and root difference are
all associated to the same nonzero uniformizer have coprime 37th-power
generators.

After replacing the three associated elements by a uniformizer times a unit,
subtracting the equations and cancelling the uniformizer gives

`v*θ = u₁*r₁^37 - u₂*r₂^37`.

The source coprimality of `ω` and `θ` first gives `IsCoprime r₁ θ`; the last
identity then gives `IsCoprime r₁ r₂`. -/
theorem coprime_generators_of_distinct_linearEquations37
    [IsDomain R]
    {ω θ π t₁ t₂ c₁ c₂ r₁ r₂ : R}
    (hπ0 : π ≠ 0)
    (hωθ : IsCoprime ω θ)
    (hc₁ : Associated c₁ π)
    (hc₂ : Associated c₂ π)
    (ht : Associated (t₁ - t₂) π)
    (heq₁ : ω + t₁ * θ = c₁ * r₁ ^ 37)
    (heq₂ : ω + t₂ * θ = c₂ * r₂ ^ 37) :
    IsCoprime r₁ r₂ := by
  obtain ⟨u₁, hu₁⟩ := hc₁.symm
  obtain ⟨u₂, hu₂⟩ := hc₂.symm
  obtain ⟨v, hv⟩ := ht.symm
  have heq₁' :
      ω + t₁ * θ = π * (u₁ : R) * r₁ ^ 37 := by
    calc
      ω + t₁ * θ = c₁ * r₁ ^ 37 := heq₁
      _ = π * (u₁ : R) * r₁ ^ 37 := by rw [hu₁]
  have heq₂' :
      ω + t₂ * θ = π * (u₂ : R) * r₂ ^ 37 := by
    calc
      ω + t₂ * θ = c₂ * r₂ ^ 37 := heq₂
      _ = π * (u₂ : R) * r₂ ^ 37 := by rw [hu₂]
  have hdiff :
      (v : R) * θ =
        (u₁ : R) * r₁ ^ 37 - (u₂ : R) * r₂ ^ 37 := by
    apply mul_left_cancel₀ hπ0
    calc
      π * ((v : R) * θ) = (t₁ - t₂) * θ := by rw [← hv]; ring
      _ = (ω + t₁ * θ) - (ω + t₂ * θ) := by ring
      _ = (π * (u₁ : R) * r₁ ^ 37) -
          (π * (u₂ : R) * r₂ ^ 37) := by rw [heq₁', heq₂']
      _ = π * ((u₁ : R) * r₁ ^ 37 -
          (u₂ : R) * r₂ ^ 37) := by ring
  have hr₁θ : IsCoprime r₁ θ :=
    isCoprime_linearRoot_theta37 hωθ heq₁
  have hcop :
      IsCoprime r₁
        ((u₁ : R) * r₁ ^ 37 - (u₂ : R) * r₂ ^ 37) := by
    rw [← hdiff]
    exact (isCoprime_mul_unit_left_right v.isUnit r₁ θ).mpr hr₁θ
  have hcop' : IsCoprime r₁ ((u₂ : R) * r₂ ^ 37) := by
    rw [show (u₁ : R) * r₁ ^ 37 =
      r₁ * ((u₁ : R) * r₁ ^ 36) by ring] at hcop
    exact IsCoprime.mul_sub_left_right_iff.mp hcop
  have hpow : IsCoprime r₁ (r₂ ^ 37) :=
    (isCoprime_mul_unit_left_right u₂.isUnit r₁ (r₂ ^ 37)).mp hcop'
  exact (IsCoprime.pow_right_iff (by norm_num : 0 < 37)).mp hpow

/-- In a one-dimensional domain, a prime element is coprime to every element
it does not divide.  This is the ideal-theoretic replacement for the usual
gcd-domain lemma: the nonzero principal prime ideal is maximal. -/
theorem isCoprime_prime_of_not_dvd_dimensionOne37
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
theorem coprime_generator_zero_of_linearEquations37
    [IsDomain R] [Ring.DimensionLEOne R]
    {ω θ π t c r d r₀ : R}
    (hπ : Prime π)
    (hrπ : ¬ π ∣ r)
    (hωθ : IsCoprime ω θ)
    (hc : Associated c π)
    (ht : Associated (t - 1) π)
    (heq : ω + t * θ = c * r ^ 37)
    (hzero : ω + θ = d * r₀ ^ 37) :
    IsCoprime r r₀ := by
  obtain ⟨u, hu⟩ := hc.symm
  have heq' : ω + t * θ = π * (u : R) * r ^ 37 := by
    calc
      ω + t * θ = c * r ^ 37 := heq
      _ = π * (u : R) * r ^ 37 := by rw [hu]
  have hπr : IsCoprime π r :=
    isCoprime_prime_of_not_dvd_dimensionOne37 hπ hrπ
  obtain ⟨v, hv⟩ := ht.symm
  have hrt : IsCoprime r (t - 1) := by
    rw [← hv]
    exact (isCoprime_mul_unit_right_right v.isUnit r π).mpr hπr.symm
  have hrθ : IsCoprime r θ :=
    isCoprime_linearRoot_theta37 hωθ heq
  have hrprod : IsCoprime r ((t - 1) * θ) :=
    hrt.mul_right hrθ
  have hrewrite :
      ω + θ =
        r * (π * (u : R) * r ^ 36) - (t - 1) * θ := by
    calc
      ω + θ = (ω + t * θ) - (t - 1) * θ := by ring
      _ = (π * (u : R) * r ^ 37) - (t - 1) * θ := by rw [heq']
      _ = r * (π * (u : R) * r ^ 36) - (t - 1) * θ := by ring
  have hrsum : IsCoprime r (ω + θ) := by
    rw [hrewrite]
    exact IsCoprime.mul_sub_left_right_iff.mpr hrprod
  rw [hzero] at hrsum
  exact (IsCoprime.pow_right_iff (by norm_num : 0 < 37)).mp
    hrsum.of_mul_right_right

/-- Package the eight atomic generator coprimalities into the exact
nonvanishing and pairwise-coprimality fields needed for
`ConjugationPowerReductionData37` with

`x = r₁*r₋₁`, `y = r₂*r₋₂`, and `z = r₀^2`. -/
theorem products_and_square_coprimality37
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

section PrincipalIdealSupport

variable {K : Type} [Field K] [NumberField K]

/-- Associated generators have identical finite prime-ideal support. -/
theorem primeIdealFactorSupport37_eq_of_associated
    {x y : 𝓞 K} (hxy : Associated x y) :
    primeIdealFactorSupport37 x = primeIdealFactorSupport37 y := by
  unfold primeIdealFactorSupport37
  rw [Ideal.span_singleton_eq_span_singleton.mpr hxy]

/-- Multiplication by a unit followed by a nonzero power preserves the
finite prime-ideal support of a generator. -/
theorem primeIdealFactorSupport37_unit_mul_pow
    (u : (𝓞 K)ˣ) (x : 𝓞 K) {n : ℕ} (hn : n ≠ 0) :
    primeIdealFactorSupport37 ((u : 𝓞 K) * x ^ n) =
      primeIdealFactorSupport37 x := by
  calc
    primeIdealFactorSupport37 ((u : 𝓞 K) * x ^ n) =
        primeIdealFactorSupport37 (x ^ n) :=
      primeIdealFactorSupport37_eq_of_associated
        (associated_unit_mul_left (x ^ n) (u : 𝓞 K) u.isUnit)
    _ = primeIdealFactorSupport37 x :=
      primeIdealFactorSupport37_pow x hn

/-- In particular, the zero-root normalization used after equation (10)
does not alter the support of the equation-(8a) generator. -/
theorem primeIdealFactorSupport37_unit_mul_square
    (u : (𝓞 K)ˣ) (r₀ : 𝓞 K) :
    primeIdealFactorSupport37 ((u : 𝓞 K) * r₀ ^ 2) =
      primeIdealFactorSupport37 r₀ :=
  primeIdealFactorSupport37_unit_mul_pow u r₀ (by norm_num)

/-- Strict support descent is unchanged by the unit-times-square
normalization of the equation-(8a) generator. -/
theorem primeIdealFactorSupport37_unit_mul_square_ssubset_iff
    (u : (𝓞 K)ˣ) (r₀ ξ : 𝓞 K) :
    primeIdealFactorSupport37 ((u : 𝓞 K) * r₀ ^ 2) ⊂
        primeIdealFactorSupport37 ξ ↔
      primeIdealFactorSupport37 r₀ ⊂ primeIdealFactorSupport37 ξ := by
  rw [primeIdealFactorSupport37_unit_mul_square]

end PrincipalIdealSupport

end

end Fermat.ThirtySeven.VandiverHistorical
