import Fermat.Irregular.VandiverHistoricalSupportPrime

/-!
# Prime-generic generator coprimality in Vandiver's reduction

This module proves the commutative-algebra bookkeeping used when the four
generators from equation (8) and the distinguished generator from equation
(8a) are assembled into

`x = r₁ * r₋₁`, `y = r₂ * r₋₂`, and `z = r₀ ^ 2`.

Only the four displayed linear equations, source coprimality, and
nondivisibility by the cyclotomic uniformizer are required.  Consequently
the proof is uniform for every prime `p ≥ 5`.
-/

namespace Fermat.Irregular.VandiverGeneratorSupportPrime

open scoped NumberField nonZeroDivisors

noncomputable section

section ElementaryCoprimality

variable {p : ℕ} [Fact p.Prime]
variable {R : Type*} [CommRing R]

/-- A linear factor `ω + t*θ` which is a coefficient times a positive
`p`-th power forces its generator to be coprime to `θ`. -/
lemma isCoprime_linearRoot_theta
    {ω θ t c r : R}
    (hωθ : IsCoprime ω θ)
    (heq : ω + t * θ = c * r ^ p) :
    IsCoprime r θ := by
  have hlinear : IsCoprime (ω + t * θ) θ :=
    hωθ.add_mul_right_left t
  rw [heq] at hlinear
  exact (IsCoprime.pow_left_iff (Fact.out : p.Prime).pos).mp
    hlinear.of_mul_left_right

/-- Two distinct linear equations whose coefficients and root difference
are associated to the same nonzero uniformizer have coprime generators. -/
theorem coprime_generators_of_distinct_linearEquations
    [IsDomain R]
    {ω θ π t₁ t₂ c₁ c₂ r₁ r₂ : R}
    (hπ0 : π ≠ 0)
    (hωθ : IsCoprime ω θ)
    (hc₁ : Associated c₁ π)
    (hc₂ : Associated c₂ π)
    (ht : Associated (t₁ - t₂) π)
    (heq₁ : ω + t₁ * θ = c₁ * r₁ ^ p)
    (heq₂ : ω + t₂ * θ = c₂ * r₂ ^ p) :
    IsCoprime r₁ r₂ := by
  obtain ⟨u₁, hu₁⟩ := hc₁.symm
  obtain ⟨u₂, hu₂⟩ := hc₂.symm
  obtain ⟨v, hv⟩ := ht.symm
  have heq₁' :
      ω + t₁ * θ = π * (u₁ : R) * r₁ ^ p := by
    calc
      ω + t₁ * θ = c₁ * r₁ ^ p := heq₁
      _ = π * (u₁ : R) * r₁ ^ p := by rw [hu₁]
  have heq₂' :
      ω + t₂ * θ = π * (u₂ : R) * r₂ ^ p := by
    calc
      ω + t₂ * θ = c₂ * r₂ ^ p := heq₂
      _ = π * (u₂ : R) * r₂ ^ p := by rw [hu₂]
  have hdiff :
      (v : R) * θ =
        (u₁ : R) * r₁ ^ p - (u₂ : R) * r₂ ^ p := by
    apply mul_left_cancel₀ hπ0
    calc
      π * ((v : R) * θ) = (t₁ - t₂) * θ := by rw [← hv]; ring
      _ = (ω + t₁ * θ) - (ω + t₂ * θ) := by ring
      _ = (π * (u₁ : R) * r₁ ^ p) -
          (π * (u₂ : R) * r₂ ^ p) := by rw [heq₁', heq₂']
      _ = π * ((u₁ : R) * r₁ ^ p -
          (u₂ : R) * r₂ ^ p) := by ring
  have hr₁θ : IsCoprime r₁ θ :=
    isCoprime_linearRoot_theta hωθ heq₁
  have hcop :
      IsCoprime r₁
        ((u₁ : R) * r₁ ^ p - (u₂ : R) * r₂ ^ p) := by
    rw [← hdiff]
    exact (isCoprime_mul_unit_left_right v.isUnit r₁ θ).mpr hr₁θ
  have hpSucc : p - 1 + 1 = p := by
    have := (Fact.out : p.Prime).pos
    omega
  have hfactor :
      (u₁ : R) * r₁ ^ p = r₁ * ((u₁ : R) * r₁ ^ (p - 1)) := by
    calc
      (u₁ : R) * r₁ ^ p =
          (u₁ : R) * r₁ ^ ((p - 1) + 1) := by rw [hpSucc]
      _ = r₁ * ((u₁ : R) * r₁ ^ (p - 1)) := by
        rw [pow_succ]
        ac_rfl
  have hcop' : IsCoprime r₁ ((u₂ : R) * r₂ ^ p) := by
    rw [hfactor] at hcop
    exact IsCoprime.mul_sub_left_right_iff.mp hcop
  have hpow : IsCoprime r₁ (r₂ ^ p) :=
    (isCoprime_mul_unit_left_right u₂.isUnit r₁ (r₂ ^ p)).mp hcop'
  exact (IsCoprime.pow_right_iff (Fact.out : p.Prime).pos).mp hpow

/-- In a one-dimensional domain, a prime element is coprime to every
element it does not divide. -/
theorem isCoprime_prime_of_not_dvd_dimensionOne
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

/-- A generator from a nonzero linear root is coprime to the generator
from the zero-root equation. -/
theorem coprime_generator_zero_of_linearEquations
    [IsDomain R] [Ring.DimensionLEOne R]
    {ω θ π t c r d r₀ : R}
    (hπ : Prime π)
    (hrπ : ¬ π ∣ r)
    (hωθ : IsCoprime ω θ)
    (hc : Associated c π)
    (ht : Associated (t - 1) π)
    (heq : ω + t * θ = c * r ^ p)
    (hzero : ω + θ = d * r₀ ^ p) :
    IsCoprime r r₀ := by
  obtain ⟨u, hu⟩ := hc.symm
  have heq' : ω + t * θ = π * (u : R) * r ^ p := by
    calc
      ω + t * θ = c * r ^ p := heq
      _ = π * (u : R) * r ^ p := by rw [hu]
  have hπr : IsCoprime π r :=
    isCoprime_prime_of_not_dvd_dimensionOne hπ hrπ
  obtain ⟨v, hv⟩ := ht.symm
  have hrt : IsCoprime r (t - 1) := by
    rw [← hv]
    exact (isCoprime_mul_unit_right_right v.isUnit r π).mpr hπr.symm
  have hrθ : IsCoprime r θ :=
    isCoprime_linearRoot_theta hωθ heq
  have hrprod : IsCoprime r ((t - 1) * θ) :=
    hrt.mul_right hrθ
  have hpSucc : p - 1 + 1 = p := by
    have := (Fact.out : p.Prime).pos
    omega
  have hfactor :
      π * (u : R) * r ^ p =
        r * (π * (u : R) * r ^ (p - 1)) := by
    calc
      π * (u : R) * r ^ p =
          π * (u : R) * r ^ ((p - 1) + 1) := by rw [hpSucc]
      _ = r * (π * (u : R) * r ^ (p - 1)) := by
        rw [pow_succ]
        ac_rfl
  have hrewrite :
      ω + θ =
        r * (π * (u : R) * r ^ (p - 1)) - (t - 1) * θ := by
    calc
      ω + θ = (ω + t * θ) - (t - 1) * θ := by ring
      _ = (π * (u : R) * r ^ p) - (t - 1) * θ := by rw [heq']
      _ = r * (π * (u : R) * r ^ (p - 1)) -
          (t - 1) * θ := by rw [hfactor]
  have hrsum : IsCoprime r (ω + θ) := by
    rw [hrewrite]
    exact IsCoprime.mul_sub_left_right_iff.mpr hrprod
  rw [hzero] at hrsum
  exact (IsCoprime.pow_right_iff (Fact.out : p.Prime).pos).mp
    hrsum.of_mul_right_right

/-- Package the eight atomic coprimalities into the exact nonvanishing and
pairwise-coprimality fields needed by the historical reduction data. -/
theorem products_and_square_coprimality
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

variable {K : Type} {p : ℕ} [Fact p.Prime]
  [Field K] [NumberField K]

/-- Distinct powers in the standard range differ by an associate of the
cyclotomic uniformizer. -/
lemma associated_zetaPowers_sub
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {a b : ℕ} (ha : a < p) (hb : b < p) (hab : a ≠ b) :
    Associated
      ((hζ.unit' : 𝓞 K) ^ a - (hζ.unit' : 𝓞 K) ^ b)
      ((hζ.unit' : 𝓞 K) - 1) := by
  have hroot (j : ℕ) :
      (hζ.unit' : 𝓞 K) ^ j ∈
        Polynomial.nthRootsFinset p (1 : 𝓞 K) := by
    rw [Polynomial.mem_nthRootsFinset (Fact.out : p.Prime).pos]
    rw [← pow_mul, Nat.mul_comm j p, pow_mul,
      hζ.unit'_coe.pow_eq_one, one_pow]
  have hne :
      (hζ.unit' : 𝓞 K) ^ a ≠ (hζ.unit' : 𝓞 K) ^ b := by
    intro heq
    exact hab (hζ.unit'_coe.pow_inj ha hb heq)
  exact
    (hζ.unit'_coe.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
      (Fact.out : p.Prime) (hroot a) (hroot b) hne).symm

/-- The coefficient `(1 - ζ^a)ε` is associated to the standard
uniformizer whenever `0 < a < p`. -/
lemma associated_one_sub_zetaPow_mul_unit
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (a : ℕ) (ha0 : a ≠ 0) (hap : a < p)
    (ε : (𝓞 K)ˣ) :
    Associated
      ((1 - (hζ.unit' : 𝓞 K) ^ a) * (ε : 𝓞 K))
      ((hζ.unit' : 𝓞 K) - 1) := by
  have hsub :
      Associated ((hζ.unit' : 𝓞 K) ^ a - 1)
        ((hζ.unit' : 𝓞 K) - 1) := by
    simpa only [pow_zero] using
      associated_zetaPowers_sub hζ hap
        (Fact.out : p.Prime).pos ha0
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

/-- In the group of integral cyclotomic units, `ζ⁻¹ = ζ^(p-1)`. -/
lemma zetaUnit_inv_eq_pow_sub_one
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    hζ.unit'⁻¹ = hζ.unit' ^ (p - 1) := by
  symm
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ]
  rw [show p - 1 + 1 = p by
    have := (Fact.out : p.Prime).pos
    omega]
  apply Units.ext
  exact hζ.unit'_coe.pow_eq_one

/-- For `p ≥ 5`, `(ζ²)⁻¹ = ζ^(p-2)`. -/
lemma zetaUnit_sq_inv_eq_pow_sub_two
    (hp5 : 5 ≤ p) {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    (hζ.unit' ^ 2)⁻¹ = hζ.unit' ^ (p - 2) := by
  symm
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_add]
  rw [show p - 2 + 2 = p by omega]
  apply Units.ext
  exact hζ.unit'_coe.pow_eq_one

variable [IsCyclotomicExtension {p} ℚ K]

/-- Power-form specialization of the four equation-(8) generators at the
standard exponents `1`, `p-1`, `2`, and `p-2`. -/
theorem equationEight_generators_products_coprime_powForms
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {ω θ r₁ rminus₁ r₂ rminus₂ r₀ : 𝓞 K}
    (ε₁ εminus₁ ε₂ εminus₂ : (𝓞 K)ˣ) (d : 𝓞 K)
    (hr₀ : r₀ ≠ 0)
    (hωθ : IsCoprime ω θ)
    (heq₁ :
      ω + (hζ.unit' : 𝓞 K) * θ =
        (1 - (hζ.unit' : 𝓞 K)) * ε₁ * r₁ ^ p)
    (heqminus₁ :
      ω + (hζ.unit' : 𝓞 K) ^ (p - 1) * θ =
        (1 - (hζ.unit' : 𝓞 K) ^ (p - 1)) * εminus₁ *
          rminus₁ ^ p)
    (heq₂ :
      ω + (hζ.unit' : 𝓞 K) ^ 2 * θ =
        (1 - (hζ.unit' : 𝓞 K) ^ 2) * ε₂ * r₂ ^ p)
    (heqminus₂ :
      ω + (hζ.unit' : 𝓞 K) ^ (p - 2) * θ =
        (1 - (hζ.unit' : 𝓞 K) ^ (p - 2)) * εminus₂ *
          rminus₂ ^ p)
    (hzero : ω + θ = d * r₀ ^ p)
    (hr₁π : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ r₁)
    (hrminus₁π : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ rminus₁)
    (hr₂π : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ r₂)
    (hrminus₂π : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ rminus₂) :
    r₀ ^ 2 ≠ 0 ∧
      IsCoprime (r₁ * rminus₁) (r₂ * rminus₂) ∧
      IsCoprime (r₂ * rminus₂) (r₀ ^ 2) ∧
      IsCoprime (r₁ * rminus₁) (r₀ ^ 2) := by
  let π : 𝓞 K := (hζ.unit' : 𝓞 K) - 1
  have hπ0 : π ≠ 0 :=
    hζ.unit'_coe.sub_one_ne_zero (by omega)
  have hc₁ :
      Associated
        ((1 - (hζ.unit' : 𝓞 K)) * (ε₁ : 𝓞 K)) π := by
    simpa only [π, pow_one] using
      associated_one_sub_zetaPow_mul_unit hζ 1
        (by omega) (by omega) ε₁
  have hcminus₁ :
      Associated
        ((1 - (hζ.unit' : 𝓞 K) ^ (p - 1)) *
          (εminus₁ : 𝓞 K)) π := by
    simpa only [π] using
      associated_one_sub_zetaPow_mul_unit hζ (p - 1)
        (by omega) (by omega) εminus₁
  have hc₂ :
      Associated
        ((1 - (hζ.unit' : 𝓞 K) ^ 2) * (ε₂ : 𝓞 K)) π := by
    simpa only [π] using
      associated_one_sub_zetaPow_mul_unit hζ 2
        (by omega) (by omega) ε₂
  have hcminus₂ :
      Associated
        ((1 - (hζ.unit' : 𝓞 K) ^ (p - 2)) *
          (εminus₂ : 𝓞 K)) π := by
    simpa only [π] using
      associated_one_sub_zetaPow_mul_unit hζ (p - 2)
        (by omega) (by omega) εminus₂
  have ht₁₂ :
      Associated
        ((hζ.unit' : 𝓞 K) - (hζ.unit' : 𝓞 K) ^ 2) π := by
    simpa only [π, pow_one] using
      associated_zetaPowers_sub hζ
        (a := 1) (b := 2) (by omega) (by omega) (by omega)
  have ht₁minus₂ :
      Associated
        ((hζ.unit' : 𝓞 K) -
          (hζ.unit' : 𝓞 K) ^ (p - 2)) π := by
    simpa only [π, pow_one] using
      associated_zetaPowers_sub hζ
        (a := 1) (b := p - 2) (by omega) (by omega) (by omega)
  have htminus₁₂ :
      Associated
        ((hζ.unit' : 𝓞 K) ^ (p - 1) -
          (hζ.unit' : 𝓞 K) ^ 2) π := by
    simpa only [π] using
      associated_zetaPowers_sub hζ
        (a := p - 1) (b := 2) (by omega) (by omega) (by omega)
  have htminus₁minus₂ :
      Associated
        ((hζ.unit' : 𝓞 K) ^ (p - 1) -
          (hζ.unit' : 𝓞 K) ^ (p - 2)) π := by
    simpa only [π] using
      associated_zetaPowers_sub hζ
        (a := p - 1) (b := p - 2)
        (by omega) (by omega) (by omega)
  have ht₁zero :
      Associated ((hζ.unit' : 𝓞 K) - 1) π :=
    Associated.refl π
  have htminus₁zero :
      Associated ((hζ.unit' : 𝓞 K) ^ (p - 1) - 1) π := by
    simpa only [π, pow_zero] using
      associated_zetaPowers_sub hζ
        (a := p - 1) (b := 0)
        (by omega) (by omega) (by omega)
  have ht₂zero :
      Associated ((hζ.unit' : 𝓞 K) ^ 2 - 1) π := by
    simpa only [π, pow_zero] using
      associated_zetaPowers_sub hζ
        (a := 2) (b := 0) (by omega) (by omega) (by omega)
  have htminus₂zero :
      Associated ((hζ.unit' : 𝓞 K) ^ (p - 2) - 1) π := by
    simpa only [π, pow_zero] using
      associated_zetaPowers_sub hζ
        (a := p - 2) (b := 0)
        (by omega) (by omega) (by omega)
  have h₁₂ : IsCoprime r₁ r₂ :=
    coprime_generators_of_distinct_linearEquations hπ0 hωθ
      hc₁ hc₂ ht₁₂ heq₁ heq₂
  have h₁minus₂ : IsCoprime r₁ rminus₂ :=
    coprime_generators_of_distinct_linearEquations hπ0 hωθ
      hc₁ hcminus₂ ht₁minus₂ heq₁ heqminus₂
  have hminus₁₂ : IsCoprime rminus₁ r₂ :=
    coprime_generators_of_distinct_linearEquations hπ0 hωθ
      hcminus₁ hc₂ htminus₁₂ heqminus₁ heq₂
  have hminus₁minus₂ : IsCoprime rminus₁ rminus₂ :=
    coprime_generators_of_distinct_linearEquations hπ0 hωθ
      hcminus₁ hcminus₂ htminus₁minus₂ heqminus₁ heqminus₂
  have h₁zero : IsCoprime r₁ r₀ :=
    coprime_generator_zero_of_linearEquations
      hζ.zeta_sub_one_prime' hr₁π hωθ hc₁ ht₁zero heq₁ hzero
  have hminus₁zero : IsCoprime rminus₁ r₀ :=
    coprime_generator_zero_of_linearEquations
      hζ.zeta_sub_one_prime' hrminus₁π hωθ hcminus₁
        htminus₁zero heqminus₁ hzero
  have h₂zero : IsCoprime r₂ r₀ :=
    coprime_generator_zero_of_linearEquations
      hζ.zeta_sub_one_prime' hr₂π hωθ hc₂ ht₂zero heq₂ hzero
  have hminus₂zero : IsCoprime rminus₂ r₀ :=
    coprime_generator_zero_of_linearEquations
      hζ.zeta_sub_one_prime' hrminus₂π hωθ hcminus₂
        htminus₂zero heqminus₂ hzero
  exact products_and_square_coprimality hr₀
    h₁₂ h₁minus₂ hminus₁₂ hminus₁minus₂
    h₁zero hminus₁zero h₂zero hminus₂zero

/-- Inverse-root form of the four equation-(8) generators. -/
theorem equationEight_generators_products_coprime
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {ω θ r₁ rminus₁ r₂ rminus₂ r₀ : 𝓞 K}
    (ε₁ εminus₁ ε₂ εminus₂ : (𝓞 K)ˣ) (d : 𝓞 K)
    (hr₀ : r₀ ≠ 0)
    (hωθ : IsCoprime ω θ)
    (heq₁ :
      ω + (hζ.unit' : 𝓞 K) * θ =
        (1 - (hζ.unit' : 𝓞 K)) * ε₁ * r₁ ^ p)
    (heqminus₁ :
      ω + (hζ.unit'⁻¹ : (𝓞 K)ˣ) * θ =
        (1 - (hζ.unit'⁻¹ : (𝓞 K)ˣ)) * εminus₁ *
          rminus₁ ^ p)
    (heq₂ :
      ω + (hζ.unit' ^ 2 : (𝓞 K)ˣ) * θ =
        (1 - (hζ.unit' ^ 2 : (𝓞 K)ˣ)) * ε₂ * r₂ ^ p)
    (heqminus₂ :
      ω + ((hζ.unit' ^ 2)⁻¹ : (𝓞 K)ˣ) * θ =
        (1 - ((hζ.unit' ^ 2)⁻¹ : (𝓞 K)ˣ)) * εminus₂ *
          rminus₂ ^ p)
    (hzero : ω + θ = d * r₀ ^ p)
    (hr₁π : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ r₁)
    (hrminus₁π : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ rminus₁)
    (hr₂π : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ r₂)
    (hrminus₂π : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ rminus₂) :
    r₀ ^ 2 ≠ 0 ∧
      IsCoprime (r₁ * rminus₁) (r₂ * rminus₂) ∧
      IsCoprime (r₂ * rminus₂) (r₀ ^ 2) ∧
      IsCoprime (r₁ * rminus₁) (r₀ ^ 2) := by
  have heqminus₁' :
      ω + (hζ.unit' : 𝓞 K) ^ (p - 1) * θ =
        (1 - (hζ.unit' : 𝓞 K) ^ (p - 1)) * εminus₁ *
          rminus₁ ^ p := by
    rw [← Units.val_pow_eq_pow_val,
      ← zetaUnit_inv_eq_pow_sub_one hζ]
    exact heqminus₁
  have heq₂' :
      ω + (hζ.unit' : 𝓞 K) ^ 2 * θ =
        (1 - (hζ.unit' : 𝓞 K) ^ 2) * ε₂ * r₂ ^ p := by
    simpa only [Units.val_pow_eq_pow_val] using heq₂
  have heqminus₂' :
      ω + (hζ.unit' : 𝓞 K) ^ (p - 2) * θ =
        (1 - (hζ.unit' : 𝓞 K) ^ (p - 2)) * εminus₂ *
          rminus₂ ^ p := by
    rw [← Units.val_pow_eq_pow_val,
      ← zetaUnit_sq_inv_eq_pow_sub_two hp5 hζ]
    exact heqminus₂
  exact equationEight_generators_products_coprime_powForms hp5
    hζ ε₁ εminus₁ ε₂ εminus₂ d hr₀ hωθ
    heq₁ heqminus₁' heq₂' heqminus₂' hzero
    hr₁π hrminus₁π hr₂π hrminus₂π

end CyclotomicSpecialization

end

end Fermat.Irregular.VandiverGeneratorSupportPrime
