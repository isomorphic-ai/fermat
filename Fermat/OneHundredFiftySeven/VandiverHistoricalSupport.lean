import Fermat.OneHundredFiftySeven.VandiverHistorical

/-!
# Prime-support bookkeeping for Vandiver's historical descent at 157

This file isolates the unique-factorization bookkeeping used after
Vandiver's equation (10).  If a principal ideal factors as

`(b) = (a) * Q`,

then every prime-ideal factor of `(a)` occurs in `(b)`.  The inclusion is
strict as soon as `Q` is a nonunit and is coprime to `(a)`.  The final
theorem is phrased for the equation-(8a) ideal and for the square of its
chosen generator, which is the generator occurring on the right side of
the quadratic equation (10a).
-/

namespace Fermat.OneHundredFiftySeven.VandiverHistorical

open scoped NumberField nonZeroDivisors

open Fermat.Irregular.VandiverHistoricalDescent

noncomputable section

variable {K : Type} [Field K] [NumberField K]

local instance : Fact (Nat.Prime 157) := ⟨by norm_num⟩

/-- Taking a positive power does not change the set of distinct normalized
prime-ideal factors of a principal ideal. -/
lemma primeIdealFactorSupport157_pow (a : 𝓞 K) {n : ℕ} (hn : n ≠ 0) :
    primeIdealFactorSupport157 (a ^ n) =
      primeIdealFactorSupport157 a := by
  unfold primeIdealFactorSupport157
  rw [← Ideal.span_singleton_pow,
    UniqueFactorizationMonoid.normalizedFactors_pow]
  simp [hn]

/-- A displayed ideal factorization `(b) = (a) * Q` gives inclusion of
the distinct prime-ideal supports. -/
lemma primeIdealFactorSupport157_subset_of_span_factor
    {a b : 𝓞 K} {Q : Ideal (𝓞 K)}
    (hb : b ≠ 0)
    (hfactor : Ideal.span {b} = Ideal.span {a} * Q) :
    primeIdealFactorSupport157 a ⊆ primeIdealFactorSupport157 b := by
  have hbI : Ideal.span {b} ≠ 0 := by
    simpa only [Ideal.zero_eq_bot, ne_eq,
      Ideal.span_singleton_eq_bot] using hb
  have hmul : Ideal.span {a} * Q ≠ 0 := by
    rw [← hfactor]
    exact hbI
  have haI : Ideal.span {a} ≠ 0 := left_ne_zero_of_mul hmul
  intro P hP
  have hP' :
      P ∈ UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span {a}) := by
    simpa only [primeIdealFactorSupport157, Multiset.mem_toFinset] using hP
  have hprime :
      P.IsPrime ∧ Ideal.span {a} ≤ P :=
    (Ideal.mem_normalizedFactors_iff haI).mp hP'
  have hba : Ideal.span {b} ≤ Ideal.span {a} := by
    rw [hfactor]
    exact Ideal.mul_le_right
  have hP'' :
      P ∈ UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span {b}) :=
    (Ideal.mem_normalizedFactors_iff hbI).mpr
      ⟨hprime.1, hba.trans hprime.2⟩
  simpa only [primeIdealFactorSupport157, Multiset.mem_toFinset] using hP''

/-- Witness form of strictness: a factor of `Q` which is absent from
`(a)` is a genuinely new prime-ideal factor of `(b)`. -/
lemma primeIdealFactorSupport157_ssubset_of_span_factor_of_witness
    {a b : 𝓞 K} {Q P : Ideal (𝓞 K)}
    (hb : b ≠ 0)
    (hfactor : Ideal.span {b} = Ideal.span {a} * Q)
    (hPQ :
      P ∈ UniqueFactorizationMonoid.normalizedFactors Q)
    (hPa :
      P ∉ UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span {a})) :
    primeIdealFactorSupport157 a ⊂ primeIdealFactorSupport157 b := by
  have hmul : Ideal.span {a} * Q ≠ 0 := by
    rw [← hfactor]
    simpa only [Ideal.zero_eq_bot, ne_eq,
      Ideal.span_singleton_eq_bot] using hb
  have haI : Ideal.span {a} ≠ 0 := left_ne_zero_of_mul hmul
  have hQI : Q ≠ 0 := right_ne_zero_of_mul hmul
  have hsubset :=
    primeIdealFactorSupport157_subset_of_span_factor hb hfactor
  apply (Finset.ssubset_iff_of_subset hsubset).mpr
  refine ⟨P, ?_, ?_⟩
  · change P ∈
      (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span {b})).toFinset
    rw [hfactor,
      UniqueFactorizationMonoid.normalizedFactors_mul haI hQI]
    simp only [Multiset.toFinset_add, Finset.mem_union,
      Multiset.mem_toFinset]
    exact Or.inr hPQ
  · simpa only [primeIdealFactorSupport157, Multiset.mem_toFinset] using hPa

/-- Coprime-factor form of strictness.  A nonunit ideal `Q` has a
normalized prime factor, and coprimality makes that factor absent from
`(a)`. -/
lemma primeIdealFactorSupport157_ssubset_of_span_factor
    {a b : 𝓞 K} {Q : Ideal (𝓞 K)}
    (hb : b ≠ 0)
    (hfactor : Ideal.span {b} = Ideal.span {a} * Q)
    (hQ : Q ≠ ⊤)
    (hcop : IsCoprime (Ideal.span {a}) Q) :
    primeIdealFactorSupport157 a ⊂ primeIdealFactorSupport157 b := by
  have hmul : Ideal.span {a} * Q ≠ 0 := by
    rw [← hfactor]
    simpa only [Ideal.zero_eq_bot, ne_eq,
      Ideal.span_singleton_eq_bot] using hb
  have hQI : Q ≠ 0 := right_ne_zero_of_mul hmul
  have hQunit : ¬ IsUnit Q := by
    simpa only [Ideal.isUnit_iff] using hQ
  obtain ⟨P, hPQ⟩ :=
    UniqueFactorizationMonoid.exists_mem_normalizedFactors hQI hQunit
  apply primeIdealFactorSupport157_ssubset_of_span_factor_of_witness
    hb hfactor hPQ
  intro hPa
  exact (Multiset.disjoint_left.mp
    (UniqueFactorizationMonoid.disjoint_normalizedFactors
      hcop.isRelPrime)) hPa hPQ

/-- Equation-(10) support drop for the square of the distinguished
equation-(8a) generator.

The historical construction supplies the factorization of `(ξ)` by the
equation-(8a) ideal.  Once its complementary factor is nontrivial and
coprime, replacing the chosen generator `ρ₀` by `ρ₀²` preserves its support
and gives the strict inclusion required by `ConjugationPowerReductionData157`.
-/
theorem historicalEquationEightA_square_support_strict157
    [IsCyclotomicExtension {157} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 157)
    (s : HistoricalState hζ) (ρzero : 𝓞 K) (Q : Ideal (𝓞 K))
    (hgenerator :
      historicalEquationEightAIdeal157 hζ s =
        Ideal.span {ρzero})
    (hfactor :
      Ideal.span {s.xi} =
        historicalEquationEightAIdeal157 hζ s * Q)
    (hQ : Q ≠ ⊤)
    (hcop :
      IsCoprime (historicalEquationEightAIdeal157 hζ s) Q) :
    primeIdealFactorSupport157 (ρzero ^ 2) ⊂
      primeIdealFactorSupport157 s.xi := by
  rw [primeIdealFactorSupport157_pow ρzero (by norm_num : 2 ≠ 0)]
  apply primeIdealFactorSupport157_ssubset_of_span_factor
    s.xi_ne_zero
  · simpa only [hgenerator] using hfactor
  · exact hQ
  · simpa only [hgenerator] using hcop

end

end Fermat.OneHundredFiftySeven.VandiverHistorical
