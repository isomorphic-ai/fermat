import Fermat.Descent.Irregular.VandiverHistoricalPrime

/-!
# Prime-ideal support in Vandiver's historical descent

This module isolates the prime-independent unique-factorization bookkeeping
used after equation (10).  If

`(b) = (a) * Q`,

then every prime-ideal factor of `(a)` occurs in `(b)`.  The inclusion is
strict when `Q` is nontrivial and coprime to `(a)`.  The final theorem
packages the exact support drop used for the square of the distinguished
equation-(8a) generator.
-/

namespace Fermat.Irregular.VandiverHistoricalSupportPrime

open scoped NumberField

open Fermat.Irregular.VandiverHistoricalPrime

noncomputable section

variable {K : Type} [Field K] [NumberField K]

/-- Taking a positive power does not change the set of distinct normalized
prime-ideal factors of a principal ideal. -/
lemma primeIdealFactorSupport_pow (a : 𝓞 K) {n : ℕ} (hn : n ≠ 0) :
    primeIdealFactorSupport (a ^ n) = primeIdealFactorSupport a := by
  unfold primeIdealFactorSupport
  rw [← Ideal.span_singleton_pow,
    UniqueFactorizationMonoid.normalizedFactors_pow]
  simp [hn]

/-- Associated generators have identical finite prime-ideal support. -/
theorem primeIdealFactorSupport_eq_of_associated
    {x y : 𝓞 K} (hxy : Associated x y) :
    primeIdealFactorSupport x = primeIdealFactorSupport y := by
  unfold primeIdealFactorSupport
  rw [Ideal.span_singleton_eq_span_singleton.mpr hxy]

/-- Multiplication by a unit followed by a nonzero power preserves finite
prime-ideal support. -/
theorem primeIdealFactorSupport_unit_mul_pow
    (u : (𝓞 K)ˣ) (x : 𝓞 K) {n : ℕ} (hn : n ≠ 0) :
    primeIdealFactorSupport ((u : 𝓞 K) * x ^ n) =
      primeIdealFactorSupport x := by
  calc
    primeIdealFactorSupport ((u : 𝓞 K) * x ^ n) =
        primeIdealFactorSupport (x ^ n) :=
      primeIdealFactorSupport_eq_of_associated
        (associated_unit_mul_left (x ^ n) (u : 𝓞 K) u.isUnit)
    _ = primeIdealFactorSupport x :=
      primeIdealFactorSupport_pow x hn

/-- In particular, a unit-times-square normalization preserves support. -/
theorem primeIdealFactorSupport_unit_mul_square
    (u : (𝓞 K)ˣ) (x : 𝓞 K) :
    primeIdealFactorSupport ((u : 𝓞 K) * x ^ 2) =
      primeIdealFactorSupport x :=
  primeIdealFactorSupport_unit_mul_pow u x (by norm_num)

/-- Strict support descent is unchanged by unit-times-square
normalization. -/
theorem primeIdealFactorSupport_unit_mul_square_ssubset_iff
    (u : (𝓞 K)ˣ) (x ξ : 𝓞 K) :
    primeIdealFactorSupport ((u : 𝓞 K) * x ^ 2) ⊂
        primeIdealFactorSupport ξ ↔
      primeIdealFactorSupport x ⊂ primeIdealFactorSupport ξ := by
  rw [primeIdealFactorSupport_unit_mul_square]

/-- A displayed ideal factorization `(b) = (a) * Q` gives inclusion of
the distinct prime-ideal supports. -/
lemma primeIdealFactorSupport_subset_of_span_factor
    {a b : 𝓞 K} {Q : Ideal (𝓞 K)}
    (hb : b ≠ 0)
    (hfactor : Ideal.span {b} = Ideal.span {a} * Q) :
    primeIdealFactorSupport a ⊆ primeIdealFactorSupport b := by
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
    simpa only [primeIdealFactorSupport, Multiset.mem_toFinset] using hP
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
  simpa only [primeIdealFactorSupport, Multiset.mem_toFinset] using hP''

/-- Witness form of strictness: a factor of `Q` absent from `(a)` is a
genuinely new prime-ideal factor of `(b)`. -/
lemma primeIdealFactorSupport_ssubset_of_span_factor_of_witness
    {a b : 𝓞 K} {Q P : Ideal (𝓞 K)}
    (hb : b ≠ 0)
    (hfactor : Ideal.span {b} = Ideal.span {a} * Q)
    (hPQ :
      P ∈ UniqueFactorizationMonoid.normalizedFactors Q)
    (hPa :
      P ∉ UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span {a})) :
    primeIdealFactorSupport a ⊂ primeIdealFactorSupport b := by
  have hmul : Ideal.span {a} * Q ≠ 0 := by
    rw [← hfactor]
    simpa only [Ideal.zero_eq_bot, ne_eq,
      Ideal.span_singleton_eq_bot] using hb
  have haI : Ideal.span {a} ≠ 0 := left_ne_zero_of_mul hmul
  have hQI : Q ≠ 0 := right_ne_zero_of_mul hmul
  have hsubset :=
    primeIdealFactorSupport_subset_of_span_factor hb hfactor
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
  · simpa only [primeIdealFactorSupport, Multiset.mem_toFinset] using hPa

/-- Coprime-factor form of strictness.  A nonunit ideal `Q` has a
normalized prime factor, and coprimality keeps it absent from `(a)`. -/
lemma primeIdealFactorSupport_ssubset_of_span_factor
    {a b : 𝓞 K} {Q : Ideal (𝓞 K)}
    (hb : b ≠ 0)
    (hfactor : Ideal.span {b} = Ideal.span {a} * Q)
    (hQ : Q ≠ ⊤)
    (hcop : IsCoprime (Ideal.span {a}) Q) :
    primeIdealFactorSupport a ⊂ primeIdealFactorSupport b := by
  have hmul : Ideal.span {a} * Q ≠ 0 := by
    rw [← hfactor]
    simpa only [Ideal.zero_eq_bot, ne_eq,
      Ideal.span_singleton_eq_bot] using hb
  have hQI : Q ≠ 0 := right_ne_zero_of_mul hmul
  have hQunit : ¬ IsUnit Q := by
    simpa only [Ideal.isUnit_iff] using hQ
  obtain ⟨P, hPQ⟩ :=
    UniqueFactorizationMonoid.exists_mem_normalizedFactors hQI hQunit
  apply primeIdealFactorSupport_ssubset_of_span_factor_of_witness
    hb hfactor hPQ
  intro hPa
  exact (Multiset.disjoint_left.mp
    (UniqueFactorizationMonoid.disjoint_normalizedFactors
      hcop.isRelPrime)) hPa hPQ

/-- Exact support drop for the square of a chosen generator of an ideal
factor.  This is the prime-independent support field required by
`ConjugationPowerReductionData`. -/
theorem square_support_strict_of_generator
    {ξ ρ : 𝓞 K} {I Q : Ideal (𝓞 K)}
    (hξ : ξ ≠ 0)
    (hgenerator : I = Ideal.span {ρ})
    (hfactor : Ideal.span {ξ} = I * Q)
    (hQ : Q ≠ ⊤)
    (hcop : IsCoprime I Q) :
    primeIdealFactorSupport (ρ ^ 2) ⊂
      primeIdealFactorSupport ξ := by
  rw [primeIdealFactorSupport_pow ρ (by norm_num : 2 ≠ 0)]
  apply primeIdealFactorSupport_ssubset_of_span_factor hξ
  · simpa only [hgenerator] using hfactor
  · exact hQ
  · simpa only [hgenerator] using hcop

end

end Fermat.Irregular.VandiverHistoricalSupportPrime
