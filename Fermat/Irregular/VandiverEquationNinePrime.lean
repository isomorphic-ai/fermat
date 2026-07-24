import Fermat.Irregular.VandiverHistoricalStatePrime

/-!
# Prime-generic normalization of Vandiver's equation (9a)

For an odd prime `p = 2*r+1`, the factor-allocation theorem first gives

`(ζ-1)^((2*m-2)*p+1) ∣ ρ₊ - η*ρ₋`

for a `p`-th root of unity `η`.  Multiplying the two roots by `η^r` and
`η^(r+1)` makes this a literal difference while preserving both `p`-th
powers and the conjugation relation.

This is purely local normalization.  It uses no class-number hypothesis
and no Takagi existence theorem.
-/

namespace Fermat.Irregular.VandiverEquationNinePrime

open scoped NumberField nonZeroDivisors

open Fermat.Irregular.VandiverCriterion

noncomputable section

variable {K : Type} {p r : ℕ} [Fact p.Prime]
  [Field K] [NumberField K] [NumberField.IsCMField K]
  [IsCyclotomicExtension {p} ℚ K]

/-- Complex conjugation sends an integral `p`-th root of unity to its
inverse, represented as its `(p-1)`st power. -/
lemma ringOfIntegersComplexConj_nthRoot
    (η : Polynomial.nthRootsFinset p (1 : 𝓞 K)) :
    NumberField.IsCMField.ringOfIntegersComplexConj K (η : 𝓞 K) =
      (η : 𝓞 K) ^ (p - 1) := by
  have hp0 : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
  have hηpow : (η : 𝓞 K) ^ p = 1 :=
    (Polynomial.mem_nthRootsFinset
      (Fact.out : Nat.Prime p).pos (1 : 𝓞 K)).mp η.prop
  let u : (𝓞 K)ˣ :=
    ⟨(η : 𝓞 K), (η : 𝓞 K) ^ (p - 1),
      by
        rw [← pow_succ']
        simpa only [Nat.sub_add_cancel
          (Fact.out : Nat.Prime p).one_le] using hηpow,
      by
        rw [mul_comm, ← pow_succ']
        simpa only [Nat.sub_add_cancel
          (Fact.out : Nat.Prime p).one_le] using hηpow⟩
  have hupow : u ^ p = 1 := by
    apply Units.ext
    simpa only [u, Units.val_pow_eq_pow_val, Units.val_one] using hηpow
  have huTorsion : u ∈ NumberField.Units.torsion K := by
    rw [NumberField.Units.torsion, CommGroup.mem_torsion,
      isOfFinOrder_iff_pow_eq_one]
    exact ⟨p, (Fact.out : Nat.Prime p).pos, hupow⟩
  have hc : NumberField.IsCMField.unitsComplexConj K u = u⁻¹ := by
    simpa using NumberField.IsCMField.unitsComplexConj_torsion
      (K := K) (⟨u, huTorsion⟩ : NumberField.Units.torsion K)
  exact congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) hc

/-- Conjugation-compatible normalization of equation (9a), uniformly for
`p = 2*r+1`.

The supplied difference equation is the algebra immediately preceding
equation (9); its existence remains a separate, explicit input. -/
theorem equationNineA_normalized_conjugate
    (hp2 : p ≠ 2) (hr : p = 2 * r + 1)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (m : ℕ) (hm : 1 < m)
    (rhoPlus rhoMinus rhoZero : 𝓞 K) (epsilon : (𝓞 K)ˣ)
    (hdiff :
      rhoPlus ^ p - rhoMinus ^ p =
        epsilon *
          ((hζ.unit'.1 - 1) ^ (2 * m - 1) * rhoZero) ^ p)
    (hconj :
      NumberField.IsCMField.ringOfIntegersComplexConj K rhoPlus =
        rhoMinus)
    (hminus :
      ¬ hζ.unit'.1 - 1 ∣ rhoMinus) :
    ∃ normalizedPlus normalizedMinus : 𝓞 K,
      normalizedPlus ^ p = rhoPlus ^ p ∧
      normalizedMinus ^ p = rhoMinus ^ p ∧
      (hζ.unit'.1 - 1) ^ ((2 * m - 2) * p + 1) ∣
        normalizedPlus - normalizedMinus ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K
          normalizedPlus =
        normalizedMinus ∧
      ¬ hζ.unit'.1 - 1 ∣ normalizedMinus := by
  have hexp : 2 * m - 1 = (2 * m - 2) + 1 := by omega
  have hpOdd : Odd p :=
    (Fact.out : Nat.Prime p).odd_of_ne_two hp2
  have e' :
      rhoPlus ^ p + (-rhoMinus) ^ p =
        epsilon *
          ((hζ.unit'.1 - 1) ^ ((2 * m - 2) + 1) *
            rhoZero) ^ p := by
    rw [← hexp]
    simpa only [Odd.neg_pow hpOdd, sub_eq_add_neg] using hdiff
  have hy' : ¬ hζ.unit'.1 - 1 ∣ -rhoMinus := by
    simpa using hminus
  let η := zeta_sub_one_dvd_root hp2 hζ e' hy'
  have hηdiv :
      (hζ.unit'.1 - 1) ^ ((2 * m - 2) * p + 1) ∣
        rhoPlus - (η : 𝓞 K) * rhoMinus := by
    dsimp only [η]
    simpa only [sub_eq_add_neg, neg_mul, mul_comm] using
      (distinguishedFactor_highDivisibility hp2 hζ e' hy')
  have hηpow : (η : 𝓞 K) ^ p = 1 :=
    (Polynomial.mem_nthRootsFinset
      (Fact.out : Nat.Prime p).pos (1 : 𝓞 K)).mp η.prop
  have hηconj :
      NumberField.IsCMField.ringOfIntegersComplexConj K (η : 𝓞 K) =
        (η : 𝓞 K) ^ (p - 1) :=
    ringOfIntegersComplexConj_nthRoot η
  have hηunit : IsUnit (η : 𝓞 K) := by
    apply isUnit_iff_dvd_one.mpr
    refine ⟨(η : 𝓞 K) ^ (p - 1), ?_⟩
    rw [← pow_succ']
    simpa only [Nat.sub_add_cancel
      (Fact.out : Nat.Prime p).one_le] using hηpow.symm
  let normalizedPlus : 𝓞 K := (η : 𝓞 K) ^ r * rhoPlus
  let normalizedMinus : 𝓞 K :=
    (η : 𝓞 K) ^ (r + 1) * rhoMinus
  refine ⟨normalizedPlus, normalizedMinus, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [normalizedPlus]
    rw [mul_pow, ← pow_mul, Nat.mul_comm r p, pow_mul,
      hηpow, one_pow, one_mul]
  · dsimp [normalizedMinus]
    rw [mul_pow, ← pow_mul, Nat.mul_comm (r + 1) p, pow_mul,
      hηpow, one_pow, one_mul]
  · have hrewrite :
        normalizedPlus - normalizedMinus =
          (η : 𝓞 K) ^ r *
            (rhoPlus - (η : 𝓞 K) * rhoMinus) := by
      dsimp [normalizedPlus, normalizedMinus]
      rw [pow_succ']
      ring
    rw [hrewrite]
    exact dvd_mul_of_dvd_right hηdiv ((η : 𝓞 K) ^ r)
  · dsimp [normalizedPlus, normalizedMinus]
    rw [map_mul, map_pow, hηconj, hconj, ← pow_mul]
    have hrexp :
        (p - 1) * r = p * (r - 1) + (r + 1) := by
      have hrpos : 0 < r := by
        have := (Fact.out : Nat.Prime p).two_le
        omega
      rw [Nat.sub_mul, Nat.mul_sub]
      have hp_le : p ≤ p * r := by
        simpa only [mul_one] using
          Nat.mul_le_mul_left p (show 1 ≤ r by omega)
      have hr_le : r ≤ p * r := by
        simpa only [one_mul] using
          Nat.mul_le_mul_right r
            (show 1 ≤ p by exact (Fact.out : Nat.Prime p).pos)
      omega
    rw [hrexp, pow_add, pow_mul, hηpow, one_pow, one_mul]
  · dsimp [normalizedMinus]
    intro hram
    rcases hζ.zeta_sub_one_prime'.dvd_mul.mp hram with hroot | hρ
    · exact hζ.zeta_sub_one_prime'.not_unit
        (isUnit_of_dvd_unit hroot (hηunit.pow (r + 1)))
    · exact hminus hρ

end

end Fermat.Irregular.VandiverEquationNinePrime
