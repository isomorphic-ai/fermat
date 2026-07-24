import Fermat.Irregular.VandiverHistoricalPrime

/-!
# Prime-generic linear comparison in Vandiver's equation (10)

Vandiver compares the normalized equation-(8) factors at exponents one
and two.  If

`L₁ = η₁ * r₁^p` and `L₂ = η₂ * r₂^p`,

their two displayed linear equations imply

`L₁ - L₂ = ζ * (L₂ + θ)`.

Moreover, `(1 - ζ²) * (L₂ + θ) = ω + θ`.  Since `1 - ζ²` is a unit
times `ζ - 1`, one uniformizer can be cancelled from any supplied high
divisibility of `ω + θ`.  This calculation is independent of the prime
apart from the elementary condition `Coprime 2 p`.
-/

namespace Fermat.Irregular.VandiverLinearComparisonPrime

open scoped NumberField nonZeroDivisors

noncomputable section

variable {K : Type} {p : ℕ} [Fact p.Prime]
  [Field K] [NumberField K]

/-- Algebraic coefficient comparison between equation-(8) at exponents
one and two.  A depth-`D+1` divisibility of `ω+θ` gives depth `D` for the
difference of the two normalized coefficient sides. -/
theorem equationEight_one_two_coefficients_close
    (hp2 : Nat.Coprime 2 p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (D : ℕ) (ω θ r₁ r₂ : 𝓞 K) (η₁ η₂ : (𝓞 K)ˣ)
    (hhigh :
      ((hζ.unit' : 𝓞 K) - 1) ^ (D + 1) ∣ ω + θ)
    (heq₁ :
      ω + (hζ.unit' : 𝓞 K) * θ =
        (1 - (hζ.unit' : 𝓞 K)) * η₁ * r₁ ^ p)
    (heq₂ :
      ω + (hζ.unit' ^ 2 : (𝓞 K)ˣ) * θ =
        (1 - (hζ.unit' ^ 2 : (𝓞 K)ˣ)) * η₂ * r₂ ^ p) :
    ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
      (η₁ : 𝓞 K) * r₁ ^ p - (η₂ : 𝓞 K) * r₂ ^ p := by
  let π : 𝓞 K := (hζ.unit' : 𝓞 K) - 1
  let L₁ : 𝓞 K := (η₁ : 𝓞 K) * r₁ ^ p
  let L₂ : 𝓞 K := (η₂ : 𝓞 K) * r₂ ^ p
  have hπ0 : π ≠ 0 :=
    hζ.unit'_coe.sub_one_ne_zero
      (Fact.out : Nat.Prime p).one_lt
  obtain ⟨u, hu⟩ :=
    hζ.unit'_coe.associated_sub_one_pow_sub_one_of_coprime hp2
  let uden : (𝓞 K)ˣ := -u
  have hden :
      (1 : 𝓞 K) - (hζ.unit' : 𝓞 K) ^ 2 =
        (uden : 𝓞 K) * π := by
    dsimp [uden, π]
    calc
      (1 : 𝓞 K) - (hζ.unit' : 𝓞 K) ^ 2 =
          -((hζ.unit' : 𝓞 K) ^ 2 - 1) := by ring
      _ = -(((hζ.unit' : 𝓞 K) - 1) * (u : 𝓞 K)) := by
        rw [hu]
      _ = (-(u : 𝓞 K)) * ((hζ.unit' : 𝓞 K) - 1) := by ring
  have hsum₂ :
      ω + θ =
        (1 - (hζ.unit' : 𝓞 K) ^ 2) * (L₂ + θ) := by
    dsimp [L₂]
    have heq₂' :
        ω + (hζ.unit' : 𝓞 K) ^ 2 * θ =
          (1 - (hζ.unit' : 𝓞 K) ^ 2) *
            ((η₂ : 𝓞 K) * r₂ ^ p) := by
      simpa only [Units.val_pow_eq_pow_val, mul_assoc] using heq₂
    calc
      ω + θ =
          (ω + (hζ.unit' : 𝓞 K) ^ 2 * θ) +
            (1 - (hζ.unit' : 𝓞 K) ^ 2) * θ := by ring
      _ = (1 - (hζ.unit' : 𝓞 K) ^ 2) *
          ((η₂ : 𝓞 K) * r₂ ^ p) +
            (1 - (hζ.unit' : 𝓞 K) ^ 2) * θ := by
        rw [heq₂']
      _ = (1 - (hζ.unit' : 𝓞 K) ^ 2) *
          ((η₂ : 𝓞 K) * r₂ ^ p + θ) := by ring
  have hdiv₂ :
      π ^ D ∣ L₂ + θ := by
    have hraw :
        π ^ (D + 1) ∣ (uden : 𝓞 K) * (π * (L₂ + θ)) := by
      simpa only [hden, hsum₂, π, mul_assoc] using hhigh
    have hcancelUnit : π ^ (D + 1) ∣ π * (L₂ + θ) :=
      ((uden.isUnit.dvd_mul_left).mp hraw)
    have hcancel :
        π ^ D * π ∣ (L₂ + θ) * π := by
      simpa only [pow_succ, mul_comm] using hcancelUnit
    exact (mul_dvd_mul_iff_right hπ0).mp hcancel
  have hdifference :
      L₁ - L₂ = (hζ.unit' : 𝓞 K) * (L₂ + θ) := by
    apply mul_left_cancel₀ hπ0
    have heq₁' :
        ω + (hζ.unit' : 𝓞 K) * θ =
          (1 - (hζ.unit' : 𝓞 K)) * L₁ := by
      simpa only [L₁, mul_assoc] using heq₁
    have heq₂' :
        ω + (hζ.unit' : 𝓞 K) ^ 2 * θ =
          (1 - (hζ.unit' : 𝓞 K) ^ 2) * L₂ := by
      simpa only [L₂, Units.val_pow_eq_pow_val, mul_assoc] using heq₂
    dsimp only [π]
    linear_combination heq₁' - heq₂'
  dsimp only [L₁, L₂] at hdifference ⊢
  rw [hdifference]
  exact dvd_mul_of_dvd_right hdiv₂ _

end

end Fermat.Irregular.VandiverLinearComparisonPrime
