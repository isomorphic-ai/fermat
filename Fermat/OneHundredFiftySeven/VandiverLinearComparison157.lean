import Fermat.OneHundredFiftySeven.VandiverCongruenceSupport157

/-!
# Comparing Vandiver's linear factors at indices one and two

Vandiver's equation (10) compares the two normalized linear factors

`(ω + ζ*θ)/(1 - ζ)` and `(ω + ζ²*θ)/(1 - ζ²)`.

Both differ from `-θ` by a quotient of the exceptionally divisible real
factor `ω + θ`.  This file turns that source observation into an exact
divisibility theorem, first algebraically and then at the historical
exponent `(2*m - 2)*157`.
-/

namespace Fermat.OneHundredFiftySeven.VandiverHistorical

open scoped NumberField nonZeroDivisors

open Fermat.Irregular.VandiverHistoricalDescent
open Fermat.Irregular.VandiverCriterion
open Fermat.Irregular.VandiverLemmaOne

noncomputable section

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {157} ℚ K]

local instance : Fact (Nat.Prime 157) := ⟨by norm_num⟩
local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 157) K (by norm_num)

/-- The full divisibility of the distinguished real factor.  The earlier
depth-158 wrapper is enough for Lemma 1; equation (10) uses the entire
source exponent. -/
theorem historicalState_omega_add_theta_fullHighDivisibility157
    {ζ : K} (hζ : IsPrimitiveRoot ζ 157) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    ((hζ.unit' : 𝓞 K) - 1) ^ ((2 * s.m - 1) * 157 + 1) ∣
      s.omega + s.theta := by
  let e := historicalState_regularEquation157 hζ s
  let hy := historicalState_theta_not_dvd157 hζ s
  have hroot := distinguishedRoot_eq_one_of_real157 hζ e hy hs.1 hs.2.1
  have hhigh := distinguishedFactor_highDivisibility
    (by norm_num : 157 ≠ 2) hζ e hy
  rw [hroot] at hhigh
  simpa only [oneNthRoot, mul_one] using hhigh

/-- Algebraic comparison of the coefficient sides of equation (8) at
`a = 1` and `a = 2`.

Writing `Lᵢ = ηᵢ*rᵢ^157`, the two equations imply

`L₁ - L₂ = ζ*(L₂ + θ)`.

But `(1 - ζ²)*(L₂ + θ) = ω + θ`.  Since `1 - ζ²` is a unit times
`ζ - 1`, cancelling one uniformizer from the high divisibility of `ω+θ`
gives the result. -/
theorem equationEight_one_two_coefficients_close157
    {ζ : K} (hζ : IsPrimitiveRoot ζ 157)
    (D : ℕ) (ω θ r₁ r₂ : 𝓞 K) (η₁ η₂ : (𝓞 K)ˣ)
    (hhigh :
      ((hζ.unit' : 𝓞 K) - 1) ^ (D + 1) ∣ ω + θ)
    (heq₁ :
      ω + (hζ.unit' : 𝓞 K) * θ =
        (1 - (hζ.unit' : 𝓞 K)) * η₁ * r₁ ^ 157)
    (heq₂ :
      ω + (hζ.unit' ^ 2 : (𝓞 K)ˣ) * θ =
        (1 - (hζ.unit' ^ 2 : (𝓞 K)ˣ)) * η₂ * r₂ ^ 157) :
    ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
      (η₁ : 𝓞 K) * r₁ ^ 157 - (η₂ : 𝓞 K) * r₂ ^ 157 := by
  let π : 𝓞 K := (hζ.unit' : 𝓞 K) - 1
  let L₁ : 𝓞 K := (η₁ : 𝓞 K) * r₁ ^ 157
  let L₂ : 𝓞 K := (η₂ : 𝓞 K) * r₂ ^ 157
  have hπ0 : π ≠ 0 :=
    hζ.unit'_coe.sub_one_ne_zero (by norm_num)
  obtain ⟨u, hu⟩ :=
    hζ.unit'_coe.associated_sub_one_pow_sub_one_of_coprime
      (by norm_num : Nat.Coprime 2 157)
  let uden : (𝓞 K)ˣ := -u
  have hden :
      (1 : 𝓞 K) - (hζ.unit' : 𝓞 K) ^ 2 =
        (uden : 𝓞 K) * π := by
    dsimp [uden, π]
    calc
      (1 : 𝓞 K) - (hζ.unit' : 𝓞 K) ^ 2 =
          -((hζ.unit' : 𝓞 K) ^ 2 - 1) := by ring
      _ = -(((hζ.unit' : 𝓞 K) - 1) * (u : 𝓞 K)) := by rw [hu]
      _ = (-(u : 𝓞 K)) * ((hζ.unit' : 𝓞 K) - 1) := by ring
  have hsum₂ :
      ω + θ =
        (1 - (hζ.unit' : 𝓞 K) ^ 2) * (L₂ + θ) := by
    dsimp [L₂]
    have heq₂' :
        ω + (hζ.unit' : 𝓞 K) ^ 2 * θ =
          (1 - (hζ.unit' : 𝓞 K) ^ 2) *
            ((η₂ : 𝓞 K) * r₂ ^ 157) := by
      simpa only [Units.val_pow_eq_pow_val, mul_assoc] using heq₂
    calc
      ω + θ =
          (ω + (hζ.unit' : 𝓞 K) ^ 2 * θ) +
            (1 - (hζ.unit' : 𝓞 K) ^ 2) * θ := by ring
      _ = (1 - (hζ.unit' : 𝓞 K) ^ 2) *
          ((η₂ : 𝓞 K) * r₂ ^ 157) +
            (1 - (hζ.unit' : 𝓞 K) ^ 2) * θ := by rw [heq₂']
      _ = (1 - (hζ.unit' : 𝓞 K) ^ 2) *
          ((η₂ : 𝓞 K) * r₂ ^ 157 + θ) := by ring
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

/-- Historical specialization at the full equation-(10) depth
`(2*m - 2)*157`. -/
theorem historicalEquationEight_one_two_coefficients_close157
    {ζ : K} (hζ : IsPrimitiveRoot ζ 157)
    (s : HistoricalState hζ) (hs : RealSourceAdmissible hζ s)
    (r₁ r₂ : 𝓞 K) (η₁ η₂ : (𝓞 K)ˣ)
    (heq₁ :
      s.omega + (hζ.unit' : 𝓞 K) * s.theta =
        (1 - (hζ.unit' : 𝓞 K)) * η₁ * r₁ ^ 157)
    (heq₂ :
      s.omega + (hζ.unit' ^ 2 : (𝓞 K)ˣ) * s.theta =
        (1 - (hζ.unit' ^ 2 : (𝓞 K)ˣ)) * η₂ * r₂ ^ 157) :
    ((hζ.unit' : 𝓞 K) - 1) ^ ((2 * s.m - 2) * 157) ∣
      (η₁ : 𝓞 K) * r₁ ^ 157 - (η₂ : 𝓞 K) * r₂ ^ 157 := by
  let D : ℕ := (2 * s.m - 2) * 157
  have hfull :=
    historicalState_omega_add_theta_fullHighDivisibility157 hζ s hs
  have hle : D + 1 ≤ (2 * s.m - 1) * 157 + 1 := by
    dsimp [D]
    omega
  have hhigh :
      ((hζ.unit' : 𝓞 K) - 1) ^ (D + 1) ∣
        s.omega + s.theta :=
    (pow_dvd_pow ((hζ.unit' : 𝓞 K) - 1) hle).trans hfull
  simpa only [D] using
    equationEight_one_two_coefficients_close157
      hζ D s.omega s.theta r₁ r₂ η₁ η₂ hhigh heq₁ heq₂

end

end Fermat.OneHundredFiftySeven.VandiverHistorical
