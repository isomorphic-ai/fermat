import Fermat.Descent.Irregular.VandiverGeneratorSupportPrime
import Fermat.Descent.Irregular.VandiverRealNormalizationPrime

/-!
# Prime-generic conjugate equation-(8) pairs

After the Takagi--Furtwängler step supplies equation (8) for one
root-of-unity coefficient `t`, complex conjugation supplies the equation
at `t⁻¹`.  This file isolates that elementary passage, including
nondivisibility of both generators by the cyclotomic uniformizer and the
quadratic product identity used in equation (10).

The genuinely deep Takagi input is kept visible: a caller must supply the
single plus equation, a real coefficient unit, and nonramification of its
generator.  No exponent-specific reflection theorem is postulated here.
-/

namespace Fermat.Irregular.VandiverTakagiPairPrime

open scoped NumberField

open Fermat.Irregular.VandiverRealNormalizationPrime

noncomputable section

variable {K : Type} {p : ℕ} [Fact p.Prime]
  [Field K] [NumberField K] [NumberField.IsCMField K]
  [IsCyclotomicExtension {p} ℚ K]

omit [IsCyclotomicExtension {p} ℚ K] in
/-- Complex conjugation changes the standard uniformizer `ζ-1` by the
explicit unit `-ζ⁻¹`. -/
lemma ringOfIntegersComplexConj_zeta_sub_one
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    NumberField.IsCMField.ringOfIntegersComplexConj K
        ((hζ.unit' : 𝓞 K) - 1) =
      ((-hζ.unit'⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
        ((hζ.unit' : 𝓞 K) - 1) := by
  rw [map_sub, map_one]
  have hconjζ :
      NumberField.IsCMField.ringOfIntegersComplexConj K
          (hζ.unit' : 𝓞 K) =
        (hζ.unit'⁻¹ : (𝓞 K)ˣ) :=
    congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K)
      (unitsComplexConj_zeta hζ)
  rw [hconjζ]
  have hinv :
      (hζ.unit'⁻¹ : (𝓞 K)ˣ) *
          (hζ.unit' : 𝓞 K) = 1 := by
    rw [← Units.val_mul]
    simp
  simp only [Units.val_neg, neg_mul, mul_sub, hinv]
  ring

omit [IsCyclotomicExtension {p} ℚ K] in
/-- Divisibility by a power of `ζ-1` is preserved by complex
conjugation. -/
lemma zeta_sub_one_pow_dvd_conj_of_dvd
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (n : ℕ) (a : 𝓞 K)
    (h : ((hζ.unit' : 𝓞 K) - 1) ^ n ∣ a) :
    ((hζ.unit' : 𝓞 K) - 1) ^ n ∣
      NumberField.IsCMField.ringOfIntegersComplexConj K a := by
  obtain ⟨b, rfl⟩ := h
  rw [map_mul, map_pow,
    ringOfIntegersComplexConj_zeta_sub_one, mul_pow]
  refine
    ⟨(((-hζ.unit'⁻¹ : (𝓞 K)ˣ) ^ n : (𝓞 K)ˣ) : 𝓞 K) *
        NumberField.IsCMField.ringOfIntegersComplexConj K b, ?_⟩
  simp only [Units.val_pow_eq_pow_val]
  ring

/-- A conjugate pair of equation-(8) generators at `t` and `t⁻¹`.
Nonramification is measured using the chosen primitive root `ζ`, while
`t` may be any unit whose conjugate is its inverse (in particular a power
of `ζ`). -/
structure ConjugateEquationEightPair
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (omega theta : 𝓞 K) (t : (𝓞 K)ˣ) where
  rplus : 𝓞 K
  rminus : 𝓞 K
  coefficient : (𝓞 K)ˣ
  coefficient_real :
    NumberField.IsCMField.unitsComplexConj K coefficient = coefficient
  equation_plus :
    omega + (t : 𝓞 K) * theta =
      (1 - (t : 𝓞 K)) * coefficient * rplus ^ p
  equation_minus :
    omega + (t⁻¹ : (𝓞 K)ˣ) * theta =
      (1 - (t⁻¹ : (𝓞 K)ˣ)) * coefficient * rminus ^ p
  conjugate :
    NumberField.IsCMField.ringOfIntegersComplexConj K rplus = rminus
  rplus_not_ramified :
    ¬ (hζ.unit' : 𝓞 K) - 1 ∣ rplus
  rminus_not_ramified :
    ¬ (hζ.unit' : 𝓞 K) - 1 ∣ rminus

omit [IsCyclotomicExtension {p} ℚ K] in
/-- A single real-unit equation-(8) witness supplies its full conjugate
pair. -/
theorem conjugateEquationEightPair_of_plus
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {omega theta rho : 𝓞 K} (t eta : (𝓞 K)ˣ)
    (homega :
      NumberField.IsCMField.ringOfIntegersComplexConj K omega = omega)
    (htheta :
      NumberField.IsCMField.ringOfIntegersComplexConj K theta = theta)
    (ht :
      NumberField.IsCMField.unitsComplexConj K t = t⁻¹)
    (heta :
      NumberField.IsCMField.unitsComplexConj K eta = eta)
    (hplus :
      omega + (t : 𝓞 K) * theta =
        (1 - (t : 𝓞 K)) * eta * rho ^ p)
    (hrho : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ rho) :
    Nonempty (ConjugateEquationEightPair hζ omega theta t) := by
  let rhominus : 𝓞 K :=
    NumberField.IsCMField.ringOfIntegersComplexConj K rho
  have htval :
      NumberField.IsCMField.ringOfIntegersComplexConj K (t : 𝓞 K) =
        (t⁻¹ : (𝓞 K)ˣ) :=
    congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) ht
  have hetaval :
      NumberField.IsCMField.ringOfIntegersComplexConj K (eta : 𝓞 K) =
        eta :=
    congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) heta
  have hminus :
      omega + (t⁻¹ : (𝓞 K)ˣ) * theta =
        (1 - (t⁻¹ : (𝓞 K)ˣ)) * eta * rhominus ^ p := by
    have hc := congrArg
      (NumberField.IsCMField.ringOfIntegersComplexConj K) hplus
    simpa only [map_add, map_mul, map_sub, map_one, map_pow,
      homega, htheta, htval, hetaval, rhominus] using hc
  have hrhominus :
      ¬ (hζ.unit' : 𝓞 K) - 1 ∣ rhominus := by
    intro hdiv
    have hc := zeta_sub_one_pow_dvd_conj_of_dvd
      hζ 1 rhominus (by simpa only [pow_one] using hdiv)
    have hcc :
        NumberField.IsCMField.ringOfIntegersComplexConj K rhominus =
          rho := by
      dsimp [rhominus]
      apply NumberField.RingOfIntegers.ext
      exact NumberField.IsCMField.complexConj_apply_apply K rho
    exact hrho (by simpa only [pow_one, hcc] using hc)
  exact
    ⟨{ rplus := rho
       rminus := rhominus
       coefficient := eta
       coefficient_real := heta
       equation_plus := hplus
       equation_minus := hminus
       conjugate := rfl
       rplus_not_ramified := hrho
       rminus_not_ramified := hrhominus }⟩

omit [IsCyclotomicExtension {p} ℚ K] in
/-- Complex conjugation sends every power of the chosen primitive root to
its inverse. -/
lemma unitsComplexConj_zeta_pow
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (a : ℕ) :
    NumberField.IsCMField.unitsComplexConj K (hζ.unit' ^ a) =
      (hζ.unit' ^ a)⁻¹ := by
  rw [map_pow, unitsComplexConj_zeta hζ, inv_pow]

omit [IsCyclotomicExtension {p} ℚ K] in
/-- Power-of-`ζ` specialization of
`conjugateEquationEightPair_of_plus`. -/
theorem conjugateEquationEightPair_of_zetaPow_plus
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {omega theta rho : 𝓞 K} (a : ℕ) (eta : (𝓞 K)ˣ)
    (homega :
      NumberField.IsCMField.ringOfIntegersComplexConj K omega = omega)
    (htheta :
      NumberField.IsCMField.ringOfIntegersComplexConj K theta = theta)
    (heta :
      NumberField.IsCMField.unitsComplexConj K eta = eta)
    (hplus :
      omega + (hζ.unit' ^ a : (𝓞 K)ˣ) * theta =
        (1 - (hζ.unit' ^ a : (𝓞 K)ˣ)) * eta * rho ^ p)
    (hrho : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ rho) :
    Nonempty
      (ConjugateEquationEightPair hζ omega theta (hζ.unit' ^ a)) :=
  conjugateEquationEightPair_of_plus hζ
    (hζ.unit' ^ a) eta homega htheta
    (unitsComplexConj_zeta_pow hζ a) heta hplus hrho

namespace ConjugateEquationEightPair

variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)
  (omega theta : 𝓞 K) (t : (𝓞 K)ˣ)
  (d : ConjugateEquationEightPair hζ omega theta t)

omit [IsCyclotomicExtension {p} ℚ K] in
/-- Multiplying the two conjugate equations gives the quadratic identity
used in Vandiver's equation (10). -/
lemma quadraticEquation :
    omega ^ 2 +
        ((t : 𝓞 K) + (t⁻¹ : (𝓞 K)ˣ)) *
          (omega * theta) +
        theta ^ 2 =
      ((1 - (t : 𝓞 K)) * (1 - (t⁻¹ : (𝓞 K)ˣ))) *
        ((d.coefficient ^ 2 : (𝓞 K)ˣ) *
          (d.rplus * d.rminus) ^ p) := by
  have htinv :
      (t : 𝓞 K) * (t⁻¹ : (𝓞 K)ˣ) = 1 := by
    rw [← Units.val_mul]
    simp
  calc
    omega ^ 2 +
          ((t : 𝓞 K) + (t⁻¹ : (𝓞 K)ˣ)) *
            (omega * theta) +
          theta ^ 2 =
        (omega + (t : 𝓞 K) * theta) *
          (omega + (t⁻¹ : (𝓞 K)ˣ) * theta) := by
      linear_combination -(theta ^ 2) * htinv
    _ = ((1 - (t : 𝓞 K)) * d.coefficient * d.rplus ^ p) *
        ((1 - (t⁻¹ : (𝓞 K)ˣ)) * d.coefficient *
          d.rminus ^ p) := by
      rw [d.equation_plus, d.equation_minus]
    _ = ((1 - (t : 𝓞 K)) * (1 - (t⁻¹ : (𝓞 K)ˣ))) *
        ((d.coefficient ^ 2 : (𝓞 K)ˣ) *
          (d.rplus * d.rminus) ^ p) := by
      simp only [Units.val_pow_eq_pow_val, mul_pow]
      ring

omit [IsCyclotomicExtension {p} ℚ K] in
/-- The product of the two conjugate generators is literally real. -/
lemma product_real :
    NumberField.IsCMField.ringOfIntegersComplexConj K
        (d.rplus * d.rminus) =
      d.rplus * d.rminus := by
  have hminus :
      NumberField.IsCMField.ringOfIntegersComplexConj K d.rminus =
        d.rplus := by
    have hcc := congrArg
      (NumberField.IsCMField.ringOfIntegersComplexConj K) d.conjugate
    have hinvol :
        NumberField.IsCMField.ringOfIntegersComplexConj K
            (NumberField.IsCMField.ringOfIntegersComplexConj K
              d.rplus) =
          d.rplus := by
      apply NumberField.RingOfIntegers.ext
      exact NumberField.IsCMField.complexConj_apply_apply K d.rplus
    simpa only [hinvol] using hcc.symm
  rw [map_mul, d.conjugate, hminus, mul_comm]

end ConjugateEquationEightPair

end

end Fermat.Irregular.VandiverTakagiPairPrime
