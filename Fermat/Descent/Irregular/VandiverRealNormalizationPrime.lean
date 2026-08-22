import Fermat.Descent.Irregular.VandiverHistoricalPrime

/-!
# Prime-generic real normalization in Vandiver's descent

For an odd prime written `p = 2 * r + 1`, multiplication by
`ζ ^ ((r + 1) * j)` removes a conjugation quotient `ζ ^ j`: the exponent
`r + 1` is the inverse of two modulo `p`.  Since this multiplier is a
`p`-th root of unity, it does not alter any displayed `p`-th power.

The same cyclotomic-unit calculation shows that a `p`-th root of a real
unit can be adjusted by a power of `ζ` so that the root itself is real.
These two constructions implement the reusable normalization interfaces
consumed by `VandiverHistoricalPrime.equationsSevenToTenReduction`.
-/

namespace Fermat.Irregular.VandiverRealNormalizationPrime

open scoped NumberField

open Fermat.Irregular.VandiverHistoricalPrime

noncomputable section

variable {K : Type} {p : ℕ} [Fact p.Prime]
  [Field K] [NumberField K] [NumberField.IsCMField K]
  [IsCyclotomicExtension {p} ℚ K]

omit [IsCyclotomicExtension {p} ℚ K] in
/-- Complex conjugation sends the integral unit attached to `ζ` to its
inverse. -/
lemma unitsComplexConj_zeta {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    NumberField.IsCMField.unitsComplexConj K hζ.unit' = hζ.unit'⁻¹ := by
  apply Units.ext
  apply NumberField.RingOfIntegers.ext
  change NumberField.IsCMField.complexConj K ζ = ζ⁻¹
  exact
    Fermat.Irregular.CyclotomicDiscriminantPrime.complexConj_zeta_inv hζ

/-- Adjust a generator by the inverse-of-two power of its conjugation
quotient. -/
def realAdjustedGenerator (r : ℕ)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (a : 𝓞 K) (j : ℕ) : 𝓞 K :=
  (hζ.unit' ^ ((r + 1) * j) : (𝓞 K)ˣ) * a

omit [NumberField K] [NumberField.IsCMField K]
    [IsCyclotomicExtension {p} ℚ K] in
/-- The root-of-unity adjustment leaves `p`-th powers unchanged. -/
lemma realAdjustedGenerator_pow (r : ℕ)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (a : 𝓞 K) (j : ℕ) :
    realAdjustedGenerator r hζ a j ^ p = a ^ p := by
  rw [realAdjustedGenerator, mul_pow]
  have hzpow : hζ.unit' ^ p = 1 := by
    ext
    exact hζ.pow_eq_one
  have hvpow : (hζ.unit' ^ ((r + 1) * j)) ^ p = 1 := by
    rw [← pow_mul]
    rw [show ((r + 1) * j) * p = p * ((r + 1) * j) by ring]
    rw [pow_mul, hzpow, one_pow]
  rw [← Units.val_pow_eq_pow_val, hvpow]
  simp

omit [IsCyclotomicExtension {p} ℚ K] in
/-- The inverse-of-two adjustment makes a generator literally real. -/
lemma realAdjustedGenerator_real {r : ℕ} (hr : p = 2 * r + 1)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (a : 𝓞 K) (j : ℕ)
    (ha : NumberField.IsCMField.ringOfIntegersComplexConj K a =
      (hζ.unit' ^ j : (𝓞 K)ˣ) * a) :
    NumberField.IsCMField.ringOfIntegersComplexConj K
      (realAdjustedGenerator r hζ a j) =
        realAdjustedGenerator r hζ a j := by
  let k := (r + 1) * j
  let v : (𝓞 K)ˣ := hζ.unit' ^ k
  have hzpow : hζ.unit' ^ p = 1 := by
    ext
    exact hζ.pow_eq_one
  have hv_sq : v ^ 2 = hζ.unit' ^ j := by
    dsimp [v, k]
    rw [← pow_mul]
    have hexp : ((r + 1) * j) * 2 = j + p * j := by
      rw [hr]
      ring
    rw [hexp, pow_add, pow_mul, hzpow, one_pow, mul_one]
  change NumberField.IsCMField.ringOfIntegersComplexConj K
      ((v : 𝓞 K) * a) = (v : 𝓞 K) * a
  rw [map_mul]
  have hvconj :
      NumberField.IsCMField.ringOfIntegersComplexConj K (v : 𝓞 K) =
        (v⁻¹ : (𝓞 K)ˣ) := by
    have hvconjU :
        NumberField.IsCMField.unitsComplexConj K v = v⁻¹ := by
      dsimp [v]
      rw [map_pow, unitsComplexConj_zeta hζ, inv_pow]
    exact congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) hvconjU
  rw [hvconj, ha]
  rw [← mul_assoc, ← Units.val_mul, ← hv_sq]
  congr 1
  rw [pow_two, ← mul_assoc]
  simp

/-- Prime-generic implementation of the real-generator normalization
interface. -/
def realGeneratorNormalizer {r : ℕ} (hr : p = 2 * r + 1)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    RealGeneratorNormalizer hζ where
  multiplier j := hζ.unit' ^ ((r + 1) * j)
  power_eq := by
    intro a j
    exact realAdjustedGenerator_pow r hζ a j
  real := by
    intro a j ha
    exact realAdjustedGenerator_real hr hζ a j ha

/-- A `p`-th root of a real unit can be adjusted by a power of `ζ`,
without changing its `p`-th power, so that the root itself is real. -/
lemma exists_real_unit_root (hp2 : 2 < p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (a v : (𝓞 K)ˣ) (hv : a = v ^ p) :
    ∃ w : (𝓞 K)ˣ, a = w ^ p ∧
      NumberField.IsCMField.unitsComplexConj K w = w := by
  obtain ⟨j, hj⟩ := unit_inv_conj_is_root_of_unity hζ v hp2
  let w : (𝓞 K)ˣ := v / hζ.unit' ^ j
  refine ⟨w, ?_, ?_⟩
  · dsimp [w]
    rw [div_pow, ← hv]
    have hzpow : hζ.unit' ^ p = 1 := by
      ext
      exact hζ.pow_eq_one
    rw [← pow_mul, show j * p = p * j by ring, pow_mul, hzpow, one_pow,
      div_one]
  · dsimp [w]
    rw [map_div, map_pow, unitsComplexConj_zeta hζ]
    rw [← div_eq_mul_inv] at hj
    have hmul : v = (hζ.unit' ^ j) ^ 2 *
        NumberField.IsCMField.unitsComplexConj K v :=
      div_eq_iff_eq_mul.mp hj
    rw [inv_pow, div_inv_eq_mul]
    calc
      NumberField.IsCMField.unitsComplexConj K v * hζ.unit' ^ j =
          (hζ.unit' ^ j) ^ 2 *
              NumberField.IsCMField.unitsComplexConj K v / hζ.unit' ^ j := by
        symm
        rw [pow_two]
        calc
          (hζ.unit' ^ j * hζ.unit' ^ j) *
                NumberField.IsCMField.unitsComplexConj K v / hζ.unit' ^ j =
              (NumberField.IsCMField.unitsComplexConj K v * hζ.unit' ^ j) *
                hζ.unit' ^ j / hζ.unit' ^ j := by ac_rfl
          _ = NumberField.IsCMField.unitsComplexConj K v * hζ.unit' ^ j :=
            mul_div_cancel_right _ _
      _ = v / hζ.unit' ^ j := by rw [← hmul]

/-- Prime-generic implementation of the real-unit-root normalization
interface. -/
theorem realUnitRootNormalization (hp2 : 2 < p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    RealUnitRootNormalization hζ :=
  exists_real_unit_root hp2 hζ

end

end Fermat.Irregular.VandiverRealNormalizationPrime
