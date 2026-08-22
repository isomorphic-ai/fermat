import Fermat.Descent.Irregular.VandiverHistoricalStatePrime

/-!
# Prime-generic cyclotomic simplification of Vandiver's equation (10)

For the concrete indices `a = 1` and `b = 2`, put

`A = ζ + ζ⁻¹`, `B = ζ² + ζ⁻²`.

Then

`2 - A = κ`, `A - B = κ * (A + 1)`, and
`2 - B = κ * (A + 2)`.

For every prime `p ≥ 5`, the last two factors are the explicit
cyclotomic units

`ζ⁻¹(1 + ζ + ζ²)` and `ζ⁻¹(1 + ζ)²`.

Substitution into the universal quadratic elimination and cancellation
of the nonzero common factor `κ` (or `κ²` when all three source equations
already contain `κ`) gives Vandiver's weighted equation (10b).
-/

namespace Fermat.Irregular.VandiverEquationTenPrime

open scoped NumberField nonZeroDivisors

open Fermat.Irregular.VandiverHistoricalDescent
open Fermat.Irregular.VandiverHistoricalPrime
open Fermat.Irregular.VandiverHistoricalStatePrime
open Fermat.Irregular.VandiverRealNormalizationPrime

noncomputable section

variable {K : Type} {p : ℕ} [Fact p.Prime]
  [Field K] [NumberField K] [NumberField.IsCMField K]
  [IsCyclotomicExtension {p} ℚ K]

/-- For a prime at least five, `2` is coprime to the prime. -/
lemma coprime_two_prime (hp5 : 5 ≤ p) : Nat.Coprime 2 p := by
  exact
    ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr (by
      intro hdvd
      have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      omega)).symm

/-- For a prime at least five, `3` is coprime to the prime. -/
lemma coprime_three_prime (hp5 : 5 ≤ p) : Nat.Coprime 3 p := by
  exact
    ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr (by
      intro hdvd
      have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
      omega)).symm

/-- The real cyclotomic trace `A = ζ + ζ⁻¹` used in equation (10). -/
def equationTenTraceOne
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) : 𝓞 K :=
  (hζ.unit' : 𝓞 K) + (hζ.unit'⁻¹ : (𝓞 K)ˣ)

/-- The real cyclotomic trace `B = ζ² + ζ⁻²` used in equation (10). -/
def equationTenTraceTwo
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) : 𝓞 K :=
  (hζ.unit' : 𝓞 K) ^ 2 +
    (hζ.unit'⁻¹ : (𝓞 K)ˣ) ^ 2

/-- The cyclotomic unit `ζ⁻¹(1 + ζ + ζ²) = A + 1`. -/
def equationTenTraceOneUnit
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) : (𝓞 K)ˣ :=
  hζ.unit'⁻¹ *
    (hζ.unit'_coe.geom_sum_isUnit
      (by omega) (coprime_three_prime hp5)).unit

/-- The cyclotomic unit `ζ⁻¹(1 + ζ)² = A + 2`. -/
def equationTenTraceTwoUnit
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) : (𝓞 K)ˣ :=
  hζ.unit'⁻¹ *
    (hζ.unit'_coe.geom_sum_isUnit
      (by omega) (coprime_two_prime hp5)).unit ^ 2

omit [NumberField.IsCMField K] [IsCyclotomicExtension {p} ℚ K] in
lemma equationTenTraceOneUnit_val
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    (equationTenTraceOneUnit hp5 hζ : 𝓞 K) =
      equationTenTraceOne hζ + 1 := by
  have huinv :
      (hζ.unit'⁻¹ : (𝓞 K)ˣ) *
          (hζ.unit' : 𝓞 K) = 1 := by
    rw [← Units.val_mul]
    simp
  have hgeom :
      (((hζ.unit'_coe.geom_sum_isUnit
        (by omega) (coprime_three_prime hp5)).unit :
          (𝓞 K)ˣ) : 𝓞 K) =
        1 + (hζ.unit' : 𝓞 K) +
          (hζ.unit' : 𝓞 K) ^ 2 := by
    rw [(hζ.unit'_coe.geom_sum_isUnit
      (by omega) (coprime_three_prime hp5)).unit_spec]
    norm_num [Finset.sum_range_succ]
  simp only [equationTenTraceOneUnit, Units.val_mul]
  rw [hgeom]
  simp only [equationTenTraceOne]
  linear_combination
    (1 + (hζ.unit' : 𝓞 K)) * huinv

omit [NumberField.IsCMField K] [IsCyclotomicExtension {p} ℚ K] in
lemma equationTenTraceTwoUnit_val
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    (equationTenTraceTwoUnit hp5 hζ : 𝓞 K) =
      equationTenTraceOne hζ + 2 := by
  have huinv :
      (hζ.unit'⁻¹ : (𝓞 K)ˣ) *
          (hζ.unit' : 𝓞 K) = 1 := by
    rw [← Units.val_mul]
    simp
  have hgeom :
      (((hζ.unit'_coe.geom_sum_isUnit
        (by omega) (coprime_two_prime hp5)).unit :
          (𝓞 K)ˣ) : 𝓞 K) =
        1 + (hζ.unit' : 𝓞 K) := by
    rw [(hζ.unit'_coe.geom_sum_isUnit
      (by omega) (coprime_two_prime hp5)).unit_spec]
    norm_num [Finset.sum_range_succ]
  simp only [equationTenTraceTwoUnit, Units.val_mul,
    Units.val_pow_eq_pow_val]
  rw [hgeom]
  simp only [equationTenTraceOne]
  linear_combination
    (2 + (hζ.unit' : 𝓞 K)) * huinv

omit [NumberField K] [NumberField.IsCMField K]
    [IsCyclotomicExtension {p} ℚ K] in
/-- The first concrete coefficient is Vandiver's `κ`. -/
lemma two_sub_equationTenTraceOne
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    2 - equationTenTraceOne hζ = kappa hζ := by
  have huinv :
      (hζ.unit' : 𝓞 K) *
          (hζ.unit'⁻¹ : (𝓞 K)ˣ) = 1 := by
    rw [← Units.val_mul]
    simp
  simp only [equationTenTraceOne, kappa]
  linear_combination -huinv

omit [NumberField.IsCMField K] [IsCyclotomicExtension {p} ℚ K] in
/-- The trace difference `A - B` is `κ` times `A + 1`. -/
lemma equationTenTraceOne_sub_two
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    equationTenTraceOne hζ - equationTenTraceTwo hζ =
      kappa hζ *
        (equationTenTraceOneUnit hp5 hζ : 𝓞 K) := by
  rw [equationTenTraceOneUnit_val hp5 hζ]
  have huinv :
      (hζ.unit' : 𝓞 K) *
          (hζ.unit'⁻¹ : (𝓞 K)ˣ) = 1 := by
    rw [← Units.val_mul]
    simp
  rw [← two_sub_equationTenTraceOne hζ]
  simp only [equationTenTraceOne, equationTenTraceTwo]
  linear_combination 2 * huinv

omit [NumberField.IsCMField K] [IsCyclotomicExtension {p} ℚ K] in
/-- The coefficient `2 - B` is `κ` times `A + 2`. -/
lemma two_sub_equationTenTraceTwo
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    2 - equationTenTraceTwo hζ =
      kappa hζ *
        (equationTenTraceTwoUnit hp5 hζ : 𝓞 K) := by
  rw [equationTenTraceTwoUnit_val hp5 hζ]
  have huinv :
      (hζ.unit' : 𝓞 K) *
          (hζ.unit'⁻¹ : (𝓞 K)ˣ) = 1 := by
    rw [← Units.val_mul]
    simp
  rw [← two_sub_equationTenTraceOne hζ]
  simp only [equationTenTraceOne, equationTenTraceTwo]
  linear_combination 2 * huinv

omit [NumberField K] [NumberField.IsCMField K]
    [IsCyclotomicExtension {p} ℚ K] in
/-- The integral unit attached to `ζ²` is the square of the unit attached
to `ζ`. -/
lemma powTwoPrimitiveRoot_unit
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    (hζ.pow_of_coprime 2 (coprime_two_prime hp5)).unit' =
      hζ.unit' ^ 2 := by
  ext
  rfl

omit [NumberField.IsCMField K] [IsCyclotomicExtension {p} ℚ K] in
/-- Changing the chosen primitive root from `ζ` to `ζ²` multiplies
Vandiver's `κ` by `A + 2`. -/
lemma kappa_powTwoPrimitiveRoot
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    kappa (hζ.pow_of_coprime 2 (coprime_two_prime hp5)) =
      kappa hζ *
        (equationTenTraceTwoUnit hp5 hζ : 𝓞 K) := by
  rw [← two_sub_equationTenTraceTwo hp5 hζ]
  simp only [kappa, powTwoPrimitiveRoot_unit hp5 hζ,
    Units.val_pow_eq_pow_val, equationTenTraceTwo]
  change
    (1 - (hζ.unit' : 𝓞 K) ^ 2) *
        (1 - (hζ.unit'⁻¹ : (𝓞 K)ˣ) ^ 2) =
      2 - ((hζ.unit' : 𝓞 K) ^ 2 +
        (hζ.unit'⁻¹ : (𝓞 K)ˣ) ^ 2)
  have huinv :
      (hζ.unit' : 𝓞 K) *
          (hζ.unit'⁻¹ : (𝓞 K)ˣ) = 1 := by
    rw [← Units.val_mul]
    simp
  have huinv2 :
      (hζ.unit' : 𝓞 K) ^ 2 *
          (hζ.unit'⁻¹ : (𝓞 K)ˣ) ^ 2 = 1 := by
    rw [← mul_pow, huinv, one_pow]
  ring_nf
  rw [huinv2]
  ring

/-- The trace `ζ + ζ⁻¹` is fixed by complex conjugation. -/
lemma equationTenTraceOne_real
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    NumberField.IsCMField.ringOfIntegersComplexConj K
        (equationTenTraceOne hζ) =
      equationTenTraceOne hζ := by
  have hz :
      NumberField.IsCMField.ringOfIntegersComplexConj K
          (hζ.unit' : 𝓞 K) =
        (hζ.unit'⁻¹ : (𝓞 K)ˣ) :=
    congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K)
      (unitsComplexConj_zeta hζ)
  have hzinv :
      NumberField.IsCMField.ringOfIntegersComplexConj K
          (hζ.unit'⁻¹ : (𝓞 K)ˣ) =
        (hζ.unit' : 𝓞 K) := by
    apply NumberField.RingOfIntegers.ext
    change NumberField.IsCMField.complexConj K ζ⁻¹ = ζ
    rw [map_inv₀,
      Fermat.Irregular.CyclotomicDiscriminantPrime.complexConj_zeta_inv hζ,
      inv_inv]
  simp only [equationTenTraceOne, map_add, hz, hzinv, add_comm]

/-- The unit `A + 1` is fixed by complex conjugation. -/
lemma equationTenTraceOneUnit_real
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    NumberField.IsCMField.unitsComplexConj K
        (equationTenTraceOneUnit hp5 hζ) =
      equationTenTraceOneUnit hp5 hζ := by
  apply Units.ext
  change
    NumberField.IsCMField.ringOfIntegersComplexConj K
        (equationTenTraceOneUnit hp5 hζ : 𝓞 K) =
      (equationTenTraceOneUnit hp5 hζ : 𝓞 K)
  rw [equationTenTraceOneUnit_val hp5 hζ, map_add,
    equationTenTraceOne_real hζ, map_one]

/-- The unit `A + 2` is fixed by complex conjugation. -/
lemma equationTenTraceTwoUnit_real
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    NumberField.IsCMField.unitsComplexConj K
        (equationTenTraceTwoUnit hp5 hζ) =
      equationTenTraceTwoUnit hp5 hζ := by
  apply Units.ext
  change
    NumberField.IsCMField.ringOfIntegersComplexConj K
        (equationTenTraceTwoUnit hp5 hζ : 𝓞 K) =
      (equationTenTraceTwoUnit hp5 hζ : 𝓞 K)
  rw [equationTenTraceTwoUnit_val hp5 hζ, map_add,
    equationTenTraceOne_real hζ, map_ofNat]

omit [NumberField.IsCMField K]
    [IsCyclotomicExtension {p} ℚ K] in
/-- Equation (10a) after the concrete trace identities and cancellation
of one common nonzero factor `κ`. -/
theorem equationTenB_cyclotomicSimplification
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (omega theta Xa Xb Xzero : 𝓞 K)
    (Ua Ub Uzero : (𝓞 K)ˣ)
    (ha :
      omega ^ 2 +
          equationTenTraceOne hζ * (omega * theta) +
          theta ^ 2 =
        Ua * Xa ^ p)
    (hb :
      omega ^ 2 +
          equationTenTraceTwo hζ * (omega * theta) +
          theta ^ 2 =
        Ub * Xb ^ p)
    (hzero :
      omega ^ 2 + 2 * (omega * theta) + theta ^ 2 =
        Uzero * Xzero) :
    (equationTenTraceTwoUnit hp5 hζ * Ua : (𝓞 K)ˣ) *
          Xa ^ p +
        (-Ub : (𝓞 K)ˣ) * Xb ^ p =
      (equationTenTraceOneUnit hp5 hζ * Uzero :
          (𝓞 K)ˣ) * Xzero := by
  have hkappa0 : kappa hζ ≠ 0 := by
    rw [kappa_eq_kappaUnit_mul_sq]
    exact mul_ne_zero (kappaUnit hζ).isUnit.ne_zero
      (pow_ne_zero 2
        (sub_ne_zero.mpr
          (hζ.unit'_coe.ne_one
            (Fact.out : Nat.Prime p).one_lt)))
  have helim :=
    equationTenA_quadraticElimination p
      omega theta
      (equationTenTraceOne hζ)
      (equationTenTraceTwo hζ)
      Ua Ub Uzero Xa Xb Xzero ha hb hzero
  rw [two_sub_equationTenTraceTwo hp5,
    two_sub_equationTenTraceOne,
    equationTenTraceOne_sub_two hp5] at helim
  apply mul_left_cancel₀ hkappa0
  calc
    kappa hζ *
        ((equationTenTraceTwoUnit hp5 hζ * Ua :
            (𝓞 K)ˣ) * Xa ^ p +
          (-Ub : (𝓞 K)ˣ) * Xb ^ p) =
        kappa hζ *
            (equationTenTraceTwoUnit hp5 hζ : 𝓞 K) *
            ((Ua : 𝓞 K) * Xa ^ p) -
          kappa hζ * ((Ub : 𝓞 K) * Xb ^ p) := by
      simp only [Units.val_mul, Units.val_neg]
      ring
    _ = kappa hζ *
          (equationTenTraceOneUnit hp5 hζ : 𝓞 K) *
          ((Uzero : 𝓞 K) * Xzero) := helim
    _ = kappa hζ *
        ((equationTenTraceOneUnit hp5 hζ * Uzero :
            (𝓞 K)ˣ) * Xzero) := by
      simp only [Units.val_mul]
      ring

omit [NumberField.IsCMField K]
    [IsCyclotomicExtension {p} ℚ K] in
/-- Equation (10a) when all three source equations already contain the
common ramified factor `κ`.  Cancellation of `κ²` gives the weighted
three-term equation (10b). -/
theorem equationTenB_commonKappa
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (omega theta Xa Xb Xzero : 𝓞 K)
    (Ua Ub Uzero : (𝓞 K)ˣ)
    (ha :
      omega ^ 2 +
          equationTenTraceOne hζ * (omega * theta) +
          theta ^ 2 =
        kappa hζ * (Ua * Xa ^ p))
    (hb :
      omega ^ 2 +
          equationTenTraceTwo hζ * (omega * theta) +
          theta ^ 2 =
        kappa hζ * (Ub * Xb ^ p))
    (hzero :
      omega ^ 2 + 2 * (omega * theta) + theta ^ 2 =
        kappa hζ * (Uzero * Xzero ^ p)) :
    (equationTenTraceTwoUnit hp5 hζ * Ua : (𝓞 K)ˣ) *
          Xa ^ p +
        (-Ub : (𝓞 K)ˣ) * Xb ^ p =
      (equationTenTraceOneUnit hp5 hζ * Uzero :
          (𝓞 K)ˣ) * Xzero ^ p := by
  have hkappa0 : kappa hζ ≠ 0 := by
    rw [kappa_eq_kappaUnit_mul_sq]
    exact mul_ne_zero (kappaUnit hζ).isUnit.ne_zero
      (pow_ne_zero 2
        (sub_ne_zero.mpr
          (hζ.unit'_coe.ne_one
            (Fact.out : Nat.Prime p).one_lt)))
  have ha' :
      omega ^ 2 +
          equationTenTraceOne hζ * (omega * theta) +
          theta ^ 2 =
        (kappa hζ * Ua) * Xa ^ p := by
    simpa only [mul_assoc] using ha
  have hb' :
      omega ^ 2 +
          equationTenTraceTwo hζ * (omega * theta) +
          theta ^ 2 =
        (kappa hζ * Ub) * Xb ^ p := by
    simpa only [mul_assoc] using hb
  have hzero' :
      omega ^ 2 + 2 * (omega * theta) + theta ^ 2 =
        (kappa hζ * Uzero) * Xzero ^ p := by
    simpa only [mul_assoc] using hzero
  have helim :=
    equationTenA_quadraticElimination p
      omega theta
      (equationTenTraceOne hζ)
      (equationTenTraceTwo hζ)
      (kappa hζ * Ua) (kappa hζ * Ub)
      (kappa hζ * Uzero)
      Xa Xb (Xzero ^ p) ha' hb' hzero'
  rw [two_sub_equationTenTraceTwo hp5,
    two_sub_equationTenTraceOne,
    equationTenTraceOne_sub_two hp5] at helim
  apply mul_left_cancel₀ (mul_ne_zero hkappa0 hkappa0)
  calc
    kappa hζ * kappa hζ *
        ((equationTenTraceTwoUnit hp5 hζ * Ua :
            (𝓞 K)ˣ) * Xa ^ p +
          (-Ub : (𝓞 K)ˣ) * Xb ^ p) =
        kappa hζ *
            (equationTenTraceTwoUnit hp5 hζ : 𝓞 K) *
            (kappa hζ * ((Ua : 𝓞 K) * Xa ^ p)) -
          kappa hζ *
            (kappa hζ * ((Ub : 𝓞 K) * Xb ^ p)) := by
      simp only [Units.val_mul, Units.val_neg]
      ring
    _ = kappa hζ *
          (equationTenTraceOneUnit hp5 hζ : 𝓞 K) *
          (kappa hζ *
            ((Uzero : 𝓞 K) * Xzero ^ p)) := by
      simpa only [mul_assoc] using helim
    _ = kappa hζ * kappa hζ *
        ((equationTenTraceOneUnit hp5 hζ * Uzero :
            (𝓞 K)ˣ) * Xzero ^ p) := by
      simp only [Units.val_mul]
      ring

end

end Fermat.Irregular.VandiverEquationTenPrime
