import Fermat.Descent.KummerIso.Correction

/-!
# Full-valuation Kummer correction

This file isolates the strongest coefficientwise correction theorem which is
valid without bounding the `p`-adic valuations of the coefficient family.

For a nonzero integer coefficient `B i`, put

`ν i = padicValInt p (B i)`

and write `B i = p ^ (ν i) * q i`.  Maximality of the valuation says that
`q i` is nonzero modulo `p`, so multiplication by the residues of the `q i`
is a diagonal automorphism over `ZMod p`.

The exact congruence needed before applying this automorphism is

`p ^ (ν i + 1) ∣ a i * B i`.

After cancelling `p ^ (ν i)`, this becomes
`p ∣ a i * q i`; the diagonal automorphism then gives `p ∣ a i`.

The fixed historical congruence `p ^ 3 ∣ a i * B i` supplies this precision
only when `ν i ≤ 2`.  The counterexample at the end records why full
normalization alone cannot remove that precision requirement.
-/

namespace Fermat.KummerIso.FullValuationCorrection

open scoped BigOperators
open Fermat.KummerIso.Correction

/-- A nonzero integral coefficient family.  Nonzeroness is necessary because
zero has no finite exact `p`-adic valuation with unit normalized quotient. -/
structure CoefficientFamily (p : ℕ) (ι : Type*) where
  B : ι → ℤ
  B_ne_zero : ∀ i, B i ≠ 0

namespace CoefficientFamily

variable {p : ℕ} {ι : Type*}

/-- The full `p`-adic valuation of one coefficient. -/
def valuation (C : CoefficientFamily p ι) (i : ι) : ℕ :=
  padicValInt p (C.B i)

/-- The quotient left after removing the full `p`-power from a coefficient. -/
noncomputable def normalizedQuotient
    (C : CoefficientFamily p ι) (i : ι) : ℤ :=
  Classical.choose (padicValInt_dvd (p := p) (C.B i))

/-- The defining exact-valuation factorization. -/
theorem B_eq_pow_mul_normalizedQuotient
    (C : CoefficientFamily p ι) (i : ι) :
    C.B i =
      (p : ℤ) ^ C.valuation i * C.normalizedQuotient i := by
  exact Classical.choose_spec (padicValInt_dvd (p := p) (C.B i))

/-- Removing the complete valuation leaves a quotient not divisible by `p`. -/
theorem normalizedQuotient_not_dvd
    (C : CoefficientFamily p ι) (hp : p.Prime) (i : ι) :
    ¬(p : ℤ) ∣ C.normalizedQuotient i := by
  letI : Fact p.Prime := ⟨hp⟩
  intro hdiv
  obtain ⟨q, hq⟩ := hdiv
  have hnext :
      (p : ℤ) ^ (C.valuation i + 1) ∣ C.B i := by
    refine ⟨q, ?_⟩
    calc
      C.B i =
          (p : ℤ) ^ C.valuation i *
            C.normalizedQuotient i :=
        C.B_eq_pow_mul_normalizedQuotient i
      _ = (p : ℤ) ^ C.valuation i * ((p : ℤ) * q) := by
        rw [hq]
      _ = (p : ℤ) ^ (C.valuation i + 1) * q := by
        rw [pow_succ]
        ring
  have hle :
      C.valuation i + 1 ≤ padicValInt p (C.B i) :=
    ((padicValInt_dvd_iff (p := p)
      (C.valuation i + 1) (C.B i)).mp hnext).resolve_left
      (C.B_ne_zero i)
  simp only [valuation] at hle
  exact (Nat.not_succ_le_self (C.valuation i)) hle

/-- The honest full-valuation diagonal gauge.  Its entries are automatically
units modulo `p`; there is no bounded-valuation or no-cube hypothesis. -/
noncomputable def diagonalGauge
    (C : CoefficientFamily p ι) (hp : p.Prime) :
    DiagonalGauge p ι where
  value i := C.normalizedQuotient i
  value_ne_zero i := by
    intro hzero
    exact C.normalizedQuotient_not_dvd hp i <|
      (CharP.intCast_eq_zero_iff
        (ZMod p) p (C.normalizedQuotient i)).mp hzero

@[simp]
theorem diagonalGauge_value
    (C : CoefficientFamily p ι) (hp : p.Prime) (i : ι) :
    (C.diagonalGauge hp).value i =
      (C.normalizedQuotient i : ZMod p) :=
  rfl

/-- Cancel the complete `p`-power from an adaptive-precision congruence. -/
theorem dvd_exponent_mul_normalizedQuotient
    (C : CoefficientFamily p ι) (hp : p.Prime)
    (a : ι → ℤ)
    (hprecision : ∀ i,
      (p : ℤ) ^ (C.valuation i + 1) ∣ a i * C.B i)
    (i : ι) :
    (p : ℤ) ∣ a i * C.normalizedQuotient i := by
  have hpPow : (p : ℤ) ^ C.valuation i ≠ 0 :=
    pow_ne_zero _ (Int.natCast_ne_zero.mpr hp.ne_zero)
  have hi :
      (p : ℤ) ^ C.valuation i * (p : ℤ) ∣
        (p : ℤ) ^ C.valuation i *
          (a i * C.normalizedQuotient i) := by
    rw [← pow_succ]
    convert hprecision i using 1
    rw [C.B_eq_pow_mul_normalizedQuotient i]
    ring
  exact (mul_dvd_mul_iff_left hpPow).mp hi

/-- Adaptive precision gives a zero in every corrected coordinate. -/
theorem corrected_coordinate_eq_zero_of_full_precision
    (C : CoefficientFamily p ι) (hp : p.Prime)
    (a : ι → ℤ)
    (hprecision : ∀ i,
      (p : ℤ) ^ (C.valuation i + 1) ∣ a i * C.B i)
    (i : ι) :
    (C.diagonalGauge hp).value i * (a i : ZMod p) = 0 := by
  have hzero :
      ((a i * C.normalizedQuotient i : ℤ) : ZMod p) = 0 :=
    (CharP.intCast_eq_zero_iff
      (ZMod p) p (a i * C.normalizedQuotient i)).mpr
        (C.dvd_exponent_mul_normalizedQuotient
          hp a hprecision i)
  simpa [mul_comm] using hzero

/-- Adaptive precision assembles into the corrected-zero vector equation. -/
theorem corrected_exponents_eq_zero_of_full_precision
    (C : CoefficientFamily p ι) (hp : p.Prime)
    (a : ι → ℤ)
    (hprecision : ∀ i,
      (p : ℤ) ^ (C.valuation i + 1) ∣ a i * C.B i) :
    (C.diagonalGauge hp).automorphism hp
      (fun i ↦ (a i : ZMod p)) = 0 := by
  funext i
  simpa using
    C.corrected_coordinate_eq_zero_of_full_precision
      hp a hprecision i

/-- Inverting the full-valuation automorphism proves divisibility of every
original exponent by `p`. -/
theorem exponents_dvd_of_full_precision
    (C : CoefficientFamily p ι) (hp : p.Prime)
    (a : ι → ℤ)
    (hprecision : ∀ i,
      (p : ℤ) ^ (C.valuation i + 1) ∣ a i * C.B i) :
    ∀ i, (p : ℤ) ∣ a i := by
  apply
    ((C.diagonalGauge hp).corrected_exponents_eq_zero_iff_dvd hp a).1
  exact C.corrected_exponents_eq_zero_of_full_precision
    hp a hprecision

end CoefficientFamily

/-- The exact source-independent logarithmic-derivative seam after replacing
the fixed cube cutoff by full-valuation normalization. -/
def PrimitiveRelationFullValuationCongruences
    {G ι : Type*} [CommGroup G] [Fintype ι]
    (p : ℕ) (u : G) (E : ι → G)
    (C : CoefficientFamily p ι) : Prop :=
  ∀ (t : ℕ) (a : ι → ℤ),
    0 < t →
    u ^ t = ∏ i, E i ^ a i →
    ¬(p ∣ t ∧ ∀ i, (p : ℤ) ∣ a i) →
    ∀ i, (p : ℤ) ^ (C.valuation i + 1) ∣ a i * C.B i

/-- Primitive-relation root extraction through the full-valuation
automorphism. -/
theorem isPower_of_primitive_relation_and_fullValuationCorrection
    {G ι : Type*} [CommGroup G] [Fintype ι]
    {p t : ℕ} (hp : p.Prime) (C : CoefficientFamily p ι)
    (u : G) (E : ι → G) (a : ι → ℤ)
    (hrel : u ^ t = ∏ i, E i ^ a i)
    (hprimitive : ¬(p ∣ t ∧ ∀ i, (p : ℤ) ∣ a i))
    (hprecision : ∀ i,
      (p : ℤ) ^ (C.valuation i + 1) ∣ a i * C.B i) :
    ∃ v : G, u = v ^ p := by
  apply isPower_of_primitive_relation_and_corrected_zero
    hp (C.diagonalGauge hp) u E a hrel hprimitive
  exact C.corrected_exponents_eq_zero_of_full_precision
    hp a hprecision

/-- Finite-index unit extraction with arbitrary nonzero coefficient
valuations.  This is the strongest generic algebraic repair: all remaining
arithmetic content is isolated in the adaptive-precision congruence. -/
theorem isPower_of_finiteIndex_family_and_fullValuationCorrection
    {G ι : Type*} [CommGroup G] [Fintype ι]
    {p : ℕ} (hp : p.Prime)
    (hpow : Function.Injective (fun x : G ↦ x ^ p))
    (u : G) (E : ι → G) (C : CoefficientFamily p ι)
    [hfinite : (Subgroup.closure (Set.range E)).FiniteIndex]
    (hprecision :
      PrimitiveRelationFullValuationCongruences p u E C) :
    ∃ v : G, u = v ^ p := by
  obtain ⟨a, ht, hrel⟩ :=
    Fermat.Irregular.VandiverUnitPower.exists_index_relation E u
  obtain ⟨t', a', ht', hrel', hprimitive⟩ :=
    Fermat.Irregular.VandiverUnitPower.exists_primitive_relation_of_relation
      hp.two_le hpow u E a ht hrel
  exact isPower_of_primitive_relation_and_fullValuationCorrection
    hp C u E a' hrel' hprimitive
      (hprecision t' a' ht' hrel' hprimitive)

/-- Fixed cube precision cannot support full normalization at arbitrary
valuation.  Here the normalized quotient of `B = 5^3` is the unit `1`, the
fixed cube congruence holds with exponent `a = 1`, but `5 ∤ a`. -/
theorem fixed_cube_precision_counterexample :
    ∃ (p : ℕ) (a B q : ℤ),
      p.Prime ∧
      B = (p : ℤ) ^ 3 * q ∧
      ¬(p : ℤ) ∣ q ∧
      (p : ℤ) ^ 3 ∣ a * B ∧
      ¬(p : ℤ) ∣ a := by
  refine ⟨5, 1, 125, 1, by norm_num, ?_⟩
  norm_num

end Fermat.KummerIso.FullValuationCorrection
