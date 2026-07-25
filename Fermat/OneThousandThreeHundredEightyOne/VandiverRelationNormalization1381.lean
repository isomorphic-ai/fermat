import Fermat.Irregular.VandiverLemmaOne
import Fermat.OneThousandThreeHundredEightyOne.VandiverDeepPolynomial

/-!
# Positive normalization of Vandiver exponent relations at 1381

Vandiver writes the left side of equation (3b) as an integer polynomial,
although the exponents in the preceding unit relation are arbitrary
integers. This file supplies the omitted rigorous normalization.

For a positive relation exponent `t`, replace an integer exponent `a` by

`a⁺ + (t * 1381^3 - 1) * a⁻`.

The new exponent is natural and differs from `a` by
`t * 1381^3 * a⁻`. Multiplying the original unit by the corresponding
`1381^3`-rd power therefore gives a relation with only natural exponents.

The local hypothesis is preserved. The proof starts with congruence modulo
`zeta - 1`; three successive 1381st powers raise the depth from `1` to
`1381`, then `2761`, then `4141`, which is more than the required `2762`.
-/

open scoped BigOperators NumberField

namespace Fermat.OneThousandThreeHundredEightyOne.VandiverRelationNormalization

noncomputable section

open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma

local instance : Fact (Nat.Prime 1381) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {1381} ℚ K]

/-- If two cyclotomic integers agree modulo `pi^m`, their 1381st powers
agree modulo `pi^(m+1380)`. -/
theorem zeta_sub_one_pow_add_oneThousandThreeHundredEighty_dvd_pow_sub_pow1381
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 1381)
    (m : ℕ) (hm : 1 ≤ m) (x y : 𝓞 K)
    (hxy : ((hzeta.unit' : 𝓞 K) - 1) ^ m ∣ x - y) :
    ((hzeta.unit' : 𝓞 K) - 1) ^ (m + 1380) ∣
      x ^ 1381 - y ^ 1381 := by
  let pi : 𝓞 K := (hzeta.unit' : 𝓞 K) - 1
  obtain ⟨k, hk⟩ := hxy
  have hx : x = y + pi ^ m * k := by
    rw [sub_eq_iff_eq_add] at hk
    simpa only [pi, add_comm] using hk
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq
    (show Nat.Prime 1381 by norm_num)
    y (pi ^ m * k)
  have h1380 : (1381 - 1 : ℕ) = 1380 := by norm_num
  have hCast1381 : (((1381 : ℕ) : 𝓞 K)) = (1381 : 𝓞 K) := by norm_num
  have hpdiv : pi ^ 1380 ∣ (1381 : 𝓞 K) := by
    simpa only [pi, h1380, hCast1381] using
      (associated_zeta_sub_one_pow_prime hzeta).dvd
  obtain ⟨q, hq⟩ := hpdiv
  have hlast : pi ^ (m + 1380) ∣ (pi ^ m * k) ^ 1381 := by
    have hle : m + 1380 ≤ m * 1381 := by omega
    have hpow : pi ^ (m + 1380) ∣ pi ^ (m * 1381) :=
      pow_dvd_pow pi hle
    rw [mul_pow, ← pow_mul]
    exact dvd_mul_of_dvd_left hpow _
  have hmixed : pi ^ (m + 1380) ∣
      (1381 : 𝓞 K) * y * (pi ^ m * k) * r := by
    refine ⟨q * y * k * r, ?_⟩
    rw [hq, pow_add]
    ac_rfl
  rw [hx, hr]
  convert dvd_add hlast hmixed using 1
  ring

/-- Every `1381^3`-rd power of a unit satisfies Vandiver's depth-2762
hypothesis. -/
theorem cube_prime_power_isVandiverDeep {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1381) (w : (𝓞 K)ˣ) :
    IsVandiverDeep (K := K) (p := 1381) hzeta (w ^ (1381 ^ 3)) := by
  let pi : 𝓞 K := (hzeta.unit' : 𝓞 K) - 1
  obtain ⟨c, hc⟩ :=
    exists_zeta_sub_one_dvd_sub_Int hzeta (w : 𝓞 K)
  have h1 : pi ^ 1 ∣ (w : 𝓞 K) - (c : 𝓞 K) := by
    simpa only [pi, pow_one] using hc
  have h1381 :=
    zeta_sub_one_pow_add_oneThousandThreeHundredEighty_dvd_pow_sub_pow1381
      hzeta 1 (by omega) (w : 𝓞 K) (c : 𝓞 K) h1
  have h1381' : pi ^ 1381 ∣
      (w : 𝓞 K) ^ 1381 - (c : 𝓞 K) ^ 1381 := by
    simpa only [pi] using h1381
  have h2761 :=
    zeta_sub_one_pow_add_oneThousandThreeHundredEighty_dvd_pow_sub_pow1381
      hzeta 1381 (by omega)
      ((w : 𝓞 K) ^ 1381) ((c : 𝓞 K) ^ 1381) h1381'
  have hExp2761 : (1381 + 1380 : ℕ) = 2761 := by norm_num
  have hSq1381 : (1381 * 1381 : ℕ) = 1381 ^ 2 := by norm_num
  have h2761' : pi ^ 2761 ∣
      (w : 𝓞 K) ^ (1381 ^ 2) - (c : 𝓞 K) ^ (1381 ^ 2) := by
    simpa only [pi, ← pow_mul, hExp2761, hSq1381] using h2761
  have h4141 :=
    zeta_sub_one_pow_add_oneThousandThreeHundredEighty_dvd_pow_sub_pow1381
      hzeta 2761 (by omega)
      ((w : 𝓞 K) ^ (1381 ^ 2)) ((c : 𝓞 K) ^ (1381 ^ 2)) h2761'
  have h4141' : pi ^ 4141 ∣
      (w : 𝓞 K) ^ (1381 ^ 3) - (c : 𝓞 K) ^ (1381 ^ 3) := by
    change pi ^ (2761 + 1380) ∣
      ((w : 𝓞 K) ^ (1381 ^ 2)) ^ 1381 -
        ((c : 𝓞 K) ^ (1381 ^ 2)) ^ 1381 at h4141
    convert h4141 using 1
    all_goals norm_num [← pow_mul]
  have hpi2762 : pi ^ 2762 ∣
      (w : 𝓞 K) ^ (1381 ^ 3) - (c : 𝓞 K) ^ (1381 ^ 3) :=
    (pow_dvd_pow pi (by omega)).trans h4141'
  have hneg : (1 : 𝓞 K) - hzeta.unit' ∣ pi := by
    refine ⟨-1, ?_⟩
    dsimp [pi]
    ring
  have hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 2762 ∣
      (w : 𝓞 K) ^ (1381 ^ 3) - (c : 𝓞 K) ^ (1381 ^ 3) :=
    (pow_dvd_pow_of_dvd hneg 2762).trans hpi2762
  refine ⟨c ^ (1381 ^ 2), ?_⟩
  simpa only [Units.val_pow_eq_pow_val, Int.cast_pow, ← pow_mul,
    show (1381 ^ 2) * 1381 = 1381 ^ 3 by norm_num] using hdeep

omit [NumberField K] [IsCyclotomicExtension {1381} ℚ K] in
/-- Vandiver depth is closed under multiplication. -/
theorem isVandiverDeep_mul {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1381) (u v : (𝓞 K)ˣ)
    (hu : IsVandiverDeep (K := K) (p := 1381) hzeta u)
    (hv : IsVandiverDeep (K := K) (p := 1381) hzeta v) :
    IsVandiverDeep (K := K) (p := 1381) hzeta (u * v) := by
  obtain ⟨c, hc⟩ := hu
  obtain ⟨d, hd⟩ := hv
  refine ⟨c * d, ?_⟩
  have h1 := dvd_mul_of_dvd_left hc (v : 𝓞 K)
  have h2 := dvd_mul_of_dvd_right hd ((c : 𝓞 K) ^ 1381)
  convert dvd_add h1 h2 using 1
  simp only [Units.val_mul, Int.cast_mul, mul_pow]
  ring

/-! ## Positive relation normalization -/

/-- The nonnegative replacement for an arbitrary integer exponent. -/
def normalizedRelationExponent1381 (t : ℕ) (a : ℤ) : ℕ :=
  a.toNat + (t * 1381 ^ 3 - 1) * (-a).toNat

/-- The replacement differs from the original exponent by exactly
`t * 1381^3 * a⁻`. -/
theorem normalizedRelationExponent1381_cast
    (t : ℕ) (ht : 0 < t) (a : ℤ) :
    (normalizedRelationExponent1381 t a : ℤ) =
      a + (t * 1381 ^ 3 : ℕ) * (-a).toNat := by
  have ht1 : 1 ≤ t := ht
  have hM : 1 ≤ t * 1381 ^ 3 := by
    exact (show 1 ≤ 1 * 1381 ^ 3 by norm_num).trans
      (Nat.mul_le_mul_right (1381 ^ 3) ht1)
  have ha := Int.toNat_sub_toNat_neg a
  simp only [normalizedRelationExponent1381]
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hM]
  push_cast
  calc
    (a.toNat : ℤ) + ((t : ℤ) * (1381 : ℤ) ^ 3 - 1) *
        ((-a).toNat : ℤ) =
      ((a.toNat : ℤ) - ((-a).toNat : ℤ)) +
        (t : ℤ) * (1381 : ℤ) ^ 3 * ((-a).toNat : ℤ) := by ring
    _ = a + (t : ℤ) * (1381 : ℤ) ^ 3 *
        ((-a).toNat : ℤ) := by rw [ha]

/-- The correcting `1381^3`-rd power attached to the negative exponents. -/
def relationNormalizationMultiplier1381
    {G : Type*} [CommGroup G] (E : SourceIndex 1381 → G)
    (a : SourceIndex 1381 → ℤ) : G :=
  (∏ i, E i ^ (-a i).toNat) ^ (1381 ^ 3)

/-- The unit with which the normalized positive relation is formed. -/
def normalizedRelationUnit1381
    {G : Type*} [CommGroup G] (u : G) (E : SourceIndex 1381 → G)
    (a : SourceIndex 1381 → ℤ) : G :=
  u * relationNormalizationMultiplier1381 E a

/-- The normalized unit satisfies the relation with the natural exponents
`normalizedRelationExponent1381`. -/
theorem normalizedRelationUnit1381_pow
    {G : Type*} [CommGroup G]
    (u : G) (E : SourceIndex 1381 → G)
    (t : ℕ) (ht : 0 < t) (a : SourceIndex 1381 → ℤ)
    (hrel : u ^ t = ∏ i, E i ^ a i) :
    (normalizedRelationUnit1381 u E a) ^ t =
      ∏ i, E i ^ normalizedRelationExponent1381 t (a i) := by
  rw [normalizedRelationUnit1381, mul_pow, hrel,
    relationNormalizationMultiplier1381, ← pow_mul]
  rw [← Finset.prod_pow Finset.univ (1381 ^ 3 * t)
    (fun i ↦ E i ^ (-a i).toNat)]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← pow_mul]
  rw [← zpow_natCast (E i) (normalizedRelationExponent1381 t (a i)),
    ← zpow_natCast (E i) ((-a i).toNat * ((1381 ^ 3) * t)),
    ← zpow_add]
  congr 1
  rw [normalizedRelationExponent1381_cast t ht (a i)]
  push_cast
  ring

/-- The positive normalization preserves Vandiver's deep hypothesis. -/
theorem normalizedRelationUnit1381_isVandiverDeep {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1381)
    (u : (𝓞 K)ˣ) (E : SourceIndex 1381 → (𝓞 K)ˣ)
    (a : SourceIndex 1381 → ℤ)
    (hu : IsVandiverDeep (K := K) (p := 1381) hzeta u) :
    IsVandiverDeep (K := K) (p := 1381) hzeta
      (normalizedRelationUnit1381 u E a) := by
  apply isVandiverDeep_mul hzeta
  · exact hu
  · exact cube_prime_power_isVandiverDeep hzeta
      (∏ i, E i ^ (-a i).toNat)

end

end Fermat.OneThousandThreeHundredEightyOne.VandiverRelationNormalization
