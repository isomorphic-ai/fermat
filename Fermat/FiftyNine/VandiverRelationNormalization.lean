import Fermat.Irregular.VandiverLemmaOne
import Fermat.FiftyNine.VandiverDeepPolynomial

/-!
# Positive normalization of Vandiver exponent relations at 59

Vandiver writes the left side of equation (3b) as an integer polynomial,
although the exponents in the preceding unit relation are arbitrary
integers.  This file supplies the omitted rigorous normalization.

For a positive relation exponent `t`, replace an integer exponent `a` by

`a⁺ + (t * 59^3 - 1) * a⁻`.

The new exponent is natural and differs from `a` by
`t * 59^3 * a⁻`.  Multiplying the original unit by the corresponding
`59^3`-rd power therefore gives a relation with only natural exponents.

The local hypothesis is preserved.  The proof starts with congruence modulo
`zeta - 1`; three successive 59th powers raise the depth from `1` to `59`,
then `117`, then `175`, which is more than the required `118`.

This also explains why no positivity assumption on Vandiver's original
integer exponents is needed.
-/

open scoped BigOperators NumberField

namespace Fermat.FiftyNine.VandiverRelationNormalization

noncomputable section

open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

/-- If two cyclotomic integers agree modulo `pi^m`, their 59th powers
agree modulo `pi^(m+58)`. -/
theorem zeta_sub_one_pow_add_fiftyEight_dvd_pow_sub_pow59
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 59)
    (m : ℕ) (hm : 1 ≤ m) (x y : 𝓞 K)
    (hxy : ((hzeta.unit' : 𝓞 K) - 1) ^ m ∣ x - y) :
    ((hzeta.unit' : 𝓞 K) - 1) ^ (m + 58) ∣
      x ^ 59 - y ^ 59 := by
  let pi : 𝓞 K := (hzeta.unit' : 𝓞 K) - 1
  obtain ⟨k, hk⟩ := hxy
  have hx : x = y + pi ^ m * k := by
    rw [sub_eq_iff_eq_add] at hk
    simpa only [pi, add_comm] using hk
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq
    (show Nat.Prime 59 by norm_num) y (pi ^ m * k)
  have hpdiv : pi ^ 58 ∣ (59 : 𝓞 K) := by
    simpa only [pi] using (associated_zeta_sub_one_pow_prime hzeta).dvd
  obtain ⟨q, hq⟩ := hpdiv
  have hlast : pi ^ (m + 58) ∣ (pi ^ m * k) ^ 59 := by
    have hle : m + 58 ≤ m * 59 := by omega
    have hpow : pi ^ (m + 58) ∣ pi ^ (m * 59) :=
      pow_dvd_pow pi hle
    rw [mul_pow, ← pow_mul]
    exact dvd_mul_of_dvd_left hpow _
  have hmixed : pi ^ (m + 58) ∣
      (59 : 𝓞 K) * y * (pi ^ m * k) * r := by
    refine ⟨q * y * k * r, ?_⟩
    rw [hq, pow_add]
    ring
  rw [hx, hr]
  convert dvd_add hlast hmixed using 1
  ring

/-- Every `59^3`-rd power of a unit satisfies Vandiver's depth-118
hypothesis. -/
theorem cube_prime_power_isVandiverDeep {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 59) (w : (𝓞 K)ˣ) :
    IsVandiverDeep (K := K) (p := 59) hzeta (w ^ (59 ^ 3)) := by
  let pi : 𝓞 K := (hzeta.unit' : 𝓞 K) - 1
  obtain ⟨c, hc⟩ :=
    exists_zeta_sub_one_dvd_sub_Int hzeta (w : 𝓞 K)
  have h1 : pi ^ 1 ∣ (w : 𝓞 K) - (c : 𝓞 K) := by
    simpa only [pi, pow_one] using hc
  have h59 := zeta_sub_one_pow_add_fiftyEight_dvd_pow_sub_pow59
    hzeta 1 (by omega) (w : 𝓞 K) (c : 𝓞 K) h1
  have h59' : pi ^ 59 ∣
      (w : 𝓞 K) ^ 59 - (c : 𝓞 K) ^ 59 := by
    simpa only [pi] using h59
  have h117 := zeta_sub_one_pow_add_fiftyEight_dvd_pow_sub_pow59
    hzeta 59 (by omega)
      ((w : 𝓞 K) ^ 59) ((c : 𝓞 K) ^ 59) h59'
  have h117' : pi ^ 117 ∣
      (w : 𝓞 K) ^ (59 ^ 2) - (c : 𝓞 K) ^ (59 ^ 2) := by
    simpa only [pi, ← pow_mul] using h117
  have h175 := zeta_sub_one_pow_add_fiftyEight_dvd_pow_sub_pow59
    hzeta 117 (by omega)
      ((w : 𝓞 K) ^ (59 ^ 2)) ((c : 𝓞 K) ^ (59 ^ 2)) h117'
  have h175' : pi ^ 175 ∣
      (w : 𝓞 K) ^ (59 ^ 3) - (c : 𝓞 K) ^ (59 ^ 3) := by
    change pi ^ (117 + 58) ∣
      ((w : 𝓞 K) ^ (59 ^ 2)) ^ 59 -
        ((c : 𝓞 K) ^ (59 ^ 2)) ^ 59 at h175
    convert h175 using 1 <;> norm_num [← pow_mul]
  have hpi118 : pi ^ 118 ∣
      (w : 𝓞 K) ^ (59 ^ 3) - (c : 𝓞 K) ^ (59 ^ 3) :=
    (pow_dvd_pow pi (by omega)).trans h175'
  have hneg : (1 : 𝓞 K) - hzeta.unit' ∣ pi := by
    refine ⟨-1, ?_⟩
    dsimp [pi]
    ring
  have hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 118 ∣
      (w : 𝓞 K) ^ (59 ^ 3) - (c : 𝓞 K) ^ (59 ^ 3) :=
    (pow_dvd_pow_of_dvd hneg 118).trans hpi118
  refine ⟨c ^ (59 ^ 2), ?_⟩
  simpa only [Units.val_pow_eq_pow_val, Int.cast_pow, ← pow_mul,
    show (59 ^ 2) * 59 = 59 ^ 3 by norm_num] using hdeep

/-- Vandiver depth is closed under multiplication. -/
theorem isVandiverDeep_mul {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 59) (u v : (𝓞 K)ˣ)
    (hu : IsVandiverDeep (K := K) (p := 59) hzeta u)
    (hv : IsVandiverDeep (K := K) (p := 59) hzeta v) :
    IsVandiverDeep (K := K) (p := 59) hzeta (u * v) := by
  obtain ⟨c, hc⟩ := hu
  obtain ⟨d, hd⟩ := hv
  refine ⟨c * d, ?_⟩
  have h1 := dvd_mul_of_dvd_left hc (v : 𝓞 K)
  have h2 := dvd_mul_of_dvd_right hd ((c : 𝓞 K) ^ 59)
  convert dvd_add h1 h2 using 1
  simp only [Units.val_mul, Int.cast_mul, mul_pow]
  ring

/-! ## Positive relation normalization -/

/-- The nonnegative replacement for an arbitrary integer exponent. -/
def normalizedRelationExponent59 (t : ℕ) (a : ℤ) : ℕ :=
  a.toNat + (t * 59 ^ 3 - 1) * (-a).toNat

/-- The replacement differs from the original exponent by exactly
`t * 59^3 * a⁻`. -/
theorem normalizedRelationExponent59_cast
    (t : ℕ) (ht : 0 < t) (a : ℤ) :
    (normalizedRelationExponent59 t a : ℤ) =
      a + (t * 59 ^ 3 : ℕ) * (-a).toNat := by
  have ht1 : 1 ≤ t := ht
  have hM : 1 ≤ t * 59 ^ 3 := by
    exact (show 1 ≤ 1 * 59 ^ 3 by norm_num).trans
      (Nat.mul_le_mul_right (59 ^ 3) ht1)
  have ha := Int.toNat_sub_toNat_neg a
  simp only [normalizedRelationExponent59]
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hM]
  push_cast
  calc
    (a.toNat : ℤ) + ((t : ℤ) * (59 : ℤ) ^ 3 - 1) *
        ((-a).toNat : ℤ) =
      ((a.toNat : ℤ) - ((-a).toNat : ℤ)) +
        (t : ℤ) * (59 : ℤ) ^ 3 * ((-a).toNat : ℤ) := by ring
    _ = a + (t : ℤ) * (59 : ℤ) ^ 3 *
        ((-a).toNat : ℤ) := by rw [ha]

/-- The correcting `59^3`-rd power attached to the negative exponents. -/
def relationNormalizationMultiplier59
    {G : Type*} [CommGroup G] (E : SourceIndex 59 → G)
    (a : SourceIndex 59 → ℤ) : G :=
  (∏ i, E i ^ (-a i).toNat) ^ (59 ^ 3)

/-- The unit with which the normalized positive relation is formed. -/
def normalizedRelationUnit59
    {G : Type*} [CommGroup G] (u : G) (E : SourceIndex 59 → G)
    (a : SourceIndex 59 → ℤ) : G :=
  u * relationNormalizationMultiplier59 E a

/-- The normalized unit satisfies the relation with the natural exponents
`normalizedRelationExponent59`. -/
theorem normalizedRelationUnit59_pow
    {G : Type*} [CommGroup G]
    (u : G) (E : SourceIndex 59 → G)
    (t : ℕ) (ht : 0 < t) (a : SourceIndex 59 → ℤ)
    (hrel : u ^ t = ∏ i, E i ^ a i) :
    (normalizedRelationUnit59 u E a) ^ t =
      ∏ i, E i ^ normalizedRelationExponent59 t (a i) := by
  rw [normalizedRelationUnit59, mul_pow, hrel,
    relationNormalizationMultiplier59, ← pow_mul]
  rw [← Finset.prod_pow Finset.univ (59 ^ 3 * t)
    (fun i ↦ E i ^ (-a i).toNat)]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← pow_mul]
  rw [← zpow_natCast (E i) (normalizedRelationExponent59 t (a i)),
    ← zpow_natCast (E i) ((-a i).toNat * ((59 ^ 3) * t)),
    ← zpow_add]
  congr 1
  rw [normalizedRelationExponent59_cast t ht (a i)]
  push_cast
  ring

/-- The positive normalization preserves Vandiver's deep hypothesis. -/
theorem normalizedRelationUnit59_isVandiverDeep {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 59)
    (u : (𝓞 K)ˣ) (E : SourceIndex 59 → (𝓞 K)ˣ)
    (a : SourceIndex 59 → ℤ)
    (hu : IsVandiverDeep (K := K) (p := 59) hzeta u) :
    IsVandiverDeep (K := K) (p := 59) hzeta
      (normalizedRelationUnit59 u E a) := by
  apply isVandiverDeep_mul hzeta
  · exact hu
  · exact cube_prime_power_isVandiverDeep hzeta
      (∏ i, E i ^ (-a i).toNat)

end

end Fermat.FiftyNine.VandiverRelationNormalization
