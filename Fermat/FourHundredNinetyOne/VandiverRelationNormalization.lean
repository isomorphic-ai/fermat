import Fermat.Irregular.VandiverLemmaOne
import Fermat.FourHundredNinetyOne.VandiverDeepPolynomial

/-!
# Positive normalization of Vandiver exponent relations at 491

Vandiver writes the left side of equation (3b) as an integer polynomial,
although the exponents in the preceding unit relation are arbitrary
integers.  This file supplies the omitted rigorous normalization.

For a positive relation exponent `t`, replace an integer exponent `a` by

`a⁺ + (t * 491^3 - 1) * a⁻`.

The new exponent is natural and differs from `a` by
`t * 491^3 * a⁻`.  Multiplying the original unit by the corresponding
`491^3`-rd power therefore gives a relation with only natural exponents.

The local hypothesis is preserved.  The proof starts with congruence modulo
`zeta - 1`; three successive 491st powers raise the depth from `1` to `491`,
then `981`, then `1471`, which is more than the required `982`.
-/

open scoped BigOperators NumberField

namespace Fermat.FourHundredNinetyOne.VandiverRelationNormalization

noncomputable section

open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma

local instance : Fact (Nat.Prime 491) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {491} ℚ K]

/-- If two cyclotomic integers agree modulo `pi^m`, their 491st powers
agree modulo `pi^(m+490)`. -/
theorem zeta_sub_one_pow_add_fourHundredNinety_dvd_pow_sub_pow491
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 491)
    (m : ℕ) (hm : 1 ≤ m) (x y : 𝓞 K)
    (hxy : ((hzeta.unit' : 𝓞 K) - 1) ^ m ∣ x - y) :
    ((hzeta.unit' : 𝓞 K) - 1) ^ (m + 490) ∣
      x ^ 491 - y ^ 491 := by
  let pi : 𝓞 K := (hzeta.unit' : 𝓞 K) - 1
  obtain ⟨k, hk⟩ := hxy
  have hx : x = y + pi ^ m * k := by
    rw [sub_eq_iff_eq_add] at hk
    simpa only [pi, add_comm] using hk
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq
    (show Nat.Prime 491 by norm_num) y (pi ^ m * k)
  have h490 : (491 - 1 : ℕ) = 490 := by norm_num
  have hCast491 : (((491 : ℕ) : 𝓞 K)) = (491 : 𝓞 K) := by norm_num
  have hpdiv : pi ^ 490 ∣ (491 : 𝓞 K) := by
    simpa only [pi, h490, hCast491] using
      (associated_zeta_sub_one_pow_prime hzeta).dvd
  obtain ⟨q, hq⟩ := hpdiv
  have hlast : pi ^ (m + 490) ∣ (pi ^ m * k) ^ 491 := by
    have hle : m + 490 ≤ m * 491 := by omega
    have hpow : pi ^ (m + 490) ∣ pi ^ (m * 491) :=
      pow_dvd_pow pi hle
    rw [mul_pow, ← pow_mul]
    exact dvd_mul_of_dvd_left hpow _
  have hmixed : pi ^ (m + 490) ∣
      (491 : 𝓞 K) * y * (pi ^ m * k) * r := by
    refine ⟨q * y * k * r, ?_⟩
    rw [hq, pow_add]
    ring
  rw [hx, hr]
  convert dvd_add hlast hmixed using 1
  ring

/-- Every `491^3`-rd power of a unit satisfies Vandiver's depth-982
hypothesis. -/
theorem cube_prime_power_isVandiverDeep {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491) (w : (𝓞 K)ˣ) :
    IsVandiverDeep (K := K) (p := 491) hzeta (w ^ (491 ^ 3)) := by
  let pi : 𝓞 K := (hzeta.unit' : 𝓞 K) - 1
  obtain ⟨c, hc⟩ :=
    exists_zeta_sub_one_dvd_sub_Int hzeta (w : 𝓞 K)
  have h1 : pi ^ 1 ∣ (w : 𝓞 K) - (c : 𝓞 K) := by
    simpa only [pi, pow_one] using hc
  have h491 := zeta_sub_one_pow_add_fourHundredNinety_dvd_pow_sub_pow491
    hzeta 1 (by omega) (w : 𝓞 K) (c : 𝓞 K) h1
  have h491' : pi ^ 491 ∣
      (w : 𝓞 K) ^ 491 - (c : 𝓞 K) ^ 491 := by
    simpa only [pi] using h491
  have h981 := zeta_sub_one_pow_add_fourHundredNinety_dvd_pow_sub_pow491
    hzeta 491 (by omega)
      ((w : 𝓞 K) ^ 491) ((c : 𝓞 K) ^ 491) h491'
  have hExp981 : (491 + 490 : ℕ) = 981 := by norm_num
  have hSq491 : (491 * 491 : ℕ) = 491 ^ 2 := by norm_num
  have h981' : pi ^ 981 ∣
      (w : 𝓞 K) ^ (491 ^ 2) - (c : 𝓞 K) ^ (491 ^ 2) := by
    simpa only [pi, ← pow_mul, hExp981, hSq491] using h981
  have h1471 := zeta_sub_one_pow_add_fourHundredNinety_dvd_pow_sub_pow491
    hzeta 981 (by omega)
      ((w : 𝓞 K) ^ (491 ^ 2)) ((c : 𝓞 K) ^ (491 ^ 2)) h981'
  have h1471' : pi ^ 1471 ∣
      (w : 𝓞 K) ^ (491 ^ 3) - (c : 𝓞 K) ^ (491 ^ 3) := by
    change pi ^ (981 + 490) ∣
      ((w : 𝓞 K) ^ (491 ^ 2)) ^ 491 -
        ((c : 𝓞 K) ^ (491 ^ 2)) ^ 491 at h1471
    convert h1471 using 1 <;> norm_num [← pow_mul]
  have hpi982 : pi ^ 982 ∣
      (w : 𝓞 K) ^ (491 ^ 3) - (c : 𝓞 K) ^ (491 ^ 3) :=
    (pow_dvd_pow pi (by omega)).trans h1471'
  have hneg : (1 : 𝓞 K) - hzeta.unit' ∣ pi := by
    refine ⟨-1, ?_⟩
    dsimp [pi]
    ring
  have hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 982 ∣
      (w : 𝓞 K) ^ (491 ^ 3) - (c : 𝓞 K) ^ (491 ^ 3) :=
    (pow_dvd_pow_of_dvd hneg 982).trans hpi982
  refine ⟨c ^ (491 ^ 2), ?_⟩
  simpa only [Units.val_pow_eq_pow_val, Int.cast_pow, ← pow_mul,
    show (491 ^ 2) * 491 = 491 ^ 3 by norm_num] using hdeep

/-- Vandiver depth is closed under multiplication. -/
theorem isVandiverDeep_mul {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491) (u v : (𝓞 K)ˣ)
    (hu : IsVandiverDeep (K := K) (p := 491) hzeta u)
    (hv : IsVandiverDeep (K := K) (p := 491) hzeta v) :
    IsVandiverDeep (K := K) (p := 491) hzeta (u * v) := by
  obtain ⟨c, hc⟩ := hu
  obtain ⟨d, hd⟩ := hv
  refine ⟨c * d, ?_⟩
  have h1 := dvd_mul_of_dvd_left hc (v : 𝓞 K)
  have h2 := dvd_mul_of_dvd_right hd ((c : 𝓞 K) ^ 491)
  convert dvd_add h1 h2 using 1
  simp only [Units.val_mul, Int.cast_mul, mul_pow]
  ring

/-! ## Positive relation normalization -/

/-- The nonnegative replacement for an arbitrary integer exponent. -/
def normalizedRelationExponent491 (t : ℕ) (a : ℤ) : ℕ :=
  a.toNat + (t * 491 ^ 3 - 1) * (-a).toNat

/-- The replacement differs from the original exponent by exactly
`t * 491^3 * a⁻`. -/
theorem normalizedRelationExponent491_cast
    (t : ℕ) (ht : 0 < t) (a : ℤ) :
    (normalizedRelationExponent491 t a : ℤ) =
      a + (t * 491 ^ 3 : ℕ) * (-a).toNat := by
  have ht1 : 1 ≤ t := ht
  have hM : 1 ≤ t * 491 ^ 3 := by
    exact (show 1 ≤ 1 * 491 ^ 3 by norm_num).trans
      (Nat.mul_le_mul_right (491 ^ 3) ht1)
  have ha := Int.toNat_sub_toNat_neg a
  simp only [normalizedRelationExponent491]
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hM]
  push_cast
  calc
    (a.toNat : ℤ) + ((t : ℤ) * (491 : ℤ) ^ 3 - 1) *
        ((-a).toNat : ℤ) =
      ((a.toNat : ℤ) - ((-a).toNat : ℤ)) +
        (t : ℤ) * (491 : ℤ) ^ 3 * ((-a).toNat : ℤ) := by ring
    _ = a + (t : ℤ) * (491 : ℤ) ^ 3 *
        ((-a).toNat : ℤ) := by rw [ha]

/-- The correcting `491^3`-rd power attached to the negative exponents. -/
def relationNormalizationMultiplier491
    {G : Type*} [CommGroup G] (E : SourceIndex 491 → G)
    (a : SourceIndex 491 → ℤ) : G :=
  (∏ i, E i ^ (-a i).toNat) ^ (491 ^ 3)

/-- The unit with which the normalized positive relation is formed. -/
def normalizedRelationUnit491
    {G : Type*} [CommGroup G] (u : G) (E : SourceIndex 491 → G)
    (a : SourceIndex 491 → ℤ) : G :=
  u * relationNormalizationMultiplier491 E a

/-- The normalized unit satisfies the relation with the natural exponents
`normalizedRelationExponent491`. -/
theorem normalizedRelationUnit491_pow
    {G : Type*} [CommGroup G]
    (u : G) (E : SourceIndex 491 → G)
    (t : ℕ) (ht : 0 < t) (a : SourceIndex 491 → ℤ)
    (hrel : u ^ t = ∏ i, E i ^ a i) :
    (normalizedRelationUnit491 u E a) ^ t =
      ∏ i, E i ^ normalizedRelationExponent491 t (a i) := by
  rw [normalizedRelationUnit491, mul_pow, hrel,
    relationNormalizationMultiplier491, ← pow_mul]
  rw [← Finset.prod_pow Finset.univ (491 ^ 3 * t)
    (fun i ↦ E i ^ (-a i).toNat)]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← pow_mul]
  rw [← zpow_natCast (E i) (normalizedRelationExponent491 t (a i)),
    ← zpow_natCast (E i) ((-a i).toNat * ((491 ^ 3) * t)),
    ← zpow_add]
  congr 1
  rw [normalizedRelationExponent491_cast t ht (a i)]
  push_cast
  ring

/-- The positive normalization preserves Vandiver's deep hypothesis. -/
theorem normalizedRelationUnit491_isVandiverDeep {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491)
    (u : (𝓞 K)ˣ) (E : SourceIndex 491 → (𝓞 K)ˣ)
    (a : SourceIndex 491 → ℤ)
    (hu : IsVandiverDeep (K := K) (p := 491) hzeta u) :
    IsVandiverDeep (K := K) (p := 491) hzeta
      (normalizedRelationUnit491 u E a) := by
  apply isVandiverDeep_mul hzeta
  · exact hu
  · exact cube_prime_power_isVandiverDeep hzeta
      (∏ i, E i ^ (-a i).toNat)

end

end Fermat.FourHundredNinetyOne.VandiverRelationNormalization
