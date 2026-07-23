import Fermat.Irregular.VandiverLemmaOne
import Fermat.SixtySeven.VandiverDeepPolynomial

/-!
# Positive normalization of Vandiver exponent relations at 67

Vandiver writes the left side of equation (3b) as an integer polynomial,
although the exponents in the preceding unit relation are arbitrary
integers.  This file supplies the omitted rigorous normalization.

For a positive relation exponent `t`, replace an integer exponent `a` by

`a⁺ + (t * 67^3 - 1) * a⁻`.

The new exponent is natural and differs from `a` by
`t * 67^3 * a⁻`.  Multiplying the original unit by the corresponding
`67^3`-rd power therefore gives a relation with only natural exponents.

The local hypothesis is preserved.  The proof starts with congruence modulo
`zeta - 1`; three successive 67th powers raise the depth from `1` to `67`,
then `133`, then `199`, which is more than the required `134`.

This also explains why no positivity assumption on Vandiver's original
integer exponents is needed.
-/

open scoped BigOperators NumberField

namespace Fermat.SixtySeven.VandiverRelationNormalization

noncomputable section

open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma

local instance : Fact (Nat.Prime 67) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {67} ℚ K]

/-- If two cyclotomic integers agree modulo `pi^m`, their 67th powers
agree modulo `pi^(m+66)`. -/
theorem zeta_sub_one_pow_add_sixtySix_dvd_pow_sub_pow67
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 67)
    (m : ℕ) (hm : 1 ≤ m) (x y : 𝓞 K)
    (hxy : ((hzeta.unit' : 𝓞 K) - 1) ^ m ∣ x - y) :
    ((hzeta.unit' : 𝓞 K) - 1) ^ (m + 66) ∣
      x ^ 67 - y ^ 67 := by
  let pi : 𝓞 K := (hzeta.unit' : 𝓞 K) - 1
  obtain ⟨k, hk⟩ := hxy
  have hx : x = y + pi ^ m * k := by
    rw [sub_eq_iff_eq_add] at hk
    simpa only [pi, add_comm] using hk
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq
    (show Nat.Prime 67 by norm_num) y (pi ^ m * k)
  have h66 : (67 - 1 : ℕ) = 66 := by norm_num
  have hCast67 : (((67 : ℕ) : 𝓞 K)) = (67 : 𝓞 K) := by norm_num
  have hpdiv : pi ^ 66 ∣ (67 : 𝓞 K) := by
    simpa only [pi, h66, hCast67] using
      (associated_zeta_sub_one_pow_prime hzeta).dvd
  obtain ⟨q, hq⟩ := hpdiv
  have hlast : pi ^ (m + 66) ∣ (pi ^ m * k) ^ 67 := by
    have hle : m + 66 ≤ m * 67 := by omega
    have hpow : pi ^ (m + 66) ∣ pi ^ (m * 67) :=
      pow_dvd_pow pi hle
    rw [mul_pow, ← pow_mul]
    exact dvd_mul_of_dvd_left hpow _
  have hmixed : pi ^ (m + 66) ∣
      (67 : 𝓞 K) * y * (pi ^ m * k) * r := by
    refine ⟨q * y * k * r, ?_⟩
    rw [hq, pow_add]
    ring
  rw [hx, hr]
  convert dvd_add hlast hmixed using 1
  ring

/-- Every `67^3`-rd power of a unit satisfies Vandiver's depth-134
hypothesis. -/
theorem cube_prime_power_isVandiverDeep {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 67) (w : (𝓞 K)ˣ) :
    IsVandiverDeep (K := K) (p := 67) hzeta (w ^ (67 ^ 3)) := by
  let pi : 𝓞 K := (hzeta.unit' : 𝓞 K) - 1
  obtain ⟨c, hc⟩ :=
    exists_zeta_sub_one_dvd_sub_Int hzeta (w : 𝓞 K)
  have h1 : pi ^ 1 ∣ (w : 𝓞 K) - (c : 𝓞 K) := by
    simpa only [pi, pow_one] using hc
  have h67 := zeta_sub_one_pow_add_sixtySix_dvd_pow_sub_pow67
    hzeta 1 (by omega) (w : 𝓞 K) (c : 𝓞 K) h1
  have h67' : pi ^ 67 ∣
      (w : 𝓞 K) ^ 67 - (c : 𝓞 K) ^ 67 := by
    simpa only [pi] using h67
  have h133 := zeta_sub_one_pow_add_sixtySix_dvd_pow_sub_pow67
    hzeta 67 (by omega)
      ((w : 𝓞 K) ^ 67) ((c : 𝓞 K) ^ 67) h67'
  have hExp133 : (67 + 66 : ℕ) = 133 := by norm_num
  have hSq67 : (67 * 67 : ℕ) = 67 ^ 2 := by norm_num
  have h133' : pi ^ 133 ∣
      (w : 𝓞 K) ^ (67 ^ 2) - (c : 𝓞 K) ^ (67 ^ 2) := by
    simpa only [pi, ← pow_mul, hExp133, hSq67] using h133
  have h199 := zeta_sub_one_pow_add_sixtySix_dvd_pow_sub_pow67
    hzeta 133 (by omega)
      ((w : 𝓞 K) ^ (67 ^ 2)) ((c : 𝓞 K) ^ (67 ^ 2)) h133'
  have h199' : pi ^ 199 ∣
      (w : 𝓞 K) ^ (67 ^ 3) - (c : 𝓞 K) ^ (67 ^ 3) := by
    change pi ^ (133 + 66) ∣
      ((w : 𝓞 K) ^ (67 ^ 2)) ^ 67 -
        ((c : 𝓞 K) ^ (67 ^ 2)) ^ 67 at h199
    convert h199 using 1 <;> norm_num [← pow_mul]
  have hpi134 : pi ^ 134 ∣
      (w : 𝓞 K) ^ (67 ^ 3) - (c : 𝓞 K) ^ (67 ^ 3) :=
    (pow_dvd_pow pi (by omega)).trans h199'
  have hneg : (1 : 𝓞 K) - hzeta.unit' ∣ pi := by
    refine ⟨-1, ?_⟩
    dsimp [pi]
    ring
  have hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 134 ∣
      (w : 𝓞 K) ^ (67 ^ 3) - (c : 𝓞 K) ^ (67 ^ 3) :=
    (pow_dvd_pow_of_dvd hneg 134).trans hpi134
  refine ⟨c ^ (67 ^ 2), ?_⟩
  simpa only [Units.val_pow_eq_pow_val, Int.cast_pow, ← pow_mul,
    show (67 ^ 2) * 67 = 67 ^ 3 by norm_num] using hdeep

/-- Vandiver depth is closed under multiplication. -/
theorem isVandiverDeep_mul {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 67) (u v : (𝓞 K)ˣ)
    (hu : IsVandiverDeep (K := K) (p := 67) hzeta u)
    (hv : IsVandiverDeep (K := K) (p := 67) hzeta v) :
    IsVandiverDeep (K := K) (p := 67) hzeta (u * v) := by
  obtain ⟨c, hc⟩ := hu
  obtain ⟨d, hd⟩ := hv
  refine ⟨c * d, ?_⟩
  have h1 := dvd_mul_of_dvd_left hc (v : 𝓞 K)
  have h2 := dvd_mul_of_dvd_right hd ((c : 𝓞 K) ^ 67)
  convert dvd_add h1 h2 using 1
  simp only [Units.val_mul, Int.cast_mul, mul_pow]
  ring

/-! ## Positive relation normalization -/

/-- The nonnegative replacement for an arbitrary integer exponent. -/
def normalizedRelationExponent67 (t : ℕ) (a : ℤ) : ℕ :=
  a.toNat + (t * 67 ^ 3 - 1) * (-a).toNat

/-- The replacement differs from the original exponent by exactly
`t * 67^3 * a⁻`. -/
theorem normalizedRelationExponent67_cast
    (t : ℕ) (ht : 0 < t) (a : ℤ) :
    (normalizedRelationExponent67 t a : ℤ) =
      a + (t * 67 ^ 3 : ℕ) * (-a).toNat := by
  have ht1 : 1 ≤ t := ht
  have hM : 1 ≤ t * 67 ^ 3 := by
    exact (show 1 ≤ 1 * 67 ^ 3 by norm_num).trans
      (Nat.mul_le_mul_right (67 ^ 3) ht1)
  have ha := Int.toNat_sub_toNat_neg a
  simp only [normalizedRelationExponent67]
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hM]
  push_cast
  calc
    (a.toNat : ℤ) + ((t : ℤ) * (67 : ℤ) ^ 3 - 1) *
        ((-a).toNat : ℤ) =
      ((a.toNat : ℤ) - ((-a).toNat : ℤ)) +
        (t : ℤ) * (67 : ℤ) ^ 3 * ((-a).toNat : ℤ) := by ring
    _ = a + (t : ℤ) * (67 : ℤ) ^ 3 *
        ((-a).toNat : ℤ) := by rw [ha]

/-- The correcting `67^3`-rd power attached to the negative exponents. -/
def relationNormalizationMultiplier67
    {G : Type*} [CommGroup G] (E : SourceIndex 67 → G)
    (a : SourceIndex 67 → ℤ) : G :=
  (∏ i, E i ^ (-a i).toNat) ^ (67 ^ 3)

/-- The unit with which the normalized positive relation is formed. -/
def normalizedRelationUnit67
    {G : Type*} [CommGroup G] (u : G) (E : SourceIndex 67 → G)
    (a : SourceIndex 67 → ℤ) : G :=
  u * relationNormalizationMultiplier67 E a

/-- The normalized unit satisfies the relation with the natural exponents
`normalizedRelationExponent67`. -/
theorem normalizedRelationUnit67_pow
    {G : Type*} [CommGroup G]
    (u : G) (E : SourceIndex 67 → G)
    (t : ℕ) (ht : 0 < t) (a : SourceIndex 67 → ℤ)
    (hrel : u ^ t = ∏ i, E i ^ a i) :
    (normalizedRelationUnit67 u E a) ^ t =
      ∏ i, E i ^ normalizedRelationExponent67 t (a i) := by
  rw [normalizedRelationUnit67, mul_pow, hrel,
    relationNormalizationMultiplier67, ← pow_mul]
  rw [← Finset.prod_pow Finset.univ (67 ^ 3 * t)
    (fun i ↦ E i ^ (-a i).toNat)]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← pow_mul]
  rw [← zpow_natCast (E i) (normalizedRelationExponent67 t (a i)),
    ← zpow_natCast (E i) ((-a i).toNat * ((67 ^ 3) * t)),
    ← zpow_add]
  congr 1
  rw [normalizedRelationExponent67_cast t ht (a i)]
  push_cast
  ring

/-- The positive normalization preserves Vandiver's deep hypothesis. -/
theorem normalizedRelationUnit67_isVandiverDeep {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 67)
    (u : (𝓞 K)ˣ) (E : SourceIndex 67 → (𝓞 K)ˣ)
    (a : SourceIndex 67 → ℤ)
    (hu : IsVandiverDeep (K := K) (p := 67) hzeta u) :
    IsVandiverDeep (K := K) (p := 67) hzeta
      (normalizedRelationUnit67 u E a) := by
  apply isVandiverDeep_mul hzeta
  · exact hu
  · exact cube_prime_power_isVandiverDeep hzeta
      (∏ i, E i ^ (-a i).toNat)

end

end Fermat.SixtySeven.VandiverRelationNormalization
