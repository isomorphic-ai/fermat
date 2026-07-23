import Fermat.Irregular.VandiverLemmaOne
import Fermat.ThirtySeven.VandiverDeepPolynomial

/-!
# Positive normalization of Vandiver exponent relations at 37

Vandiver writes the left side of equation (3b) as an integer polynomial,
although the exponents in the preceding unit relation are arbitrary
integers.  This file supplies the omitted rigorous normalization.

For a positive relation exponent `t`, replace an integer exponent `a` by

`a⁺ + (t * 37^3 - 1) * a⁻`.

The new exponent is natural and differs from `a` by
`t * 37^3 * a⁻`.  Multiplying the original unit by the corresponding
`37^3`-rd power therefore gives a relation with only natural exponents.

The local hypothesis is preserved.  The proof starts with congruence modulo
`zeta - 1`; three successive 37th powers raise the depth from `1` to `37`,
then `73`, then `109`, which is more than the required `74`.

This also explains why no positivity assumption on Vandiver's original
integer exponents is needed.
-/

open scoped BigOperators NumberField

namespace Fermat.ThirtySeven.VandiverRelationNormalization

noncomputable section

open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {37} ℚ K]

/-- If two cyclotomic integers agree modulo `pi^m`, their 37th powers
agree modulo `pi^(m+36)`. -/
theorem zeta_sub_one_pow_add_thirtySix_dvd_pow_sub_pow37
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 37)
    (m : ℕ) (hm : 1 ≤ m) (x y : 𝓞 K)
    (hxy : ((hzeta.unit' : 𝓞 K) - 1) ^ m ∣ x - y) :
    ((hzeta.unit' : 𝓞 K) - 1) ^ (m + 36) ∣
      x ^ 37 - y ^ 37 := by
  let pi : 𝓞 K := (hzeta.unit' : 𝓞 K) - 1
  obtain ⟨k, hk⟩ := hxy
  have hx : x = y + pi ^ m * k := by
    rw [sub_eq_iff_eq_add] at hk
    simpa only [pi, add_comm] using hk
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq
    (show Nat.Prime 37 by norm_num) y (pi ^ m * k)
  have h36 : (37 - 1 : ℕ) = 36 := by norm_num
  have hCast37 : (((37 : ℕ) : 𝓞 K)) = (37 : 𝓞 K) := by norm_num
  have hpdiv : pi ^ 36 ∣ (37 : 𝓞 K) := by
    simpa only [pi, h36, hCast37] using
      (associated_zeta_sub_one_pow_prime hzeta).dvd
  obtain ⟨q, hq⟩ := hpdiv
  have hlast : pi ^ (m + 36) ∣ (pi ^ m * k) ^ 37 := by
    have hle : m + 36 ≤ m * 37 := by omega
    have hpow : pi ^ (m + 36) ∣ pi ^ (m * 37) :=
      pow_dvd_pow pi hle
    rw [mul_pow, ← pow_mul]
    exact dvd_mul_of_dvd_left hpow _
  have hmixed : pi ^ (m + 36) ∣
      (37 : 𝓞 K) * y * (pi ^ m * k) * r := by
    refine ⟨q * y * k * r, ?_⟩
    rw [hq, pow_add]
    ring
  rw [hx, hr]
  convert dvd_add hlast hmixed using 1
  ring

/-- Every `37^3`-rd power of a unit satisfies Vandiver's depth-74
hypothesis. -/
theorem cube_prime_power_isVandiverDeep {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) (w : (𝓞 K)ˣ) :
    IsVandiverDeep (K := K) (p := 37) hzeta (w ^ (37 ^ 3)) := by
  let pi : 𝓞 K := (hzeta.unit' : 𝓞 K) - 1
  obtain ⟨c, hc⟩ :=
    exists_zeta_sub_one_dvd_sub_Int hzeta (w : 𝓞 K)
  have h1 : pi ^ 1 ∣ (w : 𝓞 K) - (c : 𝓞 K) := by
    simpa only [pi, pow_one] using hc
  have h37 := zeta_sub_one_pow_add_thirtySix_dvd_pow_sub_pow37
    hzeta 1 (by omega) (w : 𝓞 K) (c : 𝓞 K) h1
  have h37' : pi ^ 37 ∣
      (w : 𝓞 K) ^ 37 - (c : 𝓞 K) ^ 37 := by
    simpa only [pi] using h37
  have h73 := zeta_sub_one_pow_add_thirtySix_dvd_pow_sub_pow37
    hzeta 37 (by omega)
      ((w : 𝓞 K) ^ 37) ((c : 𝓞 K) ^ 37) h37'
  have hExp73 : (37 + 36 : ℕ) = 73 := by norm_num
  have hSq37 : (37 * 37 : ℕ) = 37 ^ 2 := by norm_num
  have h73' : pi ^ 73 ∣
      (w : 𝓞 K) ^ (37 ^ 2) - (c : 𝓞 K) ^ (37 ^ 2) := by
    simpa only [pi, ← pow_mul, hExp73, hSq37] using h73
  have h109 := zeta_sub_one_pow_add_thirtySix_dvd_pow_sub_pow37
    hzeta 73 (by omega)
      ((w : 𝓞 K) ^ (37 ^ 2)) ((c : 𝓞 K) ^ (37 ^ 2)) h73'
  have h109' : pi ^ 109 ∣
      (w : 𝓞 K) ^ (37 ^ 3) - (c : 𝓞 K) ^ (37 ^ 3) := by
    change pi ^ (73 + 36) ∣
      ((w : 𝓞 K) ^ (37 ^ 2)) ^ 37 -
        ((c : 𝓞 K) ^ (37 ^ 2)) ^ 37 at h109
    convert h109 using 1 <;> norm_num [← pow_mul]
  have hpi74 : pi ^ 74 ∣
      (w : 𝓞 K) ^ (37 ^ 3) - (c : 𝓞 K) ^ (37 ^ 3) :=
    (pow_dvd_pow pi (by omega)).trans h109'
  have hneg : (1 : 𝓞 K) - hzeta.unit' ∣ pi := by
    refine ⟨-1, ?_⟩
    dsimp [pi]
    ring
  have hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 74 ∣
      (w : 𝓞 K) ^ (37 ^ 3) - (c : 𝓞 K) ^ (37 ^ 3) :=
    (pow_dvd_pow_of_dvd hneg 74).trans hpi74
  refine ⟨c ^ (37 ^ 2), ?_⟩
  simpa only [Units.val_pow_eq_pow_val, Int.cast_pow, ← pow_mul,
    show (37 ^ 2) * 37 = 37 ^ 3 by norm_num] using hdeep

/-- Vandiver depth is closed under multiplication. -/
theorem isVandiverDeep_mul {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) (u v : (𝓞 K)ˣ)
    (hu : IsVandiverDeep (K := K) (p := 37) hzeta u)
    (hv : IsVandiverDeep (K := K) (p := 37) hzeta v) :
    IsVandiverDeep (K := K) (p := 37) hzeta (u * v) := by
  obtain ⟨c, hc⟩ := hu
  obtain ⟨d, hd⟩ := hv
  refine ⟨c * d, ?_⟩
  have h1 := dvd_mul_of_dvd_left hc (v : 𝓞 K)
  have h2 := dvd_mul_of_dvd_right hd ((c : 𝓞 K) ^ 37)
  convert dvd_add h1 h2 using 1
  simp only [Units.val_mul, Int.cast_mul, mul_pow]
  ring

/-! ## Positive relation normalization -/

/-- The nonnegative replacement for an arbitrary integer exponent. -/
def normalizedRelationExponent37 (t : ℕ) (a : ℤ) : ℕ :=
  a.toNat + (t * 37 ^ 3 - 1) * (-a).toNat

/-- The replacement differs from the original exponent by exactly
`t * 37^3 * a⁻`. -/
theorem normalizedRelationExponent37_cast
    (t : ℕ) (ht : 0 < t) (a : ℤ) :
    (normalizedRelationExponent37 t a : ℤ) =
      a + (t * 37 ^ 3 : ℕ) * (-a).toNat := by
  have ht1 : 1 ≤ t := ht
  have hM : 1 ≤ t * 37 ^ 3 := by
    exact (show 1 ≤ 1 * 37 ^ 3 by norm_num).trans
      (Nat.mul_le_mul_right (37 ^ 3) ht1)
  have ha := Int.toNat_sub_toNat_neg a
  simp only [normalizedRelationExponent37]
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hM]
  push_cast
  calc
    (a.toNat : ℤ) + ((t : ℤ) * (37 : ℤ) ^ 3 - 1) *
        ((-a).toNat : ℤ) =
      ((a.toNat : ℤ) - ((-a).toNat : ℤ)) +
        (t : ℤ) * (37 : ℤ) ^ 3 * ((-a).toNat : ℤ) := by ring
    _ = a + (t : ℤ) * (37 : ℤ) ^ 3 *
        ((-a).toNat : ℤ) := by rw [ha]

/-- The correcting `37^3`-rd power attached to the negative exponents. -/
def relationNormalizationMultiplier37
    {G : Type*} [CommGroup G] (E : SourceIndex 37 → G)
    (a : SourceIndex 37 → ℤ) : G :=
  (∏ i, E i ^ (-a i).toNat) ^ (37 ^ 3)

/-- The unit with which the normalized positive relation is formed. -/
def normalizedRelationUnit37
    {G : Type*} [CommGroup G] (u : G) (E : SourceIndex 37 → G)
    (a : SourceIndex 37 → ℤ) : G :=
  u * relationNormalizationMultiplier37 E a

/-- The normalized unit satisfies the relation with the natural exponents
`normalizedRelationExponent37`. -/
theorem normalizedRelationUnit37_pow
    {G : Type*} [CommGroup G]
    (u : G) (E : SourceIndex 37 → G)
    (t : ℕ) (ht : 0 < t) (a : SourceIndex 37 → ℤ)
    (hrel : u ^ t = ∏ i, E i ^ a i) :
    (normalizedRelationUnit37 u E a) ^ t =
      ∏ i, E i ^ normalizedRelationExponent37 t (a i) := by
  rw [normalizedRelationUnit37, mul_pow, hrel,
    relationNormalizationMultiplier37, ← pow_mul]
  rw [← Finset.prod_pow Finset.univ (37 ^ 3 * t)
    (fun i ↦ E i ^ (-a i).toNat)]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← pow_mul]
  rw [← zpow_natCast (E i) (normalizedRelationExponent37 t (a i)),
    ← zpow_natCast (E i) ((-a i).toNat * ((37 ^ 3) * t)),
    ← zpow_add]
  congr 1
  rw [normalizedRelationExponent37_cast t ht (a i)]
  push_cast
  ring

/-- The positive normalization preserves Vandiver's deep hypothesis. -/
theorem normalizedRelationUnit37_isVandiverDeep {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37)
    (u : (𝓞 K)ˣ) (E : SourceIndex 37 → (𝓞 K)ˣ)
    (a : SourceIndex 37 → ℤ)
    (hu : IsVandiverDeep (K := K) (p := 37) hzeta u) :
    IsVandiverDeep (K := K) (p := 37) hzeta
      (normalizedRelationUnit37 u E a) := by
  apply isVandiverDeep_mul hzeta
  · exact hu
  · exact cube_prime_power_isVandiverDeep hzeta
      (∏ i, E i ^ (-a i).toNat)

end

end Fermat.ThirtySeven.VandiverRelationNormalization
