import Fermat.Descent.Irregular.VandiverLemmaOne
import Fermat.Exponents.SixHundredSeven.VandiverDeepPolynomial

/-!
# Positive normalization of Vandiver exponent relations at 607

Vandiver writes the left side of equation (3b) as an integer polynomial,
although the exponents in the preceding unit relation are arbitrary
integers. This file supplies the omitted rigorous normalization.

For a positive relation exponent `t`, replace an integer exponent `a` by

`a⁺ + (t * 607^3 - 1) * a⁻`.

The new exponent is natural and differs from `a` by
`t * 607^3 * a⁻`. Multiplying the original unit by the corresponding
`607^3`-rd power therefore gives a relation with only natural exponents.

The local hypothesis is preserved. The proof starts with congruence modulo
`zeta - 1`; three successive 607st powers raise the depth from `1` to
`607`, then `1213`, then `1819`, which is more than the required `1214`.
-/

open scoped BigOperators NumberField

namespace Fermat.SixHundredSeven.VandiverRelationNormalization

noncomputable section

open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma

local instance : Fact (Nat.Prime 607) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {607} ℚ K]

/-- If two cyclotomic integers agree modulo `pi^m`, their 607st powers
agree modulo `pi^(m+606)`. -/
theorem zeta_sub_one_pow_add_sixHundredSix_dvd_pow_sub_pow607
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 607)
    (m : ℕ) (hm : 1 ≤ m) (x y : 𝓞 K)
    (hxy : ((hzeta.unit' : 𝓞 K) - 1) ^ m ∣ x - y) :
    ((hzeta.unit' : 𝓞 K) - 1) ^ (m + 606) ∣
      x ^ 607 - y ^ 607 := by
  let pi : 𝓞 K := (hzeta.unit' : 𝓞 K) - 1
  obtain ⟨k, hk⟩ := hxy
  have hx : x = y + pi ^ m * k := by
    rw [sub_eq_iff_eq_add] at hk
    simpa only [pi, add_comm] using hk
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq
    (show Nat.Prime 607 by norm_num)
    y (pi ^ m * k)
  have h606 : (607 - 1 : ℕ) = 606 := by norm_num
  have hCast607 : (((607 : ℕ) : 𝓞 K)) = (607 : 𝓞 K) := by norm_num
  have hpdiv : pi ^ 606 ∣ (607 : 𝓞 K) := by
    simpa only [pi, h606, hCast607] using
      (associated_zeta_sub_one_pow_prime hzeta).dvd
  obtain ⟨q, hq⟩ := hpdiv
  have hlast : pi ^ (m + 606) ∣ (pi ^ m * k) ^ 607 := by
    have hle : m + 606 ≤ m * 607 := by omega
    have hpow : pi ^ (m + 606) ∣ pi ^ (m * 607) :=
      pow_dvd_pow pi hle
    rw [mul_pow, ← pow_mul]
    exact dvd_mul_of_dvd_left hpow _
  have hmixed : pi ^ (m + 606) ∣
      (607 : 𝓞 K) * y * (pi ^ m * k) * r := by
    refine ⟨q * y * k * r, ?_⟩
    rw [hq, pow_add]
    ac_rfl
  rw [hx, hr]
  convert dvd_add hlast hmixed using 1
  ring

/-- Every `607^3`-rd power of a unit satisfies Vandiver's depth-1214
hypothesis. -/
theorem cube_prime_power_isVandiverDeep {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 607) (w : (𝓞 K)ˣ) :
    IsVandiverDeep (K := K) (p := 607) hzeta (w ^ (607 ^ 3)) := by
  let pi : 𝓞 K := (hzeta.unit' : 𝓞 K) - 1
  obtain ⟨c, hc⟩ :=
    exists_zeta_sub_one_dvd_sub_Int hzeta (w : 𝓞 K)
  have h1 : pi ^ 1 ∣ (w : 𝓞 K) - (c : 𝓞 K) := by
    simpa only [pi, pow_one] using hc
  have h607 :=
    zeta_sub_one_pow_add_sixHundredSix_dvd_pow_sub_pow607
      hzeta 1 (by omega) (w : 𝓞 K) (c : 𝓞 K) h1
  have h607' : pi ^ 607 ∣
      (w : 𝓞 K) ^ 607 - (c : 𝓞 K) ^ 607 := by
    simpa only [pi] using h607
  have h1213 :=
    zeta_sub_one_pow_add_sixHundredSix_dvd_pow_sub_pow607
      hzeta 607 (by omega)
      ((w : 𝓞 K) ^ 607) ((c : 𝓞 K) ^ 607) h607'
  have hExp1213 : (607 + 606 : ℕ) = 1213 := by norm_num
  have hSq607 : (607 * 607 : ℕ) = 607 ^ 2 := by norm_num
  have h1213' : pi ^ 1213 ∣
      (w : 𝓞 K) ^ (607 ^ 2) - (c : 𝓞 K) ^ (607 ^ 2) := by
    simpa only [pi, ← pow_mul, hExp1213, hSq607] using h1213
  have h1819 :=
    zeta_sub_one_pow_add_sixHundredSix_dvd_pow_sub_pow607
      hzeta 1213 (by omega)
      ((w : 𝓞 K) ^ (607 ^ 2)) ((c : 𝓞 K) ^ (607 ^ 2)) h1213'
  have h1819' : pi ^ 1819 ∣
      (w : 𝓞 K) ^ (607 ^ 3) - (c : 𝓞 K) ^ (607 ^ 3) := by
    change pi ^ (1213 + 606) ∣
      ((w : 𝓞 K) ^ (607 ^ 2)) ^ 607 -
        ((c : 𝓞 K) ^ (607 ^ 2)) ^ 607 at h1819
    convert h1819 using 1
    all_goals norm_num [← pow_mul]
  have hpi1214 : pi ^ 1214 ∣
      (w : 𝓞 K) ^ (607 ^ 3) - (c : 𝓞 K) ^ (607 ^ 3) :=
    (pow_dvd_pow pi (by omega)).trans h1819'
  have hneg : (1 : 𝓞 K) - hzeta.unit' ∣ pi := by
    refine ⟨-1, ?_⟩
    dsimp [pi]
    ring
  have hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 1214 ∣
      (w : 𝓞 K) ^ (607 ^ 3) - (c : 𝓞 K) ^ (607 ^ 3) :=
    (pow_dvd_pow_of_dvd hneg 1214).trans hpi1214
  refine ⟨c ^ (607 ^ 2), ?_⟩
  simpa only [Units.val_pow_eq_pow_val, Int.cast_pow, ← pow_mul,
    show (607 ^ 2) * 607 = 607 ^ 3 by norm_num] using hdeep

omit [NumberField K] [IsCyclotomicExtension {607} ℚ K] in
/-- Vandiver depth is closed under multiplication. -/
theorem isVandiverDeep_mul {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 607) (u v : (𝓞 K)ˣ)
    (hu : IsVandiverDeep (K := K) (p := 607) hzeta u)
    (hv : IsVandiverDeep (K := K) (p := 607) hzeta v) :
    IsVandiverDeep (K := K) (p := 607) hzeta (u * v) := by
  obtain ⟨c, hc⟩ := hu
  obtain ⟨d, hd⟩ := hv
  refine ⟨c * d, ?_⟩
  have h1 := dvd_mul_of_dvd_left hc (v : 𝓞 K)
  have h2 := dvd_mul_of_dvd_right hd ((c : 𝓞 K) ^ 607)
  convert dvd_add h1 h2 using 1
  simp only [Units.val_mul, Int.cast_mul, mul_pow]
  ring

/-! ## Positive relation normalization -/

/-- The nonnegative replacement for an arbitrary integer exponent. -/
def normalizedRelationExponent607 (t : ℕ) (a : ℤ) : ℕ :=
  a.toNat + (t * 607 ^ 3 - 1) * (-a).toNat

/-- The replacement differs from the original exponent by exactly
`t * 607^3 * a⁻`. -/
theorem normalizedRelationExponent607_cast
    (t : ℕ) (ht : 0 < t) (a : ℤ) :
    (normalizedRelationExponent607 t a : ℤ) =
      a + (t * 607 ^ 3 : ℕ) * (-a).toNat := by
  have ht1 : 1 ≤ t := ht
  have hM : 1 ≤ t * 607 ^ 3 := by
    exact (show 1 ≤ 1 * 607 ^ 3 by norm_num).trans
      (Nat.mul_le_mul_right (607 ^ 3) ht1)
  have ha := Int.toNat_sub_toNat_neg a
  simp only [normalizedRelationExponent607]
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hM]
  push_cast
  calc
    (a.toNat : ℤ) + ((t : ℤ) * (607 : ℤ) ^ 3 - 1) *
        ((-a).toNat : ℤ) =
      ((a.toNat : ℤ) - ((-a).toNat : ℤ)) +
        (t : ℤ) * (607 : ℤ) ^ 3 * ((-a).toNat : ℤ) := by ring
    _ = a + (t : ℤ) * (607 : ℤ) ^ 3 *
        ((-a).toNat : ℤ) := by rw [ha]

/-- The correcting `607^3`-rd power attached to the negative exponents. -/
def relationNormalizationMultiplier607
    {G : Type*} [CommGroup G] (E : SourceIndex 607 → G)
    (a : SourceIndex 607 → ℤ) : G :=
  (∏ i, E i ^ (-a i).toNat) ^ (607 ^ 3)

/-- The unit with which the normalized positive relation is formed. -/
def normalizedRelationUnit607
    {G : Type*} [CommGroup G] (u : G) (E : SourceIndex 607 → G)
    (a : SourceIndex 607 → ℤ) : G :=
  u * relationNormalizationMultiplier607 E a

/-- The normalized unit satisfies the relation with the natural exponents
`normalizedRelationExponent607`. -/
theorem normalizedRelationUnit607_pow
    {G : Type*} [CommGroup G]
    (u : G) (E : SourceIndex 607 → G)
    (t : ℕ) (ht : 0 < t) (a : SourceIndex 607 → ℤ)
    (hrel : u ^ t = ∏ i, E i ^ a i) :
    (normalizedRelationUnit607 u E a) ^ t =
      ∏ i, E i ^ normalizedRelationExponent607 t (a i) := by
  rw [normalizedRelationUnit607, mul_pow, hrel,
    relationNormalizationMultiplier607, ← pow_mul]
  rw [← Finset.prod_pow Finset.univ (607 ^ 3 * t)
    (fun i ↦ E i ^ (-a i).toNat)]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← pow_mul]
  rw [← zpow_natCast (E i) (normalizedRelationExponent607 t (a i)),
    ← zpow_natCast (E i) ((-a i).toNat * ((607 ^ 3) * t)),
    ← zpow_add]
  congr 1
  rw [normalizedRelationExponent607_cast t ht (a i)]
  push_cast
  ring

/-- The positive normalization preserves Vandiver's deep hypothesis. -/
theorem normalizedRelationUnit607_isVandiverDeep {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 607)
    (u : (𝓞 K)ˣ) (E : SourceIndex 607 → (𝓞 K)ˣ)
    (a : SourceIndex 607 → ℤ)
    (hu : IsVandiverDeep (K := K) (p := 607) hzeta u) :
    IsVandiverDeep (K := K) (p := 607) hzeta
      (normalizedRelationUnit607 u E a) := by
  apply isVandiverDeep_mul hzeta
  · exact hu
  · exact cube_prime_power_isVandiverDeep hzeta
      (∏ i, E i ^ (-a i).toNat)

end

end Fermat.SixHundredSeven.VandiverRelationNormalization
