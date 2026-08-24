import Fermat.Descent.Irregular.VandiverLemmaOne
import Fermat.Descent.Irregular.VandiverLemmaTwoCore
import Fermat.Descent.Irregular.VandiverUnitLemma
import Fermat.Descent.Irregular.Voronoi

/-!
# Prime-generic normalization of Vandiver exponent relations

The polynomial argument in Vandiver's Lemma II is naturally stated for
nonnegative exponents.  This module performs the normalization uniformly
at every prime: an integer exponent is replaced by a nonnegative exponent
which differs from it by a multiple of `t * p^3`.

The corresponding correction is a `p^3`-rd power.  Three applications of
the ramified binomial congruence show that such a correction satisfies the
depth-`2p` local hypothesis.  Thus positive-relation derivative congruences
can be transported back to arbitrary primitive relations without any
prime-specific arithmetic.
-/

open scoped BigOperators NumberField

namespace Fermat.Irregular.VandiverRelationNormalizationPrime

noncomputable section

open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma
open Fermat.Irregular.Voronoi

variable {K : Type} {p : ℕ} [Fact p.Prime]
  [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- If two cyclotomic integers agree modulo `pi^m`, their `p`-th powers
agree modulo `pi^(m + p - 1)`. -/
theorem zeta_sub_one_pow_add_pred_dvd_pow_sub_pow
    {zeta : K} (hzeta : IsPrimitiveRoot zeta p)
    (m : ℕ) (hm : 1 ≤ m) (x y : 𝓞 K)
    (hxy : ((hzeta.unit' : 𝓞 K) - 1) ^ m ∣ x - y) :
    ((hzeta.unit' : 𝓞 K) - 1) ^ (m + (p - 1)) ∣
      x ^ p - y ^ p := by
  let pi : 𝓞 K := (hzeta.unit' : 𝓞 K) - 1
  obtain ⟨k, hk⟩ := hxy
  have hx : x = y + pi ^ m * k := by
    rw [sub_eq_iff_eq_add] at hk
    simpa only [pi, add_comm] using hk
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq
    (Fact.out : Nat.Prime p) y (pi ^ m * k)
  have hpdiv : pi ^ (p - 1) ∣ (p : 𝓞 K) := by
    simpa only [pi] using
      (associated_zeta_sub_one_pow_prime hzeta).dvd
  obtain ⟨q, hq⟩ := hpdiv
  have hlast : pi ^ (m + (p - 1)) ∣ (pi ^ m * k) ^ p := by
    have hle : m + (p - 1) ≤ m * p := by
      have hpOne := (Fact.out : Nat.Prime p).one_lt
      calc
        m + (p - 1) ≤ m + m * (p - 1) := by
          exact Nat.add_le_add_left
            (by simpa only [one_mul] using
              Nat.mul_le_mul_right (p - 1) hm) m
        _ = m * (1 + (p - 1)) := by ring
        _ = m * p := by rw [Nat.add_sub_of_le hpOne.le]
    have hpow : pi ^ (m + (p - 1)) ∣ pi ^ (m * p) :=
      pow_dvd_pow pi hle
    rw [mul_pow, ← pow_mul]
    exact dvd_mul_of_dvd_left hpow _
  have hmixed : pi ^ (m + (p - 1)) ∣
      (p : 𝓞 K) * y * (pi ^ m * k) * r := by
    refine ⟨q * y * k * r, ?_⟩
    rw [hq, pow_add]
    ring
  rw [hx, hr]
  convert dvd_add hlast hmixed using 1
  ring

/-- Every `p^3`-rd power of a unit satisfies Vandiver's depth-`2p`
hypothesis. -/
theorem cube_prime_power_isVandiverDeep
    (hp2 : 2 ≤ p) {zeta : K} (hzeta : IsPrimitiveRoot zeta p)
    (w : (𝓞 K)ˣ) :
    IsVandiverDeep (K := K) (p := p) hzeta (w ^ (p ^ 3)) := by
  let pi : 𝓞 K := (hzeta.unit' : 𝓞 K) - 1
  obtain ⟨c, hc⟩ :=
    exists_zeta_sub_one_dvd_sub_Int hzeta (w : 𝓞 K)
  have h1 : pi ^ 1 ∣ (w : 𝓞 K) - (c : 𝓞 K) := by
    simpa only [pi, pow_one] using hc
  have hp := zeta_sub_one_pow_add_pred_dvd_pow_sub_pow
    hzeta 1 (by omega) (w : 𝓞 K) (c : 𝓞 K) h1
  have hp' : pi ^ p ∣
      (w : 𝓞 K) ^ p - (c : 𝓞 K) ^ p := by
    have hdepth : 1 + (p - 1) = p := by omega
    simpa only [pi, hdepth] using hp
  have htwo := zeta_sub_one_pow_add_pred_dvd_pow_sub_pow
    hzeta p (by omega)
      ((w : 𝓞 K) ^ p) ((c : 𝓞 K) ^ p) hp'
  have htwo' : pi ^ (2 * p - 1) ∣
      (w : 𝓞 K) ^ (p ^ 2) -
        (c : 𝓞 K) ^ (p ^ 2) := by
    have hdepth : p + (p - 1) = 2 * p - 1 := by omega
    simpa only [pi, hdepth, ← pow_mul, pow_two] using htwo
  have hthree := zeta_sub_one_pow_add_pred_dvd_pow_sub_pow
    hzeta (2 * p - 1) (by omega)
      ((w : 𝓞 K) ^ (p ^ 2)) ((c : 𝓞 K) ^ (p ^ 2)) htwo'
  have hthree' : pi ^ (3 * p - 2) ∣
      (w : 𝓞 K) ^ (p ^ 3) -
        (c : 𝓞 K) ^ (p ^ 3) := by
    have hdepth : (2 * p - 1) + (p - 1) = 3 * p - 2 := by omega
    rw [hdepth] at hthree
    convert hthree using 1
    all_goals simp only [← pow_mul]
    all_goals ring
  have hpi : pi ^ (2 * p) ∣
      (w : 𝓞 K) ^ (p ^ 3) -
        (c : 𝓞 K) ^ (p ^ 3) :=
    (pow_dvd_pow pi (by omega)).trans hthree'
  have hneg : (1 : 𝓞 K) - hzeta.unit' ∣ pi := by
    refine ⟨-1, ?_⟩
    dsimp [pi]
    ring
  have hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ (2 * p) ∣
      (w : 𝓞 K) ^ (p ^ 3) -
        (c : 𝓞 K) ^ (p ^ 3) :=
    (pow_dvd_pow_of_dvd hneg (2 * p)).trans hpi
  refine ⟨c ^ (p ^ 2), ?_⟩
  simpa only [Units.val_pow_eq_pow_val, Int.cast_pow, ← pow_mul,
    show (p ^ 2) * p = p ^ 3 by ring] using hdeep

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- Vandiver depth is closed under multiplication. -/
theorem isVandiverDeep_mul {zeta : K}
    (hzeta : IsPrimitiveRoot zeta p) (u v : (𝓞 K)ˣ)
    (hu : IsVandiverDeep (K := K) (p := p) hzeta u)
    (hv : IsVandiverDeep (K := K) (p := p) hzeta v) :
    IsVandiverDeep (K := K) (p := p) hzeta (u * v) := by
  obtain ⟨c, hc⟩ := hu
  obtain ⟨d, hd⟩ := hv
  refine ⟨c * d, ?_⟩
  have h1 := dvd_mul_of_dvd_left hc (v : 𝓞 K)
  have h2 := dvd_mul_of_dvd_right hd ((c : 𝓞 K) ^ p)
  convert dvd_add h1 h2 using 1
  simp only [Units.val_mul, Int.cast_mul, mul_pow]
  ring

/-! ## Positive relation normalization -/

/-- The nonnegative replacement for an arbitrary integer exponent. -/
def normalizedRelationExponent (p t : ℕ) (a : ℤ) : ℕ :=
  a.toNat + (t * p ^ 3 - 1) * (-a).toNat

omit [Fact p.Prime] in
/-- The replacement differs from the original exponent by exactly
`t * p^3 * a⁻`. -/
theorem normalizedRelationExponent_cast
    (hp : 0 < p) (t : ℕ) (ht : 0 < t) (a : ℤ) :
    (normalizedRelationExponent p t a : ℤ) =
      a + (t * p ^ 3 : ℕ) * (-a).toNat := by
  have ht1 : 1 ≤ t := ht
  have hpPow : 1 ≤ p ^ 3 := Nat.one_le_pow _ _ hp
  have hM : 1 ≤ t * p ^ 3 :=
    (show 1 * 1 ≤ t * p ^ 3 from Nat.mul_le_mul ht1 hpPow)
  have ha := Int.toNat_sub_toNat_neg a
  simp only [normalizedRelationExponent]
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hM]
  push_cast
  calc
    (a.toNat : ℤ) + ((t : ℤ) * (p : ℤ) ^ 3 - 1) *
        ((-a).toNat : ℤ) =
      ((a.toNat : ℤ) - ((-a).toNat : ℤ)) +
        (t : ℤ) * (p : ℤ) ^ 3 * ((-a).toNat : ℤ) := by ring
    _ = a + (t : ℤ) * (p : ℤ) ^ 3 *
        ((-a).toNat : ℤ) := by rw [ha]

/-- The correcting `p^3`-rd power attached to the negative exponents. -/
def relationNormalizationMultiplier
    {G : Type*} [CommGroup G] (p : ℕ) {I : Type*} [Fintype I]
    (E : I → G) (a : I → ℤ) : G :=
  (∏ i, E i ^ (-a i).toNat) ^ (p ^ 3)

/-- The unit with which the normalized positive relation is formed. -/
def normalizedRelationUnit
    {G : Type*} [CommGroup G] (p : ℕ) {I : Type*} [Fintype I]
    (u : G) (E : I → G) (a : I → ℤ) : G :=
  u * relationNormalizationMultiplier p E a

/-- The normalized unit satisfies the relation with natural exponents. -/
theorem normalizedRelationUnit_pow
    {G : Type*} [CommGroup G] {I : Type*} [Fintype I]
    (p : ℕ) (hp : 0 < p) (u : G) (E : I → G)
    (t : ℕ) (ht : 0 < t) (a : I → ℤ)
    (hrel : u ^ t = ∏ i, E i ^ a i) :
    (normalizedRelationUnit p u E a) ^ t =
      ∏ i, E i ^ normalizedRelationExponent p t (a i) := by
  rw [normalizedRelationUnit, mul_pow, hrel,
    relationNormalizationMultiplier, ← pow_mul]
  rw [← Finset.prod_pow Finset.univ (p ^ 3 * t)
    (fun i ↦ E i ^ (-a i).toNat)]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← pow_mul]
  rw [← zpow_natCast (E i) (normalizedRelationExponent p t (a i)),
    ← zpow_natCast (E i) ((-a i).toNat * ((p ^ 3) * t)),
    ← zpow_add]
  congr 1
  rw [normalizedRelationExponent_cast hp t ht (a i)]
  push_cast
  ring

/-- The positive normalization preserves Vandiver's deep hypothesis. -/
theorem normalizedRelationUnit_isVandiverDeep
    (hp2 : 2 ≤ p) {zeta : K} (hzeta : IsPrimitiveRoot zeta p)
    (u : (𝓞 K)ˣ) (E : SourceIndex p → (𝓞 K)ˣ)
    (a : SourceIndex p → ℤ)
    (hu : IsVandiverDeep (K := K) (p := p) hzeta u) :
    IsVandiverDeep (K := K) (p := p) hzeta
      (normalizedRelationUnit p u E a) := by
  apply isVandiverDeep_mul hzeta
  · exact hu
  · exact cube_prime_power_isVandiverDeep hp2 hzeta
      (∏ i, E i ^ (-a i).toNat)

omit [Fact p.Prime] in
/-- Divisibility by `p^3` for a normalized exponent times an integer
factor implies the same divisibility for the original exponent. -/
theorem cube_dvd_mul_of_normalizedRelationExponent
    (hp : 0 < p) (t : ℕ) (ht : 0 < t) (a B : ℤ)
    (h : (p : ℤ) ^ 3 ∣
      (normalizedRelationExponent p t a : ℤ) * B) :
    (p : ℤ) ^ 3 ∣ a * B := by
  have hcorrection : (p : ℤ) ^ 3 ∣
      (normalizedRelationExponent p t a : ℤ) * B - a * B := by
    refine ⟨(t : ℤ) * ((-a).toNat : ℤ) * B, ?_⟩
    rw [normalizedRelationExponent_cast hp t ht a]
    push_cast
    ring
  have hsub := dvd_sub h hcorrection
  convert hsub using 1
  ring

/-! ## From positive derivative relations to primitive relations -/

/-- Prime-generic normalization of the positive derivative argument.

The input `hpositive` is the polynomial calculation for natural exponent
vectors in the chosen unit family.  The input `hcube` is the diagonal
derivative-to-Bernoulli endpoint.  No property of the family besides these
two inputs is used, so the theorem applies directly to Vandiver's
diagonalized family at every exponent. -/
theorem primitiveRelationCubeCongruences_of_positive
    (hp2 : 2 ≤ p) {zeta : K} (hzeta : IsPrimitiveRoot zeta p)
    (E : SourceIndex p → (𝓞 K)ˣ)
    (relationDerivative :
      (SourceIndex p → ℤ) → SourceIndex p → ℚ)
    (u : (𝓞 K)ˣ)
    (hdeep : IsVandiverDeep (K := K) (p := p) hzeta u)
    (hpositive :
      ∀ (v : (𝓞 K)ˣ) (t : ℕ) (b : SourceIndex p → ℕ),
        IsVandiverDeep (K := K) (p := p) hzeta v →
        v ^ t = ∏ i, E i ^ b i →
        ∀ k, HasPadicValAtLeast p 2
          (relationDerivative (fun i ↦ (b i : ℤ)) k))
    (hcube :
      ∀ a : SourceIndex p → ℤ,
        (∀ k, HasPadicValAtLeast p 2 (relationDerivative a k)) →
        ∀ i, (p : ℤ) ^ 3 ∣
          a i * vandiverBernoulliNumerator p i) :
    PrimitiveRelationCubeCongruences p u E := by
  intro t a ht hrel _hprimitive
  let b : SourceIndex p → ℕ :=
    fun i ↦ normalizedRelationExponent p t (a i)
  let v : (𝓞 K)ˣ := normalizedRelationUnit p u E a
  have hvdeep : IsVandiverDeep (K := K) (p := p) hzeta v :=
    normalizedRelationUnit_isVandiverDeep hp2 hzeta u E a hdeep
  have hvrel : v ^ t = ∏ i, E i ^ b i := by
    exact normalizedRelationUnit_pow p (Fact.out : Nat.Prime p).pos
      u E t ht a hrel
  have hderivative : ∀ k, HasPadicValAtLeast p 2
      (relationDerivative (fun i ↦ (b i : ℤ)) k) :=
    hpositive v t b hvdeep hvrel
  have hnormalized := hcube (fun i ↦ (b i : ℤ)) hderivative
  intro i
  exact cube_dvd_mul_of_normalizedRelationExponent
    (Fact.out : Nat.Prime p).pos t ht (a i)
      (vandiverBernoulliNumerator p i)
      (by simpa only [b] using hnormalized i)

end

end Fermat.Irregular.VandiverRelationNormalizationPrime
