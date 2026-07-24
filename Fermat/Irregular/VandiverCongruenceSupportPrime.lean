import Fermat.Irregular.VandiverLemmaOne
import Fermat.Irregular.VandiverRealEquationNineGeneratorPrime
import Fermat.Irregular.VandiverTakagiPairPrime

/-!
# Prime-generic local congruence support for Vandiver's descent

This module formalizes the local calculation between equations (9a) and
(10) uniformly for an odd prime `p`.

* A real cyclotomic integer has a rational-integer residue modulo
  `(ζ - 1)^2`.
* Raising a congruence to the `p`-th power adds `p - 1` to its ramified
  depth.
* Two such lifts turn a congruence modulo `(ζ - 1)^2` into one modulo
  `(ζ - 1)^(2*p)` between `p^2`-th powers.
* The resulting unit ratio is a rational `p^2`-th power, and its negative
  square is a rational `p`-th power, at that same depth.

These are the common proofs behind the exponent-specific congruence
support modules.
-/

namespace Fermat.Irregular.VandiverCongruenceSupportPrime

open scoped NumberField nonZeroDivisors

open Fermat.Irregular.VandiverTakagiPairPrime
open Fermat.Irregular.VandiverRealEquationNineGeneratorPrime

noncomputable section

variable {K : Type} {p : ℕ} [Fact p.Prime]
  [Field K] [NumberField K] [NumberField.IsCMField K]
  [IsCyclotomicExtension {p} ℚ K]

/-- If two cyclotomic integers agree modulo `π^m`, their `p`-th powers
agree modulo `π^(m + p - 1)`. -/
theorem zeta_sub_one_pow_add_pred_dvd_pow_sub_pow
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (m : ℕ) (hm : 1 ≤ m) (x y : 𝓞 K)
    (hxy : ((hζ.unit' : 𝓞 K) - 1) ^ m ∣ x - y) :
    ((hζ.unit' : 𝓞 K) - 1) ^ (m + (p - 1)) ∣
      x ^ p - y ^ p := by
  let pi : 𝓞 K := (hζ.unit' : 𝓞 K) - 1
  obtain ⟨k, hk⟩ := hxy
  have hx : x = y + pi ^ m * k := by
    rw [sub_eq_iff_eq_add] at hk
    simpa only [pi, add_comm] using hk
  obtain ⟨r, hr⟩ :=
    exists_add_pow_prime_eq
      (Fact.out : Nat.Prime p) y (pi ^ m * k)
  have hpdiv : pi ^ (p - 1) ∣ (p : 𝓞 K) := by
    simpa only [pi] using
      (associated_zeta_sub_one_pow_prime hζ).dvd
  obtain ⟨q, hq⟩ := hpdiv
  have hlast :
      pi ^ (m + (p - 1)) ∣ (pi ^ m * k) ^ p := by
    have hle : m + (p - 1) ≤ m * p := by
      have hpOne := (Fact.out : Nat.Prime p).one_lt
      calc
        m + (p - 1) ≤ m + m * (p - 1) := by
          exact Nat.add_le_add_left
            (by simpa only [one_mul] using
              Nat.mul_le_mul_right (p - 1) hm) m
        _ = m * (1 + (p - 1)) := by ring
        _ = m * p := by rw [Nat.add_sub_of_le hpOne.le]
    have hpow :
        pi ^ (m + (p - 1)) ∣ pi ^ (m * p) :=
      pow_dvd_pow pi hle
    rw [mul_pow, ← pow_mul]
    exact dvd_mul_of_dvd_left hpow _
  have hmixed :
      pi ^ (m + (p - 1)) ∣
        (p : 𝓞 K) * y * (pi ^ m * k) * r := by
    refine ⟨q * y * k * r, ?_⟩
    rw [hq, pow_add]
    ring
  rw [hx, hr]
  convert dvd_add hlast hmixed using 1
  ring

/-- A real cyclotomic integer is congruent to a rational integer modulo
the square of the ramified uniformizer. -/
theorem exists_zeta_sub_one_sq_dvd_sub_int_of_real
    (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (a : 𝓞 K)
    (ha : NumberField.IsCMField.ringOfIntegersComplexConj K a = a) :
    ∃ c : ℤ,
      ((hζ.unit' : 𝓞 K) - 1) ^ 2 ∣ a - (c : 𝓞 K) := by
  let pi : 𝓞 K := (hζ.unit' : 𝓞 K) - 1
  obtain ⟨c, k, hk⟩ :=
    exists_zeta_sub_one_dvd_sub_Int hζ a
  have hpi0 : pi ≠ 0 :=
    hζ.unit'_coe.sub_one_ne_zero
      (Fact.out : Nat.Prime p).one_lt
  have hconjk :
      pi ∣
        NumberField.IsCMField.ringOfIntegersComplexConj K k - k := by
    rw [← Ideal.mem_span_singleton,
      ← Ideal.Quotient.eq_zero_iff_mem]
    rw [map_sub,
      ringOfIntegersComplexConj_eq_mod_zeta_sub_one hζ k,
      sub_self]
  have hrel :
      k = ((-hζ.unit'⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
        NumberField.IsCMField.ringOfIntegersComplexConj K k := by
    apply mul_left_cancel₀ hpi0
    calc
      pi * k = a - (c : 𝓞 K) := hk.symm
      _ = NumberField.IsCMField.ringOfIntegersComplexConj K
          (a - (c : 𝓞 K)) := by
        rw [map_sub, ha, map_intCast]
      _ = NumberField.IsCMField.ringOfIntegersComplexConj K
          (pi * k) := by rw [hk]
      _ = pi *
          (((-hζ.unit'⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
            NumberField.IsCMField.ringOfIntegersComplexConj K k) := by
        rw [map_mul]
        change
          NumberField.IsCMField.ringOfIntegersComplexConj K pi *
                NumberField.IsCMField.ringOfIntegersComplexConj K k =
            pi * (((-hζ.unit'⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
              NumberField.IsCMField.ringOfIntegersComplexConj K k)
        rw [show
          NumberField.IsCMField.ringOfIntegersComplexConj K pi =
            (((-hζ.unit'⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * pi) by
              simpa only [pi] using
                ringOfIntegersComplexConj_zeta_sub_one hζ]
        ring
  have huplus :
      pi ∣ (((-hζ.unit'⁻¹ : (𝓞 K)ˣ) : 𝓞 K) + 1) := by
    refine ⟨(hζ.unit'⁻¹ : (𝓞 K)ˣ), ?_⟩
    change
      -((hζ.unit'⁻¹ : (𝓞 K)ˣ) : 𝓞 K) + 1 =
        pi * ((hζ.unit'⁻¹ : (𝓞 K)ˣ) : 𝓞 K)
    have hinv :
        (hζ.unit' : 𝓞 K) *
            (hζ.unit'⁻¹ : (𝓞 K)ˣ) = 1 := by
      rw [← Units.val_mul]
      simp
    calc
      -((hζ.unit'⁻¹ : (𝓞 K)ˣ) : 𝓞 K) + 1 =
          1 - ((hζ.unit'⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by ring
      _ = (hζ.unit' : 𝓞 K) *
            (hζ.unit'⁻¹ : (𝓞 K)ˣ) -
          ((hζ.unit'⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by rw [hinv]
      _ = pi * ((hζ.unit'⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by
        dsimp [pi]
        ring
  have hsum :
      pi ∣
        k + NumberField.IsCMField.ringOfIntegersComplexConj K k := by
    have hmul :=
      dvd_mul_of_dvd_left huplus
        (NumberField.IsCMField.ringOfIntegersComplexConj K k)
    have heq :
        k + NumberField.IsCMField.ringOfIntegersComplexConj K k =
          ((((-hζ.unit'⁻¹ : (𝓞 K)ˣ) : 𝓞 K) + 1) *
            NumberField.IsCMField.ringOfIntegersComplexConj K k) := by
      calc
        k + NumberField.IsCMField.ringOfIntegersComplexConj K k =
            (((-hζ.unit'⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
              NumberField.IsCMField.ringOfIntegersComplexConj K k) +
              NumberField.IsCMField.ringOfIntegersComplexConj K k :=
            congrArg
              (· + NumberField.IsCMField.ringOfIntegersComplexConj K k)
              hrel
        _ = ((((-hζ.unit'⁻¹ : (𝓞 K)ˣ) : 𝓞 K) + 1) *
              NumberField.IsCMField.ringOfIntegersComplexConj K k) := by
          ring
    rw [heq]
    exact hmul
  have htwo : pi ∣ (2 : 𝓞 K) * k := by
    have hdiff :
        pi ∣
          k - NumberField.IsCMField.ringOfIntegersComplexConj K k := by
      simpa only [neg_sub] using dvd_neg.mpr hconjk
    convert dvd_add hsum hdiff using 1
    ring
  have hpinot2 : ¬ pi ∣ (2 : 𝓞 K) := by
    intro htwo
    have hpIntDvd : (p : ℤ) ∣ 2 :=
      (zeta_sub_one_dvd_Int_iff hζ).mp (by
        change
          (hζ.unit' : 𝓞 K) - 1 ∣ ((2 : ℤ) : 𝓞 K)
        norm_num at htwo ⊢
        exact htwo)
    have hpNatDvd : p ∣ 2 := by
      exact_mod_cast hpIntDvd
    have hpLe : p ≤ 2 :=
      Nat.le_of_dvd (by norm_num) hpNatDvd
    have hpOne := (Fact.out : Nat.Prime p).one_lt
    omega
  have hpik : pi ∣ k :=
    (hζ.zeta_sub_one_prime'.dvd_mul.mp htwo).resolve_left hpinot2
  obtain ⟨d, hd⟩ := hpik
  refine ⟨c, d, ?_⟩
  rw [hk, hd]
  ring

/-- If real, nonramified factors occur in a depth-`2*p` product
congruence between `p^2`-th powers, the unit ratio is congruent to the
`p^2`-th power of a rational integer at the same depth. -/
theorem exists_int_ratio_pow_sq_congruent
    (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (U V : (𝓞 K)ˣ) (a b : 𝓞 K)
    (ha_real :
      NumberField.IsCMField.ringOfIntegersComplexConj K a = a)
    (hb_real :
      NumberField.IsCMField.ringOfIntegersComplexConj K b = b)
    (hapi : ¬ ((hζ.unit' : 𝓞 K) - 1) ∣ a)
    (hprod :
      ((hζ.unit' : 𝓞 K) - 1) ^ (2 * p) ∣
        (U : 𝓞 K) * a ^ (p ^ 2) -
          (V : 𝓞 K) * b ^ (p ^ 2)) :
    ∃ c : ℤ,
      ((hζ.unit' : 𝓞 K) - 1) ^ (2 * p) ∣
        (((U / V : (𝓞 K)ˣ) : 𝓞 K) -
          (c : 𝓞 K) ^ (p ^ 2)) := by
  let pi : 𝓞 K := (hζ.unit' : 𝓞 K) - 1
  have hpgt2 : 2 < p := by
    have hpOne := (Fact.out : Nat.Prime p).one_lt
    omega
  obtain ⟨ca, hca⟩ :=
    exists_zeta_sub_one_sq_dvd_sub_int_of_real
      hp2 hζ a ha_real
  obtain ⟨cb, hcb⟩ :=
    exists_zeta_sub_one_sq_dvd_sub_int_of_real
      hp2 hζ b hb_real
  have hpipred : pi ^ (p - 1) ∣ (p : 𝓞 K) := by
    simpa only [pi] using
      (associated_zeta_sub_one_pow_prime hζ).dvd
  have hpi2p : pi ^ 2 ∣ (p : 𝓞 K) :=
    (pow_dvd_pow pi (by omega : 2 ≤ p - 1)).trans hpipred
  have hca_not : ¬ (p : ℤ) ∣ ca := by
    intro hpca
    have hpica : pi ∣ (ca : 𝓞 K) := by
      simpa only [pi] using
        (zeta_sub_one_dvd_Int_iff hζ).mpr hpca
    have hpidiff : pi ∣ a - (ca : 𝓞 K) := by
      simpa only [pow_one] using
        (pow_dvd_pow pi (by norm_num : 1 ≤ 2)).trans hca
    apply hapi
    dsimp only [pi] at hpica hpidiff ⊢
    convert dvd_add hpidiff hpica using 1
    ring
  have hpInt : Prime (p : ℤ) := by
    rw [← Nat.prime_iff_prime_int]
    exact (Fact.out : Nat.Prime p)
  have hcopPca : IsCoprime (p : ℤ) ca :=
    (hpInt.coprime_iff_not_dvd).mpr hca_not
  obtain ⟨u, v, huv⟩ := hcopPca.symm
  let c : ℤ := u * cb
  have hmiddle_int : (p : ℤ) ∣ ca * c - cb := by
    refine ⟨-(v * cb), ?_⟩
    dsimp only [c]
    calc
      ca * (u * cb) - cb = (u * ca - 1) * cb := by ring
      _ = (-(v * p)) * cb := by
        congr 1
        linarith [huv]
      _ = p * -(v * cb) := by ring
  have hmiddle :
      pi ^ 2 ∣
        (ca : 𝓞 K) * (c : 𝓞 K) - (cb : 𝓞 K) := by
    obtain ⟨q, hq⟩ := hmiddle_int
    have hcast :
        (ca : 𝓞 K) * (c : 𝓞 K) - (cb : 𝓞 K) =
          (p : 𝓞 K) * (q : 𝓞 K) := by
      norm_cast
    rw [hcast]
    exact hpi2p.trans (dvd_mul_right _ _)
  have hacb :
      pi ^ 2 ∣ a * (c : 𝓞 K) - b := by
    have hleft :
        pi ^ 2 ∣
          (a - (ca : 𝓞 K)) * (c : 𝓞 K) :=
      dvd_mul_of_dvd_left hca _
    have hright :
        pi ^ 2 ∣ (cb : 𝓞 K) - b := by
      simpa only [neg_sub] using dvd_neg.mpr hcb
    convert dvd_add (dvd_add hleft hmiddle) hright using 1
    ring
  have hpFirst :=
    zeta_sub_one_pow_add_pred_dvd_pow_sub_pow
      hζ 2 (by norm_num) (a * (c : 𝓞 K)) b hacb
  have hfirstDepth : 2 + (p - 1) = p + 1 := by omega
  have hpFirst' :
      pi ^ (p + 1) ∣
        (a * (c : 𝓞 K)) ^ p - b ^ p := by
    rw [← hfirstDepth]
    simpa only [pi] using hpFirst
  have hpSecond :=
    zeta_sub_one_pow_add_pred_dvd_pow_sub_pow
      hζ (p + 1) (by omega)
        ((a * (c : 𝓞 K)) ^ p) (b ^ p) hpFirst'
  have hsecondDepth :
      (p + 1) + (p - 1) = 2 * p := by omega
  have hpowers :
      pi ^ (2 * p) ∣
        a ^ (p ^ 2) * (c : 𝓞 K) ^ (p ^ 2) -
          b ^ (p ^ 2) := by
    rw [← hsecondDepth]
    simpa only [pi, mul_pow, ← pow_mul, pow_two] using hpSecond
  have hcombined :
      pi ^ (2 * p) ∣
        a ^ (p ^ 2) *
          ((U : 𝓞 K) -
            (V : 𝓞 K) * (c : 𝓞 K) ^ (p ^ 2)) := by
    have hscaled :=
      dvd_mul_of_dvd_left hpowers (V : 𝓞 K)
    have hsub := dvd_sub hprod hscaled
    convert hsub using 1
    ring
  have hUV :
      pi ^ (2 * p) ∣
        (U : 𝓞 K) -
          (V : 𝓞 K) * (c : 𝓞 K) ^ (p ^ 2) := by
    have htoInteger :
        hζ.toInteger = (hζ.unit' : 𝓞 K) := by
      apply NumberField.RingOfIntegers.ext
      rfl
    have hapow : ¬ pi ∣ a ^ (p ^ 2) := by
      intro h
      exact hapi
        (hζ.zeta_sub_one_prime'.dvd_of_dvd_pow h)
    apply (hζ.zeta_sub_one_prime').pow_dvd_of_dvd_mul_left
      (2 * p) hapow
    simpa only [pi, htoInteger] using hcombined
  refine ⟨c, ?_⟩
  have hscaled :=
    dvd_mul_of_dvd_left hUV
      (((V⁻¹ : (𝓞 K)ˣ) : 𝓞 K))
  change
    pi ^ (2 * p) ∣
      (U : 𝓞 K) * ((V⁻¹ : (𝓞 K)ˣ) : 𝓞 K) -
        (c : 𝓞 K) ^ (p ^ 2)
  convert hscaled using 1
  rw [sub_mul, mul_assoc, ← Units.val_mul]
  rw [show
    (V : 𝓞 K) *
        ((c : 𝓞 K) ^ (p ^ 2) *
          ((V⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) =
      (c : 𝓞 K) ^ (p ^ 2) *
        (((V : 𝓞 K) *
          ((V⁻¹ : (𝓞 K)ˣ) : 𝓞 K))) by ring,
    ← Units.val_mul]
  simp

/-- The negative square of a unit that is a rational `p^2`-th power
modulo `(ζ - 1)^(2*p)` is a rational `p`-th power modulo
`(1 - ζ)^(2*p)`. -/
theorem exists_int_negative_square_ratio_pow_congruent
    (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (R : (𝓞 K)ˣ) (c : ℤ)
    (h :
      ((hζ.unit' : 𝓞 K) - 1) ^ (2 * p) ∣
        (R : 𝓞 K) - (c : 𝓞 K) ^ (p ^ 2)) :
    ∃ d : ℤ,
      ((1 : 𝓞 K) - hζ.unit') ^ (2 * p) ∣
        (((-(R ^ 2) : (𝓞 K)ˣ) : 𝓞 K) -
          (d : 𝓞 K) ^ p) := by
  refine ⟨-(c ^ (2 * p)), ?_⟩
  have hsquare :
      ((hζ.unit' : 𝓞 K) - 1) ^ (2 * p) ∣
        (R : 𝓞 K) ^ 2 -
          ((c : 𝓞 K) ^ (p ^ 2)) ^ 2 :=
    h.trans
      (sub_dvd_pow_sub_pow
        (R : 𝓞 K) ((c : 𝓞 K) ^ (p ^ 2)) 2)
  have hevenDepth : Even (2 * p) := by
    exact ⟨p, by omega⟩
  have heven :
      ((1 : 𝓞 K) - hζ.unit') ^ (2 * p) =
        ((hζ.unit' : 𝓞 K) - 1) ^ (2 * p) := by
    rw [show
      (1 : 𝓞 K) - hζ.unit' =
        -((hζ.unit' : 𝓞 K) - 1) by ring]
    exact Even.neg_pow hevenDepth _
  rw [heven]
  have hneg := dvd_neg.mpr hsquare
  have hodd : Odd p :=
    (Fact.out : Nat.Prime p).odd_of_ne_two hp2
  have hexp : (2 * p) * p = (p ^ 2) * 2 := by
    rw [pow_two]
    ring
  convert hneg using 1
  simp only [Units.val_neg, Units.val_pow_eq_pow_val,
    Int.cast_neg, Int.cast_pow]
  rw [Odd.neg_pow hodd]
  simp only [← pow_mul]
  rw [hexp]
  ring

end

end Fermat.Irregular.VandiverCongruenceSupportPrime
