import Fermat.ThirtySeven.VandiverHistorical
import Fermat.ThirtySeven.VandiverRelationNormalization

/-!
# Local congruence support for Vandiver's historical descent at 37

This file formalizes the local calculation between equations (9a) and (10)
in Vandiver's 1929 proof.

A real cyclotomic integer has a rational-integer residue modulo
`(ζ - 1)^2`, rather than merely modulo `ζ - 1`.  Applying the ramified
37th-power depth step twice then turns congruence modulo `(ζ - 1)^2` into
congruence modulo `(ζ - 1)^74` for 1369th powers.  The final two theorems
package the quotient and negative-square forms used in equation (10).
-/

namespace Fermat.ThirtySeven.VandiverHistorical

open scoped NumberField nonZeroDivisors

open Fermat.ThirtySeven.VandiverRelationNormalization

noncomputable section

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {37} ℚ K]

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩
local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 37) K (by norm_num)

/-- A real cyclotomic integer is congruent to a rational integer modulo the
square of the ramified uniformizer.

Starting from `a - c = (ζ - 1)k`, conjugation shows that `k + conj k` is
divisible by `ζ - 1`; conjugation is itself the identity modulo `ζ - 1`,
so `2k` is divisible.  Since the prime above 37 does not divide 2, it
divides `k`. -/
theorem exists_zeta_sub_one_sq_dvd_sub_int_of_real37
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37) (a : 𝓞 K)
    (ha : NumberField.IsCMField.ringOfIntegersComplexConj K a = a) :
    ∃ c : ℤ, ((hζ.unit' : 𝓞 K) - 1) ^ 2 ∣ a - (c : 𝓞 K) := by
  let π : 𝓞 K := (hζ.unit' : 𝓞 K) - 1
  obtain ⟨c, k, hk⟩ := exists_zeta_sub_one_dvd_sub_Int hζ a
  have hπ0 : π ≠ 0 :=
    hζ.unit'_coe.sub_one_ne_zero (by norm_num)
  have hconjk :
      π ∣ NumberField.IsCMField.ringOfIntegersComplexConj K k - k := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
    rw [map_sub,
      ringOfIntegersComplexConj_eq_mod_zeta_sub_one37 hζ k,
      sub_self]
  have hrel :
      k = ((-hζ.unit'⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
        NumberField.IsCMField.ringOfIntegersComplexConj K k := by
    apply mul_left_cancel₀ hπ0
    calc
      π * k = a - (c : 𝓞 K) := hk.symm
      _ = NumberField.IsCMField.ringOfIntegersComplexConj K
          (a - (c : 𝓞 K)) := by rw [map_sub, ha, map_intCast]
      _ = NumberField.IsCMField.ringOfIntegersComplexConj K (π * k) := by
        rw [hk]
      _ = π * (((-hζ.unit'⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
          NumberField.IsCMField.ringOfIntegersComplexConj K k) := by
        rw [map_mul]
        change
          NumberField.IsCMField.ringOfIntegersComplexConj K π *
              NumberField.IsCMField.ringOfIntegersComplexConj K k =
            π * (((-hζ.unit'⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
              NumberField.IsCMField.ringOfIntegersComplexConj K k)
        rw [show NumberField.IsCMField.ringOfIntegersComplexConj K π =
          (((-hζ.unit'⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * π) by
            simpa only [π] using
              ringOfIntegersComplexConj_zeta_sub_one37 hζ]
        ring
  have huplus :
      π ∣ (((-hζ.unit'⁻¹ : (𝓞 K)ˣ) : 𝓞 K) + 1) := by
    refine ⟨(hζ.unit'⁻¹ : (𝓞 K)ˣ), ?_⟩
    change -((hζ.unit'⁻¹ : (𝓞 K)ˣ) : 𝓞 K) + 1 =
      π * ((hζ.unit'⁻¹ : (𝓞 K)ˣ) : 𝓞 K)
    have hinv :
        (hζ.unit' : 𝓞 K) * (hζ.unit'⁻¹ : (𝓞 K)ˣ) = 1 := by
      rw [← Units.val_mul]
      simp
    calc
      -((hζ.unit'⁻¹ : (𝓞 K)ˣ) : 𝓞 K) + 1 =
          1 - ((hζ.unit'⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by ring
      _ = (hζ.unit' : 𝓞 K) * (hζ.unit'⁻¹ : (𝓞 K)ˣ) -
          ((hζ.unit'⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by rw [hinv]
      _ = π * ((hζ.unit'⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by
        dsimp [π]
        ring
  have hsum :
      π ∣ k + NumberField.IsCMField.ringOfIntegersComplexConj K k := by
    have hmul := dvd_mul_of_dvd_left huplus
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
  have htwo : π ∣ (2 : 𝓞 K) * k := by
    have hdiff :
        π ∣ k - NumberField.IsCMField.ringOfIntegersComplexConj K k := by
      simpa only [neg_sub] using dvd_neg.mpr hconjk
    convert dvd_add hsum hdiff using 1
    ring
  have hπnot2 : ¬ π ∣ (2 : 𝓞 K) := by
    intro htwo
    have : (37 : ℤ) ∣ 2 := (zeta_sub_one_dvd_Int_iff hζ).mp (by
      change (hζ.unit' : 𝓞 K) - 1 ∣ ((2 : ℤ) : 𝓞 K)
      norm_num at htwo ⊢
      exact htwo)
    norm_num at this
  have hπk : π ∣ k :=
    (hζ.zeta_sub_one_prime'.dvd_mul.mp htwo).resolve_left hπnot2
  obtain ⟨d, hd⟩ := hπk
  refine ⟨c, d, ?_⟩
  rw [hk, hd]
  ring

/-- If real, nonramified factors `a` and `b` occur in a depth-74 product
congruence

`U*a^(37²) ≡ V*b^(37²)`,

then `U/V` is congruent to the 1369th power of a rational integer at the
same depth.

The rational residue of `a` is invertible modulo 37.  A Bézout inverse
therefore chooses a rational multiplier making `a*c` and `b` congruent
modulo `(ζ - 1)^2`; two applications of the ramified power-depth lemma lift
this to depth 74. -/
theorem exists_int_ratio_pow1369_congruent37
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    (U V : (𝓞 K)ˣ) (a b : 𝓞 K)
    (ha_real : NumberField.IsCMField.ringOfIntegersComplexConj K a = a)
    (hb_real : NumberField.IsCMField.ringOfIntegersComplexConj K b = b)
    (haπ : ¬ ((hζ.unit' : 𝓞 K) - 1) ∣ a)
    (hprod :
      ((hζ.unit' : 𝓞 K) - 1) ^ 74 ∣
        (U : 𝓞 K) * a ^ 1369 - (V : 𝓞 K) * b ^ 1369) :
    ∃ c : ℤ,
      ((hζ.unit' : 𝓞 K) - 1) ^ 74 ∣
        (((U / V : (𝓞 K)ˣ) : 𝓞 K) - (c : 𝓞 K) ^ 1369) := by
  let π : 𝓞 K := (hζ.unit' : 𝓞 K) - 1
  obtain ⟨ca, hca⟩ :=
    exists_zeta_sub_one_sq_dvd_sub_int_of_real37 hζ a ha_real
  obtain ⟨cb, hcb⟩ :=
    exists_zeta_sub_one_sq_dvd_sub_int_of_real37 hζ b hb_real
  have hπ36 : π ^ 36 ∣ (37 : 𝓞 K) := by
    simpa only [π] using (associated_zeta_sub_one_pow_prime hζ).dvd
  have hπ2_37 : π ^ 2 ∣ (37 : 𝓞 K) :=
    (pow_dvd_pow π (by norm_num : 2 ≤ 36)).trans hπ36
  have hca_not : ¬ (37 : ℤ) ∣ ca := by
    intro h37ca
    have hπca : π ∣ (ca : 𝓞 K) := by
      simpa only [π] using
        (zeta_sub_one_dvd_Int_iff hζ).mpr h37ca
    have hπdiff : π ∣ a - (ca : 𝓞 K) := by
      simpa only [pow_one] using
        (pow_dvd_pow π (by norm_num : 1 ≤ 2)).trans hca
    apply haπ
    dsimp only [π] at hπca hπdiff ⊢
    convert dvd_add hπdiff hπca using 1
    ring
  have hcop37ca : IsCoprime (37 : ℤ) ca :=
    ((show Prime (37 : ℤ) by norm_num).coprime_iff_not_dvd).mpr hca_not
  obtain ⟨u, v, huv⟩ := hcop37ca.symm
  let c : ℤ := u * cb
  have hmiddle_int : (37 : ℤ) ∣ ca * c - cb := by
    refine ⟨-(v * cb), ?_⟩
    dsimp only [c]
    calc
      ca * (u * cb) - cb = (u * ca - 1) * cb := by ring
      _ = (-(v * 37)) * cb := by
        congr 1
        linarith [huv]
      _ = 37 * -(v * cb) := by ring
  have hmiddle :
      π ^ 2 ∣ (ca : 𝓞 K) * (c : 𝓞 K) - (cb : 𝓞 K) := by
    obtain ⟨q, hq⟩ := hmiddle_int
    have hcast :
        (ca : 𝓞 K) * (c : 𝓞 K) - (cb : 𝓞 K) =
          (37 : 𝓞 K) * (q : 𝓞 K) := by
      norm_cast
    rw [hcast]
    exact hπ2_37.trans (dvd_mul_right _ _)
  have hacb : π ^ 2 ∣ a * (c : 𝓞 K) - b := by
    have hleft : π ^ 2 ∣
        (a - (ca : 𝓞 K)) * (c : 𝓞 K) :=
      dvd_mul_of_dvd_left hca _
    have hright : π ^ 2 ∣ (cb : 𝓞 K) - b := by
      simpa only [neg_sub] using dvd_neg.mpr hcb
    convert dvd_add (dvd_add hleft hmiddle) hright using 1
    ring
  have hp38 :=
    zeta_sub_one_pow_add_thirtySix_dvd_pow_sub_pow37
      hζ 2 (by norm_num) (a * (c : 𝓞 K)) b hacb
  have hp74 :=
    zeta_sub_one_pow_add_thirtySix_dvd_pow_sub_pow37
      hζ 38 (by norm_num)
      ((a * (c : 𝓞 K)) ^ 37) (b ^ 37)
      (by simpa only [π] using hp38)
  have hpowers :
      π ^ 74 ∣
        a ^ 1369 * (c : 𝓞 K) ^ 1369 - b ^ 1369 := by
    simpa only [π, mul_pow, ← pow_mul] using hp74
  have hcombined :
      π ^ 74 ∣
        a ^ 1369 *
          ((U : 𝓞 K) - (V : 𝓞 K) * (c : 𝓞 K) ^ 1369) := by
    have hscaled := dvd_mul_of_dvd_left hpowers (V : 𝓞 K)
    have hsub := dvd_sub hprod hscaled
    convert hsub using 1
    ring
  have hUV :
      π ^ 74 ∣
        (U : 𝓞 K) - (V : 𝓞 K) * (c : 𝓞 K) ^ 1369 := by
    have hapow : ¬ π ∣ a ^ 1369 := by
      intro h
      exact haπ (hζ.zeta_sub_one_prime'.dvd_of_dvd_pow h)
    apply hζ.zeta_sub_one_prime'.pow_dvd_of_dvd_mul_left 74 hapow
    simpa only [π] using hcombined
  refine ⟨c, ?_⟩
  have hscaled := dvd_mul_of_dvd_left hUV
    (((V⁻¹ : (𝓞 K)ˣ) : 𝓞 K))
  change π ^ 74 ∣
    (U : 𝓞 K) * ((V⁻¹ : (𝓞 K)ˣ) : 𝓞 K) -
      (c : 𝓞 K) ^ 1369
  convert hscaled using 1
  rw [sub_mul, mul_assoc, ← Units.val_mul]
  rw [show (V : 𝓞 K) *
      ((c : 𝓞 K) ^ 1369 * ((V⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) =
        (c : 𝓞 K) ^ 1369 *
          (((V : 𝓞 K) * ((V⁻¹ : (𝓞 K)ˣ) : 𝓞 K))) by ring,
    ← Units.val_mul]
  simp

/-- The negative square of a unit which is a rational 1369th power modulo
`(ζ - 1)^74` is a rational 37th power modulo `(1 - ζ)^74`.

Concretely, if `R ≡ c^1369`, then

`-R² ≡ (-c^74)^37`.

The change from `ζ - 1` to `1 - ζ` is harmless because the exponent 74 is
even. -/
theorem exists_int_negative_square_ratio_pow37_congruent37
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    (R : (𝓞 K)ˣ) (c : ℤ)
    (h :
      ((hζ.unit' : 𝓞 K) - 1) ^ 74 ∣
        (R : 𝓞 K) - (c : 𝓞 K) ^ 1369) :
    ∃ d : ℤ,
      ((1 : 𝓞 K) - hζ.unit') ^ 74 ∣
        (((-(R ^ 2) : (𝓞 K)ˣ) : 𝓞 K) - (d : 𝓞 K) ^ 37) := by
  refine ⟨-(c ^ 74), ?_⟩
  have hsquare :
      ((hζ.unit' : 𝓞 K) - 1) ^ 74 ∣
        (R : 𝓞 K) ^ 2 - ((c : 𝓞 K) ^ 1369) ^ 2 :=
    h.trans (sub_dvd_pow_sub_pow (R : 𝓞 K) ((c : 𝓞 K) ^ 1369) 2)
  have heven :
      ((1 : 𝓞 K) - hζ.unit') ^ 74 =
        ((hζ.unit' : 𝓞 K) - 1) ^ 74 := by
    rw [show (1 : 𝓞 K) - hζ.unit' =
      -((hζ.unit' : 𝓞 K) - 1) by ring]
    exact Even.neg_pow (by norm_num) _
  rw [heven]
  have hneg := dvd_neg.mpr hsquare
  convert hneg using 1
  norm_num [Units.val_neg, Units.val_pow_eq_pow_val, ← pow_mul]
  rw [Odd.neg_pow (by norm_num : Odd 37)]
  norm_num [← pow_mul]
  ring

end

end Fermat.ThirtySeven.VandiverHistorical
