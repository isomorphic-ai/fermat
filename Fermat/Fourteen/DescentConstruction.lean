import Fermat.Fourteen.FirstCase

/-!
# Construction of the smaller Dirichlet solution

This file carries out the second signed power extraction, splits the three
coprime factors on page 392, normalizes their powers of `7`, and constructs
the strictly smaller solution required by infinite descent.
-/

namespace Fermat.Fourteen.Dirichlet

open Fermat.Fourteen.PowerExtraction

def finalPrefactor (r s : ℤ) : ℤ := 2 * 7 ^ 5 * r * s
def plusFactor (r s : ℤ) : ℤ := R r s + 7 * (4 * r * s) ^ 3
def minusFactor (r s : ℤ) : ℤ := R r s - 7 * (4 * r * s) ^ 3

theorem oppositeParity_psi_scaledChi {t u chi : ℤ}
    (hparity : OppositeParity chi (psi t u)) :
    (Odd (psi t u) ∧ Even (7 ^ 2 * chi ^ 3)) ∨
      (Even (psi t u) ∧ Odd (7 ^ 2 * chi ^ 3)) := by
  rcases hparity with ⟨hchi, hpsi⟩ | ⟨hchi, hpsi⟩
  · left
    refine ⟨hpsi, ?_⟩
    simp +decide [hchi, parity_simps]
  · right
    refine ⟨hpsi, ?_⟩
    exact (by norm_num : Odd (7 ^ 2 : ℤ)).mul hchi.pow

theorem oppositeParity_of_odd_rootNorm {r s : ℤ} (hodd : Odd (rootNorm r s)) :
    OppositeParity r s := by
  rcases Int.even_or_odd r with hr | hr <;> rcases Int.even_or_odd s with hs | hs
  · exfalso
    have : Even (rootNorm r s) := by
      simp +decide [rootNorm, hr, hs, parity_simps]
    exact Int.not_even_iff_odd.mpr hodd this
  · exact Or.inl ⟨hr, hs⟩
  · exact Or.inr ⟨hr, hs⟩
  · exfalso
    have hr' : ¬Even r := Int.not_even_iff_odd.mpr hr
    have hs' : ¬Even s := Int.not_even_iff_odd.mpr hs
    have : Even (rootNorm r s) := by
      simp +decide [rootNorm, hr', hs', parity_simps]
    exact Int.not_even_iff_odd.mpr hodd this

/-- Consequences of the second signed power extraction. -/
structure RootData {t u w : ℤ} {m n : ℕ} {chi a b : ℤ}
    (p : Prepared t u w m n chi a b) (r s : ℤ) : Prop where
  signed_power :
    (⟨psi t u, 7 ^ 2 * chi ^ 3⟩ : Zsqrtd (-7)) =
        (⟨r, s⟩ : Zsqrtd (-7)) ^ 14 ∨
      (⟨psi t u, 7 ^ 2 * chi ^ 3⟩ : Zsqrtd (-7)) =
        -((⟨r, s⟩ : Zsqrtd (-7)) ^ 14)
  norm_eq : rootNorm r s = a
  coprime : IsCoprime r s
  parity : OppositeParity r s
  r_not_seven : ¬(7 : ℤ) ∣ r
  r_ne_zero : r ≠ 0
  s_ne_zero : s ≠ 0

theorem Prepared.extractRoot {t u w : ℤ} {m n : ℕ} {chi a b : ℤ}
    (p : Prepared t u w m n chi a b) :
    ∃ r s : ℤ, RootData p r s := by
  have hpsiSeven : IsCoprime (psi t u) (7 : ℤ) :=
    ((show Prime (7 : ℤ) by norm_num).coprime_iff_not_dvd.mpr p.psi_not_seven).symm
  have hPQ : IsCoprime (psi t u) (7 ^ 2 * chi ^ 3) :=
    (hpsiSeven.pow_right (n := 2)).mul_right (p.chi_psi_coprime.symm.pow_right (n := 3))
  obtain ⟨r, s, hpow⟩ := exists_signed_fourteenthPower_in_suborder
    (psi t u) (7 ^ 2 * chi ^ 3) a hPQ
    (oppositeParity_psi_scaledChi p.chi_psi_parity) p.psi_not_seven p.quadratic_eq
  let q : Zsqrtd (-7) := ⟨r, s⟩
  have hnormQ : Zsqrtd.norm (q ^ 14) = Zsqrtd.norm q ^ 14 :=
    Zsqrtd.normMonoidHom.map_pow q 14
  have hnormPower : quadraticFactor chi (psi t u) = rootNorm r s ^ 14 := by
    rcases hpow with hpow | hpow
    · have h := congrArg Zsqrtd.norm hpow
      rw [hnormQ] at h
      convert h using 1 <;>
        simp [q, quadraticFactor, rootNorm, Zsqrtd.norm, pow_two] <;> ring
    · have h := congrArg Zsqrtd.norm hpow
      rw [Zsqrtd.norm_neg, hnormQ] at h
      convert h using 1 <;>
        simp [q, quadraticFactor, rootNorm, Zsqrtd.norm, pow_two] <;> ring
  have hrootNonneg : 0 ≤ rootNorm r s := by
    simp only [rootNorm]
    positivity
  have hroot : rootNorm r s = a := by
    apply (pow_left_inj₀ hrootNonneg p.a_pos.le (by norm_num : 14 ≠ 0)).mp
    exact hnormPower.symm.trans p.quadratic_eq
  have hrootCoprime : IsCoprime r s := by
    have hdiv : q ∣ (⟨psi t u, 7 ^ 2 * chi ^ 3⟩ : Zsqrtd (-7)) := by
      rcases hpow with hpow | hpow
      · rw [hpow]
        exact dvd_pow_self q (by norm_num)
      · rw [hpow]
        exact dvd_neg.mpr (dvd_pow_self q (by norm_num))
    simpa only [q] using Zsqrtd.isCoprime_of_dvd_isCoprime hPQ hdiv
  have haOdd : Odd a := by
    have hquadOdd := odd_quadraticFactor p.chi_psi_parity
    rw [p.quadratic_eq] at hquadOdd
    exact (Int.odd_pow' (by norm_num : 14 ≠ 0)).mp hquadOdd
  have hrootParity : OppositeParity r s := by
    apply oppositeParity_of_odd_rootNorm
    rwa [hroot]
  have haSeven : ¬(7 : ℤ) ∣ a := by
    intro ha
    apply not_seven_dvd_quadraticFactor p.psi_not_seven
    rw [p.quadratic_eq]
    exact dvd_pow ha (by norm_num)
  have hrSeven : ¬(7 : ℤ) ∣ r := by
    intro hr
    apply haSeven
    rw [← hroot]
    simp only [rootNorm]
    exact dvd_add (dvd_pow hr (by norm_num)) (dvd_mul_right 7 (s ^ 2))
  have himNonzero : ((q ^ 14).im) ≠ 0 := by
    intro him
    have hQzero : 7 ^ 2 * chi ^ 3 = 0 := by
      rcases hpow with hpow | hpow
      · have h := congrArg Zsqrtd.im hpow
        simpa only [q, him] using h
      · have h := congrArg Zsqrtd.im hpow
        simpa only [q, Zsqrtd.im_neg, him, neg_zero] using h
    have : 0 < 7 ^ 2 * chi ^ 3 :=
      mul_pos (by norm_num) (pow_pos p.chi_pos 3)
    omega
  have hr0 : r ≠ 0 := by
    intro hr
    subst r
    apply himNonzero
    rw [im_pow_fourteen]
    ring
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    apply himNonzero
    rw [im_pow_fourteen]
    ring
  exact ⟨r, s, hpow, hroot, hrootCoprime, hrootParity, hrSeven, hr0, hs0⟩

theorem RootData.finalProduct_signed {t u w : ℤ} {m n : ℕ} {chi a b : ℤ}
    {p : Prepared t u w m n chi a b} {r s : ℤ} (d : RootData p r s) :
    finalPrefactor r s * plusFactor r s * minusFactor r s = 7 ^ 6 * chi ^ 3 ∨
      finalPrefactor r s * plusFactor r s * minusFactor r s = -(7 ^ 6 * chi ^ 3) := by
  have hscaled := scaled_im_pow_fourteen r s
  rcases d.signed_power with hpow | hpow
  · left
    simp only [finalPrefactor, plusFactor, minusFactor]
    rw [← hscaled]
    have him := congrArg Zsqrtd.im hpow
    change 7 ^ 2 * chi ^ 3 = ((⟨r, s⟩ : Zsqrtd (-7)) ^ 14).im at him
    rw [← him]
    ring
  · right
    simp only [finalPrefactor, plusFactor, minusFactor]
    rw [← hscaled]
    have him := congrArg Zsqrtd.im hpow
    change 7 ^ 2 * chi ^ 3 = -((⟨r, s⟩ : Zsqrtd (-7)) ^ 14).im at him
    rw [show ((⟨r, s⟩ : Zsqrtd (-7)) ^ 14).im = -(7 ^ 2 * chi ^ 3) by omega]
    ring

theorem Prepared.scaled_cube {t u w : ℤ} {m n : ℕ} {chi a b : ℤ}
    (p : Prepared t u w m n chi a b) :
    7 ^ 6 * chi ^ 3 =
      ((2 : ℤ) ^ m * 7 ^ (n + 1)) ^ 3 * (b ^ 3) ^ 14 := by
  calc
    7 ^ 6 * chi ^ 3 = (scaledPhi chi) ^ 3 := by simp only [scaledPhi]; ring
    _ = ((2 : ℤ) ^ m * 7 ^ (n + 1) * b ^ 14) ^ 3 := by rw [p.scaled_eq]
    _ = ((2 : ℤ) ^ m * 7 ^ (n + 1)) ^ 3 * (b ^ 3) ^ 14 := by ring

private theorem isCoprime_coefficientCube_factor {r s F : ℤ} {m n : ℕ}
    (h : IsCoprime (finalPrefactor r s) F) :
    IsCoprime (((2 : ℤ) ^ m * 7 ^ (n + 1)) ^ 3) F := by
  have hbase : IsCoprime ((2 : ℤ) * (7 * 7 ^ 4)) F := by
    have := h.of_mul_left_left.of_mul_left_left
    norm_num [finalPrefactor] at this ⊢
    exact this
  have htwo : IsCoprime (2 : ℤ) F := hbase.of_mul_left_left
  have hseven : IsCoprime (7 : ℤ) F := hbase.of_mul_left_right.of_mul_left_left
  have hK : IsCoprime ((2 : ℤ) ^ m * 7 ^ (n + 1)) F :=
    (htwo.pow_left (m := m)).mul_left (hseven.pow_left (m := n + 1))
  exact hK.pow_left (m := 3)

/-- The three-factor allocation, before the special `n = 0` normalization. -/
structure SplitData {t u w : ℤ} {m n : ℕ} {chi a b r s : ℤ}
    {p : Prepared t u w m n chi a b} (d : RootData p r s) (V x y : ℤ) : Prop where
  plus_abs : |plusFactor r s| = x ^ 14
  minus_abs : |minusFactor r s| = y ^ 14
  prefactor_abs :
    |finalPrefactor r s| = ((2 : ℤ) ^ m * 7 ^ (n + 1)) ^ 3 * V ^ 14
  x_ne_zero : x ≠ 0
  y_ne_zero : y ≠ 0
  xy_coprime : IsCoprime x y

theorem RootData.splitFactors {t u w : ℤ} {m n : ℕ} {chi a b r s : ℤ}
    {p : Prepared t u w m n chi a b} (d : RootData p r s) :
    ∃ V x y : ℤ, SplitData d V x y := by
  let K : ℤ := (2 : ℤ) ^ m * 7 ^ (n + 1)
  let F0 := finalPrefactor r s
  let Fp := plusFactor r s
  let Fm := minusFactor r s
  have hpairs := finalFactors_pairwise_isCoprime d.coprime d.r_not_seven d.parity
  have h0p : IsCoprime F0 Fp := by
    simpa only [F0, Fp, finalPrefactor, plusFactor] using hpairs.1
  have h0m : IsCoprime F0 Fm := by
    simpa only [F0, Fm, finalPrefactor, minusFactor] using hpairs.2.1
  have hpm : IsCoprime Fp Fm := by
    simpa only [Fp, Fm, plusFactor, minusFactor] using hpairs.2.2
  have hKp : IsCoprime (K ^ 3) Fp := by
    simpa only [K, F0, Fp] using
      isCoprime_coefficientCube_factor (m := m) (n := n) h0p
  have hKm : IsCoprime (K ^ 3) Fm := by
    simpa only [K, F0, Fm] using
      isCoprime_coefficientCube_factor (m := m) (n := n) h0m
  have hKpm : IsCoprime (K ^ 3) (Fp * Fm) := hKp.mul_right hKm
  have hwhole : F0 * Fp * Fm = K ^ 3 * (b ^ 3) ^ 14 ∨
      F0 * Fp * Fm = -(K ^ 3 * (b ^ 3) ^ 14) := by
    rcases d.finalProduct_signed with h | h
    · left
      exact h.trans p.scaled_cube
    · right
      rw [h, p.scaled_cube]
  have hKdvd : K ^ 3 ∣ F0 := by
    apply hKpm.dvd_of_dvd_mul_right
    rcases hwhole with h | h
    · rw [show F0 * (Fp * Fm) = K ^ 3 * (b ^ 3) ^ 14 by
        simpa only [mul_assoc] using h]
      exact dvd_mul_right (K ^ 3) _
    · rw [show F0 * (Fp * Fm) = -(K ^ 3 * (b ^ 3) ^ 14) by
        simpa only [mul_assoc] using h]
      exact dvd_neg.mpr (dvd_mul_right (K ^ 3) _)
  obtain ⟨e, hF0⟩ := hKdvd
  have hKpos : 0 < K := by dsimp only [K]; positivity
  have heWhole : e * Fp * Fm = (b ^ 3) ^ 14 ∨
      e * Fp * Fm = -((b ^ 3) ^ 14) := by
    rcases hwhole with h | h
    · left
      apply mul_left_cancel₀ (pow_ne_zero 3 hKpos.ne')
      calc
        K ^ 3 * (e * Fp * Fm) = F0 * Fp * Fm := by rw [hF0]; ring
        _ = K ^ 3 * (b ^ 3) ^ 14 := h
    · right
      apply mul_left_cancel₀ (pow_ne_zero 3 hKpos.ne')
      calc
        K ^ 3 * (e * Fp * Fm) = F0 * Fp * Fm := by rw [hF0]; ring
        _ = -(K ^ 3 * (b ^ 3) ^ 14) := h
        _ = K ^ 3 * (-((b ^ 3) ^ 14)) := by ring
  have hassoc : Associated ((b ^ 3) ^ 14) (e * Fp * Fm) := by
    rw [Int.associated_iff_natAbs]
    rcases heWhole with h | h <;> simp [h]
  have hep : IsCoprime e Fp := by
    rw [hF0] at h0p
    exact h0p.of_mul_left_right
  have hem : IsCoprime e Fm := by
    rw [hF0] at h0m
    exact h0m.of_mul_left_right
  obtain ⟨x, y, hx, hy⟩ := exists_two_pow_eq_abs_of_associated_pow_three
    hep hem hpm (by decide : Even 14) hassoc
  have hepm : IsCoprime e (Fp * Fm) := hep.mul_right hem
  obtain ⟨V, hV⟩ := exists_pow_eq_abs_of_associated_pow_mul_left
    hepm (by decide : Even 14) (by simpa only [mul_assoc] using hassoc)
  have hF0abs : |F0| = K ^ 3 * V ^ 14 := by
    rw [hF0, abs_mul, abs_of_pos (pow_pos hKpos 3), hV]
  have hxy : IsCoprime x y := by
    have h := hpm.abs_abs
    rw [hx, hy] at h
    exact (IsCoprime.pow_iff (by norm_num) (by norm_num)).mp h
  have hx0 : x ≠ 0 := by
    intro hx0
    subst x
    have hzero : Fp = 0 := by simpa using hx
    have hzero' : plusFactor r s = 0 := by simpa only [Fp] using hzero
    have hodd : Odd (plusFactor r s) := by
      simpa only [plusFactor] using (odd_finalFactors d.parity).1
    rw [hzero'] at hodd
    simp at hodd
  have hy0 : y ≠ 0 := by
    intro hy0
    subst y
    have hzero : Fm = 0 := by simpa using hy
    have hzero' : minusFactor r s = 0 := by simpa only [Fm] using hzero
    have hodd : Odd (minusFactor r s) := by
      simpa only [minusFactor] using (odd_finalFactors d.parity).2
    rw [hzero'] at hodd
    simp at hodd
  exact ⟨V, x, y, hx, hy, hF0abs, hx0, hy0, hxy⟩

theorem SplitData.prefactor_equation {t u w : ℤ} {m n : ℕ}
    {chi a b r s V x y : ℤ} {p : Prepared t u w m n chi a b}
    {d : RootData p r s} (e : SplitData d V x y) :
    2 * 7 ^ 5 * |r * s| =
      (2 : ℤ) ^ (3 * m) * 7 ^ (3 * (n + 1)) * V ^ 14 := by
  calc
    2 * 7 ^ 5 * |r * s| = |finalPrefactor r s| := by
      simp only [finalPrefactor, abs_mul]
      norm_num
      ring
    _ = ((2 : ℤ) ^ m * 7 ^ (n + 1)) ^ 3 * V ^ 14 := e.prefactor_abs
    _ = (2 : ℤ) ^ (3 * m) * 7 ^ (3 * (n + 1)) * V ^ 14 := by
      simp [mul_pow, ← pow_mul, Nat.mul_comm]

/-- Normalize the exceptional power of `7` in the first displayed factor.
For `n > 0` this subtracts five powers of `7`; for `n = 0`, divisibility
forces `7 ∣ V`, whose fourteenth power supplies the deficit. -/
theorem normalize_prefactor {r s V : ℤ} {m n : ℕ}
    (heq : 2 * 7 ^ 5 * |r * s| =
      (2 : ℤ) ^ (3 * m) * 7 ^ (3 * (n + 1)) * V ^ 14) :
    ∃ n' : ℕ, ∃ V' : ℤ,
      4 * |r * s| = (2 : ℤ) ^ (3 * m + 1) * 7 ^ (n' + 1) * V' ^ 14 := by
  rcases n with _ | k
  · have hcancel : (2 : ℤ) ^ (3 * m) * V ^ 14 = 7 ^ 2 * (2 * |r * s|) := by
      apply mul_left_cancel₀ (show (7 : ℤ) ^ 3 ≠ 0 by norm_num)
      calc
        7 ^ 3 * ((2 : ℤ) ^ (3 * m) * V ^ 14) =
            (2 : ℤ) ^ (3 * m) * 7 ^ (3 * (0 + 1)) * V ^ 14 := by ring
        _ = 2 * 7 ^ 5 * |r * s| := heq.symm
        _ = 7 ^ 3 * (7 ^ 2 * (2 * |r * s|)) := by ring
    have hsevenProduct : (7 : ℤ) ∣ (2 : ℤ) ^ (3 * m) * V ^ 14 := by
      rw [hcancel]
      refine ⟨7 * (2 * |r * s|), ?_⟩
      ring
    have hsevenTwo : IsCoprime (7 : ℤ) ((2 : ℤ) ^ (3 * m)) := by
      have h : IsCoprime (7 : ℤ) (2 : ℤ) := by norm_num
      exact h.pow_right (n := 3 * m)
    have hsevenVpow : (7 : ℤ) ∣ V ^ 14 :=
      hsevenTwo.dvd_of_dvd_mul_left hsevenProduct
    have hsevenV : (7 : ℤ) ∣ V :=
      (show Prime (7 : ℤ) by norm_num).dvd_of_dvd_pow hsevenVpow
    obtain ⟨V', rfl⟩ := hsevenV
    refine ⟨11, V', ?_⟩
    apply mul_left_cancel₀ (show (7 : ℤ) ^ 5 ≠ 0 by norm_num)
    calc
      7 ^ 5 * (4 * |r * s|) = 2 * (2 * 7 ^ 5 * |r * s|) := by ring
      _ = 2 * ((2 : ℤ) ^ (3 * m) * 7 ^ (3 * (0 + 1)) * (7 * V') ^ 14) := by rw [heq]
      _ = 7 ^ 5 * ((2 : ℤ) ^ (3 * m + 1) * 7 ^ (11 + 1) * V' ^ 14) := by ring
  · refine ⟨3 * k, V, ?_⟩
    apply mul_left_cancel₀ (show (7 : ℤ) ^ 5 ≠ 0 by norm_num)
    calc
      7 ^ 5 * (4 * |r * s|) = 2 * (2 * 7 ^ 5 * |r * s|) := by ring
      _ = 2 * ((2 : ℤ) ^ (3 * m) * 7 ^ (3 * (k + 1 + 1)) * V ^ 14) := by rw [heq]
      _ = 7 ^ 5 * ((2 : ℤ) ^ (3 * m + 1) * 7 ^ (3 * k + 1) * V ^ 14) := by
        rw [show 3 * (k + 1 + 1) = 5 + (3 * k + 1) by omega, pow_add]
        rw [show 3 * m + 1 = 1 + 3 * m by omega, pow_add]
        ring

theorem SplitData.roots_abs_lt_a {t u w : ℤ} {m n : ℕ}
    {chi a b r s V x y : ℤ} {p : Prepared t u w m n chi a b}
    {d : RootData p r s} (e : SplitData d V x y) : |x| < a ∧ |y| < a := by
  have hrSq : 1 ≤ r ^ 2 := by
    have := sq_pos_of_ne_zero d.r_ne_zero
    omega
  have hsSq : 1 ≤ s ^ 2 := by
    have := sq_pos_of_ne_zero d.s_ne_zero
    omega
  have hrootEight : 8 ≤ rootNorm r s := by
    simp only [rootNorm]
    nlinarith
  have haTwo : 2 ≤ a := by rw [← d.norm_eq]; omega
  have hplusBound : |plusFactor r s| < a ^ 14 := by
    have h := abs_finalFactor_lt_rootNorm_pow_fourteen
      (r := r) (s := s) (sign := 1) (by omega) (Or.inl rfl)
    simpa only [plusFactor, one_mul, d.norm_eq] using h
  have hminusBound : |minusFactor r s| < a ^ 14 := by
    have h := abs_finalFactor_lt_rootNorm_pow_fourteen
      (r := r) (s := s) (sign := -1) (by omega) (Or.inr rfl)
    simpa only [minusFactor, neg_one_mul, sub_eq_add_neg, d.norm_eq] using h
  constructor
  · apply (pow_lt_pow_iff_left₀ (abs_nonneg x) p.a_pos.le (by norm_num : 14 ≠ 0)).mp
    calc
      |x| ^ 14 = x ^ 14 := (show Even 14 by decide).pow_abs x
      _ = |plusFactor r s| := e.plus_abs.symm
      _ < a ^ 14 := hplusBound
  · apply (pow_lt_pow_iff_left₀ (abs_nonneg y) p.a_pos.le (by norm_num : 14 ≠ 0)).mp
    calc
      |y| ^ 14 = y ^ 14 := (show Even 14 by decide).pow_abs y
      _ = |minusFactor r s| := e.minus_abs.symm
      _ < a ^ 14 := hminusBound

/-- Orient the two same-sign factors so their difference is the positive
quantity involving `|rs|`. -/
theorem SplitData.exists_oriented {t u w : ℤ} {m n : ℕ}
    {chi a b r s V x y : ℤ} {p : Prepared t u w m n chi a b}
    {d : RootData p r s} (e : SplitData d V x y) :
    ∃ T U : ℤ, T ≠ 0 ∧ U ≠ 0 ∧ IsCoprime T U ∧
      |T| < a ∧ |U| < a ∧
      T ^ 14 - U ^ 14 = 14 * (4 * |r * s|) ^ 3 := by
  have hrs0 : r * s ≠ 0 := mul_ne_zero d.r_ne_zero d.s_ne_zero
  have hdiff : plusFactor r s - minusFactor r s = 14 * (4 * r * s) ^ 3 := by
    simpa only [plusFactor, minusFactor] using final_factors_sub r s
  have hbounds := e.roots_abs_lt_a
  rcases finalFactors_same_sign d.parity e.plus_abs e.minus_abs with hpos | hneg
  · have hposp : 0 < plusFactor r s := by simpa only [plusFactor] using hpos.1
    have hposm : 0 < minusFactor r s := by simpa only [minusFactor] using hpos.2
    have hp := e.plus_abs
    have hm := e.minus_abs
    rw [abs_of_pos hposp] at hp
    rw [abs_of_pos hposm] at hm
    rcases lt_or_gt_of_ne hrs0 with hrs | hrs
    · refine ⟨y, x, e.y_ne_zero, e.x_ne_zero, e.xy_coprime.symm,
        hbounds.2, hbounds.1, ?_⟩
      calc
        y ^ 14 - x ^ 14 = -(plusFactor r s - minusFactor r s) := by rw [hp, hm]; ring
        _ = -(14 * (4 * r * s) ^ 3) := by rw [hdiff]
        _ = 14 * (4 * |r * s|) ^ 3 := by rw [abs_of_neg hrs]; ring
    · refine ⟨x, y, e.x_ne_zero, e.y_ne_zero, e.xy_coprime,
        hbounds.1, hbounds.2, ?_⟩
      calc
        x ^ 14 - y ^ 14 = plusFactor r s - minusFactor r s := by rw [hp, hm]
        _ = 14 * (4 * r * s) ^ 3 := hdiff
        _ = 14 * (4 * |r * s|) ^ 3 := by rw [abs_of_pos hrs]; ring
  · have hnegp : plusFactor r s < 0 := by simpa only [plusFactor] using hneg.1
    have hnegm : minusFactor r s < 0 := by simpa only [minusFactor] using hneg.2
    have hp := e.plus_abs
    have hm := e.minus_abs
    rw [abs_of_neg hnegp] at hp
    rw [abs_of_neg hnegm] at hm
    rcases lt_or_gt_of_ne hrs0 with hrs | hrs
    · refine ⟨x, y, e.x_ne_zero, e.y_ne_zero, e.xy_coprime,
        hbounds.1, hbounds.2, ?_⟩
      calc
        x ^ 14 - y ^ 14 = -(plusFactor r s - minusFactor r s) := by rw [← hp, ← hm]; ring
        _ = -(14 * (4 * r * s) ^ 3) := by rw [hdiff]
        _ = 14 * (4 * |r * s|) ^ 3 := by rw [abs_of_neg hrs]; ring
    · refine ⟨y, x, e.y_ne_zero, e.x_ne_zero, e.xy_coprime.symm,
        hbounds.2, hbounds.1, ?_⟩
      calc
        y ^ 14 - x ^ 14 = plusFactor r s - minusFactor r s := by rw [← hp, ← hm]; ring
        _ = 14 * (4 * r * s) ^ 3 := hdiff
        _ = 14 * (4 * |r * s|) ^ 3 := by rw [abs_of_pos hrs]; ring

/-- The quadratic-form root norm is already strictly below the old descent
height. -/
theorem Prepared.a_lt_abs_t {t u w : ℤ} {m n : ℕ} {chi a b : ℤ}
    (h : DescentEquation t u w m n) (p : Prepared t u w m n chi a b) :
    a < |t| := by
  have hu : u ≠ 0 := by
    intro hu
    subst u
    simp [DescentEquation] at h
  have huPow : 0 < u ^ 14 := (show Even 14 by decide).pow_pos hu
  have hmain : t ^ 14 - u ^ 14 = scaledPhi chi * a ^ 14 := by
    calc
      t ^ 14 - u ^ 14 = scaledPhi chi * quadraticFactor chi (psi t u) :=
        factorization_with_chi p.phi_eq
      _ = scaledPhi chi * a ^ 14 := by rw [p.quadratic_eq]
  have hproductLt : scaledPhi chi * a ^ 14 < t ^ 14 := by omega
  have hscale : 1 ≤ scaledPhi chi := by
    simp only [scaledPhi]
    nlinarith [p.chi_pos]
  have haPowNonneg : 0 ≤ a ^ 14 := (show Even 14 by decide).pow_nonneg a
  have haLeProduct : a ^ 14 ≤ scaledPhi chi * a ^ 14 := by
    have := mul_nonneg (sub_nonneg.mpr hscale) haPowNonneg
    nlinarith
  have haPowLt : a ^ 14 < |t| ^ 14 := by
    rw [(show Even 14 by decide).pow_abs]
    exact haLeProduct.trans_lt hproductLt
  exact (pow_lt_pow_iff_left₀ p.a_pos.le (abs_nonneg t) (by norm_num : 14 ≠ 0)).mp haPowLt

/-- Substitute the normalized first factor into the oriented difference. -/
theorem new_descent_equation {r s V' T U : ℤ} {m n' : ℕ}
    (hrs : 4 * |r * s| =
      (2 : ℤ) ^ (3 * m + 1) * 7 ^ (n' + 1) * V' ^ 14)
    (hTU : T ^ 14 - U ^ 14 = 14 * (4 * |r * s|) ^ 3) :
    T ^ 14 - U ^ 14 =
      (2 : ℤ) ^ (9 * m + 4) * 7 ^ ((3 * n' + 3) + 1) * (V' ^ 3) ^ 14 := by
  rw [hTU, hrs]
  simp only [mul_pow, ← pow_mul]
  rw [show (3 * m + 1) * 3 = 9 * m + 3 by omega]
  rw [show (n' + 1) * 3 = 3 * n' + 3 by omega]
  rw [show 9 * m + 4 = 1 + (9 * m + 3) by omega, pow_add]
  rw [show 3 * n' + 3 + 1 = 1 + (3 * n' + 3) by omega, pow_add]
  ring

/-- Dirichlet's explicit construction satisfies the abstract strict-descent
obligation. -/
theorem descends : Descends := by
  intro t u w m n h
  obtain ⟨chi, a, b, p⟩ := h.prepare
  obtain ⟨r, s, d⟩ := p.extractRoot
  obtain ⟨V, x, y, e⟩ := d.splitFactors
  obtain ⟨n', V', hnormalized⟩ := normalize_prefactor e.prefactor_equation
  obtain ⟨T, U, hT0, hU0, hTUcoprime, hTlt, -, hTU⟩ := e.exists_oriented
  have hrs0 : r * s ≠ 0 := mul_ne_zero d.r_ne_zero d.s_ne_zero
  have hV'0 : V' ≠ 0 := by
    intro hV'
    subst V'
    have hleft : 0 < 4 * |r * s| := by positivity
    have hzero : 4 * |r * s| = 0 := by simpa using hnormalized
    exact hleft.ne' hzero
  have hnew : DescentEquation T U (V' ^ 3) (9 * m + 4) (3 * n' + 3) := by
    refine ⟨?_, hTUcoprime, new_descent_equation hnormalized hTU⟩
    exact mul_ne_zero (mul_ne_zero hT0 hU0) (pow_ne_zero 3 hV'0)
  have haOld : a < |t| := p.a_lt_abs_t h
  have hheightZ : |T| < |t| := hTlt.trans haOld
  have hheight : height T < height t := by
    simp only [height]
    apply Int.ofNat_lt.mp
    simpa only [Int.natCast_natAbs] using hheightZ
  exact ⟨T, U, V' ^ 3, 9 * m + 4, 3 * n' + 3, hnew, hheight⟩

/-- Dirichlet's original 1832 proof of the `n = 14` case, independent of
the `n = 7` theorem. -/
theorem holdsAt_fourteen_dirichlet : Fermat.HoldsAt 14 :=
  holdsAt_fourteen_of_dirichlet firstCaseImpossible descends

end Fermat.Fourteen.Dirichlet
