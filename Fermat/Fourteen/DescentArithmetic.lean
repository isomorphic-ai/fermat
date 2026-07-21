import Fermat.Fourteen.Dirichlet

/-!
# Elementary arithmetic in Dirichlet's descent

This file collects the order and congruence arguments used at the end of
Dirichlet's direct proof for exponent `14`.  They are independent of the
quadratic-order power extraction: once that extraction supplies the integers
`r` and `s`, these lemmas orient the two signed factors and prove the strict
decrease in the descent height.
-/

namespace Fermat.Fourteen.Dirichlet

/-- The quadratic norm used in the size estimate after the second power
extraction. -/
def rootNorm (r s : ℤ) : ℤ := r ^ 2 + 7 * s ^ 2

/-- Dirichlet's elementary estimate `4 |rs| ≤ r² + 7s²`. -/
theorem four_mul_abs_mul_le_rootNorm (r s : ℤ) :
    4 * |r * s| ≤ rootNorm r s := by
  have h : 0 ≤ (|r| - 2 * |s|) ^ 2 + 3 * |s| ^ 2 := by positivity
  rw [abs_mul]
  simp only [rootNorm]
  nlinarith [sq_abs r, sq_abs s]

/-- The sextic factor occurring in `R` has absolute value at most seven
times the square of the quadratic norm. -/
theorem abs_sexticFactor_le (r s : ℤ) :
    |r ^ 4 - 2 * 7 ^ 2 * r ^ 2 * s ^ 2 + 7 ^ 2 * s ^ 4| ≤
      7 * rootNorm r s ^ 2 := by
  have hr : 0 ≤ r ^ 2 := sq_nonneg r
  have hs : 0 ≤ s ^ 2 := sq_nonneg s
  rw [abs_le]
  simp only [rootNorm]
  constructor <;> nlinarith [sq_nonneg (r ^ 2 + 7 * s ^ 2)]

/-- The bound `|R| ≤ 7(r²+7s²)³` used in the repaired height
argument. -/
theorem abs_R_le_seven_mul_rootNorm_cube (r s : ℤ) :
    |R r s| ≤ 7 * rootNorm r s ^ 3 := by
  have ha : 0 ≤ rootNorm r s := by
    simp only [rootNorm]
    positivity
  change
    |rootNorm r s *
      (r ^ 4 - 2 * 7 ^ 2 * r ^ 2 * s ^ 2 + 7 ^ 2 * s ^ 4)| ≤
        7 * rootNorm r s ^ 3
  rw [abs_mul, abs_of_nonneg ha]
  calc
    rootNorm r s *
          |r ^ 4 - 2 * 7 ^ 2 * r ^ 2 * s ^ 2 + 7 ^ 2 * s ^ 4| ≤
        rootNorm r s * (7 * rootNorm r s ^ 2) :=
      mul_le_mul_of_nonneg_left (abs_sexticFactor_le r s) ha
    _ = 7 * rootNorm r s ^ 3 := by ring

/-- The other summand in each of Dirichlet's final two factors satisfies the
same cubic bound as `R`. -/
theorem abs_seven_mul_four_mul_cube_le_rootNorm_cube (r s : ℤ) :
    |7 * (4 * r * s) ^ 3| ≤ 7 * rootNorm r s ^ 3 := by
  have hbase : |4 * r * s| ≤ rootNorm r s := by
    calc
      |4 * r * s| = 4 * |r * s| := by
        rw [show 4 * r * s = 4 * (r * s) by ring, abs_mul]
        norm_num
      _ ≤ rootNorm r s := four_mul_abs_mul_le_rootNorm r s
  have hnonneg : 0 ≤ rootNorm r s := by
    simp only [rootNorm]
    positivity
  calc
    |7 * (4 * r * s) ^ 3| = 7 * |4 * r * s| ^ 3 := by
      rw [abs_mul, abs_pow]
      norm_num
    _ ≤ 7 * rootNorm r s ^ 3 := by gcongr

/-- Each signed factor produced by the imaginary-part factorization is at
most `14(r²+7s²)³` in absolute value. -/
theorem abs_finalFactor_le_fourteen_mul_rootNorm_cube (r s sign : ℤ)
    (hsign : sign = 1 ∨ sign = -1) :
    |R r s + sign * (7 * (4 * r * s) ^ 3)| ≤
      14 * rootNorm r s ^ 3 := by
  rcases hsign with rfl | rfl
  ·
    calc
      |R r s + 1 * (7 * (4 * r * s) ^ 3)| ≤
          |R r s| + |7 * (4 * r * s) ^ 3| := by
        simpa only [one_mul] using abs_add_le (R r s) (7 * (4 * r * s) ^ 3)
      _ ≤ 7 * rootNorm r s ^ 3 + 7 * rootNorm r s ^ 3 :=
        add_le_add (abs_R_le_seven_mul_rootNorm_cube r s)
          (abs_seven_mul_four_mul_cube_le_rootNorm_cube r s)
      _ = 14 * rootNorm r s ^ 3 := by ring
  ·
    calc
      |R r s + -1 * (7 * (4 * r * s) ^ 3)| ≤
          |R r s| + |7 * (4 * r * s) ^ 3| := by
        simpa only [neg_one_mul, abs_neg] using
          abs_add_le (R r s) (-(7 * (4 * r * s) ^ 3))
      _ ≤ 7 * rootNorm r s ^ 3 + 7 * rootNorm r s ^ 3 :=
        add_le_add (abs_R_le_seven_mul_rootNorm_cube r s)
          (abs_seven_mul_four_mul_cube_le_rootNorm_cube r s)
      _ = 14 * rootNorm r s ^ 3 := by ring

/-- A numerical form of the final strict estimate.  The weak lower bound
`2 ≤ a` is enough by a wide margin. -/
theorem fourteen_mul_cube_lt_pow_fourteen {a : ℕ} (ha : 2 ≤ a) :
    14 * a ^ 3 < a ^ 14 := by
  have ha0 : 0 < a ^ 3 := pow_pos (by omega) _
  have hpow : 2 ^ 11 ≤ a ^ 11 := Nat.pow_le_pow_left ha 11
  have hsixteen : 16 ≤ a ^ 11 := by norm_num at hpow ⊢; omega
  calc
    14 * a ^ 3 < 16 * a ^ 3 := by omega
    _ ≤ a ^ 11 * a ^ 3 := Nat.mul_le_mul_right _ hsixteen
    _ = a ^ 14 := by ring

/-- Integer-valued version of `fourteen_mul_cube_lt_pow_fourteen`, convenient
for the norm `r²+7s²`. -/
theorem fourteen_mul_cube_lt_pow_fourteen_int {a : ℤ} (ha : 2 ≤ a) :
    14 * a ^ 3 < a ^ 14 := by
  have hpow : (2 : ℤ) ^ 11 ≤ a ^ 11 := by gcongr
  have hsixteen : (16 : ℤ) ≤ a ^ 11 := by norm_num at hpow ⊢; omega
  have hacube : 0 < a ^ 3 := by positivity
  calc
    14 * a ^ 3 < 16 * a ^ 3 := by nlinarith
    _ ≤ a ^ 11 * a ^ 3 := mul_le_mul_of_nonneg_right hsixteen hacube.le
    _ = a ^ 14 := by ring

/-- The complete repaired size bound for either sign. -/
theorem abs_finalFactor_lt_rootNorm_pow_fourteen
    {r s sign : ℤ} (ha : 2 ≤ rootNorm r s)
    (hsign : sign = 1 ∨ sign = -1) :
    |R r s + sign * (7 * (4 * r * s) ^ 3)| < rootNorm r s ^ 14 :=
  (abs_finalFactor_le_fourteen_mul_rootNorm_cube r s sign hsign).trans_lt
    (fourteen_mul_cube_lt_pow_fourteen_int ha)

/-- The parity normalization on the root supplied by the quadratic-form
representation theorem. -/
def OppositeParity (r s : ℤ) : Prop :=
  (Even r ∧ Odd s) ∨ (Odd r ∧ Even s)

/-- For roots of opposite parity, Dirichlet's sextic `R` is odd. -/
theorem odd_R {r s : ℤ} (hparity : OppositeParity r s) : Odd (R r s) := by
  rcases hparity with ⟨hr, hs⟩ | ⟨hr, hs⟩
  · have hr' : ¬Odd r := Int.not_odd_iff_even.mpr hr
    have hs' : ¬Even s := Int.not_even_iff_odd.mpr hs
    simp +decide [R, hr, hr', hs', parity_simps]
  · simp +decide [R, hr, hs, parity_simps]

/-- The sextic `R` is coprime to `r`.  The hypothesis `7 ∤ r` is exactly
what is needed when reducing its two factors modulo `r`. -/
theorem isCoprime_R_r {r s : ℤ} (hrs : IsCoprime r s)
    (hseven : ¬(7 : ℤ) ∣ r) : IsCoprime (R r s) r := by
  have h7r : IsCoprime (7 : ℤ) r :=
    (show Prime (7 : ℤ) by norm_num).coprime_iff_not_dvd.mpr hseven
  have hr7 : IsCoprime r (7 : ℤ) := h7r.symm
  have hrFirstBase : IsCoprime r (7 * s ^ 2) :=
    hr7.mul_right (hrs.pow_right (n := 2))
  have hrFirst : IsCoprime r (r ^ 2 + 7 * s ^ 2) := by
    have heq : r ^ 2 + 7 * s ^ 2 = 7 * s ^ 2 + r * r := by ring
    rw [heq]
    exact hrFirstBase.add_mul_left_right r
  have hrSecondBase : IsCoprime r (7 ^ 2 * s ^ 4) :=
    (hr7.pow_right (n := 2)).mul_right (hrs.pow_right (n := 4))
  have hrSecond :
      IsCoprime r (r ^ 4 - 2 * 7 ^ 2 * r ^ 2 * s ^ 2 + 7 ^ 2 * s ^ 4) := by
    have heq : r ^ 4 - 2 * 7 ^ 2 * r ^ 2 * s ^ 2 + 7 ^ 2 * s ^ 4 =
        7 ^ 2 * s ^ 4 + (r ^ 3 - 2 * 7 ^ 2 * r * s ^ 2) * r := by ring
    rw [heq]
    exact hrSecondBase.add_mul_right_right _
  simpa only [R] using (hrFirst.mul_right hrSecond).symm

/-- The sextic `R` is coprime to `s`. -/
theorem isCoprime_R_s {r s : ℤ} (hrs : IsCoprime r s) :
    IsCoprime (R r s) s := by
  have hsFirstBase : IsCoprime s (r ^ 2) := hrs.symm.pow_right (n := 2)
  have hsFirst : IsCoprime s (r ^ 2 + 7 * s ^ 2) := by
    have heq : r ^ 2 + 7 * s ^ 2 = r ^ 2 + s * (7 * s) := by ring
    rw [heq]
    exact hsFirstBase.add_mul_left_right _
  have hsSecondBase : IsCoprime s (r ^ 4) := hrs.symm.pow_right (n := 4)
  have hsSecond :
      IsCoprime s (r ^ 4 - 2 * 7 ^ 2 * r ^ 2 * s ^ 2 + 7 ^ 2 * s ^ 4) := by
    have heq : r ^ 4 - 2 * 7 ^ 2 * r ^ 2 * s ^ 2 + 7 ^ 2 * s ^ 4 =
        r ^ 4 + s * (-2 * 7 ^ 2 * r ^ 2 * s + 7 ^ 2 * s ^ 3) := by ring
    rw [heq]
    exact hsSecondBase.add_mul_left_right _
  simpa only [R] using (hsFirst.mul_right hsSecond).symm

/-- The sextic `R` is coprime to `7` when `7 ∤ r`. -/
theorem isCoprime_R_seven {r s : ℤ} (hseven : ¬(7 : ℤ) ∣ r) :
    IsCoprime (R r s) 7 := by
  have h7r : IsCoprime (7 : ℤ) r :=
    (show Prime (7 : ℤ) by norm_num).coprime_iff_not_dvd.mpr hseven
  have h7FirstBase : IsCoprime (7 : ℤ) (r ^ 2) := h7r.pow_right (n := 2)
  have h7First : IsCoprime (7 : ℤ) (r ^ 2 + 7 * s ^ 2) :=
    h7FirstBase.add_mul_left_right (s ^ 2)
  have h7SecondBase : IsCoprime (7 : ℤ) (r ^ 4) := h7r.pow_right (n := 4)
  have h7Second :
      IsCoprime (7 : ℤ)
        (r ^ 4 - 2 * 7 ^ 2 * r ^ 2 * s ^ 2 + 7 ^ 2 * s ^ 4) := by
    have heq : r ^ 4 - 2 * 7 ^ 2 * r ^ 2 * s ^ 2 + 7 ^ 2 * s ^ 4 =
        r ^ 4 + 7 * (-2 * 7 * r ^ 2 * s ^ 2 + 7 * s ^ 4) := by ring
    rw [heq]
    exact h7SecondBase.add_mul_left_right _
  simpa only [R] using (h7First.mul_right h7Second).symm

/-- `R` and the correction term `7(4rs)³` are coprime under Dirichlet's
primitive and parity hypotheses. -/
theorem isCoprime_R_correction {r s : ℤ} (hrs : IsCoprime r s)
    (hseven : ¬(7 : ℤ) ∣ r) (hparity : OppositeParity r s) :
    IsCoprime (R r s) (7 * (4 * r * s) ^ 3) := by
  have hRtwo : IsCoprime (R r s) 2 := Int.isCoprime_two_right.mpr (odd_R hparity)
  have hRfour : IsCoprime (R r s) 4 := by
    simpa using hRtwo.pow_right (n := 2)
  have hRrs : IsCoprime (R r s) (r * s) :=
    (isCoprime_R_r hrs hseven).mul_right (isCoprime_R_s hrs)
  have hRbase : IsCoprime (R r s) (4 * r * s) := by
    simpa only [mul_assoc] using hRfour.mul_right hRrs
  exact (isCoprime_R_seven hseven).mul_right (hRbase.pow_right (n := 3))

/-- Either signed final factor is coprime to Dirichlet's first displayed
factor `2·7⁵rs`.  This completes the coprimality allocation needed before
extracting the three fourteenth powers. -/
theorem isCoprime_finalFactor_prefactor {r s : ℤ} (hrs : IsCoprime r s)
    (hseven : ¬(7 : ℤ) ∣ r) (hparity : OppositeParity r s) (sign : ℤ) :
    IsCoprime (R r s + sign * (7 * (4 * r * s) ^ 3))
      (2 * 7 ^ 5 * r * s) := by
  let D : ℤ := 7 * (4 * r * s) ^ 3
  have hRtwo : IsCoprime (R r s) 2 := Int.isCoprime_two_right.mpr (odd_R hparity)
  have hRseven : IsCoprime (R r s) 7 := isCoprime_R_seven hseven
  have hRr : IsCoprime (R r s) r := isCoprime_R_r hrs hseven
  have hRs : IsCoprime (R r s) s := isCoprime_R_s hrs
  have hD : Even D := by simp +decide [D, parity_simps]
  have hsignD : Even (sign * D) := hD.mul_left sign
  have hFodd : Odd (R r s + sign * D) := by
    rw [Int.odd_add]
    simpa [hsignD] using odd_R hparity
  have hFtwo : IsCoprime (R r s + sign * D) 2 :=
    Int.isCoprime_two_right.mpr hFodd
  have hFseven : IsCoprime (R r s + sign * D) 7 := by
    have hterm : sign * D = (sign * (4 * r * s) ^ 3) * 7 := by
      simp only [D]
      ring
    rw [hterm]
    exact hRseven.add_mul_right_left _
  have hFr : IsCoprime (R r s + sign * D) r := by
    have hterm : sign * D =
        (sign * 7 * 4 ^ 3 * r ^ 2 * s ^ 3) * r := by
      simp only [D]
      ring
    rw [hterm]
    exact hRr.add_mul_right_left _
  have hFs : IsCoprime (R r s + sign * D) s := by
    have hterm : sign * D =
        (sign * 7 * 4 ^ 3 * r ^ 3 * s ^ 2) * s := by
      simp only [D]
      ring
    rw [hterm]
    exact hRs.add_mul_right_left _
  have hresult : IsCoprime (R r s + sign * D) (2 * 7 ^ 5 * r * s) :=
    ((hFtwo.mul_right (hFseven.pow_right (n := 5))).mul_right hFr).mul_right hFs
  simpa only [D] using hresult

/-- The two odd factors `R ± 7(4rs)³` are coprime. -/
theorem isCoprime_finalFactors {r s : ℤ} (hrs : IsCoprime r s)
    (hseven : ¬(7 : ℤ) ∣ r) (hparity : OppositeParity r s) :
    IsCoprime (R r s + 7 * (4 * r * s) ^ 3)
      (R r s - 7 * (4 * r * s) ^ 3) := by
  let D : ℤ := 7 * (4 * r * s) ^ 3
  have hRD : IsCoprime (R r s) D := isCoprime_R_correction hrs hseven hparity
  have hplusR : IsCoprime (R r s + D) (R r s) := by
    simpa only [mul_one, add_comm] using hRD.symm.add_mul_left_left (1 : ℤ)
  have hplusTwo : IsCoprime (R r s + D) 2 := by
    rw [Int.isCoprime_two_right]
    have hR := odd_R hparity
    have hD : Even D := by simp +decide [D, parity_simps]
    exact Int.odd_add.mpr (by simpa [hD] using hR)
  have hplusTwoR : IsCoprime (R r s + D) (2 * R r s) :=
    hplusTwo.mul_right hplusR
  have hresult : IsCoprime (R r s + D) (R r s - D) := by
    have heq : R r s - D = 2 * R r s + (R r s + D) * (-1) := by ring
    rw [heq]
    exact hplusTwoR.add_mul_left_right _
  simpa only [D] using hresult

/-- The three factors in Dirichlet's page-392 identity are pairwise
coprime. -/
theorem finalFactors_pairwise_isCoprime {r s : ℤ} (hrs : IsCoprime r s)
    (hseven : ¬(7 : ℤ) ∣ r) (hparity : OppositeParity r s) :
    IsCoprime (2 * 7 ^ 5 * r * s) (R r s + 7 * (4 * r * s) ^ 3) ∧
      IsCoprime (2 * 7 ^ 5 * r * s) (R r s - 7 * (4 * r * s) ^ 3) ∧
      IsCoprime (R r s + 7 * (4 * r * s) ^ 3)
        (R r s - 7 * (4 * r * s) ^ 3) := by
  refine ⟨?_, ?_, isCoprime_finalFactors hrs hseven hparity⟩
  · simpa only [one_mul] using
      (isCoprime_finalFactor_prefactor hrs hseven hparity 1).symm
  · simpa only [neg_one_mul, sub_eq_add_neg] using
      (isCoprime_finalFactor_prefactor hrs hseven hparity (-1)).symm

/-- The correction term in the final factors is always even (indeed, it is
divisible by `64`). -/
theorem even_seven_mul_four_mul_cube (r s : ℤ) :
    Even (7 * (4 * r * s) ^ 3) := by
  simp +decide [parity_simps]

/-- Both of Dirichlet's final factors are odd. -/
theorem odd_finalFactors {r s : ℤ} (hparity : OppositeParity r s) :
    Odd (R r s + 7 * (4 * r * s) ^ 3) ∧
      Odd (R r s - 7 * (4 * r * s) ^ 3) := by
  have hR := odd_R hparity
  have hD := even_seven_mul_four_mul_cube r s
  constructor <;> simp [hR, hD, parity_simps]

/-- An odd integer square is congruent to one modulo eight, hence so is its
fourteenth power. -/
theorem odd_fourteenthPower_modEq_one {x : ℤ} (hx : Odd x) :
    x ^ 14 ≡ 1 [ZMOD 8] := by
  have hsquare : x ^ 2 ≡ 1 [ZMOD 8] := by
    rw [Int.modEq_iff_dvd]
    simpa only [neg_sub] using
      (dvd_neg.mpr (Int.eight_dvd_sq_sub_one_of_odd hx))
  simpa [← pow_mul] using hsquare.pow 7

/-- The sum of two odd fourteenth powers is `2` modulo eight and therefore
cannot be divisible by eight. -/
theorem eight_not_dvd_add_fourteenthPowers {x y : ℤ}
    (hx : Odd x) (hy : Odd y) :
    ¬(8 : ℤ) ∣ x ^ 14 + y ^ 14 := by
  intro hdiv
  have htwo : x ^ 14 + y ^ 14 ≡ 2 [ZMOD 8] := by
    simpa using (odd_fourteenthPower_modEq_one hx).add
      (odd_fourteenthPower_modEq_one hy)
  have hzero : x ^ 14 + y ^ 14 ≡ 0 [ZMOD 8] := hdiv.modEq_zero_int
  have : (2 : ℤ) ≡ 0 [ZMOD 8] := htwo.symm.trans hzero
  norm_num [Int.ModEq] at this

/-- If two nonzero signed factors have odd fourteenth powers as their
absolute values and their difference is divisible by eight, then the factors
have the same sign.  This is the orientation argument on page 393. -/
theorem same_sign_of_abs_eq_fourteenthPowers
    {A B x y : ℤ}
    (hA : |A| = x ^ 14) (hB : |B| = y ^ 14)
    (hx : Odd x) (hy : Odd y) (hsub : (8 : ℤ) ∣ A - B) :
    (0 < A ∧ 0 < B) ∨ (A < 0 ∧ B < 0) := by
  have hx0 : x ≠ 0 := by
    intro hxzero
    subst x
    simp at hx
  have hy0 : y ≠ 0 := by
    intro hyzero
    subst y
    simp at hy
  have hA0 : A ≠ 0 := by
    intro hAzero
    subst A
    simp only [abs_zero] at hA
    exact pow_ne_zero 14 hx0 (by omega)
  have hB0 : B ≠ 0 := by
    intro hBzero
    subst B
    simp only [abs_zero] at hB
    exact pow_ne_zero 14 hy0 (by omega)
  rcases lt_or_gt_of_ne hA0 with hAneg | hApos
  · rcases lt_or_gt_of_ne hB0 with hBneg | hBpos
    · exact Or.inr ⟨hAneg, hBneg⟩
    · exfalso
      apply eight_not_dvd_add_fourteenthPowers hx hy
      have hab : -(A - B) = x ^ 14 + y ^ 14 := by
        rw [← hA, ← hB, abs_of_neg hAneg, abs_of_pos hBpos]
        ring
      rw [← hab]
      exact dvd_neg.mpr hsub
  · rcases lt_or_gt_of_ne hB0 with hBneg | hBpos
    · exfalso
      apply eight_not_dvd_add_fourteenthPowers hx hy
      have hab : A - B = x ^ 14 + y ^ 14 := by
        rw [← hA, ← hB, abs_of_pos hApos, abs_of_neg hBneg]
        ring
      rwa [← hab]
    · exact Or.inl ⟨hApos, hBpos⟩

/-- Variant of the orientation lemma in which oddness is known for the
factors themselves.  Oddness of the fourteenth-power bases follows from the
absolute-value equations. -/
theorem same_sign_of_abs_eq_fourteenthPowers_of_odd
    {A B x y : ℤ}
    (hA : |A| = x ^ 14) (hB : |B| = y ^ 14)
    (hAodd : Odd A) (hBodd : Odd B) (hsub : (8 : ℤ) ∣ A - B) :
    (0 < A ∧ 0 < B) ∨ (A < 0 ∧ B < 0) := by
  have hx : Odd x := (Int.odd_pow' (by norm_num : 14 ≠ 0)).mp <| by
    rw [← hA]
    exact odd_abs.mpr hAodd
  have hy : Odd y := (Int.odd_pow' (by norm_num : 14 ≠ 0)).mp <| by
    rw [← hB]
    exact odd_abs.mpr hBodd
  exact same_sign_of_abs_eq_fourteenthPowers hA hB hx hy hsub

/-- The difference of the two final factors is divisible by eight. -/
theorem eight_dvd_finalFactors_sub (r s : ℤ) :
    (8 : ℤ) ∣
      (R r s + 7 * (4 * r * s) ^ 3) - (R r s - 7 * (4 * r * s) ^ 3) := by
  rw [final_factors_sub]
  refine ⟨112 * r ^ 3 * s ^ 3, ?_⟩
  ring

/-- The page-393 sign argument specialized to Dirichlet's two factors. -/
theorem finalFactors_same_sign
    {r s x y : ℤ} (hparity : OppositeParity r s)
    (hplus : |R r s + 7 * (4 * r * s) ^ 3| = x ^ 14)
    (hminus : |R r s - 7 * (4 * r * s) ^ 3| = y ^ 14) :
    (0 < R r s + 7 * (4 * r * s) ^ 3 ∧
        0 < R r s - 7 * (4 * r * s) ^ 3) ∨
      (R r s + 7 * (4 * r * s) ^ 3 < 0 ∧
        R r s - 7 * (4 * r * s) ^ 3 < 0) := by
  rcases odd_finalFactors hparity with ⟨hplusOdd, hminusOdd⟩
  exact same_sign_of_abs_eq_fourteenthPowers_of_odd hplus hminus
    hplusOdd hminusOdd (eight_dvd_finalFactors_sub r s)

end Fermat.Fourteen.Dirichlet
