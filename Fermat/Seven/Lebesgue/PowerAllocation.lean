import Fermat.Seven.Lebesgue.Symmetric

/-!
# Power allocation in Lebesgue's proof for exponent seven

Lebesgue's argument on p. 278 extracts a fourteenth power from

`s ^ 7 = 7 * v * t`.

The source phrases this as a prime-exponent calculation.  Here we give an
equivalent UFD proof that keeps the exceptional prime `7` explicit.  If `7`
divides `t`, split the coprime factors `(7 * t) * v`; otherwise split
`t * (7 * v)`.  In either branch a second coprime factorization of the square
`u ^ 2` forces the relevant seventh-power root to be a square.  The first
branch is impossible modulo `4`, and the second gives Lebesgue's asserted
data

`t = q ^ 14`, `u = q * r`, `v = 7 ^ 6 * p ^ 7`, `s = 7 * p * q ^ 2`.
-/

namespace Fermat.Seven.Lebesgue

/-- Lebesgue's quartic `t` is nonnegative.  The proof is the positive
sum-of-squares identity obtained after putting
`a = x + y`, `b = x + z`, and `c = y + z`:

`16t = 3(a⁴+b⁴+c⁴) + 10(a²b²+a²c²+b²c²)`.
-/
theorem t_nonneg (x y z : ℤ) : 0 ≤ t x y z := by
  let a := x + y
  let b := x + z
  let c := y + z
  have hid :
      16 * t x y z =
        3 * (a ^ 4 + b ^ 4 + c ^ 4) +
          10 * (a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2) := by
    simp only [t, u, s, a, b, c]
    ring
  have ha4 : 0 ≤ a ^ 4 := by positivity
  have hb4 : 0 ≤ b ^ 4 := by positivity
  have hc4 : 0 ≤ c ^ 4 := by positivity
  have hab : 0 ≤ a ^ 2 * b ^ 2 := mul_nonneg (sq_nonneg a) (sq_nonneg b)
  have hac : 0 ≤ a ^ 2 * c ^ 2 := mul_nonneg (sq_nonneg a) (sq_nonneg c)
  have hbc : 0 ≤ b ^ 2 * c ^ 2 := mul_nonneg (sq_nonneg b) (sq_nonneg c)
  nlinarith

private theorem seventh_power_product_roots {A B C : ℤ}
    (hAB : IsCoprime A B) (h : A * B = C ^ 7) :
    ∃ a b : ℤ, A = a ^ 7 ∧ B = b ^ 7 ∧ C = a * b := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ :=
    Int.eq_pow_of_mul_eq_pow_odd hAB (by norm_num : Odd 7) h
  refine ⟨a, b, ha, hb, ?_⟩
  apply (show Odd 7 by norm_num).pow_injective
  calc
    C ^ 7 = A * B := h.symm
    _ = a ^ 7 * b ^ 7 := by rw [ha, hb]
    _ = (a * b) ^ 7 := by ring

private theorem root_coprime_of_pow_coprime_left {a b : ℤ}
    (h : IsCoprime (a ^ 7) b) : IsCoprime a b :=
  (IsCoprime.pow_left_iff (by norm_num : 0 < 7)).mp h

private theorem square_root_of_coprime_square_factor {A D U : ℤ}
    (hAD : IsCoprime A D) (hU : U ^ 2 = A * D) (hApos : 0 < A) :
    ∃ q : ℤ, A = q ^ 2 := by
  obtain ⟨q, hq | hq⟩ := Int.sq_of_isCoprime hAD hU.symm
  · exact ⟨q, hq⟩
  · exfalso
    have hsq : 0 ≤ q ^ 2 := sq_nonneg q
    rw [hq] at hApos
    omega

private theorem coprime_power_difference {A W B : ℤ}
    (hAW : IsCoprime A W) (hAB : IsCoprime A B) :
    IsCoprime A (A ^ 6 - W * B) := by
  have hAWB : IsCoprime A (W * B) := hAW.mul_right hAB
  have h := hAWB
  rw [← IsCoprime.mul_sub_left_right_iff (x := A) (y := W * B) (z := A ^ 5)] at h
  simpa only [show A * A ^ 5 = A ^ 6 by ring] using h

private theorem zmod_four_fourteenth_ne_three (a : ZMod 4) : a ^ 14 ≠ 3 := by
  native_decide +revert

/-- The exceptional allocation `7 ∣ T` in Lebesgue's power extraction is
impossible.  This is the rigorous counterpart of the source's observation
that `7T`, being congruent to `3` modulo `4`, cannot be a square. -/
theorem not_seven_dvd_of_lebesgue_power_data
    {S U V T W : ℤ}
    (hdef : T = U ^ 2 + W * S)
    (hpow : S ^ 7 = 7 * V * T)
    (hTW : IsCoprime T W)
    (hTV : IsCoprime T V)
    (hmod : T ≡ 1 [ZMOD 4])
    (hTnonneg : 0 ≤ T) :
    ¬(7 : ℤ) ∣ T := by
  intro hseven
  have hTpos : 0 < T := by
    have hTne : T ≠ 0 := by
      intro hzero
      have hbad : (0 : ℤ) ≡ 1 [ZMOD 4] := hzero ▸ hmod
      norm_num at hbad
    omega
  have hsevenV : IsCoprime (7 : ℤ) V :=
    hTV.of_isCoprime_of_dvd_left hseven
  have hcop : IsCoprime ((7 : ℤ) * T) V := hsevenV.mul_left hTV
  have hprod : (7 * T) * V = S ^ 7 := by
    rw [hpow]
    ring
  obtain ⟨A, B, hA, hB, hS⟩ := seventh_power_product_roots hcop hprod
  have hsevenA : (7 : ℤ) ∣ A := by
    apply Int.Prime.dvd_pow' Nat.prime_seven
    rw [← hA]
    exact dvd_mul_right 7 T
  obtain ⟨C, hAC⟩ := hsevenA
  have hTfactor : T = A * (7 ^ 5 * C ^ 6) := by
    apply mul_left_cancel₀ (show (7 : ℤ) ≠ 0 by norm_num)
    calc
      7 * T = A ^ 7 := hA
      _ = 7 * (A * (7 ^ 5 * C ^ 6)) := by rw [hAC]; ring
  have hAW : IsCoprime A W := by
    have hsevenW : IsCoprime (7 : ℤ) W :=
      hTW.of_isCoprime_of_dvd_left hseven
    have hpowCop : IsCoprime (A ^ 7) W := by
      rw [← hA]
      exact hsevenW.mul_left hTW
    exact root_coprime_of_pow_coprime_left hpowCop
  have hAB : IsCoprime A B := by
    apply (IsCoprime.pow_iff (by norm_num : 0 < 7) (by norm_num : 0 < 7)).mp
    rw [← hA, ← hB]
    exact hcop
  have hUsq : U ^ 2 = A * (7 ^ 5 * C ^ 6 - W * B) := by
    calc
      U ^ 2 = T - W * S := by rw [hdef]; ring
      _ = A * (7 ^ 5 * C ^ 6) - W * (A * B) := by rw [hTfactor, hS]
      _ = A * (7 ^ 5 * C ^ 6 - W * B) := by ring
  have hAF : IsCoprime A (7 ^ 5 * C ^ 6 - W * B) := by
    have hAWB : IsCoprime A (W * B) := hAW.mul_right hAB
    have hlead : 7 ^ 5 * C ^ 6 = A * (7 ^ 4 * C ^ 5) := by rw [hAC]; ring
    rw [hlead, IsCoprime.mul_sub_left_right_iff]
    exact hAWB
  have hApos : 0 < A := by
    apply (show Odd 7 by norm_num).pow_pos_iff.mp
    rw [← hA]
    positivity
  obtain ⟨q, hAq⟩ := square_root_of_coprime_square_factor hAF hUsq hApos
  have hcastT : (T : ZMod 4) = 1 :=
    (ZMod.intCast_eq_intCast_iff T 1 4).2 hmod
  have hqInt : q ^ 14 = 7 * T := by rw [hA, hAq]; ring
  have hqCast := congrArg (fun n : ℤ ↦ (n : ZMod 4)) hqInt
  apply zmod_four_fourteenth_ne_three (q : ZMod 4)
  simp only [Int.cast_pow, Int.cast_mul, Int.cast_ofNat, hcastT, mul_one] at hqCast
  exact hqCast

/-- Rigorous power allocation for the nonexceptional branch of Lebesgue's
argument. -/
theorem exists_power_data_of_lebesgue
    {S U V T W : ℤ}
    (hdef : T = U ^ 2 + W * S)
    (hpow : S ^ 7 = 7 * V * T)
    (hTW : IsCoprime T W)
    (hTV : IsCoprime T V)
    (hmod : T ≡ 1 [ZMOD 4])
    (hTnonneg : 0 ≤ T)
    (hVeven : Even V) :
    ∃ p q r : ℤ,
      T = q ^ 14 ∧ U = q * r ∧ V = 7 ^ 6 * p ^ 7 ∧
        S = 7 * p * q ^ 2 ∧ Even p ∧
        IsCoprime p q ∧ IsCoprime q r := by
  have hnotseven :=
    not_seven_dvd_of_lebesgue_power_data hdef hpow hTW hTV hmod hTnonneg
  have hsevenCop : IsCoprime T (7 : ℤ) := by
    exact ((show Prime (7 : ℤ) by norm_num).coprime_iff_not_dvd.mpr hnotseven).symm
  have hcop : IsCoprime T ((7 : ℤ) * V) := hsevenCop.mul_right hTV
  have hprod : T * (7 * V) = S ^ 7 := by
    rw [hpow]
    ring
  obtain ⟨A, B, hA, hB, hS⟩ := seventh_power_product_roots hcop hprod
  have hTpos : 0 < T := by
    have hTne : T ≠ 0 := by
      intro hzero
      have hbad : (0 : ℤ) ≡ 1 [ZMOD 4] := hzero ▸ hmod
      norm_num at hbad
    omega
  have hApos : 0 < A := by
    apply (show Odd 7 by norm_num).pow_pos_iff.mp
    rw [← hA]
    exact hTpos
  have hAW : IsCoprime A W := by
    apply root_coprime_of_pow_coprime_left
    simpa only [hA] using hTW
  have hAB : IsCoprime A B := by
    apply (IsCoprime.pow_iff (by norm_num : 0 < 7) (by norm_num : 0 < 7)).mp
    rw [← hA, ← hB]
    exact hcop
  have hUsq : U ^ 2 = A * (A ^ 6 - W * B) := by
    calc
      U ^ 2 = T - W * S := by rw [hdef]; ring
      _ = A ^ 7 - W * (A * B) := by rw [hA, hS]
      _ = A * (A ^ 6 - W * B) := by ring
  have hAF : IsCoprime A (A ^ 6 - W * B) :=
    coprime_power_difference hAW hAB
  obtain ⟨q, hAq⟩ := square_root_of_coprime_square_factor hAF hUsq hApos
  have hTq : T = q ^ 14 := by rw [hA, hAq]; ring
  have hqU : q ∣ U := by
    apply (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd
      (R := ℤ) (n := 2) (by norm_num)).mp
    refine ⟨A ^ 6 - W * B, ?_⟩
    rw [hUsq, hAq]
  obtain ⟨r, hUr⟩ := hqU
  have hsevenB : (7 : ℤ) ∣ B := by
    apply Int.Prime.dvd_pow' Nat.prime_seven
    rw [← hB]
    exact dvd_mul_right 7 V
  obtain ⟨p, hBp⟩ := hsevenB
  have hVp : V = 7 ^ 6 * p ^ 7 := by
    apply mul_left_cancel₀ (show (7 : ℤ) ≠ 0 by norm_num)
    calc
      7 * V = B ^ 7 := hB
      _ = 7 * (7 ^ 6 * p ^ 7) := by rw [hBp]; ring
  have hSpq : S = 7 * p * q ^ 2 := by rw [hS, hAq, hBp]; ring
  have hpEven : Even p := by
    rw [even_iff_two_dvd] at hVeven ⊢
    rw [hVp] at hVeven
    have hp7 : (2 : ℤ) ∣ p ^ 7 :=
      (Int.Prime.dvd_mul' Nat.prime_two hVeven).resolve_left (by norm_num)
    exact Int.Prime.dvd_pow' Nat.prime_two hp7
  have hpq : IsCoprime p q := by
    have h := hTV
    rw [hTq, hVp] at h
    have hqpPowers : IsCoprime (q ^ 14) (p ^ 7) := h.of_mul_right_right
    exact ((IsCoprime.pow_iff (by norm_num : 0 < 14) (by norm_num : 0 < 7)).mp
      hqpPowers).symm
  have hqne : q ≠ 0 := by
    intro hq
    have hAzero : A = 0 := by rw [hAq, hq]; norm_num
    omega
  have hFr : A ^ 6 - W * B = r ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hqne)
    calc
      q ^ 2 * (A ^ 6 - W * B) = A * (A ^ 6 - W * B) := by rw [hAq]
      _ = U ^ 2 := hUsq.symm
      _ = (q * r) ^ 2 := by rw [hUr]
      _ = q ^ 2 * r ^ 2 := by ring
  have hqr : IsCoprime q r := by
    have h := hAF
    rw [hFr, hAq] at h
    exact (IsCoprime.pow_iff (by norm_num : 0 < 2) (by norm_num : 0 < 2)).mp h
  exact ⟨p, q, r, hTq, hUr, hVp, hSpq, hpEven, hpq, hqr⟩

/-- The remaining coprimality in Lebesgue's extracted triple follows from
primitivity of `x,y,z`.  A prime dividing both `p` and `r` would divide
`s`, `u`, and `v`, hence `xyz`; the symmetric identities then force it to
divide two of `x,y,z`. -/
theorem isCoprime_p_r_of_symmetric_data
    {x y z p q r : ℤ}
    (hxy : IsCoprime x y) (hxz : IsCoprime x z)
    (hur : u x y z = q * r)
    (hvp : v x y z = 7 ^ 6 * p ^ 7)
    (hspq : s x y z = 7 * p * q ^ 2)
    (htmod : t x y z ≡ 1 [ZMOD 4]) :
    IsCoprime p r := by
  refine isCoprime_of_prime_dvd ?_ (fun θ hθ hθp hθr ↦ ?_)
  · rintro ⟨rfl, rfl⟩
    have hs0 : s x y z = 0 := by simpa using hspq
    have hu0 : u x y z = 0 := by simpa using hur
    have ht0 : t x y z = 0 := by simp [t, hs0, hu0]
    have hbad : (0 : ℤ) ≡ 1 [ZMOD 4] := ht0 ▸ htmod
    norm_num at hbad
  · have hθs : θ ∣ s x y z := by
      rw [hspq]
      exact ((hθp.mul_left 7).mul_right (q ^ 2))
    have hθu : θ ∣ u x y z := by
      rw [hur]
      exact hθr.mul_left q
    have hθv : θ ∣ v x y z := by
      rw [hvp]
      exact (dvd_pow hθp (by norm_num)).mul_left (7 ^ 6)
    let e₂ := x * y + x * z + y * z
    have hθe₂ : θ ∣ e₂ := by
      have hs2 : θ ∣ s x y z ^ 2 := dvd_pow hθs (by norm_num)
      have hsub : θ ∣ s x y z ^ 2 - u x y z := dvd_sub hs2 hθu
      have heq : s x y z ^ 2 - u x y z = e₂ := by
        rw [u_eq_s_sq_sub]
        simp only [e₂]
        ring
      rwa [heq] at hsub
    have hθxyz : θ ∣ x * y * z := by
      have hprod : θ ∣ s x y z * e₂ := hθs.mul_right e₂
      have hsub : θ ∣ s x y z * e₂ - v x y z := dvd_sub hprod hθv
      have heq : s x y z * e₂ - v x y z = x * y * z := by
        rw [v_eq_s_mul_sub_xyz]
        simp only [e₂]
        ring
      rwa [heq] at hsub
    rcases hθ.dvd_mul.mp hθxyz with hθxy | hθz
    · rcases hθ.dvd_mul.mp hθxy with hθx | hθy
      · have hθy2 : θ ∣ y ^ 2 := by
          have hzS : θ ∣ z * s x y z := hθs.mul_left z
          have hxTerm : θ ∣ x * (x + y) := hθx.mul_right (x + y)
          have hcomb : θ ∣ u x y z - z * s x y z - x * (x + y) :=
            dvd_sub (dvd_sub hθu hzS) hxTerm
          convert hcomb using 1
          simp only [u, s]
          ring
        have hθy : θ ∣ y := hθ.dvd_of_dvd_pow hθy2
        exact hθ.not_unit (hxy.isUnit_of_dvd' hθx hθy)
      · have hθx2 : θ ∣ x ^ 2 := by
          have hzS : θ ∣ z * s x y z := hθs.mul_left z
          have hyTerm : θ ∣ y * (x + y) := hθy.mul_right (x + y)
          have hcomb : θ ∣ u x y z - z * s x y z - y * (x + y) :=
            dvd_sub (dvd_sub hθu hzS) hyTerm
          convert hcomb using 1
          simp only [u, s]
          ring
        have hθx : θ ∣ x := hθ.dvd_of_dvd_pow hθx2
        exact hθ.not_unit (hxy.isUnit_of_dvd' hθx hθy)
    · have hθx2 : θ ∣ x ^ 2 := by
        have hyS : θ ∣ y * s x y z := hθs.mul_left y
        have hzTerm : θ ∣ z * (x + z) := hθz.mul_right (x + z)
        have hcomb : θ ∣ u x y z - y * s x y z - z * (x + z) :=
          dvd_sub (dvd_sub hθu hyS) hzTerm
        convert hcomb using 1
        simp only [u, s]
        ring
      have hθx : θ ∣ x := hθ.dvd_of_dvd_pow hθx2
      exact hθ.not_unit (hxz.isUnit_of_dvd' hθx hθz)

/-- The power data in the notation of Lebesgue's symmetric polynomials. -/
theorem exists_power_data_of_symmetric
    {x y z : ℤ}
    (hpow : s x y z ^ 7 = 7 * v x y z * t x y z)
    (htxyz : IsCoprime (t x y z) (x * y * z))
    (htv : IsCoprime (t x y z) (v x y z))
    (htmod : t x y z ≡ 1 [ZMOD 4])
    (hveven : Even (v x y z)) :
    ∃ p q r : ℤ,
      t x y z = q ^ 14 ∧ u x y z = q * r ∧
        v x y z = 7 ^ 6 * p ^ 7 ∧
        s x y z = 7 * p * q ^ 2 ∧ Even p ∧
        IsCoprime p q ∧ IsCoprime q r := by
  apply exists_power_data_of_lebesgue
      (S := s x y z) (U := u x y z) (V := v x y z)
      (T := t x y z) (W := x * y * z)
  · rfl
  · exact hpow
  · exact htxyz
  · exact htv
  · exact htmod
  · exact t_nonneg x y z
  · exact hveven

/-- Lebesgue's full extracted triple, including the pairwise coprimalities
used in the substitution into Theorem I. -/
theorem exists_pairwise_power_data_of_symmetric
    {x y z : ℤ}
    (hxy : IsCoprime x y) (hxz : IsCoprime x z)
    (hpow : s x y z ^ 7 = 7 * v x y z * t x y z)
    (htxyz : IsCoprime (t x y z) (x * y * z))
    (htv : IsCoprime (t x y z) (v x y z))
    (htmod : t x y z ≡ 1 [ZMOD 4])
    (hveven : Even (v x y z)) :
    ∃ p q r : ℤ,
      t x y z = q ^ 14 ∧ u x y z = q * r ∧
        v x y z = 7 ^ 6 * p ^ 7 ∧
        s x y z = 7 * p * q ^ 2 ∧ Even p ∧
        IsCoprime p q ∧ IsCoprime p r ∧ IsCoprime q r := by
  obtain ⟨p, q, r, htq, hur, hvp, hspq, hpEven, hpq, hqr⟩ :=
    exists_power_data_of_symmetric hpow htxyz htv htmod hveven
  have hpr := isCoprime_p_r_of_symmetric_data hxy hxz hur hvp hspq htmod
  exact ⟨p, q, r, htq, hur, hvp, hspq, hpEven, hpq, hpr, hqr⟩

end Fermat.Seven.Lebesgue
