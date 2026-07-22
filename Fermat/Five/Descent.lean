import Fermat.Five.PowerSplitting
import Fermat.Five.PowerExtraction

/-!
# Dirichlet's two descents for exponent five

This file records the elementary arithmetic after the fifth-power extraction
in `ℤ[√5]`.  It deliberately keeps the two parity branches in the
normalization used in Dirichlet's 1828 addition:

* `5^h s F(t,s) = 16 w^5` when `t,s` are odd;
* `2^g 5^h s F(t,s) = w^5` when `t` is odd and `s` is even.

The new second coordinate is strictly smaller.  Its coefficient exponents
are respectively `2h+1` and `(2g-1,2h+1)`, so minimality of a positive
second coordinate rules out both families.
-/

namespace Fermat.Five.Dirichlet

open Fermat.Five.PowerExtraction

/-- The quartic factor occurring in both of Dirichlet's descents. -/
def F (t s : ℕ) : ℕ := t ^ 4 + 10 * t ^ 2 * s ^ 2 + 5 * s ^ 4

/-- The odd-coordinate normalization on Crelle p. 374. -/
structure OddState (h t s w : ℕ) : Prop where
  equation : 5 ^ h * s * F t s = 16 * w ^ 5
  t_pos : 0 < t
  s_pos : 0 < s
  w_pos : 0 < w
  coprime : t.Coprime s
  t_odd : Odd t
  s_odd : Odd s
  s_five : 5 ∣ s
  t_not_five : ¬5 ∣ t

/-- The opposite-parity normalization used in the other historical branch. -/
structure EvenState (g h t s w : ℕ) : Prop where
  equation : 2 ^ g * 5 ^ h * s * F t s = w ^ 5
  g_pos : 0 < g
  t_pos : 0 < t
  s_pos : 0 < s
  w_pos : 0 < w
  coprime : t.Coprime s
  t_odd : Odd t
  s_even : Even s
  s_five : 5 ∣ s
  t_not_five : ¬5 ∣ t

theorem F_pos {t s : ℕ} (ht : 0 < t) : 0 < F t s := by
  simp only [F]
  positivity

theorem five_coprime_F {t s : ℕ} (ht : ¬5 ∣ t) : Nat.Coprime 5 (F t s) := by
  have h5t : Nat.Coprime 5 t := Nat.prime_five.coprime_iff_not_dvd.mpr ht
  have h5t4 : Nat.Coprime 5 (t ^ 4) := h5t.pow_right 4
  rw [show F t s = t ^ 4 + (2 * t ^ 2 * s ^ 2 + s ^ 4) * 5 by
    simp only [F]
    ring]
  exact (Nat.coprime_add_mul_right_right 5 (t ^ 4)
    (2 * t ^ 2 * s ^ 2 + s ^ 4)).mpr h5t4

theorem s_coprime_F {t s : ℕ} (hts : t.Coprime s) : s.Coprime (F t s) := by
  have hst4 : s.Coprime (t ^ 4) := hts.symm.pow_right 4
  rw [show F t s = t ^ 4 + (10 * t ^ 2 * s + 5 * s ^ 3) * s by
    simp only [F]
    ring]
  exact (Nat.coprime_add_mul_right_right s (t ^ 4)
    (10 * t ^ 2 * s + 5 * s ^ 3)).mpr hst4

theorem not_five_dvd_F {t s : ℕ} (ht : ¬5 ∣ t) : ¬5 ∣ F t s := by
  exact Nat.prime_five.coprime_iff_not_dvd.mp (five_coprime_F ht)

private theorem zmod_sixteen_F_odd :
    ∀ a b : ZMod 16,
      (2 * a + 1) ^ 4 + 10 * (2 * a + 1) ^ 2 * (2 * b + 1) ^ 2 +
          5 * (2 * b + 1) ^ 4 = 0 := by
  decide

/-- For odd inputs the quartic factor contains Dirichlet's exact factor `16`. -/
theorem sixteen_dvd_F_of_odd {t s : ℕ} (ht : Odd t) (hs : Odd s) : 16 ∣ F t s := by
  obtain ⟨a, rfl⟩ := ht
  obtain ⟨b, rfl⟩ := hs
  rw [← ZMod.natCast_eq_zero_iff]
  simpa only [F, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
    zmod_sixteen_F_odd (a : ZMod 16) (b : ZMod 16)

/-- In the even branch the quartic factor is odd. -/
theorem odd_F_of_odd_even {t s : ℕ} (ht : Odd t) (hs : Even s) : Odd (F t s) := by
  rcases ht with ⟨a, rfl⟩
  rcases hs with ⟨b, rfl⟩
  refine ⟨8 * a ^ 4 + 16 * a ^ 3 + 12 * a ^ 2 + 4 * a +
      80 * a ^ 2 * b ^ 2 + 80 * a * b ^ 2 + 20 * b ^ 2 + 40 * b ^ 4, ?_⟩
  simp only [F]
  ring

theorem odd_F_of_even_odd {t s : ℕ} (ht : Even t) (hs : Odd s) : Odd (F t s) := by
  rcases ht with ⟨a, rfl⟩
  rcases hs with ⟨b, rfl⟩
  refine ⟨8 * a ^ 4 + 20 * a ^ 2 * (4 * b ^ 2 + 4 * b + 1) +
      40 * b ^ 4 + 80 * b ^ 3 + 60 * b ^ 2 + 20 * b + 2, ?_⟩
  simp only [F]
  ring

theorem odd_factor_coprime {h t s : ℕ} (hts : t.Coprime s)
    (hfive : ¬5 ∣ t) : (5 ^ h * s).Coprime (F t s) := by
  exact ((five_coprime_F hfive).pow_left h).mul_left (s_coprime_F hts)

theorem even_factor_coprime {g h t s : ℕ} (hts : t.Coprime s)
    (htodd : Odd t) (hseven : Even s) (hfive : ¬5 ∣ t) :
    (2 ^ g * 5 ^ h * s).Coprime (F t s) := by
  have h2 : Nat.Coprime 2 (F t s) := (odd_F_of_odd_even htodd hseven).coprime_two_left
  exact ((h2.pow_left g).mul_left ((five_coprime_F hfive).pow_left h)).mul_left
    (s_coprime_F hts)

private theorem exists_nat_pow_of_coprime_mul {a b c k : ℕ}
    (hab : a.Coprime b) (heq : a * b = c ^ k) : ∃ d : ℕ, a = d ^ k := by
  apply exists_eq_pow_of_mul_eq_pow
  · rw [show GCDMonoid.gcd a b = 1 by exact hab.gcd_eq_one]
    exact isUnit_one
  · exact heq

/-- Unique factorization after removing the exact displayed factor `16`. -/
theorem OddState.split {h t s w : ℕ} (d : OddState h t s w) :
    ∃ u v : ℕ, 5 ^ h * s = u ^ 5 ∧ F t s = 16 * v ^ 5 := by
  obtain ⟨G, hG⟩ := sixteen_dvd_F_of_odd d.t_odd d.s_odd
  have hFG : F t s = 16 * G := by
    simpa [mul_comm] using hG
  have hwhole : (5 ^ h * s) * G = w ^ 5 := by
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 16)
    calc
      16 * ((5 ^ h * s) * G) = (5 ^ h * s) * (16 * G) := by ring
      _ = (5 ^ h * s) * F t s := by rw [← hFG]
      _ = 16 * w ^ 5 := d.equation
  have hcopF : (5 ^ h * s).Coprime (F t s) :=
    odd_factor_coprime d.coprime d.t_not_five
  have hcopG : (5 ^ h * s).Coprime G :=
    Nat.Coprime.of_dvd_right ⟨16, by simpa [mul_comm] using hFG⟩ hcopF
  obtain ⟨u, hu⟩ := exists_nat_pow_of_coprime_mul hcopG hwhole
  obtain ⟨v, hv⟩ := exists_nat_pow_of_coprime_mul hcopG.symm (by
    simpa [mul_comm] using hwhole)
  exact ⟨u, v, hu, hFG.trans (by rw [hv])⟩

/-- Unique factorization in the opposite-parity normalization. -/
theorem EvenState.split {g h t s w : ℕ} (d : EvenState g h t s w) :
    ∃ u v : ℕ, 2 ^ g * 5 ^ h * s = u ^ 5 ∧ F t s = v ^ 5 := by
  have hcop : (2 ^ g * 5 ^ h * s).Coprime (F t s) :=
    even_factor_coprime d.coprime d.t_odd d.s_even d.t_not_five
  obtain ⟨u, hu⟩ := exists_nat_pow_of_coprime_mul hcop d.equation
  obtain ⟨v, hv⟩ := exists_nat_pow_of_coprime_mul hcop.symm (by
    simpa [mul_comm] using d.equation)
  exact ⟨u, v, hu, hv⟩

theorem norm_identity (t s : ℕ) :
    (t ^ 2 + 5 * s ^ 2) ^ 2 = 5 * (2 * s ^ 2) ^ 2 + F t s := by
  simp only [F]
  ring

private theorem half_norm_odd {t s P : ℕ} (ht : Odd t) (hs : Odd s)
    (hP : t ^ 2 + 5 * s ^ 2 = P + P) : Odd P := by
  obtain ⟨a, rfl⟩ := ht
  obtain ⟨b, rfl⟩ := hs
  let k := a ^ 2 + a + 5 * b ^ 2 + 5 * b + 1
  refine ⟨k, ?_⟩
  dsimp only [k]
  nlinarith

private theorem norm_coprime_square {t s : ℕ} (hts : t.Coprime s) :
    (t ^ 2 + 5 * s ^ 2).Coprime (s ^ 2) := by
  have hpows : (t ^ 2).Coprime (s ^ 2) := hts.pow 2 2
  simpa [mul_comm] using (Nat.coprime_add_mul_left_left (t ^ 2) (s ^ 2) 5).mpr hpows

private theorem half_norm_coprime {t s P : ℕ} (hts : t.Coprime s)
    (hP : t ^ 2 + 5 * s ^ 2 = P + P) : P.Coprime (s ^ 2) := by
  apply Nat.Coprime.of_dvd_left (b := s ^ 2) (a₂ := t ^ 2 + 5 * s ^ 2)
  · exact ⟨2, by rw [hP]; ring⟩
  · exact norm_coprime_square hts

private theorem not_five_dvd_norm {t s : ℕ} (ht : ¬5 ∣ t) :
    ¬5 ∣ t ^ 2 + 5 * s ^ 2 := by
  intro hnorm
  have ht2 : 5 ∣ t ^ 2 :=
    (Nat.dvd_add_iff_left (Nat.dvd_mul_right 5 (s ^ 2))).mpr hnorm
  exact ht (Nat.prime_five.dvd_of_dvd_pow ht2)

private theorem not_five_dvd_half_norm {t s P : ℕ} (ht : ¬5 ∣ t)
    (hP : t ^ 2 + 5 * s ^ 2 = P + P) : ¬5 ∣ P := by
  intro hfive
  apply not_five_dvd_norm ht
  rw [hP]
  exact dvd_add hfive hfive

/-- The primitive positive representation to which the odd extraction is
applied after `F(t,s)=16v^5` has been split off. -/
theorem OddState.normData {h t s w v : ℕ} (d : OddState h t s w)
    (hF : F t s = 16 * v ^ 5) :
    ∃ P : ℕ,
      0 < P ∧ P.Coprime (s ^ 2) ∧ Odd P ∧ Odd (s ^ 2) ∧
        5 ∣ s ^ 2 ∧ ¬5 ∣ P ∧ P ^ 2 = 5 * (s ^ 2) ^ 2 + 4 * v ^ 5 := by
  have heven : Even (t ^ 2 + 5 * s ^ 2) :=
    (d.t_odd.pow.add_odd ((show Odd 5 by norm_num).mul d.s_odd.pow))
  obtain ⟨P, hP⟩ := heven
  refine ⟨P, ?_, half_norm_coprime d.coprime hP, half_norm_odd d.t_odd d.s_odd hP,
    d.s_odd.pow, dvd_pow d.s_five (by norm_num),
    not_five_dvd_half_norm d.t_not_five hP, ?_⟩
  · have ht2 : 0 < t ^ 2 := pow_pos d.t_pos 2
    have hsumPos : 0 < t ^ 2 + 5 * s ^ 2 := by omega
    omega
  · apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 4)
    calc
      4 * P ^ 2 = (P + P) ^ 2 := by ring
      _ = (t ^ 2 + 5 * s ^ 2) ^ 2 := by rw [hP]
      _ = 5 * (2 * s ^ 2) ^ 2 + F t s := norm_identity t s
      _ = 4 * (5 * (s ^ 2) ^ 2 + 4 * v ^ 5) := by rw [hF]; ring

/-- The primitive positive representation used by the opposite-parity
extraction after `F(t,s)=v^5`. -/
theorem EvenState.normData {g h t s w v : ℕ} (d : EvenState g h t s w)
    (hF : F t s = v ^ 5) :
    let P := t ^ 2 + 5 * s ^ 2
    let Q := 2 * s ^ 2
    0 < P ∧ 0 < Q ∧ P.Coprime Q ∧ Odd P ∧ Even Q ∧ 5 ∣ Q ∧ ¬5 ∣ P ∧
      P ^ 2 = 5 * Q ^ 2 + v ^ 5 := by
  dsimp only
  have hPodd : Odd (t ^ 2 + 5 * s ^ 2) := by
    obtain ⟨a, ha⟩ := d.t_odd
    obtain ⟨b, hb⟩ := d.s_even
    refine ⟨2 * a ^ 2 + 2 * a + 5 * (b ^ 2 + b * b), ?_⟩
    rw [ha, hb]
    ring
  have hQeven : Even (2 * s ^ 2) := ⟨s ^ 2, by ring⟩
  have hPcopSquare := norm_coprime_square d.coprime
  have hPcopTwo : (t ^ 2 + 5 * s ^ 2).Coprime 2 := hPodd.coprime_two_right
  have hcop : (t ^ 2 + 5 * s ^ 2).Coprime (2 * s ^ 2) :=
    hPcopTwo.mul_right hPcopSquare
  have ht2 : 0 < t ^ 2 := pow_pos d.t_pos 2
  have hs2 : 0 < s ^ 2 := pow_pos d.s_pos 2
  refine ⟨by omega, by omega, hcop, hPodd, hQeven, ?_,
    not_five_dvd_norm d.t_not_five, ?_⟩
  · exact dvd_mul_of_dvd_right (dvd_pow d.s_five (by norm_num)) 2
  · rw [norm_identity, hF]

/-- Coordinate output of the odd fifth-power extraction. -/
structure OddCoordinates (s t' s' : ℕ) : Prop where
  relation : 16 * s ^ 2 = 5 * s' * F t' s'
  t_pos : 0 < t'
  s_pos : 0 < s'
  coprime : t'.Coprime s'
  t_odd : Odd t'
  s_odd : Odd s'
  t_not_five : ¬5 ∣ t'

/-- Coordinate output of the opposite-parity fifth-power extraction, after
the parity orientation forced by its coefficient equation. -/
structure EvenCoordinates (s t' s' : ℕ) : Prop where
  relation : 2 * s ^ 2 = 5 * s' * F t' s'
  t_pos : 0 < t'
  s_pos : 0 < s'
  coprime : t'.Coprime s'
  t_odd : Odd t'
  s_even : Even s'
  t_not_five : ¬5 ∣ t'

/-- The coefficient relation orients the opposite parity returned by the
quadratic extraction: the first coordinate is odd and the second is even. -/
theorem EvenCoordinates.ofOppositeParity {s t' s' : ℕ}
    (hrel : 2 * s ^ 2 = 5 * s' * F t' s') (htpos : 0 < t') (hspos : 0 < s')
    (hcop : t'.Coprime s')
    (hparity : (Odd t' ∧ Even s') ∨ (Even t' ∧ Odd s'))
    (htfive : ¬5 ∣ t') : EvenCoordinates s t' s' := by
  rcases hparity with hgood | hbad
  · exact ⟨hrel, htpos, hspos, hcop, hgood.1, hgood.2, htfive⟩
  · exfalso
    have hright : Odd (5 * s' * F t' s') :=
      ((show Odd 5 by norm_num).mul hbad.2).mul (odd_F_of_even_odd hbad.1 hbad.2)
    have hleftOdd : Odd (2 * s ^ 2) := by rwa [hrel]
    have hleftEven : Even (2 * s ^ 2) := ⟨s ^ 2, by ring⟩
    exact (Nat.not_even_iff_odd.mpr hleftOdd) hleftEven

/-- The algebraic extraction, converted to the exact natural-number
coordinate relation used by the odd descent. -/
theorem OddState.extractCoordinates {h t s w v : ℕ} (d : OddState h t s w)
    (hF : F t s = 16 * v ^ 5) : ∃ t' s' : ℕ, OddCoordinates s t' s' := by
  obtain ⟨P, hPpos, hcop, hPodd, hQodd, hQfive, hPfive, hnorm⟩ := d.normData hF
  obtain ⟨t', s', htpos, hspos, hcop', htodd, hsodd, htfive, hrel⟩ :=
    exists_odd_coordinates_nat P (s ^ 2) v hPpos (pow_pos d.s_pos 2) hcop
      hPodd hQodd hQfive hPfive hnorm
  refine ⟨t', s', hrel, htpos, hspos, hcop', htodd, hsodd, htfive⟩

/-- The algebraic extraction, converted to the exact natural-number
coordinate relation used by the opposite-parity descent. -/
theorem EvenState.extractCoordinates {g h t s w v : ℕ} (d : EvenState g h t s w)
    (hF : F t s = v ^ 5) : ∃ t' s' : ℕ, EvenCoordinates s t' s' := by
  rcases d.normData hF with ⟨hPpos, hQpos, hcop, hPodd, hQeven, hQfive,
    hPfive, hnorm⟩
  obtain ⟨t', s', htpos, hspos, hcop', htodd, hseven, htfive, hrel⟩ :=
    exists_oppositeParity_coordinates_nat (t ^ 2 + 5 * s ^ 2) (2 * s ^ 2) v
      hPpos hQpos hcop hPodd hQeven hQfive hPfive hnorm
  refine ⟨t', s', hrel, htpos, hspos, hcop', htodd, hseven, htfive⟩

private theorem five_dvd_new_second {K s t' s' : ℕ} (hs : 5 ∣ s)
    (ht : ¬5 ∣ t') (hrel : K * s ^ 2 = 5 * s' * F t' s') : 5 ∣ s' := by
  have h25s : 25 ∣ s ^ 2 := by
    simpa [pow_two] using Nat.mul_dvd_mul hs hs
  have h25lhs : 25 ∣ K * s ^ 2 := dvd_mul_of_dvd_right h25s K
  rw [hrel] at h25lhs
  have hcancel : 5 * 5 ∣ 5 * (s' * F t' s') := by
    simpa [mul_assoc] using h25lhs
  have hprod : 5 ∣ s' * F t' s' :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num) hcancel
  rcases Nat.prime_five.dvd_mul.mp hprod with hs' | hF
  · exact hs'
  · exact (not_five_dvd_F ht hF).elim

private theorem smaller_of_coordinate_relation {K s t' s' : ℕ}
    (hK : K < 25) (hs' : 0 < s') (ht' : 0 < t')
    (hrel : K * s ^ 2 = 5 * s' * F t' s') : s' < s := by
  have ht4 : 0 < t' ^ 4 := pow_pos ht' 4
  have hF : 5 * s' ^ 4 < F t' s' := by
    simp only [F]
    omega
  have hmul := (Nat.mul_lt_mul_left (show 0 < 5 * s' by positivity)).mpr hF
  have hmain : 25 * s' ^ 5 < K * s ^ 2 := by
    rw [hrel]
    convert hmul using 1
    all_goals ring
  by_contra hnlt
  have hss : s ≤ s' := Nat.le_of_not_gt hnlt
  have hsquares : s ^ 2 ≤ s' ^ 2 := Nat.pow_le_pow_left hss 2
  have hpowers : s' ^ 2 ≤ s' ^ 5 := Nat.pow_le_pow_right hs' (by omega)
  have hKle : K * s ^ 2 ≤ K * s' ^ 5 :=
    Nat.mul_le_mul_left K (hsquares.trans hpowers)
  have hKlt : K * s' ^ 5 < 25 * s' ^ 5 :=
    (Nat.mul_lt_mul_right (pow_pos hs' 5)).mpr hK
  omega

theorem OddCoordinates.five_dvd {s t' s' : ℕ} (c : OddCoordinates s t' s')
    (hs : 5 ∣ s) : 5 ∣ s' :=
  five_dvd_new_second hs c.t_not_five c.relation

theorem OddCoordinates.smaller {s t' s' : ℕ} (c : OddCoordinates s t' s') :
    s' < s :=
  smaller_of_coordinate_relation (by norm_num) c.s_pos c.t_pos c.relation

theorem EvenCoordinates.five_dvd {s t' s' : ℕ} (c : EvenCoordinates s t' s')
    (hs : 5 ∣ s) : 5 ∣ s' :=
  five_dvd_new_second hs c.t_not_five c.relation

theorem EvenCoordinates.smaller {s t' s' : ℕ} (c : EvenCoordinates s t' s') :
    s' < s :=
  smaller_of_coordinate_relation (by norm_num) c.s_pos c.t_pos c.relation

private theorem five_pow_double (h : ℕ) : 5 ^ (2 * h) = (5 ^ h) ^ 2 := by
  calc
    5 ^ (2 * h) = 5 ^ (h * 2) := by
      congr 1
      omega
    _ = (5 ^ h) ^ 2 := pow_mul 5 h 2

private theorem two_pow_double (g : ℕ) : 2 ^ (2 * g) = (2 ^ g) ^ 2 := by
  calc
    2 ^ (2 * g) = 2 ^ (g * 2) := by
      congr 1
      omega
    _ = (2 ^ g) ^ 2 := pow_mul 2 g 2

/-- The exact odd recurrence `h ↦ 2h+1`. -/
theorem OddState.nextOfCoordinates {h t s w u t' s' : ℕ}
    (d : OddState h t s w) (hu : 5 ^ h * s = u ^ 5)
    (c : OddCoordinates s t' s') : OddState (2 * h + 1) t' s' (u ^ 2) := by
  have huPos : 0 < u := by
    have hleft : 0 < 5 ^ h * s := mul_pos (pow_pos (by norm_num) h) d.s_pos
    have : 0 < u ^ 5 := by rwa [← hu]
    exact Nat.pos_of_ne_zero fun hu0 ↦ by simp [hu0] at this
  refine
    { equation := ?_
      t_pos := c.t_pos
      s_pos := c.s_pos
      w_pos := pow_pos huPos 2
      coprime := c.coprime
      t_odd := c.t_odd
      s_odd := c.s_odd
      s_five := c.five_dvd d.s_five
      t_not_five := c.t_not_five }
  calc
    5 ^ (2 * h + 1) * s' * F t' s' =
        5 ^ (2 * h) * (5 * s' * F t' s') := by rw [pow_succ]; ring
    _ = 5 ^ (2 * h) * (16 * s ^ 2) := by rw [← c.relation]
    _ = 16 * (5 ^ h * s) ^ 2 := by rw [five_pow_double]; ring
    _ = 16 * (u ^ 2) ^ 5 := by rw [hu]; ring

/-- The exact opposite-parity recurrence `(g,h) ↦ (2g-1,2h+1)`. -/
theorem EvenState.nextOfCoordinates {g h t s w u t' s' : ℕ}
    (d : EvenState g h t s w) (hu : 2 ^ g * 5 ^ h * s = u ^ 5)
    (c : EvenCoordinates s t' s') :
    EvenState (2 * g - 1) (2 * h + 1) t' s' (u ^ 2) := by
  have huPos : 0 < u := by
    have hcoeff : 0 < 2 ^ g * 5 ^ h :=
      mul_pos (pow_pos (by norm_num) g) (pow_pos (by norm_num) h)
    have hleft : 0 < 2 ^ g * 5 ^ h * s := mul_pos hcoeff d.s_pos
    have : 0 < u ^ 5 := by rwa [← hu]
    exact Nat.pos_of_ne_zero fun hu0 ↦ by simp [hu0] at this
  have hgPos := d.g_pos
  have hsucc : 2 * g - 1 + 1 = 2 * g := by omega
  have htwo : 2 ^ (2 * g - 1) * 2 = 2 ^ (2 * g) := by
    rw [← pow_succ, hsucc]
  refine
    { equation := ?_
      g_pos := by omega
      t_pos := c.t_pos
      s_pos := c.s_pos
      w_pos := pow_pos huPos 2
      coprime := c.coprime
      t_odd := c.t_odd
      s_even := c.s_even
      s_five := c.five_dvd d.s_five
      t_not_five := c.t_not_five }
  calc
    2 ^ (2 * g - 1) * 5 ^ (2 * h + 1) * s' * F t' s' =
        2 ^ (2 * g - 1) * 5 ^ (2 * h) * (5 * s' * F t' s') := by
          rw [pow_succ]
          ring
    _ = 2 ^ (2 * g - 1) * 5 ^ (2 * h) * (2 * s ^ 2) := by rw [← c.relation]
    _ = 2 ^ (2 * g) * 5 ^ (2 * h) * s ^ 2 := by
      calc
        2 ^ (2 * g - 1) * 5 ^ (2 * h) * (2 * s ^ 2) =
            (2 ^ (2 * g - 1) * 2) * 5 ^ (2 * h) * s ^ 2 := by ring
        _ = 2 ^ (2 * g) * 5 ^ (2 * h) * s ^ 2 := by rw [htwo]
    _ = (2 ^ g * 5 ^ h * s) ^ 2 := by
      rw [two_pow_double, five_pow_double]
      ring
    _ = (u ^ 2) ^ 5 := by rw [hu]; ring

/-- A source-normalized odd state produces one with the historical exponent
`2h+1` and a strictly smaller positive second coordinate. -/
theorem OddState.descends {h t s w : ℕ} (d : OddState h t s w) :
    ∃ h' t' s' w' : ℕ, OddState h' t' s' w' ∧ s' < s := by
  obtain ⟨u, v, hu, hF⟩ := d.split
  obtain ⟨t', s', c⟩ := d.extractCoordinates hF
  exact ⟨2 * h + 1, t', s', u ^ 2, d.nextOfCoordinates hu c, c.smaller⟩

/-- A source-normalized opposite-parity state produces one with exponents
`(2g-1,2h+1)` and a strictly smaller positive second coordinate. -/
theorem EvenState.descends {g h t s w : ℕ} (d : EvenState g h t s w) :
    ∃ g' h' t' s' w' : ℕ, EvenState g' h' t' s' w' ∧ s' < s := by
  obtain ⟨u, v, hu, hF⟩ := d.split
  obtain ⟨t', s', c⟩ := d.extractCoordinates hF
  exact ⟨2 * g - 1, 2 * h + 1, t', s', u ^ 2,
    d.nextOfCoordinates hu c, c.smaller⟩

/-- Minimal-positive-coordinate engine for the odd normalization. -/
theorem no_oddState_of_descends
    (hdesc : ∀ {h t s w : ℕ}, OddState h t s w →
      ∃ h' t' s' w' : ℕ, OddState h' t' s' w' ∧ s' < s) :
    ∀ h t s w : ℕ, ¬OddState h t s w := by
  classical
  intro h t s w d
  let P : ℕ → Prop := fun k ↦ ∃ h t w : ℕ, OddState h t k w
  have hP : ∃ k, P k := ⟨s, h, t, w, d⟩
  obtain ⟨h₀, t₀, w₀, d₀⟩ := Nat.find_spec hP
  obtain ⟨h₁, t₁, s₁, w₁, d₁, hlt⟩ := hdesc d₀
  have hminimal : Nat.find hP ≤ s₁ :=
    Nat.find_min' hP ⟨h₁, t₁, w₁, d₁⟩
  exact (Nat.not_lt_of_ge hminimal) hlt

/-- Minimal-positive-coordinate engine for the opposite-parity normalization. -/
theorem no_evenState_of_descends
    (hdesc : ∀ {g h t s w : ℕ}, EvenState g h t s w →
      ∃ g' h' t' s' w' : ℕ, EvenState g' h' t' s' w' ∧ s' < s) :
    ∀ g h t s w : ℕ, ¬EvenState g h t s w := by
  classical
  intro g h t s w d
  let P : ℕ → Prop := fun k ↦ ∃ g h t w : ℕ, EvenState g h t k w
  have hP : ∃ k, P k := ⟨s, g, h, t, w, d⟩
  obtain ⟨g₀, h₀, t₀, w₀, d₀⟩ := Nat.find_spec hP
  obtain ⟨g₁, h₁, t₁, s₁, w₁, d₁, hlt⟩ := hdesc d₀
  have hminimal : Nat.find hP ≤ s₁ :=
    Nat.find_min' hP ⟨g₁, h₁, t₁, w₁, d₁⟩
  exact (Nat.not_lt_of_ge hminimal) hlt

/-- There is no state in Dirichlet's odd-coordinate descent family. -/
theorem no_oddState (h t s w : ℕ) : ¬OddState h t s w :=
  no_oddState_of_descends (fun d ↦ d.descends) h t s w

/-- There is no state in Dirichlet's opposite-parity descent family. -/
theorem no_evenState (g h t s w : ℕ) : ¬EvenState g h t s w :=
  no_evenState_of_descends (fun d ↦ d.descends) g h t s w

end Fermat.Five.Dirichlet
