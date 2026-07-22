import Fermat.Five.Coordinates
import Fermat.Five.Descent

/-!
# Entry data for Dirichlet's exponent-five descents

This file carries the two historical core equations into the quadratic
representations used for fifth-power extraction.  In the odd branch the
algebraic integer is half-integral and its norm is `b^5`; in the even branch
it lies in `ℤ[√5]` directly.
-/

namespace Fermat.Five.Dirichlet

private theorem initial_norm_coprime_square {q r : ℕ} (hqr : q.Coprime r) :
    (q ^ 2 + 25 * r ^ 2).Coprime (r ^ 2) := by
  have hpows : (q ^ 2).Coprime (r ^ 2) := hqr.pow 2 2
  simpa [mul_comm] using
    (Nat.coprime_add_mul_left_left (q ^ 2) (r ^ 2) 25).mpr hpows

private theorem initial_half_norm_coprime_square {q r P : ℕ}
    (hqr : q.Coprime r) (hP : q ^ 2 + 25 * r ^ 2 = P + P) :
    P.Coprime (r ^ 2) := by
  apply Nat.Coprime.of_dvd_left (b := r ^ 2) (a₂ := q ^ 2 + 25 * r ^ 2)
  · exact ⟨2, by rw [hP]; ring⟩
  · exact initial_norm_coprime_square hqr

private theorem initial_not_five_dvd_norm {q r : ℕ} (hq : ¬5 ∣ q) :
    ¬5 ∣ q ^ 2 + 25 * r ^ 2 := by
  intro hnorm
  have hterm : 5 ∣ 25 * r ^ 2 := by
    exact dvd_mul_of_dvd_left (by norm_num) _
  have hq2 : 5 ∣ q ^ 2 := (Nat.dvd_add_iff_left hterm).mpr hnorm
  exact hq (Nat.prime_five.dvd_of_dvd_pow hq2)

private theorem initial_not_five_dvd_half_norm {q r P : ℕ} (hq : ¬5 ∣ q)
    (hP : q ^ 2 + 25 * r ^ 2 = P + P) : ¬5 ∣ P := by
  intro hfive
  apply initial_not_five_dvd_norm hq
  rw [hP]
  exact dvd_add hfive hfive

private theorem initial_half_norm_odd {q r P : ℕ} (hq : Odd q) (hr : Odd r)
    (hP : q ^ 2 + 25 * r ^ 2 = P + P) : Odd P := by
  obtain ⟨a, rfl⟩ := hq
  obtain ⟨b, rfl⟩ := hr
  let k := a ^ 2 + a + 25 * b ^ 2 + 25 * b + 6
  refine ⟨k, ?_⟩
  dsimp only [k]
  nlinarith

/-- The exact positive primitive norm representation obtained from an odd
core.  Its second coordinate is `5r²`, so coefficient comparison after the
half-integral extraction produces `16r² = sF(t,s)`.
-/
theorem OddCore.initialNormData {q r z : ℕ} (d : OddCore q r z) :
    ∃ a b P : ℕ,
      0 < a ∧ 0 < b ∧ 25 * r = a ^ 5 ∧
      0 < P ∧ P.Coprime (5 * r ^ 2) ∧ Odd P ∧ Odd (5 * r ^ 2) ∧
      5 ∣ 5 * r ^ 2 ∧ ¬5 ∣ P ∧
      P ^ 2 = 5 * (5 * r ^ 2) ^ 2 + 4 * b ^ 5 := by
  obtain ⟨a, b, haPos, hbPos, ha, hb⟩ :=
    split_odd_core d.q_pos d.r_pos d.coprime d.q_odd d.r_odd d.q_not_five d.equation
  have hsumEven : Even (q ^ 2 + 25 * r ^ 2) :=
    d.q_odd.pow.add_odd ((show Odd 25 by norm_num).mul d.r_odd.pow)
  obtain ⟨P, hP⟩ := hsumEven
  have hPPos : 0 < P := by
    have hq2 : 0 < q ^ 2 := pow_pos d.q_pos 2
    have hsumPos : 0 < q ^ 2 + 25 * r ^ 2 := by omega
    omega
  have hPfive : ¬5 ∣ P :=
    initial_not_five_dvd_half_norm d.q_not_five hP
  have hPcopFive : P.Coprime 5 :=
    (Nat.prime_five.coprime_iff_not_dvd.mpr hPfive).symm
  have hPcopSquare : P.Coprime (r ^ 2) :=
    initial_half_norm_coprime_square d.coprime hP
  refine ⟨a, b, P, haPos, hbPos, ha, hPPos,
    hPcopFive.mul_right hPcopSquare, initial_half_norm_odd d.q_odd d.r_odd hP,
    (show Odd 5 by norm_num).mul d.r_odd.pow, dvd_mul_right 5 (r ^ 2), hPfive, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 4)
  calc
    4 * P ^ 2 = (P + P) ^ 2 := by ring
    _ = (q ^ 2 + 25 * r ^ 2) ^ 2 := by rw [hP]
    _ = 5 * (2 * (5 * r ^ 2)) ^ 2 + H q r := by
      simp only [H]
      ring
    _ = 4 * (5 * (5 * r ^ 2) ^ 2 + 4 * b ^ 5) := by rw [hb]; ring

/-- The exact positive primitive norm representation obtained from an even
core.  Its second coordinate is `10r²`, so direct coefficient comparison
produces `2r² = sF(t,s)`.
-/
theorem EvenCore.initialNormData {q r z : ℕ} (d : EvenCore q r z) :
    ∃ a b : ℕ,
      0 < a ∧ 0 < b ∧ 2 * 25 * r = a ^ 5 ∧
      let P := q ^ 2 + 25 * r ^ 2
      let Q := 10 * r ^ 2
      0 < P ∧ 0 < Q ∧ P.Coprime Q ∧ Odd P ∧ Even Q ∧
        5 ∣ Q ∧ ¬5 ∣ P ∧ P ^ 2 = 5 * Q ^ 2 + b ^ 5 := by
  obtain ⟨a, b, haPos, hbPos, ha, hb⟩ :=
    split_even_core d.q_pos d.r_pos d.coprime d.q_odd d.r_even d.q_not_five d.equation
  refine ⟨a, b, haPos, hbPos, ha, ?_⟩
  dsimp only
  have hrSquareEven : Even (r ^ 2) := by
    obtain ⟨k, hk⟩ := d.r_even
    refine ⟨2 * k ^ 2, ?_⟩
    rw [hk]
    ring
  have hPodd : Odd (q ^ 2 + 25 * r ^ 2) :=
    d.q_odd.pow.add_even (hrSquareEven.mul_left 25)
  have hQeven : Even (10 * r ^ 2) := ⟨5 * r ^ 2, by ring⟩
  have hPfive : ¬5 ∣ q ^ 2 + 25 * r ^ 2 :=
    initial_not_five_dvd_norm d.q_not_five
  have hPcopTwo : (q ^ 2 + 25 * r ^ 2).Coprime 2 := hPodd.coprime_two_right
  have hPcopFive : (q ^ 2 + 25 * r ^ 2).Coprime 5 :=
    (Nat.prime_five.coprime_iff_not_dvd.mpr hPfive).symm
  have hPcopSquare := initial_norm_coprime_square d.coprime
  have hcop : (q ^ 2 + 25 * r ^ 2).Coprime (10 * r ^ 2) := by
    simpa only [show 10 * r ^ 2 = 2 * 5 * r ^ 2 by ring, mul_assoc] using
      (hPcopTwo.mul_right hPcopFive).mul_right hPcopSquare
  refine ⟨by have := d.q_pos; positivity, by have := d.r_pos; positivity,
    hcop, hPodd, hQeven,
    ⟨2 * r ^ 2, by ring⟩, hPfive, ?_⟩
  calc
    (q ^ 2 + 25 * r ^ 2) ^ 2 = 5 * (10 * r ^ 2) ^ 2 + H q r := by
      simp only [H]
      ring
    _ = 5 * (10 * r ^ 2) ^ 2 + b ^ 5 := by rw [hb]

end Fermat.Five.Dirichlet
