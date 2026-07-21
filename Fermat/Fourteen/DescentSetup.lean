import Fermat.Fourteen.DescentArithmetic
import Fermat.Fourteen.PowerExtraction
import Fermat.Fourteen.PowerSplitting

/-!
# Preparing one step of Dirichlet's descent

This file turns a solution of Dirichlet's generalized equation into the
primitive quadratic-form representation to which the signed power-extraction
theorem applies.
-/

namespace Fermat.Fourteen.Dirichlet

/-- The positive quadratic-form factor on page 392. -/
def quadraticFactor (chi p : ℤ) : ℤ :=
  p ^ 2 + 7 * (7 ^ 2 * chi ^ 3) ^ 2

/-- The other factor after `φ = 7χ` is extracted. -/
def scaledPhi (chi : ℤ) : ℤ := 7 ^ 2 * chi

private theorem zmod_seven_pow_fourteen_eq_sq :
    ∀ x : ZMod 7, x ^ 14 = x ^ 2 := by
  native_decide

/-- Neither of the two coprime leading entries in the generalized equation
is divisible by `7`. -/
theorem DescentEquation.not_seven_dvd {t u w : ℤ} {m n : ℕ}
    (h : DescentEquation t u w m n) :
    ¬(7 : ℤ) ∣ t ∧ ¬(7 : ℤ) ∣ u := by
  rcases h with ⟨-, htu, heq⟩
  have hrhs : (7 : ℤ) ∣ 2 ^ m * 7 ^ (n + 1) * w ^ 14 := by
    refine dvd_mul_of_dvd_left (dvd_mul_of_dvd_right ?_ _) _
    exact dvd_pow_self 7 (by omega)
  constructor
  · intro ht
    have hu14 : (7 : ℤ) ∣ u ^ 14 := by
      rw [show u ^ 14 = t ^ 14 - (2 ^ m * 7 ^ (n + 1) * w ^ 14) by omega]
      exact dvd_sub (dvd_pow ht (by norm_num)) hrhs
    have hu : (7 : ℤ) ∣ u :=
      (show Prime (7 : ℤ) by norm_num).dvd_of_dvd_pow hu14
    have hunit : IsUnit (7 : ℤ) := htu.isUnit_of_dvd' ht hu
    norm_num [Int.isUnit_iff] at hunit
  · intro hu
    have ht14 : (7 : ℤ) ∣ t ^ 14 := by
      rw [show t ^ 14 = u ^ 14 + (2 ^ m * 7 ^ (n + 1) * w ^ 14) by omega]
      exact dvd_add (dvd_pow hu (by norm_num)) hrhs
    have ht : (7 : ℤ) ∣ t :=
      (show Prime (7 : ℤ) by norm_num).dvd_of_dvd_pow ht14
    have hunit : IsUnit (7 : ℤ) := htu.isUnit_of_dvd' ht hu
    norm_num [Int.isUnit_iff] at hunit

/-- The generalized equation forces `7 ∣ φ`. -/
theorem DescentEquation.seven_dvd_phi {t u w : ℤ} {m n : ℕ}
    (h : DescentEquation t u w m n) : (7 : ℤ) ∣ phi t u := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rcases h with ⟨-, -, heq⟩
  have heq' : (((t ^ 14 - u ^ 14 : ℤ) : ZMod 7)) = 0 := by
    calc
      ((t ^ 14 - u ^ 14 : ℤ) : ZMod 7) =
          ((2 ^ m * 7 ^ (n + 1) * w ^ 14 : ℤ) : ZMod 7) :=
        congrArg (fun z : ℤ ↦ (z : ZMod 7)) heq
      _ = 0 := by
        push_cast
        rw [show (7 : ZMod 7) = 0 from ZMod.natCast_self 7]
        simp [pow_succ]
  push_cast at heq'
  have hz : ((phi t u : ℤ) : ZMod 7) = 0 := by
    rw [phi]
    push_cast
    rw [← zmod_seven_pow_fourteen_eq_sq (t : ZMod 7),
      ← zmod_seven_pow_fourteen_eq_sq (u : ZMod 7)]
    exact heq'
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (phi t u) 7).1 hz

/-- For coprime `t,u`, Dirichlet's `φ` and `ψ` have opposite parity. -/
theorem oppositeParity_phi_psi {t u : ℤ} (htu : IsCoprime t u) :
    OppositeParity (phi t u) (psi t u) := by
  rcases Int.even_or_odd t with ht | ht <;> rcases Int.even_or_odd u with hu | hu
  · have hunit : IsUnit (2 : ℤ) :=
      htu.isUnit_of_dvd' (even_iff_two_dvd.mp ht) (even_iff_two_dvd.mp hu)
    norm_num [Int.isUnit_iff] at hunit
  · right
    have ht' : ¬Odd t := Int.not_odd_iff_even.mpr ht
    have hu' : ¬Even u := Int.not_even_iff_odd.mpr hu
    simp +decide [phi, psi, ht, ht', hu', parity_simps]
  · right
    simp +decide [phi, psi, ht, hu, parity_simps]
  · left
    have ht' : ¬Even t := Int.not_even_iff_odd.mpr ht
    have hu' : ¬Even u := Int.not_even_iff_odd.mpr hu
    simp +decide [phi, psi, ht, hu, ht', hu', parity_simps]

/-- Replacing `φ` by `7χ` preserves its parity relation with `ψ`. -/
theorem oppositeParity_chi_psi {t u chi : ℤ}
    (hphi : phi t u = 7 * chi) (hparity : OppositeParity (phi t u) (psi t u)) :
    OppositeParity chi (psi t u) := by
  rcases hparity with ⟨hphiEven, hpsiOdd⟩ | ⟨hphiOdd, hpsiEven⟩
  · left
    refine ⟨?_, hpsiOdd⟩
    rw [hphi] at hphiEven
    exact (Int.even_mul.mp hphiEven).resolve_left (by norm_num)
  · right
    refine ⟨?_, hpsiEven⟩
    rw [hphi] at hphiOdd
    exact (Int.odd_mul.mp hphiOdd).2

/-- The exact refactorization after writing `φ = 7χ`. -/
theorem factorization_with_chi {t u chi : ℤ} (hphi : phi t u = 7 * chi) :
    t ^ 14 - u ^ 14 = scaledPhi chi * quadraticFactor chi (psi t u) := by
  rw [factorization, hphi]
  simp only [scaledPhi, quadraticFactor]
  ring

theorem psi_ne_zero {t u : ℤ} (ht : t ≠ 0) (hu : u ≠ 0) : psi t u ≠ 0 := by
  have htuSq : 0 < t ^ 2 * u ^ 2 :=
    mul_pos (sq_pos_of_ne_zero ht) (sq_pos_of_ne_zero hu)
  have hpoly : 0 < t ^ 4 - t ^ 2 * u ^ 2 + u ^ 4 := by
    nlinarith [sq_nonneg (t ^ 2 - u ^ 2)]
  exact mul_ne_zero (mul_ne_zero ht hu) hpoly.ne'

theorem DescentEquation.phi_pos {t u w : ℤ} {m n : ℕ}
    (h : DescentEquation t u w m n) : 0 < phi t u := by
  have hlt := h.natAbs_lt
  have hsqNat : u.natAbs ^ 2 < t.natAbs ^ 2 :=
    pow_lt_pow_left₀ hlt (Nat.zero_le _) (by norm_num)
  have hsqInt : (u.natAbs : ℤ) ^ 2 < (t.natAbs : ℤ) ^ 2 := by exact_mod_cast hsqNat
  rw [Int.natCast_natAbs, Int.natCast_natAbs, sq_abs, sq_abs] at hsqInt
  exact sub_pos.mpr hsqInt

theorem quadraticFactor_pos {chi p : ℤ} (hp : p ≠ 0) :
    0 < quadraticFactor chi p := by
  simp only [quadraticFactor]
  have hp2 : 0 < p ^ 2 := sq_pos_of_ne_zero hp
  positivity

theorem odd_quadraticFactor {chi p : ℤ} (hparity : OppositeParity chi p) :
    Odd (quadraticFactor chi p) := by
  rcases hparity with ⟨hchi, hp⟩ | ⟨hchi, hp⟩
  · simp +decide [quadraticFactor, hchi, hp, parity_simps]
  · have hchi' : ¬Even chi := Int.not_even_iff_odd.mpr hchi
    have hp' : ¬Odd p := Int.not_odd_iff_even.mpr hp
    simp +decide [quadraticFactor, hchi', hp', parity_simps]

theorem not_seven_dvd_quadraticFactor {chi p : ℤ} (hp : ¬(7 : ℤ) ∣ p) :
    ¬(7 : ℤ) ∣ quadraticFactor chi p := by
  have h7p : IsCoprime (7 : ℤ) p :=
    (show Prime (7 : ℤ) by norm_num).coprime_iff_not_dvd.mpr hp
  have hbase := h7p.pow_right (n := 2)
  have hcoprime : IsCoprime (7 : ℤ) (quadraticFactor chi p) := by
    convert hbase.add_mul_left_right ((7 : ℤ) ^ 4 * chi ^ 6) using 1
    simp only [quadraticFactor]
    ring
  intro hdiv
  have hunit : IsUnit (7 : ℤ) := hcoprime.isUnit_of_dvd' dvd_rfl hdiv
  norm_num [Int.isUnit_iff] at hunit

/-- The two page-392 factors are coprime. -/
theorem isCoprime_scaledPhi_quadraticFactor {t u chi : ℤ}
    (htu : IsCoprime t u) (hphi : phi t u = 7 * chi) :
    IsCoprime (scaledPhi chi) (quadraticFactor chi (psi t u)) := by
  have hphiPsi := isCoprime_phi_psi t u htu
  rw [hphi] at hphiPsi
  have h7psi : IsCoprime (7 : ℤ) (psi t u) := hphiPsi.of_mul_left_left
  have hchiPsi : IsCoprime chi (psi t u) := hphiPsi.of_mul_left_right
  have h7quad : IsCoprime (7 : ℤ) (quadraticFactor chi (psi t u)) := by
    have hbase := h7psi.pow_right (n := 2)
    convert hbase.add_mul_left_right ((7 : ℤ) ^ 4 * chi ^ 6) using 1
    simp only [quadraticFactor]
    ring
  have hchiQuad : IsCoprime chi (quadraticFactor chi (psi t u)) := by
    have hbase := hchiPsi.pow_right (n := 2)
    convert hbase.add_mul_left_right ((7 : ℤ) ^ 5 * chi ^ 5) using 1
    simp only [quadraticFactor]
    ring
  simpa only [scaledPhi] using (h7quad.pow_left (m := 2)).mul_left hchiQuad

/-- The distinguished factor `2^m 7^(n+1)` is coprime to the quadratic
factor, so it must be allocated wholly to `7²χ`. -/
theorem isCoprime_coefficient_quadraticFactor {chi p : ℤ} {m n : ℕ}
    (hodd : Odd (quadraticFactor chi p))
    (hseven : ¬(7 : ℤ) ∣ quadraticFactor chi p) :
    IsCoprime ((2 : ℤ) ^ m * 7 ^ (n + 1)) (quadraticFactor chi p) := by
  have htwo : IsCoprime (2 : ℤ) (quadraticFactor chi p) :=
    Int.isCoprime_two_left.mpr hodd
  have hseven' : IsCoprime (7 : ℤ) (quadraticFactor chi p) :=
    (show Prime (7 : ℤ) by norm_num).coprime_iff_not_dvd.mpr hseven
  exact (htwo.pow_left (m := m)).mul_left (hseven'.pow_left (m := n + 1))

/-- Data obtained before applying the quadratic-order representation theorem. -/
structure Prepared (t u w : ℤ) (m n : ℕ) (chi a b : ℤ) : Prop where
  phi_eq : phi t u = 7 * chi
  chi_pos : 0 < chi
  psi_not_seven : ¬(7 : ℤ) ∣ psi t u
  chi_psi_coprime : IsCoprime chi (psi t u)
  chi_psi_parity : OppositeParity chi (psi t u)
  quadratic_eq : quadraticFactor chi (psi t u) = a ^ 14
  a_pos : 0 < a
  scaled_eq : scaledPhi chi = (2 : ℤ) ^ m * 7 ^ (n + 1) * b ^ 14

/-- All elementary factor allocation preceding the quadratic-order power
extraction. -/
theorem DescentEquation.prepare {t u w : ℤ} {m n : ℕ}
    (h : DescentEquation t u w m n) :
    ∃ chi a b : ℤ, Prepared t u w m n chi a b := by
  obtain ⟨chi, hphi⟩ := h.seven_dvd_phi
  rcases h with ⟨hnonzero, htu, heq⟩
  have ht : t ≠ 0 := by
    intro ht
    subst t
    simp at hnonzero
  have hu : u ≠ 0 := by
    intro hu
    subst u
    simp at hnonzero
  have hp0 : psi t u ≠ 0 := psi_ne_zero ht hu
  have hnotSeven := DescentEquation.not_seven_dvd
    (⟨hnonzero, htu, heq⟩ : DescentEquation t u w m n)
  have hpSeven : ¬(7 : ℤ) ∣ psi t u :=
    not_seven_dvd_psi t u hnotSeven.1 hnotSeven.2
  have hphiPsi := isCoprime_phi_psi t u htu
  rw [hphi] at hphiPsi
  have hchiPsi : IsCoprime chi (psi t u) := hphiPsi.of_mul_left_right
  have hparity : OppositeParity chi (psi t u) :=
    oppositeParity_chi_psi hphi (oppositeParity_phi_psi htu)
  have hchiPos : 0 < chi := by
    have hphiPos := DescentEquation.phi_pos
      (⟨hnonzero, htu, heq⟩ : DescentEquation t u w m n)
    rw [hphi] at hphiPos
    nlinarith
  let C := quadraticFactor chi (psi t u)
  let K : ℤ := 2 ^ m * 7 ^ (n + 1)
  have hCpos : 0 < C := quadraticFactor_pos hp0
  have hCodd : Odd C := odd_quadraticFactor hparity
  have hCseven : ¬(7 : ℤ) ∣ C := not_seven_dvd_quadraticFactor hpSeven
  have hAC : IsCoprime (scaledPhi chi) C :=
    isCoprime_scaledPhi_quadraticFactor htu hphi
  have hKC : IsCoprime K C :=
    isCoprime_coefficient_quadraticFactor hCodd hCseven
  have hproduct : scaledPhi chi * C = K * w ^ 14 := by
    dsimp only [C, K]
    rw [← heq]
    exact (factorization_with_chi hphi).symm
  have hKdvd : K ∣ scaledPhi chi := by
    apply hKC.dvd_of_dvd_mul_right
    rw [hproduct]
    exact dvd_mul_right K (w ^ 14)
  obtain ⟨q, hscaledQ⟩ := hKdvd
  have hKpos : 0 < K := by dsimp only [K]; positivity
  have hscaledPos : 0 < scaledPhi chi := by
    simp only [scaledPhi]
    positivity
  have hqpos : 0 < q := by
    have hKqpos : 0 < K * q := by rwa [← hscaledQ]
    by_contra hq
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hKpos.le (le_of_not_gt hq))) hKqpos
  have hqC : IsCoprime q C := by
    rw [hscaledQ] at hAC
    exact hAC.of_mul_left_right
  have hqeq : q * C = w ^ 14 := by
    apply mul_left_cancel₀ hKpos.ne'
    calc
      K * (q * C) = scaledPhi chi * C := by rw [hscaledQ]; ring
      _ = K * w ^ 14 := hproduct
  obtain ⟨b, hb⟩ := exists_pow_eq_abs_of_mul_eq_pow_left
    hqC (by decide : Even 14) hqeq
  obtain ⟨a, ha⟩ := exists_pow_eq_abs_of_mul_eq_pow_right
    hqC (by decide : Even 14) hqeq
  have hqpow : q = b ^ 14 := by simpa [abs_of_pos hqpos] using hb
  have hCpow : C = a ^ 14 := by simpa [abs_of_pos hCpos] using ha
  have ha0 : a ≠ 0 := by
    intro ha0
    subst a
    simp at hCpow
    omega
  refine ⟨chi, |a|, b,
    {
      phi_eq := hphi
      chi_pos := hchiPos
      psi_not_seven := hpSeven
      chi_psi_coprime := hchiPsi
      chi_psi_parity := hparity
      quadratic_eq := ?_
      a_pos := abs_pos.mpr ha0
      scaled_eq := ?_ }⟩
  · dsimp only [C] at hCpow
    rw [hCpow, (show Even 14 by decide).pow_abs]
  · rw [hscaledQ, hqpow]

end Fermat.Fourteen.Dirichlet
