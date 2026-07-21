import Fermat.Basic

/-!
# Dirichlet's 1832 proof for exponent 14

This file follows Dirichlet's direct proof for `n = 14`. In particular, it
does not obtain the result by applying the `n = 7` case to squares.

Dirichlet replaces the case in which the third term is divisible by `7` by
the generalized equation

`t ^ 14 - u ^ 14 = 2 ^ m * 7 ^ (n + 1) * w ^ 14`

and constructs a solution with smaller coprime `t` and `u`. The definitions
and lemmas below isolate the factorization and the infinite-descent engine.
-/

namespace Fermat.Fourteen.Dirichlet

/-- Dirichlet's `φ = t² - u²`. -/
def phi (t u : ℤ) : ℤ := t ^ 2 - u ^ 2

/-- Dirichlet's `ψ = tu(t⁴ - t²u² + u⁴)`. -/
def psi (t u : ℤ) : ℤ := t * u * (t ^ 4 - t ^ 2 * u ^ 2 + u ^ 4)

/-- Equation (5) in Dirichlet's paper, including the required coprimality. -/
def DescentEquation (t u w : ℤ) (m n : ℕ) : Prop :=
  t * u * w ≠ 0 ∧ IsCoprime t u ∧
    t ^ 14 - u ^ 14 = 2 ^ m * 7 ^ (n + 1) * w ^ 14

/-- The larger base decreased in Dirichlet's infinite descent. Solutions are
normalized so that this is the absolute value of `t`. -/
def height (t : ℤ) : ℕ := t.natAbs

/-- The precise descent obligation extracted from pages 392--393. -/
def Descends : Prop :=
  ∀ ⦃t u w : ℤ⦄ ⦃m n : ℕ⦄, DescentEquation t u w m n →
    ∃ t' u' w' : ℤ, ∃ m' n' : ℕ,
      DescentEquation t' u' w' m' n' ∧ height t' < height t

theorem DescentEquation.natAbs_lt {t u w : ℤ} {m n : ℕ}
    (h : DescentEquation t u w m n) : u.natAbs < t.natAbs := by
  rcases h with ⟨hnonzero, -, heq⟩
  have hw : w ≠ 0 := by
    intro hw
    simp [hw] at hnonzero
  have hrhs : 0 < (2 : ℤ) ^ m * 7 ^ (n + 1) * w ^ 14 := by positivity
  have hpows : u ^ 14 < t ^ 14 := by omega
  have hpowsAbs : u.natAbs ^ 14 < t.natAbs ^ 14 := by
    simpa only [Int.natAbs_pow] using
      Int.natAbs_lt_natAbs_of_nonneg_of_lt (by positivity : 0 ≤ u ^ 14) hpows
  exact (pow_lt_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by norm_num)).mp hpowsAbs

/-- Once the first case has forced `7 ∣ v`, an `n = 14` counterexample enters
Dirichlet's generalized family at parameters `m = 0`, `n = 13`. -/
theorem descentEquation_zero_thirteen {t u v : ℤ}
    (hnonzero : t * u * v ≠ 0) (htu : IsCoprime t u)
    (heq : t ^ 14 = u ^ 14 + v ^ 14) (hv : (7 : ℤ) ∣ v) :
    ∃ w : ℤ, DescentEquation t u w 0 13 := by
  obtain ⟨w, rfl⟩ := hv
  refine ⟨w, ?_, htu, ?_⟩
  · intro hw
    apply hnonzero
    calc
      t * u * (7 * w) = 7 * (t * u * w) := by ring
      _ = 0 := by rw [hw]; simp
  · norm_num [mul_pow] at heq ⊢
    omega

/-- Equation (3) in Dirichlet's paper. -/
theorem factorization (t u : ℤ) :
    t ^ 14 - u ^ 14 = phi t u * ((phi t u ^ 3) ^ 2 + 7 * psi t u ^ 2) := by
  simp only [phi, psi]
  ring

/-- Dirichlet's first coprimality observation. -/
theorem isCoprime_phi_mul (t u : ℤ) (htu : IsCoprime t u) :
    IsCoprime (phi t u) (t * u) := by
  have hphi_t : IsCoprime (phi t u) t := by
    have h := htu.symm.pow_left (m := 2) |>.neg_left |>.add_mul_right_left t
    rw [phi]
    convert h using 1
    ring
  have hphi_u : IsCoprime (phi t u) u := by
    have h := htu.pow_left (m := 2) |>.add_mul_left_left (-u)
    rw [phi]
    convert h using 1
    ring
  exact hphi_t.mul_right hphi_u

/-- The factors `φ` and `ψ` introduced on page 390 are coprime. -/
theorem isCoprime_phi_psi (t u : ℤ) (htu : IsCoprime t u) :
    IsCoprime (phi t u) (psi t u) := by
  have hmul := isCoprime_phi_mul t u htu
  have hquad : IsCoprime (phi t u) (t ^ 4 - t ^ 2 * u ^ 2 + u ^ 4) := by
    have h := hmul.pow_right (n := 2) |>.add_mul_left_right (phi t u)
    convert h using 1
    simp only [phi]
    ring
  simpa only [psi, mul_assoc] using hmul.mul_right hquad

/-- The order `ℤ[√-7]` used in Dirichlet's representation step. -/
abbrev Quad := Zsqrtd (-7)

/-- Dirichlet's degree-six polynomial `R` on page 392. -/
def R (r s : ℤ) : ℤ :=
  (r ^ 2 + 7 * s ^ 2) * (r ^ 4 - 2 * 7 ^ 2 * r ^ 2 * s ^ 2 + 7 ^ 2 * s ^ 4)

/-- The imaginary-part identity underlying the second factorization on page
392. This also checks the constants in the historical source. -/
theorem im_pow_fourteen (r s : ℤ) :
    ((⟨r, s⟩ : Quad) ^ 14).im =
      2 * 7 * r * s * (R r s ^ 2 - (7 * 4 ^ 3 * r ^ 3 * s ^ 3) ^ 2) := by
  norm_num [pow_succ, R]
  ring

/-- The coefficient of `√-7` in a fourteenth power is divisible by `7`.
This is the coefficient comparison used on page 391. -/
theorem seven_dvd_im_pow_fourteen (g h : ℤ) :
    7 ∣ ((⟨g, h⟩ : Quad) ^ 14).im := by
  rw [im_pow_fourteen]
  refine ⟨2 * g * h * (R g h ^ 2 - (7 * 4 ^ 3 * g ^ 3 * h ^ 3) ^ 2), ?_⟩
  ring

/-- Power extraction must retain the unit `±1` because the exponent is even. -/
def IsSignedFourteenthPower (z : Quad) : Prop :=
  ∃ q : Quad, z = q ^ 14 ∨ z = -(q ^ 14)

theorem seven_dvd_im_of_signed_fourteenthPower {z : Quad}
    (hz : IsSignedFourteenthPower z) : 7 ∣ z.im := by
  obtain ⟨⟨g, h⟩, hpow | hpow⟩ := hz
  · rw [hpow]
    exact seven_dvd_im_pow_fourteen g h
  · rw [hpow, Zsqrtd.im_neg]
    exact dvd_neg.mpr (seven_dvd_im_pow_fourteen g h)

/-- Dirichlet's three-factor identity after multiplying the imaginary-part
formula by `7⁴`. -/
theorem scaled_im_pow_fourteen (r s : ℤ) :
    7 ^ 4 * ((⟨r, s⟩ : Quad) ^ 14).im =
      (2 * 7 ^ 5 * r * s) * (R r s + 7 * (4 * r * s) ^ 3) *
        (R r s - 7 * (4 * r * s) ^ 3) := by
  rw [im_pow_fourteen]
  ring

/-- Difference of the final two factors; this is the equation used to create
the next descent solution on page 393. -/
theorem final_factors_sub (r s : ℤ) :
    (R r s + 7 * (4 * r * s) ^ 3) - (R r s - 7 * (4 * r * s) ^ 3) =
      14 * (4 * r * s) ^ 3 := by
  ring

/-- The elementary modulo-`7` calculation behind Dirichlet's assertion that
`ψ` is not divisible by `7` when neither `t` nor `u` is. -/
private theorem zmod_seven_aux :
    ∀ a b : ZMod 7, a ≠ 0 → b ≠ 0 → (a ^ 2 - b ^ 2) ^ 2 + a ^ 2 * b ^ 2 ≠ 0 := by
  native_decide

theorem not_seven_dvd_psi (t u : ℤ) (ht : ¬(7 : ℤ) ∣ t) (hu : ¬(7 : ℤ) ∣ u) :
    ¬(7 : ℤ) ∣ psi t u := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have ht' : (t : ZMod 7) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hu' : (u : ZMod 7) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hquad := zmod_seven_aux (t : ZMod 7) (u : ZMod 7) ht' hu'
  intro hpsi
  have hcast : ((psi t u : ℤ) : ZMod 7) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hpsi
  have hne : (t : ZMod 7) * u *
      (t ^ 4 - t ^ 2 * u ^ 2 + u ^ 4) ≠ 0 :=
    mul_ne_zero (mul_ne_zero ht' hu') (by
      convert hquad using 1
      ring)
  exact hne (by
    simpa only [psi, Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_pow] using hcast)

/-- Once Dirichlet's signed power extraction has been performed, the
coefficient comparison rules out his first case `7 ∤ v`. -/
theorem first_case_contradiction (t u : ℤ)
    (ht : ¬(7 : ℤ) ∣ t) (hu : ¬(7 : ℤ) ∣ u)
    (hpow : IsSignedFourteenthPower (⟨phi t u ^ 3, psi t u⟩ : Quad)) : False := by
  exact not_seven_dvd_psi t u ht hu (seven_dvd_im_of_signed_fourteenthPower hpow)

/-- A checked infinite-descent engine: the construction of a smaller solution
rules out every solution of Dirichlet's generalized equation. -/
theorem no_descentEquation_of_descends (hdesc : Descends) :
    ∀ t u w : ℤ, ∀ m n : ℕ, ¬DescentEquation t u w m n := by
  classical
  intro t u w m n h
  let P : ℕ → Prop := fun k ↦
    ∃ t u w : ℤ, ∃ m n : ℕ, DescentEquation t u w m n ∧ height t = k
  have hP : ∃ k, P k := ⟨height t, t, u, w, m, n, h, rfl⟩
  obtain ⟨t₀, u₀, w₀, m₀, n₀, h₀, hheight⟩ := Nat.find_spec hP
  obtain ⟨t₁, u₁, w₁, m₁, n₁, h₁, hlt⟩ := hdesc h₀
  have hminimal : Nat.find hP ≤ height t₁ :=
    Nat.find_min' hP ⟨t₁, u₁, w₁, m₁, n₁, h₁, rfl⟩
  rw [hheight] at hlt
  exact (Nat.not_lt_of_ge hminimal) hlt

end Fermat.Fourteen.Dirichlet
