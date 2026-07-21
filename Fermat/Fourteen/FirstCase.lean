import Fermat.Fourteen.DescentSetup
import Fermat.Fourteen.Reduction

/-!
# Dirichlet's first case for exponent 14

If none of the three entries is divisible by `7`, the first factorization
and signed quadratic-form extraction force `7 ∣ ψ`, contradicting the
elementary modulo-`7` calculation.
-/

namespace Fermat.Fourteen.Dirichlet

open Fermat.Fourteen.PowerExtraction

/-- The positive norm factor in Dirichlet's first factorization. -/
def firstNormFactor (t u : ℤ) : ℤ :=
  phi t u ^ 6 + 7 * psi t u ^ 2

theorem first_factorization (t u : ℤ) :
    t ^ 14 - u ^ 14 = phi t u * firstNormFactor t u := by
  rw [factorization]
  simp only [firstNormFactor]
  ring

theorem firstNormFactor_pos {t u : ℤ} (ht : t ≠ 0) (hu : u ≠ 0) :
    0 < firstNormFactor t u := by
  have hp : psi t u ≠ 0 := psi_ne_zero ht hu
  simp only [firstNormFactor]
  have hp2 : 0 < psi t u ^ 2 := sq_pos_of_ne_zero hp
  positivity

theorem isCoprime_phi_firstNormFactor {t u : ℤ}
    (htu : IsCoprime t u) (hseven : ¬(7 : ℤ) ∣ phi t u) :
    IsCoprime (phi t u) (firstNormFactor t u) := by
  have hphiSeven : IsCoprime (phi t u) (7 : ℤ) :=
    ((show Prime (7 : ℤ) by norm_num).coprime_iff_not_dvd.mpr hseven).symm
  have hphiPsi := isCoprime_phi_psi t u htu
  have hbase : IsCoprime (phi t u) (7 * psi t u ^ 2) :=
    hphiSeven.mul_right (hphiPsi.pow_right (n := 2))
  convert hbase.add_mul_left_right (phi t u ^ 5) using 1
  simp only [firstNormFactor]
  ring

theorem not_seven_dvd_phi_of_not_seven_dvd_v {t u v : ℤ}
    (heq : t ^ 14 = u ^ 14 + v ^ 14) (hv : ¬(7 : ℤ) ∣ v) :
    ¬(7 : ℤ) ∣ phi t u := by
  intro hphi
  have h7v14 : (7 : ℤ) ∣ v ^ 14 := by
    rw [show v ^ 14 = t ^ 14 - u ^ 14 by omega, first_factorization]
    exact dvd_mul_of_dvd_left hphi _
  exact hv ((show Prime (7 : ℤ) by norm_num).dvd_of_dvd_pow h7v14)

theorem oppositeParity_phi_cube_psi {t u : ℤ} (htu : IsCoprime t u) :
    OppositeParity (phi t u ^ 3) (psi t u) := by
  rcases oppositeParity_phi_psi htu with ⟨hphi, hpsi⟩ | ⟨hphi, hpsi⟩
  · exact Or.inl ⟨Int.even_pow.mpr ⟨hphi, by norm_num⟩, hpsi⟩
  · exact Or.inr ⟨hphi.pow, hpsi⟩

/-- Dirichlet's first case, now using the sign-correct representation
theorem proved through the Euclidean maximal order. -/
theorem firstCaseImpossible : FirstCaseImpossible := by
  intro t u v hnonzero htu _ heq htSeven huSeven hvSeven
  have ht : t ≠ 0 := by
    intro ht
    subst t
    simp at hnonzero
  have hu : u ≠ 0 := by
    intro hu
    subst u
    simp at hnonzero
  have hphiSeven := not_seven_dvd_phi_of_not_seven_dvd_v heq hvSeven
  have hcoprime := isCoprime_phi_firstNormFactor htu hphiSeven
  have hproduct : phi t u * firstNormFactor t u = v ^ 14 := by
    rw [← first_factorization]
    omega
  obtain ⟨A, hA⟩ := exists_pow_eq_abs_of_mul_eq_pow_right
    hcoprime (by decide : Even 14) hproduct
  have hnormPos := firstNormFactor_pos ht hu
  have hnorm : (phi t u ^ 3) ^ 2 + 7 * psi t u ^ 2 = A ^ 14 := by
    rw [← hA, abs_of_pos hnormPos]
    simp only [firstNormFactor]
    ring
  have hphiCubeSeven : ¬(7 : ℤ) ∣ phi t u ^ 3 := by
    intro h
    exact hphiSeven ((show Prime (7 : ℤ) by norm_num).dvd_of_dvd_pow h)
  obtain ⟨r, s, hpow⟩ := exists_signed_fourteenthPower_in_suborder
    (phi t u ^ 3) (psi t u) A
    ((isCoprime_phi_psi t u htu).pow_left (m := 3))
    (by
      rcases oppositeParity_phi_cube_psi htu with h | h
      · exact Or.inr h
      · exact Or.inl h)
    hphiCubeSeven hnorm
  exact first_case_contradiction t u htSeven huSeven ⟨⟨r, s⟩, hpow⟩

end Fermat.Fourteen.Dirichlet
