import Fermat.Five.Equation

/-!
# Reduction of FLT for exponent 5 to Dirichlet's fifth-power equation

This file is the outer shell of Dirichlet's proof.  It turns a primitive
counterexample to Fermat's Last Theorem at exponent `5` into a nonzero
primitive solution of `FifthEquation`.  The modulo-`25` calculation and all
signed permutations are encapsulated by `exists_fifthEquation_of_pairwise`.
-/

namespace Fermat.Five.Dirichlet

/-- The descent obligation needed by the outer reduction, stated without
committing to any particular implementation of the descent. -/
def FifthEquationImpossible : Prop :=
  ∀ {x y z : ℤ}, ¬ FifthEquation x y z

/-- Pairwise coprimality follows from primitivity and the Fermat equation. -/
private theorem pairwise_isCoprime_of_gcd_eq_one {a b c : ℤ}
    (hgcd : Finset.gcd {a, b, c} id = 1)
    (heq : a ^ 5 + b ^ 5 = c ^ 5) :
    IsCoprime a b ∧ IsCoprime a c ∧ IsCoprime b c := by
  have common_prime_absurd (p : ℤ) (hp : Prime p)
      (hpa : p ∣ a) (hpb : p ∣ b) (hpc : p ∣ c) : False := by
    apply hp.not_dvd_one
    rw [← hgcd]
    refine Finset.dvd_gcd (fun q hq ↦ ?_)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact hpa
    · exact hpb
    · exact hpc
  have hab : IsCoprime a b := by
    refine isCoprime_of_prime_dvd ?_ (fun p hp hpa hpb ↦ ?_)
    · rintro ⟨rfl, rfl⟩
      have hc : c = 0 := (pow_eq_zero_iff (by norm_num)).1 heq.symm
      subst c
      norm_num at hgcd
    · have hpc : p ∣ c := hp.dvd_of_dvd_pow (heq ▸ dvd_add
          (dvd_pow hpa (by norm_num)) (dvd_pow hpb (by norm_num)))
      exact common_prime_absurd p hp hpa hpb hpc
  have hac : IsCoprime a c := by
    refine isCoprime_of_prime_dvd ?_ (fun p hp hpa hpc ↦ ?_)
    · rintro ⟨rfl, rfl⟩
      simp at heq
      subst b
      norm_num at hgcd
    · have hpb5 : p ∣ b ^ 5 := by
        rw [show b ^ 5 = c ^ 5 - a ^ 5 by omega]
        exact dvd_sub (dvd_pow hpc (by norm_num)) (dvd_pow hpa (by norm_num))
      exact common_prime_absurd p hp hpa (hp.dvd_of_dvd_pow hpb5) hpc
  have hbc : IsCoprime b c := by
    refine isCoprime_of_prime_dvd ?_ (fun p hp hpb hpc ↦ ?_)
    · rintro ⟨rfl, rfl⟩
      simp at heq
      subst a
      norm_num at hgcd
    · have hpa5 : p ∣ a ^ 5 := by
        rw [show a ^ 5 = c ^ 5 - b ^ 5 by omega]
        exact dvd_sub (dvd_pow hpc (by norm_num)) (dvd_pow hpb (by norm_num))
      exact common_prime_absurd p hp (hp.dvd_of_dvd_pow hpa5) hpb hpc
  exact ⟨hab, hac, hbc⟩

/-- Impossibility of Dirichlet's generalized fifth-power equation implies
Fermat's Last Theorem for exponent `5`. -/
theorem holdsAt_five_of_fifthEquationImpossible
    (hno : FifthEquationImpossible) : Fermat.HoldsAt 5 := by
  change FermatLastTheoremFor 5
  rw [fermatLastTheoremFor_iff_int]
  refine fermatLastTheoremWith_of_fermatLastTheoremWith_coprime
    (fun a b c ha hb hc hgcd heq ↦ ?_)
  obtain ⟨hab, hac, hbc⟩ := pairwise_isCoprime_of_gcd_eq_one hgcd heq
  have hnonzero : a * b * c ≠ 0 := by positivity
  obtain ⟨x, y, z, hxyz⟩ :=
    exists_fifthEquation_of_pairwise hnonzero hab hac hbc heq
  exact hno hxyz

end Fermat.Five.Dirichlet
