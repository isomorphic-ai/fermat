/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Primitive entry data for the native exponent-six ledger

This module packages a hypothetical primitive integer solution at exponent
six without passing through any exponent-transport theorem.  Its first
consequences are likewise native: pairwise coprimality, the sixth-cyclotomic
factor ledger, the Pythagorean balance on cube coordinates, and the exact
modulo-nine allocation of the ramified prime.
-/
import Fermat.Exponents.Six.Conservation.Spine
import Fermat.Core.Statement.Basic
import Mathlib.Data.ZMod.Basic

namespace Fermat.Six.Conservation

/-- A nonzero primitive integer solution of the Fermat equation at exponent
six.  This is the native entry state for the conservation development. -/
structure PrimitiveSolution where
  a : ℤ
  b : ℤ
  c : ℤ
  a_ne_zero : a ≠ 0
  b_ne_zero : b ≠ 0
  c_ne_zero : c ≠ 0
  equation : a ^ 6 + b ^ 6 = c ^ 6
  primitive : Finset.gcd {a, b, c} id = 1

namespace PrimitiveSolution

/-- The three bases of a primitive sixth-power solution are pairwise
coprime. -/
theorem pairwise_isCoprime (S : PrimitiveSolution) :
    IsCoprime S.a S.b ∧ IsCoprime S.a S.c ∧ IsCoprime S.b S.c := by
  have common_prime_absurd (p : ℤ) (hp : Prime p)
      (hpa : p ∣ S.a) (hpb : p ∣ S.b) (hpc : p ∣ S.c) : False := by
    apply hp.not_dvd_one
    rw [← S.primitive]
    refine Finset.dvd_gcd (fun q hq ↦ ?_)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact hpa
    · exact hpb
    · exact hpc
  have hab : IsCoprime S.a S.b := by
    refine isCoprime_of_prime_dvd (fun h ↦ S.a_ne_zero h.1)
      (fun p hp hpa hpb ↦ ?_)
    have hpc : p ∣ S.c :=
      hp.dvd_of_dvd_pow (S.equation ▸
        dvd_add (dvd_pow hpa (by norm_num)) (dvd_pow hpb (by norm_num)))
    exact common_prime_absurd p hp hpa hpb hpc
  have hac : IsCoprime S.a S.c := by
    refine isCoprime_of_prime_dvd (fun h ↦ S.a_ne_zero h.1)
      (fun p hp hpa hpc ↦ ?_)
    have hpb6 : p ∣ S.b ^ 6 := by
      rw [show S.b ^ 6 = S.c ^ 6 - S.a ^ 6 by
        calc
          S.b ^ 6 = (S.a ^ 6 + S.b ^ 6) - S.a ^ 6 := by ring
          _ = S.c ^ 6 - S.a ^ 6 := by rw [S.equation]]
      exact dvd_sub (dvd_pow hpc (by norm_num)) (dvd_pow hpa (by norm_num))
    exact common_prime_absurd p hp hpa (hp.dvd_of_dvd_pow hpb6) hpc
  have hbc : IsCoprime S.b S.c := by
    refine isCoprime_of_prime_dvd (fun h ↦ S.b_ne_zero h.1)
      (fun p hp hpb hpc ↦ ?_)
    have hpa6 : p ∣ S.a ^ 6 := by
      rw [show S.a ^ 6 = S.c ^ 6 - S.b ^ 6 by
        calc
          S.a ^ 6 = (S.a ^ 6 + S.b ^ 6) - S.b ^ 6 := by ring
          _ = S.c ^ 6 - S.b ^ 6 := by rw [S.equation]]
      exact dvd_sub (dvd_pow hpc (by norm_num)) (dvd_pow hpb (by norm_num))
    exact common_prime_absurd p hp (hp.dvd_of_dvd_pow hpa6) hpb hpc
  exact ⟨hab, hac, hbc⟩

/-- The solution equation closes the native sixth-cyclotomic factor
ledger. -/
theorem native_ledger (S : PrimitiveSolution) :
    (S.a ^ 2 + S.b ^ 2) * charge (cofactorElement S.a S.b) =
      S.c ^ 6 := by
  rw [← sixth_ledger]
  exact S.equation

/-- The same solution is a Pythagorean balance whose legs and hypotenuse are
cubes. -/
theorem cube_balance (S : PrimitiveSolution) :
    PythagoreanTriple (S.a ^ 3) (S.b ^ 3) (S.c ^ 3) :=
  pythagorean_cube_balance S.equation

/-- Every sixth power modulo nine is exactly zero or one. -/
private theorem sixth_power_mod_nine (z : ZMod 9) :
    z ^ 6 = 0 ∨ z ^ 6 = 1 := by
  revert z
  decide

/-- A zero sixth-power residue modulo nine detects divisibility of its
integer base by three. -/
private theorem three_dvd_of_sixth_power_mod_nine_eq_zero {x : ℤ}
    (h : (x : ZMod 9) ^ 6 = 0) : (3 : ℤ) ∣ x := by
  have h9 : (9 : ℤ) ∣ x ^ 6 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (x ^ 6) 9).mp
    simpa only [Int.cast_pow] using h
  exact Int.prime_three.dvd_of_dvd_pow
    ((show (3 : ℤ) ∣ 9 by norm_num).trans h9)

/-- If three divides an integer, its sixth power vanishes modulo nine. -/
private theorem sixth_power_mod_nine_eq_zero_of_three_dvd {x : ℤ}
    (h : (3 : ℤ) ∣ x) : (x : ZMod 9) ^ 6 = 0 := by
  obtain ⟨k, rfl⟩ := h
  have hdvd : (9 : ℤ) ∣ (3 * k) ^ 6 := by
    refine ⟨81 * k ^ 6, ?_⟩
    ring
  have hcast :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd ((3 * k) ^ 6) 9).mpr hdvd
  simpa only [Int.cast_pow] using hcast

/-- A unit sixth-power residue modulo nine detects nondivisibility of its
integer base by three. -/
private theorem three_not_dvd_of_sixth_power_mod_nine_eq_one {x : ℤ}
    (h : (x : ZMod 9) ^ 6 = 1) : ¬(3 : ℤ) ∣ x := by
  intro h3
  have h0 := sixth_power_mod_nine_eq_zero_of_three_dvd h3
  exact (show (0 : ZMod 9) ≠ 1 by decide) (h0.symm.trans h)

/-- The exact modulo-nine allocation forced by a primitive sixth-power
solution: precisely one leg is divisible by three, and the hypotenuse is
not. -/
theorem three_divisibility_pattern (S : PrimitiveSolution) :
    ((3 : ℤ) ∣ S.a ∧ ¬(3 : ℤ) ∣ S.b ∧ ¬(3 : ℤ) ∣ S.c) ∨
      ((3 : ℤ) ∣ S.b ∧ ¬(3 : ℤ) ∣ S.a ∧ ¬(3 : ℤ) ∣ S.c) := by
  have heq : (S.a : ZMod 9) ^ 6 + (S.b : ZMod 9) ^ 6 =
      (S.c : ZMod 9) ^ 6 := by
    simpa only [Int.cast_add, Int.cast_pow] using
      congrArg (fun z : ℤ ↦ (z : ZMod 9)) S.equation
  rcases sixth_power_mod_nine (S.a : ZMod 9) with ha0 | ha1
  · have h3a : (3 : ℤ) ∣ S.a :=
      three_dvd_of_sixth_power_mod_nine_eq_zero ha0
    rcases sixth_power_mod_nine (S.b : ZMod 9) with hb0 | hb1
    · have h3b : (3 : ℤ) ∣ S.b :=
        three_dvd_of_sixth_power_mod_nine_eq_zero hb0
      rcases sixth_power_mod_nine (S.c : ZMod 9) with hc0 | hc1
      · have h3c : (3 : ℤ) ∣ S.c :=
          three_dvd_of_sixth_power_mod_nine_eq_zero hc0
        have h3gcd : (3 : ℤ) ∣ Finset.gcd {S.a, S.b, S.c} id := by
          refine Finset.dvd_gcd (fun q hq ↦ ?_)
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl
          · exact h3a
          · exact h3b
          · exact h3c
        rw [S.primitive] at h3gcd
        exact ((by norm_num : ¬(3 : ℤ) ∣ 1) h3gcd).elim
      · have hbad : (0 : ZMod 9) = 1 := by
          simpa only [ha0, hb0, hc1, zero_add] using heq
        exact ((by decide : (0 : ZMod 9) ≠ 1) hbad).elim
    · have h3b : ¬(3 : ℤ) ∣ S.b :=
        three_not_dvd_of_sixth_power_mod_nine_eq_one hb1
      rcases sixth_power_mod_nine (S.c : ZMod 9) with hc0 | hc1
      · have hbad : (1 : ZMod 9) = 0 := by
          simpa only [ha0, hb1, hc0, zero_add] using heq
        exact ((by decide : (1 : ZMod 9) ≠ 0) hbad).elim
      · have h3c : ¬(3 : ℤ) ∣ S.c :=
          three_not_dvd_of_sixth_power_mod_nine_eq_one hc1
        exact Or.inl ⟨h3a, h3b, h3c⟩
  · have h3a : ¬(3 : ℤ) ∣ S.a :=
      three_not_dvd_of_sixth_power_mod_nine_eq_one ha1
    rcases sixth_power_mod_nine (S.b : ZMod 9) with hb0 | hb1
    · have h3b : (3 : ℤ) ∣ S.b :=
        three_dvd_of_sixth_power_mod_nine_eq_zero hb0
      rcases sixth_power_mod_nine (S.c : ZMod 9) with hc0 | hc1
      · have hbad : (1 : ZMod 9) = 0 := by
          simpa only [ha1, hb0, hc0, add_zero] using heq
        exact ((by decide : (1 : ZMod 9) ≠ 0) hbad).elim
      · have h3c : ¬(3 : ℤ) ∣ S.c :=
          three_not_dvd_of_sixth_power_mod_nine_eq_one hc1
        exact Or.inr ⟨h3b, h3a, h3c⟩
    · rcases sixth_power_mod_nine (S.c : ZMod 9) with hc0 | hc1
      · have htwo_ne : (1 + 1 : ZMod 9) ≠ 0 := by decide
        have hbad : (1 + 1 : ZMod 9) = 0 := by
          simpa only [ha1, hb1, hc0] using heq
        exact (htwo_ne hbad).elim
      · have htwo_ne : (1 + 1 : ZMod 9) ≠ 1 := by decide
        have hbad : (1 + 1 : ZMod 9) = 1 := by
          simpa only [ha1, hb1, hc1] using heq
        exact (htwo_ne hbad).elim

end PrimitiveSolution

end Fermat.Six.Conservation
