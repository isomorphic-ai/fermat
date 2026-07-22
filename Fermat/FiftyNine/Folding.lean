import Fermat.Classical
import Fermat.Five.Dirichlet
import Fermat.FiftyNine.FirstCase

/-!
# Structural folding certificates for exponent 59

This module records the compact exact objects that make the supplied
seven-fold decomposition specific to `59`: the safe-prime circle, the two
neighbor reductions, the quadratic norm geometry, and the literal
`B59 = B11 * Q24` composition.  These identities organize the proof but do
not silently claim the singular-primary second-case theorem.
-/

namespace Fermat.FiftyNine.Folding

/-- The safe-prime ladder visible in the multiplicative circle at `59`. -/
theorem safePrimeLadder :
    59 = 2 * 29 + 1 ∧ 29 = 2 * 14 + 1 ∧ 14 = 2 * 7 := by
  norm_num

/-- The element `2` generates the full nonzero residue circle modulo `59`. -/
theorem two_order_mod_59 : orderOf (2 : ZMod 59) = 58 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro p hp hpd
  have hprod : p ∣ 2 * 29 := by simpa using hpd
  rcases hp.dvd_mul.mp hprod with hp2 | hp29
  · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hp2 with hp1 | rfl
    · exact (hp.ne_one hp1).elim
    · decide
  · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 29)).mp hp29 with hp1 | rfl
    · exact (hp.ne_one hp1).elim
    · decide

/-- Squaring folds the order-`58` circle onto its order-`29` subgroup. -/
theorem four_order_mod_59 : orderOf (4 : ZMod 59) = 29 := by
  letI : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

/-- A proof at exponent `29` closes the left neighbor `58` by squaring. -/
theorem holdsAt_fiftyEight_of_twentyNine
    (h29 : Fermat.HoldsAt 29) : Fermat.HoldsAt 58 :=
  h29.mono_of_dvd (by norm_num)

/-- The right neighbor `60` closes through exponent `3`. -/
theorem holdsAt_sixty_via_three : Fermat.HoldsAt 60 :=
  Fermat.holdsAt_three.mono_of_dvd (by norm_num)

/-- The same right neighbor independently closes through exponent `4`. -/
theorem holdsAt_sixty_via_four : Fermat.HoldsAt 60 :=
  Fermat.holdsAt_four.mono_of_dvd (by norm_num)

/-- The same right neighbor independently closes through Dirichlet's
historical exponent-`5` proof. -/
theorem holdsAt_sixty_via_five : Fermat.HoldsAt 60 :=
  Fermat.Five.Dirichlet.holdsAt_five_dirichlet.mono_of_dvd (by norm_num)

/-- Norm form in `ℤ[(1 + sqrt(-59))/2]`. -/
def quadraticNorm (a b : ℤ) : ℤ :=
  a ^ 2 + a * b + 15 * b ^ 2

/-- The discriminant identity making the square-root sheet explicit. -/
theorem quadraticNorm_discriminant (a b : ℤ) :
    (2 * a + b) ^ 2 + 59 * b ^ 2 = 4 * quadraticNorm a b := by
  simp only [quadraticNorm]
  ring

/-- The old exponent-`11` square-root coordinate occurring inside the
exponent-`59` fold. -/
def B11 (x y : ℤ) : ℤ :=
  x * y * (x - y) * (x ^ 2 + x * y + y ^ 2)

/-- The irreducible degree-`24` residual supplied by the proof package. -/
def Q24 (x y : ℤ) : ℤ :=
  x ^ 24 - 2 * x ^ 22 * y ^ 2 - 2 * x ^ 21 * y ^ 3 - x ^ 20 * y ^ 4 +
    2 * x ^ 19 * y ^ 5 + 2 * x ^ 18 * y ^ 6 - 2 * x ^ 16 * y ^ 8 -
    x ^ 15 * y ^ 9 + x ^ 14 * y ^ 10 + 2 * x ^ 13 * y ^ 11 +
    3 * x ^ 12 * y ^ 12 + 2 * x ^ 11 * y ^ 13 + x ^ 10 * y ^ 14 -
    x ^ 9 * y ^ 15 - 2 * x ^ 8 * y ^ 16 + 2 * x ^ 6 * y ^ 18 +
    2 * x ^ 5 * y ^ 19 - x ^ 4 * y ^ 20 - 2 * x ^ 3 * y ^ 21 -
    2 * x ^ 2 * y ^ 22 + y ^ 24

/-- The square-root coordinate produced by the `59`th quadratic-period
fold, written exactly as generated in the package. -/
def B59 (x y : ℤ) : ℤ :=
  x ^ 28 * y - 2 * x ^ 26 * y ^ 3 - 3 * x ^ 25 * y ^ 4 -
    x ^ 24 * y ^ 5 + 4 * x ^ 23 * y ^ 6 + 4 * x ^ 22 * y ^ 7 +
    x ^ 21 * y ^ 8 - 4 * x ^ 20 * y ^ 9 - 3 * x ^ 19 * y ^ 10 +
    x ^ 18 * y ^ 11 + 4 * x ^ 17 * y ^ 12 + 4 * x ^ 16 * y ^ 13 +
    x ^ 15 * y ^ 14 - x ^ 14 * y ^ 15 - 4 * x ^ 13 * y ^ 16 -
    4 * x ^ 12 * y ^ 17 - x ^ 11 * y ^ 18 + 3 * x ^ 10 * y ^ 19 +
    4 * x ^ 9 * y ^ 20 - x ^ 8 * y ^ 21 - 4 * x ^ 7 * y ^ 22 -
    4 * x ^ 6 * y ^ 23 + x ^ 5 * y ^ 24 + 3 * x ^ 4 * y ^ 25 +
    2 * x ^ 3 * y ^ 26 - x * y ^ 28

/-- The central exact scalar composition `B59 = B11 * Q24`. -/
theorem B59_eq_B11_mul_Q24 (x y : ℤ) :
    B59 x y = B11 x y * Q24 x y := by
  simp only [B59, B11, Q24]
  ring

/-- The degree-`24` residual is reciprocal, a prerequisite for the package's
mirror fold to degree `12`. -/
theorem Q24_symmetric (x y : ℤ) : Q24 x y = Q24 y x := by
  simp only [Q24]
  ring

end Fermat.FiftyNine.Folding
