/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Integral Fermat states at exponent 59

This is the stock state consumed by the selected factor ledger.  The
orientation theorem rotates a second-case state until the third coordinate
is divisible by the exponent.  It deliberately asserts no preservation of
the hypotenuse charge under that rotation.
-/
import Fermat.Experiments.Conservation.Floor
import Mathlib.Tactic

namespace Fermat.FiftyNine.Conservation.FermatState

/-- A primitive nonzero integral second-case solution at exponent 59. -/
structure PrimitiveSecondCaseSolution where
  x : ℤ
  y : ℤ
  z : ℤ
  x_ne_zero : x ≠ 0
  y_ne_zero : y ≠ 0
  z_ne_zero : z ≠ 0
  primitive : ({x, y, z} : Finset ℤ).gcd id = 1
  equation : x ^ 59 + y ^ 59 = z ^ 59
  secondCase : (59 : ℤ) ∣ x * y * z

/-- The literal hypotenuse charge. -/
def PrimitiveSecondCaseSolution.charge
    (S : PrimitiveSecondCaseSolution) : ℕ :=
  S.z.natAbs

theorem PrimitiveSecondCaseSolution.charge_pos
    (S : PrimitiveSecondCaseSolution) :
    0 < S.charge :=
  Int.natAbs_pos.mpr S.z_ne_zero

/-- The exact strict-successor output required by the conservation floor. -/
def StrictSuccessor (S : PrimitiveSecondCaseSolution) : Prop :=
  ∃ next : PrimitiveSecondCaseSolution, next.charge < S.charge

/-- The complete state transformer required by the conservation floor. -/
def StockCreditTransformer : Prop :=
  ∀ S : PrimitiveSecondCaseSolution, StrictSuccessor S

theorem false_of_stockCreditTransformer
    (htransform : StockCreditTransformer)
    (start : PrimitiveSecondCaseSolution) :
    False :=
  Fermat.Conservation.impossible_of_strict_charge_drain
    start PrimitiveSecondCaseSolution.charge
      PrimitiveSecondCaseSolution.charge_pos htransform

private lemma int_gcd_left_comm (a b c : ℤ) :
    Int.gcd a (Int.gcd b c) = Int.gcd b (Int.gcd a c) := by
  rw [← Int.gcd_assoc, ← Int.gcd_assoc, Int.gcd_comm a b]

/-- Every second-case solution has an odd rotation whose third coordinate
is divisible by 59.  This is an existence theorem, not a charge identity. -/
theorem PrimitiveSecondCaseSolution.exists_oriented
    (S : PrimitiveSecondCaseSolution) :
    ∃ T : PrimitiveSecondCaseSolution, (59 : ℤ) ∣ T.z := by
  have hpodd : Odd 59 := by norm_num
  obtain hab | hpc :=
    (Nat.prime_iff_prime_int.mp (by norm_num : Nat.Prime 59)).dvd_or_dvd
      S.secondCase
  · obtain hpa | hpb :=
      (Nat.prime_iff_prime_int.mp (by norm_num : Nat.Prime 59)).dvd_or_dvd hab
    · refine ⟨{
        x := S.y
        y := -S.z
        z := -S.x
        x_ne_zero := S.y_ne_zero
        y_ne_zero := neg_ne_zero.mpr S.z_ne_zero
        z_ne_zero := neg_ne_zero.mpr S.x_ne_zero
        primitive := ?_
        equation := ?_
        secondCase := ?_ }, ?_⟩
      · simp only [← S.primitive, Finset.gcd_insert, id_eq, ← Int.coe_gcd,
          Int.neg_gcd, ← LawfulSingleton.insert_empty_eq, Finset.gcd_empty,
          int_gcd_left_comm _ S.x]
      · rw [hpodd.neg_pow, hpodd.neg_pow]
        linear_combination S.equation
      · exact dvd_mul_of_dvd_right (by rwa [dvd_neg]) _
      · rwa [dvd_neg]
    · refine ⟨{
        x := -S.z
        y := S.x
        z := -S.y
        x_ne_zero := neg_ne_zero.mpr S.z_ne_zero
        y_ne_zero := S.x_ne_zero
        z_ne_zero := neg_ne_zero.mpr S.y_ne_zero
        primitive := ?_
        equation := ?_
        secondCase := ?_ }, ?_⟩
      · simp only [← S.primitive, Finset.gcd_insert, id_eq, ← Int.coe_gcd,
          Int.neg_gcd, ← LawfulSingleton.insert_empty_eq, Finset.gcd_empty,
          int_gcd_left_comm _ S.z]
      · rw [hpodd.neg_pow, hpodd.neg_pow]
        linear_combination S.equation
      · exact dvd_mul_of_dvd_right (by rwa [dvd_neg]) _
      · rwa [dvd_neg]
  · exact ⟨S, hpc⟩

end Fermat.FiftyNine.Conservation.FermatState
