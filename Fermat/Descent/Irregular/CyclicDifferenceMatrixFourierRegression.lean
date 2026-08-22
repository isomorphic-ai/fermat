import Fermat.Descent.Irregular.CyclicDifferenceMatrixFourier

/-!
# Small-cycle regressions for the Fourier determinant formula

These examples lock down the coordinate and reversal conventions before the
factored determinant path is applied to large exponent certificates.  Cycle
lengths `2`, `3`, `4`, and `5` exercise both signs of `Fin.revPerm`, including
the fixed order-two character in the even cycle.
-/

namespace Fermat.Irregular.CyclicDifferenceMatrix.FourierRegression

open scoped BigOperators Matrix

private def f2 (u : Cyc 1) : ZMod 5 := u.val + 2
private def f3 (u : Cyc 2) : ZMod 7 := if u = 0 then 1 else 0
private def f4 (u : Cyc 3) : ZMod 5 := u.val ^ 2 + 3 * u.val + 1
private def f5 (u : Cyc 4) : ZMod 11 := u.val ^ 3 + 2 * u.val + 4

private theorem primitive2 : IsPrimitiveRoot (4 : ZMod 5) 2 := by
  refine IsPrimitiveRoot.mk_of_lt _ (by omega) (by decide) ?_
  intro l hl hlt
  interval_cases l
  decide

private theorem primitive3 : IsPrimitiveRoot (2 : ZMod 7) 3 := by
  refine IsPrimitiveRoot.mk_of_lt _ (by omega) (by decide) ?_
  intro l hl hlt
  interval_cases l <;> decide

private theorem primitive4 : IsPrimitiveRoot (2 : ZMod 5) 4 := by
  refine IsPrimitiveRoot.mk_of_lt _ (by omega) (by decide) ?_
  intro l hl hlt
  interval_cases l <;> decide

private theorem primitive5 : IsPrimitiveRoot (4 : ZMod 11) 5 := by
  refine IsPrimitiveRoot.mk_of_lt _ (by omega) (by decide) ?_
  intro l hl hlt
  interval_cases l <;> decide

/-- Cycle length two: reversal fixes the sole nontrivial character. -/
theorem cycleTwo :
    (differenceMatrix 1 f2).det =
      (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin 1)) : ZMod 5) *
        ∏ k : Fin 1,
          ∑ u : Cyc 1, f2 u * (4 : ZMod 5) ^ ((k.val + 1) * u.val) := by
  decide

/-- Cycle length three: reversal swaps both nontrivial characters. -/
theorem cycleThree :
    (differenceMatrix 2 f3).det =
      (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin 2)) : ZMod 7) *
        ∏ k : Fin 2,
          ∑ u : Cyc 2, f3 u * (2 : ZMod 7) ^ ((k.val + 1) * u.val) := by
  decide

/-- Cycle length four: reversal has one pair and one fixed character. -/
theorem cycleFour :
    (differenceMatrix 3 f4).det =
      (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin 3)) : ZMod 5) *
        ∏ k : Fin 3,
          ∑ u : Cyc 3, f4 u * (2 : ZMod 5) ^ ((k.val + 1) * u.val) := by
  decide

/-- Cycle length five: reversal has two pairs and positive sign. -/
theorem cycleFive :
    (differenceMatrix 4 f5).det =
      (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin 4)) : ZMod 11) *
        ∏ k : Fin 4,
          ∑ u : Cyc 4, f5 u * (4 : ZMod 11) ^ ((k.val + 1) * u.val) := by
  decide

/-- In the length-three sign test, the determinant is `-1` modulo `7`. -/
theorem cycleThree_det_value : (differenceMatrix 2 f3).det = (6 : ZMod 7) := by
  decide

/-- The concrete length-three Fourier factors are both nonzero. -/
theorem cycleThree_fourierCoeff_ne_zero :
    ∀ k : Fin 2, fourierCoeff (2 : ZMod 7) primitive3.pow_eq_one f3 k ≠ 0 := by
  decide

/-- The nonvanishing criterion recovers nonsingularity in the small model. -/
theorem cycleThree_det_ne_zero : (differenceMatrix 2 f3).det ≠ 0 := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  rw [differenceMatrix_det_ne_zero_iff_fourierCoeff
    (2 : ZMod 7) primitive3 f3]
  exact cycleThree_fourierCoeff_ne_zero

end Fermat.Irregular.CyclicDifferenceMatrix.FourierRegression
