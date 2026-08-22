import Fermat.Descent.Irregular.CyclicDifferenceMatrixFourier

/-!
# Kernel-trusted finite Fourier evaluation

Concrete Fourier coefficients over `ZMod` can be expensive for the kernel
to normalize in their abstract finite-sum form.  This module supplies a
structurally recursive Horner evaluator on natural representatives and
proves once and for all that casting its result recovers the corresponding
finite sum.

The evaluator changes only the executable representation of the
calculation.  Its certificates still use ordinary kernel reduction; no
native evaluation or additional trust primitive is involved.
-/

namespace Fermat.Irregular.CyclicNatFourier

open scoped BigOperators

/-- Evaluate the coefficient list
`a₀ + a₁ X + ⋯ + aₙ Xⁿ` modulo `modulus` by Horner recursion. -/
def evaluate (modulus root : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: as => (a + root * evaluate modulus root as) % modulus

/-- Casting the Horner evaluator gives the usual finite power sum. -/
theorem cast_evaluate (modulus root : ℕ) (data : List ℕ) :
    (evaluate modulus root data : ZMod modulus) =
      ∑ i ∈ Finset.range data.length,
        (data[i]! : ZMod modulus) * (root : ZMod modulus) ^ i := by
  induction data with
  | nil => simp [evaluate]
  | cons a as ih =>
      rw [evaluate]
      simp only [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul]
      simp only [List.length_cons]
      rw [Finset.sum_range_succ']
      simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]
      rw [ih]
      simp only [pow_succ]
      rw [Finset.mul_sum]
      ring_nf

/-- When an array has exactly the cycle length, its Horner evaluation is
the abstract cyclic power sum indexed by `ZMod cycleLength`. -/
theorem cast_evaluate_toList_eq_cyclicSum
    (modulus cycleLength root : ℕ) [NeZero cycleLength]
    (data : Array ℕ) (hlen : data.size = cycleLength) :
    (evaluate modulus root data.toList : ZMod modulus) =
      ∑ u : ZMod cycleLength,
        (data[u.val]! : ZMod modulus) * (root : ZMod modulus) ^ u.val := by
  rw [cast_evaluate]
  simp only [Array.length_toList, hlen]
  rw [show
      (∑ u : ZMod cycleLength,
          (data[u.val]! : ZMod modulus) * (root : ZMod modulus) ^ u.val) =
        ∑ i : Fin cycleLength,
          (data[(ZMod.finEquiv cycleLength i).val]! : ZMod modulus) *
            (root : ZMod modulus) ^ (ZMod.finEquiv cycleLength i).val by
    exact (Equiv.sum_comp (ZMod.finEquiv cycleLength).toEquiv
      (fun u : ZMod cycleLength ↦
        (data[u.val]! : ZMod modulus) *
          (root : ZMod modulus) ^ u.val)).symm]
  have hfin (i : Fin cycleLength) :
      (ZMod.finEquiv cycleLength i).val = i.val := by
    cases cycleLength with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ _ => rfl
  simpa only [hfin, Array.getElem!_toList] using
    (Fin.sum_univ_eq_sum_range
      (fun i : ℕ ↦
        (data[i]! : ZMod modulus) * (root : ZMod modulus) ^ i)
      cycleLength).symm

end Fermat.Irregular.CyclicNatFourier
