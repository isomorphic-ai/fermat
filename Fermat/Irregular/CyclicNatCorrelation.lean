import Fermat.Irregular.CyclicDifferenceMatrix

/-!
# Kernel-trusted natural evaluators for cyclic correlations

Large concrete correlations over `ZMod` can be expensive for the kernel to
normalize directly. This module supplies a tail-recursive evaluator on
natural representatives. Its accumulator is reduced modulo the target
characteristic at every step, and `cast_evaluate_eq_cyclicCorrelation`
proves once and for all that casting its result recovers the abstract
cyclic correlation.

The finite certificate still uses ordinary kernel reduction: this module
only changes the executable representation of the same computation.
-/

namespace Fermat.Irregular.CyclicNatCorrelation

open scoped BigOperators

/-- Read an array of natural representatives as a function between two
finite residue rings. -/
def arrayFunction (modulus : ℕ) (data : Array ℕ) {cycleLength : ℕ}
    (x : ZMod cycleLength) : ZMod modulus :=
  data[x.val]!

/-- Tail-recursive modular dot product. The `fuel` positions are processed
from `fuel - 1` down to zero. -/
def loop (modulus cycleLength : ℕ) (left right : Array ℕ) (shift : ℕ) :
    ℕ → ℕ → ℕ
  | 0, acc => acc
  | fuel + 1, acc =>
      loop modulus cycleLength left right shift fuel
        ((acc + left[fuel]! * right[(fuel + shift) % cycleLength]!) % modulus)

/-- Evaluate one complete cyclic correlation on natural representatives. -/
def evaluate (modulus cycleLength : ℕ) (left right : Array ℕ) (shift : ℕ) :
    ℕ :=
  loop modulus cycleLength left right shift cycleLength 0

/-- Casting the tail-recursive loop gives the corresponding partial dot
product. This is the algebraic seam that keeps later finite checks small. -/
theorem cast_loop (modulus cycleLength : ℕ) (left right : Array ℕ)
    (shift fuel acc : ℕ) :
    (loop modulus cycleLength left right shift fuel acc : ZMod modulus) =
      (acc : ZMod modulus) +
        ∑ i ∈ Finset.range fuel,
          (left[i]! : ZMod modulus) *
            (right[(i + shift) % cycleLength]! : ZMod modulus) := by
  induction fuel generalizing acc with
  | zero =>
      simp [loop]
  | succ fuel ih =>
      rw [loop, ih, Finset.sum_range_succ]
      simp only [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul]
      ring

/-- The natural evaluator is exactly the abstract cyclic correlation after
casting to the target residue ring. -/
theorem cast_evaluate_eq_cyclicCorrelation
    (modulus cycleLength : ℕ) [NeZero cycleLength]
    (left right : Array ℕ) (d : ZMod cycleLength) :
    (evaluate modulus cycleLength left right d.val : ZMod modulus) =
      ∑ u : ZMod cycleLength,
        arrayFunction modulus left u *
          arrayFunction modulus right (u + d) := by
  rw [evaluate, cast_loop]
  simp only [Nat.cast_zero, zero_add]
  rw [show
      (∑ u : ZMod cycleLength,
          arrayFunction modulus left u *
            arrayFunction modulus right (u + d)) =
        ∑ i : Fin cycleLength,
          arrayFunction modulus left (ZMod.finEquiv cycleLength i) *
            arrayFunction modulus right
              (ZMod.finEquiv cycleLength i + d) by
      exact (Equiv.sum_comp (ZMod.finEquiv cycleLength).toEquiv
        (fun u : ZMod cycleLength =>
          arrayFunction modulus left u *
            arrayFunction modulus right (u + d))).symm]
  have hfin (i : Fin cycleLength) :
      (ZMod.finEquiv cycleLength i).val = i.val := by
    cases cycleLength with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n => rfl
  simpa only [arrayFunction, ZMod.val_add, hfin] using
    (Fin.sum_univ_eq_sum_range
      (fun i : ℕ =>
        (left[i]! : ZMod modulus) *
          (right[(i + d.val) % cycleLength]! : ZMod modulus))
      cycleLength).symm

end Fermat.Irregular.CyclicNatCorrelation
