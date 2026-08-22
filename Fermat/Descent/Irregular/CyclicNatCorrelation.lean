import Fermat.Descent.Irregular.CyclicDifferenceMatrix

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

/-- Tail-recursively verify a consecutive range of natural-valued
certificates. Each comparison is discharged before the recursive call, so
large ranges need not elaborate as one quantified decision problem. -/
def verifyRange (actual expected : ℕ → ℕ) (offset : ℕ) : ℕ → Bool
  | 0 => true
  | size + 1 =>
      if actual offset = expected offset then
        verifyRange actual expected (offset + 1) size
      else
        false

/-- Extract any local equality from a successful tail-recursive range
verification. -/
theorem verifyRange_get (actual expected : ℕ → ℕ) (offset size : ℕ)
    (h : verifyRange actual expected offset size = true) (i : Fin size) :
    actual (offset + i.val) = expected (offset + i.val) := by
  induction size generalizing offset with
  | zero =>
      exact Fin.elim0 i
  | succ size ih =>
      by_cases hhead : actual offset = expected offset
      · simp only [verifyRange, if_pos hhead] at h
        by_cases hi : i.val = 0
        · simpa only [hi, add_zero] using hhead
        · let j : Fin size := ⟨i.val - 1, by omega⟩
          have hj := ih (offset + 1) h j
          have hoffset : offset + 1 + j.val = offset + i.val := by
            simp only [j]
            omega
          simpa only [hoffset] using hj
      · simp only [verifyRange, if_neg hhead] at h
        contradiction

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
