import Fermat.Descent.Irregular.CyclicDifferenceMatrix
import Mathlib.Data.Fin.Rev
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Fourier determinant formula for reduced cyclic difference matrices

For a cycle of length `n + 1`, a primitive root `ω`, and a function `f`,
the determinant of the reduced difference matrix factors as the product of
the `n` nontrivial finite Fourier coefficients of `f`.

The matrix convention in `differenceMatrix` uses `f (x + y)`, so its action
reverses characters.  The exact formula therefore includes the sign of
`Fin.revPerm`.  This is the structural source of the minus sign in the
exponent-1831 determinant computation.

The proof uses the nontrivial-character matrix.  It is a row-scaled
Vandermonde matrix and hence has nonzero determinant over any integral
domain.  The identity

`differenceMatrix f * fourierMatrix =`
`  reversedFourierMatrix * diagonal (fourierCoeff f)`

then gives the result by taking determinants and cancelling the Fourier
matrix determinant.  No division by the cycle length is required.
-/

namespace Fermat.Irregular.CyclicDifferenceMatrix

open scoped BigOperators Matrix

noncomputable section

variable {n : ℕ} [NeZero (n + 1)] {R : Type*} [CommRing R]

/-- The nontrivial additive character indexed by `k + 1`. -/
def fourierChar (ω : R) (hroot : ω ^ (n + 1) = 1) (k : Fin n) :
    AddChar (Cyc n) R :=
  (AddChar.zmodChar (n + 1) hroot).mulShift (coord n k)

@[simp]
theorem coord_val (i : Fin n) : (coord n i).val = i.val + 1 := rfl

@[simp]
theorem coord_eq_natCast (i : Fin n) :
    coord n i = ((i.val + 1 : ℕ) : Cyc n) := by
  symm
  simpa only [coord_val] using ZMod.natCast_zmod_val (coord n i)

@[simp]
theorem fourierChar_apply (ω : R) (hroot : ω ^ (n + 1) = 1)
    (k : Fin n) (u : Cyc n) :
    fourierChar ω hroot k u = ω ^ ((k.val + 1) * u.val) := by
  rw [fourierChar, AddChar.mulShift_apply, coord_eq_natCast,
    ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow,
    AddChar.zmodChar_apply, ← pow_mul, Nat.mul_comm]

/-- The Fourier coefficient at the nontrivial character `k + 1`. -/
def fourierCoeff (ω : R) (hroot : ω ^ (n + 1) = 1)
    (f : Cyc n → R) (k : Fin n) : R :=
  ∑ u : Cyc n, f u * fourierChar ω hroot k u

@[simp]
theorem fourierCoeff_eq_sum_pow (ω : R) (hroot : ω ^ (n + 1) = 1)
    (f : Cyc n → R) (k : Fin n) :
    fourierCoeff ω hroot f k =
      ∑ u : Cyc n, f u * ω ^ ((k.val + 1) * u.val) := by
  simp [fourierCoeff]

/-- The matrix of the nontrivial characters on nonzero cycle coordinates. -/
def fourierMatrix (ω : R) (hroot : ω ^ (n + 1) = 1) :
    Matrix (Fin n) (Fin n) R :=
  fun i k ↦ fourierChar ω hroot k (coord n i)

@[simp]
theorem fourierMatrix_apply (ω : R) (hroot : ω ^ (n + 1) = 1)
    (i k : Fin n) :
    fourierMatrix ω hroot i k =
      ω ^ ((i.val + 1) * (k.val + 1)) := by
  rw [fourierMatrix, fourierChar_apply, coord_val, Nat.mul_comm]

/-- Reversal of nonzero coordinates is additive negation on the cycle. -/
theorem coord_rev (i : Fin n) : coord n i.rev = -coord n i := by
  rw [coord_eq_natCast, coord_eq_natCast, eq_neg_iff_add_eq_zero,
    ← Nat.cast_add]
  have hsum : i.rev.val + 1 + (i.val + 1) = n + 1 := by
    simp only [Fin.val_rev]
    omega
  rw [hsum]
  exact ZMod.natCast_self (n + 1)

theorem fourierChar_rev_apply (ω : R) (hroot : ω ^ (n + 1) = 1)
    (k : Fin n) (u : Cyc n) :
    fourierChar ω hroot k.rev u = fourierChar ω hroot k (-u) := by
  simp only [fourierChar, AddChar.mulShift_apply, coord_rev]
  congr 1
  ring

theorem fourierChar_ne_one [IsDomain R] (ω : R)
    (hω : IsPrimitiveRoot ω (n + 1)) (k : Fin n) :
    fourierChar ω hω.pow_eq_one k ≠ 1 := by
  rw [AddChar.zmod_char_ne_one_iff]
  simp only [fourierChar, AddChar.mulShift_apply, mul_one,
    AddChar.zmodChar_apply, coord_val]
  exact hω.pow_ne_one_of_pos_of_lt (by omega) (by omega)

/-- Translation multiplies a Fourier coefficient by the corresponding
character value. -/
theorem sum_shift_mul_fourierChar [IsDomain R] (ω : R)
    (hω : IsPrimitiveRoot ω (n + 1)) (f : Cyc n → R)
    (x : Cyc n) (k : Fin n) :
    (∑ y : Cyc n, f (x + y) * fourierChar ω hω.pow_eq_one k y) =
      fourierChar ω hω.pow_eq_one k (-x) *
        fourierCoeff ω hω.pow_eq_one f k := by
  let χ := fourierChar ω hω.pow_eq_one k
  let H : Cyc n → R := fun u ↦ f u * χ (-x + u)
  calc
    (∑ y : Cyc n, f (x + y) * χ y) =
        ∑ y : Cyc n, H (x + y) := by
      apply Fintype.sum_congr
      intro y
      simp only [H]
      congr 2
      ring
    _ = ∑ u : Cyc n, H u := by
      exact Equiv.sum_comp (Equiv.addLeft x) H
    _ = χ (-x) * ∑ u : Cyc n, f u * χ u := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      change f u * χ (-x + u) = χ (-x) * (f u * χ u)
      rw [χ.map_add_eq_mul]
      ring
    _ = fourierChar ω hω.pow_eq_one k (-x) *
        fourierCoeff ω hω.pow_eq_one f k := rfl

/-- The reduced difference matrix intertwines the Fourier matrix with a
reversal and the diagonal matrix of Fourier coefficients. -/
theorem differenceMatrix_mul_fourierMatrix [IsDomain R] (ω : R)
    (hω : IsPrimitiveRoot ω (n + 1)) (f : Cyc n → R) :
    differenceMatrix n f * fourierMatrix ω hω.pow_eq_one =
      (fourierMatrix ω hω.pow_eq_one).submatrix id Fin.revPerm *
        Matrix.diagonal (fourierCoeff ω hω.pow_eq_one f) := by
  ext i k
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  simp only [Matrix.submatrix_apply, id_eq, Fin.revPerm_apply]
  let χ := fourierChar ω hω.pow_eq_one k
  let F : Cyc n → R := fun y ↦
    (f (coord n i + y) - f (coord n i)) * χ y
  have hFzero : F 0 = 0 := by simp [F]
  change (∑ j : Fin n, F (coord n j)) = _
  rw [sum_coord_eq_sum_cyc_of_zero F hFzero]
  change (∑ y : Cyc n,
    (f (coord n i + y) - f (coord n i)) * χ y) = _
  rw [show (∑ y : Cyc n,
      (f (coord n i + y) - f (coord n i)) * χ y) =
      (∑ y : Cyc n, f (coord n i + y) * χ y) -
        f (coord n i) * ∑ y : Cyc n, χ y by
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]]
  rw [sum_shift_mul_fourierChar ω hω f (coord n i) k,
    AddChar.sum_eq_zero_of_ne_one (fourierChar_ne_one ω hω k),
    mul_zero, sub_zero]
  change fourierChar ω hω.pow_eq_one k (-coord n i) *
      fourierCoeff ω hω.pow_eq_one f k =
    fourierChar ω hω.pow_eq_one k.rev (coord n i) *
      fourierCoeff ω hω.pow_eq_one f k
  rw [fourierChar_rev_apply]

private def fourierRoots (ω : R) : Fin n → R :=
  fun i ↦ ω ^ (i.val + 1)

private theorem fourierMatrix_eq_diagonal_mul_vandermonde (ω : R)
    (hroot : ω ^ (n + 1) = 1) :
    fourierMatrix ω hroot =
      Matrix.diagonal (fourierRoots ω) *
        Matrix.vandermonde (fourierRoots ω) := by
  ext i k
  rw [Matrix.diagonal_mul]
  simp only [Matrix.vandermonde, Matrix.of_apply, fourierRoots]
  rw [← pow_succ', ← pow_mul]
  simp [fourierMatrix_apply]

omit [NeZero (n + 1)] in
private theorem fourierRoots_injective (ω : R)
    (hω : IsPrimitiveRoot ω (n + 1)) :
    Function.Injective (fourierRoots ω : Fin n → R) := by
  intro i j hij
  have hexp : i.val + 1 = j.val + 1 :=
    hω.pow_inj (by omega) (by omega) hij
  exact Fin.ext (by omega)

private theorem fourierMatrix_det_ne_zero [IsDomain R] (ω : R)
    (hω : IsPrimitiveRoot ω (n + 1)) :
    (fourierMatrix ω hω.pow_eq_one).det ≠ 0 := by
  rw [fourierMatrix_eq_diagonal_mul_vandermonde, Matrix.det_mul]
  apply mul_ne_zero
  · rw [Matrix.det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact ((hω.isUnit (by omega)).pow (i.val + 1)).ne_zero
  · exact Matrix.det_vandermonde_ne_zero_iff.mpr
      (fourierRoots_injective ω hω)

/-- The determinant of a reduced difference matrix is the signed product
of its nontrivial finite Fourier coefficients.  The sign is exactly the
sign of character negation in the enumeration `1, ..., n`. -/
theorem differenceMatrix_det_eq_prod_fourier [IsDomain R] (ω : R)
    (hω : IsPrimitiveRoot ω (n + 1)) (f : Cyc n → R) :
    (differenceMatrix n f).det =
      (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : R) *
        ∏ k : Fin n, fourierCoeff ω hω.pow_eq_one f k := by
  have hP := fourierMatrix_det_ne_zero ω hω
  apply mul_right_cancel₀ hP
  calc
    (differenceMatrix n f).det * (fourierMatrix ω hω.pow_eq_one).det =
        (differenceMatrix n f * fourierMatrix ω hω.pow_eq_one).det := by
      rw [Matrix.det_mul]
    _ = ((fourierMatrix ω hω.pow_eq_one).submatrix id Fin.revPerm *
        Matrix.diagonal (fourierCoeff ω hω.pow_eq_one f)).det := by
      rw [differenceMatrix_mul_fourierMatrix ω hω f]
    _ = ((fourierMatrix ω hω.pow_eq_one).submatrix id Fin.revPerm).det *
        (Matrix.diagonal (fourierCoeff ω hω.pow_eq_one f)).det := by
      rw [Matrix.det_mul]
    _ = ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : R) *
        ∏ k : Fin n, fourierCoeff ω hω.pow_eq_one f k) *
          (fourierMatrix ω hω.pow_eq_one).det := by
      rw [Matrix.det_permute', Matrix.det_diagonal]
      ring

/-- A reduced cyclic difference matrix is nonsingular exactly when all of
its nontrivial finite Fourier coefficients are nonzero. -/
theorem differenceMatrix_det_ne_zero_iff_fourierCoeff [IsDomain R] (ω : R)
    (hω : IsPrimitiveRoot ω (n + 1)) (f : Cyc n → R) :
    (differenceMatrix n f).det ≠ 0 ↔
      ∀ k : Fin n, fourierCoeff ω hω.pow_eq_one f k ≠ 0 := by
  constructor
  · intro hdet k hk
    apply hdet
    rw [differenceMatrix_det_eq_prod_fourier ω hω f,
      Finset.prod_eq_zero (Finset.mem_univ k) hk, mul_zero]
  · intro hcoeff
    rw [differenceMatrix_det_eq_prod_fourier ω hω f]
    apply mul_ne_zero
    · change ((Units.map (Int.castRingHom R)
          (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) : Rˣ) : R) ≠ 0
      exact Units.ne_zero _
    · exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ hcoeff k

end

end Fermat.Irregular.CyclicDifferenceMatrix
