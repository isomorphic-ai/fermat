import Fermat.Descent.Irregular.CyclicDifferenceMatrixFourier

/-!
# Character projections of reduced cyclic-difference kernels

The reduced difference matrix deletes the trivial coordinate of a cyclic
convolution operator. Its left Fourier projection therefore uses the
deleted-character rows `χ(x) - 1`. This module proves that a matrix-kernel
vector has zero inverse-character moment after multiplication by the
corresponding Fourier coefficient.

Unlike the determinant factorization, this statement can be used one
frequency at a time. It is the reusable linear-algebra seam for selective
Case-II.1 certificates.
-/

namespace Fermat.Irregular.CyclicDifferenceMatrix

open scoped BigOperators Matrix

noncomputable section

variable {n : ℕ} [NeZero (n + 1)] {R : Type*} [CommRing R]

/-- Deleted positive-character moments. -/
def positiveMomentMatrix (ω : R) (hroot : ω ^ (n + 1) = 1) :
    Matrix (Fin n) (Fin n) R :=
  fun k i ↦ fourierChar ω hroot k (coord n i) - 1

/-- Deleted inverse-character moments. -/
def inverseMomentMatrix (ω : R) (hroot : ω ^ (n + 1) = 1) :
    Matrix (Fin n) (Fin n) R :=
  fun k i ↦ fourierChar ω hroot k (-coord n i) - 1

/-- Left character projection of a reduced difference matrix. -/
theorem positiveMomentMatrix_mul_differenceMatrix [IsDomain R]
    (ω : R) (hω : IsPrimitiveRoot ω (n + 1)) (f : Cyc n → R) :
    positiveMomentMatrix ω hω.pow_eq_one * differenceMatrix n f =
      Matrix.diagonal (fourierCoeff ω hω.pow_eq_one f) *
        inverseMomentMatrix ω hω.pow_eq_one := by
  classical
  ext k j
  rw [Matrix.mul_apply, Matrix.diagonal_mul]
  let χ := fourierChar ω hω.pow_eq_one k
  let y := coord n j
  let F : Cyc n → R := fun x ↦
    (χ x - 1) * (f (x + y) - f x)
  have hFzero : F 0 = 0 := by simp [F]
  change (∑ i : Fin n, F (coord n i)) = _
  rw [sum_coord_eq_sum_cyc_of_zero F hFzero]
  have hsplit :
      (∑ x : Cyc n, F x) =
        ((∑ x : Cyc n, f (y + x) * χ x) -
          ∑ x : Cyc n, f x * χ x) -
        ((∑ x : Cyc n, f (x + y)) - ∑ x : Cyc n, f x) := by
    dsimp only [F]
    simp_rw [show ∀ x : Cyc n,
        (χ x - 1) * (f (x + y) - f x) =
          (f (y + x) * χ x - f x * χ x) -
            (f (x + y) - f x) by
      intro x
      rw [add_comm x y]
      ring]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib]
  rw [hsplit]
  rw [sum_shift_mul_fourierChar ω hω f y k]
  change
    (χ (-y) * fourierCoeff ω hω.pow_eq_one f k -
      fourierCoeff ω hω.pow_eq_one f k) -
      ((∑ x : Cyc n, f (x + y)) - ∑ x : Cyc n, f x) = _
  rw [sum_add_right]
  simp only [sub_self, sub_zero, inverseMomentMatrix]
  ring

/-- A reduced-difference kernel vector has zero projected moment after
multiplication by the corresponding Fourier detector. -/
theorem fourierCoeff_mul_inverseMoment_of_mulVec_eq_zero [IsDomain R]
    (ω : R) (hω : IsPrimitiveRoot ω (n + 1)) (f : Cyc n → R)
    (v : Fin n → R)
    (hv : differenceMatrix n f *ᵥ v = 0) (k : Fin n) :
    fourierCoeff ω hω.pow_eq_one f k *
        (inverseMomentMatrix ω hω.pow_eq_one *ᵥ v) k = 0 := by
  have hmatrix := congrArg (fun M ↦ M *ᵥ v)
    (positiveMomentMatrix_mul_differenceMatrix ω hω f)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_zero] at hmatrix
  have hk := congrFun hmatrix k
  have hkdiag :
      (Matrix.diagonal (fourierCoeff ω hω.pow_eq_one f) *ᵥ
        (inverseMomentMatrix ω hω.pow_eq_one *ᵥ v)) k = 0 := by
    simpa only [Pi.zero_apply] using hk.symm
  simpa only [Matrix.mulVec_diagonal] using hkdiag

/-- Transport a right-kernel vector through independent row and column
reindexings. -/
theorem mulVec_reindex_equiv
    {S : Type*} [CommRing S] {I : Type*} [Fintype I]
    (row column : Equiv.Perm I) (M : Matrix I I S) (v : I → S) (r : I) :
    ((Matrix.reindex row.symm column.symm M) *ᵥ v) (row.symm r) =
      (M *ᵥ (v ∘ column.symm)) r := by
  classical
  simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
    Function.comp_apply]
  simpa only [Equiv.symm_apply_apply] using
    (Equiv.sum_comp column
      (fun i ↦ M r i * v (column.symm i)))

/-- A reduced difference matrix determines every nontrivial Fourier
coefficient. Its phase is determined only up to an additive constant, which
the nontrivial character sum kills. -/
theorem fourierCoeff_eq_of_differenceMatrix_eq [IsDomain R]
    (ω : R) (hω : IsPrimitiveRoot ω (n + 1))
    (f g : Cyc n → R)
    (hD : differenceMatrix n f = differenceMatrix n g)
    (frequency : Fin n) :
    fourierCoeff ω hω.pow_eq_one f frequency =
      fourierCoeff ω hω.pow_eq_one g frequency := by
  let x : Cyc n := coord n frequency
  let χ := fourierChar ω hω.pow_eq_one frequency
  let F : Cyc n → R := fun y ↦ (f (x + y) - f x) * χ y
  let G : Cyc n → R := fun y ↦ (g (x + y) - g x) * χ y
  have hFzero : F 0 = 0 := by simp [F]
  have hGzero : G 0 = 0 := by simp [G]
  have hsums : (∑ y : Cyc n, F y) = ∑ y : Cyc n, G y := by
    rw [← sum_coord_eq_sum_cyc_of_zero F hFzero,
      ← sum_coord_eq_sum_cyc_of_zero G hGzero]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [F, G, x]
    have hij := congrArg (fun M ↦ M frequency i) hD
    exact congrArg (fun z : R ↦ z * χ (coord n i)) hij
  have hcharSum : (∑ y : Cyc n, χ y) = 0 :=
    AddChar.sum_eq_zero_of_ne_one (fourierChar_ne_one ω hω frequency)
  have hF : (∑ y : Cyc n, F y) =
      χ (-x) * fourierCoeff ω hω.pow_eq_one f frequency := by
    calc
      (∑ y : Cyc n, F y) =
          (∑ y : Cyc n, f (x + y) * χ y) - f x * ∑ y : Cyc n, χ y := by
        simp only [F, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
      _ = (∑ y : Cyc n, f (x + y) * χ y) := by
        rw [hcharSum, mul_zero, sub_zero]
      _ = χ (-x) * fourierCoeff ω hω.pow_eq_one f frequency :=
        sum_shift_mul_fourierChar ω hω f x frequency
  have hG : (∑ y : Cyc n, G y) =
      χ (-x) * fourierCoeff ω hω.pow_eq_one g frequency := by
    calc
      (∑ y : Cyc n, G y) =
          (∑ y : Cyc n, g (x + y) * χ y) - g x * ∑ y : Cyc n, χ y := by
        simp only [G, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
      _ = (∑ y : Cyc n, g (x + y) * χ y) := by
        rw [hcharSum, mul_zero, sub_zero]
      _ = χ (-x) * fourierCoeff ω hω.pow_eq_one g frequency :=
        sum_shift_mul_fourierChar ω hω g x frequency
  rw [hF, hG] at hsums
  have hχ : χ (-x) ≠ 0 := by
    dsimp only [χ]
    rw [fourierChar_apply]
    exact pow_ne_zero _ (hω.ne_zero (by omega))
  exact mul_left_cancel₀ hχ hsums

end

end Fermat.Irregular.CyclicDifferenceMatrix
