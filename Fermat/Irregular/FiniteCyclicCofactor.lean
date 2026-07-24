import Fermat.Irregular.CyclotomicLogDetPrime
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Compact finite convolution and augmentation-cofactor certificates

Large circular-unit residue matrices are complementary minors of a
convolution matrix on the real residue group

`(ZMod p)ˣ / {±1}`.

A dense inverse certificate for an `N × N` minor stores `N²` field
elements and asks the kernel to evaluate `N³` products.  The group
structure admits a much smaller certificate: an inverse convolution
kernel stores only `N` elements, and its `N` convolution identities cost
`N²` products to check.

This file proves the algebraic passage from such an inverse kernel to the
nonvanishing of every augmentation cofactor over an arbitrary field.  Its
last section records the standard real-residue reindexing used by the
prime-generic cyclotomic modules, including the transpose alignment with
the circular-unit evaluation convention.
-/

open scoped Classical BigOperators

namespace Fermat.Irregular.FiniteCyclicCofactor

noncomputable section

/-! ## Convolution inverse certificates -/

variable {G F : Type*} [CommGroup G] [Fintype G] [Field F]

/-- Right-regular convolution matrix over an arbitrary field. -/
def convolutionMatrix (f : G → F) : Matrix G G F :=
  Matrix.of fun x y ↦ f (x * y⁻¹)

/-- Convolution with the convention matching `convolutionMatrix`. -/
def convolution (f g : G → F) (x : G) : F :=
  ∑ y : G, f (x * y⁻¹) * g y

/-- The delta kernel at the group identity. -/
def deltaKernel (x : G) : F :=
  if x = 1 then 1 else 0

/-- Multiplication of convolution matrices is convolution of kernels. -/
theorem convolutionMatrix_mul (f g : G → F) :
    convolutionMatrix f * convolutionMatrix g =
      convolutionMatrix (convolution f g) := by
  ext x z
  rw [Matrix.mul_apply]
  simp only [convolutionMatrix, Matrix.of_apply, convolution]
  let e : G ≃ G := Equiv.mulRight z⁻¹
  calc
    (∑ y : G, f (x * y⁻¹) * g (y * z⁻¹)) =
        ∑ y : G,
          f ((x * z⁻¹) * (e y)⁻¹) * g (e y) := by
      apply Finset.sum_congr rfl
      intro y _
      change f (x * y⁻¹) * g (y * z⁻¹) =
        f ((x * z⁻¹) * (y * z⁻¹)⁻¹) * g (y * z⁻¹)
      congr 2
      group
    _ = ∑ y : G, f ((x * z⁻¹) * y⁻¹) * g y :=
      Equiv.sum_comp e
        (fun y : G ↦ f ((x * z⁻¹) * y⁻¹) * g y)

omit [Fintype G] in
@[simp]
theorem convolutionMatrix_delta :
    convolutionMatrix (deltaKernel (G := G) (F := F)) = 1 := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [convolutionMatrix, deltaKernel]
  · have hne : x * y⁻¹ ≠ 1 := by
      intro h
      exact hxy (mul_inv_eq_one.mp h)
    simp [convolutionMatrix, deltaKernel, hxy, hne]

/-- A right inverse convolution kernel certifies a nonsingular convolution
matrix. -/
theorem convolutionMatrix_det_ne_zero_of_inverseKernel
    {f g : G → F}
    (hinverse : ∀ x, convolution f g x = deltaKernel x) :
    (convolutionMatrix f).det ≠ 0 := by
  have hkernel : convolution f g = deltaKernel := funext hinverse
  have hmul : convolutionMatrix f * convolutionMatrix g = 1 := by
    rw [convolutionMatrix_mul, hkernel, convolutionMatrix_delta]
  intro hzero
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, hzero, zero_mul, Matrix.det_one] at hdet
  exact zero_ne_one hdet

/-! ## Augmentation cofactors over a field -/

variable {n : ℕ}

/-- The determinant-one row operation subtracting row `i₀` from every
other row. -/
def rowSubtractPivotTransform (i₀ : Fin (n + 1)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
  1 + Matrix.replicateCol (Fin 1)
      (fun i ↦ if i = i₀ then (0 : F) else -1) *
    Matrix.replicateRow (Fin 1)
      (fun j ↦ if j = i₀ then (1 : F) else 0)

theorem rowSubtractPivotTransform_det (i₀ : Fin (n + 1)) :
    (rowSubtractPivotTransform (F := F) i₀).det = 1 := by
  let u : Fin (n + 1) → F := fun i ↦ if i = i₀ then 0 else -1
  let v : Fin (n + 1) → F := fun j ↦ if j = i₀ then 1 else 0
  have hd : v ⬝ᵥ u = 0 := by
    rw [dotProduct]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i = i₀ <;> simp [u, v, hi]
  change
    (1 + Matrix.replicateCol (Fin 1) u *
      Matrix.replicateRow (Fin 1) v).det = 1
  calc
    _ = 1 + v ⬝ᵥ u :=
      Matrix.det_one_add_replicateCol_mul_replicateRow
        (ι := Fin 1) u v
    _ = 1 := by rw [hd, add_zero]

@[simp]
theorem rowSubtractPivotTransform_apply
    (i₀ i j : Fin (n + 1)) :
    rowSubtractPivotTransform (F := F) i₀ i j =
      (if i = j then 1 else 0) +
        (if i = i₀ then 0 else -1) *
          (if j = i₀ then 1 else 0) := by
  simp [rowSubtractPivotTransform, Matrix.add_apply, Matrix.one_apply,
    Matrix.mul_apply, Matrix.replicateCol_apply,
    Matrix.replicateRow_apply]

theorem rowSubtractPivotTransform_mul_apply
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (i₀ i j : Fin (n + 1)) :
    (rowSubtractPivotTransform (F := F) i₀ * A) i j =
      if i = i₀ then A i j else A i j - A i₀ j := by
  rw [Matrix.mul_apply]
  simp_rw [rowSubtractPivotTransform_apply]
  by_cases hi : i = i₀
  · subst i
    simp
  · simp [hi, Finset.sum_add_distrib, sub_eq_add_neg, add_mul]

/-- A convolution matrix reindexed by `Fin (n + 1)`. -/
def reindexedConvolutionMatrix
    (e : Fin (n + 1) ≃ G) (f : G → F) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
  Matrix.reindex e.symm e.symm (convolutionMatrix f)

omit [Fintype G] [Field F] in
@[simp]
theorem reindexedConvolutionMatrix_apply
    (e : Fin (n + 1) ≃ G) (f : G → F)
    (i j : Fin (n + 1)) :
    reindexedConvolutionMatrix e f i j =
      f (e i * (e j)⁻¹) := by
  simp [reindexedConvolutionMatrix, Matrix.reindex_apply,
    convolutionMatrix]

/-- Subtract the identity-indexed row from all other rows. -/
def augmentationDifferenceMatrix
    (e : Fin (n + 1) ≃ G) (f : G → F) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
  rowSubtractPivotTransform (F := F) (e.symm 1) *
    reindexedConvolutionMatrix e f

omit [Fintype G] in
theorem augmentationDifferenceMatrix_apply
    (e : Fin (n + 1) ≃ G) (f : G → F)
    (i j : Fin (n + 1)) :
    augmentationDifferenceMatrix e f i j =
      if i = e.symm 1 then f ((e j)⁻¹)
      else f (e i * (e j)⁻¹) - f ((e j)⁻¹) := by
  rw [augmentationDifferenceMatrix,
    rowSubtractPivotTransform_mul_apply]
  by_cases hi : i = e.symm 1
  · subst i
    simp
  · simp [hi]

theorem augmentationDifferenceMatrix_det
    (e : Fin (n + 1) ≃ G) (f : G → F) :
    (augmentationDifferenceMatrix e f).det =
      (convolutionMatrix f).det := by
  rw [augmentationDifferenceMatrix, Matrix.det_mul,
    rowSubtractPivotTransform_det, one_mul,
    reindexedConvolutionMatrix, Matrix.det_reindex_self]

theorem augmentationDifferenceMatrix_row_sum_eq_zero
    (e : Fin (n + 1) ≃ G) (f : G → F)
    (i : Fin (n + 1)) (hi : i ≠ e.symm 1) :
    ∑ j, augmentationDifferenceMatrix e f i j = 0 := by
  simp_rw [augmentationDifferenceMatrix_apply, if_neg hi]
  rw [Finset.sum_sub_distrib]
  have hsum :
      (∑ j : Fin (n + 1), f (e i * (e j)⁻¹)) =
        ∑ j : Fin (n + 1), f ((e j)⁻¹) := by
    let leftIndex : Fin (n + 1) ≃ G :=
      e.trans ((Equiv.inv G).trans (Equiv.mulLeft (e i)))
    let inverseIndex : Fin (n + 1) ≃ G :=
      e.trans (Equiv.inv G)
    calc
      (∑ j : Fin (n + 1), f (e i * (e j)⁻¹)) =
          ∑ j : Fin (n + 1), f (leftIndex j) := by rfl
      _ = ∑ g : G, f g := Equiv.sum_comp leftIndex f
      _ = ∑ j : Fin (n + 1), f (inverseIndex j) :=
        (Equiv.sum_comp inverseIndex f).symm
      _ = ∑ j : Fin (n + 1), f ((e j)⁻¹) := by rfl
  rw [hsum, sub_self]

theorem augmentationDifferenceMatrix_pivot_row_sum
    (e : Fin (n + 1) ≃ G) (f : G → F) :
    ∑ j, augmentationDifferenceMatrix e f (e.symm 1) j =
      ∑ g : G, f g := by
  simp_rw [augmentationDifferenceMatrix_apply]
  let inverseIndex : Fin (n + 1) ≃ G :=
    e.trans (Equiv.inv G)
  calc
    (∑ j : Fin (n + 1), f ((e j)⁻¹)) =
        ∑ j : Fin (n + 1), f (inverseIndex j) := by rfl
    _ = ∑ g : G, f g := Equiv.sum_comp inverseIndex f

/-- The cofactor identity over an arbitrary field. -/
theorem det_convolutionMatrix_eq_augmentation_mul_cofactor
    (e : Fin (n + 1) ≃ G) (f : G → F)
    (j₀ : Fin (n + 1)) :
    (convolutionMatrix f).det =
      (-1 : F) ^ ((e.symm 1).val + j₀.val) *
        (∑ g : G, f g) *
        ((augmentationDifferenceMatrix e f).submatrix
          (Fin.succAbove (e.symm 1))
          (Fin.succAbove j₀)).det := by
  rw [← augmentationDifferenceMatrix_det e f]
  have hdet :=
    Matrix.det_eq_sum_row_mul_submatrix_succAbove_succAbove_det
      (augmentationDifferenceMatrix e f) (e.symm 1) j₀
      (augmentationDifferenceMatrix_row_sum_eq_zero e f)
  rw [augmentationDifferenceMatrix_pivot_row_sum] at hdet
  simpa using hdet

/-- An inverse convolution kernel makes every augmentation cofactor
nonsingular. -/
theorem augmentationCofactor_det_ne_zero_of_inverseKernel
    (e : Fin (n + 1) ≃ G) {f g : G → F}
    (hinverse : ∀ x, convolution f g x = deltaKernel x)
    (j₀ : Fin (n + 1)) :
    ((augmentationDifferenceMatrix e f).submatrix
      (Fin.succAbove (e.symm 1))
      (Fin.succAbove j₀)).det ≠ 0 := by
  have hfull :=
    convolutionMatrix_det_ne_zero_of_inverseKernel hinverse
  intro hzero
  apply hfull
  rw [det_convolutionMatrix_eq_augmentation_mul_cofactor
    e f j₀, hzero, mul_zero]

/-! ## Standard real-residue alignment -/

open Fermat.Irregular.CyclotomicCharactersPrime
open Fermat.Irregular.CyclotomicLogDetPrime

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 < p)]

local notation3 "r" => (p - 3) / 2
local notation3 "N" => r + 1

/-- Inversion transported to the standard enumeration of the real residue
group. -/
def inverseIndex : Equiv.Perm (Fin N) :=
  ((standardRealResiduesEquiv (p := p)).trans
    (Equiv.inv (RealResidueGroup p))).trans
      (standardRealResiduesEquiv (p := p)).symm

@[simp]
theorem standardRealResiduesEquiv_inverseIndex (j : Fin N) :
    standardRealResiduesEquiv (p := p) (inverseIndex (p := p) j) =
      (standardRealResiduesEquiv (p := p) j)⁻¹ := by
  simp [inverseIndex]

/-- The cofactor column omitted by the circular-unit embedding order. -/
def omittedInverseIndex : Fin N :=
  inverseIndex (p := p) (Fin.last r)

def inverseColumnsEquiv :
    Fin r ≃ {j : Fin N // j ≠ omittedInverseIndex (p := p)} :=
  (finSuccAboveEquiv (Fin.last r)).trans
    (Equiv.subtypeEquiv (inverseIndex (p := p)) fun j ↦ by
      change j ≠ Fin.last r ↔
        inverseIndex (p := p) j ≠
          inverseIndex (p := p) (Fin.last r)
      exact ((inverseIndex (p := p)).injective.ne_iff).symm)

theorem inverseColumnsEquiv_apply (j : Fin r) :
    (inverseColumnsEquiv (p := p) j).val =
      inverseIndex (p := p) j.castSucc := by
  simp [inverseColumnsEquiv, finSuccAboveEquiv_apply]

def inverseColumnReindex : Equiv.Perm (Fin r) :=
  (inverseColumnsEquiv (p := p)).trans
    (finSuccAboveEquiv (omittedInverseIndex (p := p))).symm

theorem succAbove_inverseColumnReindex_apply (j : Fin r) :
    Fin.succAbove (omittedInverseIndex (p := p))
        (inverseColumnReindex (p := p) j) =
      inverseIndex (p := p) j.castSucc := by
  calc
    Fin.succAbove (omittedInverseIndex (p := p))
        (inverseColumnReindex (p := p) j) =
      ((finSuccAboveEquiv (omittedInverseIndex (p := p)))
        (inverseColumnReindex (p := p) j)).val := rfl
    _ = (inverseColumnsEquiv (p := p) j).val := by
      simp [inverseColumnReindex]
    _ = inverseIndex (p := p) j.castSucc :=
      inverseColumnsEquiv_apply (p := p) j

/-- The arbitrary-column augmentation cofactor used by the circular-unit
row/column convention. -/
def realResidueCofactor (f : RealResidueGroup p → F) :
    Matrix (Fin r) (Fin r) F :=
  (augmentationDifferenceMatrix
    (standardRealResiduesEquiv (p := p)) f).submatrix
      (Fin.succAbove 0)
      (Fin.succAbove (omittedInverseIndex (p := p)))

/-- Reindex the cofactor columns by inverses, matching the embedding
indices `1, ..., (p-3)/2`. -/
def inverseAlignedRealResidueCofactor
    (f : RealResidueGroup p → F) :
    Matrix (Fin r) (Fin r) F :=
  (realResidueCofactor f).submatrix id
    (inverseColumnReindex (p := p))

theorem inverseAlignedRealResidueCofactor_apply
    (f : RealResidueGroup p → F) (i j : Fin r) :
    inverseAlignedRealResidueCofactor f i j =
      f (standardRealResiduesEquiv (p := p) i.succ *
          standardRealResiduesEquiv (p := p) j.castSucc) -
        f (standardRealResiduesEquiv (p := p) j.castSucc) := by
  rw [inverseAlignedRealResidueCofactor, realResidueCofactor]
  simp only [Matrix.submatrix_apply, id_eq]
  rw [succAbove_inverseColumnReindex_apply]
  rw [augmentationDifferenceMatrix_apply]
  rw [standardRealResiduesEquiv_symm_one]
  simp only [Fin.succAbove_zero, if_neg (Fin.succ_ne_zero i)]
  rw [standardRealResiduesEquiv_inverseIndex]
  simp only [inv_inv]

/-- A compact inverse-kernel certificate proves the determinant required
by the transposed circular-unit evaluation matrix. -/
theorem transpose_inverseAlignedRealResidueCofactor_det_ne_zero
    {f g : RealResidueGroup p → F}
    (hinverse : ∀ x, convolution f g x = deltaKernel x) :
    (Matrix.transpose (inverseAlignedRealResidueCofactor f)).det ≠ 0 := by
  rw [Matrix.det_transpose]
  have hcofactor :=
    augmentationCofactor_det_ne_zero_of_inverseKernel
      (standardRealResiduesEquiv (p := p)) hinverse
      (omittedInverseIndex (p := p))
  have hcofactor' : (realResidueCofactor f).det ≠ 0 := by
    simpa [realResidueCofactor,
      standardRealResiduesEquiv_symm_one] using hcofactor
  have hsign :
      ((↑(↑(Equiv.Perm.sign
        (inverseColumnReindex (p := p))) : ℤ) : F)) ≠ 0 := by
    rcases Int.units_eq_one_or
      (Equiv.Perm.sign (inverseColumnReindex (p := p))) with hs | hs
    · rw [hs]
      norm_num
    · rw [hs]
      norm_num
  rw [inverseAlignedRealResidueCofactor, Matrix.det_permute']
  exact mul_ne_zero hsign hcofactor'

end

end Fermat.Irregular.FiniteCyclicCofactor
