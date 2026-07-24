import Fermat.Irregular.CyclotomicPlaces37
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Finite abelian group determinants and the exponent-37 logarithm matrix

This file supplies the Fourier-algebra layer needed to factor the fixed cyclotomic logarithm
determinant.  For a finite commutative group `G`, its complex-valued characters form another
group of the same cardinality.  The character table diagonalizes every convolution matrix;
consequently the group determinant is the product of the corresponding character sums.

The construction is independent of a cyclic generator and is therefore suited to the real
cyclotomic group `(Z/37Z)^× / {±1}`.  Connecting the fixed sine matrix to the appropriate
augmentation cofactor is the remaining finite reindexing step.
-/

namespace Fermat.Irregular.CyclotomicLogDet

noncomputable section

open scoped Classical BigOperators

variable {G : Type*} [CommGroup G] [Fintype G]

local instance : Fintype (G →* ℂˣ) := Fintype.ofFinite _

/-- A fixed enumeration of all complex characters of a finite commutative group. -/
def characterEquiv : G ≃ (G →* ℂˣ) :=
  (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G ℂ).some.symm.toEquiv

/-- The character table, with group elements indexing rows and characters indexing columns. -/
def characterMatrix : Matrix G G ℂ :=
  Matrix.of fun g i ↦ (characterEquiv i g : ℂ)

/-- The unnormalized inverse character table. -/
def inverseCharacterMatrix : Matrix G G ℂ :=
  Matrix.of fun i g ↦ ((characterEquiv i g : ℂˣ) : ℂ)⁻¹

/-- A nontrivial complex character sums to zero on a finite group. -/
theorem sum_character_eq_zero {χ : G →* ℂˣ} (hχ : χ ≠ 1) :
    ∑ g : G, (χ g : ℂ) = 0 := by
  rw [ne_eq, MonoidHom.ext_iff] at hχ
  push Not at hχ
  obtain ⟨b, hb⟩ := hχ
  have hb' : (χ b : ℂ) ≠ 1 := by
    exact fun h ↦ hb (Units.val_eq_one.mp h)
  refine eq_zero_of_mul_eq_self_left hb' ?_
  rw [Finset.mul_sum]
  calc
    ∑ g : G, (χ b : ℂ) * (χ g : ℂ) = ∑ g : G, (χ (b * g) : ℂ) := by
      apply Finset.sum_congr rfl
      intro g _
      simp
    _ = ∑ g : G, (χ g : ℂ) := by
      exact Equiv.sum_comp (Equiv.mulLeft b) (fun g : G ↦ (χ g : ℂ))

/-- Orthogonality of two columns of the character table. -/
theorem sum_inv_character_mul_character (i j : G) :
    ∑ g : G, ((characterEquiv i g : ℂˣ) : ℂ)⁻¹ * (characterEquiv j g : ℂ) =
      if i = j then Fintype.card G else 0 := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    simp
  · rw [if_neg hij]
    let χ : G →* ℂˣ := (characterEquiv i)⁻¹ * characterEquiv j
    have hχ : χ ≠ 1 := by
      intro h
      apply hij
      apply characterEquiv.injective
      exact inv_mul_eq_one.mp h
    calc
      ∑ g : G, ((characterEquiv i g : ℂˣ) : ℂ)⁻¹ * (characterEquiv j g : ℂ) =
          ∑ g : G, (χ g : ℂ) := by
        apply Finset.sum_congr rfl
        intro g _
        simp [χ, Units.val_inv_eq_inv_val]
      _ = 0 := sum_character_eq_zero hχ
    norm_num

/-- The inverse character table times the character table is the group order times identity. -/
theorem inverseCharacterMatrix_mul_characterMatrix :
    inverseCharacterMatrix * characterMatrix =
      (Fintype.card G : ℂ) • (1 : Matrix G G ℂ) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [inverseCharacterMatrix, characterMatrix, Matrix.of_apply]
  rw [sum_inv_character_mul_character]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

/-- The complex character table of a finite commutative group is nonsingular. -/
theorem characterMatrix_det_ne_zero : (characterMatrix (G := G)).det ≠ 0 := by
  intro hzero
  have hdet := congrArg Matrix.det
    (inverseCharacterMatrix_mul_characterMatrix (G := G))
  rw [Matrix.det_mul, hzero, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at hdet
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact (pow_ne_zero _ hcard) hdet.symm

/-- The convolution matrix associated to `f`, with the right-regular convention. -/
def convolutionMatrix (f : G → ℂ) : Matrix G G ℂ :=
  Matrix.of fun x y ↦ f (x * y⁻¹)

/-- The Fourier eigenvalue of a convolution kernel at a character. -/
def characterEigenvalue (f : G → ℂ) (i : G) : ℂ :=
  ∑ t : G, f t * ((characterEquiv i t : ℂˣ) : ℂ)⁻¹

/-- The character table diagonalizes every convolution matrix. -/
theorem convolutionMatrix_mul_characterMatrix (f : G → ℂ) :
    convolutionMatrix f * characterMatrix =
      characterMatrix * Matrix.diagonal (characterEigenvalue f) := by
  ext x i
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  simp only [convolutionMatrix, characterMatrix, Matrix.of_apply, characterEigenvalue]
  let e : G ≃ G := (Equiv.inv G).trans (Equiv.mulLeft x)
  calc
    ∑ y : G, f (x * y⁻¹) * (characterEquiv i y : ℂ) =
        ∑ t : G, (f t * ((characterEquiv i t : ℂˣ) : ℂ)⁻¹) *
          (characterEquiv i x : ℂ) := by
      apply Fintype.sum_equiv e
      intro y
      change f (x * y⁻¹) * (characterEquiv i y : ℂ) =
        (f (e y) * ((characterEquiv i (e y) : ℂˣ) : ℂ)⁻¹) *
          (characterEquiv i x : ℂ)
      have he : e y = x * y⁻¹ := by rfl
      rw [he]
      have hchar : (characterEquiv i (x * y⁻¹))⁻¹ * characterEquiv i x =
          characterEquiv i y := by
        rw [map_mul, map_inv]
        group
      rw [mul_assoc]
      congr 1
      simpa only [Units.val_mul, Units.val_inv_eq_inv_val] using congrArg Units.val hchar.symm
    _ = (∑ t : G, f t * ((characterEquiv i t : ℂˣ) : ℂ)⁻¹) *
        (characterEquiv i x : ℂ) := by
      rw [Finset.sum_mul]
    _ = (characterEquiv i x : ℂ) *
        ∑ t : G, f t * ((characterEquiv i t : ℂˣ) : ℂ)⁻¹ := by
      rw [mul_comm]

/-- The finite Fourier coefficient of `f` at a complex character. -/
def fourierCoefficient (f : G → ℂ) (χ : G →* ℂˣ) : ℂ :=
  ∑ t : G, f t * ((χ t : ℂˣ) : ℂ)⁻¹

@[simp]
theorem fourierCoefficient_one (f : G → ℂ) :
    fourierCoefficient f (1 : G →* ℂˣ) = ∑ t : G, f t := by
  simp [fourierCoefficient]

@[simp]
theorem characterEigenvalue_eq_fourierCoefficient (f : G → ℂ) (i : G) :
    characterEigenvalue f i = fourierCoefficient f (characterEquiv i) := rfl

/-- The group determinant formula: a finite abelian convolution determinant is the product of
the eigenvalues indexed by the chosen enumeration of characters. -/
theorem det_convolutionMatrix_eq_prod_characterEigenvalue (f : G → ℂ) :
    (convolutionMatrix f).det = ∏ i : G, characterEigenvalue f i := by
  have hdet := congrArg Matrix.det (convolutionMatrix_mul_characterMatrix f)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hdet
  have hchar := characterMatrix_det_ne_zero (G := G)
  apply mul_right_cancel₀ hchar
  rw [hdet, mul_comm]

/-- The group determinant formula: a finite abelian convolution determinant is the product of
all of its character sums. -/
theorem det_convolutionMatrix_eq_prod_fourierCoefficient (f : G → ℂ) :
    (convolutionMatrix f).det =
      ∏ χ : G →* ℂˣ, fourierCoefficient f χ := by
  rw [det_convolutionMatrix_eq_prod_characterEigenvalue]
  exact Equiv.prod_comp characterEquiv (fourierCoefficient f)

/-! ## The augmentation cofactor -/

variable {n : ℕ}

/-- The row-operation matrix which fixes row `i₀` and subtracts row `i₀` from every other
row.  It is a rank-one perturbation of the identity. -/
def rowSubtractPivotTransform (i₀ : Fin (n + 1)) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  1 + Matrix.replicateCol (Fin 1) (fun i ↦ if i = i₀ then (0 : ℂ) else -1) *
    Matrix.replicateRow (Fin 1) (fun j ↦ if j = i₀ then (1 : ℂ) else 0)

theorem rowSubtractPivotTransform_det (i₀ : Fin (n + 1)) :
    (rowSubtractPivotTransform i₀).det = 1 := by
  let u : Fin (n + 1) → ℂ := fun i ↦ if i = i₀ then 0 else -1
  let v : Fin (n + 1) → ℂ := fun j ↦ if j = i₀ then 1 else 0
  have hd : v ⬝ᵥ u = 0 := by
    rw [dotProduct]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i = i₀ <;> simp [u, v, hi]
  change (1 + Matrix.replicateCol (Fin 1) u * Matrix.replicateRow (Fin 1) v).det = 1
  calc
    _ = 1 + v ⬝ᵥ u :=
      Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) u v
    _ = 1 := by rw [hd, add_zero]

@[simp]
theorem rowSubtractPivotTransform_apply (i₀ i j : Fin (n + 1)) :
    rowSubtractPivotTransform i₀ i j =
      (if i = j then 1 else 0) +
        (if i = i₀ then 0 else -1) * (if j = i₀ then 1 else 0) := by
  simp [rowSubtractPivotTransform, Matrix.add_apply, Matrix.one_apply,
    Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply]

/-- Multiplying by `rowSubtractPivotTransform` performs the advertised simultaneous row
subtractions. -/
theorem rowSubtractPivotTransform_mul_apply
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i₀ i j : Fin (n + 1)) :
    (rowSubtractPivotTransform i₀ * A) i j =
      if i = i₀ then A i j else A i j - A i₀ j := by
  rw [Matrix.mul_apply]
  simp_rw [rowSubtractPivotTransform_apply]
  by_cases hi : i = i₀
  · subst i
    simp
  · simp [hi, Finset.sum_add_distrib, sub_eq_add_neg, add_mul]

/-- A convolution matrix in an arbitrary enumeration by `Fin (n + 1)`. -/
def reindexedConvolutionMatrix (e : Fin (n + 1) ≃ G) (f : G → ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.reindex e.symm e.symm (convolutionMatrix f)

omit [Fintype G] in
@[simp]
theorem reindexedConvolutionMatrix_apply (e : Fin (n + 1) ≃ G) (f : G → ℂ)
    (i j : Fin (n + 1)) :
    reindexedConvolutionMatrix e f i j = f (e i * (e j)⁻¹) := by
  simp [reindexedConvolutionMatrix, Matrix.reindex_apply, convolutionMatrix]

/-- Subtract the identity-indexed row of a reindexed convolution matrix from all its other
rows.  This is the augmentation matrix whose complementary minor is the regulator-type
determinant. -/
def augmentationDifferenceMatrix (e : Fin (n + 1) ≃ G) (f : G → ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  rowSubtractPivotTransform (e.symm 1) * reindexedConvolutionMatrix e f

omit [Fintype G] in
theorem augmentationDifferenceMatrix_apply (e : Fin (n + 1) ≃ G) (f : G → ℂ)
    (i j : Fin (n + 1)) :
    augmentationDifferenceMatrix e f i j =
      if i = e.symm 1 then f ((e j)⁻¹) else f (e i * (e j)⁻¹) - f ((e j)⁻¹) := by
  rw [augmentationDifferenceMatrix, rowSubtractPivotTransform_mul_apply]
  by_cases hi : i = e.symm 1
  · subst i
    simp
  · simp [hi]

/-- The simultaneous row subtractions do not change the convolution determinant. -/
theorem augmentationDifferenceMatrix_det (e : Fin (n + 1) ≃ G) (f : G → ℂ) :
    (augmentationDifferenceMatrix e f).det = (convolutionMatrix f).det := by
  rw [augmentationDifferenceMatrix, Matrix.det_mul, rowSubtractPivotTransform_det, one_mul,
    reindexedConvolutionMatrix, Matrix.det_reindex_self]

/-- Every nonidentity row of the augmentation matrix has sum zero. -/
theorem augmentationDifferenceMatrix_row_sum_eq_zero
    (e : Fin (n + 1) ≃ G) (f : G → ℂ) (i : Fin (n + 1))
    (hi : i ≠ e.symm 1) :
    ∑ j, augmentationDifferenceMatrix e f i j = 0 := by
  simp_rw [augmentationDifferenceMatrix_apply, if_neg hi]
  rw [Finset.sum_sub_distrib]
  have hsum :
      (∑ j : Fin (n + 1), f (e i * (e j)⁻¹)) =
        ∑ j : Fin (n + 1), f ((e j)⁻¹) := by
    let leftIndex : Fin (n + 1) ≃ G :=
      e.trans ((Equiv.inv G).trans (Equiv.mulLeft (e i)))
    let inverseIndex : Fin (n + 1) ≃ G := e.trans (Equiv.inv G)
    calc
      (∑ j : Fin (n + 1), f (e i * (e j)⁻¹)) =
          ∑ j : Fin (n + 1), f (leftIndex j) := by rfl
      _ = ∑ g : G, f g := Equiv.sum_comp leftIndex f
      _ = ∑ j : Fin (n + 1), f (inverseIndex j) :=
        (Equiv.sum_comp inverseIndex f).symm
      _ = ∑ j : Fin (n + 1), f ((e j)⁻¹) := by rfl
  rw [hsum, sub_self]

/-- The distinguished row sum is the augmentation (the trivial-character Fourier
coefficient) of the kernel. -/
theorem augmentationDifferenceMatrix_pivot_row_sum
    (e : Fin (n + 1) ≃ G) (f : G → ℂ) :
    ∑ j, augmentationDifferenceMatrix e f (e.symm 1) j = ∑ g : G, f g := by
  simp_rw [augmentationDifferenceMatrix_apply]
  let inverseIndex : Fin (n + 1) ≃ G := e.trans (Equiv.inv G)
  calc
    (∑ j : Fin (n + 1), f ((e j)⁻¹)) =
        ∑ j : Fin (n + 1), f (inverseIndex j) := by rfl
    _ = ∑ g : G, f g := Equiv.sum_comp inverseIndex f

/-- Augmentation-cofactor formula for a finite abelian group determinant.  After subtracting
the identity row from all other rows, deleting that row and any chosen column extracts the
trivial Fourier factor, up to the explicit cofactor sign. -/
theorem det_convolutionMatrix_eq_augmentation_mul_cofactor
    (e : Fin (n + 1) ≃ G) (f : G → ℂ) (j₀ : Fin (n + 1)) :
    (convolutionMatrix f).det =
      (-1 : ℂ) ^ ((e.symm 1).val + j₀.val) * (∑ g : G, f g) *
        ((augmentationDifferenceMatrix e f).submatrix
          (Fin.succAbove (e.symm 1)) (Fin.succAbove j₀)).det := by
  rw [← augmentationDifferenceMatrix_det e f]
  have hdet := Matrix.det_eq_sum_row_mul_submatrix_succAbove_succAbove_det
    (augmentationDifferenceMatrix e f) (e.symm 1) j₀
    (augmentationDifferenceMatrix_row_sum_eq_zero e f)
  rw [augmentationDifferenceMatrix_pivot_row_sum] at hdet
  simpa using hdet

/-- Choosing the identity-indexed column makes the cofactor sign positive. -/
theorem det_convolutionMatrix_eq_augmentation_mul_principalCofactor
    (e : Fin (n + 1) ≃ G) (f : G → ℂ) :
    (convolutionMatrix f).det = (∑ g : G, f g) *
      ((augmentationDifferenceMatrix e f).submatrix
        (Fin.succAbove (e.symm 1)) (Fin.succAbove (e.symm 1))).det := by
  simpa [← two_mul, pow_mul] using
    (det_convolutionMatrix_eq_augmentation_mul_cofactor e f (e.symm 1))

/-- Fourier form of the augmentation-cofactor formula.  This is the exact algebraic bridge
between the product over all characters and a regulator-type complementary minor. -/
theorem prod_fourierCoefficient_eq_augmentation_mul_cofactor
    (e : Fin (n + 1) ≃ G) (f : G → ℂ) (j₀ : Fin (n + 1)) :
    (∏ χ : G →* ℂˣ, fourierCoefficient f χ) =
      (-1 : ℂ) ^ ((e.symm 1).val + j₀.val) * (∑ g : G, f g) *
        ((augmentationDifferenceMatrix e f).submatrix
          (Fin.succAbove (e.symm 1)) (Fin.succAbove j₀)).det := by
  rw [← det_convolutionMatrix_eq_prod_fourierCoefficient]
  exact det_convolutionMatrix_eq_augmentation_mul_cofactor e f j₀

/-- The principal augmentation cofactor is the product of the nontrivial Fourier factors,
provided the trivial factor is nonzero. -/
theorem augmentation_principalCofactor_det_eq_prod_nontrivial_fourierCoefficient
    (e : Fin (n + 1) ≃ G) (f : G → ℂ) (haugmentation : (∑ g : G, f g) ≠ 0) :
    ((augmentationDifferenceMatrix e f).submatrix
        (Fin.succAbove (e.symm 1)) (Fin.succAbove (e.symm 1))).det =
      ∏ χ : {χ : G →* ℂˣ // χ ≠ 1}, fourierCoefficient f χ := by
  apply mul_left_cancel₀ haugmentation
  rw [← det_convolutionMatrix_eq_augmentation_mul_principalCofactor e f,
    det_convolutionMatrix_eq_prod_fourierCoefficient,
    Fintype.prod_eq_mul_prod_subtype_ne, fourierCoefficient_one]

/-! ## The real residue group at 37 -/

/-- The subgroup `{1, -1}` of `(Z/37Z)^×`. -/
def signSubgroup37 : Subgroup (ZMod 37)ˣ :=
  Subgroup.zpowers (-1)

/-- The Galois group of the maximal real subfield of the `37`th cyclotomic field. -/
abbrev RealResidueGroup37 := (ZMod 37)ˣ ⧸ signSubgroup37

/-- The real residue group has order eighteen. -/
theorem card_realResidueGroup37 : Fintype.card RealResidueGroup37 = 18 := by
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup signSubgroup37
  have hunits : Nat.card (ZMod 37)ˣ = 36 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    decide
  have hsign : Nat.card signSubgroup37 = 2 := by
    rw [Nat.card_eq_fintype_card, signSubgroup37, Fintype.card_zpowers]
    apply orderOf_eq_prime
    · norm_num
    · intro h
      have hval := congrArg Units.val h
      exact (by decide : (-1 : ZMod 37) ≠ 1) hval
  rw [hunits, hsign] at hcard
  have hfinite : Nat.card RealResidueGroup37 = Fintype.card RealResidueGroup37 :=
    Nat.card_eq_fintype_card
  change Nat.card ((ZMod 37)ˣ ⧸ signSubgroup37) =
    Fintype.card RealResidueGroup37 at hfinite
  rw [hfinite] at hcard
  omega

/-- The unit represented by the integer `j + 1`, for `j = 0, ..., 17`. -/
def standardUnit37 (j : Fin 18) : (ZMod 37)ˣ :=
  ZMod.unitOfCoprime (j.val + 1) (by
    apply Nat.Coprime.symm
    exact (by decide : Nat.Prime 37).coprime_iff_not_dvd.mpr (by omega))

/-- The real residue class represented by `j + 1`, for `j = 0, ..., 17`. -/
def standardRealResidue37 (j : Fin 18) : RealResidueGroup37 :=
  QuotientGroup.mk (standardUnit37 j)

/-- Membership in the sign subgroup means equality to one of its two elements. -/
theorem signSubgroup37_mem_iff (u : (ZMod 37)ˣ) :
    u ∈ signSubgroup37 ↔ u = 1 ∨ u = -1 := by
  constructor
  · intro hu
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [neg_one_zpow_eq_ite] at hk
    by_cases heven : Even k
    · left
      simpa [heven] using hk.symm
    · right
      simpa [heven] using hk.symm
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers (-1)

/-- Distinct integers in `1, ..., 18` remain distinct modulo the sign relation. -/
theorem standardRealResidue37_injective : Function.Injective standardRealResidue37 := by
  intro i j hij
  rw [standardRealResidue37, standardRealResidue37,
    QuotientGroup.eq_iff_div_mem, signSubgroup37_mem_iff] at hij
  rcases hij with hdiv | hdiv
  · have hu : standardUnit37 i = standardUnit37 j := div_eq_one.mp hdiv
    have hz : (i.val + 1 : ZMod 37) = (j.val + 1 : ZMod 37) := by
      simpa [standardUnit37] using congrArg Units.val hu
    have hz' : ((i.val + 1 : ℕ) : ZMod 37) = ((j.val + 1 : ℕ) : ZMod 37) := by
      push_cast
      exact hz
    rw [ZMod.natCast_eq_natCast_iff] at hz'
    apply Fin.ext
    have heq := Nat.ModEq.eq_of_lt_of_lt hz' (by omega) (by omega)
    omega
  · have hu : standardUnit37 i = -(standardUnit37 j) := by
      calc
        standardUnit37 i = (standardUnit37 i / standardUnit37 j) * standardUnit37 j :=
          (div_mul_cancel _ _).symm
        _ = (-1) * standardUnit37 j := by rw [hdiv]
        _ = -(standardUnit37 j) := neg_one_mul _
    have hz : (i.val + 1 : ZMod 37) = -(j.val + 1 : ZMod 37) := by
      simpa [standardUnit37] using congrArg Units.val hu
    have hzsum : (i.val + 1 + (j.val + 1) : ZMod 37) = 0 := by
      rw [hz]
      ring
    have hzsum' : ((i.val + 1 + (j.val + 1) : ℕ) : ZMod 37) = 0 := by
      push_cast
      exact hzsum
    have hdvd : 37 ∣ i.val + 1 + (j.val + 1) :=
      (ZMod.natCast_eq_zero_iff _ _).mp hzsum'
    have hlt : i.val + 1 + (j.val + 1) < 37 := by omega
    exfalso
    exact (Nat.not_dvd_of_pos_of_lt (by omega) hlt) hdvd

/-- The standard representatives `1, ..., 18` enumerate the real residue group. -/
def standardRealResiduesEquiv37 : Fin 18 ≃ RealResidueGroup37 :=
  Equiv.ofBijective standardRealResidue37
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨standardRealResidue37_injective, by
        rw [Fintype.card_fin, card_realResidueGroup37]⟩)

@[simp]
theorem standardRealResiduesEquiv37_apply (j : Fin 18) :
    standardRealResiduesEquiv37 j = standardRealResidue37 j := rfl

@[simp]
theorem standardRealResidue37_zero : standardRealResidue37 0 = 1 := by
  rw [standardRealResidue37, QuotientGroup.eq_one_iff]
  have hu : standardUnit37 0 = 1 := by
    apply Units.ext
    simp [standardUnit37]
  rw [hu]
  exact Subgroup.one_mem _

@[simp]
theorem standardRealResiduesEquiv37_symm_one : standardRealResiduesEquiv37.symm 1 = 0 := by
  rw [← standardRealResidue37_zero, ← standardRealResiduesEquiv37_apply]
  exact standardRealResiduesEquiv37.symm_apply_apply 0

/-! ## Normalizing the fixed sine determinant -/

open Fermat.Irregular.CyclotomicPlaces37
open Fermat.Irregular.CyclotomicZeta

/-- The fixed sine matrix with the common archimedean multiplicity `2` removed and the logarithm
of the quotient expanded as a difference. -/
def logSineDifferenceMatrix37 : Matrix (Fin 17) (Fin 17) ℝ :=
  Matrix.of fun i j ↦
    Real.log |Real.sin (Real.pi * (((i.val + 2 : ℕ) : ℝ) *
        ((j.val + 1 : ℕ) : ℝ) / (37 : ℝ)))| -
      Real.log |Real.sin (Real.pi * (((j.val + 1 : ℕ) : ℝ) / (37 : ℝ)))|

/-- A rational multiple `pi * m / 37` has nonzero sine when `37` does not divide `m`. -/
theorem sin_pi_mul_div_37_ne_zero (m : ℕ) (hm : ¬37 ∣ m) :
    Real.sin (Real.pi * ((m : ℝ) / (37 : ℝ))) ≠ 0 := by
  intro hsin
  have hnorm : ‖1 - eta37 ^ m‖ =
      2 * |Real.sin (Real.pi * ((m : ℝ) / (37 : ℝ)))| := by
    simpa [eta37] using norm_one_sub_exp_two_pi_I_pow 1 m 37
  have hzero : ‖1 - eta37 ^ m‖ = 0 := by
    rw [hnorm, hsin]
    norm_num
  have hpow : eta37 ^ m = 1 := by
    exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm
  exact hm (eta37_primitive.dvd_of_pow_eq_one m hpow)

/-- The fixed regulator matrix is twice the logarithmic-difference matrix. -/
theorem explicitSineMatrix37_eq_two_smul_logSineDifference :
    explicitSineMatrix37 = (2 : ℝ) • logSineDifferenceMatrix37 := by
  ext i j
  let a := i.val + 2
  let k := j.val + 1
  have ha : ¬37 ∣ a := by
    intro h
    have hle := Nat.le_of_dvd (by omega : 0 < a) h
    omega
  have hk : ¬37 ∣ k := by
    intro h
    have hle := Nat.le_of_dvd (by omega : 0 < k) h
    omega
  have hak : ¬37 ∣ a * k := (by decide : Nat.Prime 37).not_dvd_mul ha hk
  have hnum :
      |Real.sin (Real.pi * ((a : ℝ) * (k : ℝ) / (37 : ℝ)))| ≠ 0 := by
    rw [abs_ne_zero]
    simpa [Nat.cast_mul] using sin_pi_mul_div_37_ne_zero (a * k) hak
  have hden : |Real.sin (Real.pi * ((k : ℝ) / (37 : ℝ)))| ≠ 0 := by
    rw [abs_ne_zero]
    exact sin_pi_mul_div_37_ne_zero k hk
  simp only [explicitSineMatrix37, logSineDifferenceMatrix37, Matrix.of_apply,
    Matrix.smul_apply, smul_eq_mul]
  change 2 * Real.log
      (|Real.sin (Real.pi * ((a : ℝ) * (k : ℝ) / (37 : ℝ)))| /
        |Real.sin (Real.pi * ((k : ℝ) / (37 : ℝ)))|) = _
  rw [Real.log_div hnum hden]

/-- Removing the common factor `2` from all seventeen rows extracts exactly `2^17` from the
fixed determinant. -/
theorem explicitSineMatrix37_det_eq_pow_mul_logDifferenceDet :
    explicitSineMatrix37.det =
      (2 : ℝ) ^ 17 * logSineDifferenceMatrix37.det := by
  rw [explicitSineMatrix37_eq_two_smul_logSineDifference, Matrix.det_smul]
  norm_num

end

end Fermat.Irregular.CyclotomicLogDet
