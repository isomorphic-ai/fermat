import Fermat.Irregular.CyclotomicPlaces37
import Mathlib.GroupTheory.FiniteAbelian.Duality
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
