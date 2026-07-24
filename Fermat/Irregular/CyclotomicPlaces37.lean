import Fermat.Irregular.CyclotomicZeta

/-!
# Canonical infinite places and the fixed exponent-37 sine determinant

The preceding circular-regulator reduction still allows an arbitrary ordering of the infinite
places and an arbitrary representative complex embedding at each place.  Here those choices are
removed.

For a primitive `37`th root `zeta`, we construct the eighteen infinite places induced by the
embeddings

`zeta |-> exp (2 * pi * I / 37) ^ j`, for `1 <= j <= 18`.

They are pairwise distinct as infinite places: equality of two embeddings forces equal powers,
while equality up to complex conjugation would force `37` to divide a positive integer at most
`36`.  Since a `37`th cyclotomic field has exactly eighteen infinite places, these places exhaust
them.  Omitting `j = 18` and reindexing Mathlib's regulator determinant gives one completely
fixed `17 x 17` real matrix, independent of the ambient cyclotomic field and chosen primitive
root.
-/

open scoped NumberField Classical

namespace Fermat.Irregular.CyclotomicPlaces37

noncomputable section

open NumberField Polynomial
open Fermat.Irregular.CircularUnitIndex
open Fermat.Irregular.SinnottIndex
open Fermat.Irregular.CyclotomicZeta

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]

/-- The standard complex primitive `37`th root `exp (2 * pi * I / 37)`. -/
def eta37 : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (((1 : ℕ) : ℂ) / ((37 : ℕ) : ℂ)))

theorem eta37_primitive : IsPrimitiveRoot eta37 37 := by
  simpa [eta37, div_eq_mul_inv, mul_assoc] using
    Complex.isPrimitiveRoot_exp 37 (by norm_num)

/-- The primitive root `eta37 ^ (j + 1)`, for `j = 0, ..., 17`. -/
def root37 (j : Fin 18) : primitiveRoots 37 ℂ :=
  ⟨eta37 ^ (j.val + 1), (mem_primitiveRoots (by norm_num)).mpr
    (eta37_primitive.pow_of_coprime (j.val + 1) (by fin_cases j <;> decide))⟩

/-- The complex embedding that sends `zeta` to `eta37 ^ (j + 1)`. -/
def embedding37 {zeta : K} (hzeta : IsPrimitiveRoot zeta 37) (j : Fin 18) : K →ₐ[ℚ] ℂ :=
  (hzeta.embeddingsEquivPrimitiveRoots ℂ (cyclotomic.irreducible_rat (by norm_num))).symm
    (root37 j)

theorem embedding37_zeta {zeta : K} (hzeta : IsPrimitiveRoot zeta 37) (j : Fin 18) :
    embedding37 hzeta j zeta = eta37 ^ (j.val + 1) := by
  have h := congrArg Subtype.val
    ((hzeta.embeddingsEquivPrimitiveRoots ℂ
      (cyclotomic.irreducible_rat (by norm_num))).apply_symm_apply (root37 j))
  exact h

/-- The infinite place represented by `embedding37 hzeta j`. -/
def place37 {zeta : K} (hzeta : IsPrimitiveRoot zeta 37) (j : Fin 18) :
    NumberField.InfinitePlace K :=
  NumberField.InfinitePlace.mk (embedding37 hzeta j).toRingHom

/-- The first eighteen standard powers give pairwise distinct infinite places. -/
theorem place37_injective {zeta : K} (hzeta : IsPrimitiveRoot zeta 37) :
    Function.Injective (place37 hzeta) := by
  intro i j hij
  rw [place37, place37, NumberField.InfinitePlace.mk_eq_iff] at hij
  rcases hij with hij | hij
  · have hp : eta37 ^ (i.val + 1) = eta37 ^ (j.val + 1) := by
      rw [← embedding37_zeta hzeta i, ← embedding37_zeta hzeta j]
      exact DFunLike.congr_fun hij zeta
    apply Fin.ext
    have := eta37_primitive.pow_inj (by omega) (by omega) hp
    omega
  · have hp : (eta37 ^ (i.val + 1))⁻¹ = eta37 ^ (j.val + 1) := by
      rw [Complex.inv_eq_conj (by
        rw [norm_pow, Complex.norm_eq_one_of_pow_eq_one
          eta37_primitive.pow_eq_one (by norm_num), one_pow])]
      rw [← embedding37_zeta hzeta i, ← embedding37_zeta hzeta j]
      exact DFunLike.congr_fun hij zeta
    have hone : eta37 ^ ((i.val + 1) + (j.val + 1)) = 1 := by
      rw [pow_add, ← hp]
      exact mul_inv_cancel₀ (pow_ne_zero _ (eta37_primitive.ne_zero (by norm_num)))
    have hdiv := eta37_primitive.dvd_of_pow_eq_one _ hone
    omega

/-- A `37`th cyclotomic field has exactly eighteen infinite places. -/
theorem card_infinitePlace37 : Fintype.card (NumberField.InfinitePlace K) = 18 := by
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero K (n := 37) (by norm_num),
    IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two (K := K) 37]
  decide

/-- The standard powers `1, ..., 18` enumerate all infinite places. -/
def placesEquiv37 {zeta : K} (hzeta : IsPrimitiveRoot zeta 37) :
    Fin 18 ≃ NumberField.InfinitePlace K :=
  Equiv.ofBijective (place37 hzeta)
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨place37_injective hzeta, by
      rw [Fintype.card_fin, card_infinitePlace37]⟩)

@[simp]
theorem placesEquiv37_apply {zeta : K} (hzeta : IsPrimitiveRoot zeta 37)
    (j : Fin 18) : placesEquiv37 hzeta j = place37 hzeta j := rfl

/-- The distinguished place omitted from the regulator determinant, represented by
`eta37 ^ 18`. -/
def omittedPlace37 {zeta : K} (hzeta : IsPrimitiveRoot zeta 37) :
    NumberField.InfinitePlace K :=
  place37 hzeta (Fin.last 17)

/-- The remaining places, in the canonical order represented by `eta37 ^ 1, ..., eta37 ^ 17`. -/
def remainingPlacesEquiv37 {zeta : K} (hzeta : IsPrimitiveRoot zeta 37) :
    Fin 17 ≃ {w : NumberField.InfinitePlace K // w ≠ omittedPlace37 hzeta} :=
  (finSuccAboveEquiv (Fin.last 17)).trans
    (Equiv.subtypeEquiv (placesEquiv37 hzeta) fun j ↦ by
      change j ≠ Fin.last 17 ↔ place37 hzeta j ≠ place37 hzeta (Fin.last 17)
      simpa only [placesEquiv37_apply] using
        ((placesEquiv37 hzeta).injective.ne_iff).symm)

theorem remainingPlacesEquiv37_apply {zeta : K} (hzeta : IsPrimitiveRoot zeta 37)
    (j : Fin 17) :
    (remainingPlacesEquiv37 hzeta j).val = place37 hzeta j.castSucc := by
  simp [remainingPlacesEquiv37, finSuccAboveEquiv_apply]
  congr 1
  apply Fin.succAbove_of_castSucc_lt
  exact Fin.castSucc_lt_last _

/-- Evaluation of a circular unit at a standard infinite place, in exact sine form. -/
theorem place37_circularUnit37 {zeta : K} (hzeta : IsPrimitiveRoot zeta 37)
    (j : Fin 18) (i : Fin 17) :
    place37 hzeta j
        (((circularUnit37 hzeta i).val : NumberField.RingOfIntegers K) : K) =
      |Real.sin (Real.pi * (((i.val + 2 : ℕ) : ℝ) * ((j.val + 1 : ℕ) : ℝ) /
        ((37 : ℕ) : ℝ)))| /
      |Real.sin (Real.pi * (((j.val + 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)))| := by
  rw [place37, NumberField.InfinitePlace.apply]
  rw [circularUnit37_coe]
  simp only [map_mul, map_div₀, map_pow, map_sub, map_one, norm_mul, norm_div, norm_pow]
  simp only [AlgHom.toRingHom_eq_coe]
  change ‖embedding37 hzeta j zeta‖ ^ normalizationExponent37 i *
        ‖1 - embedding37 hzeta j zeta ^ (i.val + 2)‖ /
      ‖1 - embedding37 hzeta j zeta‖ = _
  rw [embedding37_zeta hzeta]
  have heta : ‖eta37‖ = 1 := Complex.norm_eq_one_of_pow_eq_one
    eta37_primitive.pow_eq_one (by norm_num)
  simp only [norm_pow, heta, one_pow, one_mul]
  rw [← pow_mul]
  change
    ‖1 - Complex.exp (2 * Real.pi * Complex.I *
        (((1 : ℕ) : ℂ) / ((37 : ℕ) : ℂ))) ^ ((j.val + 1) * (i.val + 2))‖ /
      ‖1 - Complex.exp (2 * Real.pi * Complex.I *
        (((1 : ℕ) : ℂ) / ((37 : ℕ) : ℂ))) ^ (j.val + 1)‖ = _
  rw [norm_one_sub_exp_two_pi_I_pow, norm_one_sub_exp_two_pi_I_pow]
  field_simp
  congr 2 <;> congr 1 <;> push_cast <;> ring

/-- The fixed `17 x 17` sine matrix for the exponent-`37` circular regulator.  Row `i`
corresponds to the circular unit with exponent `i + 2`; column `j` corresponds to the standard
infinite place represented by `eta37 ^ (j + 1)`. -/
def explicitSineMatrix37 : Matrix (Fin 17) (Fin 17) ℝ :=
  Matrix.of fun i j ↦
    2 * Real.log
      (|Real.sin (Real.pi * (((i.val + 2 : ℕ) : ℝ) * ((j.val + 1 : ℕ) : ℝ) /
          ((37 : ℕ) : ℝ)))| /
        |Real.sin (Real.pi * (((j.val + 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)))|)

/-- Reindexing the abstract circular logarithm matrix by the standard infinite places gives the
fixed numerical sine matrix. -/
theorem reindex_circularLogMatrix37 {zeta : K} (hzeta : IsPrimitiveRoot zeta 37) :
    Matrix.reindex (remainingPlacesEquiv37 hzeta).symm
        (remainingPlacesEquiv37 hzeta).symm
        (circularLogMatrix37 zeta (omittedPlace37 hzeta)
          (remainingPlacesEquiv37 hzeta).symm) =
      explicitSineMatrix37 := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, circularLogMatrix37,
    Matrix.of_apply, Equiv.symm_symm, Equiv.symm_apply_apply, explicitSineMatrix37]
  rw [← infinitePlace_circularUnit37 hzeta (remainingPlacesEquiv37 hzeta j).val i,
    remainingPlacesEquiv37_apply hzeta j,
    place37_circularUnit37 hzeta j.castSucc i]
  simp only [Fin.val_castSucc]

/-- The exponent-`37` circular-unit regulator is the absolute determinant of one fixed,
field-independent sine matrix. -/
theorem circularUnit37_regOfFamily_eq_explicitSineDet {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) :
    NumberField.Units.regOfFamily (circularUnitRegFamily37 hzeta) =
      |explicitSineMatrix37.det| := by
  rw [circularUnit37_regOfFamily_eq_abs_det hzeta
    (omittedPlace37 hzeta) (remainingPlacesEquiv37 hzeta).symm]
  rw [← Matrix.det_reindex_self (remainingPlacesEquiv37 hzeta).symm,
    reindex_circularLogMatrix37 hzeta]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- Fully canonical finite form of the remaining exponent-`37` analytic identity.  Neither the
matrix nor its indexing now depends on `K`, `zeta`, or auxiliary choices. -/
theorem circularUnit37_realIndex_eq_classNumber_iff_explicitSineDet {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) :
    realUnitRelIndex (circularUnit37 hzeta) = NumberField.classNumber K⁺ ↔
      NumberField.dedekindZeta_residue K⁺ =
        |explicitSineMatrix37.det| / Real.sqrt |(NumberField.discr K⁺ : ℝ)| := by
  rw [circularUnit37_realIndex_eq_classNumber_iff hzeta,
    circularUnit37_regOfFamily_eq_explicitSineDet hzeta]

end

end Fermat.Irregular.CyclotomicPlaces37
