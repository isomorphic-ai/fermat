import Fermat.Irregular.SinnottIndexPrime
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Canonical places and circular regulators for odd prime conductors

This file enumerates the complex places of a prime cyclotomic field by the
standard positive powers of a complex primitive root and identifies the
canonical circular-unit regulator with one explicit sine determinant.
-/

open scoped NumberField Classical

namespace Fermat.Irregular.CyclotomicPlacesPrime

noncomputable section

open NumberField Polynomial
open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.SinnottIndex
open Fermat.Irregular.SinnottIndexPrime

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 < p)]
variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]

local notation3 "r" => (p - 3) / 2
local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- The standard complex primitive pth root. -/
def eta : ℂ :=
  Complex.exp
    (2 * Real.pi * Complex.I * (((1 : ℕ) : ℂ) / ((p : ℕ) : ℂ)))

theorem eta_primitive : IsPrimitiveRoot (eta (p := p)) p := by
  simpa [eta, div_eq_mul_inv, mul_assoc] using
    Complex.isPrimitiveRoot_exp p
      (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))

theorem standardExponent_coprime (j : Fin (r + 1)) :
    (j.val + 1).Coprime p := by
  apply Nat.Coprime.symm
  apply (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr
  intro hdvd
  have hjpos : 0 < j.val + 1 := by omega
  have hple : p ≤ j.val + 1 := Nat.le_of_dvd hjpos hdvd
  have hjlt : j.val + 1 < p := by
    have hj := j.isLt
    have hrank := half_rank_succ (p := p)
    have hpgt : 2 < p := Fact.out
    omega
  omega

/-- The standard primitive root with exponent j+1. -/
def root (j : Fin (r + 1)) : primitiveRoots p ℂ :=
  ⟨eta (p := p) ^ (j.val + 1),
    (mem_primitiveRoots (Nat.Prime.pos
      (Fact.out : Nat.Prime p))).mpr
      ((eta_primitive (p := p)).pow_of_coprime
        (j.val + 1) (standardExponent_coprime (p := p) j))⟩

/-- The embedding sending zeta to the standard root with exponent j+1. -/
def embedding {zeta : K} (hzeta : IsPrimitiveRoot zeta p)
    (j : Fin (r + 1)) : K →ₐ[ℚ] ℂ :=
  (hzeta.embeddingsEquivPrimitiveRoots ℂ
    (cyclotomic.irreducible_rat
      (Nat.Prime.pos (Fact.out : Nat.Prime p)))).symm (root (p := p) j)

theorem embedding_zeta {zeta : K} (hzeta : IsPrimitiveRoot zeta p)
    (j : Fin (r + 1)) :
    embedding hzeta j zeta = eta (p := p) ^ (j.val + 1) := by
  have h := congrArg Subtype.val
    ((hzeta.embeddingsEquivPrimitiveRoots ℂ
      (cyclotomic.irreducible_rat
        (Nat.Prime.pos (Fact.out : Nat.Prime p)))).apply_symm_apply
          (root (p := p) j))
  simpa only [embedding, root] using h

def place {zeta : K} (hzeta : IsPrimitiveRoot zeta p)
    (j : Fin (r + 1)) : NumberField.InfinitePlace K :=
  NumberField.InfinitePlace.mk (embedding hzeta j).toRingHom

theorem standardExponent_lt (j : Fin (r + 1)) :
    j.val + 1 < p := by
  have hj := j.isLt
  have hrank := half_rank_succ (p := p)
  have hpgt : 2 < p := Fact.out
  omega

theorem place_injective {zeta : K} (hzeta : IsPrimitiveRoot zeta p) :
    Function.Injective (place hzeta) := by
  intro i j hij
  rw [place, place, NumberField.InfinitePlace.mk_eq_iff] at hij
  rcases hij with hij | hij
  · have hp :
        eta (p := p) ^ (i.val + 1) =
          eta (p := p) ^ (j.val + 1) := by
      rw [← embedding_zeta hzeta i, ← embedding_zeta hzeta j]
      exact DFunLike.congr_fun hij zeta
    apply Fin.ext
    have hpow := (eta_primitive (p := p)).pow_inj
      (standardExponent_lt (p := p) i)
      (standardExponent_lt (p := p) j) hp
    omega
  · have hp :
        (eta (p := p) ^ (i.val + 1))⁻¹ =
          eta (p := p) ^ (j.val + 1) := by
      rw [Complex.inv_eq_conj (by
        rw [norm_pow, Complex.norm_eq_one_of_pow_eq_one
          (eta_primitive (p := p)).pow_eq_one
            (Nat.Prime.ne_zero (Fact.out : Nat.Prime p)), one_pow])]
      rw [← embedding_zeta hzeta i, ← embedding_zeta hzeta j]
      exact DFunLike.congr_fun hij zeta
    have hone :
        eta (p := p) ^ ((i.val + 1) + (j.val + 1)) = 1 := by
      rw [pow_add, ← hp]
      exact mul_inv_cancel₀
        (pow_ne_zero _ ((eta_primitive (p := p)).ne_zero
          (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))))
    have hdiv := (eta_primitive (p := p)).dvd_of_pow_eq_one _ hone
    have hsumlt :
        (i.val + 1) + (j.val + 1) < p := by
      have hi := i.isLt
      have hj := j.isLt
      have hrank := half_rank_succ (p := p)
      have hpodd : Odd p := Nat.Prime.odd_of_ne_two
        (Fact.out : Nat.Prime p) (prime_ne_two (p := p))
      obtain ⟨m, hm⟩ := hpodd
      omega
    have hpos : 0 < (i.val + 1) + (j.val + 1) := by omega
    exact ((Nat.not_dvd_of_pos_of_lt hpos hsumlt) hdiv).elim

theorem card_infinitePlace :
    Fintype.card (NumberField.InfinitePlace K) = r + 1 := by
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero K (n := p)
      (by
        exact (Fact.out : Nat.Prime p).two_le.lt_of_ne
          (prime_ne_two (p := p)).symm),
    IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two
      (K := K) p,
    Nat.totient_prime (Fact.out : Nat.Prime p),
    ← half_rank_succ (p := p)]
  simp

def placesEquiv {zeta : K} (hzeta : IsPrimitiveRoot zeta p) :
    Fin (r + 1) ≃ NumberField.InfinitePlace K :=
  Equiv.ofBijective (place hzeta)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨place_injective hzeta, by
        rw [Fintype.card_fin, card_infinitePlace (p := p) (K := K)]⟩)

@[simp]
theorem placesEquiv_apply {zeta : K} (hzeta : IsPrimitiveRoot zeta p)
    (j : Fin (r + 1)) :
    placesEquiv hzeta j = place hzeta j := rfl

def omittedPlace {zeta : K} (hzeta : IsPrimitiveRoot zeta p) :
    NumberField.InfinitePlace K :=
  place hzeta (Fin.last r)

def remainingPlacesEquiv {zeta : K} (hzeta : IsPrimitiveRoot zeta p) :
    Fin r ≃ {w : NumberField.InfinitePlace K // w ≠ omittedPlace hzeta} :=
  (finSuccAboveEquiv (Fin.last r)).trans
    (Equiv.subtypeEquiv (placesEquiv hzeta) fun j ↦ by
      change j ≠ Fin.last r ↔
        place hzeta j ≠ place hzeta (Fin.last r)
      simpa only [placesEquiv_apply] using
        ((placesEquiv hzeta).injective.ne_iff).symm)

theorem remainingPlacesEquiv_apply
    {zeta : K} (hzeta : IsPrimitiveRoot zeta p) (j : Fin r) :
    (remainingPlacesEquiv hzeta j).val = place hzeta j.castSucc := by
  simp [remainingPlacesEquiv, finSuccAboveEquiv_apply]

/-- The value of a circular unit at an arbitrary infinite place. -/
theorem infinitePlace_circularUnit
    {zeta : K} (hzeta : IsPrimitiveRoot zeta p)
    (w : NumberField.InfinitePlace K) (i : Fin r) :
    w (((circularUnitFamily hzeta (prime_ne_two (p := p)) i).val :
        NumberField.RingOfIntegers K) : K) =
      ‖1 - (w.embedding zeta) ^ (i.val + 2)‖ /
        ‖1 - w.embedding zeta‖ := by
  rw [← NumberField.InfinitePlace.norm_embedding_eq]
  rw [circularUnitFamily_coe]
  simp only [map_mul, map_div₀, map_pow, map_sub, map_one,
    norm_mul, norm_div, norm_pow]
  have hnorm : ‖w.embedding zeta‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one
      ((hzeta.map_of_injective w.embedding.injective).pow_eq_one)
      (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))
  rw [hnorm, one_pow, one_mul]

/-- A chord cut out by a point on the unit circle. -/
theorem norm_one_sub_exp_two_pi_I (x : ℝ) :
    ‖1 - Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))‖ =
      2 * |Real.sin (Real.pi * x)| := by
  rw [show 1 - Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) =
      -(Complex.exp (Complex.I * (2 * Real.pi * x : ℝ)) - 1) by
    have harg : 2 * Real.pi * Complex.I * (x : ℂ) =
        Complex.I * (2 * Real.pi * x : ℝ) := by
      push_cast
      ring
    rw [harg]
    ring]
  rw [norm_neg, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show 2 * Real.pi * x / 2 = Real.pi * x by ring]
  norm_num [Real.norm_eq_abs]

theorem norm_one_sub_exp_two_pi_I_pow (k a n : ℕ) :
    ‖1 - Complex.exp
        (2 * Real.pi * Complex.I * ((k : ℂ) / (n : ℂ))) ^ a‖ =
      2 * |Real.sin
        (Real.pi * ((a : ℝ) * (k : ℝ) / (n : ℝ)))| := by
  rw [← Complex.exp_nat_mul]
  rw [show (a : ℂ) *
      (2 * Real.pi * Complex.I * ((k : ℂ) / (n : ℂ))) =
      2 * Real.pi * Complex.I *
        (((a : ℝ) * (k : ℝ) / (n : ℝ) : ℝ) : ℂ) by
    push_cast
    ring]
  exact norm_one_sub_exp_two_pi_I _

theorem place_circularUnit
    {zeta : K} (hzeta : IsPrimitiveRoot zeta p)
    (j : Fin (r + 1)) (i : Fin r) :
    place hzeta j
        (((circularUnitFamily hzeta (prime_ne_two (p := p)) i).val :
          NumberField.RingOfIntegers K) : K) =
      |Real.sin (Real.pi *
        (((i.val + 2 : ℕ) : ℝ) * ((j.val + 1 : ℕ) : ℝ) /
          ((p : ℕ) : ℝ)))| /
      |Real.sin (Real.pi *
        (((j.val + 1 : ℕ) : ℝ) / ((p : ℕ) : ℝ)))| := by
  rw [place, NumberField.InfinitePlace.apply]
  rw [circularUnitFamily_coe]
  simp only [map_mul, map_div₀, map_pow, map_sub, map_one,
    norm_mul, norm_div, norm_pow, AlgHom.toRingHom_eq_coe]
  change ‖embedding hzeta j zeta‖ ^
        canonicalNormalizationExponent (p := p) (i.val + 2) *
        ‖1 - embedding hzeta j zeta ^ (i.val + 2)‖ /
      ‖1 - embedding hzeta j zeta‖ = _
  rw [embedding_zeta hzeta]
  have heta : ‖eta (p := p)‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one
      (eta_primitive (p := p)).pow_eq_one
      (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))
  simp only [norm_pow, heta, one_pow, one_mul]
  rw [← pow_mul]
  change
    ‖1 - Complex.exp (2 * Real.pi * Complex.I *
        (((1 : ℕ) : ℂ) / ((p : ℕ) : ℂ))) ^
          ((j.val + 1) * (i.val + 2))‖ /
      ‖1 - Complex.exp (2 * Real.pi * Complex.I *
        (((1 : ℕ) : ℂ) / ((p : ℕ) : ℂ))) ^ (j.val + 1)‖ = _
  rw [norm_one_sub_exp_two_pi_I_pow,
    norm_one_sub_exp_two_pi_I_pow]
  field_simp
  congr 2 <;> congr 1 <;> push_cast <;> ring

def circularLogMatrix
    (zeta : K) (w₀ : NumberField.InfinitePlace K)
    (e : {w : NumberField.InfinitePlace K // w ≠ w₀} ≃ Fin r) :
    Matrix {w : NumberField.InfinitePlace K // w ≠ w₀}
      {w : NumberField.InfinitePlace K // w ≠ w₀} ℝ :=
  Matrix.of fun i w ↦
    2 * Real.log
      (‖1 - (w.val.embedding zeta) ^ ((e i).val + 2)‖ /
        ‖1 - w.val.embedding zeta‖)

def explicitSineMatrix : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun i j ↦
    2 * Real.log
      (|Real.sin (Real.pi *
        (((i.val + 2 : ℕ) : ℝ) * ((j.val + 1 : ℕ) : ℝ) /
          ((p : ℕ) : ℝ)))| /
      |Real.sin (Real.pi *
        (((j.val + 1 : ℕ) : ℝ) / ((p : ℕ) : ℝ)))|)

theorem circularUnit_regOfFamily_eq_abs_det
    {zeta : K} (hzeta : IsPrimitiveRoot zeta p)
    (w₀ : NumberField.InfinitePlace K)
    (e : {w : NumberField.InfinitePlace K // w ≠ w₀} ≃ Fin r) :
    NumberField.Units.regOfFamily (circularUnitRegFamily hzeta) =
      |(circularLogMatrix zeta w₀ e).det| := by
  classical
  let eRank : {w : NumberField.InfinitePlace K // w ≠ w₀} ≃
      Fin (NumberField.Units.rank K) :=
    e.trans (finCongr (cyclotomicPrime_unitRank (K := K)
      (Fact.out : Nat.Prime p) (prime_ne_two (p := p)))).symm
  rw [NumberField.Units.regOfFamily_eq_det
    (circularUnitRegFamily hzeta) w₀ eRank]
  apply congrArg abs
  apply congrArg Matrix.det
  ext i w
  simp only [Matrix.of_apply, circularLogMatrix,
    NumberField.IsTotallyComplex.mult_eq, Nat.cast_ofNat]
  rw [show circularUnitRegFamily hzeta (eRank i) =
      circularUnitFamily hzeta (prime_ne_two (p := p)) (e i) by
    simp [circularUnitRegFamily, eRank]]
  rw [infinitePlace_circularUnit hzeta]

theorem reindex_circularLogMatrix
    {zeta : K} (hzeta : IsPrimitiveRoot zeta p) :
    Matrix.reindex (remainingPlacesEquiv hzeta).symm
        (remainingPlacesEquiv hzeta).symm
        (circularLogMatrix zeta (omittedPlace hzeta)
          (remainingPlacesEquiv hzeta).symm) =
      explicitSineMatrix (p := p) := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    circularLogMatrix, Matrix.of_apply, Equiv.symm_symm,
    Equiv.symm_apply_apply, explicitSineMatrix]
  rw [← infinitePlace_circularUnit hzeta
      (remainingPlacesEquiv hzeta j).val i,
    remainingPlacesEquiv_apply hzeta j,
    place_circularUnit hzeta j.castSucc i]
  simp only [Fin.val_castSucc]

/-- The canonical regulator is the absolute explicit sine determinant. -/
theorem circularUnit_regOfFamily_eq_explicitSineDet
    {zeta : K} (hzeta : IsPrimitiveRoot zeta p) :
    NumberField.Units.regOfFamily (circularUnitRegFamily hzeta) =
      |(explicitSineMatrix (p := p)).det| := by
  rw [circularUnit_regOfFamily_eq_abs_det hzeta
    (omittedPlace hzeta) (remainingPlacesEquiv hzeta).symm]
  rw [← Matrix.det_reindex_self (remainingPlacesEquiv hzeta).symm,
    reindex_circularLogMatrix hzeta]

end

end Fermat.Irregular.CyclotomicPlacesPrime
