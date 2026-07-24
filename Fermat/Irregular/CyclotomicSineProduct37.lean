import Fermat.Irregular.CyclotomicPlaces37
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

/-!
# The trivial-character sine product at exponent 37

The fixed circular-unit regulator matrix at exponent `37` is built from logarithms of
cyclotomic chord lengths.  This file proves the product formula for those lengths directly from
`cyclotomic 37` evaluated at `1`:

`prod (j = 1, ..., 18), 2 * |sin (pi * j / 37)| = sqrt 37`.

The proof first enumerates all thirty-six primitive roots, pairs each root with its inverse, and
then identifies the first eighteen chord lengths with the displayed sines.  Positivity yields the
equivalent logarithmic identities.  This is the trivial-character factor which must be separated
from the nontrivial even-character factors in the circular regulator determinant.
-/

open scoped Classical BigOperators
open Polynomial

namespace Fermat.Irregular.CyclotomicSineProduct37

noncomputable section

open Fermat.Irregular.CyclotomicPlaces37

/-- All nontrivial `37`th roots, indexed by the exponents `1, ..., 36`. -/
def fullRoot37 (k : Fin 36) : ℂ :=
  eta37 ^ (k.val + 1)

theorem fullRoot37_primitive (k : Fin 36) : IsPrimitiveRoot (fullRoot37 k) 37 := by
  exact eta37_primitive.pow_of_coprime (k.val + 1) (by fin_cases k <;> decide)

theorem fullRoot37_injective : Function.Injective fullRoot37 := by
  intro i j h
  apply Fin.ext
  have := eta37_primitive.pow_inj (by omega) (by omega) h
  omega

/-- The exponents `1, ..., 36` enumerate the primitive `37`th roots. -/
def fullRootsEquiv37 : Fin 36 ≃ primitiveRoots 37 ℂ := by
  refine Equiv.ofBijective (fun k ↦ ⟨fullRoot37 k,
    (mem_primitiveRoots (by norm_num)).mpr (fullRoot37_primitive k)⟩) ?_
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨fun i j h ↦ fullRoot37_injective (congrArg Subtype.val h), ?_⟩
  rw [Fintype.card_fin, Fintype.card_coe, Complex.card_primitiveRoots]
  decide

@[simp] theorem fullRootsEquiv37_apply_val (k : Fin 36) :
    ((fullRootsEquiv37 k : primitiveRoots 37 ℂ) : ℂ) = fullRoot37 k :=
  rfl

/-- Evaluating `cyclotomic 37` at `1` gives the product of all thirty-six chord lengths. -/
theorem prod_full_chords37 :
    ∏ k : Fin 36, ‖1 - fullRoot37 k‖ = 37 := by
  have hpoly := cyclotomic_eq_prod_X_sub_primitiveRoots eta37_primitive
  have heval := congrArg (Polynomial.eval (1 : ℂ)) hpoly
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] at heval
  letI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have heval' : (37 : ℂ) =
      Finset.univ.prod (fun z : {x : ℂ // x ∈ primitiveRoots 37 ℂ} ↦
        (1 : ℂ) - z.1) := by
    rw [Polynomial.eval_one_cyclotomic_prime] at heval
    rw [← Finset.prod_attach] at heval
    rw [← Finset.univ_eq_attach] at heval
    exact heval
  rw [← (fullRootsEquiv37.prod_comp fun z : primitiveRoots 37 ℂ ↦ (1 : ℂ) - z)] at heval'
  have hnorm := congrArg norm heval'
  simpa only [Complex.norm_prod, Complex.norm_natCast, Complex.norm_ofNat, Nat.cast_ofNat,
    fullRootsEquiv37_apply_val] using hnorm.symm

theorem norm_one_sub_inv_of_norm_one (z : ℂ) (hz : ‖z‖ = 1) :
    ‖1 - z⁻¹‖ = ‖1 - z‖ := by
  rw [Complex.inv_eq_conj hz]
  rw [show 1 - starRingEnd ℂ z = starRingEnd ℂ (1 - z) by simp]
  exact Complex.norm_conj (1 - z)

/-- The root in the second half is the inverse of the root at the reversed first-half index. -/
theorem fullRoot37_natAdd_eq_inv (j : Fin 18) :
    fullRoot37 (Fin.natAdd 18 j) =
      (fullRoot37 (Fin.castAdd 18 (Fin.rev j)))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [fullRoot37, fullRoot37, ← pow_add]
  convert eta37_primitive.pow_eq_one using 2
  simp only [Fin.val_natAdd, Fin.val_castAdd, Fin.val_rev]
  omega

theorem fullRoot37_secondHalf_chord (j : Fin 18) :
    ‖1 - fullRoot37 (Fin.natAdd 18 j)‖ =
      ‖1 - fullRoot37 (Fin.castAdd 18 (Fin.rev j))‖ := by
  rw [fullRoot37_natAdd_eq_inv]
  apply norm_one_sub_inv_of_norm_one
  rw [fullRoot37, norm_pow,
    Complex.norm_eq_one_of_pow_eq_one eta37_primitive.pow_eq_one (by norm_num), one_pow]

theorem prod_full_chords37_eq_half_sq :
    (∏ k : Fin 36, ‖1 - fullRoot37 k‖) =
      (∏ j : Fin 18, ‖1 - fullRoot37 (Fin.castAdd 18 j)‖) ^ 2 := by
  have hsplit := (finSumFinEquiv (m := 18) (n := 18)).prod_comp
    (fun k : Fin 36 ↦ ‖1 - fullRoot37 k‖)
  rw [Fintype.prod_sum_type] at hsplit
  simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right] at hsplit
  rw [← hsplit]
  simp only [pow_two]
  have hsecond :
      (∏ j : Fin 18, ‖1 - fullRoot37 (Fin.natAdd 18 j)‖) =
        ∏ j : Fin 18, ‖1 - fullRoot37 (Fin.castAdd 18 j)‖ := by
    have hrev := Equiv.prod_comp (Fin.revPerm : Equiv.Perm (Fin 18))
      (fun j : Fin 18 ↦ ‖1 - fullRoot37 (Fin.natAdd 18 j)‖)
    rw [← hrev]
    apply Fintype.prod_congr
    intro j
    rw [fullRoot37_secondHalf_chord]
    simp only [Fin.revPerm_apply, Fin.rev_rev]
  rw [hsecond]

def halfChordProduct37 : ℝ :=
  ∏ j : Fin 18, ‖1 - fullRoot37 (Fin.castAdd 18 j)‖

theorem halfChordProduct37_sq : halfChordProduct37 ^ 2 = 37 := by
  change (∏ j : Fin 18, ‖1 - fullRoot37 (Fin.castAdd 18 j)‖) ^ 2 = 37
  rw [← prod_full_chords37_eq_half_sq]
  exact prod_full_chords37

theorem halfChordProduct37_eq_sqrt : halfChordProduct37 = Real.sqrt 37 := by
  have hnonneg : 0 ≤ halfChordProduct37 := by
    apply Finset.prod_nonneg
    intro j _
    positivity
  calc
    halfChordProduct37 = |halfChordProduct37| := (abs_of_nonneg hnonneg).symm
    _ = Real.sqrt (halfChordProduct37 ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ = Real.sqrt 37 := by rw [halfChordProduct37_sq]

/-- The positive chord length at the standard representative `j + 1`. -/
def chord37 (j : Fin 18) : ℝ :=
  2 * |Real.sin (Real.pi * (((j.val + 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)))|

theorem chord37_eq_norm (j : Fin 18) :
    chord37 j = ‖1 - fullRoot37 (Fin.castAdd 18 j)‖ := by
  rw [fullRoot37]
  change chord37 j =
    ‖1 - Complex.exp (2 * Real.pi * Complex.I *
      (((1 : ℕ) : ℂ) / ((37 : ℕ) : ℂ))) ^ (j.val + 1)‖
  rw [Fermat.Irregular.CyclotomicZeta.norm_one_sub_exp_two_pi_I_pow]
  simp only [chord37, Nat.cast_one]
  congr 2
  congr 1
  ring

/-- The classical half-product of the `37`th cyclotomic chord lengths. -/
theorem prod_chord37 : (∏ j : Fin 18, chord37 j) = Real.sqrt 37 := by
  rw [← halfChordProduct37_eq_sqrt]
  apply Fintype.prod_congr
  intro j
  exact chord37_eq_norm j

theorem chord37_pos (j : Fin 18) : 0 < chord37 j := by
  have hnum_lt : (((j.val + 1 : ℕ) : ℝ)) < 37 := by
    exact_mod_cast (show j.val + 1 < 37 by omega)
  have hfrac_pos : 0 < (((j.val + 1 : ℕ) : ℝ) / 37) := by positivity
  have hfrac_lt : (((j.val + 1 : ℕ) : ℝ) / 37) < 1 := by
    exact (div_lt_one (by norm_num)).2 hnum_lt
  have hsin : 0 < Real.sin (Real.pi * (((j.val + 1 : ℕ) : ℝ) / 37)) :=
    Real.sin_pos_of_pos_of_lt_pi
      (mul_pos Real.pi_pos hfrac_pos)
      (by simpa using mul_lt_mul_of_pos_left hfrac_lt Real.pi_pos)
  exact mul_pos (by norm_num) (abs_pos.mpr hsin.ne')

/-- Logarithmic form of the half-product identity. -/
theorem sum_log_chord37 :
    (∑ j : Fin 18, Real.log (chord37 j)) = Real.log (Real.sqrt 37) := by
  rw [← prod_chord37]
  symm
  exact Real.log_prod (fun j _ ↦ (chord37_pos j).ne')

/-- Doubled logarithmic form, matching the trivial even character. -/
theorem two_mul_sum_log_chord37 :
    2 * (∑ j : Fin 18, Real.log (chord37 j)) = Real.log 37 := by
  rw [sum_log_chord37]
  calc
    2 * Real.log (Real.sqrt 37) = Real.log (Real.sqrt 37 ^ 2) :=
      (Real.log_pow _ 2).symm
    _ = Real.log 37 := by rw [Real.sq_sqrt (by norm_num)]

end

end Fermat.Irregular.CyclotomicSineProduct37
