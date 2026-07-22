import Fermat.Irregular.CyclotomicPlacesPrime
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

/-!
# The half chord product at an odd prime

The product of the positive pth cyclotomic chord lengths over one
representative from every conjugate pair is the square root of p.
-/

open scoped Classical BigOperators
open Polynomial

namespace Fermat.Irregular.CyclotomicSineProductPrime

noncomputable section

open Fermat.Irregular.CyclotomicPlacesPrime
open Fermat.Irregular.SinnottIndexPrime

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 < p)]

local notation3 "r" => (p - 3) / 2
local notation3 "n" => r + 1

theorem two_half_add_one : n + n + 1 = p := by
  have hhalf := half_rank_succ (p := p)
  have hpodd : Odd p := Nat.Prime.odd_of_ne_two
    (Fact.out : Nat.Prime p) (prime_ne_two (p := p))
  obtain ⟨m, hm⟩ := hpodd
  have hpgt : 2 < p := Fact.out
  omega

theorem full_exponent_lt (k : Fin (n + n)) : k.val + 1 < p := by
  have hk := k.isLt
  have hsize := two_half_add_one (p := p)
  omega

theorem full_exponent_coprime (k : Fin (n + n)) :
    (k.val + 1).Coprime p := by
  exact (Nat.coprime_of_lt_prime (by omega)
    (full_exponent_lt (p := p) k)
    (Fact.out : Nat.Prime p)).symm

/-- All nontrivial pth roots, indexed by exponents one through p-1. -/
def fullRoot (k : Fin (n + n)) : ℂ :=
  eta (p := p) ^ (k.val + 1)

theorem fullRoot_primitive (k : Fin (n + n)) :
    IsPrimitiveRoot (fullRoot (p := p) k) p :=
  (eta_primitive (p := p)).pow_of_coprime
    (k.val + 1) (full_exponent_coprime (p := p) k)

theorem fullRoot_injective :
    Function.Injective (fullRoot (p := p)) := by
  intro i j h
  apply Fin.ext
  have hpow := (eta_primitive (p := p)).pow_inj
    (full_exponent_lt (p := p) i)
    (full_exponent_lt (p := p) j) h
  omega

def fullRootsEquiv : Fin (n + n) ≃ primitiveRoots p ℂ := by
  refine Equiv.ofBijective (fun k ↦
    ⟨fullRoot (p := p) k,
      (mem_primitiveRoots (Nat.Prime.pos
        (Fact.out : Nat.Prime p))).mpr
        (fullRoot_primitive (p := p) k)⟩) ?_
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨fun i j h ↦ fullRoot_injective (p := p)
    (congrArg Subtype.val h), ?_⟩
  rw [Fintype.card_fin, Fintype.card_coe,
    Complex.card_primitiveRoots, Nat.totient_prime
      (Fact.out : Nat.Prime p)]
  have hsize := two_half_add_one (p := p)
  omega

@[simp]
theorem fullRootsEquiv_apply_val (k : Fin (n + n)) :
    ((fullRootsEquiv (p := p) k : primitiveRoots p ℂ) : ℂ) =
      fullRoot (p := p) k := rfl

theorem prod_full_chords :
    ∏ k : Fin (n + n), ‖1 - fullRoot (p := p) k‖ = p := by
  have hpoly :=
    cyclotomic_eq_prod_X_sub_primitiveRoots (eta_primitive (p := p))
  have heval := congrArg (Polynomial.eval (1 : ℂ)) hpoly
  simp only [Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C] at heval
  have heval' : (p : ℂ) =
      Finset.univ.prod
        (fun z : {x : ℂ // x ∈ primitiveRoots p ℂ} ↦
          (1 : ℂ) - z.1) := by
    rw [Polynomial.eval_one_cyclotomic_prime] at heval
    rw [← Finset.prod_attach] at heval
    rw [← Finset.univ_eq_attach] at heval
    exact heval
  rw [← (fullRootsEquiv (p := p)).prod_comp
    (fun z : primitiveRoots p ℂ ↦ (1 : ℂ) - z)] at heval'
  have hnorm := congrArg norm heval'
  simpa only [Complex.norm_prod, Complex.norm_natCast,
    fullRootsEquiv_apply_val] using hnorm.symm

theorem norm_one_sub_inv_of_norm_one (z : ℂ) (hz : ‖z‖ = 1) :
    ‖1 - z⁻¹‖ = ‖1 - z‖ := by
  rw [Complex.inv_eq_conj hz]
  rw [show 1 - starRingEnd ℂ z = starRingEnd ℂ (1 - z) by simp]
  exact Complex.norm_conj (1 - z)

theorem fullRoot_natAdd_eq_inv (j : Fin n) :
    fullRoot (p := p) (Fin.natAdd n j) =
      (fullRoot (p := p)
        (Fin.castAdd n (Fin.rev j)))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [fullRoot, fullRoot, ← pow_add]
  convert (eta_primitive (p := p)).pow_eq_one using 2
  simp only [Fin.val_natAdd, Fin.val_castAdd, Fin.val_rev]
  have hsize := two_half_add_one (p := p)
  omega

theorem fullRoot_secondHalf_chord (j : Fin n) :
    ‖1 - fullRoot (p := p) (Fin.natAdd n j)‖ =
      ‖1 - fullRoot (p := p)
        (Fin.castAdd n (Fin.rev j))‖ := by
  rw [fullRoot_natAdd_eq_inv]
  apply norm_one_sub_inv_of_norm_one
  rw [fullRoot, norm_pow,
    Complex.norm_eq_one_of_pow_eq_one
      (eta_primitive (p := p)).pow_eq_one
      (Nat.Prime.ne_zero (Fact.out : Nat.Prime p)), one_pow]

theorem prod_full_chords_eq_half_sq :
    (∏ k : Fin (n + n), ‖1 - fullRoot (p := p) k‖) =
      (∏ j : Fin n,
        ‖1 - fullRoot (p := p) (Fin.castAdd n j)‖) ^ 2 := by
  have hsplit := (@finSumFinEquiv n n).prod_comp
    (fun k : Fin (n + n) ↦ ‖1 - fullRoot (p := p) k‖)
  rw [Fintype.prod_sum_type] at hsplit
  simp only [finSumFinEquiv_apply_left,
    finSumFinEquiv_apply_right] at hsplit
  rw [← hsplit]
  simp only [pow_two]
  have hsecond :
      (∏ j : Fin n,
        ‖1 - fullRoot (p := p) (Fin.natAdd n j)‖) =
      ∏ j : Fin n,
        ‖1 - fullRoot (p := p) (Fin.castAdd n j)‖ := by
    have hrev := Equiv.prod_comp
      (Fin.revPerm : Equiv.Perm (Fin n))
      (fun j : Fin n ↦
        ‖1 - fullRoot (p := p) (Fin.natAdd n j)‖)
    rw [← hrev]
    apply Fintype.prod_congr
    intro j
    rw [fullRoot_secondHalf_chord]
    simp only [Fin.revPerm_apply, Fin.rev_rev]
  rw [hsecond]

def halfChordProduct : ℝ :=
  ∏ j : Fin n,
    ‖1 - fullRoot (p := p) (Fin.castAdd n j)‖

theorem halfChordProduct_sq :
    halfChordProduct (p := p) ^ 2 = p := by
  change (∏ j : Fin n,
    ‖1 - fullRoot (p := p) (Fin.castAdd n j)‖) ^ 2 = p
  rw [← prod_full_chords_eq_half_sq]
  exact prod_full_chords (p := p)

theorem halfChordProduct_eq_sqrt :
    halfChordProduct (p := p) = Real.sqrt p := by
  have hnonneg : 0 ≤ halfChordProduct (p := p) := by
    apply Finset.prod_nonneg
    intro j _
    positivity
  calc
    halfChordProduct (p := p) =
        |halfChordProduct (p := p)| :=
      (abs_of_nonneg hnonneg).symm
    _ = Real.sqrt (halfChordProduct (p := p) ^ 2) :=
      (Real.sqrt_sq_eq_abs _).symm
    _ = Real.sqrt p := by rw [halfChordProduct_sq]

def chord (j : Fin n) : ℝ :=
  2 * |Real.sin
    (Real.pi * (((j.val + 1 : ℕ) : ℝ) / ((p : ℕ) : ℝ)))|

theorem chord_eq_norm (j : Fin n) :
    chord (p := p) j =
      ‖1 - fullRoot (p := p) (Fin.castAdd n j)‖ := by
  rw [fullRoot]
  change chord (p := p) j =
    ‖1 - Complex.exp (2 * Real.pi * Complex.I *
      (((1 : ℕ) : ℂ) / ((p : ℕ) : ℂ))) ^ (j.val + 1)‖
  rw [Fermat.Irregular.CyclotomicPlacesPrime.norm_one_sub_exp_two_pi_I_pow]
  simp only [chord, Nat.cast_one]
  congr 2
  congr 1
  ring

theorem prod_chord :
    (∏ j : Fin n, chord (p := p) j) = Real.sqrt p := by
  rw [← halfChordProduct_eq_sqrt]
  apply Fintype.prod_congr
  intro j
  exact chord_eq_norm (p := p) j

theorem chord_pos (j : Fin n) : 0 < chord (p := p) j := by
  have hnum_lt : (((j.val + 1 : ℕ) : ℝ)) < p := by
    exact_mod_cast standardExponent_lt (p := p) j
  have hpR : 0 < (p : ℝ) := by
    exact_mod_cast Nat.Prime.pos (Fact.out : Nat.Prime p)
  have hfrac_pos :
      0 < (((j.val + 1 : ℕ) : ℝ) / (p : ℝ)) :=
    div_pos (by positivity) hpR
  have hfrac_lt :
      (((j.val + 1 : ℕ) : ℝ) / (p : ℝ)) < 1 := by
    exact (div_lt_one hpR).2 hnum_lt
  have hsin :
      0 < Real.sin (Real.pi *
        (((j.val + 1 : ℕ) : ℝ) / (p : ℝ))) :=
    Real.sin_pos_of_pos_of_lt_pi
      (mul_pos Real.pi_pos hfrac_pos)
      (by simpa using
        mul_lt_mul_of_pos_left hfrac_lt Real.pi_pos)
  exact mul_pos (by norm_num) (abs_pos.mpr hsin.ne')

theorem sum_log_chord :
    (∑ j : Fin n, Real.log (chord (p := p) j)) =
      Real.log (Real.sqrt p) := by
  rw [← prod_chord]
  symm
  exact Real.log_prod (fun j _ ↦ (chord_pos (p := p) j).ne')

end

end Fermat.Irregular.CyclotomicSineProductPrime
