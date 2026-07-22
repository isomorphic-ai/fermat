import Fermat.Irregular.CyclotomicLogDet
import Fermat.Irregular.CyclotomicPlacesPrime
import Fermat.Irregular.CyclotomicCharactersPrime

/-!
# Real residue enumeration and the generic logarithmic sine matrix

This file supplies the prime-uniform finite indexing needed to apply the
abstract group-determinant theorem to the circular-unit regulator.
-/

open scoped Classical BigOperators

namespace Fermat.Irregular.CyclotomicLogDetPrime

noncomputable section

open Fermat.Irregular.CyclotomicLogDet
open Fermat.Irregular.CyclotomicPlacesPrime
open Fermat.Irregular.CyclotomicCharactersPrime
open Fermat.Irregular.SinnottIndexPrime

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 < p)]

local notation3 "r" => (p - 3) / 2
local notation3 "n" => r + 1

def standardUnit (j : Fin n) : (ZMod p)ˣ :=
  ZMod.unitOfCoprime (j.val + 1)
    (standardExponent_coprime (p := p) j)

def standardRealResidue (j : Fin n) : RealResidueGroup p :=
  QuotientGroup.mk (standardUnit (p := p) j)

theorem standardUnit_coe (j : Fin n) :
    (standardUnit (p := p) j : ZMod p) =
      (j.val + 1 : ℕ) :=
  ZMod.coe_unitOfCoprime _ _

theorem standardRealResidue_injective :
    Function.Injective (standardRealResidue (p := p)) := by
  intro i j hij
  rw [standardRealResidue, standardRealResidue,
    QuotientGroup.eq_iff_div_mem, signSubgroup_mem_iff] at hij
  rcases hij with hdiv | hdiv
  · have hu : standardUnit (p := p) i =
        standardUnit (p := p) j := div_eq_one.mp hdiv
    have hz : (i.val + 1 : ZMod p) =
        (j.val + 1 : ZMod p) := by
      simpa [standardUnit] using congrArg Units.val hu
    have hz' :
        ((i.val + 1 : ℕ) : ZMod p) =
          ((j.val + 1 : ℕ) : ZMod p) := by
      push_cast
      exact hz
    rw [ZMod.natCast_eq_natCast_iff] at hz'
    apply Fin.ext
    have heq := Nat.ModEq.eq_of_lt_of_lt hz'
      (standardExponent_lt (p := p) i)
      (standardExponent_lt (p := p) j)
    omega
  · have hu : standardUnit (p := p) i =
        -(standardUnit (p := p) j) := by
      calc
        standardUnit (p := p) i =
            (standardUnit (p := p) i /
              standardUnit (p := p) j) *
                standardUnit (p := p) j :=
          (div_mul_cancel _ _).symm
        _ = (-1) * standardUnit (p := p) j := by rw [hdiv]
        _ = -(standardUnit (p := p) j) := neg_one_mul _
    have hz : (i.val + 1 : ZMod p) =
        -(j.val + 1 : ZMod p) := by
      simpa [standardUnit] using congrArg Units.val hu
    have hzsum :
        (i.val + 1 + (j.val + 1) : ZMod p) = 0 := by
      rw [hz]
      ring
    have hzsum' :
        ((i.val + 1 + (j.val + 1) : ℕ) : ZMod p) = 0 := by
      push_cast
      exact hzsum
    have hdvd : p ∣ i.val + 1 + (j.val + 1) :=
      (ZMod.natCast_eq_zero_iff _ _).mp hzsum'
    have hlt : i.val + 1 + (j.val + 1) < p := by
      have hi := i.isLt
      have hj := j.isLt
      have hrank := half_rank_succ (p := p)
      have hpodd : Odd p := Nat.Prime.odd_of_ne_two
        (Fact.out : Nat.Prime p) (prime_ne_two (p := p))
      obtain ⟨m, hm⟩ := hpodd
      omega
    exfalso
    exact (Nat.not_dvd_of_pos_of_lt (by omega) hlt) hdvd

def standardRealResiduesEquiv : Fin n ≃ RealResidueGroup p :=
  Equiv.ofBijective (standardRealResidue (p := p))
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨standardRealResidue_injective (p := p), by
        rw [Fintype.card_fin, card_realResidueGroup,
          half_rank_succ (p := p)]⟩)

@[simp]
theorem standardRealResiduesEquiv_apply (j : Fin n) :
    standardRealResiduesEquiv (p := p) j =
      standardRealResidue (p := p) j := rfl

@[simp]
theorem standardRealResidue_zero :
    standardRealResidue (p := p) 0 = 1 := by
  rw [standardRealResidue, QuotientGroup.eq_one_iff]
  have hu : standardUnit (p := p) 0 = 1 := by
    apply Units.ext
    simp [standardUnit]
  rw [hu]
  exact Subgroup.one_mem _

@[simp]
theorem standardRealResiduesEquiv_symm_one :
    (standardRealResiduesEquiv (p := p)).symm 1 = 0 := by
  rw [← standardRealResidue_zero (p := p),
    ← standardRealResiduesEquiv_apply]
  exact (standardRealResiduesEquiv (p := p)).symm_apply_apply 0

def logSineDifferenceMatrix : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun i j ↦
    Real.log |Real.sin (Real.pi *
      (((i.val + 2 : ℕ) : ℝ) * ((j.val + 1 : ℕ) : ℝ) /
        (p : ℝ)))| -
    Real.log |Real.sin (Real.pi *
      (((j.val + 1 : ℕ) : ℝ) / (p : ℝ)))|

theorem sin_pi_mul_div_ne_zero (m : ℕ) (hm : ¬p ∣ m) :
    Real.sin (Real.pi * ((m : ℝ) / (p : ℝ))) ≠ 0 := by
  intro hsin
  have hnorm : ‖1 - eta (p := p) ^ m‖ =
      2 * |Real.sin
        (Real.pi * ((m : ℝ) / (p : ℝ)))| := by
    simpa [eta] using
      norm_one_sub_exp_two_pi_I_pow 1 m p
  have hzero : ‖1 - eta (p := p) ^ m‖ = 0 := by
    rw [hnorm, hsin]
    norm_num
  have hpow : eta (p := p) ^ m = 1 := by
    exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm
  exact hm ((eta_primitive (p := p)).dvd_of_pow_eq_one m hpow)

theorem explicitSineMatrix_eq_two_smul_logSineDifference :
    explicitSineMatrix (p := p) =
      (2 : ℝ) • logSineDifferenceMatrix (p := p) := by
  ext i j
  let a := i.val + 2
  let k := j.val + 1
  have ha : ¬p ∣ a := by
    intro h
    have hle := Nat.le_of_dvd (by omega : 0 < a) h
    have hi := i.isLt
    have hpgt : 2 < p := Fact.out
    omega
  have hk : ¬p ∣ k := by
    intro h
    have hle := Nat.le_of_dvd (by omega : 0 < k) h
    exact (Nat.not_le_of_lt
      (standardExponent_lt (p := p) j.castSucc)) hle
  have hak : ¬p ∣ a * k :=
    (Fact.out : Nat.Prime p).not_dvd_mul ha hk
  have hnum :
      |Real.sin
        (Real.pi * ((a : ℝ) * (k : ℝ) / (p : ℝ)))| ≠ 0 := by
    rw [abs_ne_zero]
    simpa [Nat.cast_mul] using
      sin_pi_mul_div_ne_zero (p := p) (a * k) hak
  have hden :
      |Real.sin (Real.pi * ((k : ℝ) / (p : ℝ)))| ≠ 0 := by
    rw [abs_ne_zero]
    exact sin_pi_mul_div_ne_zero (p := p) k hk
  simp only [explicitSineMatrix, logSineDifferenceMatrix,
    Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  change 2 * Real.log
      (|Real.sin
        (Real.pi * ((a : ℝ) * (k : ℝ) / (p : ℝ)))| /
       |Real.sin (Real.pi * ((k : ℝ) / (p : ℝ)))|) = _
  rw [Real.log_div hnum hden]

theorem explicitSineMatrix_det_eq_pow_mul_logDifferenceDet :
    (explicitSineMatrix (p := p)).det =
      (2 : ℝ) ^ r *
        (logSineDifferenceMatrix (p := p)).det := by
  rw [explicitSineMatrix_eq_two_smul_logSineDifference,
    Matrix.det_smul]
  norm_num

end

end Fermat.Irregular.CyclotomicLogDetPrime
