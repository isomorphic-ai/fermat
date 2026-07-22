import Fermat.FiftyNine.HighBernoulli
import Fermat.ThirtySeven.ArithmeticCertificate

/-!
# Bernoulli arithmetic at exponent 59

The generic scanner first introduced in the exponent-`37` certificate is
reused here.  Its already checked Bernoulli table through index `34` is
extended to `56`; the resulting exact scan finds the single irregular index
`44`.  Combined with the compact high-Bernoulli certificate, this proves all
finite Bernoulli-cube conditions used by Vandiver's criterion.
-/

namespace Fermat.FiftyNine.ArithmeticCertificate

open Fermat.Irregular.VandiverData

set_option maxHeartbeats 0
set_option maxRecDepth 100000

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

@[simp] private theorem bernoulli'_thirty_six :
    bernoulli' 36 = -(26315271553053477373 : ℚ) / 1919190 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_thirty_eight :
    bernoulli' 38 = 2929993913841559 / 6 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_forty :
    bernoulli' 40 = -(261082718496449122051 : ℚ) / 13530 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_forty_two :
    bernoulli' 42 = 1520097643918070802691 / 1806 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_forty_four :
    bernoulli' 44 = -(27833269579301024235023 : ℚ) / 690 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_forty_six :
    bernoulli' 46 = 596451111593912163277961 / 282 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_forty_eight :
    bernoulli' 48 = -(5609403368997817686249127547 : ℚ) / 46410 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_fifty :
    bernoulli' 50 = 495057205241079648212477525 / 66 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_fifty_two :
    bernoulli' 52 = -(801165718135489957347924991853 : ℚ) / 1590 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_fifty_four :
    bernoulli' 54 = 29149963634884862421418123812691 / 798 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_fifty_six :
    bernoulli' 56 = -(2479392929313226753685415739663229 : ℚ) / 870 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

/-- The exact Bernoulli number at the sole irregular index. -/
theorem bernoulli_44_exact :
    bernoulli 44 = -(27833269579301024235023 : ℚ) / 690 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli'_forty_four

/-- Reuse the generic finite scanner defined by the exponent-`37` module. -/
abbrev irregularIndices :=
  Fermat.ThirtySeven.ArithmeticCertificate.irregularIndices

/-- Fifty-nine has exactly one irregular index, namely `44`. -/
theorem irregularIndices_fiftyNine : irregularIndices 59 = {44} := by
  ext n
  simp only [irregularIndices,
    Fermat.ThirtySeven.ArithmeticCertificate.irregularIndices,
    Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hn2, hn56⟩, heven, hdvd⟩
    interval_cases n <;>
      norm_num [bernoulli_eq_bernoulli'_of_ne_one,
        bernoulli'_eq_zero_of_odd] at heven
    all_goals
      norm_num [bernoulli_eq_bernoulli'_of_ne_one,
        bernoulli'_eq_zero_of_odd] at hdvd
    all_goals norm_num
  · rintro rfl
    norm_num [bernoulli_eq_bernoulli'_of_ne_one]

/-- Removing the unique factor `59` from the absolute numerator of `B44`. -/
theorem bernoulli_44_numerator_factorization :
    (27833269579301024235023 : ℕ) = 59 * 471750331852559732797 := by
  norm_num

/-- The numerator of `B44` contains exactly one factor `59`. -/
theorem bernoulli_44_numerator_not_dvd_sq :
    ¬59 ^ 2 ∣ (27833269579301024235023 : ℕ) := by
  norm_num

/-- The package's normalized residue `B44 / 59 = 9 (mod 59)`. -/
theorem bernoulli_44_scaled_residue :
    (-(471750331852559732797 : ℤ) : ZMod 59) / 690 = 9 := by
  decide

/-- The normalization used in the primary quotient. -/
theorem bernoulli_44_index_scaled_residue :
    (-(471750331852559732797 : ℤ) : ZMod 59) / (44 * 690) = 23 := by
  decide

/-- The local nonzero primary shadow from the proof package. -/
theorem primary_quotient_mod_59 :
    ((2 : ZMod 59) ^ 44 - 1) *
      ((-(471750331852559732797 : ℤ) : ZMod 59) / (44 * 690)) = 38 := by
  decide

/-- The independent non-Wieferich shadow at `59`. -/
theorem two_pow_58_mod_59_sq : (2 : ZMod (59 ^ 2)) ^ 58 = 473 := by
  decide

/-- The sole irregular channel reduces every exceptional high condition to
the already checked `B2596` certificate. -/
theorem irregularIndex_numerator_not_dvd_cube
    (j : ℕ) (hj : j ∈ indices 59)
    (hirregular : (59 : ℤ) ∣ (bernoulli j).num) :
    ¬(59 : ℤ) ^ 3 ∣ (bernoulli (j * 59)).num := by
  have hj' : 2 ≤ j ∧ j ≤ 56 ∧ Even j := by
    simpa [indices, and_assoc] using hj
  have hmem : j ∈ irregularIndices 59 := by
    simp only [irregularIndices,
      Fermat.ThirtySeven.ArithmeticCertificate.irregularIndices,
      Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hj'.1, hj'.2.1⟩, hj'.2.2, hirregular⟩
  rw [irregularIndices_fiftyNine] at hmem
  have hj44 : j = 44 := by simpa using hmem
  subst j
  simpa using
    Fermat.FiftyNine.HighBernoulli.bernoulli_2596_numerator_not_dvd_cube

/-- All finite Bernoulli-cube conditions at exponent `59`. -/
theorem bernoulliCubeCondition_fiftyNine : BernoulliCubeCondition 59 := by
  apply bernoulliCubeCondition_of_irregular (by norm_num)
  exact irregularIndex_numerator_not_dvd_cube

end Fermat.FiftyNine.ArithmeticCertificate
