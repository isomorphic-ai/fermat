import Fermat.SixtySeven.FirstCase
import Fermat.ThirtySeven.ArithmeticCertificate

/-!
# Finite Bernoulli arithmetic at exponent 67

The exponent-37 development already kernel-checks the Bernoulli recurrence
through index `34`.  Continuing the same recurrence through `58` gives the
complete irregular-index scan for `67` and the exact low valuation in its
unique exceptional channel.
-/

namespace Fermat.SixtySeven.ArithmeticCertificate

set_option maxHeartbeats 0
set_option maxRecDepth 100000

local instance : Fact (Nat.Prime 67) := ⟨Fermat.SixtySeven.prime_67⟩

@[simp] private theorem bernoulli'_thirtySix :
    bernoulli' 36 = -(26315271553053477373 : ℚ) / 1919190 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_thirtyEight :
    bernoulli' 38 = (2929993913841559 : ℚ) / 6 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_forty :
    bernoulli' 40 = -(261082718496449122051 : ℚ) / 13530 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_fortyTwo :
    bernoulli' 42 = (1520097643918070802691 : ℚ) / 1806 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_fortyFour :
    bernoulli' 44 = -(27833269579301024235023 : ℚ) / 690 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_fortySix :
    bernoulli' 46 = (596451111593912163277961 : ℚ) / 282 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_fortyEight :
    bernoulli' 48 = -(5609403368997817686249127547 : ℚ) / 46410 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_fifty :
    bernoulli' 50 = (495057205241079648212477525 : ℚ) / 66 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_fiftyTwo :
    bernoulli' 52 = -(801165718135489957347924991853 : ℚ) / 1590 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_fiftyFour :
    bernoulli' 54 = (29149963634884862421418123812691 : ℚ) / 798 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_fiftySix :
    bernoulli' 56 = -(2479392929313226753685415739663229 : ℚ) / 870 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_fiftyEight :
    bernoulli' 58 = (84483613348880041862046775994036021 : ℚ) / 354 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_sixty :
    bernoulli' 60 =
      -(1215233140483755572040304994079820246041491 : ℚ) / 56786730 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_sixtyTwo :
    bernoulli' 62 =
      (12300585434086858541953039857403386151 : ℚ) / 6 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_sixtyFour :
    bernoulli' 64 =
      -(106783830147866529886385444979142647942017 : ℚ) / 510 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

/-- The exact Bernoulli number at the package's exceptional index. -/
theorem bernoulli_58_exact :
    bernoulli 58 = (84483613348880041862046775994036021 : ℚ) / 354 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli'_fiftyEight

def irregularIndices (p : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (p - 3)).filter fun n ↦
    Even n ∧ (p : ℤ) ∣ (bernoulli n).num

/-- Sixty-seven has the unique irregular index `58`. -/
theorem irregularIndices_sixtySeven : irregularIndices 67 = {58} := by
  ext n
  simp only [irregularIndices, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hn2, hn64⟩, heven, hdvd⟩
    interval_cases n <;>
      norm_num [bernoulli_eq_bernoulli'_of_ne_one,
        bernoulli'_eq_zero_of_odd] at heven
    all_goals
      norm_num [bernoulli_eq_bernoulli'_of_ne_one,
        bernoulli'_eq_zero_of_odd] at hdvd
    all_goals norm_num
  · rintro rfl
    norm_num [bernoulli_58_exact]

theorem bernoulli_58_numerator_factorization :
    (84483613348880041862046775994036021 : ℕ) =
      67 * 1260949452968358833761892179015463 := by
  norm_num

theorem bernoulli_58_numerator_not_dvd_sq :
    ¬67 ^ 2 ∣ (84483613348880041862046775994036021 : ℕ) := by
  norm_num

theorem bernoulli_58_denominator_not_dvd : ¬67 ∣ (354 : ℕ) := by
  norm_num

/-- The package's reduced residue `B₅₈ / 67 = 15 (mod 67)`. -/
theorem bernoulli_58_scaled_residue :
    ((1260949452968358833761892179015463 : ZMod 67) / 354) = 15 := by
  decide

/-- The normalized character residue `B₅₈ / (58·67) = 43`. -/
theorem bernoulli_58_character_residue :
    ((1260949452968358833761892179015463 : ZMod 67) /
      ((58 : ZMod 67) * 354)) = 43 := by
  decide

theorem two_pow_58_mod_67 : (2 : ZMod 67) ^ 58 = 39 := by
  decide

theorem primary_quotient_mod_67 :
    ((2 : ZMod 67) ^ 58 - 1) *
      ((1260949452968358833761892179015463 : ZMod 67) /
        ((58 : ZMod 67) * 354)) = 26 := by
  decide

theorem two_pow_66_mod_67_sq :
    (2 : ZMod (67 ^ 2)) ^ 66 = 671 := by
  decide

end Fermat.SixtySeven.ArithmeticCertificate
