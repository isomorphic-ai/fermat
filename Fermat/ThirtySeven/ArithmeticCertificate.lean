import Fermat.Basic

/-!
# Finite arithmetic certificates for exponent thirty-seven

This module records the small exact computations from the uploaded
exponent-`37` proof package.  These are kernel-checked arithmetic facts;
the number-theoretic criteria that consume them are kept separate.
-/

namespace Fermat.ThirtySeven.ArithmeticCertificate

set_option maxHeartbeats 0
set_option maxRecDepth 100000

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

@[simp] private theorem bernoulli'_five : bernoulli' 5 = 0 := by
  exact bernoulli'_eq_zero_of_odd (by decide) (by decide)

@[simp] private theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_five, Nat.choose]

@[simp] private theorem bernoulli'_eight : bernoulli' 8 = -1 / 30 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_five, bernoulli'_six,
    bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_ten : bernoulli' 10 = 5 / 66 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_twelve : bernoulli' 12 = -691 / 2730 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_fourteen : bernoulli' 14 = 7 / 6 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_sixteen : bernoulli' 16 = -3617 / 510 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_eighteen : bernoulli' 18 = 43867 / 798 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_twenty : bernoulli' 20 = -174611 / 330 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_twenty_two : bernoulli' 22 = 854513 / 138 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_twenty_four : bernoulli' 24 = -236364091 / 2730 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_twenty_six : bernoulli' 26 = 8553103 / 6 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_twenty_eight : bernoulli' 28 = -23749461029 / 870 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_thirty : bernoulli' 30 = 8615841276005 / 14322 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_thirty_two :
    bernoulli' 32 = -7709321041217 / 510 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_thirty_four :
    bernoulli' 34 = 2577687858367 / 6 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

/-- The exact Bernoulli number at the unique irregular index for `37`. -/
theorem bernoulli_32_exact :
    bernoulli 32 = -(7709321041217 : ℚ) / 510 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli'_thirty_two

/-! ## The complete irregular-index scan -/

/-- Even indices in the classical range whose Bernoulli numerator is
divisible by `p`. -/
def irregularIndices (p : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (p - 3)).filter fun n ↦ Even n ∧ (p : ℤ) ∣ (bernoulli n).num

/-- Thirty-seven has the unique irregular index `32`. -/
theorem irregularIndices_thirtySeven : irregularIndices 37 = {32} := by
  ext n
  simp only [irregularIndices, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hn2, hn34⟩, heven, hdvd⟩
    interval_cases n <;>
      norm_num [bernoulli_eq_bernoulli'_of_ne_one, bernoulli'_eq_zero_of_odd] at heven
    all_goals
      norm_num [bernoulli_eq_bernoulli'_of_ne_one, bernoulli'_eq_zero_of_odd] at hdvd
    all_goals norm_num
  · rintro rfl
    norm_num [bernoulli_eq_bernoulli'_of_ne_one]

/-! ## The exact `37`-adic information in `B₃₂` -/

/-- Removing the single factor `37` from the absolute numerator of `B₃₂`. -/
theorem bernoulli_32_numerator_factorization :
    (7709321041217 : ℕ) = 37 * 208360028141 := by
  norm_num

/-- The absolute numerator of `B₃₂` is not divisible by `37²`. -/
theorem bernoulli_32_numerator_not_dvd_sq :
    ¬37 ^ 2 ∣ (7709321041217 : ℕ) := by
  norm_num

/-- The denominator of `B₃₂` is prime to `37`. -/
theorem bernoulli_32_denominator_not_dvd : ¬37 ∣ (510 : ℕ) := by
  norm_num

/-- The package's normalized residue
`B₃₂ / (32 · 37) = 1 (mod 37)`, after cancelling the single
factor `37` from its numerator. -/
theorem bernoulli_32_scaled_residue :
    (-(208360028141 : ℤ) : ZMod 37) / ((32 : ZMod 37) * 510) = 1 := by
  decide

/-- The small power used in the package's primary quotient. -/
theorem two_pow_32_mod_37 : (2 : ZMod 37) ^ 32 = 7 := by
  decide

/-- The package's compact primary quotient is the nonzero residue `6`. -/
theorem primary_quotient_mod_37 :
    ((2 : ZMod 37) ^ 32 - 1) *
        ((-(208360028141 : ℤ) : ZMod 37) / ((32 : ZMod 37) * 510)) = 6 := by
  decide

/-- The independent Wieferich cross-check from the package. -/
theorem two_pow_36_mod_37_sq : (2 : ZMod (37 ^ 2)) ^ 36 = 38 := by
  decide

/-- In particular, `2³⁶` is not `1` modulo `37²`. -/
theorem two_pow_36_not_one_mod_37_sq : (2 : ZMod (37 ^ 2)) ^ 36 ≠ 1 := by
  decide

end Fermat.ThirtySeven.ArithmeticCertificate
