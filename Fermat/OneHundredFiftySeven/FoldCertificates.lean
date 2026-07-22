import Fermat.OneHundredFiftySeven.FirstCase
import Fermat.Irregular.VandiverData

/-!
# Finite certificates along the exponent-157 seven-fold route

This file reifies the compact exponent-specific arithmetic from the uploaded
proof package.  It deliberately stops short of interpreting the circular-unit
CSV determinant as a plus-class-number theorem and stops short of turning the
two modular power sums into Bernoulli numerator valuations.  Those are shared
theorem boundaries, not exponent-specific computations.
-/

namespace Fermat.OneHundredFiftySeven.FoldCertificates

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-! ## Fold 1: prime substrate and neighbors -/

theorem prime_79 : Nat.Prime 79 := by norm_num
theorem prime_317 : Nat.Prime 317 := by norm_num
theorem prime_7537 : Nat.Prime 7537 := by norm_num

theorem leftNeighbor_decompositions :
    156 = 3 * 52 ∧ 156 = 4 * 39 ∧ 156 = 12 * 13 := by
  norm_num

theorem rightNeighbor_decomposition : 158 = 2 * 79 := by norm_num

/-! ## Folds 2 and 3: the circle and the `g = 2` crease

The displayed power tests are deterministic order certificates once combined
with primality.  Keeping them as literal finite-field equalities avoids
introducing an exponent-local discrete-log implementation.
-/

theorem generator_five_power_tests :
    (5 : ZMod 157) ^ 156 = 1 ∧
      (5 : ZMod 157) ^ 78 ≠ 1 ∧
      (5 : ZMod 157) ^ 52 ≠ 1 ∧
      (5 : ZMod 157) ^ 12 ≠ 1 := by
  decide

theorem two_crease_power_tests :
    (2 : ZMod 157) ^ 52 = 1 ∧
      (2 : ZMod 157) ^ 26 = -1 ∧
      (2 : ZMod 157) ^ 4 ≠ 1 := by
  decide

theorem square_sheet_power_tests :
    (4 : ZMod 157) ^ 26 = 1 ∧
      (4 : ZMod 157) ^ 13 = -1 := by
  decide

/-! ## Fold 4: the quadratic form and the `B₁₃ Q₇₂` composition -/

/-- Evaluate a coefficient list written in increasing degree order. -/
def evalCoeffs : List ℤ → ℤ → ℤ
  | [], _ => 0
  | a :: as, t => a + t * evalCoeffs as t

def b13Coeffs : List ℤ := [0, 1, 0, 1, 0, 1]

def q72Coeffs : List ℤ := [
  1, 0, 6, 6, 15, 18, 30, 33, 32, 35, 27, 24, 14, 10, 16, 6, 21, 8,
  17, 2, -4, -3, -18, -3, -7, 14, 23, 22, 38, 18, 34, 15, 28, 30, 29,
  49, 35, 49, 29, 30, 28, 15, 34, 18, 38, 22, 23, 14, -7, -3, -18, -3,
  -4, 2, 17, 8, 21, 6, 16, 10, 14, 24, 27, 35, 32, 33, 30, 18, 15, 6, 6,
  0, 1]

def b157Coeffs : List ℤ := [
  0, 1, 0, 7, 6, 22, 24, 51, 57, 77, 86, 89, 92, 73, 69, 57, 40, 51, 24,
  54, 16, 34, 7, -5, -4, -29, 8, -2, 33, 54, 54, 95, 55, 100, 63, 91,
  94, 92, 128, 93, 128, 92, 94, 91, 63, 100, 55, 95, 54, 54, 33, -2, 8,
  -29, -4, -5, 7, 34, 16, 54, 24, 51, 40, 57, 69, 73, 92, 89, 86, 77,
  57, 51, 24, 22, 6, 7, 0, 1]

def a157Coeffs : List ℤ := [
  2, -1, 40, 19, 160, 170, 446, 483, 813, 933, 1084, 1149, 1038, 1055,
  805, 661, 650, 385, 668, 242, 604, 158, 181, -3, -262, -7, -286, 240,
  325, 582, 982, 695, 1271, 706, 1193, 957, 1130, 1410, 1166, 1683, 1166,
  1410, 1130, 957, 1193, 706, 1271, 695, 982, 582, 325, 240, -286, -7,
  -262, -3, 181, 158, 604, 242, 668, 385, 650, 661, 805, 1055, 1038, 1149,
  1084, 933, 813, 483, 446, 170, 160, 19, 40, -1, 2]

def phi314Coeffs : List ℤ := [
  1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1,
  1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1,
  1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1,
  1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1,
  1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1,
  1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1,
  1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1,
  1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1,
  1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1]

def b13 (t : ℤ) : ℤ := evalCoeffs b13Coeffs t
def q72 (t : ℤ) : ℤ := evalCoeffs q72Coeffs t
def b157 (t : ℤ) : ℤ := evalCoeffs b157Coeffs t
def a157 (t : ℤ) : ℤ := evalCoeffs a157Coeffs t
def phi314 (t : ℤ) : ℤ := evalCoeffs phi314Coeffs t

/-- The exact scalar composition `B₁₅₇(T,1) = B₁₃(T,1) Q₇₂(T,1)`. -/
theorem b157_eq_b13_mul_q72 (t : ℤ) : b157 t = b13 t * q72 t := by
  simp [b157, b13, q72, b157Coeffs, b13Coeffs, q72Coeffs, evalCoeffs]
  ring

/-- The univariate specialization of
`4 Φ₃₁₄ = A₁₅₇² - 157 B₁₅₇²`. -/
theorem quadratic_fold (t : ℤ) :
    4 * phi314 t = a157 t ^ 2 - 157 * b157 t ^ 2 := by
  simp only [phi314, a157, b157, phi314Coeffs, a157Coeffs, b157Coeffs,
    evalCoeffs]
  ring

/-! ## Fold 5: exact branch alignment -/

theorem quadratic_branch_norm :
    74 ^ 2 + 74 * 11 - 39 * 11 ^ 2 = 1571 := by
  norm_num

theorem quadratic_branch_mod_1571 :
    (74 : ZMod 1571) + 11 * 993 = 0 := by
  decide

theorem cubic_branch_values :
    ((23 : ZMod 1571) - 19 * 640 + 640 ^ 2 = 0) ∧
      ((23 : ZMod 1571) - 19 * 494 + 494 ^ 2 = 594) ∧
      ((23 : ZMod 1571) - 19 * 436 + 436 ^ 2 = 1170) := by
  decide

/-- Algebraic content of the package's pre-projection three-channel
identity, with denominators cleared. -/
theorem threeChannelIdentity (a₀ d₀ a₁ d₁ a₂ d₂ : ℤ) :
    4 * (a₀ * a₁ * a₂ - d₀ * d₁ * d₂) =
      (a₀ - d₀) * (a₁ + d₁) * (a₂ + d₂) +
      (a₀ + d₀) * (a₁ - d₁) * (a₂ + d₂) +
      (a₀ + d₀) * (a₁ + d₁) * (a₂ - d₂) +
      (a₀ - d₀) * (a₁ - d₁) * (a₂ - d₂) := by
  ring

/-! ## Fold 6: first case and the two-probe shape -/

/-- Machine-readable description of the finite real-class probe loop.  The
determinant values are the package's externally verified CSV results; this
record does not silently promote them to a Lean theorem about class numbers. -/
structure ProbeLoop where
  count : ℕ
  localPrime : ℕ
  globalPrime : ℕ
  reportedLocalDet : ZMod 157
  reportedGlobalDet : ZMod 157
  count_eq_two : count = 2
  localPrime_eq : localPrime = 1571
  globalPrime_eq : globalPrime = 7537
  localDet_eq : reportedLocalDet = 0
  globalDet_eq : reportedGlobalDet = 74

def probeLoop : ProbeLoop where
  count := 2
  localPrime := 1571
  globalPrime := 7537
  reportedLocalDet := 0
  reportedGlobalDet := 74
  count_eq_two := rfl
  localPrime_eq := rfl
  globalPrime_eq := rfl
  localDet_eq := rfl
  globalDet_eq := rfl

theorem probeLoop_globalDet_ne_zero : probeLoop.reportedGlobalDet ≠ 0 := by
  decide

/-! ## Fold 7: the two correction-channel indices -/

def irregularChannels : Finset ℕ := {62, 110}

theorem irregularChannels_spec :
    ∀ j ∈ irregularChannels, 2 ≤ j ∧ j ≤ 154 ∧ Even j := by
  intro j hj
  simp only [irregularChannels, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl <;> norm_num

end Fermat.OneHundredFiftySeven.FoldCertificates
