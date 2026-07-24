import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.RingTheory.PowerSeries.Binomial

open scoped Classical BigOperators

namespace Fermat.Irregular.LocalEulerFactor

noncomputable section

open Finset

/-- The formal local series of an arithmetic function at `q`. -/
def primePowerSeries {R : Type*} [Semiring R]
    (q : ℕ) (a : ArithmeticFunction R) : PowerSeries R :=
  PowerSeries.mk fun k ↦ a (q ^ k)

@[simp] theorem coeff_primePowerSeries {R : Type*} [Semiring R]
    (q : ℕ) (a : ArithmeticFunction R) (k : ℕ) :
    PowerSeries.coeff k (primePowerSeries q a) = a (q ^ k) := by
  simp [primePowerSeries]

/-- At a prime, passage from arithmetic functions to their prime-power
coefficient series respects Dirichlet convolution. -/
theorem primePowerSeries_mul {R : Type*} [CommSemiring R]
    {q : ℕ} (hq : q.Prime) (a b : ArithmeticFunction R) :
    primePowerSeries q (a * b) = primePowerSeries q a * primePowerSeries q b := by
  apply PowerSeries.ext
  intro k
  rw [coeff_primePowerSeries, ArithmeticFunction.mul_apply]
  rw [Nat.sum_divisorsAntidiagonal (fun i j ↦ a i * b j),
    Nat.sum_divisors_prime_pow hq]
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j ↦ PowerSeries.coeff i (primePowerSeries q a) *
        PowerSeries.coeff j (primePowerSeries q b)) k]
  apply Finset.sum_congr rfl
  intro i hi
  rw [coeff_primePowerSeries, coeff_primePowerSeries]
  rw [Nat.pow_div (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hq.pos]

theorem primePowerSeries_one {R : Type*} [CommSemiring R]
    {q : ℕ} (hq : q.Prime) :
    primePowerSeries q (1 : ArithmeticFunction R) = 1 := by
  apply PowerSeries.ext
  intro k
  rcases k with _ | k
  · simp [primePowerSeries]
  · simp [primePowerSeries, ArithmeticFunction.one_apply, hq.ne_one]

theorem primePowerSeries_finset_prod {R : Type*} [CommSemiring R]
    {alpha : Type*} [DecidableEq alpha] {q : ℕ} (hq : q.Prime)
    (S : Finset alpha) (a : alpha → ArithmeticFunction R) :
    primePowerSeries q (∏ i ∈ S, a i) = ∏ i ∈ S, primePowerSeries q (a i) := by
  induction S using Finset.induction_on with
  | empty => simp [primePowerSeries_one hq]
  | @insert i S hi ih =>
      rw [prod_insert hi, prod_insert hi, primePowerSeries_mul hq, ih]

end

end Fermat.Irregular.LocalEulerFactor
