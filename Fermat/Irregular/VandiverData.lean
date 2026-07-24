import Fermat.Irregular.KummerTheorem

/-!
# The finite Bernoulli data in Vandiver's second-case criterion

Vandiver's criterion asks that `p ^ 3` not divide the numerator of
`B_(j*p)` for every even `j` in the classical range `2 ≤ j ≤ p - 3`.
This file packages that finite condition and proves the reusable Kummer
reduction: regular indices are automatic from Kummer's congruence, so only
the irregular indices require high Bernoulli computations.

This is a reduction of the numerical hypotheses.  It is not the global
singular-primary-unit theorem that turns those hypotheses and `p ∤ h⁺` into
an exclusion of Case II.
-/

namespace Fermat.Irregular.VandiverData

/-- The even indices occurring in Vandiver's Case-II criterion. -/
def indices (p : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (p - 3)).filter Even

/-- The all-index Bernoulli numerator condition in Vandiver's criterion. -/
def BernoulliCubeCondition (p : ℕ) : Prop :=
  ∀ j ∈ indices p, ¬(p : ℤ) ^ 3 ∣ (bernoulli (j * p)).num

/-- Kummer's congruence discharges every regular index.  Consequently, to
prove Vandiver's all-index condition it is enough to check the high Bernoulli
number only at indices where `p` divides the numerator of `B_j`.

The explicit hypotheses `hKummer` make this reduction usable with any
source of Kummer congruences; `hIrregular` contains only the exceptional
finite computations.  The theorem below supplies `hKummer` unconditionally
from the Voronoi--Kummer theorem. -/
theorem bernoulliCubeCondition_of_kummer_of_irregular
    {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (hKummer : ∀ j ∈ indices p,
      KummerCongruenceModPrime p j (j * p))
    (hIrregular : ∀ j ∈ indices p,
      (p : ℤ) ∣ (bernoulli j).num →
        ¬(p : ℤ) ^ 3 ∣ (bernoulli (j * p)).num) :
    BernoulliCubeCondition p := by
  intro j hj
  have hj' : 2 ≤ j ∧ j ≤ p - 3 ∧ Even j := by
    simpa [indices, and_assoc] using hj
  by_cases hirregular : (p : ℤ) ∣ (bernoulli j).num
  · exact hIrregular j hj hirregular
  · have hBj : bernoulli j ≠ 0 := by
      intro hzero
      apply hirregular
      rw [hzero]
      simp
    exact regularIndex_bernoulli_mul_prime_numerator_not_dvd_cube
      hp hj'.1 hj'.2.1 hj'.2.2 hBj hirregular (hKummer j hj)

/-- The unconditional Kummer reduction: for a prime `p ≥ 5`, only the
irregular low indices need a separate high-Bernoulli computation.

All regular indices are discharged by the formal Voronoi proof of Kummer's
congruence in `KummerTheorem`. -/
theorem bernoulliCubeCondition_of_irregular
    {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (hIrregular : ∀ j ∈ indices p,
      (p : ℤ) ∣ (bernoulli j).num →
        ¬(p : ℤ) ^ 3 ∣ (bernoulli (j * p)).num) :
    BernoulliCubeCondition p := by
  apply bernoulliCubeCondition_of_kummer_of_irregular hp
  · intro j hj
    have hj' : 2 ≤ j ∧ j ≤ p - 3 ∧ Even j := by
      simpa [indices, and_assoc] using hj
    exact KummerTheorem.kummerCongruenceModPrime_irregularRange
      hp hj'.1 hj'.2.1 hj'.2.2
  · exact hIrregular

end Fermat.Irregular.VandiverData
