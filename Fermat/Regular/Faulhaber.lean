import Fermat.Irregular.Voronoi

/-!
# Direct Faulhaber certificates for regular Bernoulli indices

For a prime `p ≥ 5` and an even index `2 ≤ k ≤ p - 3`, Faulhaber's
formula gives

`sum (m = 1, ..., p - 1) m^k = p * B_k (mod p^2)`.

Consequently, a finite computation showing that the power sum is not
divisible by `p^2` proves that `p` does not divide the reduced numerator of
`B_k`.  This is the decompressed, per-index side of the Bernoulli layer: it
does not use Kummer's congruence.

The predicate `BernoulliNumeratorRegular` deliberately has a different name
from `IsRegularPrime`.  The latter is defined by the cyclotomic class number;
identifying it with this Bernoulli condition is Kummer's deeper regular-prime
criterion and is not presently available in Mathlib.
-/

namespace Fermat.Regular.Faulhaber

open Fermat.Irregular.BernoulliData
open Fermat.Irregular.Voronoi

/-- The low, positive, even Bernoulli indices in Kummer's regularity range. -/
def regularIndices (p : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (p - 3)).filter Even

/-- The numerical Bernoulli condition traditionally used to detect a
regular prime.  This is only the numerator statement, not the class-group
predicate `IsRegularPrime`. -/
def BernoulliNumeratorRegular (p : ℕ) : Prop :=
  ∀ k ∈ regularIndices p, ¬(p : ℤ) ∣ (bernoulli k).num

/-- The integer power sum occurring in the direct Faulhaber certificate. -/
def powerSum (p k : ℕ) : ℤ :=
  ∑ m ∈ Finset.Ico 1 p, (m : ℤ) ^ k

/-- A nonzero power-sum residue modulo `p^2` forces the numerator of `B_k`
to be nonzero modulo `p`.

The proof uses only the square-modulus Faulhaber remainder estimate and
von Staudt--Clausen denominator control. -/
theorem bernoulli_numerator_not_dvd_of_powerSum_not_dvd_sq
    {p k : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hk : 0 < k) (hkeven : Even k)
    (hindex : ¬(p - 1) ∣ k)
    (hsum : ¬(p : ℤ) ^ 2 ∣ powerSum p k) :
    ¬(p : ℤ) ∣ (bernoulli k).num := by
  intro hnum
  have hden : DenominatorPrimeTo p (bernoulli k) :=
    bernoulli_denominatorPrimeTo hkeven hindex
  have hB : HasPadicValAtLeast p 1 (bernoulli k) := by
    by_cases hzero : bernoulli k = 0
    · exact Or.inl hzero
    · right
      exact (numerator_pow_dvd_iff_le_padicValRat hzero hden).mp (by
        simpa using hnum)
  have hp : HasPadicValAtLeast p 1 (p : ℚ) := by
    simpa using HasPadicValAtLeast.primePow (p := p) 1
  have hpB : HasPadicValAtLeast p 2 ((p : ℚ) * bernoulli k) := by
    simpa using hp.mul hB
  have happrox : HasPadicValAtLeast p 2
      ((powerSum p k : ℚ) - (p : ℚ) * bernoulli k) := by
    simpa [powerSum] using
      powerSum_sub_bernoulli_primePower_hasPadicValAtLeast
        (p := p) (t := 1) hp5 (by omega) hk hkeven
  have hsumVal : HasPadicValAtLeast p 2 (powerSum p k : ℚ) := by
    have h := happrox.add hpB
    convert h using 1
    ring
  apply hsum
  rcases hsumVal with hzero | hval
  · have hzero' : powerSum p k = 0 := by
      exact_mod_cast hzero
    simp [hzero']
  · rw [padicValRat.of_int] at hval
    exact (padicValInt_dvd_iff 2 (powerSum p k)).mpr (Or.inr (by
      exact_mod_cast hval))

/-- Bundle one square-modulus power-sum certificate at every low even index
into the complete numerical Bernoulli regularity condition. -/
theorem bernoulliNumeratorRegular_of_powerSums
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hsums : ∀ k ∈ regularIndices p,
      ¬(p : ℤ) ^ 2 ∣ powerSum p k) :
    BernoulliNumeratorRegular p := by
  intro k hk
  have hk' : 2 ≤ k ∧ k ≤ p - 3 ∧ Even k := by
    simpa [regularIndices, and_assoc] using hk
  apply bernoulli_numerator_not_dvd_of_powerSum_not_dvd_sq
    hp5 (by omega) hk'.2.2
  · intro hdiv
    have hle : p - 1 ≤ k :=
      Nat.le_of_dvd (by omega : 0 < k) hdiv
    omega
  · exact hsums k hk

end Fermat.Regular.Faulhaber
