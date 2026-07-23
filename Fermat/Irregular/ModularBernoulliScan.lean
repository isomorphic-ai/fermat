import Fermat.Irregular.VandiverData

/-!
# Modular low-Bernoulli scans

For a prime `p`, the classical irregular-index scan asks which even
Bernoulli numerators in the range `2 ≤ k ≤ p - 3` are divisible by `p`.
Expanding the Bernoulli recurrence over `ℚ` is a poor finite certificate at
four-digit primes: the exact numerators grow much faster than the modular
information being measured.

This file packages the finite alternative already implicit in the formal
Voronoi proof.  At depth one, Voronoi identifies

`(a^k - 1) * B_k / k`

modulo `p` with an integer quotient-weighted power sum.  Consequently, if
the finite sum is nonzero modulo `p`, then `p` cannot divide the numerator
of `B_k`.  A complete low scan can therefore retain only the small modular
residues and the exceptional candidate indices.

The result is unconditional: it consumes the proved Voronoi theorem in
`KummerTheorem`, not an imported Bernoulli-congruence oracle.
-/

namespace Fermat.Irregular.ModularBernoulliScan

open Fermat.Irregular.BernoulliData
open Fermat.Irregular.Voronoi

/-- The depth-one Voronoi residue used by a modular irregular-index scan. -/
def scanResidue (p a k : ℕ) : ZMod p :=
  quotientPowerSum p 1 a k

/-- An integer cast with positive `p`-adic valuation is zero modulo `p`. -/
private theorem intCast_zmod_eq_zero_of_hasPadicValAtLeast_one
    {p : ℕ} [Fact p.Prime] {z : ℤ}
    (hz : HasPadicValAtLeast p 1 (z : ℚ)) :
    (z : ZMod p) = 0 := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd z p).2
  rcases hz with hz | hz
  · have hz' : z = 0 := by exact_mod_cast hz
    subst z
    exact dvd_zero _
  · rw [padicValRat.of_int] at hz
    simpa using (padicValInt_dvd_iff 1 z).2 (Or.inr (by
      exact_mod_cast hz))

/-- A nonzero depth-one Voronoi residue excludes divisibility of the
corresponding low Bernoulli numerator.

The bounds `0 < k < p - 1` ensure simultaneously that the Bernoulli
denominator and the normalizing index `k` are prime to `p`. -/
theorem bernoulli_numerator_not_dvd_of_scanResidue_ne_zero
    {p a k : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hk : 0 < k) (hklt : k < p - 1)
    (hkeven : Even k) (ha : a.Coprime p)
    (hscan : scanResidue p a k ≠ 0) :
    ¬(p : ℤ) ∣ (bernoulli k).num := by
  intro hdvd
  have hnotPeriod : ¬(p - 1) ∣ k := by
    intro hperiod
    have hle := Nat.le_of_dvd hk hperiod
    omega
  have hden : DenominatorPrimeTo p (bernoulli k) :=
    bernoulli_denominatorPrimeTo hkeven hnotPeriod
  have hpk : ¬p ∣ k := by
    intro hdiv
    have hle := Nat.le_of_dvd hk hdiv
    omega
  have hBk : HasPadicValAtLeast p 1 (bernoulli k / (k : ℚ)) := by
    by_cases hBzero : bernoulli k = 0
    · left
      simp [hBzero]
    · right
      have hBval : (1 : ℤ) ≤ padicValRat p (bernoulli k) :=
        (numerator_pow_dvd_iff_le_padicValRat
          (p := p) (n := 1) hBzero hden).1 (by simpa using hdvd)
      rw [padicValRat.div hBzero (Nat.cast_ne_zero.mpr hk.ne'),
        padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hpk]
      simpa using hBval
  have hcoefficient :
      HasPadicValAtLeast p 0 (((a : ℚ) ^ k) - 1) := by
    have hint :
        HasPadicValAtLeast p 0 ((((a : ℤ) ^ k) - 1 : ℤ) : ℚ) :=
      HasPadicValAtLeast.intCast (((a : ℤ) ^ k) - 1)
    simpa only [Int.cast_sub, Int.cast_pow, Int.cast_natCast,
      Int.cast_one] using hint
  have hproduct :
      HasPadicValAtLeast p 1
        ((((a : ℚ) ^ k) - 1) * (bernoulli k / (k : ℚ))) := by
    simpa using hcoefficient.mul hBk
  have hkVal : padicValNat p k ≤ 0 := by
    rw [padicValNat.eq_zero_of_not_dvd hpk]
  have hvoronoi :
      HasPadicValAtLeast p 1
        ((((a : ℚ) ^ k) - 1) * (bernoulli k / (k : ℚ)) -
          (quotientPowerSum p 1 a k : ℚ)) := by
    simpa using normalized_voronoi_hasPadicValAtLeast_one
      (p := p) (s := 0) hp5 ha hk hkeven hkVal
  have hsum :
      HasPadicValAtLeast p 1
        (quotientPowerSum p 1 a k : ℚ) := by
    have h := hproduct.sub hvoronoi
    convert h using 1
    ring
  exact hscan <| by
    simpa only [scanResidue] using
      intCast_zmod_eq_zero_of_hasPadicValAtLeast_one hsum

/-- A finite residue scan outside a candidate set gives exactly the
implication needed by the Kummer--Vandiver reduction. -/
theorem bernoulli_numerator_dvd_imp_mem_candidates
    {p a : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (ha : a.Coprime p)
    (candidates : Finset ℕ)
    (hscan : ∀ k ∈ Fermat.Irregular.VandiverData.indices p,
      k ∉ candidates → scanResidue p a k ≠ 0) :
    ∀ k ∈ Fermat.Irregular.VandiverData.indices p,
      (p : ℤ) ∣ (bernoulli k).num → k ∈ candidates := by
  intro k hk hdvd
  by_contra hnot
  have hbounds : 2 ≤ k ∧ k ≤ p - 3 ∧ Even k := by
    simpa [Fermat.Irregular.VandiverData.indices, and_assoc] using hk
  exact bernoulli_numerator_not_dvd_of_scanResidue_ne_zero
    hp5 (by omega) (by omega) hbounds.2.2 ha (hscan k hk hnot) hdvd

end Fermat.Irregular.ModularBernoulliScan
