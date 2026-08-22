import Fermat.Descent.Irregular.DirectBernoulli

/-!
# Exact valuations from direct Faulhaber certificates

This module exposes the exact valuation carried by the direct power-sum
certificate in `Fermat.Irregular.DirectBernoulli`.  It is prime-generic and
contains no exponent-specific data.

The parameter `chooseQuotient` is the quotient in the relevant binomial
coefficient.  The parameter `residue` is the power-sum residue after removing
one leading factor of `p`; in a lifted irregular channel it has valuation two.
-/

namespace Fermat.GenericIrregular.ExactFaulhaberValuation

open Fermat.Irregular.DirectBernoulli

/-- A Faulhaber residue below precision `p^3` determines the exact
`p`-adic valuation of the target Bernoulli number. -/
theorem bernoulli_padicValRat_eq_of_faulhaber
    {p n chooseQuotient residue : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hn : 6 ≤ n) (heven : Even n)
    (hdenNext : ¬p ∣ n + 1)
    (hprev : PIntegral p (bernoulli (n - 2)))
    (hchoose :
      (n + 1).choose (n - 2) = p * chooseQuotient)
    (hmod : (∑ a ∈ Finset.range p,
      (a : ZMod (p ^ 4)) ^ n) = p * residue)
    (hresidue0 : residue ≠ 0)
    (hresidueLt : padicValRat p (residue : ℚ) < 3) :
    padicValRat p (bernoulli n) =
      padicValRat p (residue : ℚ) := by
  obtain ⟨u, hu, hB⟩ :=
    bernoulli_representation_of_faulhaber
      hp5 hn heven hdenNext hprev hchoose hmod
  exact
    (representation_ne_zero_and_padicValRat_eq
      hresidue0 hu hB hresidueLt).2

/-- In a lifted irregular channel, a residue of valuation two proves that
the target Bernoulli number has valuation exactly two. -/
theorem bernoulli_padicValRat_eq_two_of_faulhaber
    {p n chooseQuotient residue : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hn : 6 ≤ n) (heven : Even n)
    (hdenNext : ¬p ∣ n + 1)
    (hprev : PIntegral p (bernoulli (n - 2)))
    (hchoose :
      (n + 1).choose (n - 2) = p * chooseQuotient)
    (hmod : (∑ a ∈ Finset.range p,
      (a : ZMod (p ^ 4)) ^ n) = p * residue)
    (hresidue0 : residue ≠ 0)
    (hresidueVal : padicValRat p (residue : ℚ) = 2) :
    padicValRat p (bernoulli n) = 2 := by
  have hresidueLt : padicValRat p (residue : ℚ) < 3 := by
    omega
  exact
    (bernoulli_padicValRat_eq_of_faulhaber
      hp5 hn heven hdenNext hprev hchoose hmod
      hresidue0 hresidueLt).trans hresidueVal

end Fermat.GenericIrregular.ExactFaulhaberValuation
