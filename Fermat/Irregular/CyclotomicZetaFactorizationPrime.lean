import Fermat.Irregular.MaximalRealSplittingPrime
import Fermat.Irregular.PrimePowerIdealCount
import Fermat.Irregular.RamifiedLocalFactorPrime

/-!
# Artin factorization for maximal real prime cyclotomic fields

This file combines the generic unramified splitting law, the multichoose
ideal-count formula, and the generic ramified local factor.  It proves the
Dedekind-zeta factorization for the maximal real subfield of every odd-prime
cyclotomic field.
-/

open scoped NumberField Classical

namespace Fermat.Irregular.CyclotomicZetaFactorizationPrime

noncomputable section

open Fermat.Irregular.CyclotomicCharactersPrime
open Fermat.Irregular.CyclotomicZetaCoefficientsPrime
open Fermat.Irregular.PrimePowerIdealCount
open Fermat.Irregular.MaximalRealSplittingPrime
open Fermat.Irregular.RamifiedLocalFactorPrime
open Fermat.Irregular.CircularUnitFamily

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 < p)]
variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K] [IsAbelianGalois ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- At every unramified rational prime, the actual and character-predicted
prime-power coefficients agree. -/
theorem idealCount_eq_expected_primePow_of_coprime
    (q k : ℕ) (hq : q.Prime) (hcop : q.Coprime p) :
    idealCount K⁺ (q ^ k) =
      expectedIdealCount (p := p) (q ^ k) := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have hnorm : ∀ P ∈ (rationalPrimeIdeal q).primesOver
      (NumberField.RingOfIntegers K⁺),
      Ideal.absNorm P =
        q ^ orderOf (realResidueOfCoprime q hcop) := by
    intro P hP
    letI : P.IsPrime := hP.1
    letI : P.LiesOver (rationalPrimeIdeal q) := hP.2
    exact absNorm_primeOver_maximalReal
      (p := p) (K := K) q hcop P
  have hcard :
      ((rationalPrimeIdeal q).primesOver
        (NumberField.RingOfIntegers K⁺)).ncard =
        ((p - 1) / 2) /
          orderOf (realResidueOfCoprime q hcop) :=
    ncard_primesOver_maximalReal
      (p := p) (K := K) q hcop
  change Fermat.Irregular.IdealCount.idealCountArithmetic
      (S := NumberField.RingOfIntegers K⁺) (q ^ k) = _
  rw [idealCountArithmetic_prime_pow_eq_multichoose q
    (orderOf (realResidueOfCoprime q hcop)) k hq
    (orderOf_pos _) hnorm]
  rw [expectedIdealCount_primePow_of_coprime
    (p := p) q k hq hcop]
  rw [hcard]

/-- The actual and predicted coefficients agree at every rational prime
power, including the ramified prime p. -/
theorem idealCount_eq_expected_primePow
    (q k : ℕ) (hq : q.Prime) :
    idealCount K⁺ (q ^ k) =
      expectedIdealCount (p := p) (q ^ k) := by
  by_cases hqp : q = p
  · subst q
    exact idealCount_eq_expected_p_pow (p := p) (K := K) k
  · letI : Fact (Nat.Prime q) := ⟨hq⟩
    exact idealCount_eq_expected_primePow_of_coprime
      (p := p) (K := K) q k hq
        (prime_coprime_exponent q hqp)

/-- The ideal-counting arithmetic function is the convolution predicted by
all even characters. -/
theorem idealCount_eq_expected :
    idealCount K⁺ = expectedIdealCount (p := p) :=
  idealCount_eq_expected_of_primePowers
    (fun q k hq ↦
      idealCount_eq_expected_primePow (p := p) (K := K) q k hq)

/-- Artin factorization, given the canonical CM and Galois instances. -/
theorem cyclotomicZetaFactorization :
    CyclotomicZetaFactorization (p := p) K :=
  cyclotomicZetaFactorization_of_idealCount_eq_expected
    (idealCount_eq_expected (p := p) (K := K))

/-- Unconditional Artin factorization for an odd-prime cyclotomic field.
The required CM and abelian-Galois structures are constructed internally. -/
theorem cyclotomicZetaFactorization_of_cyclotomic
    {r : ℕ} [Fact (Nat.Prime r)] [Fact (2 < r)]
    {L : Type*} [Field L] [NumberField L]
    [IsCyclotomicExtension {r} ℚ L] :
    CyclotomicZetaFactorization (p := r) L := by
  letI : NumberField.IsCMField L :=
    cyclotomicPrime_isCMField (K := L)
      (Fact.out : Nat.Prime r) (by
        have hrgt : 2 < r := Fact.out
        omega)
  letI : IsAbelianGalois ℚ L :=
    (IsCyclotomicExtension.isAbelianGalois
      ({r} : Set ℕ) ℚ L : IsAbelianGalois ℚ L)
  exact cyclotomicZetaFactorization (p := r) (K := L)

end

end Fermat.Irregular.CyclotomicZetaFactorizationPrime
