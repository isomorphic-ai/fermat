import Fermat.Irregular.MaximalRealSplitting37
import Fermat.Irregular.PrimePowerIdealCount
import Fermat.Irregular.RamifiedLocalFactor37

/-!
# Artin factorization for the maximal real 37th cyclotomic field

This file combines the unramified splitting law, the multichoose ideal-count
formula, and the ramified local factor at `37`.  The actual ideal-counting
arithmetic function of the maximal real subfield is therefore equal to the
convolution of the Riemann-zeta coefficient with the seventeen nontrivial even
Dirichlet-character coefficients.  Coefficientwise equality gives the complete
Dedekind-zeta factorization on `re s > 1`.
-/

open scoped NumberField Classical

namespace Fermat.Irregular.CyclotomicZetaFactorization37

noncomputable section

open Fermat.Irregular.CyclotomicZetaCoefficients37
open Fermat.Irregular.PrimePowerIdealCount
open Fermat.Irregular.MaximalRealSplitting37
open Fermat.Irregular.RamifiedLocalFactor37
open Fermat.Irregular.CyclotomicSinnottBridge37

local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {37} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- At every unramified rational prime, the actual and character-predicted
prime-power coefficients agree. -/
theorem idealCount_eq_expected_primePow_of_coprime
    (q k : ℕ) (hq : q.Prime) (hcop : q.Coprime 37) :
    idealCount K⁺ (q ^ k) = expectedIdealCount (q ^ k) := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have hnorm : ∀ P ∈ (rationalPrimeIdeal q).primesOver
      (NumberField.RingOfIntegers K⁺),
      Ideal.absNorm P = q ^ orderOf (realResidueOfCoprime37 q hcop) := by
    intro P hP
    letI : P.IsPrime := hP.1
    letI : P.LiesOver (rationalPrimeIdeal q) := hP.2
    exact absNorm_primeOver_maximalReal37 (K := K) q hcop P
  have hcard : ((rationalPrimeIdeal q).primesOver
      (NumberField.RingOfIntegers K⁺)).ncard =
      18 / orderOf (realResidueOfCoprime37 q hcop) :=
    ncard_primesOver_maximalReal37 (K := K) q hcop
  change Fermat.Irregular.IdealCount.idealCountArithmetic
      (S := NumberField.RingOfIntegers K⁺) (q ^ k) = _
  rw [idealCountArithmetic_prime_pow_eq_multichoose q
    (orderOf (realResidueOfCoprime37 q hcop)) k hq (orderOf_pos _) hnorm]
  rw [expectedIdealCount_primePow_of_coprime q k hq hcop]
  rw [hcard]

/-- The actual and predicted coefficients agree at every rational prime power,
including the ramified prime `37`. -/
theorem idealCount_eq_expected_primePow
    (q k : ℕ) (hq : q.Prime) :
    idealCount K⁺ (q ^ k) = expectedIdealCount (q ^ k) := by
  by_cases hq37 : q = 37
  · subst q
    exact idealCount_eq_expected_37_pow (K := K) k
  · have hnot : ¬ q ∣ 37 := by
      intro hdvd
      rcases (Nat.dvd_prime (by decide : Nat.Prime 37)).mp hdvd with hq1 | hqeq
      · exact hq.ne_one hq1
      · exact hq37 hqeq
    exact idealCount_eq_expected_primePow_of_coprime q k hq
      (hq.coprime_iff_not_dvd.mpr hnot)

/-- The ideal-counting arithmetic function of the maximal real field is the
predicted convolution of the eighteen even character coefficients. -/
theorem idealCount_eq_expected :
    idealCount K⁺ = expectedIdealCount :=
  idealCount_eq_expected_of_primePowers
    (fun q k hq ↦ idealCount_eq_expected_primePow (K := K) q k hq)

/-- The unconditional Artin factorization of the Dedekind zeta function of the
maximal real 37th cyclotomic field on `re s > 1`. -/
theorem cyclotomicZetaFactorization37 : CyclotomicZetaFactorization37 K :=
  cyclotomicZetaFactorization37_of_idealCount_eq_expected
    (idealCount_eq_expected (K := K))

end

end Fermat.Irregular.CyclotomicZetaFactorization37
