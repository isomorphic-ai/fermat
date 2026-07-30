/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Exact depth of the selected high-flow certificate

The checked pole-safe Faulhaber table already gives every generated
high-eigenvalue depth at most two.  Its irregular row has corrected residue
equal to a nonzero multiple of the prime square, so that row attains depth
two exactly.
-/
import Fermat.Conservation.Credit.DepthCertificate
import Fermat.FiftyNine.Conservation.Instance

namespace Fermat.FiftyNine.Conservation.DepthCertificate

open Fermat.Conservation.Credit
open Fermat.FiftyNine.Conservation.Instance

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

private theorem bernoulli_representation
    (row : Fin gaugeData.rank) :
    ∃ u : ℚ, Bernoulli.PIntegral 59 u ∧
      bernoulli (RealFlow.highIndex (data := realGaugeData) row) =
        (BernoulliCertificate.correctedResidue row : ℚ) +
          (59 : ℚ) ^ 3 * u := by
  apply
    Bernoulli.exceptional_bernoulli_representation_of_faulhaber
      (p := 59)
      (n := RealFlow.highIndex (data := realGaugeData) row)
      (c := BernoulliCertificate.chooseQuotient row)
      (raw := BernoulliCertificate.rawPowerResidue row)
      (s := BernoulliCertificate.correctedResidue row)
      (q := BernoulliCertificate.predecessorResidue row)
      (w := BernoulliCertificate.correctionWeight row)
      (correctionLift := 0)
  · norm_num
  · dsimp [RealFlow.highIndex]
    omega
  · exact (even_two.mul_right (row.val + 1)).mul_right 59
  · intro hdvd
    obtain ⟨k, hk⟩ := hdvd
    dsimp [RealFlow.highIndex] at hk
    omega
  · exact BernoulliCertificate.choose_factor row
  · exact BernoulliCertificate.raw_power_sum row
  · exact BernoulliCertificate.predecessor_representation row
  · exact BernoulliCertificate.correction_weight_representation row
  · exact BernoulliCertificate.corrected_residue_normalization row

/-- The checked irregular row attains the square layer of the generated
high-eigenvalue family. -/
theorem highEigenvalue_square_attained :
    ∃ row : Fin realGaugeData.rank,
      (59 : ℤ) ^ 2 ∣
        RealFlow.highEigenvalue (data := realGaugeData) row := by
  let row : Fin gaugeData.rank :=
    ⟨21, by norm_num [gaugeData]⟩
  obtain ⟨u, hu, hB⟩ := bernoulli_representation row
  have hresidue0 :
      BernoulliCertificate.correctedResidue row ≠ 0 :=
    BernoulliCertificate.correctedResidue_ne_zero row
  have hresidueCube :
      ¬(59 : ℤ) ^ 3 ∣
        (BernoulliCertificate.correctedResidue row : ℤ) :=
    BernoulliCertificate.correctedResidue_cubeFree row
  have hresidueSquare :
      (59 : ℤ) ^ 2 ∣
        (BernoulliCertificate.correctedResidue row : ℤ) := by
    decide +kernel
  have hresidueDen :
      Bernoulli.DenominatorPrimeTo 59
        (BernoulliCertificate.correctedResidue row : ℚ) := by
    simp [Bernoulli.DenominatorPrimeTo]
  have hresidueValGe :
      (2 : ℤ) ≤
        padicValRat 59
          (BernoulliCertificate.correctedResidue row : ℚ) := by
    apply
      (Bernoulli.numerator_pow_dvd_iff_le_padicValRat
        (p := 59) (exponent := 2)
        (Nat.cast_ne_zero.mpr hresidue0) hresidueDen).mp
    simpa using hresidueSquare
  have hresidueValLt :
      padicValRat 59
          (BernoulliCertificate.correctedResidue row : ℚ) < 3 := by
    by_contra hnot
    apply hresidueCube
    have hle :
        (3 : ℤ) ≤
          padicValRat 59
            (BernoulliCertificate.correctedResidue row : ℚ) := by
      omega
    simpa using
      (Bernoulli.numerator_pow_dvd_iff_le_padicValRat
        (p := 59) (exponent := 3)
        (Nat.cast_ne_zero.mpr hresidue0) hresidueDen).mpr hle
  obtain ⟨hB0, hval⟩ :=
    Bernoulli.representation_ne_zero_and_padicValRat_eq
      hresidue0 hu hB hresidueValLt
  have htarget :=
    BernoulliCertificate.target_denominator row
  refine ⟨row, ?_⟩
  change
    (59 : ℤ) ^ 2 ∣
      (bernoulli
        (RealFlow.highIndex (data := realGaugeData) row)).num
  apply
    (Bernoulli.numerator_pow_dvd_iff_le_padicValRat
      (p := 59) (exponent := 2) hB0 htarget).mpr
  rw [hval]
  exact hresidueValGe

/-- The current selected data has exact Bernoulli correction depth two. -/
theorem depthTwoCertificate :
    RealFlow.DepthTwoCertificate realGaugeData :=
  RealFlow.DepthTwoCertificate.ofFlowCertificate
    flowCertificate highEigenvalue_square_attained

end Fermat.FiftyNine.Conservation.DepthCertificate
