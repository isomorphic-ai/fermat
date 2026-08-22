import Fermat.Exponents.OneThousandThreeHundredEightyOne.HighBernoulli
import Fermat.Exponents.OneThousandThreeHundredEightyOne.IrregularScanCertificate

/-!
# Compact irregular-index scan at exponent 1381

The paired four-digit proof package reports the single irregular channel
`{266}`.  Rather than expand exact rational Bernoulli numbers through
`B₁₃₇₈`, this module checks the equivalent depth-one Voronoi residues modulo
`1381`.

There are `689` even indices in the classical scan range.  The finite theorem
below evaluates all of them in the kernel and proves the implication needed
by the direct high-Bernoulli certificate.
-/

namespace Fermat.OneThousandThreeHundredEightyOne.IrregularScan

open Fermat.Irregular.ModularBernoulliScan
open Fermat.Irregular.VandiverData

local instance : Fact (Nat.Prime 1381) := ⟨by norm_num⟩

private theorem even_index_eq_scanIndex
    (k : ℕ) (hk2 : 2 ≤ k) (hk1378 : k ≤ 1378) (hkeven : Even k) :
    ∃ i : Fin 689, scanIndex i = k := by
  obtain ⟨r, hr⟩ := hkeven
  let i : Fin 689 := ⟨r - 1, by omega⟩
  refine ⟨i, ?_⟩
  simp only [scanIndex, i]
  omega

/-- Every noncandidate index in the classical range has nonzero Voronoi
residue modulo `1381`. -/
theorem scanResidue_ne_zero_outside_channel
    (k : ℕ) (hk : k ∈ indices 1381)
    (hnot : k ∉ ({266} : Finset ℕ)) :
    scanResidue 1381 2 k ≠ 0 := by
  have hbounds : 2 ≤ k ∧ k ≤ 1378 ∧ Even k := by
    simpa [indices, and_assoc] using hk
  obtain ⟨i, hi⟩ :=
    even_index_eq_scanIndex k hbounds.1 hbounds.2.1 hbounds.2.2
  intro hzero
  have hchannel :=
    scanResidue_zero_only_at_channel i (hi ▸ hzero)
  rw [hi] at hchannel
  apply hnot
  simpa only [Finset.mem_singleton] using hchannel

/-- The complete implication-form low scan consumed by the direct
high-Bernoulli certificate. -/
theorem completeIrregularScan :
    Fermat.OneThousandThreeHundredEightyOne.HighBernoulli.CompleteIrregularScan := by
  intro j hj hirregular
  have hmem : j ∈ ({266} : Finset ℕ) :=
    bernoulli_numerator_dvd_imp_mem_candidates
      (p := 1381) (a := 2) (by norm_num) (by norm_num)
      {266} scanResidue_ne_zero_outside_channel
      j hj hirregular
  simpa only [Finset.mem_singleton] using hmem

/-- The compact low scan and direct Faulhaber certificate prove the full
finite-channel Bernoulli cube condition at exponent `1381`. -/
theorem bernoulliCubeCondition_1381 : BernoulliCubeCondition 1381 :=
  Fermat.OneThousandThreeHundredEightyOne.HighBernoulli.bernoulliCubeCondition_of_completeIrregularScan
    completeIrregularScan

end Fermat.OneThousandThreeHundredEightyOne.IrregularScan
