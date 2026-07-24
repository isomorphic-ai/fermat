import Fermat.OneThousandEightHundredThirtyOne.HighBernoulli
import Fermat.OneThousandEightHundredThirtyOne.IrregularScanCertificate

/-!
# Compact irregular-index scan at exponent 1831

The paired four-digit proof package reports the single irregular channel
`{1274}`. Rather than expand exact rational Bernoulli numbers through
`B₁₈₂₈`, this module checks the equivalent depth-one Voronoi residues modulo
`1831`.

There are `914` even indices in the classical scan range. The finite theorem
below assembles their serialized kernel computations and proves the
implication needed by the direct high-Bernoulli certificate.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.IrregularScan

open Fermat.Irregular.ModularBernoulliScan
open Fermat.Irregular.VandiverData

local instance : Fact (Nat.Prime 1831) := ⟨by norm_num⟩

private theorem even_index_eq_scanIndex
    (k : ℕ) (hk2 : 2 ≤ k) (hk1828 : k ≤ 1828) (hkeven : Even k) :
    ∃ i : Fin 914, scanIndex i = k := by
  obtain ⟨r, hr⟩ := hkeven
  let i : Fin 914 := ⟨r - 1, by omega⟩
  refine ⟨i, ?_⟩
  simp only [scanIndex, i]
  omega

/-- Every noncandidate index in the classical range has nonzero Voronoi
residue modulo `1831`. -/
theorem scanResidue_ne_zero_outside_channel
    (k : ℕ) (hk : k ∈ indices 1831)
    (hnot : k ∉ ({1274} : Finset ℕ)) :
    scanResidue 1831 3 k ≠ 0 := by
  have hbounds : 2 ≤ k ∧ k ≤ 1828 ∧ Even k := by
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
    Fermat.OneThousandEightHundredThirtyOne.HighBernoulli.CompleteIrregularScan := by
  intro j hj hirregular
  have hmem : j ∈ ({1274} : Finset ℕ) :=
    bernoulli_numerator_dvd_imp_mem_candidates
      (p := 1831) (a := 3) (by norm_num) (by norm_num)
      {1274} scanResidue_ne_zero_outside_channel
      j hj hirregular
  simpa only [Finset.mem_singleton] using hmem

/-- The compact low scan and direct Faulhaber certificate prove the full
finite-channel Bernoulli cube condition at exponent `1831`. -/
theorem bernoulliCubeCondition_1831 : BernoulliCubeCondition 1831 :=
  Fermat.OneThousandEightHundredThirtyOne.HighBernoulli.bernoulliCubeCondition_of_completeIrregularScan
    completeIrregularScan

end Fermat.OneThousandEightHundredThirtyOne.IrregularScan
