import Fermat.Exponents.SixHundredSeven.HighBernoulli
import Fermat.Descent.Irregular.ModularBernoulliScan

/-!
# Compact irregular-index scan at exponent 607

The paired `78233`/`94693` package reports the single irregular channel
`{592}`. Rather than expand exact rational Bernoulli numbers through
`B₆₀₄`, this module checks the equivalent depth-one Voronoi residues modulo
`607`.

There are exactly `302` even indices in the classical range. The finite
theorem evaluates all of them in the kernel and proves the implication
needed by the direct high-Bernoulli certificate.
-/

namespace Fermat.SixHundredSeven.IrregularScan

open Fermat.Irregular.ModularBernoulliScan
open Fermat.Irregular.VandiverData

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 700

local instance : Fact (Nat.Prime 607) := ⟨by norm_num⟩

/-- The `i`-th even index in the classical range `2 ≤ k ≤ 604`. -/
def scanIndex (i : Fin 302) : ℕ := 2 * (i + 1)

/-- Kernel-checked compact scan: only the package channel can have zero
depth-one Voronoi residue. -/
theorem scanResidue_zero_only_at_channel (i : Fin 302) :
    scanResidue 607 3 (scanIndex i) = 0 →
      scanIndex i = 592 := by
  decide +revert

/-- The reported candidate really has zero depth-one Voronoi residue. -/
theorem scanResidue_592_eq_zero :
    scanResidue 607 3 592 = 0 := by
  decide

private theorem even_index_eq_scanIndex
    (k : ℕ) (hk2 : 2 ≤ k) (hk604 : k ≤ 604) (hkeven : Even k) :
    ∃ i : Fin 302, scanIndex i = k := by
  obtain ⟨r, hr⟩ := hkeven
  let i : Fin 302 := ⟨r - 1, by omega⟩
  refine ⟨i, ?_⟩
  simp only [scanIndex, i]
  omega

/-- Every noncandidate index in the classical range has nonzero Voronoi
residue modulo `607`. -/
theorem scanResidue_ne_zero_outside_channel
    (k : ℕ) (hk : k ∈ indices 607)
    (hnot : k ∉ ({592} : Finset ℕ)) :
    scanResidue 607 3 k ≠ 0 := by
  have hbounds : 2 ≤ k ∧ k ≤ 604 ∧ Even k := by
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
    Fermat.SixHundredSeven.HighBernoulli.CompleteIrregularScan := by
  intro j hj hirregular
  have hmem : j ∈ ({592} : Finset ℕ) :=
    bernoulli_numerator_dvd_imp_mem_candidates
      (p := 607) (a := 3) (by norm_num) (by norm_num)
      {592} scanResidue_ne_zero_outside_channel
      j hj hirregular
  simpa only [Finset.mem_singleton] using hmem

/-- The compact low scan and direct Faulhaber certificate prove the full
finite-channel Bernoulli cube condition at exponent `607`. -/
theorem bernoulliCubeCondition_607 : BernoulliCubeCondition 607 :=
  Fermat.SixHundredSeven.HighBernoulli.bernoulliCubeCondition_of_completeIrregularScan
    completeIrregularScan

end Fermat.SixHundredSeven.IrregularScan
