import Fermat.SixHundredNinetyOne.HighBernoulli
import Fermat.Irregular.ModularBernoulliScan

/-!
# Compact irregular-index scan at exponent 691

The uploaded paired four-digit folding package reports candidate channels
`{12, 200}`.  Expanding the exact rational Bernoulli recurrence through
`B₆₈₈` produces needlessly enormous certificates.  This file instead checks
the equivalent depth-one Voronoi residues modulo `691`.

There are exactly `344` even indices in the scan range.  The finite theorem
below evaluates all of them in the kernel and proves only the implication
needed here: a zero residue can occur only at one of the two package
candidates.  The shared modular-scan theorem then turns every nonzero residue
into Bernoulli-numerator nondivisibility.
-/

namespace Fermat.SixHundredNinetyOne.IrregularScan

open Fermat.Irregular.ModularBernoulliScan
open Fermat.Irregular.VandiverData

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 700

local instance : Fact (Nat.Prime 691) := ⟨by norm_num⟩

/-- The `i`-th even index in the classical range `2 ≤ k ≤ 688`. -/
def scanIndex (i : Fin 344) : ℕ := 2 * (i + 1)

/-- Kernel-checked compact scan: only the two package candidates can have
zero depth-one Voronoi residue.  This implication does not assert that either
candidate actually has zero residue. -/
theorem scanResidue_zero_only_at_two_channels (i : Fin 344) :
    scanResidue 691 3 (scanIndex i) = 0 →
      scanIndex i = 12 ∨ scanIndex i = 200 := by
  decide +revert

private theorem even_index_eq_scanIndex
    (k : ℕ) (hk2 : 2 ≤ k) (hk688 : k ≤ 688) (hkeven : Even k) :
    ∃ i : Fin 344, scanIndex i = k := by
  obtain ⟨r, hr⟩ := hkeven
  let i : Fin 344 := ⟨r - 1, by omega⟩
  refine ⟨i, ?_⟩
  simp only [scanIndex, i]
  omega

/-- Every noncandidate index in the classical range has nonzero Voronoi
residue modulo `691`. -/
theorem scanResidue_ne_zero_outside_two_channels
    (k : ℕ) (hk : k ∈ indices 691)
    (hnot : k ∉ ({12, 200} : Finset ℕ)) :
    scanResidue 691 3 k ≠ 0 := by
  have hbounds : 2 ≤ k ∧ k ≤ 688 ∧ Even k := by
    simpa [indices, and_assoc] using hk
  obtain ⟨i, hi⟩ :=
    even_index_eq_scanIndex k hbounds.1 hbounds.2.1 hbounds.2.2
  intro hzero
  have hchannels :=
    scanResidue_zero_only_at_two_channels i (hi ▸ hzero)
  rw [hi] at hchannels
  apply hnot
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hchannels

/-- The complete implication-form low scan consumed by the two high
Bernoulli certificates. -/
theorem completeIrregularScan :
    Fermat.SixHundredNinetyOne.HighBernoulli.CompleteIrregularScan := by
  intro j hj hirregular
  have hmem : j ∈ ({12, 200} : Finset ℕ) :=
    bernoulli_numerator_dvd_imp_mem_candidates
      (p := 691) (a := 3) (by norm_num) (by norm_num)
      {12, 200} scanResidue_ne_zero_outside_two_channels
      j hj hirregular
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem

/-- The compact low scan and the two direct Faulhaber certificates prove the
full finite-channel Bernoulli cube condition at exponent `691`. -/
theorem bernoulliCubeCondition_691 : BernoulliCubeCondition 691 :=
  Fermat.SixHundredNinetyOne.HighBernoulli.bernoulliCubeCondition_of_completeIrregularScan
    completeIrregularScan

end Fermat.SixHundredNinetyOne.IrregularScan
