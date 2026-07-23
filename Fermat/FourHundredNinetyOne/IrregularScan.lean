import Fermat.FourHundredNinetyOne.HighBernoulli
import Fermat.Irregular.ModularBernoulliScan

/-!
# Compact irregular-index scan at exponent 491

The uploaded three-loop package reports the three irregular channels
`{292, 336, 338}`.  Expanding the exact rational Bernoulli recurrence through
`B₄₈₈` produces needlessly enormous certificates.  This file instead checks
the equivalent depth-one Voronoi residues modulo `491`.

There are exactly `244` even indices in the scan range.  The finite theorem
below evaluates all of them in the kernel and proves that a zero residue can
occur only at the three package channels.  The shared modular-scan theorem
then turns every nonzero residue into Bernoulli-numerator nondivisibility.
-/

namespace Fermat.FourHundredNinetyOne.IrregularScan

open Fermat.Irregular.ModularBernoulliScan
open Fermat.Irregular.VandiverData

set_option maxHeartbeats 0
set_option maxRecDepth 100000

local instance : Fact (Nat.Prime 491) := ⟨by norm_num⟩

/-- The `i`-th even index in the classical range `2 ≤ k ≤ 488`. -/
def scanIndex (i : Fin 244) : ℕ := 2 * (i + 1)

/-- Kernel-checked compact scan: only the three package channels can have
zero depth-one Voronoi residue. -/
theorem scanResidue_zero_only_at_three_channels (i : Fin 244) :
    scanResidue 491 2 (scanIndex i) = 0 →
      scanIndex i = 292 ∨ scanIndex i = 336 ∨ scanIndex i = 338 := by
  decide +revert

private theorem even_index_eq_scanIndex
    (k : ℕ) (hk2 : 2 ≤ k) (hk488 : k ≤ 488) (hkeven : Even k) :
    ∃ i : Fin 244, scanIndex i = k := by
  obtain ⟨r, hr⟩ := hkeven
  let i : Fin 244 := ⟨r - 1, by omega⟩
  refine ⟨i, ?_⟩
  simp only [scanIndex, i]
  omega

/-- Every noncandidate index in the classical range has nonzero Voronoi
residue modulo `491`. -/
theorem scanResidue_ne_zero_outside_three_channels
    (k : ℕ) (hk : k ∈ indices 491)
    (hnot : k ∉ ({292, 336, 338} : Finset ℕ)) :
    scanResidue 491 2 k ≠ 0 := by
  have hbounds : 2 ≤ k ∧ k ≤ 488 ∧ Even k := by
    simpa [indices, and_assoc] using hk
  obtain ⟨i, hi⟩ :=
    even_index_eq_scanIndex k hbounds.1 hbounds.2.1 hbounds.2.2
  intro hzero
  have hchannels :=
    scanResidue_zero_only_at_three_channels i (hi ▸ hzero)
  rw [hi] at hchannels
  apply hnot
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hchannels

/-- The complete implication-form low scan consumed by the three high
Bernoulli certificates. -/
theorem completeIrregularScan :
    Fermat.FourHundredNinetyOne.HighBernoulli.CompleteIrregularScan := by
  intro j hj hirregular
  have hmem : j ∈ ({292, 336, 338} : Finset ℕ) :=
    bernoulli_numerator_dvd_imp_mem_candidates
      (p := 491) (a := 2) (by norm_num) (by norm_num)
      {292, 336, 338} scanResidue_ne_zero_outside_three_channels
      j hj hirregular
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem

/-- The compact low scan and the three direct Faulhaber certificates prove
the full finite-channel Bernoulli cube condition at exponent `491`. -/
theorem bernoulliCubeCondition_491 : BernoulliCubeCondition 491 :=
  Fermat.FourHundredNinetyOne.HighBernoulli.bernoulliCubeCondition_of_completeIrregularScan
    completeIrregularScan

end Fermat.FourHundredNinetyOne.IrregularScan
