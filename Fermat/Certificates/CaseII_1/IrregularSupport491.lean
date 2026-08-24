import Fermat.Descent.Irregular.ModularBernoulliScan

/-!
# Bernoulli irregular support at exponent 491

This lightweight Case-II.1 certificate checks the depth-one Voronoi scan and
proves that every irregular index in the classical range belongs to
`{292, 336, 338}`. It deliberately avoids the lifted high-Bernoulli and
power-sum modules used by the historical Case-II.2 route.
-/

namespace Fermat.FourHundredNinetyOne.IrregularSupport

open Fermat.Irregular.ModularBernoulliScan
open Fermat.Irregular.VandiverData

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 1000

local instance : Fact (Nat.Prime 491) := ⟨by norm_num⟩

/-- The `i`-th even index in the classical range `2 ≤ k ≤ 488`. -/
def scanIndex (i : Fin 244) : ℕ := 2 * (i + 1)

/-- Kernel-checked compact scan: only the three listed channels can have
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

/-- Every noncandidate classical index has nonzero Voronoi scan residue. -/
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

/-- Complete low-index support implication consumed by selective Case-II.1. -/
theorem completeIrregularScan
    (j : ℕ) (hj : j ∈ indices 491)
    (hirregular : (491 : ℤ) ∣ (bernoulli j).num) :
    j = 292 ∨ j = 336 ∨ j = 338 := by
  have hmem : j ∈ ({292, 336, 338} : Finset ℕ) :=
    bernoulli_numerator_dvd_imp_mem_candidates
      (p := 491) (a := 2) (by norm_num) (by norm_num)
      {292, 336, 338} scanResidue_ne_zero_outside_three_channels
      j hj hirregular
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem

end Fermat.FourHundredNinetyOne.IrregularSupport
