import Fermat.Exponents.OneThousandEightHundredThirtyOne.IrregularScanCertificate

/-!
# Bernoulli irregular support at exponent 1831

This lightweight Case-II.1 adapter exposes only the low Bernoulli support
proved by the modular scan: every irregular index in the classical range is
`1274`.  It deliberately avoids the lifted high-Bernoulli and power-sum
modules used by the legacy Case-II.2 route.

Future prime generators should emit the analogous support theorem together
with one detector receipt for each listed index.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.IrregularSupport

open Fermat.Irregular.ModularBernoulliScan
open Fermat.Irregular.VandiverData
open Fermat.OneThousandEightHundredThirtyOne.IrregularScan

local instance : Fact (Nat.Prime 1831) := ⟨by norm_num⟩

private theorem even_index_eq_scanIndex
    (k : ℕ) (hk2 : 2 ≤ k) (hk1828 : k ≤ 1828) (hkeven : Even k) :
    ∃ i : Fin 914, scanIndex i = k := by
  obtain ⟨r, hr⟩ := hkeven
  let i : Fin 914 := ⟨r - 1, by omega⟩
  refine ⟨i, ?_⟩
  simp only [scanIndex, i]
  omega

/-- Every noncandidate classical index has nonzero Voronoi scan residue. -/
theorem scanResidue_ne_zero_outside_channel
    (k : ℕ) (hk : k ∈ indices 1831)
    (hnot : k ≠ 1274) :
    scanResidue 1831 3 k ≠ 0 := by
  have hbounds : 2 ≤ k ∧ k ≤ 1828 ∧ Even k := by
    simpa [indices, and_assoc] using hk
  obtain ⟨i, hi⟩ :=
    even_index_eq_scanIndex k hbounds.1 hbounds.2.1 hbounds.2.2
  intro hzero
  have hchannel :=
    scanResidue_zero_only_at_channel i (hi ▸ hzero)
  exact hnot (hi ▸ hchannel)

/-- The complete low-index support implication used by selective Case-II.1. -/
theorem irregular_index_eq_1274
    (k : ℕ) (hk : k ∈ indices 1831)
    (hirregular : (1831 : ℤ) ∣ (bernoulli k).num) :
    k = 1274 := by
  have hmem : k ∈ ({1274} : Finset ℕ) :=
    bernoulli_numerator_dvd_imp_mem_candidates
      (p := 1831) (a := 3) (by norm_num) (by norm_num)
      {1274} (by
        intro j hj hnot
        exact scanResidue_ne_zero_outside_channel j hj (by simpa using hnot))
      k hk hirregular
  simpa only [Finset.mem_singleton] using hmem

end Fermat.OneThousandEightHundredThirtyOne.IrregularSupport
