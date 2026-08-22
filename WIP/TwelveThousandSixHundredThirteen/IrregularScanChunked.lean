import Fermat.Exponents.TwelveThousandSixHundredThirteen.HighBernoulliChunked
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedAssembly

/-!
# Complete chunked low scan and Bernoulli bridge at exponent 12613

The balanced batch certificate excludes every noncandidate low index.  The
generic modular Bernoulli scan then supplies the complete low-scan premise
consumed by `HighBernoulliChunked`.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.Irregular.VandiverData
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

local instance : Fact (Nat.Prime 12613) := ⟨by norm_num⟩

private theorem even_index_eq_scanIndex_chunked
    (k : ℕ) (hk2 : 2 ≤ k) (hk12610 : k ≤ 12610)
    (hkeven : Even k) :
    ∃ i : Fin 6305, scanIndex i = k := by
  obtain ⟨r, hr⟩ := hkeven
  let i : Fin 6305 := ⟨r - 1, by omega⟩
  refine ⟨i, ?_⟩
  simp only [scanIndex, i]
  omega

/-- Every noncandidate low index has nonzero depth-one Voronoi residue. -/
theorem scanResidue_ne_zero_outside_irregularCandidates_chunked
    (k : ℕ) (hk : k ∈ indices 12613)
    (hnot : k ∉ irregularCandidates) :
    scanResidue 12613 2 k ≠ 0 := by
  have hbounds : 2 ≤ k ∧ k ≤ 12610 ∧ Even k := by
    simpa [indices, and_assoc] using hk
  obtain ⟨i, hi⟩ :=
    even_index_eq_scanIndex_chunked
      k hbounds.1 hbounds.2.1 hbounds.2.2
  intro hzero
  have hcandidate :=
    scanResidue_zero_imp_mem_irregularCandidates_chunked
      i (hi ▸ hzero)
  rw [hi] at hcandidate
  exact hnot hcandidate

/-- The complete implication-form low scan consumed by the chunked high
Bernoulli certificates. -/
theorem completeIrregularScan_chunked :
    Fermat.TwelveThousandSixHundredThirteen.HighBernoulliChunked.CompleteIrregularScan_chunked := by
  intro j hj hirregular
  have hmem : j ∈ irregularCandidates :=
    bernoulli_numerator_dvd_imp_mem_candidates
      (p := 12613) (a := 2) (by norm_num) (by norm_num)
      irregularCandidates
      scanResidue_ne_zero_outside_irregularCandidates_chunked
      j hj hirregular
  simpa only [irregularCandidates] using hmem

/-- The complete chunked low and high certificates prove the Bernoulli cube
condition at exponent `12613`. -/
theorem bernoulliCubeCondition_12613_chunked :
    BernoulliCubeCondition 12613 :=
  Fermat.TwelveThousandSixHundredThirteen.HighBernoulliChunked.bernoulliCubeCondition_of_completeIrregularScan_chunked
    completeIrregularScan_chunked

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
