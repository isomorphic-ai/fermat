import Fermat.FiveHundredEightySeven.HighBernoulli
import Fermat.Irregular.ModularBernoulliScan
import Fermat.OneHundredFiftySeven.IrregularScan

/-!
# Compact irregular-index scan at exponent 587

The uploaded package reports the two irregular channels `{90, 92}`.
Continuing the exact rational Bernoulli recurrence through `B₅₈₄` produces
enormous certificates.  This module instead checks the equivalent depth-one
Voronoi residues modulo `587`, using the unconditional generic theorem in
`Irregular.ModularBernoulliScan`.

The two exceptional Bernoulli values are still checked exactly.  Together,
the compact exclusion scan and those two exact values prove that the
irregular-index set is precisely `{90, 92}`.

The import of the exponent-157 scan reuses its already kernel-checked exact
recurrence prefix for `B₉₀` and `B₉₂`; the exclusion of every other index
at exponent 587 is the independent modular scan below.

Combining the scan with the independently checked high channels in
`FiveHundredEightySeven.HighBernoulli` gives the unconditional
`BernoulliCubeCondition 587`.
-/

namespace Fermat.FiveHundredEightySeven.IrregularScan

open Fermat.Irregular.ModularBernoulliScan
open Fermat.Irregular.VandiverData

set_option maxHeartbeats 0
set_option maxRecDepth 100000

local instance : Fact (Nat.Prime 587) := ⟨by norm_num⟩

/-! ## Compact modular scan -/

/-- Reuse the common definition of an irregular-index scan. -/
abbrev irregularIndices :=
  Fermat.SixtySeven.ArithmeticCertificate.irregularIndices

/-- The `i`-th even index in the classical range `2 ≤ k ≤ 584`. -/
def scanIndex (i : Fin 292) : ℕ := 2 * (i + 1)

/-- Kernel-checked compact scan: only the two package channels can have
zero depth-one Voronoi residue. -/
theorem scanResidue_zero_only_at_two_channels (i : Fin 292) :
    scanResidue 587 2 (scanIndex i) = 0 →
      scanIndex i = 90 ∨ scanIndex i = 92 := by
  decide +revert

private theorem even_index_eq_scanIndex
    (k : ℕ) (hk2 : 2 ≤ k) (hk584 : k ≤ 584) (hkeven : Even k) :
    ∃ i : Fin 292, scanIndex i = k := by
  obtain ⟨r, hr⟩ := hkeven
  let i : Fin 292 := ⟨r - 1, by omega⟩
  refine ⟨i, ?_⟩
  simp only [scanIndex, i]
  omega

/-- Every noncandidate index in the classical range has nonzero Voronoi
residue modulo `587`. -/
theorem scanResidue_ne_zero_outside_two_channels
    (k : ℕ) (hk : k ∈ indices 587)
    (hnot : k ∉ ({90, 92} : Finset ℕ)) :
    scanResidue 587 2 k ≠ 0 := by
  have hbounds : 2 ≤ k ∧ k ≤ 584 ∧ Even k := by
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
    Fermat.FiveHundredEightySeven.HighBernoulli.CompleteIrregularScan := by
  intro j hj hirregular
  have hmem : j ∈ ({90, 92} : Finset ℕ) :=
    bernoulli_numerator_dvd_imp_mem_candidates
      (p := 587) (a := 2) (by norm_num) (by norm_num)
      {90, 92} scanResidue_ne_zero_outside_two_channels
      j hj hirregular
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem

/-! ## Exact exceptional values -/

/-- Exact first exceptional Bernoulli number. -/
theorem bernoulli_90_exact :
    bernoulli 90 = (1179057279021082799884123351249215083775254949669647116231545215727922535 : ℚ) / 272118 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  norm_num

/-- Exact second exceptional Bernoulli number. -/
theorem bernoulli_92_exact :
    bernoulli 92 = -(1295585948207537527989427828538576749659341483719435143023316326829946247 : ℚ) / 1410 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  norm_num

/-- The complete low Bernoulli scan at exponent 587. -/
theorem irregularIndices_fiveHundredEightySeven :
    irregularIndices 587 = {90, 92} := by
  ext n
  simp only [irregularIndices,
    Fermat.SixtySeven.ArithmeticCertificate.irregularIndices,
    Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hn2, hn584⟩, heven, hdvd⟩
    apply completeIrregularScan n
    · simpa [indices, and_assoc] using ⟨hn2, hn584, heven⟩
    · exact hdvd
  · rintro (rfl | rfl) <;>
      norm_num [bernoulli_90_exact, bernoulli_92_exact]

/-- Numeric-name alias for downstream generated files. -/
theorem irregularIndices_587 : irregularIndices 587 = {90, 92} :=
  irregularIndices_fiveHundredEightySeven

/-- The numerator of `B_90` contains exactly one factor `587`. -/
theorem bernoulli_90_numerator_factorization :
    (1179057279021082799884123351249215083775254949669647116231545215727922535 : ℕ) = 587 * 2008615466816154684640755283218424333518321890408257438213876006350805 := by
  norm_num

theorem bernoulli_90_numerator_not_dvd_sq :
    ¬587 ^ 2 ∣ (1179057279021082799884123351249215083775254949669647116231545215727922535 : ℕ) := by
  norm_num

theorem bernoulli_90_denominator_not_dvd :
    ¬587 ∣ (272118 : ℕ) := by
  norm_num

/-- The package's reduced residue `B_90 / 587 = 200 (mod 587)`. -/
theorem bernoulli_90_scaled_residue :
    ((2008615466816154684640755283218424333518321890408257438213876006350805 : ZMod 587) / 272118) = 200 := by
  decide +kernel +revert

/-- The numerator of `B_92` contains exactly one factor `587`. -/
theorem bernoulli_92_numerator_factorization :
    (1295585948207537527989427828538576749659341483719435143023316326829946247 : ℕ) = 587 * 2207131087236009417358480116760778108448622629845715746206671766320181 := by
  norm_num

theorem bernoulli_92_numerator_not_dvd_sq :
    ¬587 ^ 2 ∣ (1295585948207537527989427828538576749659341483719435143023316326829946247 : ℕ) := by
  norm_num

theorem bernoulli_92_denominator_not_dvd :
    ¬587 ∣ (1410 : ℕ) := by
  norm_num

/-- The package's reduced residue `B_92 / 587 = 426 (mod 587)`. -/
theorem bernoulli_92_scaled_residue :
    (-(2207131087236009417358480116760778108448622629845715746206671766320181 : ZMod 587) / 1410) = 426 := by
  decide +kernel +revert

/-- The complete scan and the two high certificates give the full
Vandiver Bernoulli cube condition at exponent 587. -/
theorem bernoulliCubeCondition_fiveHundredEightySeven :
    Fermat.Irregular.VandiverData.BernoulliCubeCondition 587 :=
  Fermat.FiveHundredEightySeven.HighBernoulli.bernoulliCubeCondition_of_completeIrregularScan
    completeIrregularScan

/-- Numeric-name alias for campaign consumers. -/
theorem bernoulliCubeCondition_587 :
    Fermat.Irregular.VandiverData.BernoulliCubeCondition 587 :=
  bernoulliCubeCondition_fiveHundredEightySeven

end Fermat.FiveHundredEightySeven.IrregularScan
