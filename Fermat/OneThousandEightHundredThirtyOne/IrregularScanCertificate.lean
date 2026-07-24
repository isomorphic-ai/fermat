import Fermat.OneThousandEightHundredThirtyOne.IrregularScanCertificateChunk18

/-!
# Finite Voronoi scan certificate at exponent 1831

This module assembles nineteen serialized kernel computations. Each chunk
checks at most fifty of the `914` scan coordinates, keeping peak memory low
and making every completed segment independently cacheable.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.IrregularScan

open Fermat.Irregular.ModularBernoulliScan

/-- Kernel-checked compact scan: only the package channel can have zero
depth-one Voronoi residue. -/
theorem scanResidue_zero_only_at_channel (i : Fin 914) :
    scanResidue 1831 3 (scanIndex i) = 0 →
      scanIndex i = 1274 := by
  by_cases h0 : i.val < 50
  · let j : Fin 50 := ⟨i.val, h0⟩
    have hij : offsetIndex 0 50 (by omega) j = i := by
      apply Fin.ext
      simp [offsetIndex, j]
    simpa only [hij] using scanResidue_zero_only_at_channel_chunk0 j
  by_cases h1 : i.val < 100
  · let j : Fin 50 := ⟨i.val - 50, by omega⟩
    have hij : offsetIndex 50 50 (by omega) j = i := by
      apply Fin.ext
      simp [offsetIndex, j]
      omega
    simpa only [hij] using scanResidue_zero_only_at_channel_chunk1 j
  by_cases h2 : i.val < 150
  · let j : Fin 50 := ⟨i.val - 100, by omega⟩
    have hij : offsetIndex 100 50 (by omega) j = i := by
      apply Fin.ext
      simp [offsetIndex, j]
      omega
    simpa only [hij] using scanResidue_zero_only_at_channel_chunk2 j
  by_cases h3 : i.val < 200
  · let j : Fin 50 := ⟨i.val - 150, by omega⟩
    have hij : offsetIndex 150 50 (by omega) j = i := by
      apply Fin.ext
      simp [offsetIndex, j]
      omega
    simpa only [hij] using scanResidue_zero_only_at_channel_chunk3 j
  by_cases h4 : i.val < 250
  · let j : Fin 50 := ⟨i.val - 200, by omega⟩
    have hij : offsetIndex 200 50 (by omega) j = i := by
      apply Fin.ext
      simp [offsetIndex, j]
      omega
    simpa only [hij] using scanResidue_zero_only_at_channel_chunk4 j
  by_cases h5 : i.val < 300
  · let j : Fin 50 := ⟨i.val - 250, by omega⟩
    have hij : offsetIndex 250 50 (by omega) j = i := by
      apply Fin.ext
      simp [offsetIndex, j]
      omega
    simpa only [hij] using scanResidue_zero_only_at_channel_chunk5 j
  by_cases h6 : i.val < 350
  · let j : Fin 50 := ⟨i.val - 300, by omega⟩
    have hij : offsetIndex 300 50 (by omega) j = i := by
      apply Fin.ext
      simp [offsetIndex, j]
      omega
    simpa only [hij] using scanResidue_zero_only_at_channel_chunk6 j
  by_cases h7 : i.val < 400
  · let j : Fin 50 := ⟨i.val - 350, by omega⟩
    have hij : offsetIndex 350 50 (by omega) j = i := by
      apply Fin.ext
      simp [offsetIndex, j]
      omega
    simpa only [hij] using scanResidue_zero_only_at_channel_chunk7 j
  by_cases h8 : i.val < 450
  · let j : Fin 50 := ⟨i.val - 400, by omega⟩
    have hij : offsetIndex 400 50 (by omega) j = i := by
      apply Fin.ext
      simp [offsetIndex, j]
      omega
    simpa only [hij] using scanResidue_zero_only_at_channel_chunk8 j
  by_cases h9 : i.val < 500
  · let j : Fin 50 := ⟨i.val - 450, by omega⟩
    have hij : offsetIndex 450 50 (by omega) j = i := by
      apply Fin.ext
      simp [offsetIndex, j]
      omega
    simpa only [hij] using scanResidue_zero_only_at_channel_chunk9 j
  by_cases h10 : i.val < 550
  · let j : Fin 50 := ⟨i.val - 500, by omega⟩
    have hij : offsetIndex 500 50 (by omega) j = i := by
      apply Fin.ext
      simp [offsetIndex, j]
      omega
    simpa only [hij] using scanResidue_zero_only_at_channel_chunk10 j
  by_cases h11 : i.val < 600
  · let j : Fin 50 := ⟨i.val - 550, by omega⟩
    have hij : offsetIndex 550 50 (by omega) j = i := by
      apply Fin.ext
      simp [offsetIndex, j]
      omega
    simpa only [hij] using scanResidue_zero_only_at_channel_chunk11 j
  by_cases h12 : i.val < 650
  · let j : Fin 50 := ⟨i.val - 600, by omega⟩
    have hij : offsetIndex 600 50 (by omega) j = i := by
      apply Fin.ext
      simp [offsetIndex, j]
      omega
    simpa only [hij] using scanResidue_zero_only_at_channel_chunk12 j
  by_cases h13 : i.val < 700
  · let j : Fin 50 := ⟨i.val - 650, by omega⟩
    have hij : offsetIndex 650 50 (by omega) j = i := by
      apply Fin.ext
      simp [offsetIndex, j]
      omega
    simpa only [hij] using scanResidue_zero_only_at_channel_chunk13 j
  by_cases h14 : i.val < 750
  · let j : Fin 50 := ⟨i.val - 700, by omega⟩
    have hij : offsetIndex 700 50 (by omega) j = i := by
      apply Fin.ext
      simp [offsetIndex, j]
      omega
    simpa only [hij] using scanResidue_zero_only_at_channel_chunk14 j
  by_cases h15 : i.val < 800
  · let j : Fin 50 := ⟨i.val - 750, by omega⟩
    have hij : offsetIndex 750 50 (by omega) j = i := by
      apply Fin.ext
      simp [offsetIndex, j]
      omega
    simpa only [hij] using scanResidue_zero_only_at_channel_chunk15 j
  by_cases h16 : i.val < 850
  · let j : Fin 50 := ⟨i.val - 800, by omega⟩
    have hij : offsetIndex 800 50 (by omega) j = i := by
      apply Fin.ext
      simp [offsetIndex, j]
      omega
    simpa only [hij] using scanResidue_zero_only_at_channel_chunk16 j
  by_cases h17 : i.val < 900
  · let j : Fin 50 := ⟨i.val - 850, by omega⟩
    have hij : offsetIndex 850 50 (by omega) j = i := by
      apply Fin.ext
      simp [offsetIndex, j]
      omega
    simpa only [hij] using scanResidue_zero_only_at_channel_chunk17 j
  · let j : Fin 14 := ⟨i.val - 900, by omega⟩
    have hij : offsetIndex 900 14 (by omega) j = i := by
      apply Fin.ext
      simp [offsetIndex, j]
      omega
    simpa only [hij] using scanResidue_zero_only_at_channel_chunk18 j

end Fermat.OneThousandEightHundredThirtyOne.IrregularScan
