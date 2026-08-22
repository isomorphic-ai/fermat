import Fermat.Exponents.OneThousandFiftyOne.RegularityCertificateChunk10

/-!
# Finite Voronoi scan certificate at exponent 1051

The exponent-12613 proof package uses `1051` as its regular support
exponent through `12613 = 12 * 1051 + 1`.  This module assembles eleven
serialized kernel computations covering the complete regularity range.

There are exactly `524` even indices from `2` through `1048`.  Each chunk
checks at most fifty depth-one Voronoi residues using base `7`, the
full-order Lucas witness recorded by the package.
-/

namespace Fermat.OneThousandFiftyOne.RegularityCertificate

open Fermat.Irregular.ModularBernoulliScan

/-- Every depth-one Voronoi residue in Kummer's regularity range is
nonzero modulo `1051`. -/
theorem scanResidue_ne_zero (i : Fin 524) :
    scanResidue 1051 7 (scanIndex i) ≠ 0 := by
  by_cases h0 : i.val < 50
  · let j : Fin 50 := ⟨i.val, h0⟩
    have hij : offsetIndex 0 50 (by omega) j = i := by
      apply Fin.ext
      simp [offsetIndex, j]
    simpa only [hij] using scanResidue_ne_zero_chunk0 j
  by_cases h1 : i.val < 100
  · let j : Fin 50 := ⟨i.val - 50, by omega⟩
    have hij : offsetIndex 50 50 (by omega) j = i := by
      apply Fin.ext
      simp [offsetIndex, j]
      omega
    simpa only [hij] using scanResidue_ne_zero_chunk1 j
  by_cases h2 : i.val < 150
  · let j : Fin 50 := ⟨i.val - 100, by omega⟩
    have hij : offsetIndex 100 50 (by omega) j = i := by
      apply Fin.ext
      simp [offsetIndex, j]
      omega
    simpa only [hij] using scanResidue_ne_zero_chunk2 j
  by_cases h3 : i.val < 200
  · let j : Fin 50 := ⟨i.val - 150, by omega⟩
    have hij : offsetIndex 150 50 (by omega) j = i := by
      apply Fin.ext
      simp [offsetIndex, j]
      omega
    simpa only [hij] using scanResidue_ne_zero_chunk3 j
  by_cases h4 : i.val < 250
  · let j : Fin 50 := ⟨i.val - 200, by omega⟩
    have hij : offsetIndex 200 50 (by omega) j = i := by
      apply Fin.ext
      simp [offsetIndex, j]
      omega
    simpa only [hij] using scanResidue_ne_zero_chunk4 j
  by_cases h5 : i.val < 300
  · let j : Fin 50 := ⟨i.val - 250, by omega⟩
    have hij : offsetIndex 250 50 (by omega) j = i := by
      apply Fin.ext
      simp [offsetIndex, j]
      omega
    simpa only [hij] using scanResidue_ne_zero_chunk5 j
  by_cases h6 : i.val < 350
  · let j : Fin 50 := ⟨i.val - 300, by omega⟩
    have hij : offsetIndex 300 50 (by omega) j = i := by
      apply Fin.ext
      simp [offsetIndex, j]
      omega
    simpa only [hij] using scanResidue_ne_zero_chunk6 j
  by_cases h7 : i.val < 400
  · let j : Fin 50 := ⟨i.val - 350, by omega⟩
    have hij : offsetIndex 350 50 (by omega) j = i := by
      apply Fin.ext
      simp [offsetIndex, j]
      omega
    simpa only [hij] using scanResidue_ne_zero_chunk7 j
  by_cases h8 : i.val < 450
  · let j : Fin 50 := ⟨i.val - 400, by omega⟩
    have hij : offsetIndex 400 50 (by omega) j = i := by
      apply Fin.ext
      simp [offsetIndex, j]
      omega
    simpa only [hij] using scanResidue_ne_zero_chunk8 j
  by_cases h9 : i.val < 500
  · let j : Fin 50 := ⟨i.val - 450, by omega⟩
    have hij : offsetIndex 450 50 (by omega) j = i := by
      apply Fin.ext
      simp [offsetIndex, j]
      omega
    simpa only [hij] using scanResidue_ne_zero_chunk9 j
  · let j : Fin 24 := ⟨i.val - 500, by omega⟩
    have hij : offsetIndex 500 24 (by omega) j = i := by
      apply Fin.ext
      simp [offsetIndex, j]
      omega
    simpa only [hij] using scanResidue_ne_zero_chunk10 j

end Fermat.OneThousandFiftyOne.RegularityCertificate
