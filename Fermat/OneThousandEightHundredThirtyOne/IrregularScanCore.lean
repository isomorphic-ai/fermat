import Fermat.Irregular.ModularBernoulliScan

/-!
# Core definition for the exponent-1831 Voronoi scan

The expensive finite scan is split across serialized certificate modules.
This lightweight module holds their common index definition.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.IrregularScan

/-- The `i`-th even index in the classical range `2 ≤ k ≤ 1828`. -/
def scanIndex (i : Fin 914) : ℕ := 2 * (i + 1)

/-- Embed a short serialized scan block into the full `914`-coordinate
range. -/
def offsetIndex (offset size : ℕ) (h : offset + size ≤ 914)
    (i : Fin size) : Fin 914 :=
  ⟨offset + i.val, by omega⟩

end Fermat.OneThousandEightHundredThirtyOne.IrregularScan
