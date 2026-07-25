import Fermat.Irregular.ModularBernoulliScan

/-!
# Core definition for the exponent-1381 Voronoi scan

The expensive finite scan is split across serialized certificate modules.
This lightweight module holds their common index definition.
-/

namespace Fermat.OneThousandThreeHundredEightyOne.IrregularScan

/-- The `i`-th even index in the classical range `2 ≤ k ≤ 1378`. -/
def scanIndex (i : Fin 689) : ℕ := 2 * (i + 1)

/-- Embed a short serialized scan block into the full `689`-coordinate
range. -/
def offsetIndex (offset size : ℕ) (h : offset + size ≤ 689)
    (i : Fin size) : Fin 689 :=
  ⟨offset + i.val, by omega⟩

end Fermat.OneThousandThreeHundredEightyOne.IrregularScan
