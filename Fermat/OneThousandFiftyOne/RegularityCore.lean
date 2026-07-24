import Fermat.Irregular.ModularBernoulliScan

/-!
# Core definitions for the exponent-1051 regularity scan

The expensive finite scan is split across serialized certificate modules.
This lightweight module holds their common index and embedding definitions.
-/

namespace Fermat.OneThousandFiftyOne.RegularityCertificate

/-- The `i`-th even index in Kummer's range `2 ≤ k ≤ 1048`. -/
def scanIndex (i : Fin 524) : ℕ := 2 * (i + 1)

/-- Embed a short serialized scan block into the full `524`-coordinate
range. -/
def offsetIndex (offset size : ℕ) (h : offset + size ≤ 524)
    (i : Fin size) : Fin 524 :=
  ⟨offset + i.val, by omega⟩

end Fermat.OneThousandFiftyOne.RegularityCertificate
