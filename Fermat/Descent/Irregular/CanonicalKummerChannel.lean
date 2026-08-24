import KummerCriterion.CyclotomicUnits.Vandermonde

/-!
# Intrinsic Kummer character channels

This module owns the p-only linear functional used by selective Case-II.1.
It deliberately has no auxiliary-prime, residue-map, or finite-field phase
dependency.
-/

open scoped Matrix

namespace Fermat.Irregular.AuxiliaryResidueChannels

noncomputable section

open KummerCriterion.CyclotomicUnits

variable (p : ℕ) [Fact p.Prime]

/-- The canonical, auxiliary-prime-independent Kummer character channel. -/
def canonicalKummerChannel (hp_three : 3 ≤ p)
    (j : Fin (kummerLogRank p))
    (e : Fin (kummerLogRank p) → ZMod p) : ZMod p :=
  (vandermondeTeichmullerEvenSubOneMatrix (p := p) hp_three *ᵥ e) j

end


end Fermat.Irregular.AuxiliaryResidueChannels
