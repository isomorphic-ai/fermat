import Fermat.Exponents.OneHundredFiftySeven.CircularUnitChannelCoordinates

/-!
# Selected Case-II.1 Fourier channels for p = 157, q = 7537

The old `77 × 77` matrix is a cyclic difference matrix after the fixed
p-only row and column reindexings.  This receipt records its 78-value phase
and checks only the two Fourier scalars selected by the irregular Bernoulli
indices `62` and `110`.  It proves no full determinant statement.
-/

namespace Fermat.OneHundredFiftySeven.CircularUnitIrregularChannels157AtQ7537

open Fermat.Irregular.CyclicDifferenceMatrix
open Fermat.OneHundredFiftySeven.CircularUnitChannelCoordinates
open Fermat.OneHundredFiftySeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 157) := ⟨by norm_num⟩

/-- The normalized `q = 7537` residue phase in the p-only real coordinates. -/
def symbolPhase : Cyc 77 → ZMod 157 :=
  ![0, 144, 69, 13, 116, 49, 37, 105, 136, 81, 129, 52, 140,
    16, 108, 51, 155, 122, 113, 42, 49, 2, 8, 50, 149, 4, 30, 135,
    147, 58, 128, 128, 144, 45, 45, 59, 141, 136, 122, 82, 20, 122,
    140, 156, 71, 13, 124, 126, 142, 42, 135, 61, 121, 60, 119, 81,
    50, 141, 15, 119, 55, 78, 87, 72, 53, 20, 119, 74, 124, 72, 58,
    7, 53, 113, 118, 16, 118, 122]

/-- The stored phase and p-only permutations reconstruct every authenticated
source matrix entry. -/
theorem matrix_entry_eq_phase (j i : Fin 77) :
    matrix j i =
      symbolPhase
          (coord 77 (rowPermutation j) + coord 77 (columnPermutation i)) -
        symbolPhase (coord 77 (rowPermutation j)) := by
  decide +revert

/-- Fourier coefficients use zero-based storage for nontrivial frequencies. -/
abbrev coefficient (k : Fin 77) : ZMod 157 :=
  fourierCoeff (25 : ZMod 157)
    fourierRoot_isPrimitive.pow_eq_one symbolPhase k

/-- Actual frequency `47`, attached to Bernoulli index `62`. -/
def slotSixtyTwo : Fin 77 := 46

/-- Actual frequency `23`, attached to Bernoulli index `110`. -/
def slotOneHundredTen : Fin 77 := 22

/-- The selected `B_62` detector scalar is `5 mod 157`. -/
theorem coefficient_sixtyTwo_eq : coefficient slotSixtyTwo = 5 := by
  decide

/-- The selected `B_110` detector scalar is `104 mod 157`. -/
theorem coefficient_oneHundredTen_eq :
    coefficient slotOneHundredTen = 104 := by
  decide

end Fermat.OneHundredFiftySeven.CircularUnitIrregularChannels157AtQ7537
