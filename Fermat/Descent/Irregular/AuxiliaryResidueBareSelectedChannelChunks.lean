import Fermat.Descent.Irregular.AuxiliaryResidueBareSelectedChannel

/-!
# Strong-trust chunking for bare selected-character receipts

Large selected-character products should remain kernel-checkable without
placing a native evaluator in the theorem's trust boundary. This file
partitions the bare product into half-open natural intervals, packages one
checked interval value, and assembles adjacent receipts algebraically.

Generated certificate files therefore evaluate only bounded leaves. Their
balanced assembly and conversion to `SelectedChannelReceipt` contain no
further finite-field search or discrete-log data.
-/

open scoped BigOperators

namespace Fermat.Irregular.BareAuxiliaryResidueChannel

open Fermat.Irregular.CircularUnitResidues
open KummerCriterion.CyclotomicUnits

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime]

namespace SplitPrimeData

variable (D : SplitPrimeData p q)

/-- One natural-coordinate factor in the selected character product. -/
def selectedChannelFactor
    (symbolHalf : ℕ) (channelRow : Fin (kummerLogRank p))
    (k : ℕ) : ZMod q :=
  evenSymbolWeight symbolHalf (D.root ^ (k + 1)) ^
    (((((k + 1 : ℕ) : ZMod p) ^
      (2 * kummerLogRowIndex (p := p) channelRow))⁻¹).val)

/-- The selected character product on a half-open natural interval. -/
def selectedChannelChunk
    (symbolHalf : ℕ) (channelRow : Fin (kummerLogRank p))
    (lo hi : ℕ) : ZMod q :=
  ∏ k ∈ Finset.Ico lo hi,
    D.selectedChannelFactor symbolHalf channelRow k

/-- The original `Fin`-indexed product is the full natural interval. -/
theorem selectedChannelProduct_eq_fullChunk
    (symbolHalf : ℕ) (channelRow : Fin (kummerLogRank p)) :
    D.selectedChannelProduct symbolHalf channelRow =
      D.selectedChannelChunk symbolHalf channelRow 0
        (kummerLogRank p + 1) := by
  rw [selectedChannelProduct, selectedChannelChunk,
    Nat.Ico_zero_eq_range]
  simpa only [selectedChannelFactor] using
    Fin.prod_univ_eq_prod_range
      (fun k : ℕ ↦ D.selectedChannelFactor symbolHalf channelRow k)
      (kummerLogRank p + 1)

/-- Adjacent chunks multiply to the chunk on their union. -/
theorem selectedChannelChunk_consecutive
    (symbolHalf : ℕ) (channelRow : Fin (kummerLogRank p))
    {lo mid hi : ℕ} (hlo : lo ≤ mid) (hhi : mid ≤ hi) :
    D.selectedChannelChunk symbolHalf channelRow lo mid *
        D.selectedChannelChunk symbolHalf channelRow mid hi =
      D.selectedChannelChunk symbolHalf channelRow lo hi := by
  exact Finset.prod_Ico_consecutive
    (D.selectedChannelFactor symbolHalf channelRow) hlo hhi

end SplitPrimeData

/-- A checked scalar value for one half-open selected-product interval. -/
structure SelectedChannelChunkReceipt
    (D : SplitPrimeData p q)
    (symbolHalf : ℕ) (channelRow : Fin (kummerLogRank p))
    (lo hi : ℕ) where
  value : ZMod q
  authenticate :
    D.selectedChannelChunk symbolHalf channelRow lo hi = value

namespace SelectedChannelChunkReceipt

variable {D : SplitPrimeData p q}
variable {symbolHalf : ℕ} {channelRow : Fin (kummerLogRank p)}

/-- Assemble two adjacent checked chunks without reevaluating either leaf. -/
def append {lo mid hi : ℕ}
    (A : SelectedChannelChunkReceipt D symbolHalf channelRow lo mid)
    (B : SelectedChannelChunkReceipt D symbolHalf channelRow mid hi)
    (hlo : lo ≤ mid) (hhi : mid ≤ hi) :
    SelectedChannelChunkReceipt D symbolHalf channelRow lo hi where
  value := A.value * B.value
  authenticate := by
    rw [← A.authenticate, ← B.authenticate]
    exact
      (D.selectedChannelChunk_consecutive symbolHalf channelRow hlo hhi).symm

/-- Turn a checked full-interval chunk into the existing bare selected
channel receipt. -/
def toSelectedChannelReceipt
    {hp_three : 3 ≤ p}
    (A : SelectedChannelChunkReceipt D symbolHalf channelRow 0
      (kummerLogRank p + 1))
    (symbolExponent_eq : D.symbolExponent = 2 * symbolHalf)
    (scalar : ZMod p) (scalar_ne : scalar ≠ 0)
    (value_eq : A.value = D.root ^ scalar.val) :
    SelectedChannelReceipt D hp_three channelRow where
  symbolHalf := symbolHalf
  symbolExponent_eq := symbolExponent_eq
  scalar := scalar
  scalar_ne := scalar_ne
  authenticate := by
    rw [D.selectedChannelProduct_eq_fullChunk, A.authenticate, value_eq]

end SelectedChannelChunkReceipt

end Fermat.Irregular.BareAuxiliaryResidueChannel
