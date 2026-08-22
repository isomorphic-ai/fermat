import Fermat.Core.Basic

/-!
# Chunkable lifted power sums at exponent 12613

The four lifted Faulhaber sums each contain `12613` modular powers.  This
lightweight module isolates interval sums so their finite normalization can
be serialized into bounded-memory certificate chunks.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificates

/-- A half-open interval of the lifted power sum modulo `12613⁴`. -/
def partialPowerSum (n lo hi : ℕ) : ZMod (12613 ^ 4) :=
  ∑ a ∈ Finset.Ico lo hi, (a : ZMod (12613 ^ 4)) ^ n

theorem partialPowerSum_consecutive (n : ℕ)
    {lo mid hi : ℕ} (hlm : lo ≤ mid) (hmh : mid ≤ hi) :
    partialPowerSum n lo mid + partialPowerSum n mid hi =
      partialPowerSum n lo hi := by
  exact Finset.sum_Ico_consecutive
    (fun a ↦ (a : ZMod (12613 ^ 4)) ^ n) hlm hmh

theorem powerSum_eq_partialPowerSum (n : ℕ) :
    (∑ a ∈ Finset.range 12613,
      (a : ZMod (12613 ^ 4)) ^ n) =
        partialPowerSum n 0 12613 := by
  rw [Finset.range_eq_Ico]
  rfl

end Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificates
