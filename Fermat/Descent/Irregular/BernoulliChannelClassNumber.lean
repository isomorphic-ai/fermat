import Fermat.Descent.Irregular.BernoulliChannelProjection
import Fermat.Descent.Irregular.PlusClassNondivisibility
import KummerCriterion.CyclotomicUnits.NormalizedIndex
import KummerCriterion.CyclotomicUnits.SaturationIndex

/-!
# Class-number endpoint for intrinsic Bernoulli channels

This adapter transports q-free channel saturation through the p-primary
Sinnott index theorem.  It is kept separate from the intrinsic projection
certificate so the latter has a physically auxiliary-certificate-free import
closure and remains universe-polymorphic.

The current upstream index API fixes its cyclotomic field in `Type`; only
this final adapter inherits that implementation restriction.
-/

open scoped NumberField

namespace Fermat.Irregular.BernoulliChannelProjection

noncomputable section

open Fermat.Irregular.VandiverHistoricalPrime
open KummerCriterion
open KummerCriterion.CyclotomicUnits

variable {p N : ℕ} [Fact p.Prime]
variable {support : BernoulliChannelSupport p N} {hp_three : 3 ≤ p}

namespace ProjectionKernelCertificate

/-- Intrinsic channel saturation makes the unnormalized real
cyclotomic-unit index prime to `p`. -/
theorem not_dvd_CPlus_index
    (C : ProjectionKernelCertificate.{0} support hp_three)
    (hp_five : 5 ≤ p)
    {K : Type} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] :
    ¬p ∣ (CPlus (p := p) (K := K) hp_three).index :=
  not_dvd_index_of_pSaturated (p := p) (K := K) hp_three
    (C.pSaturated hp_five)

/-- The p-primary Sinnott index theorem transports intrinsic channel
saturation to the plus class number. -/
theorem not_dvd_hPlus
    (C : ProjectionKernelCertificate.{0} support hp_three)
    (hp_five : 5 ≤ p)
    {K : Type} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] :
    ¬p ∣ hPlus K := by
  intro hdiv
  apply C.not_dvd_CPlus_index hp_five (K := K)
  have hnormalized :
      p ∣ (normalizedCPlus (p := p) (K := K)
        (by omega : p ≠ 2) hp_three).index :=
    (cyclotomicUnitIndex_primeConductor_pPrimary
      (p := p) (K := K) (by omega)).mpr hdiv
  exact (CPlus_index_prime_dvd_iff_normalizedCPlus_index_prime_dvd
    (p := p) (K := K) (by omega) hp_three).mpr hnormalized

/-- Generic Case-II.1 endpoint: a normalized finite-channel receipt proves
the exact plus-class nondivisibility input used by the historical descent. -/
theorem plusClassNondivisibility
    (C : ProjectionKernelCertificate.{0} support hp_three)
    (hp_five : 5 ≤ p)
    {K : Type} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] :
    PlusClassNondivisibility K p := by
  simpa [PlusClassNondivisibility, hPlus, NumberField.classNumber] using
    C.not_dvd_hPlus hp_five (K := K)

end ProjectionKernelCertificate

end

end Fermat.Irregular.BernoulliChannelProjection
