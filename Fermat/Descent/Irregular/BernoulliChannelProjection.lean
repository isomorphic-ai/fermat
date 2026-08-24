import Fermat.Descent.Irregular.BernoulliChannelSupport
import Fermat.Descent.Irregular.SelectiveKummerSaturation

/-!
# Intrinsic Bernoulli-channel projection receipts

A finite Bernoulli support selects a vector of canonical Kummer rows.  This
module records the q-free statement needed by the descent: every global
`p`th-power relation is annihilated by that entire vector.  The resulting
certificate proves cyclotomic-unit saturation without mentioning an
auxiliary split prime; a separate adapter transports saturation to the plus
class number.

Auxiliary-prime providers live in a separate module.  They may be replaced
without changing the certificate or the saturation theorem below; the
standard finite adapter uses one provider prime for the whole channel family.
-/

open scoped NumberField

namespace Fermat.Irregular.BernoulliChannelProjection

noncomputable section

set_option maxHeartbeats 0

open Fermat.Irregular
open Fermat.Irregular.SelectiveKummerSaturation
open KummerCriterion
open KummerCriterion.CyclotomicUnits

variable {p N : ℕ} [Fact p.Prime]

universe u

/-- A q-free receipt asserting that every global power relation lies in the
kernel of every intrinsic Kummer row selected by `support`. -/
structure ProjectionKernelCertificate
    (support : BernoulliChannelSupport p N) (hp_three : 3 ≤ p) where
  powerRelation_kernel :
    ∀ {K : Type u} [Field K] [NumberField K]
      [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]
      (s : ℤ) (e : Fin (kummerLogRank p) → ℤ),
      CPlusExponentProduct (p := p) (K := K) hp_three s e ∈
          pPowerSubgroup (EPlus (K := K)) p →
        support.projection hp_three (fun i ↦ (e i : ZMod p)) = 0

namespace ProjectionKernelCertificate

variable {support : BernoulliChannelSupport p N} {hp_three : 3 ≤ p}

/-- A regular support (`N = 0`) has a vacuous intrinsic projection receipt
and needs no auxiliary-prime provider. -/
def empty (support : BernoulliChannelSupport p 0) (hp_three : 3 ≤ p) :
    ProjectionKernelCertificate.{u} support hp_three where
  powerRelation_kernel := by
    intro K _ _ _ _ s e hpow
    exact Subsingleton.elim _ _

/-- Complete Bernoulli support plus intrinsic projection vanishing proves
that the real cyclotomic-unit subgroup is `p`-saturated. -/
theorem pSaturated
    (C : ProjectionKernelCertificate.{u} support hp_three)
    (hp_five : 5 ≤ p)
    {K : Type u} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] :
    KummerCriterion.pSaturated
      (CPlus (p := p) (K := K) hp_three) (EPlus (K := K)) p := by
  apply CPlus_pSaturated_of_irregular_support_kummer_rows
    (p := p) (K := K) hp_three hp_five support.ExceptionalRow
    support.exceptionalRow_of_dvd
  intro s e hpow j hj
  obtain ⟨i, rfl⟩ := hj
  have hprojection := C.powerRelation_kernel (K := K) s e hpow
  have hi : support.projection hp_three
      (fun a ↦ (e a : ZMod p)) i = 0 := by
    simpa using congrFun hprojection i
  simpa only [BernoulliChannelSupport.projection_apply,
    AuxiliaryResidueChannels.canonicalKummerChannel] using hi

end ProjectionKernelCertificate

end

end Fermat.Irregular.BernoulliChannelProjection
