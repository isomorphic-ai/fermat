import Fermat.Certificates.CaseII_1.CircularUnitIrregularChannels491AtQ983
import Fermat.Certificates.CaseII_1.IrregularSupport491
import Fermat.Descent.Irregular.AuxiliaryBernoulliChannelProvider
import Fermat.Descent.Irregular.BernoulliChannelClassNumber

/-!
# Three-channel normalized certificate at exponent 491

The complete Bernoulli support has three entries: `292`, `336`, and `338`.
The `q = 983` auxiliary receipt supplies one nonzero scalar per selected
Kummer row. Coordinatewise normalization compiles those finite data into a
q-free projection-kernel certificate. The historical `244 × 244`
determinant route remains separate and unchanged.
-/

open scoped NumberField

namespace Fermat.Certificates.CaseII_1.BernoulliChannelCertificate491

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Fermat.Irregular
open Fermat.Irregular.AuxiliaryBernoulliChannelProvider
open Fermat.Irregular.BernoulliChannelProjection
open Fermat.Irregular.VandiverHistoricalPrime
open Fermat.FourHundredNinetyOne.CircularUnitIrregularChannels491AtQ983

local instance : Fact (Nat.Prime 491) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 983) := ⟨by norm_num⟩

/-- The three possible irregular Bernoulli indices at exponent `491`. -/
def support : BernoulliChannelSupport 491 3 where
  index := ![292, 336, 338]
  index_mem := by
    intro i
    fin_cases i <;> norm_num [Fermat.Irregular.VandiverData.indices]
  index_injective := by decide
  complete := by
    intro k hk hdiv
    rcases
        Fermat.FourHundredNinetyOne.IrregularSupport.completeIrregularScan
          k hk hdiv with h292 | h336 | h338
    · refine ⟨0, ?_⟩
      simp [h292]
    · refine ⟨1, ?_⟩
      simp [h336]
    · refine ⟨2, ?_⟩
      simp [h338]

@[simp] theorem support_row_zero : support.row 0 = row292 := by
  apply Fin.ext
  change 292 / 2 - 1 = 145
  norm_num

@[simp] theorem support_row_one : support.row 1 = row336 := by
  apply Fin.ext
  change 336 / 2 - 1 = 167
  norm_num

@[simp] theorem support_row_two : support.row 2 = row338 := by
  apply Fin.ext
  change 338 / 2 - 1 = 168
  norm_num

/-- The q-specific receipt supplies exactly the three factorizations selected
by the Bernoulli support. -/
def provider : AuxiliaryChannelProvider support (by norm_num)
    QCertificate.certificate where
  factorization := fun i ↦ factorization (support.row i)
  scalar_ne := by
    intro i
    fin_cases i
    · change (factorization row292).scalar ≠ 0
      rw [scalar_row292_eq]
      decide
    · change (factorization row336).scalar ≠ 0
      rw [scalar_row336_eq]
      decide
    · change (factorization row338).scalar ≠ 0
      rw [scalar_row338_eq]
      decide

/-- The normalized three-channel certificate. Its type contains no auxiliary
prime, finite-field root, phase, or Fourier convention. -/
def projectionKernelCertificate.{u} :
    ProjectionKernelCertificate.{u} support (by norm_num) :=
  provider.toProjectionKernelCertificate

/-- New parallel Case-II.1 endpoint at exponent `491`. -/
theorem plusClassNondivisibility
    {K : Type} [Field K] [NumberField K]
    [IsCyclotomicExtension {491} ℚ K] [NumberField.IsCMField K] :
    PlusClassNondivisibility K 491 :=
  projectionKernelCertificate.plusClassNondivisibility (by norm_num)

end

end Fermat.Certificates.CaseII_1.BernoulliChannelCertificate491
