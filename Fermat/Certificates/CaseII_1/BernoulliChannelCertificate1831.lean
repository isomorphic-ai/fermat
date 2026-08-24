import Fermat.Descent.Irregular.AuxiliaryBernoulliChannelProvider
import Fermat.Descent.Irregular.BernoulliChannelClassNumber
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitChannelAtQ18311
import Fermat.Certificates.CaseII_1.IrregularSupport1831

/-!
# One-channel normalized certificate at exponent 1831

This is the first regression for the arbitrary-channel Case-II.1 interface.
The complete Bernoulli support has one entry, `1274`; the auxiliary-prime
provider at `q = 18311` supplies one nonzero scalar.  Normalization compiles
those finite data into a q-free projection-kernel certificate and hence into
plus-class-number nondivisibility.

The historical and earlier singleton routes remain separate and unchanged.
-/

open scoped NumberField

namespace Fermat.Certificates.CaseII_1.BernoulliChannelCertificate1831

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Fermat.Irregular
open Fermat.Irregular.AuxiliaryBernoulliChannelProvider
open Fermat.Irregular.BernoulliChannelProjection
open Fermat.Irregular.VandiverHistoricalPrime
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitChannelAtQ18311
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitChannelCoordinates
open Fermat.OneThousandEightHundredThirtyOne.IrregularSupport
open KummerCriterion.CyclotomicUnits

local instance : Fact (Nat.Prime 1831) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 18311) := ⟨by norm_num⟩

/-- The sole possible irregular Bernoulli index at exponent `1831`. -/
def support : BernoulliChannelSupport 1831 1 where
  index := fun _ ↦ 1274
  index_mem := by
    intro i
    norm_num [Fermat.Irregular.VandiverData.indices]
  index_injective := fun _ _ _ ↦ Subsingleton.elim _ _
  complete := by
    intro k hk hdiv
    have hindex := irregular_index_eq_1274 k hk hdiv
    refine ⟨0, ?_⟩
    simp [hindex]

/-- The generic support conversion sends index `1274` to Kummer row `636`. -/
@[simp] theorem support_row_zero : support.row 0 = irregularKummerRow := by
  apply Fin.ext
  norm_num [support, BernoulliChannelSupport.row, irregularKummerRow,
    Fermat.OneThousandEightHundredThirtyOne.CircularUnitProjection.irregularKummerRow]

/-- The q=18311 finite receipt supplies exactly the one factorization selected
by the Bernoulli support. -/
def provider : AuxiliaryChannelProvider support (by norm_num)
    QCertificate.certificate where
  factorization := by
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa only [support_row_zero] using factorization irregularKummerRow
  scalar_ne := by
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change (factorization irregularKummerRow).scalar ≠ 0
    rw [irregular_scalar_eq]
    decide

/-- The normalized one-channel certificate. Its type contains no auxiliary
prime, finite-field root, or Fourier convention. -/
def projectionKernelCertificate.{u} :
    ProjectionKernelCertificate.{u} support (by norm_num) :=
  provider.toProjectionKernelCertificate

/-- New parallel Case-II.1 endpoint at exponent `1831`, obtained through the
arbitrary-channel certificate function. -/
theorem plusClassNondivisibility
    {K : Type} [Field K] [NumberField K]
    [IsCyclotomicExtension {1831} ℚ K] [NumberField.IsCMField K] :
    PlusClassNondivisibility K 1831 :=
  projectionKernelCertificate.plusClassNondivisibility (by norm_num)

end

end Fermat.Certificates.CaseII_1.BernoulliChannelCertificate1831
