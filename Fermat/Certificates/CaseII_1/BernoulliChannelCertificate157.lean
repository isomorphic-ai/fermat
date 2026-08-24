import Fermat.Descent.Irregular.AuxiliaryBernoulliChannelProvider
import Fermat.Descent.Irregular.BernoulliChannelClassNumber
import Fermat.Exponents.OneHundredFiftySeven.CircularUnitChannelAtQ7537
import Fermat.Exponents.OneHundredFiftySeven.IrregularScan

/-!
# Two-channel normalized certificate at exponent 157

The complete Bernoulli scan has two entries, `62` and `110`.  The
`q = 7537` auxiliary receipt supplies one nonzero scalar for each selected
Kummer row.  Coordinatewise normalization compiles those data into a q-free
projection-kernel certificate; the historical full-determinant route remains
separate.
-/

open scoped NumberField

namespace Fermat.Certificates.CaseII_1.BernoulliChannelCertificate157

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Fermat.Irregular
open Fermat.Irregular.AuxiliaryBernoulliChannelProvider
open Fermat.Irregular.BernoulliChannelProjection
open Fermat.Irregular.VandiverHistoricalPrime
open Fermat.OneHundredFiftySeven.CircularUnitChannelAtQ7537
open Fermat.OneHundredFiftySeven.CircularUnitChannelCoordinates

local instance : Fact (Nat.Prime 157) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 7537) := ⟨by norm_num⟩

/-- The two possible irregular Bernoulli indices at exponent `157`. -/
def support : BernoulliChannelSupport 157 2 where
  index := ![62, 110]
  index_mem := by
    intro i
    fin_cases i <;> norm_num [Fermat.Irregular.VandiverData.indices]
  index_injective := by decide
  complete := by
    intro k hk hdiv
    rcases
        Fermat.OneHundredFiftySeven.IrregularScan.completeIrregularScan
          k hk hdiv with h62 | h110
    · exact ⟨0, h62.symm⟩
    · exact ⟨1, h110.symm⟩

@[simp] theorem support_row_zero : support.row 0 = rowSixtyTwo := by
  apply Fin.ext
  norm_num [support, BernoulliChannelSupport.row, rowSixtyTwo]

@[simp] theorem support_row_one : support.row 1 = rowOneHundredTen := by
  apply Fin.ext
  norm_num [support, BernoulliChannelSupport.row, rowOneHundredTen]

/-- The q-specific receipt supplies exactly the two factorizations selected by
the Bernoulli support. -/
def provider : AuxiliaryChannelProvider support (by norm_num)
    QCertificate.certificate where
  factorization := by
    intro i
    refine Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun i ↦ Fin.elim0 i) i) i
    · simpa only [support_row_zero] using factorization rowSixtyTwo
    · simpa only [show (Fin.succ 0 : Fin 2) = 1 by rfl,
        support_row_one] using factorization rowOneHundredTen
  scalar_ne := by
    intro i
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · change (factorization rowSixtyTwo).scalar ≠ 0
      rw [sixtyTwo_scalar_eq]
      decide
    · change (factorization rowOneHundredTen).scalar ≠ 0
      rw [oneHundredTen_scalar_eq]
      decide

/-- The normalized two-channel certificate.  Its type contains no auxiliary
prime, finite-field root, phase, or Fourier convention. -/
def projectionKernelCertificate.{u} :
    ProjectionKernelCertificate.{u} support (by norm_num) :=
  provider.toProjectionKernelCertificate

/-- New parallel Case-II.1 endpoint at exponent `157`. -/
theorem plusClassNondivisibility
    {K : Type} [Field K] [NumberField K]
    [IsCyclotomicExtension {157} ℚ K] [NumberField.IsCMField K] :
    PlusClassNondivisibility K 157 :=
  projectionKernelCertificate.plusClassNondivisibility (by norm_num)

end


end Fermat.Certificates.CaseII_1.BernoulliChannelCertificate157
