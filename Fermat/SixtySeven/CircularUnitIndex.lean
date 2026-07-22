import Fermat.Irregular.CircularUnitFamily
import Fermat.Irregular.CircularUnitIndex
import Fermat.SixtySeven.CircularUnitCertificate
import Fermat.SixtySeven.FirstCase

/-!
# The exponent-67 circular-unit index certificate

This file specializes the generic odd-prime circular-unit family to the
thirty-two columns at exponent `67`.  The uploaded nonsingular matrix then
proves an index prime to `67`, once its finite-field evaluations have been
realized as linear maps on units modulo torsion.

The final passage from this relative real-unit index to `67 ∤ h⁺` remains
exactly the shared Sinnott--Kummer boundary; it is not asserted here.
-/

open scoped NumberField

namespace Fermat.SixtySeven.CircularUnitIndex

noncomputable section

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitIndex
open Fermat.Irregular.CircularUnits
open Module NumberField

variable {K : Type*} [Field K] [NumberField K]

local instance : Fact (Nat.Prime 67) := ⟨Fermat.SixtySeven.prime_67⟩

local instance : Module ℤ (UnitsModTorsion K) :=
  @AddCommGroup.toIntModule (UnitsModTorsion K) (inferInstance)

theorem cyclotomic67_unitRank [IsCyclotomicExtension {67} ℚ K] :
    NumberField.Units.rank K = 32 := by
  simpa using cyclotomicPrime_unitRank (K := K) (by norm_num : Nat.Prime 67)
    (by norm_num : 67 ≠ 2)

/-- The canonical thirty-two normalized circular units, with columns
`a = 2, ..., 33`. -/
abbrev circularUnit67 {zeta : K} (hzeta : IsPrimitiveRoot zeta 67) :
    Fin 32 → (𝓞 K)ˣ :=
  circularUnitFamily hzeta (by norm_num)

def basisModTorsion67 [IsCyclotomicExtension {67} ℚ K] :
    Basis (Fin 32) ℤ (UnitsModTorsion K) :=
  (NumberField.Units.basisModTorsion K).reindex
    (finCongr (cyclotomic67_unitRank (K := K)))

/-- Nonsingularity of the uploaded matrix proves that the subgroup generated
by the thirty-two circular units and torsion has full index prime to `67`. -/
theorem not_dvd_circularUnit67_index_of_evalMatrix_eq
    [IsCyclotomicExtension {67} ℚ K]
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 67)
    (f : Fin 32 → UnitsModTorsion K →ₗ[ℤ] ZMod 67)
    (heval : evalMatrix (classOfUnit ∘ circularUnit67 hzeta) f =
      Fermat.SixtySeven.CircularUnitCertificate.matrix) :
    ¬ 67 ∣ (Subgroup.closure (Set.range (circularUnit67 hzeta)) ⊔
      NumberField.Units.torsion K).index := by
  apply not_dvd_unitIndex_of_eval_det_ne_zero
    (basisModTorsion67 (K := K)) (circularUnit67 hzeta) f
  rw [heval]
  exact Fermat.SixtySeven.CircularUnitCertificate.matrix_det_ne_zero

/-- The same certificate controls the relative index inside the real units.
This is the exact algebraic endpoint immediately before Sinnott--Kummer. -/
theorem not_dvd_circularUnit67_realUnitRelIndex_of_evalMatrix_eq
    [IsCyclotomicExtension {67} ℚ K]
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 67)
    (f : Fin 32 → UnitsModTorsion K →ₗ[ℤ] ZMod 67)
    (heval : evalMatrix (classOfUnit ∘ circularUnit67 hzeta) f =
      Fermat.SixtySeven.CircularUnitCertificate.matrix) :
    ¬ 67 ∣ (Subgroup.closure (Set.range (circularUnit67 hzeta)) ⊔
      NumberField.Units.torsion K).relIndex
        (NumberField.IsCMField.realUnits K ⊔
          NumberField.Units.torsion K) := by
  letI : NumberField.IsCMField K :=
    cyclotomicPrime_isCMField (K := K) (p := 67)
      Fermat.SixtySeven.prime_67 (by norm_num)
  apply not_dvd_realUnitRelIndex_of_eval_det_ne_zero
    (basisModTorsion67 (K := K)) (circularUnit67 hzeta)
    (circularUnitFamily_mem_realUnits hzeta (by norm_num)) f
  rw [heval]
  exact Fermat.SixtySeven.CircularUnitCertificate.matrix_det_ne_zero

end

end Fermat.SixtySeven.CircularUnitIndex
