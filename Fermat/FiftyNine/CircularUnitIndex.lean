import Fermat.FiftyNine.CircularUnitCertificate
import Fermat.FiftyNine.FirstCase
import Fermat.Irregular.CircularUnitFamily
import Fermat.Irregular.CircularUnitIndex

/-!
# From the exponent-59 matrix to the real-unit relative index

This file contains no exponent-specific cyclotomic-unit construction.  It
specializes the generic odd-prime family and the generic determinant/index
transfer to `p = 59`.  The only input left is a family of actual residue
functionals whose evaluations equal the checked package matrix.
-/

open scoped NumberField

namespace Fermat.FiftyNine.CircularUnitIndex

noncomputable section

open Fermat.Irregular.CircularUnits
open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitIndex

variable {K : Type*} [Field K] [NumberField K]

local instance : Fact (Nat.Prime 59) := ⟨Fermat.FiftyNine.prime_59⟩

local instance : Module ℤ (UnitsModTorsion K) :=
  @AddCommGroup.toIntModule (UnitsModTorsion K) (inferInstance)

/-- The generic canonical circular-unit family at exponent `59`. -/
abbrev circularUnits59 [IsCyclotomicExtension {59} ℚ K]
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 59) :
    Fin 28 → (𝓞 K)ˣ :=
  circularUnitFamily hzeta (by norm_num)

/-- Dirichlet's unit basis, reindexed by the 28 matrix columns. -/
def basisModTorsion59 [IsCyclotomicExtension {59} ℚ K] :
    Module.Basis (Fin 28) ℤ (UnitsModTorsion K) :=
  (NumberField.Units.basisModTorsion K).reindex
    (finCongr (by
      simpa using cyclotomicPrime_unitRank (K := K)
        (p := 59) Fermat.FiftyNine.prime_59 (by norm_num)))

/-- A realization of the package matrix by residue-symbol linear
functionals proves that the canonical circular units have real relative
index prime to `59`. -/
theorem not_dvd_circularUnits59_realIndex_of_evalMatrix_eq
    [IsCyclotomicExtension {59} ℚ K]
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 59)
    (f : Fin 28 → UnitsModTorsion K →ₗ[ℤ] ZMod 59)
    (heval : evalMatrix
        (classOfUnit ∘ circularUnits59 hzeta) f =
      Fermat.FiftyNine.CircularUnitCertificate.matrix) :
    letI : NumberField.IsCMField K :=
      cyclotomicPrime_isCMField (K := K) (p := 59)
        Fermat.FiftyNine.prime_59 (by norm_num)
    ¬ 59 ∣
      (Subgroup.closure (Set.range (circularUnits59 hzeta)) ⊔
        NumberField.Units.torsion K).relIndex
        (NumberField.IsCMField.realUnits K ⊔
          NumberField.Units.torsion K) := by
  letI : NumberField.IsCMField K :=
    cyclotomicPrime_isCMField (K := K) (p := 59)
      Fermat.FiftyNine.prime_59 (by norm_num)
  apply not_dvd_realUnitRelIndex_of_eval_det_ne_zero
      (basisModTorsion59 (K := K)) (circularUnits59 hzeta)
      (fun i ↦ circularUnitFamily_mem_realUnits hzeta (by norm_num) i) f
  rw [heval]
  exact Fermat.FiftyNine.CircularUnitCertificate.matrix_det_ne_zero

end

end Fermat.FiftyNine.CircularUnitIndex
