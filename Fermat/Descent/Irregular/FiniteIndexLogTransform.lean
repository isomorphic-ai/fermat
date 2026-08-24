import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.NumberTheory.NumberField.Units.Regulator

/-!
# Finite-index transport under a logarithmic change of basis

The Dirichlet logarithms of a full-rank unit family form a basis of the
real logarithmic unit space.  Consequently, applying any nonsingular real
matrix to those logarithms produces another full-rank family and hence
another finite-index subgroup of the unit group.

This form of finite-index transport deliberately works after applying the
logarithmic embedding.  It therefore ignores finite torsion factors such as
the signs introduced when a normalized real cyclotomic unit is represented
by the opposite residue class.

The module contains no auxiliary-prime or residue-certificate imports.
-/

open scoped NumberField

namespace Fermat.Irregular.FiniteIndexLogTransform

noncomputable section

open Module NumberField NumberField.Units

variable {K : Type*} [Field K] [NumberField K]

/-- A nonsingular square real transform of the Dirichlet logarithms of a
finite-index unit family again generates a finite-index subgroup.

The matrix convention is column-oriented: the logarithm of `target i` is
the linear combination whose coefficient on `base j` is `A j i`.
-/
theorem closure_range_finiteIndex_of_log_transform
    (base target : Fin (NumberField.Units.rank K) → (𝓞 K)ˣ)
    (A : Matrix (Fin (NumberField.Units.rank K))
      (Fin (NumberField.Units.rank K)) ℝ)
    [hbase : (Subgroup.closure (Set.range base)).FiniteIndex]
    (hdet : A.det ≠ 0)
    (hlog : ∀ i,
      logEmbedding K (Additive.ofMul (target i)) =
        ∑ j, A j i • logEmbedding K (Additive.ofMul (base j))) :
    (Subgroup.closure (Set.range target)).FiniteIndex := by
  have hbaseMax : IsMaxRank base :=
    isMaxRank_iff_closure_finiteIndex.mpr hbase
  let b : Module.Basis (Fin (NumberField.Units.rank K)) ℝ
      (NumberField.Units.dirichletUnitTheorem.logSpace K) :=
    basisOfIsMaxRank hbaseMax
  have hcols : LinearIndependent ℝ A.col :=
    Matrix.linearIndependent_cols_of_det_ne_zero hdet
  have hmapped : LinearIndependent ℝ
      (b.equivFun.symm.toLinearMap ∘ A.col) :=
    hcols.map' b.equivFun.symm.toLinearMap b.equivFun.symm.ker
  apply isMaxRank_iff_closure_finiteIndex.mp
  change LinearIndependent ℝ
    (fun i ↦ logEmbedding K (Additive.ofMul (target i)))
  rw [show (fun i ↦ logEmbedding K (Additive.ofMul (target i))) =
      b.equivFun.symm.toLinearMap ∘ A.col by
    funext i
    rw [hlog i]
    simp only [Function.comp_apply, Matrix.col_apply,
      LinearEquiv.coe_coe, Basis.equivFun_symm_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [basisOfIsMaxRank_apply hbaseMax]]
  exact hmapped

end

end Fermat.Irregular.FiniteIndexLogTransform
