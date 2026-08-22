/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Exterior-carrying accounted transfers

`ExteriorTransfer` extends the existing `AreaTransfer` by the degree-`r+1`
Plücker vector

`Omega_focus = f₁ ∧ ... ∧ fᵣ ∧ lambda`,

where the independent constraint covectors span `im(Fᵛ)`.  This vector is
zero exactly when the conormal class of `lambda` vanishes, and is nonzero
exactly when the literal augmented map `(F, lambda)` gains one rank.

The old fixed/steerable branch is derived as the zero/nonzero projection of
this retained coordinate.  Forgetting the exterior payload returns the
inherited `AreaTransfer`; no second ledger or conservation law is introduced.
-/
import Fermat.Experiments.Conservation.AreaTransfer
import Fermat.Experiments.Conservation.SteeringFiber
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

open scoped TensorProduct

noncomputable section

namespace Fermat.Conservation

namespace ExteriorTransfer

universe uK uV uW

variable {K : Type uK} [Field K]
  {V : Type uV} [AddCommGroup V] [Module K V]
  {W : Type uW} [AddCommGroup W] [Module K W]

/-! ## Exterior independence -/

/-- The exterior product of a linearly independent finite family is
nonzero. -/
theorem iMulti_ne_zero_of_linearIndependent {n : ℕ} (v : Fin n → V)
    (hv : LinearIndependent K v) :
    exteriorPower.ιMulti K n v ≠ 0 := by
  let e : Fin n ↪o Fin n :=
    ⟨Function.Embedding.refl _, by
      intro a b
      change (a ≤ b ↔ a ≤ b)
      rfl⟩
  let s : Set.powersetCard (Fin n) n :=
    Set.powersetCard.ofFinEmbEquiv e
  have hLI := exteriorPower.ιMulti_family_linearIndependent_field
    (K := K) (n := n) hv
  have hnz : exteriorPower.ιMulti_family K n v s ≠ 0 := hLI.ne_zero s
  simp only [exteriorPower.ιMulti_family, s, Equiv.symm_apply_apply] at hnz
  change exteriorPower.ιMulti K n (v ∘ e) ≠ 0 at hnz
  have he : v ∘ e = v := by
    ext i
    rfl
  simpa [he] using hnz

/-- An exterior product is zero exactly when its factors are linearly
dependent. -/
theorem iMulti_eq_zero_iff_not_linearIndependent {n : ℕ}
    (v : Fin n → V) :
    exteriorPower.ιMulti K n v = 0 ↔ ¬ LinearIndependent K v := by
  constructor
  · intro hz hv
    exact iMulti_ne_zero_of_linearIndependent v hv hz
  · intro hv
    exact (exteriorPower.ιMulti K n).map_linearDependent v hv

theorem iMulti_ne_zero_iff_linearIndependent {n : ℕ}
    (v : Fin n → V) :
    exteriorPower.ιMulti K n v ≠ 0 ↔ LinearIndependent K v := by
  rw [ne_eq, iMulti_eq_zero_iff_not_linearIndependent]
  exact Classical.not_not

/-! ## The focus wedge and rank -/

/-- The degree-`r+1` Plücker vector
`f₁ ∧ ... ∧ fᵣ ∧ lambda`. -/
def focusWedge {r : ℕ} (f : Fin r → Module.Dual K V)
    (lambda : Module.Dual K V) :
    ⋀[K]^(r + 1) (Module.Dual K V) :=
  exteriorPower.ιMulti K (r + 1) (Fin.snoc f lambda)

/-- Row rank of a finite family of covectors. -/
noncomputable def covectorRank {n : ℕ}
    (f : Fin n → Module.Dual K V) : ℕ :=
  Module.finrank K (Submodule.span K (Set.range f))

/-- The constraint map cut out by a finite row family. -/
def constraintMap {n : ℕ} (f : Fin n → Module.Dual K V) :
    V →ₗ[K] (Fin n → K) :=
  LinearMap.pi f

/-- The literal augmented observation `(F, lambda)`. -/
def augmentedMap (F : V →ₗ[K] W) (lambda : Module.Dual K V) :
    V →ₗ[K] (W × K) :=
  F.prod lambda

theorem range_dualMap_augmentedMap
    (F : V →ₗ[K] W) (lambda : Module.Dual K V) :
    LinearMap.range (augmentedMap F lambda).dualMap =
      LinearMap.range F.dualMap ⊔ K ∙ lambda := by
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, augmentedMap,
    LinearMap.ker_prod, Subspace.dualAnnihilator_inf_eq,
    ← LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    ← LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    LinearMap.range_dualMap_dual_eq_span_singleton]

theorem range_dualMap_constraintMap {n : ℕ}
    (f : Fin n → Module.Dual K V) :
    LinearMap.range (constraintMap f).dualMap =
      Submodule.span K (Set.range f) := by
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, constraintMap,
    LinearMap.ker_pi, Subspace.dualAnnihilator_iInf_eq]
  simp_rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    LinearMap.range_dualMap_dual_eq_span_singleton]
  exact Submodule.span_range_eq_iSup.symm

theorem finrank_range_constraintMap_eq_covectorRank {n : ℕ}
    (f : Fin n → Module.Dual K V) :
    Module.finrank K (LinearMap.range (constraintMap f)) =
      covectorRank f := by
  rw [← LinearMap.finrank_range_dualMap_eq_finrank_range,
    range_dualMap_constraintMap, covectorRank]

theorem finrank_range_eq_covectorRank_of_span {r : ℕ}
    (F : V →ₗ[K] W) (f : Fin r → Module.Dual K V)
    (hspan : Submodule.span K (Set.range f) =
      LinearMap.range F.dualMap) :
    Module.finrank K (LinearMap.range F) = covectorRank f := by
  rw [← LinearMap.finrank_range_dualMap_eq_finrank_range,
    covectorRank, hspan]

theorem finrank_range_augmentedMap_eq_covectorRank_snoc {r : ℕ}
    (F : V →ₗ[K] W) (f : Fin r → Module.Dual K V)
    (lambda : Module.Dual K V)
    (hspan : Submodule.span K (Set.range f) =
      LinearMap.range F.dualMap) :
    Module.finrank K (LinearMap.range (augmentedMap F lambda)) =
      covectorRank (Fin.snoc f lambda) := by
  rw [← LinearMap.finrank_range_dualMap_eq_finrank_range,
    range_dualMap_augmentedMap, covectorRank, Fin.range_snoc,
    Submodule.span_insert, hspan, sup_comm]

theorem covectorRank_eq_card_of_linearIndependent {n : ℕ}
    (f : Fin n → Module.Dual K V) (hf : LinearIndependent K f) :
    covectorRank f = n := by
  have h := linearIndependent_iff_card_eq_finrank_span.mp hf
  simpa [covectorRank, Set.finrank] using h.symm

/-- The exterior certificate vanishes exactly when the focus covector is in
the constraint span. -/
theorem focusWedge_eq_zero_iff_mem_span {r : ℕ}
    (f : Fin r → Module.Dual K V) (lambda : Module.Dual K V)
    (hf : LinearIndependent K f) :
    focusWedge f lambda = 0 ↔
      lambda ∈ Submodule.span K (Set.range f) := by
  rw [focusWedge, iMulti_eq_zero_iff_not_linearIndependent,
    linearIndependent_finSnoc]
  simp [hf]

theorem focusWedge_ne_zero_iff_not_mem_span {r : ℕ}
    (f : Fin r → Module.Dual K V) (lambda : Module.Dual K V)
    (hf : LinearIndependent K f) :
    focusWedge f lambda ≠ 0 ↔
      lambda ∉ Submodule.span K (Set.range f) := by
  rw [ne_eq, focusWedge_eq_zero_iff_mem_span f lambda hf]

theorem focusWedge_ne_zero_iff_covectorRank_gain {r : ℕ}
    (f : Fin r → Module.Dual K V) (lambda : Module.Dual K V)
    (hf : LinearIndependent K f) :
    focusWedge f lambda ≠ 0 ↔
      covectorRank (Fin.snoc f lambda) = covectorRank f + 1 := by
  rw [focusWedge, iMulti_ne_zero_iff_linearIndependent,
    linearIndependent_iff_card_eq_finrank_span]
  have hbase := covectorRank_eq_card_of_linearIndependent f hf
  simp only [Fintype.card_fin]
  change (r + 1 = covectorRank (Fin.snoc f lambda)) ↔
    covectorRank (Fin.snoc f lambda) = covectorRank f + 1
  rw [hbase]
  exact eq_comm

/-- With the constraint covectors as a basis of `im(Fᵛ)`, the Plücker vector
is zero exactly when the conormal class vanishes. -/
theorem focusWedge_eq_zero_iff_conormalClass_eq_zero {r : ℕ}
    (F : V →ₗ[K] W) (f : Fin r → Module.Dual K V)
    (lambda : Module.Dual K V) (hf : LinearIndependent K f)
    (hspan : Submodule.span K (Set.range f) =
      LinearMap.range F.dualMap) :
    focusWedge f lambda = 0 ↔
      FocusConormal.conormalClass F lambda = 0 := by
  rw [focusWedge_eq_zero_iff_mem_span f lambda hf,
    FocusConormal.conormalClass_eq_zero_iff_mem_range_dualMap, hspan]

/-- Nonvanishing is exactly a one-rank gain for the literal augmented map
`(F, lambda)`. -/
theorem focusWedge_ne_zero_iff_augmentedMap_rank_gain {r : ℕ}
    (F : V →ₗ[K] W) (f : Fin r → Module.Dual K V)
    (lambda : Module.Dual K V) (hf : LinearIndependent K f)
    (hspan : Submodule.span K (Set.range f) =
      LinearMap.range F.dualMap) :
    focusWedge f lambda ≠ 0 ↔
      Module.finrank K (LinearMap.range (augmentedMap F lambda)) =
        Module.finrank K (LinearMap.range F) + 1 := by
  rw [focusWedge_ne_zero_iff_covectorRank_gain f lambda hf,
    finrank_range_augmentedMap_eq_covectorRank_snoc F f lambda hspan,
    finrank_range_eq_covectorRank_of_span F f hspan]

end ExteriorTransfer

/-! ## Degree-`r+1` extension of the existing area transfer -/

/-- An existing `AreaTransfer` together with a basis of constraint
covectors and its retained focus covector.  The Plücker payload is computed
from these fields, so its zero/nonzero shadow cannot drift from the class. -/
structure ExteriorTransfer (α K V W : Type*)
    [AddCommMonoid α] [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    extends AreaTransfer α K where
  constraintRank : ℕ
  lawful : V →ₗ[K] W
  constraintCovector : Fin constraintRank → Module.Dual K V
  constraintCovector_linearIndependent :
    LinearIndependent K constraintCovector
  constraintCovector_span :
    Submodule.span K (Set.range constraintCovector) =
      LinearMap.range lawful.dualMap
  focusCovector : Module.Dual K V

namespace ExteriorTransfer

universe uα

variable {α : Type uα} [AddCommMonoid α]
  {K : Type uK} [Field K]
  {V : Type uV} [AddCommGroup V] [Module K V]
  {W : Type uW} [AddCommGroup W] [Module K W]

/-- Forget only the new exterior payload; the D=2 transfer is inherited. -/
def areaProjection (transfer : ExteriorTransfer α K V W) :
    AreaTransfer α K :=
  transfer.toAreaTransfer

/-- The retained degree-`r+1` Plücker coordinate. -/
def plueckerCoordinate (transfer : ExteriorTransfer α K V W) :
    ⋀[K]^(transfer.constraintRank + 1) (Module.Dual K V) :=
  focusWedge transfer.constraintCovector transfer.focusCovector

@[simp]
theorem areaProjection_toTransfer (transfer : ExteriorTransfer α K V W) :
    transfer.areaProjection.toTransfer = transfer.toTransfer :=
  rfl

theorem plueckerCoordinate_eq_zero_iff_conormalClass_eq_zero
    (transfer : ExteriorTransfer α K V W) :
    transfer.plueckerCoordinate = 0 ↔
      FocusConormal.conormalClass transfer.lawful
        transfer.focusCovector = 0 :=
  focusWedge_eq_zero_iff_conormalClass_eq_zero
    transfer.lawful transfer.constraintCovector transfer.focusCovector
    transfer.constraintCovector_linearIndependent
    transfer.constraintCovector_span

/-- The zero projection is the intrinsic fixed condition. -/
theorem plueckerCoordinate_eq_zero_iff_fixed
    (transfer : ExteriorTransfer α K V W) :
    transfer.plueckerCoordinate = 0 ↔
      transfer.lawful.ker ≤ transfer.focusCovector.ker := by
  rw [plueckerCoordinate_eq_zero_iff_conormalClass_eq_zero,
    FocusConormal.conormalClass_eq_zero_iff_ker_le]

/-- The nonzero projection is the one-rank transversality gain. -/
theorem plueckerCoordinate_ne_zero_iff_rank_gain
    (transfer : ExteriorTransfer α K V W) :
    transfer.plueckerCoordinate ≠ 0 ↔
      Module.finrank K
          (LinearMap.range
            (augmentedMap transfer.lawful transfer.focusCovector)) =
        Module.finrank K (LinearMap.range transfer.lawful) + 1 :=
  focusWedge_ne_zero_iff_augmentedMap_rank_gain
    transfer.lawful transfer.constraintCovector transfer.focusCovector
    transfer.constraintCovector_linearIndependent
    transfer.constraintCovector_span

/-! ## The old steering bit as a shadow -/

open SteeringFiber

/-- For the joint class/silence observation, the zero Plücker projection is
literally old `FixedAttention`. -/
theorem focusWedge_joint_eq_zero_iff_fixed {r : ℕ}
    (rho : SurjectiveLinearMap K V W)
    {Z : Type*} [AddCommGroup Z] [Module K Z]
    (T : V →ₗ[K] Z) (f : Fin r → Module.Dual K V)
    (lambda : Module.Dual K V) (hf : LinearIndependent K f)
    (hspan : Submodule.span K (Set.range f) =
      LinearMap.range (jointObservation rho T).dualMap) :
    focusWedge f lambda = 0 ↔ FixedAttention rho T lambda := by
  exact
    (focusWedge_eq_zero_iff_conormalClass_eq_zero
      (jointObservation rho T) f lambda hf hspan).trans <| by
        simpa [focusConormalClass] using
          focusConormalClass_eq_zero_iff_fixed rho T lambda

/-- The nonzero Plücker projection is literally the old transverse future. -/
theorem focusWedge_joint_ne_zero_iff_transverse {r : ℕ}
    (rho : SurjectiveLinearMap K V W)
    {Z : Type*} [AddCommGroup Z] [Module K Z]
    (T : V →ₗ[K] Z) (f : Fin r → Module.Dual K V)
    (lambda : Module.Dual K V) (hf : LinearIndependent K f)
    (hspan : Submodule.span K (Set.range f) =
      LinearMap.range (jointObservation rho T).dualMap) :
    focusWedge f lambda ≠ 0 ↔
      Nonempty (TransverseDirection rho T lambda) := by
  have hclass : focusWedge f lambda ≠ 0 ↔
      focusConormalClass rho T lambda ≠ 0 :=
    not_congr (focusWedge_joint_eq_zero_iff_fixed
      rho T f lambda hf hspan |>.trans
        (focusConormalClass_eq_zero_iff_fixed rho T lambda).symm)
  exact hclass.trans <|
    (focusConormalClass_ne_zero_iff_restriction_ne_zero rho T lambda).trans
      (focusConormalRestriction_ne_zero_iff_transverse rho T lambda)

end ExteriorTransfer

end Fermat.Conservation
