import Mathlib.GroupTheory.Index

/-!
# Finite-index transport for real unit families

An explicit Vandiver family is most naturally typed in the subgroup of
real units, while regulator and residue certificates are often stated for
the same elements in the ambient unit group.  This file transports finite
index across that subtype inclusion.
-/

namespace Fermat.Irregular.VandiverFiniteIndex

variable {G : Type*} [Group G] {ι : Type*}

/-- If a family contained in `H` has finite-index closure in the ambient
group, its subtype-valued version has finite-index closure in `H`. -/
theorem closure_range_subtype
    (H : Subgroup G) (E : ι → H)
    [hfinite : (Subgroup.closure
      (Set.range fun i ↦ (E i : G))).FiniteIndex] :
    (Subgroup.closure (Set.range E)).FiniteIndex := by
  let A : Subgroup G := Subgroup.closure (Set.range fun i ↦ (E i : G))
  have hAH : A ≤ H := by
    apply (Subgroup.closure_le H).2
    rintro _ ⟨i, rfl⟩
    exact (E i).2
  letI : A.FiniteIndex := hfinite
  letI : (A.subgroupOf H).FiniteIndex := inferInstance
  have heq : A.subgroupOf H = Subgroup.closure (Set.range E) := by
    rw [← Subgroup.map_subtype_inj]
    rw [Subgroup.map_subgroupOf_eq_of_le hAH, MonoidHom.map_closure]
    apply congrArg Subgroup.closure
    ext x
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨E i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  rw [← heq]
  infer_instance

end Fermat.Irregular.VandiverFiniteIndex
