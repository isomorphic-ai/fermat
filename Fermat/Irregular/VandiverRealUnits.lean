import Mathlib.NumberTheory.NumberField.CMField

/-!
# Real-unit algebra for Vandiver's Lemma II

The final unit-power argument in Vandiver's Lemma II must be performed in
the real-unit subgroup.  It cannot be performed in the full unit group of a
prime cyclotomic field: the primitive `p`th roots of unity lie in the kernel
of the `p`-power map there.

This file supplies the correct replacement.  A torsion real unit in a CM
field is fixed by complex conjugation, while complex conjugation inverts
torsion.  It therefore has square one, and an odd power can equal one only
when the unit itself is one.  Consequently every odd-power map is injective
on the real-unit subgroup.
-/

open scoped NumberField

namespace Fermat.Irregular.VandiverRealUnits

noncomputable section

open NumberField NumberField.Units

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsCMField K]

/-- Raising real units in a CM field to an odd power is injective. -/
theorem odd_pow_injective (p : ℕ) (hp : Odd p) :
    Function.Injective
      (fun u : NumberField.IsCMField.realUnits K ↦ u ^ p) := by
  intro x y hxy
  apply Subtype.ext
  have hxy' : (x.1 : (𝓞 K)ˣ) ^ p = y.1 ^ p :=
    congrArg Subtype.val hxy
  let z : (𝓞 K)ˣ := x.1 * y.1⁻¹
  have hzpow : z ^ p = 1 := by
    dsimp only [z]
    rw [mul_pow, hxy']
    simp
  have hp0 : 0 < p := hp.pos
  have hzmem : z ∈ NumberField.Units.torsion K := by
    rw [NumberField.Units.torsion, CommGroup.mem_torsion,
      isOfFinOrder_iff_pow_eq_one]
    exact ⟨p, hp0, hzpow⟩
  have hzreal : z ∈ NumberField.IsCMField.realUnits K := by
    exact (NumberField.IsCMField.realUnits K).mul_mem x.2
      ((NumberField.IsCMField.realUnits K).inv_mem y.2)
  have hconjSelf : NumberField.IsCMField.unitsComplexConj K z = z :=
    (NumberField.IsCMField.unitsComplexConj_eq_self_iff K z).2 hzreal
  have hconjInv : NumberField.IsCMField.unitsComplexConj K z = z⁻¹ := by
    simpa using NumberField.IsCMField.unitsComplexConj_torsion
      (K := K) (⟨z, hzmem⟩ : NumberField.Units.torsion K)
  have hzinv : z = z⁻¹ := hconjSelf.symm.trans hconjInv
  have hzsq : z ^ 2 = 1 := by
    calc
      z ^ 2 = z * z := pow_two z
      _ = z⁻¹ * z := congrArg (fun w ↦ w * z) hzinv
      _ = 1 := inv_mul_cancel z
  obtain ⟨k, rfl⟩ := hp
  have hzodd : z ^ (2 * k + 1) = z := by
    rw [pow_add, pow_mul, hzsq]
    simp
  have hz : z = 1 := hzodd.symm.trans hzpow
  exact eq_of_mul_inv_eq_one hz

end

end Fermat.Irregular.VandiverRealUnits
