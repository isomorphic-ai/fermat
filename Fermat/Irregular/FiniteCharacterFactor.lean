import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Lagrange

open scoped Classical BigOperators

/-!
# Local factors over all characters of a finite abelian group

This file proves the finite algebra behind the unramified Euler factors in cyclotomic Artin
factorization.  Evaluation at an element `g` maps the full character group onto a cyclic
subgroup of order `orderOf g`; every value occurs `|G| / orderOf g` times.  Consequently

`∏ χ, (1 - χ(g) X) = (1 - X ^ orderOf g) ^ (|G| / orderOf g)`.

The preliminary lemmas are stated for any integral domain with enough roots of unity, so the
result is reusable beyond the complex-valued cyclotomic application.
-/

namespace Fermat.Irregular.FiniteCharacterFactor

noncomputable section

open Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

theorem prod_one_sub_C_mul_X_subgroup (H : Subgroup Rˣ) [Fintype H] :
    (∏ u : H, (1 - C ((u : Rˣ) : R) * X)) = 1 - X ^ Fintype.card H := by
  have hnodal :
      (∏ u : H, (X - C ((u : Rˣ) : R))) = X ^ Fintype.card H - 1 := by
    calc
      (∏ u : H, (X - C ((u : Rˣ) : R))) =
          ∏ u ∈ (H : Set Rˣ).toFinset, (X - C (u : R)) :=
        Finset.prod_set_coe (s := (H : Set Rˣ))
          (f := fun u : Rˣ => X - C (u : R))
      _ = X ^ Fintype.card H - 1 := by
        simpa [Lagrange.nodal] using Lagrange.nodal_subgroup_eq_X_pow_card_sub_one H
  have hconstR : (∏ u : H, (-((u : Rˣ) : R))) = -(1 : R) := by
    have h := congrArg (Polynomial.eval (0 : R)) hnodal
    rw [Polynomial.eval_prod] at h
    simpa using h
  have hconst : (∏ u : H, (-C ((u : Rˣ) : R))) = -(1 : R[X]) := by
    calc
      (∏ u : H, (-C ((u : Rˣ) : R))) =
          C (∏ u : H, (-((u : Rˣ) : R))) := by
            rw [map_prod]
            simp
      _ = -(1 : R[X]) := by rw [hconstR]; simp
  calc
    (∏ u : H, (1 - C ((u : Rˣ) : R) * X)) =
        ∏ u : H, (-C ((u : Rˣ) : R)) *
          (X - C (((u⁻¹ : H) : Rˣ) : R)) := by
          apply Finset.prod_congr rfl
          intro u _
          simp only [Subgroup.coe_inv]
          have hunit :
              C ((u : Rˣ) : R) * C (((u : Rˣ)⁻¹ : Rˣ) : R) = (1 : R[X]) := by
            rw [← C_mul]
            simp
          calc
            1 - C ((u : Rˣ) : R) * X =
                -(C ((u : Rˣ) : R) * X) + 1 := by ring
            _ = -(C ((u : Rˣ) : R) * X) +
                C ((u : Rˣ) : R) * C (((u : Rˣ)⁻¹ : Rˣ) : R) := by rw [hunit]
            _ = -C ((u : Rˣ) : R) *
                (X - C (((u : Rˣ)⁻¹ : Rˣ) : R)) := by ring
    _ = (∏ u : H, (-C ((u : Rˣ) : R))) *
        (∏ u : H, (X - C (((u⁻¹ : H) : Rˣ) : R))) := by
          rw [← Finset.prod_mul_distrib]
    _ = (-(1 : R[X])) * (X ^ Fintype.card H - 1) := by
          rw [hconst]
          congr 1
          calc
            (∏ u : H, (X - C (((u⁻¹ : H) : Rˣ) : R))) =
                ∏ u : H, (X - C ((u : Rˣ) : R)) := by
              simpa only [Equiv.inv_apply] using
                (Equiv.prod_comp (Equiv.inv H)
                  (fun u : H => X - C ((u : Rˣ) : R)))
            _ = X ^ Fintype.card H - 1 := hnodal
    _ = 1 - X ^ Fintype.card H := by ring

theorem prod_one_sub_mul_subgroup (H : Subgroup Rˣ) [Fintype H] (z : R) :
    (∏ u : H, (1 - ((u : Rˣ) : R) * z)) = 1 - z ^ Fintype.card H := by
  have h := congrArg (Polynomial.eval z) (prod_one_sub_C_mul_X_subgroup H)
  rw [Polynomial.eval_prod] at h
  simpa using h

theorem prod_one_sub_monoidHom
    {A : Type*} [CommGroup A] [Fintype A] (f : A →* Rˣ) (z : R) :
    (∏ a : A, (1 - ((f a : Rˣ) : R) * z)) =
      (1 - z ^ Nat.card f.range) ^ Nat.card f.ker := by
  letI : Fintype f.range := Fintype.ofFinite _
  let fr : A →* f.range := f.rangeRestrict
  have hsurj : Function.Surjective fr := f.rangeRestrict_surjective
  have hfiber (y : f.range) :
      Nat.card {a : A // fr a = y} = Nat.card f.ker := by
    calc
      Nat.card {a : A // fr a = y} = Nat.card fr.ker :=
        Nat.card_congr (fr.fiberEquivKerOfSurjective hsurj y)
      _ = Nat.card f.ker := congrArg (fun K : Subgroup A => Nat.card K)
        (MonoidHom.ker_rangeRestrict f)
  calc
    (∏ a : A, (1 - ((f a : Rˣ) : R) * z)) =
        ∏ a : A, (1 - (((fr a : f.range) : Rˣ) : R) * z) := by rfl
    _ = ∏ y : f.range, ∏ _a : {a : A // fr a = y},
        (1 - (((y : f.range) : Rˣ) : R) * z) := by
          exact (Fintype.prod_fiberwise' fr
            (fun y : f.range => 1 - (((y : f.range) : Rˣ) : R) * z)).symm
    _ = ∏ y : f.range,
        (1 - (((y : f.range) : Rˣ) : R) * z) ^ Nat.card f.ker := by
          apply Fintype.prod_congr
          intro y
          simp only [Finset.prod_const, Finset.card_univ,
            ← Nat.card_eq_fintype_card, hfiber]
    _ = (∏ y : f.range, (1 - (((y : f.range) : Rˣ) : R) * z)) ^
        Nat.card f.ker := by
          rw [Finset.prod_pow]
    _ = (1 - z ^ Nat.card f.range) ^ Nat.card f.ker := by
          congr 1
          simpa only [Nat.card_eq_fintype_card] using
            (prod_one_sub_mul_subgroup f.range z)

variable {G : Type*} [CommGroup G] [Fintype G]
variable [HasEnoughRootsOfUnity R (Monoid.exponent G)]

local instance : Fintype (G →* Rˣ) := Fintype.ofFinite _

/-- Evaluation at `g` as a character on the full character group. -/
def characterEvaluation (g : G) : (G →* Rˣ) →* Rˣ where
  toFun χ := χ g
  map_one' := rfl
  map_mul' χ ψ := by simp

omit [IsDomain R] [Fintype G] [HasEnoughRootsOfUnity R (Monoid.exponent G)] in
@[simp] theorem characterEvaluation_apply (g : G) (χ : G →* Rˣ) :
    characterEvaluation (R := R) g χ = χ g := rfl

omit [IsDomain R] in
theorem characterEvaluation_ker_card_quotient (g : G) :
    Nat.card (characterEvaluation (R := R) g).ker =
      Nat.card (G ⧸ Subgroup.zpowers g) := by
  let H : Subgroup G := Subgroup.zpowers g
  let D : Subgroup (G →* Rˣ) :=
    (CommGroup.subgroupOrderIsoSubgroupMonoidHom G R H).ofDual
  have hker : (characterEvaluation (R := R) g).ker = D := by
    ext χ
    rw [MonoidHom.mem_ker]
    rw [CommGroup.mem_subgroupOrderIsoSubgroupMonoidHom_iff]
    change χ g = 1 ↔ ∀ x ∈ H, χ x = 1
    constructor
    · intro hg x hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [map_zpow, hg, one_zpow]
    · intro h
      exact h g (Subgroup.mem_zpowers g)
  calc
    Nat.card (characterEvaluation (R := R) g).ker = Nat.card D :=
      congrArg (fun K : Subgroup (G →* Rˣ) => Nat.card K) hker
    _ = Nat.card (G ⧸ H) :=
      CommGroup.card_subgroupOrderIsoSubgroupMonoidHom R H
    _ = Nat.card (G ⧸ Subgroup.zpowers g) := rfl

omit [IsDomain R] in
theorem characterEvaluation_ker_card (g : G) :
    Nat.card (characterEvaluation (R := R) g).ker = Nat.card G / orderOf g := by
  rw [characterEvaluation_ker_card_quotient]
  apply Nat.eq_div_of_mul_eq_right (orderOf_pos g).ne'
  rw [mul_comm, ← Nat.card_zpowers]
  exact (Subgroup.zpowers g).card_eq_card_quotient_mul_card_subgroup.symm

omit [IsDomain R] in
theorem characterEvaluation_range_card (g : G) :
    Nat.card (characterEvaluation (R := R) g).range = orderOf g := by
  let H : Subgroup G := Subgroup.zpowers g
  let q := Nat.card (G ⧸ H)
  let ev := characterEvaluation (R := R) g
  have hker : Nat.card ev.ker = q := by
    simpa [ev, q, H] using characterEvaluation_ker_card_quotient (R := R) g
  have hmul : q * Nat.card ev.range = q * orderOf g := by
    calc
      q * Nat.card ev.range = Nat.card (G →* Rˣ) := by
        rw [← hker, ← Subgroup.index_ker ev]
        exact ev.ker.card_mul_index
      _ = Nat.card G := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G R
      _ = q * Nat.card H := H.card_eq_card_quotient_mul_card_subgroup
      _ = q * orderOf g := by simp only [H, Nat.card_zpowers]
  exact Nat.mul_left_cancel Nat.card_pos hmul

/-- The local Artin factor over every character of a finite abelian group. -/
theorem prod_characters_one_sub_apply_mul (g : G) (z : R) :
    (∏ χ : G →* Rˣ, (1 - ((χ g : Rˣ) : R) * z)) =
      (1 - z ^ orderOf g) ^ (Fintype.card G / orderOf g) := by
  have h := prod_one_sub_monoidHom (R := R)
    (characterEvaluation (R := R) g) z
  simp only [characterEvaluation_apply] at h
  rw [characterEvaluation_range_card, characterEvaluation_ker_card,
    Nat.card_eq_fintype_card] at h
  exact h

end

end Fermat.Irregular.FiniteCharacterFactor
