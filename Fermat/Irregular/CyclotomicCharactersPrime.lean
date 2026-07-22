import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.GroupTheory.Coset.Card

/-!
# Even characters for a prime cyclotomic field

For an odd prime `p`, the Galois group of the maximal real subfield of the
`p`th cyclotomic field is `(ZMod p)ˣ / {±1}`.  This file packages that
quotient uniformly in `p`, computes its cardinality, and lifts its complex
characters to even Dirichlet characters modulo `p`.
-/

open scoped Classical

namespace Fermat.Irregular.CyclotomicCharactersPrime

noncomputable section

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 < p)]

/-- The subgroup `{1, -1}` of `(ZMod p)ˣ`. -/
def signSubgroup (p : ℕ) : Subgroup (ZMod p)ˣ :=
  Subgroup.zpowers (-1)

/-- The Galois group of the maximal real subfield of a prime cyclotomic
field. -/
abbrev RealResidueGroup (p : ℕ) := (ZMod p)ˣ ⧸ signSubgroup p

/-- Membership in the sign subgroup means equality to one of its two
elements. -/
theorem signSubgroup_mem_iff (u : (ZMod p)ˣ) :
    u ∈ signSubgroup p ↔ u = 1 ∨ u = -1 := by
  constructor
  · intro hu
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [neg_one_zpow_eq_ite] at hk
    by_cases heven : Even k
    · left
      simpa [heven] using hk.symm
    · right
      simpa [heven] using hk.symm
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers (-1)

/-- The sign subgroup has order two. -/
theorem card_signSubgroup : Fintype.card (signSubgroup p) = 2 := by
  rw [signSubgroup, Fintype.card_zpowers]
  apply orderOf_eq_prime
  · norm_num
  · intro h
    have hval := congrArg Units.val h
    exact ZMod.neg_one_ne_one hval

/-- The real residue group of an odd prime has order `(p - 1) / 2`. -/
theorem card_realResidueGroup :
    Fintype.card (RealResidueGroup p) = (p - 1) / 2 := by
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (signSubgroup p)
  have hunits : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime (Fact.out : Nat.Prime p)]
  have hsign : Nat.card (signSubgroup p) = 2 := by
    rw [Nat.card_eq_fintype_card, card_signSubgroup (p := p)]
  have hquot : Nat.card (RealResidueGroup p) =
      Fintype.card (RealResidueGroup p) := Nat.card_eq_fintype_card
  rw [hunits, hsign, hquot] at hcard
  exact Nat.eq_div_of_mul_eq_right (by norm_num) (by
    simpa [mul_comm] using hcard.symm)

/-- The image in the real residue group of an integer prime to `p`. -/
def realResidueOfCoprime (q : ℕ) (hq : q.Coprime p) :
    RealResidueGroup p :=
  QuotientGroup.mk (ZMod.unitOfCoprime q hq)

/-- Lift a character of the real residue quotient to a Dirichlet character
modulo `p`. -/
def quotientCharacterToDirichlet
    (χ : RealResidueGroup p →* ℂˣ) : DirichletCharacter ℂ p :=
  MulChar.ofUnitHom (χ.comp (QuotientGroup.mk' (signSubgroup p)))

theorem quotientCharacterToDirichlet_even
    (χ : RealResidueGroup p →* ℂˣ) :
    (quotientCharacterToDirichlet χ).Even := by
  rw [DirichletCharacter.Even]
  have hneg : (-1 : (ZMod p)ˣ) ∈ signSubgroup p :=
    (signSubgroup_mem_iff _).mpr (Or.inr rfl)
  rw [show (-1 : ZMod p) = ((-1 : (ZMod p)ˣ) : ZMod p) by rfl]
  rw [quotientCharacterToDirichlet, MulChar.ofUnitHom_coe]
  simp only [MonoidHom.comp_apply]
  have hq : (QuotientGroup.mk' (signSubgroup p)) (-1 : (ZMod p)ˣ) = 1 :=
    (QuotientGroup.eq_one_iff (-1 : (ZMod p)ˣ)).mpr hneg
  rw [hq]
  simp

theorem quotientCharacterToDirichlet_apply_unit
    (χ : RealResidueGroup p →* ℂˣ) (u : (ZMod p)ˣ) :
    quotientCharacterToDirichlet χ (u : ZMod p) =
      (χ (QuotientGroup.mk u) : ℂˣ) := by
  rw [quotientCharacterToDirichlet, MulChar.ofUnitHom_coe]
  rfl

theorem quotientCharacterToDirichlet_apply_nat_of_coprime
    (q : ℕ) (hq : q.Coprime p) (χ : RealResidueGroup p →* ℂˣ) :
    quotientCharacterToDirichlet χ (q : ZMod p) =
      ((χ (realResidueOfCoprime q hq) : ℂˣ) : ℂ) := by
  rw [show (q : ZMod p) =
      ((ZMod.unitOfCoprime q hq : (ZMod p)ˣ) : ZMod p) by
    simp only [ZMod.coe_unitOfCoprime]]
  exact quotientCharacterToDirichlet_apply_unit χ
    (ZMod.unitOfCoprime q hq)

end

end Fermat.Irregular.CyclotomicCharactersPrime
