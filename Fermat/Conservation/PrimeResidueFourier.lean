/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Prime-generic residue-field Fourier analysis

For every prime `p`, this file develops the Fourier dictionary for functions
from a finite cyclic group to `ZMod p`.  When the group has cardinality
`p - 1`, its unit-valued characters form a basis, with the usual normalized
Fourier coefficients.  The elementary pure-character support consequences
do not require cyclicity or the cardinality hypothesis.

The final construction reduces a `PadicInt p`-valued character to its
canonical `ZMod p`-valued character.  Nothing here depends on a Selmer
carrier, a support, an auxiliary prime, or a supplied action.
-/
import Fermat.Conservation.InvolutiveBase
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.ZMod.Torsion
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.StdBasis

open scoped BigOperators
open Module

noncomputable section

namespace Fermat.Conservation.PrimeResidueFourier

universe uDelta

variable {p : ℕ} [Fact p.Prime]

private theorem cast_pred_eq_neg_one :
    ((p - 1 : ℕ) : ZMod p) = -1 := by
  rw [Nat.cast_sub (Fact.out : Nat.Prime p).one_le, ZMod.natCast_self]
  simp

private theorem cast_pred_ne_zero :
    ((p - 1 : ℕ) : ZMod p) ≠ 0 := by
  rw [cast_pred_eq_neg_one]
  exact neg_ne_zero.mpr one_ne_zero

/-! ## Character functions -/

section CharacterFunctions

variable {Delta : Type uDelta} [CommGroup Delta]

/-- A unit-valued character, viewed as a residue-field position vector. -/
abbrev characterFunction
    (chi : Delta →* (ZMod p)ˣ) : Delta → ZMod p :=
  fun g ↦ (chi g : ZMod p)

/-- The same character as a monoid homomorphism into the residue field. -/
abbrev characterMonoidHom
    (chi : Delta →* (ZMod p)ˣ) : Delta →* ZMod p :=
  (Units.coeHom (ZMod p)).comp chi

@[simp]
theorem characterMonoidHom_apply
    (chi : Delta →* (ZMod p)ˣ) (g : Delta) :
    characterMonoidHom chi g = characterFunction chi g :=
  rfl

theorem characterMonoidHom_injective :
    Function.Injective (characterMonoidHom (p := p) (Delta := Delta)) := by
  intro chi psi h
  ext g
  exact DFunLike.congr_fun h g

theorem characterFunction_apply_ne_zero
    (chi : Delta →* (ZMod p)ˣ) (g : Delta) :
    characterFunction chi g ≠ 0 :=
  Units.ne_zero (chi g)

/-- A vector lies in one pure character mode. -/
abbrev IsPureCharacter
    (chi : Delta →* (ZMod p)ˣ) (v : Delta → ZMod p) : Prop :=
  ∃ component : ZMod p, v = component • characterFunction chi

/-- Point evaluation of a pure character vector is its character component
times the selected character value. -/
theorem pointEvaluation_of_pureCharacter
    (v : Delta → ZMod p) (chi : Delta →* (ZMod p)ˣ)
    (component : ZMod p) (selected : Delta)
    (hv : v = component • characterFunction chi) :
    v selected = component * (chi selected : ZMod p) := by
  rw [hv]
  rfl

end CharacterFunctions

/-! ## Fourier basis and coefficients -/

section Fourier

variable {Delta : Type uDelta} [CommGroup Delta] [Fintype Delta]
  [IsCyclic Delta]

local instance : DecidableEq Delta := Classical.decEq Delta
local instance : Fintype (Delta →* (ZMod p)ˣ) := Fintype.ofFinite _

omit [Fintype Delta] [IsCyclic Delta] in
theorem characterFunction_linearIndependent :
    LinearIndependent (ZMod p)
      (characterFunction (p := p) (Delta := Delta)) := by
  change LinearIndependent (ZMod p)
    (fun chi : Delta →* (ZMod p)ˣ ↦
      (characterMonoidHom chi : Delta → ZMod p))
  exact (linearIndependent_monoidHom Delta (ZMod p)).comp
    (characterMonoidHom (p := p) (Delta := Delta))
    (characterMonoidHom_injective (p := p) (Delta := Delta))

/-- `ZMod p` contains every root required by a cyclic group of order
`p - 1`. -/
theorem enoughRootsForFourier (hcard : Fintype.card Delta = p - 1) :
    HasEnoughRootsOfUnity (ZMod p) (Monoid.exponent Delta) := by
  rw [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card, hcard]
  exact (inferInstance : HasEnoughRootsOfUnity (ZMod p) (p - 1))

theorem characterDual_card (hcard : Fintype.card Delta = p - 1) :
    Nat.card (Delta →* (ZMod p)ˣ) = p - 1 := by
  letI : HasEnoughRootsOfUnity (ZMod p) (Monoid.exponent Delta) :=
    enoughRootsForFourier (p := p) (Delta := Delta) hcard
  rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity Delta (ZMod p),
    Nat.card_eq_fintype_card, hcard]

theorem sum_characters_apply
    (hcard : Fintype.card Delta = p - 1) (x : Delta) :
    (∑ chi : Delta →* (ZMod p)ˣ, (chi x : ZMod p)) =
      if x = 1 then ((p - 1 : ℕ) : ZMod p) else 0 := by
  letI : HasEnoughRootsOfUnity (ZMod p) (Monoid.exponent Delta) :=
    enoughRootsForFourier (p := p) (Delta := Delta) hcard
  by_cases hx : x = 1
  · subst x
    have hc : Fintype.card (Delta →* (ZMod p)ˣ) = p - 1 :=
      (Nat.card_eq_fintype_card :
        Nat.card (Delta →* (ZMod p)ˣ) =
          Fintype.card (Delta →* (ZMod p)ˣ)).symm.trans
            (characterDual_card (p := p) (Delta := Delta) hcard)
    simp [hc, cast_pred_eq_neg_one (p := p)]
  · rw [if_neg hx]
    obtain ⟨eta, heta⟩ :=
      CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
        Delta (ZMod p) hx
    have heta' : (eta x : ZMod p) ≠ 1 := by
      intro h
      exact heta (Units.ext h)
    refine eq_zero_of_mul_eq_self_left heta' ?_
    simp only [Finset.mul_sum, ← Units.val_mul, ← MonoidHom.mul_apply]
    exact Fintype.sum_bijective _ (Group.mulLeft_bijective eta) _ _
      (fun _ ↦ rfl)

/-- Orthogonality of the residue-field characters. -/
theorem character_orthogonality
    (hcard : Fintype.card Delta = p - 1) (s x : Delta) :
    (∑ chi : Delta →* (ZMod p)ˣ,
        ((chi s : ZMod p))⁻¹ * (chi x : ZMod p)) =
      if s = x then ((p - 1 : ℕ) : ZMod p) else 0 := by
  letI : HasEnoughRootsOfUnity (ZMod p) (Monoid.exponent Delta) :=
    enoughRootsForFourier (p := p) (Delta := Delta) hcard
  simpa only [map_inv, map_mul, Units.val_inv_eq_inv_val,
    Units.val_mul, inv_mul_eq_one] using
    (sum_characters_apply (p := p) (Delta := Delta) hcard (s⁻¹ * x))

/-- The normalized Fourier coordinate of a position vector in one character
mode. -/
abbrev fourierCoefficient (v : Delta → ZMod p)
    (chi : Delta →* (ZMod p)ˣ) : ZMod p :=
  (((p - 1 : ℕ) : ZMod p))⁻¹ *
    ∑ s : Delta, ((chi s : ZMod p))⁻¹ * v s

/-- Fourier inversion: the character modes reconstruct every position
vector. -/
theorem fourier_reconstruction
    (hcard : Fintype.card Delta = p - 1)
    (v : Delta → ZMod p) (x : Delta) :
    (∑ chi : Delta →* (ZMod p)ˣ,
        fourierCoefficient v chi * characterFunction chi x) = v x := by
  letI : HasEnoughRootsOfUnity (ZMod p) (Monoid.exponent Delta) :=
    enoughRootsForFourier (p := p) (Delta := Delta) hcard
  calc
    (∑ chi : Delta →* (ZMod p)ˣ,
        fourierCoefficient v chi * characterFunction chi x) =
        (((p - 1 : ℕ) : ZMod p))⁻¹ *
          ∑ chi : Delta →* (ZMod p)ˣ, ∑ s : Delta,
            ((chi s : ZMod p))⁻¹ * v s * (chi x : ZMod p) := by
      simp only [fourierCoefficient, characterFunction]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro chi _
      rw [mul_assoc, Finset.sum_mul]
    _ = (((p - 1 : ℕ) : ZMod p))⁻¹ *
          ∑ s : Delta, v s *
            ∑ chi : Delta →* (ZMod p)ˣ,
              ((chi s : ZMod p))⁻¹ * (chi x : ZMod p) := by
      apply congrArg ((((p - 1 : ℕ) : ZMod p))⁻¹ * ·)
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro chi _
      ring
    _ = (((p - 1 : ℕ) : ZMod p))⁻¹ *
          ∑ s : Delta, v s *
            (if s = x then ((p - 1 : ℕ) : ZMod p) else 0) := by
      apply congrArg ((((p - 1 : ℕ) : ZMod p))⁻¹ * ·)
      apply Finset.sum_congr rfl
      intro s _
      rw [character_orthogonality (p := p) (Delta := Delta) hcard s x]
    _ = v x := by
      have hpred : ((p - 1 : ℕ) : ZMod p) ≠ 0 :=
        cast_pred_ne_zero (p := p)
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_pos]
      calc
        (((p - 1 : ℕ) : ZMod p))⁻¹ *
            (v x * ((p - 1 : ℕ) : ZMod p)) =
          (((p - 1 : ℕ) : ZMod p))⁻¹ *
            ((p - 1 : ℕ) : ZMod p) * v x := by ring
        _ = v x := by rw [inv_mul_cancel₀ hpred, one_mul]

omit [IsCyclic Delta] in
/-- A position delta has a nonzero coordinate in every character frequency. -/
theorem fourierCoefficient_positionBasis
    (selected : Delta) (chi : Delta →* (ZMod p)ˣ) :
    fourierCoefficient (Pi.basisFun (ZMod p) Delta selected) chi =
      (((p - 1 : ℕ) : ZMod p))⁻¹ *
        ((chi selected : ZMod p))⁻¹ := by
  classical
  unfold fourierCoefficient
  congr 1
  rw [Finset.sum_eq_single selected]
  · rw [Pi.basisFun_apply, Pi.single_eq_same, mul_one]
  · intro s _ hs
    rw [Pi.basisFun_apply, Pi.single_eq_of_ne hs, mul_zero]
  · intro h
    exact (h (Finset.mem_univ selected)).elim

omit [IsCyclic Delta] in
theorem fourierCoefficient_positionBasis_ne_zero
    (selected : Delta) (chi : Delta →* (ZMod p)ˣ) :
    fourierCoefficient (Pi.basisFun (ZMod p) Delta selected) chi ≠ 0 := by
  rw [fourierCoefficient_positionBasis]
  exact mul_ne_zero (inv_ne_zero (cast_pred_ne_zero (p := p)))
    (inv_ne_zero (Units.ne_zero (chi selected)))

/-- The vector obtained by retaining one Fourier component. -/
abbrev characterComponent (v : Delta → ZMod p)
    (chi : Delta →* (ZMod p)ˣ) : Delta → ZMod p :=
  fourierCoefficient v chi • characterFunction chi

omit [IsCyclic Delta] in
@[simp]
theorem characterComponent_apply
    (v : Delta → ZMod p) (chi : Delta →* (ZMod p)ˣ)
    (selected : Delta) :
    characterComponent v chi selected =
      fourierCoefficient v chi * (chi selected : ZMod p) := by
  rfl

/-- The character modes form the character basis dual to the position
basis. -/
noncomputable abbrev characterBasis
    (hcard : Fintype.card Delta = p - 1) :
    Basis (Delta →* (ZMod p)ˣ) (ZMod p) (Delta → ZMod p) := by
  letI : HasEnoughRootsOfUnity (ZMod p) (Monoid.exponent Delta) :=
    enoughRootsForFourier (p := p) (Delta := Delta) hcard
  letI : Fintype (Delta →* (ZMod p)ˣ) := Fintype.ofFinite _
  apply basisOfLinearIndependentOfCardEqFinrank
    (characterFunction_linearIndependent (p := p) (Delta := Delta))
  rw [Module.finrank_fintype_fun_eq_card]
  simpa only [Nat.card_eq_fintype_card] using
    (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity Delta (ZMod p))

@[simp]
theorem characterBasis_apply
    (hcard : Fintype.card Delta = p - 1)
    (chi : Delta →* (ZMod p)ˣ) :
    characterBasis (p := p) (Delta := Delta) hcard chi =
      characterFunction chi := by
  letI : HasEnoughRootsOfUnity (ZMod p) (Monoid.exponent Delta) :=
    enoughRootsForFourier (p := p) (Delta := Delta) hcard
  letI : Fintype (Delta →* (ZMod p)ˣ) := Fintype.ofFinite _
  rw [characterBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

theorem characterBasis_fourier_sum
    (hcard : Fintype.card Delta = p - 1) (v : Delta → ZMod p) :
    (∑ chi : Delta →* (ZMod p)ˣ,
        fourierCoefficient v chi •
          characterBasis (p := p) (Delta := Delta) hcard chi) = v := by
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply, characterBasis_apply,
    characterFunction, smul_eq_mul]
  exact fourier_reconstruction (p := p) (Delta := Delta) hcard v x

/-- The explicit Fourier coefficient is literally the corresponding basis
coordinate. -/
theorem characterBasis_repr_eq_fourierCoefficient
    (hcard : Fintype.card Delta = p - 1) (v : Delta → ZMod p)
    (chi : Delta →* (ZMod p)ˣ) :
    (characterBasis (p := p) (Delta := Delta) hcard).repr v chi =
      fourierCoefficient v chi := by
  calc
    (characterBasis (p := p) (Delta := Delta) hcard).repr v chi =
        (characterBasis (p := p) (Delta := Delta) hcard).repr
          (∑ psi : Delta →* (ZMod p)ˣ,
            fourierCoefficient v psi •
              characterBasis (p := p) (Delta := Delta) hcard psi) chi := by
      rw [characterBasis_fourier_sum (p := p) (Delta := Delta) hcard v]
    _ = fourierCoefficient v chi := by
      rw [Basis.repr_sum_self]

theorem fourierCoefficient_pureCharacter
    (hcard : Fintype.card Delta = p - 1)
    (chi : Delta →* (ZMod p)ˣ) (component : ZMod p) :
    fourierCoefficient (component • characterFunction chi) chi =
      component := by
  rw [← characterBasis_repr_eq_fourierCoefficient
    (p := p) (Delta := Delta) hcard]
  rw [← characterBasis_apply (p := p) (Delta := Delta) hcard chi]
  rw [map_smul, Basis.repr_self]
  simp

theorem characterComponent_pureCharacter
    (hcard : Fintype.card Delta = p - 1)
    (chi : Delta →* (ZMod p)ˣ) (component : ZMod p) :
    characterComponent (component • characterFunction chi) chi =
      component • characterFunction chi := by
  funext x
  rw [characterComponent_apply,
    fourierCoefficient_pureCharacter (p := p) (Delta := Delta) hcard]
  rfl

/-- Projecting a vector already lying in the selected pure mode returns the
same vector. -/
theorem characterComponent_eq_self_of_pure
    (hcard : Fintype.card Delta = p - 1)
    (chi : Delta →* (ZMod p)ˣ) (v : Delta → ZMod p)
    (hpure : IsPureCharacter chi v) :
    characterComponent v chi = v := by
  rcases hpure with ⟨component, rfl⟩
  exact characterComponent_pureCharacter
    (p := p) (Delta := Delta) hcard chi component

omit [Fintype Delta] [IsCyclic Delta] in
/-- A nonzero pure character vector has full support. -/
theorem pureCharacter_support_eq_univ
    (chi : Delta →* (ZMod p)ˣ) {component : ZMod p}
    (hcomponent : component ≠ 0) :
    Function.support (component • characterFunction chi) = Set.univ := by
  ext g
  simp [Function.mem_support, hcomponent]

omit [Fintype Delta] [IsCyclic Delta] in
/-- In particular, a nonzero pure character vector cannot be a delta at one
place. -/
theorem pureCharacter_not_support_singleton
    [Nontrivial Delta]
    (chi : Delta →* (ZMod p)ˣ) {component : ZMod p}
    (hcomponent : component ≠ 0) (selected : Delta) :
    Function.support (component • characterFunction chi) ≠ {selected} := by
  obtain ⟨other, hother⟩ := exists_ne selected
  intro h
  have : other ∈ Function.support
      (component • characterFunction chi) := by
    rw [pureCharacter_support_eq_univ chi hcomponent]
    exact Set.mem_univ other
  rw [h, Set.mem_singleton_iff] at this
  exact hother this

omit [IsCyclic Delta] in
/-- Pointed silence is impossible for a nonzero pure character.  If every
nonselected coordinate vanishes, the selected coordinate vanishes too. -/
theorem pureCharacter_pointed_silence
    (hcard : 1 < Fintype.card Delta)
    (chi : Delta →* (ZMod p)ˣ) (v : Delta → ZMod p)
    (selected : Delta) (hpure : IsPureCharacter chi v)
    (hsilence : ∀ position, position ≠ selected → v position = 0) :
    v selected = 0 := by
  obtain ⟨other, hother⟩ := Fintype.exists_ne_of_one_lt_card hcard selected
  rcases hpure with ⟨component, hmode⟩
  have hz : component * (chi other : ZMod p) = 0 := by
    rw [← pointEvaluation_of_pureCharacter
      (component := component) (selected := other) _ _ hmode]
    exact hsilence other hother
  have hcomponent : component = 0 :=
    (mul_eq_zero.mp hz).resolve_right (Units.ne_zero _)
  rw [hmode]
  simp [hcomponent]

end Fourier

/-! ## Reduction of p-adic characters -/

/-- Reduction of a `p`-adic character to a residue-field character. -/
abbrev reducedCharacterAt
    {Delta : Type*} [CommGroup Delta]
    (eta : Fermat.Conservation.InvolutiveBase.Character
      (PadicInt p) Delta) :
    Delta →* (ZMod p)ˣ :=
  (Units.map PadicInt.toZMod.toMonoidHom).comp eta

@[simp]
theorem reducedCharacterAt_apply
    {Delta : Type*} [CommGroup Delta]
    (eta : Fermat.Conservation.InvolutiveBase.Character
      (PadicInt p) Delta) (delta : Delta) :
    (reducedCharacterAt eta delta : ZMod p) =
      PadicInt.toZMod (eta delta : PadicInt p) :=
  rfl

end Fermat.Conservation.PrimeResidueFourier
