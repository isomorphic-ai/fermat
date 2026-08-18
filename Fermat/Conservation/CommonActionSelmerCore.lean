/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# The concrete Selmer sequence core of the common action stage

This file packages Mathlib's actual units-to-Selmer map and the vendored
generic Selmer-to-class map in the additive notation used by the conservation
stage.  It is deliberately independent of campaign ledgers and numbered
exponent directories.
-/
import Fermat.Conservation.SelmerSequence
import Mathlib.Algebra.Module.CharacterModule

noncomputable section

namespace Fermat.Conservation.CommonActionStage

universe uR uK uChi

/-! ## The actual Kummer unit--Selmer--class sequence -/

/-- Units modulo `p`th powers, in additive notation. -/
abbrev UnitModP (R : Type uR) [CommRing R] (p : ℕ) :=
  Additive (Rˣ ⧸ (powMonoidHom p : Rˣ →* Rˣ).range)

/-- Mathlib's unramified Selmer group, in additive notation. -/
abbrev Selmer (R : Type uR) (K : Type uK)
    [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (p : ℕ) :=
  Additive
    (IsDedekindDomain.selmerGroup
      (R := R) (K := K)
      (S := (∅ : Set (IsDedekindDomain.HeightOneSpectrum R))) (n := p))

/-- The `p`-torsion subgroup of the ideal class group. -/
abbrev ClassPTorsion (R : Type uR) [CommRing R]
    [IsDedekindDomain R] (p : ℕ) :=
  AddSubgroup.torsionBy (Additive (ClassGroup R)) (p : ℤ)

section KummerSequence

variable {R : Type uR} [CommRing R] [IsDedekindDomain R]
  {K : Type uK} [Field K] [Algebra R K] [IsFractionRing R K]
  {p : ℕ} [Fact (0 < p)]

/-- The units leg supplied by Mathlib's Kummer/Selmer machinery. -/
def unitInclusion : UnitModP R p →+ Selmer R K p :=
  MonoidHom.toAdditive
    (IsDedekindDomain.selmerGroup.fromUnitLift
      (R := R) (K := K) (n := p))

/-- The available units-to-Selmer map is genuinely injective. -/
theorem unitInclusion_injective :
    Function.Injective (unitInclusion (R := R) (K := K) (p := p)) :=
  IsDedekindDomain.selmerGroup.fromUnitLift_injective
    (R := R) (K := K) (n := p)

/-- The stage-facing additive packaging of the Selmer unit--class sequence. -/
structure SelmerClassSequenceRealization where
  classProjection : Selmer R K p →+ ClassPTorsion R p
  exact_at_selmer :
    Set.range (unitInclusion (R := R) (K := K) (p := p)) =
      {s | classProjection s = 0}
  classProjection_surjective : Function.Surjective classProjection

/-- The vendored class map, restricted to the class-group `p`-torsion and
transported through the additive wrappers used by the common-action stage. -/
def selmerClassProjection : Selmer R K p →+ ClassPTorsion R p :=
  (MonoidHom.toAdditive
    (IsDedekindDomain.selmerGroup.toClass
      (R := R) (K := K) (n := p))).codRestrict
    (ClassPTorsion R p) fun s => by
      apply AddSubgroup.torsionBy.nsmul_iff.mpr
      change Additive.ofMul
        ((IsDedekindDomain.selmerGroup.toClass
          (R := R) (K := K) (n := p) (Additive.toMul s)) ^ p) = 0
      rw [show (IsDedekindDomain.selmerGroup.toClass
        (R := R) (K := K) (n := p) (Additive.toMul s)) ^ p = 1 by
          rw [← powMonoidHom_apply]
          exact MonoidHom.mem_ker.mp <|
            (IsDedekindDomain.selmerGroup.toClass_range
              (R := R) (K := K) (n := p)) ▸
              ⟨Additive.toMul s, rfl⟩]
      rfl

/-- The vendored kernel and range theorems realize the complete additive
unit--Selmer--class sequence used by the stage. -/
def selmerClassSequenceRealization :
    SelmerClassSequenceRealization (R := R) (K := K) (p := p) where
  classProjection := selmerClassProjection
  exact_at_selmer := by
    ext s
    constructor
    · rintro ⟨u, rfl⟩
      have hm :
          IsDedekindDomain.selmerGroup.fromUnitLift
              (R := R) (K := K) (n := p) (Additive.toMul u) ∈
            (IsDedekindDomain.selmerGroup.toClass
              (R := R) (K := K) (n := p)).ker := by
        rw [IsDedekindDomain.selmerGroup.toClass_ker
          (R := R) (K := K) (n := p)]
        exact ⟨Additive.toMul u, rfl⟩
      apply Subtype.ext
      exact congr_arg Additive.ofMul (MonoidHom.mem_ker.mp hm)
    · intro hs
      have hval := congr_arg Subtype.val hs
      have hm : Additive.toMul s ∈
          (IsDedekindDomain.selmerGroup.toClass
            (R := R) (K := K) (n := p)).ker := by
        rw [MonoidHom.mem_ker]
        apply Additive.ofMul.injective
        simpa [selmerClassProjection] using hval
      rw [IsDedekindDomain.selmerGroup.toClass_ker
        (R := R) (K := K) (n := p)] at hm
      obtain ⟨u, hu⟩ := hm
      refine ⟨Additive.ofMul u, ?_⟩
      apply Additive.toMul.injective
      exact hu
  classProjection_surjective := by
    intro c
    have hc : (c : Additive (ClassGroup R)) ∈
        AddSubgroup.torsionBy (Additive (ClassGroup R)) (p : ℤ) :=
      c.property
    rw [AddSubgroup.torsionBy.nsmul_iff] at hc
    change Additive.ofMul
      ((Additive.toMul (c : Additive (ClassGroup R))) ^ p) = 0 at hc
    have hpow : (Additive.toMul (c : Additive (ClassGroup R))) ^ p = 1 :=
      Additive.ofMul.injective hc
    have hker : Additive.toMul (c : Additive (ClassGroup R)) ∈
        (powMonoidHom p : ClassGroup R →* ClassGroup R).ker := by
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      exact hpow
    rw [← IsDedekindDomain.selmerGroup.toClass_range
      (R := R) (K := K) (n := p)] at hker
    obtain ⟨s, hs⟩ := hker
    refine ⟨Additive.ofMul s, Subtype.ext ?_⟩
    exact congr_arg Additive.ofMul hs

/-- The formerly withheld Selmer class-sequence realization is inhabited by
the vendored class projection, kernel theorem, and range theorem. -/
theorem WithheldSelmerClassSequenceRealization :
    Nonempty (SelmerClassSequenceRealization
      (R := R) (K := K) (p := p)) :=
  ⟨selmerClassSequenceRealization (R := R) (K := K) (p := p)⟩

end KummerSequence

/-- The contravariant character dual used for the `chi*` leg.  No equivalence
with the primal leg is implied. -/
abbrev SelmerCharacterDual (SelmerChiStar : Type uChi)
    [AddCommGroup SelmerChiStar] :=
  CharacterModule SelmerChiStar

end Fermat.Conservation.CommonActionStage
