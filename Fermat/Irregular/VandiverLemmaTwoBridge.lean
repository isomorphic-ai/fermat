import Fermat.Irregular.VandiverLemmaTwoCore
import Fermat.Irregular.VandiverUnitLemma

/-!
# Bridge from the generic Vandiver core to the repository interface

This downstream module identifies the zero-based `Fin` indexing used by
`VandiverLemmaTwoCore` with the one-based interval in
`VandiverUnitLemma.BernoulliObstruction`.  It then packages the proved core
as Vandiver's literal alternative: a `p`-th power, or the historical
Bernoulli obstruction.

The remaining hypothesis is still the narrow
`PrimitiveRelationCubeCongruences`; no unit-power conclusion is assumed.
-/

namespace Fermat.Irregular.VandiverLemmaTwoBridge

open Fermat.Irregular

/-- The core's `Fin`-indexed no-obstruction condition is exactly the
negation of the repository's one-based historical obstruction. -/
theorem noBernoulliObstruction_iff {p : ℕ} :
    VandiverLemmaTwoCore.NoBernoulliObstruction p ↔
      ¬VandiverUnitLemma.BernoulliObstruction p := by
  constructor
  · intro hcore hold
    obtain ⟨n, hn, hdiv⟩ := hold
    have hn' := Finset.mem_Icc.mp hn
    let i : VandiverLemmaTwoCore.SourceIndex p :=
      ⟨n - 1, by omega⟩
    have hi : VandiverLemmaTwoCore.sourceNumber i = n := by
      simp [VandiverLemmaTwoCore.sourceNumber, i]
      omega
    exact hcore i (by
      simpa [VandiverLemmaTwoCore.vandiverBernoulliNumerator, hi] using hdiv)
  · intro hold i hdiv
    apply hold
    refine ⟨VandiverLemmaTwoCore.sourceNumber i, ?_, ?_⟩
    · apply Finset.mem_Icc.mpr
      constructor
      · simp [VandiverLemmaTwoCore.sourceNumber]
      · have hi := i.isLt
        simp [VandiverLemmaTwoCore.sourceNumber]
    · simpa [VandiverLemmaTwoCore.vandiverBernoulliNumerator] using hdiv

/-- The generic core expressed with the repository's historical
no-obstruction predicate. -/
theorem isPower_of_no_bernoulliObstruction
    {G : Type*} [CommGroup G] {p : ℕ} (hp : p.Prime)
    (hpow : Function.Injective (fun x : G ↦ x ^ p))
    (u : G) (E : VandiverLemmaTwoCore.SourceIndex p → G)
    [hfinite : (Subgroup.closure (Set.range E)).FiniteIndex]
    (hcong : VandiverLemmaTwoCore.PrimitiveRelationCubeCongruences p u E)
    (hno : ¬VandiverUnitLemma.BernoulliObstruction p) :
    ∃ v : G, u = v ^ p :=
  VandiverLemmaTwoCore.isPower_of_primitiveRelationCubeCongruences
    hp hpow u E hcong (noBernoulliObstruction_iff.mpr hno)

/-- Vandiver's exact source-shaped alternative, proved generically from
the finite-index unit system and the primitive-relation derivative
congruences. -/
theorem isPower_or_bernoulliObstruction
    {G : Type*} [CommGroup G] {p : ℕ} (hp : p.Prime)
    (hpow : Function.Injective (fun x : G ↦ x ^ p))
    (u : G) (E : VandiverLemmaTwoCore.SourceIndex p → G)
    [hfinite : (Subgroup.closure (Set.range E)).FiniteIndex]
    (hcong : VandiverLemmaTwoCore.PrimitiveRelationCubeCongruences p u E) :
    (∃ v : G, u = v ^ p) ∨
      VandiverUnitLemma.BernoulliObstruction p := by
  by_cases hobs : VandiverUnitLemma.BernoulliObstruction p
  · exact Or.inr hobs
  · exact Or.inl <|
      isPower_of_no_bernoulliObstruction hp hpow u E hcong hobs

end Fermat.Irregular.VandiverLemmaTwoBridge
