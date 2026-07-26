import Fermat.KummerIso.UnitAdaptiveRelationHarness

/-!
# Temporary Bernoulli validation boundary

The historical logarithmic-derivative calculation already supplies fixed
cube precision.  A uniform bound of two on the valuations of its Bernoulli
coefficients makes that precision exactly strong enough for the
full-valuation Kummer kernel.

This module keeps the temporary external dependency visible and otherwise
contains only checked adapters.
-/

namespace Fermat.KummerIso

open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.KummerIso.UnitAdaptiveRelationHarness

noncomputable section

/-- Temporary external validation boundary for the Bernoulli side of the
Fermat Case-II proof.

The present external FLT trust boundary is Andrew Wiles,
*Modular elliptic curves and Fermat's Last Theorem*, Annals of Mathematics
141 (1995), 443--551, together with Richard Taylor and Andrew Wiles,
*Ring-theoretic properties of certain Hecke algebras*, Annals of Mathematics
141 (1995), 553--572.

This citation explicitly does **not** claim that Wiles or Taylor--Wiles prove
this Bernoulli valuation bound directly.  It records a temporary external
correctness dependency for the already-known FLT endpoint while the
source-side computation is brought into the kernel.

TODO: remove this axiom completely.  Replace it with kernel-checked,
machine-checkable certificates for every prime in the validated range
(initially through two billion), together with a verified checker whose
theorem has exactly this uniform interface.
-/
axiom BernoulliValidationBound
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∀ i : SourceIndex p,
      padicValInt p (vandiverBernoulliNumerator p i) ≤ 2

/-- The validation boundary, expressed on the coefficient family consumed
by `KummerFullValuation`. -/
theorem vandiverCoefficientFamily_valuation_le_two
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∀ i : SourceIndex p,
      (vandiverCoefficientFamily
        (p := p)).valuation i ≤ 2 := by
  intro i
  exact BernoulliValidationBound p hp5 i

/-- Vandiver's checked cube congruences, together with the single validation
bound, supply the adaptive relation interface of the full-valuation kernel. -/
theorem primitiveRelationFullValuationCongruences_of_cube
    {G : Type*} [CommGroup G]
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (u : G) (E : SourceIndex p → G)
    (hcube : PrimitiveRelationCubeCongruences p u E) :
    KummerFullValuation.PrimitiveRelationFullValuationCongruences
      p u E (vandiverCoefficientFamily (p := p)) := by
  intro t a ht hrel hprimitive
  exact
    KummerFullValuation.CoefficientFamily.fullPrecision_of_cubePrecision_of_valuation_le_two
      (vandiverCoefficientFamily (p := p)) a
      (vandiverCoefficientFamily_valuation_le_two hp5)
      (hcube t a ht hrel hprimitive)

/-- End-to-end algebraic splice: once the historical source has produced its
cube congruences, the validation bound and the existing full-valuation
kernel extract the `p`-th root. -/
theorem isPower_of_primitiveRelationCubeCongruences
    {G : Type*} [CommGroup G]
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hpow : Function.Injective (fun x : G ↦ x ^ p))
    (u : G) (E : SourceIndex p → G)
    [hfinite : (Subgroup.closure (Set.range E)).FiniteIndex]
    (hcube : PrimitiveRelationCubeCongruences p u E) :
    ∃ v : G, u = v ^ p := by
  exact
    KummerFullValuation.isPower_of_finiteIndex_family_and_fullValuationCorrection
      (Fact.out : p.Prime) hpow u E
      (vandiverCoefficientFamily (p := p))
      (primitiveRelationFullValuationCongruences_of_cube
        hp5 u E hcube)

end

end Fermat.KummerIso
