import Fermat.KummerIso.CanonicalCubeRelation
import Fermat.KummerIso.UnitAdaptiveRelationHarness

/-!
# Temporary Bernoulli validation boundary

The historical logarithmic-derivative calculation supplies fixed cube
precision.  A uniform bound of two on the valuations of its Bernoulli
coefficients makes that precision exactly strong enough for the
full-valuation Kummer kernel.

For the working-first splice, the one validation seam packages both parts
of that source validation: the numerical Bernoulli bound and the canonical
unit-family derivative source.  The latter is deliberately stated through
`CanonicalDeepDerivativeSource`, the narrow compiler boundary isolated by
the checked generic derivative adapter.

This module keeps that temporary external dependency visible as one named
axiom and otherwise contains only checked adapters.
-/

namespace Fermat.KummerIso

open scoped NumberField

open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma
open Fermat.KummerIso.CanonicalCubeRelation
open Fermat.KummerIso.UnitAdaptiveRelationHarness

noncomputable section

/-- The two source-validation facts temporarily carried by the single
Bernoulli seam.

The first field is purely numerical.  The second is the canonical-family
source calculation that the existing fixed-prime developments prove only
after changing to a prime-specific diagonal basis. -/
structure BernoulliValidationData
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) : Prop where
  valuation_le_two :
    ∀ i : SourceIndex p,
      padicValInt p (vandiverBernoulliNumerator p i) ≤ 2
  canonical_derivative_source :
    ∀ (K : Type) [Field K] [NumberField K]
      [IsCyclotomicExtension {p} ℚ K],
      ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ p),
        CanonicalDeepDerivativeSource hp5 hζ

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

TODO: remove this axiom completely.  Replace `valuation_le_two` with
kernel-checked, machine-checkable certificates for every prime in the
validated range (initially through two billion), together with a verified
checker.  Replace `canonical_derivative_source` by the missing generic
change-of-basis/source-derivative theorem.  Keeping both fields inside this
one temporary seam makes the present two-seam trust boundary exact and
machine-auditable.
-/
axiom BernoulliValidationBound
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    BernoulliValidationData p hp5

/-- The validation boundary, expressed on the coefficient family consumed
by `KummerFullValuation`. -/
theorem vandiverCoefficientFamily_valuation_le_two
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∀ i : SourceIndex p,
      (vandiverCoefficientFamily
        (p := p)).valuation i ≤ 2 := by
  intro i
  exact (BernoulliValidationBound p hp5).valuation_le_two i

/-- The canonical logarithmic-derivative source field of the validation
boundary.  All subsequent conversion to cube precision is checked. -/
theorem canonicalDeepDerivativeSource
    {K : Type} {p : ℕ} [Fact p.Prime]
    [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hp5 : 5 ≤ p) {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    CanonicalDeepDerivativeSource hp5 hζ :=
  (BernoulliValidationBound p hp5).canonical_derivative_source K hζ

/-- The canonical source field, converted by the generic derivative
calculation into the cube congruences used by the extraction kernel. -/
theorem canonicalPrimitiveRelationCubeCongruences
    {K : Type} {p : ℕ} [Fact p.Prime]
    [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hp5 : 5 ≤ p) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (u : (𝓞 K)ˣ) (hdeep : IsVandiverDeep hζ u) :
    PrimitiveRelationCubeCongruences p u
      (Fermat.Irregular.CircularUnitFamily.circularUnitFamily
        hζ (by omega)) :=
  primitiveRelationCubeCongruences_of_deep
    hp5 hζ (canonicalDeepDerivativeSource hp5 hζ) u hdeep

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
