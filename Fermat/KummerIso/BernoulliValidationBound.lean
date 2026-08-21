import Fermat.KummerIso.CanonicalCubeRelation
import Fermat.KummerIso.UnitAdaptiveRelationHarness

/-!
# Morishima's conjecture and the derivative-source boundary

The historical logarithmic-derivative calculation supplies fixed cube
precision.  Turning that precision into the full-valuation Kummer input
requires the assertion that no relevant Bernoulli numerator is divisible by
`p ^ 3`.  This is the per-prime statement traditionally called Morishima's
conjecture; it is not a consequence of FLT.

The conjecture is an explicit hypothesis below.  The unrelated canonical
unit-family derivative calculation remains a separately named temporary
axiom, stated through `CanonicalDeepDerivativeSource`, the narrow compiler
boundary isolated by the checked generic derivative adapter.

Thus this module no longer claims an unconditional Bernoulli valuation bound
and no longer cites Wiles as a source for one.
-/

namespace Fermat.KummerIso

open scoped NumberField

open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma
open Fermat.KummerIso.CanonicalCubeRelation
open Fermat.KummerIso.UnitAdaptiveRelationHarness

noncomputable section

/-- Morishima's conjecture at the fixed prime `p`: none of the relevant
Bernoulli numerators is divisible by `p ^ 3`.

This is exactly the existing `NoBernoulliObstruction` condition, given a
historically accurate public name at the generic Kummer splice.  See
B. C. Kellner, *On irregular prime power divisors of the Bernoulli numbers*,
Theorem 8.1 and Remark 8.3. -/
def MorishimaConjectureAt (p : ℕ) : Prop :=
  NoBernoulliObstruction p

/-- The all-prime form of Morishima's conjecture.  Generic endpoints below
only request its visible per-prime instance. -/
def MorishimaConjecture : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p → MorishimaConjectureAt p

/-- Temporary external boundary for the canonical-family derivative source.

This statement is independent of Morishima's conjecture.  It records the
generic change-of-basis/source-derivative calculation still missing from the
kernel; fixed-prime channel proofs bypass it.

TODO: replace this axiom by the generic canonical derivative calculation. -/
axiom CanonicalDeepDerivativeSourceValidation
    {K : Type} {p : ℕ} [Fact p.Prime]
    [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hp5 : 5 ≤ p) {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    CanonicalDeepDerivativeSource hp5 hζ

/-- Morishima's conjecture, expressed as the valuation bound consumed by
`KummerFullValuation`.  Unlike the former `BernoulliValidationBound` axiom,
the conjectural premise is explicit in this theorem's type. -/
theorem vandiverCoefficientFamily_valuation_le_two
    {p : ℕ} [Fact p.Prime]
    (hMorishima : MorishimaConjectureAt p) :
    ∀ i : SourceIndex p,
      (vandiverCoefficientFamily
        (p := p)).valuation i ≤ 2 := by
  intro i
  by_contra hle
  change ¬ padicValInt p (vandiverBernoulliNumerator p i) ≤ 2 at hle
  have hthree : 3 ≤ padicValInt p (vandiverBernoulliNumerator p i) := by
    omega
  exact hMorishima i
    ((padicValInt_dvd_iff 3 _).2 (Or.inr hthree))

/-- The canonical logarithmic-derivative source field of the validation
boundary.  All subsequent conversion to cube precision is checked. -/
theorem canonicalDeepDerivativeSource
    {K : Type} {p : ℕ} [Fact p.Prime]
    [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hp5 : 5 ≤ p) {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    CanonicalDeepDerivativeSource hp5 hζ :=
  CanonicalDeepDerivativeSourceValidation hp5 hζ

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

/-- Vandiver's checked cube congruences, together with the explicit
Morishima hypothesis, supply the adaptive relation interface of the
full-valuation kernel. -/
theorem primitiveRelationFullValuationCongruences_of_cube
    {G : Type*} [CommGroup G]
    {p : ℕ} [Fact p.Prime]
    (hMorishima : MorishimaConjectureAt p)
    (u : G) (E : SourceIndex p → G)
    (hcube : PrimitiveRelationCubeCongruences p u E) :
    KummerFullValuation.PrimitiveRelationFullValuationCongruences
      p u E (vandiverCoefficientFamily (p := p)) := by
  intro t a ht hrel hprimitive
  exact
    KummerFullValuation.CoefficientFamily.fullPrecision_of_cubePrecision_of_valuation_le_two
      (vandiverCoefficientFamily (p := p)) a
      (vandiverCoefficientFamily_valuation_le_two hMorishima)
      (hcube t a ht hrel hprimitive)

/-- End-to-end algebraic splice: once the historical source has produced its
cube congruences, the explicit Morishima hypothesis and the existing
full-valuation kernel extract the `p`-th root. -/
theorem isPower_of_primitiveRelationCubeCongruences
    {G : Type*} [CommGroup G]
    {p : ℕ} [Fact p.Prime]
    (hMorishima : MorishimaConjectureAt p)
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
        hMorishima u E hcube)

end

end Fermat.KummerIso
