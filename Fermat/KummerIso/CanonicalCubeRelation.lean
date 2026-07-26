import Fermat.Irregular.CircularUnitFamily
import Fermat.Irregular.VandiverDerivativeValuationPrime
import Fermat.Irregular.VandiverUnitLemma

/-!
# The canonical-family cube-relation boundary

This module records the exact compiler boundary between the generic
logarithmic-derivative machinery and the canonical circular-unit family.

The already formalized prime-generic valuation theorem turns a depth-two
isolated diagonal derivative

`a_i * c * (B_((2*i)*p) / ((2*i)*p)) * (tau^((2*i)*p) - 1)`

into the cube precision

`p^3 ∣ a_i * numerator(B_((2*i)*p))`.

What is not presently available is the theorem which produces those
isolated derivatives for relations in `circularUnitFamily`.  The historical
fixed-prime developments instead build a different, diagonal Vandiver
family and prove the source theorem for that family.  No change-of-basis
theorem from the canonical family to that diagonal family currently exists.

`CanonicalDeepDerivativeSource` is therefore a proposition, not an axiom
or a data-carrying root provider.  It states only the missing arithmetic
source theorem, including the finite Teichmüller data used by the repeated
fixed-prime calculation.  The theorem at the end of this file proves that
this source proposition is sufficient for the exact
`PrimitiveRelationCubeCongruences` interface used by Case II.
-/

open scoped BigOperators NumberField

namespace Fermat.KummerIso.CanonicalCubeRelation

noncomputable section

open Fermat.Irregular
open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.VandiverDerivativeValuationPrime
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma
open Fermat.Irregular.Voronoi

variable {K : Type} {p : ℕ} [Fact p.Prime]
  [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The last genuinely arithmetic statement immediately before the
prime-generic valuation endpoint.

It is deliberately phrased for the canonical circular-unit family used by
the generic Case-II harness.  The fixed-prime source proofs establish the
analogous statement only after replacing this family by their specially
diagonalized Vandiver units. -/
def CanonicalIsolatedDerivativeCongruences
    (hp2 : p ≠ 2) (tau : ℕ) (c : ℤ)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (u : (𝓞 K)ˣ) : Prop :=
  ∀ (t : ℕ) (a : SourceIndex p → ℤ),
    0 < t →
    u ^ t = ∏ i, circularUnitFamily hζ hp2 i ^ a i →
    ∀ i,
      PadicValAtLeast p 2
        ((a i : ℚ) * diagonalDerivativeFactor p tau c i)

/-- A prime-generic source statement in the exact shape needed to replay
the repeated fixed-prime positive-relation calculation.

The Teichmüller congruence is upstream arithmetic data for diagonalization.
The adapter below does not use it directly because the generic valuation
theorem needs only the primitive reduction and the unit diagonal
coefficient. -/
def CanonicalDeepDerivativeSource
    (hp5 : 5 ≤ p) {ζ : K} (hζ : IsPrimitiveRoot ζ p) : Prop :=
  ∃ (r tau : ℕ) (c : ℤ),
    p = 2 * r + 1 ∧
    (tau : ZMod (p ^ 2)) ^ (p - 1) = 1 ∧
    IsPrimitiveRoot (tau : ZMod p) (p - 1) ∧
    ¬(p : ℤ) ∣ c ∧
    ∀ u : (𝓞 K)ˣ,
      IsVandiverDeep hζ u →
      CanonicalIsolatedDerivativeCongruences
        (p := p) (by omega) tau c hζ u

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- The already formalized prime-generic valuation calculation converts
isolated depth-two derivatives into Vandiver's coefficient-wise cube
precision. -/
theorem primitiveRelationCubeCongruences_of_isolatedDerivatives
    {r tau : ℕ} {c : ℤ} (hp2 : p ≠ 2)
    (hp : p = 2 * r + 1)
    (htau : IsPrimitiveRoot (tau : ZMod p) (p - 1))
    (hc : ¬(p : ℤ) ∣ c)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (u : (𝓞 K)ˣ)
    (hderivative :
      CanonicalIsolatedDerivativeCongruences hp2 tau c hζ u) :
    PrimitiveRelationCubeCongruences p u
      (circularUnitFamily hζ hp2) := by
  intro t a ht hrelation _hprimitive i
  exact
    cube_dvd_exponent_mul_bernoulliNumerator_of_derivative
      (p := p) (r := r) (t := tau)
      hp htau c hc i (a i)
      (hderivative t a ht hrelation i)

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- Compiler-ready end point: once the one missing generic source theorem
is proved, every deeply congruent unit has the cube-relation precision
required by the existing Case-II extraction path. -/
theorem primitiveRelationCubeCongruences_of_deep
    (hp5 : 5 ≤ p) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hsource : CanonicalDeepDerivativeSource hp5 hζ)
    (u : (𝓞 K)ˣ) (hdeep : IsVandiverDeep hζ u) :
    PrimitiveRelationCubeCongruences p u
      (circularUnitFamily hζ (by omega)) := by
  obtain ⟨r, tau, c, hp, _hteich, htau, hc, hderivative⟩ := hsource
  exact
    primitiveRelationCubeCongruences_of_isolatedDerivatives
      (p := p) (r := r) (tau := tau) (c := c)
      (by omega) hp htau hc hζ u (hderivative u hdeep)

end

end Fermat.KummerIso.CanonicalCubeRelation
