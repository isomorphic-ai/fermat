import Fermat.FiveHundredEightySeven.VandiverDiagonalDerivative587
import Fermat.FiveHundredEightySeven.VandiverDiagonalUnits587
import Fermat.FiveHundredEightySeven.VandiverNormalizedCongruence

/-!
# From positive Vandiver relations to arbitrary primitive relations

The polynomial argument is naturally stated for nonnegative exponents.
This module isolates the exact normalization step which turns that result
into the `PrimitiveRelationCubeCongruences` interface consumed by
Vandiver's group-theoretic Lemma II core.
-/

open scoped BigOperators NumberField

namespace Fermat.FiveHundredEightySeven.VandiverNormalizedRelationDerivative

noncomputable section

open Fermat.Irregular
open Fermat.Irregular.Voronoi
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma
open Fermat.FiveHundredEightySeven.VandiverDiagonalDerivative
open Fermat.FiveHundredEightySeven.VandiverDiagonalUnits
open Fermat.FiveHundredEightySeven.VandiverNormalizedCongruence
open Fermat.FiveHundredEightySeven.VandiverRelationNormalization

local instance : Fact (Nat.Prime 587) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {587} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 587) K (by norm_num)

/-- The exact positive-relation derivative statement supplied by
Vandiver's polynomial-remainder calculation. -/
def PositiveRelationDerivativeCongruences587 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 587) : Prop :=
  ∀ (v : (𝓞 K)ˣ) (t : ℕ) (b : SourceIndex 587 → ℕ),
    IsVandiverDeep (K := K) (p := 587) hzeta v →
    v ^ t = ∏ i, diagonalVandiverUnit587 hzeta i ^ b i →
    ∀ k, HasPadicValAtLeast 587 2
      (relationDerivative587 (fun i ↦ (b i : ℤ)) k)

/-- Once the positive polynomial calculation is known, normalization
supplies the cube congruences for every integer exponent relation. -/
theorem primitiveRelationCubeCongruences_of_positive
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 587)
    (u : (𝓞 K)ˣ)
    (hdeep : IsVandiverDeep (K := K) (p := 587) hzeta u)
    (hpositive : PositiveRelationDerivativeCongruences587 hzeta) :
    PrimitiveRelationCubeCongruences 587 u
      (diagonalVandiverUnit587 hzeta) := by
  intro t a ht hrel _hprimitive
  let b : SourceIndex 587 → ℕ :=
    fun i ↦ normalizedRelationExponent587 t (a i)
  let v : (𝓞 K)ˣ :=
    normalizedRelationUnit587 u (diagonalVandiverUnit587 hzeta) a
  have hvdeep : IsVandiverDeep (K := K) (p := 587) hzeta v := by
    exact normalizedRelationUnit587_isVandiverDeep
      hzeta u (diagonalVandiverUnit587 hzeta) a hdeep
  have hvrel : v ^ t =
      ∏ i, diagonalVandiverUnit587 hzeta i ^ b i := by
    exact normalizedRelationUnit587_pow
      u (diagonalVandiverUnit587 hzeta) t ht a hrel
  have hderivative :
      ∀ k, HasPadicValAtLeast 587 2
        (relationDerivative587 (fun i ↦ (b i : ℤ)) k) :=
    hpositive v t b hvdeep hvrel
  have hnormalized :=
    cubeCongruence_of_relationDerivative
      (fun i ↦ (b i : ℤ)) hderivative
  intro i
  exact cube_dvd_mul_of_normalizedRelationExponent587
    t ht (a i) (vandiverBernoulliNumerator 587 i)
      (by simpa only [b] using hnormalized i)

end

end Fermat.FiveHundredEightySeven.VandiverNormalizedRelationDerivative
