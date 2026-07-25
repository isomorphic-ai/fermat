import Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalDerivative1381
import Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalUnits1381
import Fermat.OneThousandThreeHundredEightyOne.VandiverNormalizedCongruence1381

/-!
# From positive Vandiver relations to arbitrary primitive relations

The polynomial argument is naturally stated for nonnegative exponents.
This module isolates the exact normalization step which turns that result
into the `PrimitiveRelationCubeCongruences` interface consumed by
Vandiver's group-theoretic Lemma II core.
-/

open scoped BigOperators NumberField

namespace Fermat.OneThousandThreeHundredEightyOne.VandiverNormalizedRelationDerivative

noncomputable section

open Fermat.Irregular
open Fermat.Irregular.Voronoi
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma
open Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalDerivative
open Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalUnits
open Fermat.OneThousandThreeHundredEightyOne.VandiverNormalizedCongruence
open Fermat.OneThousandThreeHundredEightyOne.VandiverRelationNormalization

local instance : Fact (Nat.Prime 1381) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {1381} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 1381) K (by norm_num)

/-- The exact positive-relation derivative statement supplied by
Vandiver's polynomial-remainder calculation. -/
def PositiveRelationDerivativeCongruences1381 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1381) : Prop :=
  ∀ (v : (𝓞 K)ˣ) (t : ℕ) (b : SourceIndex 1381 → ℕ),
    IsVandiverDeep (K := K) (p := 1381) hzeta v →
    v ^ t = ∏ i, diagonalVandiverUnit1381 hzeta i ^ b i →
    ∀ k, HasPadicValAtLeast 1381 2
      (relationDerivative1381 (fun i ↦ (b i : ℤ)) k)

/-- Once the positive polynomial calculation is known, normalization
supplies the cube congruences for every integer exponent relation. -/
theorem primitiveRelationCubeCongruences_of_positive
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 1381)
    (u : (𝓞 K)ˣ)
    (hdeep : IsVandiverDeep (K := K) (p := 1381) hzeta u)
    (hpositive : PositiveRelationDerivativeCongruences1381 hzeta) :
    PrimitiveRelationCubeCongruences 1381 u
      (diagonalVandiverUnit1381 hzeta) := by
  intro t a ht hrel _hprimitive
  let b : SourceIndex 1381 → ℕ :=
    fun i ↦ normalizedRelationExponent1381 t (a i)
  let v : (𝓞 K)ˣ :=
    normalizedRelationUnit1381 u (diagonalVandiverUnit1381 hzeta) a
  have hvdeep : IsVandiverDeep (K := K) (p := 1381) hzeta v := by
    exact normalizedRelationUnit1381_isVandiverDeep
      hzeta u (diagonalVandiverUnit1381 hzeta) a hdeep
  have hvrel : v ^ t =
      ∏ i, diagonalVandiverUnit1381 hzeta i ^ b i := by
    exact normalizedRelationUnit1381_pow
      u (diagonalVandiverUnit1381 hzeta) t ht a hrel
  have hderivative :
      ∀ k, HasPadicValAtLeast 1381 2
        (relationDerivative1381 (fun i ↦ (b i : ℤ)) k) :=
    hpositive v t b hvdeep hvrel
  have hnormalized :=
    cubeCongruence_of_relationDerivative
      (fun i ↦ (b i : ℤ)) hderivative
  intro i
  exact cube_dvd_mul_of_normalizedRelationExponent1381
    t ht (a i) (vandiverBernoulliNumerator 1381 i)
      (by simpa only [b] using hnormalized i)

end

end Fermat.OneThousandThreeHundredEightyOne.VandiverNormalizedRelationDerivative
