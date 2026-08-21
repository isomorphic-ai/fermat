import Fermat.OneThousandEightHundredThirtyOne.VandiverDiagonalDerivative1831
import Fermat.OneThousandEightHundredThirtyOne.VandiverDiagonalUnits1831
import Fermat.OneThousandEightHundredThirtyOne.VandiverNormalizedCongruence1831

/-!
# From positive Vandiver relations to arbitrary primitive relations

The polynomial argument is naturally stated for nonnegative exponents.
This module isolates the exact normalization step which turns that result
into the `PrimitiveRelationCubeCongruences` interface consumed by
Vandiver's group-theoretic Lemma II core.
-/

open scoped BigOperators NumberField

namespace Fermat.OneThousandEightHundredThirtyOne.VandiverNormalizedRelationDerivative

noncomputable section

open Fermat.Irregular
open Fermat.Irregular.Voronoi
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma
open Fermat.OneThousandEightHundredThirtyOne.VandiverDiagonalDerivative
open Fermat.OneThousandEightHundredThirtyOne.VandiverDiagonalUnits
open Fermat.OneThousandEightHundredThirtyOne.VandiverNormalizedCongruence
open Fermat.OneThousandEightHundredThirtyOne.VandiverRelationNormalization

local instance : Fact (Nat.Prime 1831) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {1831} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 1831) K (by norm_num)

/-- The exact positive-relation derivative statement supplied by
Vandiver's polynomial-remainder calculation. -/
def PositiveRelationDerivativeCongruences1831 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1831) : Prop :=
  ∀ (v : (𝓞 K)ˣ) (t : ℕ) (b : SourceIndex 1831 → ℕ),
    IsVandiverDeep (K := K) (p := 1831) hzeta v →
    v ^ t = ∏ i, diagonalVandiverUnit1831 hzeta i ^ b i →
    ∀ k, HasPadicValAtLeast 1831 2
      (relationDerivative1831 (fun i ↦ (b i : ℤ)) k)

/-- Once the positive polynomial calculation is known, normalization
supplies the cube congruences for every integer exponent relation. -/
theorem primitiveRelationCubeCongruences_of_positive
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 1831)
    (u : (𝓞 K)ˣ)
    (hdeep : IsVandiverDeep (K := K) (p := 1831) hzeta u)
    (hpositive : PositiveRelationDerivativeCongruences1831 hzeta) :
    PrimitiveRelationCubeCongruences 1831 u
      (diagonalVandiverUnit1831 hzeta) := by
  intro t a ht hrel _hprimitive
  let b : SourceIndex 1831 → ℕ :=
    fun i ↦ normalizedRelationExponent1831 t (a i)
  let v : (𝓞 K)ˣ :=
    normalizedRelationUnit1831 u (diagonalVandiverUnit1831 hzeta) a
  have hvdeep : IsVandiverDeep (K := K) (p := 1831) hzeta v := by
    exact normalizedRelationUnit1831_isVandiverDeep
      hzeta u (diagonalVandiverUnit1831 hzeta) a hdeep
  have hvrel : v ^ t =
      ∏ i, diagonalVandiverUnit1831 hzeta i ^ b i := by
    exact normalizedRelationUnit1831_pow
      u (diagonalVandiverUnit1831 hzeta) t ht a hrel
  have hderivative :
      ∀ k, HasPadicValAtLeast 1831 2
        (relationDerivative1831 (fun i ↦ (b i : ℤ)) k) :=
    hpositive v t b hvdeep hvrel
  have hnormalized :=
    cubeCongruence_of_relationDerivative
      (fun i ↦ (b i : ℤ)) hderivative
  intro i
  exact cube_dvd_mul_of_normalizedRelationExponent1831
    t ht (a i) (vandiverBernoulliNumerator 1831 i)
      (by simpa only [b] using hnormalized i)

end

end Fermat.OneThousandEightHundredThirtyOne.VandiverNormalizedRelationDerivative
