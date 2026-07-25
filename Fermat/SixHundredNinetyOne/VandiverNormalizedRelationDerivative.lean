import Fermat.SixHundredNinetyOne.VandiverDiagonalDerivative691
import Fermat.SixHundredNinetyOne.VandiverDiagonalUnits691
import Fermat.SixHundredNinetyOne.VandiverNormalizedCongruence

/-!
# From positive Vandiver relations to arbitrary primitive relations

The polynomial argument is naturally stated for nonnegative exponents.
This module isolates the exact normalization step which turns that result
into the `PrimitiveRelationCubeCongruences` interface consumed by
Vandiver's group-theoretic Lemma II core.
-/

open scoped BigOperators NumberField

namespace Fermat.SixHundredNinetyOne.VandiverNormalizedRelationDerivative

noncomputable section

open Fermat.Irregular
open Fermat.Irregular.Voronoi
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma
open Fermat.SixHundredNinetyOne.VandiverDiagonalDerivative
open Fermat.SixHundredNinetyOne.VandiverDiagonalUnits
open Fermat.SixHundredNinetyOne.VandiverNormalizedCongruence
open Fermat.SixHundredNinetyOne.VandiverRelationNormalization

local instance : Fact (Nat.Prime 691) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {691} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 691) K (by norm_num)

/-- The exact positive-relation derivative statement supplied by
Vandiver's polynomial-remainder calculation. -/
def PositiveRelationDerivativeCongruences691 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 691) : Prop :=
  ∀ (v : (𝓞 K)ˣ) (t : ℕ) (b : SourceIndex 691 → ℕ),
    IsVandiverDeep (K := K) (p := 691) hzeta v →
    v ^ t = ∏ i, diagonalVandiverUnit691 hzeta i ^ b i →
    ∀ k, HasPadicValAtLeast 691 2
      (relationDerivative691 (fun i ↦ (b i : ℤ)) k)

/-- Once the positive polynomial calculation is known, normalization
supplies the cube congruences for every integer exponent relation. -/
theorem primitiveRelationCubeCongruences_of_positive
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 691)
    (u : (𝓞 K)ˣ)
    (hdeep : IsVandiverDeep (K := K) (p := 691) hzeta u)
    (hpositive : PositiveRelationDerivativeCongruences691 hzeta) :
    PrimitiveRelationCubeCongruences 691 u
      (diagonalVandiverUnit691 hzeta) := by
  intro t a ht hrel _hprimitive
  let b : SourceIndex 691 → ℕ :=
    fun i ↦ normalizedRelationExponent691 t (a i)
  let v : (𝓞 K)ˣ :=
    normalizedRelationUnit691 u (diagonalVandiverUnit691 hzeta) a
  have hvdeep : IsVandiverDeep (K := K) (p := 691) hzeta v := by
    exact normalizedRelationUnit691_isVandiverDeep
      hzeta u (diagonalVandiverUnit691 hzeta) a hdeep
  have hvrel : v ^ t =
      ∏ i, diagonalVandiverUnit691 hzeta i ^ b i := by
    exact normalizedRelationUnit691_pow
      u (diagonalVandiverUnit691 hzeta) t ht a hrel
  have hderivative :
      ∀ k, HasPadicValAtLeast 691 2
        (relationDerivative691 (fun i ↦ (b i : ℤ)) k) :=
    hpositive v t b hvdeep hvrel
  have hnormalized :=
    cubeCongruence_of_relationDerivative
      (fun i ↦ (b i : ℤ)) hderivative
  intro i
  exact cube_dvd_mul_of_normalizedRelationExponent691
    t ht (a i) (vandiverBernoulliNumerator 691 i)
      (by simpa only [b] using hnormalized i)

end

end Fermat.SixHundredNinetyOne.VandiverNormalizedRelationDerivative
