import Fermat.FourHundredNinetyOne.VandiverDiagonalDerivative491
import Fermat.FourHundredNinetyOne.VandiverDiagonalUnits491
import Fermat.FourHundredNinetyOne.VandiverNormalizedCongruence

/-!
# From positive Vandiver relations to arbitrary primitive relations

The polynomial argument is naturally stated for nonnegative exponents.
This module isolates the exact normalization step which turns that result
into the `PrimitiveRelationCubeCongruences` interface consumed by
Vandiver's group-theoretic Lemma II core.
-/

open scoped BigOperators NumberField

namespace Fermat.FourHundredNinetyOne.VandiverNormalizedRelationDerivative

noncomputable section

open Fermat.Irregular
open Fermat.Irregular.Voronoi
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma
open Fermat.FourHundredNinetyOne.VandiverDiagonalDerivative
open Fermat.FourHundredNinetyOne.VandiverDiagonalUnits
open Fermat.FourHundredNinetyOne.VandiverNormalizedCongruence
open Fermat.FourHundredNinetyOne.VandiverRelationNormalization

local instance : Fact (Nat.Prime 491) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {491} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 491) K (by norm_num)

/-- The exact positive-relation derivative statement supplied by
Vandiver's polynomial-remainder calculation. -/
def PositiveRelationDerivativeCongruences491 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491) : Prop :=
  ∀ (v : (𝓞 K)ˣ) (t : ℕ) (b : SourceIndex 491 → ℕ),
    IsVandiverDeep (K := K) (p := 491) hzeta v →
    v ^ t = ∏ i, diagonalVandiverUnit491 hzeta i ^ b i →
    ∀ k, HasPadicValAtLeast 491 2
      (relationDerivative491 (fun i ↦ (b i : ℤ)) k)

/-- Once the positive polynomial calculation is known, normalization
supplies the cube congruences for every integer exponent relation. -/
theorem primitiveRelationCubeCongruences_of_positive
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 491)
    (u : (𝓞 K)ˣ)
    (hdeep : IsVandiverDeep (K := K) (p := 491) hzeta u)
    (hpositive : PositiveRelationDerivativeCongruences491 hzeta) :
    PrimitiveRelationCubeCongruences 491 u
      (diagonalVandiverUnit491 hzeta) := by
  intro t a ht hrel _hprimitive
  let b : SourceIndex 491 → ℕ :=
    fun i ↦ normalizedRelationExponent491 t (a i)
  let v : (𝓞 K)ˣ :=
    normalizedRelationUnit491 u (diagonalVandiverUnit491 hzeta) a
  have hvdeep : IsVandiverDeep (K := K) (p := 491) hzeta v := by
    exact normalizedRelationUnit491_isVandiverDeep
      hzeta u (diagonalVandiverUnit491 hzeta) a hdeep
  have hvrel : v ^ t =
      ∏ i, diagonalVandiverUnit491 hzeta i ^ b i := by
    exact normalizedRelationUnit491_pow
      u (diagonalVandiverUnit491 hzeta) t ht a hrel
  have hderivative :
      ∀ k, HasPadicValAtLeast 491 2
        (relationDerivative491 (fun i ↦ (b i : ℤ)) k) :=
    hpositive v t b hvdeep hvrel
  have hnormalized :=
    cubeCongruence_of_relationDerivative
      (fun i ↦ (b i : ℤ)) hderivative
  intro i
  exact cube_dvd_mul_of_normalizedRelationExponent491
    t ht (a i) (vandiverBernoulliNumerator 491 i)
      (by simpa only [b] using hnormalized i)

end

end Fermat.FourHundredNinetyOne.VandiverNormalizedRelationDerivative
