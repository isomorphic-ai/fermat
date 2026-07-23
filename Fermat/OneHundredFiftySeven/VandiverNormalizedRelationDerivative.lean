import Fermat.OneHundredFiftySeven.VandiverDiagonalDerivative157
import Fermat.OneHundredFiftySeven.VandiverDiagonalUnits157
import Fermat.OneHundredFiftySeven.VandiverNormalizedCongruence

/-!
# From positive Vandiver relations to arbitrary primitive relations

The polynomial argument is naturally stated for nonnegative exponents.
This module isolates the exact normalization step which turns that result
into the `PrimitiveRelationCubeCongruences` interface consumed by
Vandiver's group-theoretic Lemma II core.
-/

open scoped BigOperators NumberField

namespace Fermat.OneHundredFiftySeven.VandiverNormalizedRelationDerivative

noncomputable section

open Fermat.Irregular
open Fermat.Irregular.Voronoi
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma
open Fermat.OneHundredFiftySeven.VandiverDiagonalDerivative
open Fermat.OneHundredFiftySeven.VandiverDiagonalUnits
open Fermat.OneHundredFiftySeven.VandiverNormalizedCongruence
open Fermat.OneHundredFiftySeven.VandiverRelationNormalization

local instance : Fact (Nat.Prime 157) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {157} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 157) K (by norm_num)

/-- The exact positive-relation derivative statement supplied by
Vandiver's polynomial-remainder calculation. -/
def PositiveRelationDerivativeCongruences157 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 157) : Prop :=
  ∀ (v : (𝓞 K)ˣ) (t : ℕ) (b : SourceIndex 157 → ℕ),
    IsVandiverDeep (K := K) (p := 157) hzeta v →
    v ^ t = ∏ i, diagonalVandiverUnit157 hzeta i ^ b i →
    ∀ k, HasPadicValAtLeast 157 2
      (relationDerivative157 (fun i ↦ (b i : ℤ)) k)

/-- Once the positive polynomial calculation is known, normalization
supplies the cube congruences for every integer exponent relation. -/
theorem primitiveRelationCubeCongruences_of_positive
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 157)
    (u : (𝓞 K)ˣ)
    (hdeep : IsVandiverDeep (K := K) (p := 157) hzeta u)
    (hpositive : PositiveRelationDerivativeCongruences157 hzeta) :
    PrimitiveRelationCubeCongruences 157 u
      (diagonalVandiverUnit157 hzeta) := by
  intro t a ht hrel _hprimitive
  let b : SourceIndex 157 → ℕ :=
    fun i ↦ normalizedRelationExponent157 t (a i)
  let v : (𝓞 K)ˣ :=
    normalizedRelationUnit157 u (diagonalVandiverUnit157 hzeta) a
  have hvdeep : IsVandiverDeep (K := K) (p := 157) hzeta v := by
    exact normalizedRelationUnit157_isVandiverDeep
      hzeta u (diagonalVandiverUnit157 hzeta) a hdeep
  have hvrel : v ^ t =
      ∏ i, diagonalVandiverUnit157 hzeta i ^ b i := by
    exact normalizedRelationUnit157_pow
      u (diagonalVandiverUnit157 hzeta) t ht a hrel
  have hderivative :
      ∀ k, HasPadicValAtLeast 157 2
        (relationDerivative157 (fun i ↦ (b i : ℤ)) k) :=
    hpositive v t b hvdeep hvrel
  have hnormalized :=
    cubeCongruence_of_relationDerivative
      (fun i ↦ (b i : ℤ)) hderivative
  intro i
  exact cube_dvd_mul_of_normalizedRelationExponent157
    t ht (a i) (vandiverBernoulliNumerator 157 i)
      (by simpa only [b] using hnormalized i)

end

end Fermat.OneHundredFiftySeven.VandiverNormalizedRelationDerivative
