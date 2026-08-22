import Fermat.Exponents.SixHundredSeven.VandiverDiagonalDerivative607
import Fermat.Exponents.SixHundredSeven.VandiverDiagonalUnits607
import Fermat.Exponents.SixHundredSeven.VandiverNormalizedCongruence607

/-!
# From positive Vandiver relations to arbitrary primitive relations

The polynomial argument is naturally stated for nonnegative exponents.
This module isolates the exact normalization step which turns that result
into the `PrimitiveRelationCubeCongruences` interface consumed by
Vandiver's group-theoretic Lemma II core.
-/

open scoped BigOperators NumberField

namespace Fermat.SixHundredSeven.VandiverNormalizedRelationDerivative

noncomputable section

open Fermat.Irregular
open Fermat.Irregular.Voronoi
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma
open Fermat.SixHundredSeven.VandiverDiagonalDerivative
open Fermat.SixHundredSeven.VandiverDiagonalUnits
open Fermat.SixHundredSeven.VandiverNormalizedCongruence
open Fermat.SixHundredSeven.VandiverRelationNormalization

local instance : Fact (Nat.Prime 607) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {607} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 607) K (by norm_num)

/-- The exact positive-relation derivative statement supplied by
Vandiver's polynomial-remainder calculation. -/
def PositiveRelationDerivativeCongruences607 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 607) : Prop :=
  ∀ (v : (𝓞 K)ˣ) (t : ℕ) (b : SourceIndex 607 → ℕ),
    IsVandiverDeep (K := K) (p := 607) hzeta v →
    v ^ t = ∏ i, diagonalVandiverUnit607 hzeta i ^ b i →
    ∀ k, HasPadicValAtLeast 607 2
      (relationDerivative607 (fun i ↦ (b i : ℤ)) k)

/-- Once the positive polynomial calculation is known, normalization
supplies the cube congruences for every integer exponent relation. -/
theorem primitiveRelationCubeCongruences_of_positive
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 607)
    (u : (𝓞 K)ˣ)
    (hdeep : IsVandiverDeep (K := K) (p := 607) hzeta u)
    (hpositive : PositiveRelationDerivativeCongruences607 hzeta) :
    PrimitiveRelationCubeCongruences 607 u
      (diagonalVandiverUnit607 hzeta) := by
  intro t a ht hrel _hprimitive
  let b : SourceIndex 607 → ℕ :=
    fun i ↦ normalizedRelationExponent607 t (a i)
  let v : (𝓞 K)ˣ :=
    normalizedRelationUnit607 u (diagonalVandiverUnit607 hzeta) a
  have hvdeep : IsVandiverDeep (K := K) (p := 607) hzeta v := by
    exact normalizedRelationUnit607_isVandiverDeep
      hzeta u (diagonalVandiverUnit607 hzeta) a hdeep
  have hvrel : v ^ t =
      ∏ i, diagonalVandiverUnit607 hzeta i ^ b i := by
    exact normalizedRelationUnit607_pow
      u (diagonalVandiverUnit607 hzeta) t ht a hrel
  have hderivative :
      ∀ k, HasPadicValAtLeast 607 2
        (relationDerivative607 (fun i ↦ (b i : ℤ)) k) :=
    hpositive v t b hvdeep hvrel
  have hnormalized :=
    cubeCongruence_of_relationDerivative
      (fun i ↦ (b i : ℤ)) hderivative
  intro i
  exact cube_dvd_mul_of_normalizedRelationExponent607
    t ht (a i) (vandiverBernoulliNumerator 607 i)
      (by simpa only [b] using hnormalized i)

end

end Fermat.SixHundredSeven.VandiverNormalizedRelationDerivative
