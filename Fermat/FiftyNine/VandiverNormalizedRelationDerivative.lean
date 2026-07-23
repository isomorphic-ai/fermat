import Fermat.FiftyNine.VandiverDiagonalDerivative
import Fermat.FiftyNine.VandiverDiagonalUnits
import Fermat.FiftyNine.VandiverNormalizedCongruence

/-!
# From positive Vandiver relations to arbitrary primitive relations

The polynomial argument is naturally stated for nonnegative exponents.
This module isolates the exact normalization step which turns that result
into the `PrimitiveRelationCubeCongruences` interface consumed by
Vandiver's group-theoretic Lemma II core.
-/

open scoped BigOperators NumberField

namespace Fermat.FiftyNine.VandiverNormalizedRelationDerivative

noncomputable section

open Fermat.Irregular
open Fermat.Irregular.Voronoi
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma
open Fermat.FiftyNine.VandiverDiagonalDerivative
open Fermat.FiftyNine.VandiverDiagonalUnits
open Fermat.FiftyNine.VandiverNormalizedCongruence
open Fermat.FiftyNine.VandiverRelationNormalization

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 59) K (by norm_num)

/-- The exact positive-relation derivative statement supplied by
Vandiver's polynomial-remainder calculation. -/
def PositiveRelationDerivativeCongruences59 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 59) : Prop :=
  ∀ (v : (𝓞 K)ˣ) (t : ℕ) (b : SourceIndex 59 → ℕ),
    IsVandiverDeep (K := K) (p := 59) hzeta v →
    v ^ t = ∏ i, diagonalVandiverUnit59 hzeta i ^ b i →
    ∀ k, HasPadicValAtLeast 59 2
      (relationDerivative59 (fun i ↦ (b i : ℤ)) k)

/-- Once the positive polynomial calculation is known, normalization
supplies the cube congruences for every integer exponent relation. -/
theorem primitiveRelationCubeCongruences_of_positive
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 59)
    (u : (𝓞 K)ˣ)
    (hdeep : IsVandiverDeep (K := K) (p := 59) hzeta u)
    (hpositive : PositiveRelationDerivativeCongruences59 hzeta) :
    PrimitiveRelationCubeCongruences 59 u
      (diagonalVandiverUnit59 hzeta) := by
  intro t a ht hrel _hprimitive
  let b : SourceIndex 59 → ℕ :=
    fun i ↦ normalizedRelationExponent59 t (a i)
  let v : (𝓞 K)ˣ :=
    normalizedRelationUnit59 u (diagonalVandiverUnit59 hzeta) a
  have hvdeep : IsVandiverDeep (K := K) (p := 59) hzeta v := by
    exact normalizedRelationUnit59_isVandiverDeep
      hzeta u (diagonalVandiverUnit59 hzeta) a hdeep
  have hvrel : v ^ t =
      ∏ i, diagonalVandiverUnit59 hzeta i ^ b i := by
    exact normalizedRelationUnit59_pow
      u (diagonalVandiverUnit59 hzeta) t ht a hrel
  have hderivative :
      ∀ k, HasPadicValAtLeast 59 2
        (relationDerivative59 (fun i ↦ (b i : ℤ)) k) :=
    hpositive v t b hvdeep hvrel
  have hnormalized :=
    cubeCongruence_of_relationDerivative
      (fun i ↦ (b i : ℤ)) hderivative
  intro i
  exact cube_dvd_mul_of_normalizedRelationExponent59
    t ht (a i) (vandiverBernoulliNumerator 59 i)
      (by simpa only [b] using hnormalized i)

end

end Fermat.FiftyNine.VandiverNormalizedRelationDerivative
