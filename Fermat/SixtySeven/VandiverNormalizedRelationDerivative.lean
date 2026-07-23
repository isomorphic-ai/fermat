import Fermat.SixtySeven.VandiverDiagonalDerivative67
import Fermat.SixtySeven.VandiverDiagonalUnits67
import Fermat.SixtySeven.VandiverNormalizedCongruence

/-!
# From positive Vandiver relations to arbitrary primitive relations

The polynomial argument is naturally stated for nonnegative exponents.
This module isolates the exact normalization step which turns that result
into the `PrimitiveRelationCubeCongruences` interface consumed by
Vandiver's group-theoretic Lemma II core.
-/

open scoped BigOperators NumberField

namespace Fermat.SixtySeven.VandiverNormalizedRelationDerivative

noncomputable section

open Fermat.Irregular
open Fermat.Irregular.Voronoi
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma
open Fermat.SixtySeven.VandiverDiagonalDerivative
open Fermat.SixtySeven.VandiverDiagonalUnits
open Fermat.SixtySeven.VandiverNormalizedCongruence
open Fermat.SixtySeven.VandiverRelationNormalization

local instance : Fact (Nat.Prime 67) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {67} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 67) K (by norm_num)

/-- The exact positive-relation derivative statement supplied by
Vandiver's polynomial-remainder calculation. -/
def PositiveRelationDerivativeCongruences67 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 67) : Prop :=
  ∀ (v : (𝓞 K)ˣ) (t : ℕ) (b : SourceIndex 67 → ℕ),
    IsVandiverDeep (K := K) (p := 67) hzeta v →
    v ^ t = ∏ i, diagonalVandiverUnit67 hzeta i ^ b i →
    ∀ k, HasPadicValAtLeast 67 2
      (relationDerivative67 (fun i ↦ (b i : ℤ)) k)

/-- Once the positive polynomial calculation is known, normalization
supplies the cube congruences for every integer exponent relation. -/
theorem primitiveRelationCubeCongruences_of_positive
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 67)
    (u : (𝓞 K)ˣ)
    (hdeep : IsVandiverDeep (K := K) (p := 67) hzeta u)
    (hpositive : PositiveRelationDerivativeCongruences67 hzeta) :
    PrimitiveRelationCubeCongruences 67 u
      (diagonalVandiverUnit67 hzeta) := by
  intro t a ht hrel _hprimitive
  let b : SourceIndex 67 → ℕ :=
    fun i ↦ normalizedRelationExponent67 t (a i)
  let v : (𝓞 K)ˣ :=
    normalizedRelationUnit67 u (diagonalVandiverUnit67 hzeta) a
  have hvdeep : IsVandiverDeep (K := K) (p := 67) hzeta v := by
    exact normalizedRelationUnit67_isVandiverDeep
      hzeta u (diagonalVandiverUnit67 hzeta) a hdeep
  have hvrel : v ^ t =
      ∏ i, diagonalVandiverUnit67 hzeta i ^ b i := by
    exact normalizedRelationUnit67_pow
      u (diagonalVandiverUnit67 hzeta) t ht a hrel
  have hderivative :
      ∀ k, HasPadicValAtLeast 67 2
        (relationDerivative67 (fun i ↦ (b i : ℤ)) k) :=
    hpositive v t b hvdeep hvrel
  have hnormalized :=
    cubeCongruence_of_relationDerivative
      (fun i ↦ (b i : ℤ)) hderivative
  intro i
  exact cube_dvd_mul_of_normalizedRelationExponent67
    t ht (a i) (vandiverBernoulliNumerator 67 i)
      (by simpa only [b] using hnormalized i)

end

end Fermat.SixtySeven.VandiverNormalizedRelationDerivative
