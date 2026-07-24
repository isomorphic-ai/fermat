import Fermat.Irregular.VandiverLogDerivative
import Fermat.Irregular.VandiverUnitPower

/-!
# A generic core theorem for Vandiver's Lemma 2

This module joins the formal logarithmic-derivative calculation to the
unit-power algebra, with Vandiver's exact historical indexing.  His index
`n = 1, ..., (p - 3) / 2` is represented by `SourceIndex p`, whose element
`i` has source number `i + 1`.  The associated modern Bernoulli number is

`bernoulli ((2 * (i + 1)) * p)`.

`PrimitiveRelationCubeCongruences` is now the single sharply isolated seam
in the 1929 argument.  It is not a unit-power conclusion: it states only
the output of pp. 619--621, namely that the polynomial-remainder identity
and its high logarithmic derivatives imply

`p^3 ∣ a_i * numerator (B_((2*i)*p))`

for every exponent in a primitive unit relation.  Given that exact
congruence, the final theorem proves the unit is a `p`-th power.
-/

namespace Fermat.Irregular.VandiverLemmaTwoCore

open scoped BigOperators
open Fermat.Irregular

/-- Vandiver's `1, ..., (p - 3) / 2`, represented with zero-based `Fin`
indices. -/
abbrev SourceIndex (p : ℕ) := Fin ((p - 3) / 2)

/-- The one-based number printed in Vandiver's source. -/
def sourceNumber {p : ℕ} (i : SourceIndex p) : ℕ := i + 1

/-- Numerator of the modern Bernoulli number corresponding to Vandiver's
historical `B_((i+1)*p)`. -/
def vandiverBernoulliNumerator (p : ℕ) (i : SourceIndex p) : ℤ :=
  (bernoulli ((2 * sourceNumber i) * p)).num

/-- Absence of Vandiver's exceptional `p^3` Bernoulli divisibility. -/
def NoBernoulliObstruction (p : ℕ) : Prop :=
  ∀ i : SourceIndex p,
    ¬(p : ℤ) ^ 3 ∣ vandiverBernoulliNumerator p i

/-- Exact specialization of the formal logarithmic-derivative formula to
Vandiver's Bernoulli index `(2 * (i+1)) * p`.  This is the Bernoulli factor
that enters his derivative congruence. -/
theorem source_logarithmicDerivative_formula
    (r : ℚ) (p : ℕ) (hp : 0 < p) (i : SourceIndex p) :
    VandiverLogDerivative.formalDerivativeAtZero
        (2 * (sourceNumber i * p) - 1)
        (VandiverLogDerivative.vandiverLogDerivative r) =
      bernoulli ((2 * sourceNumber i) * p) /
          ((2 * sourceNumber i) * p) *
        (r ^ ((2 * sourceNumber i) * p) - 1) := by
  rw [VandiverLogDerivative.even_formalDerivativeAtZero_vandiverLogDerivative
    r (sourceNumber i * p) (Nat.mul_pos (by simp [sourceNumber]) hp)]
  congr 1
  · rw [show 2 * (sourceNumber i * p) =
      (2 * sourceNumber i) * p by simp only [Nat.mul_assoc]]
    push_cast
    simp only [mul_assoc]
  · congr 2
    simp only [Nat.mul_assoc]

/-- The exact remaining polynomial/high-derivative statement in the
generic proof of Vandiver's Lemma 2.

It applies only to positive primitive relations and concludes only the
coefficient-wise cube divisibilities used on p. 621. -/
def PrimitiveRelationCubeCongruences
    {G : Type*} [CommGroup G] (p : ℕ) (u : G)
    (E : SourceIndex p → G) : Prop :=
  ∀ (t : ℕ) (a : SourceIndex p → ℤ),
    0 < t →
    u ^ t = ∏ i, E i ^ a i →
    ¬(p ∣ t ∧ ∀ i, (p : ℤ) ∣ a i) →
    ∀ i, (p : ℤ) ^ 3 ∣
      a i * vandiverBernoulliNumerator p i

/-- Generic form of Vandiver's Lemma 2 after the polynomial-remainder
derivative congruence has been supplied.

Finite index creates the unit relation; injectivity of the `p`-power map
normalizes it; `hcong` and the absence of a Bernoulli obstruction force all
family exponents to be divisible by `p`; primitivity and Bézout then produce
the claimed `p`-th root. -/
theorem isPower_of_primitiveRelationCubeCongruences
    {G : Type*} [CommGroup G] {p : ℕ} (hp : p.Prime)
    (hpow : Function.Injective (fun x : G ↦ x ^ p))
    (u : G) (E : SourceIndex p → G)
    [hfinite : (Subgroup.closure (Set.range E)).FiniteIndex]
    (hcong : PrimitiveRelationCubeCongruences p u E)
    (hno : NoBernoulliObstruction p) :
    ∃ v : G, u = v ^ p := by
  exact VandiverUnitPower.isPower_of_finiteIndex_family_and_cube_congruences
    hp hpow u E (vandiverBernoulliNumerator p) hcong hno

end Fermat.Irregular.VandiverLemmaTwoCore
