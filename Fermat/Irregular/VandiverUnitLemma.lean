import Fermat.Irregular.KummerTheorem
import Fermat.Irregular.VandiverCriterion
import Fermat.Irregular.VandiverData
import FltRegular.NumberTheory.Cyclotomic.UnitLemmas

/-!
# The exact unit statement in Vandiver's Lemma 2

Vandiver's 1929 Lemma 2 (Transactions AMS 31, pp. 616--621) does **not**
start from the usual semiprimary congruence modulo the rational ideal `(p)`.
For a primitive `p`-th root `ζ` and `λ = ζ - 1`, its hypothesis is the much
deeper congruence

`u ≡ c^p (mod λ^(2*p))`.

It concludes that `u` is a `p`-th power unless one of the historical
Bernoulli numbers `B_(n*p)` is divisible by `p^3`.  Vandiver numbers
Bernoulli numbers by `B_n = |bernoulli (2*n)|`; consequently the modern Lean
index is `(2*n)*p`.

This file formalizes that exact theorem boundary and all reductions around
it.  The logarithmic proof of the source lemma itself still requires a
fundamental system of cyclotomic units and high-order local logarithmic
derivatives, neither of which is available in Mathlib.  It is therefore an
explicit hypothesis `VandiverLemmaTwo`, not an axiom or a silently weakened
claim.

The source-faithful predicate is
`VandiverCriterion.KummerUnitPowerConclusion`.  The broader premise needed by
the currently extracted descent is separately named
`VandiverCriterion.SemiprimaryUnitPowerConclusion`; an implication to that
interface is proved only under the explicitly named property
`SemiprimaryDeepening`.
-/

namespace Fermat.Irregular.VandiverUnitLemma

open scoped NumberField
open Fermat.Irregular

noncomputable section

/-! ## Vandiver's Bernoulli indexing -/

/-- Vandiver's index `n = 1, ..., (p-3)/2` in Lemma 2. -/
def sourceIndices (p : ℕ) : Finset ℕ :=
  Finset.Icc 1 ((p - 3) / 2)

/-- The exceptional alternative in Vandiver's Lemma 2, translated from his
`B_(n*p)` convention to Mathlib's modern index `B_((2*n)*p)`. -/
def BernoulliObstruction (p : ℕ) : Prop :=
  ∃ n ∈ sourceIndices p,
    (p : ℤ) ^ 3 ∣ (bernoulli ((2 * n) * p)).num

/-- The repository's all-even-index Bernoulli condition rules out exactly
the obstruction appearing in Vandiver's source notation. -/
theorem not_bernoulliObstruction_of_bernoulliCubeCondition
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hB : VandiverData.BernoulliCubeCondition p) :
    ¬BernoulliObstruction p := by
  intro hobs
  obtain ⟨n, hn, hdiv⟩ := hobs
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  obtain ⟨r, hr⟩ := hpodd
  have hn' := Finset.mem_Icc.mp hn
  apply hB (2 * n)
  · simp only [VandiverData.indices, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, ?_⟩, even_two.mul_right n⟩
    omega
  · simpa only [mul_assoc] using hdiv

/-- Conversely, ruling out Vandiver's historical indices gives the
repository's even-index formulation. -/
theorem bernoulliCubeCondition_of_not_bernoulliObstruction
    {p : ℕ} (hobs : ¬BernoulliObstruction p) :
    VandiverData.BernoulliCubeCondition p := by
  intro j hj hdiv
  have hj' : 2 ≤ j ∧ j ≤ p - 3 ∧ Even j := by
    simpa [VandiverData.indices, and_assoc] using hj
  obtain ⟨n, rfl⟩ := (even_iff_two_dvd.mp hj'.2.2)
  apply hobs
  refine ⟨n, Finset.mem_Icc.mpr ⟨by omega, ?_⟩, ?_⟩
  · omega
  · simpa only [mul_assoc] using hdiv

/-- The modern and historical Bernoulli conditions are exactly equivalent
in the prime range used by Vandiver's lemma. -/
theorem bernoulliCubeCondition_iff_not_bernoulliObstruction
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    VandiverData.BernoulliCubeCondition p ↔ ¬BernoulliObstruction p :=
  ⟨not_bernoulliObstruction_of_bernoulliCubeCondition hp5,
    bernoulliCubeCondition_of_not_bernoulliObstruction⟩

/-! ## The exact local congruence -/

variable {K : Type} {p : ℕ} [Fact p.Prime] [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]

/-- A unit satisfies the deep local hypothesis of Vandiver's Lemma 2 at a
chosen primitive root. -/
def IsVandiverDeep {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (u : (𝓞 K)ˣ) : Prop :=
  ∃ c : ℤ,
    ((1 : 𝓞 K) - hζ.unit') ^ (2 * p) ∣
      (u : 𝓞 K) - (c : 𝓞 K) ^ p

/-- Exact source shape of Vandiver's Lemma 2: a deeply congruent unit is a
`p`-th power, or the Bernoulli obstruction occurs.

This is the one remaining mathematical theorem boundary.  Its 1929 proof
uses a fundamental system of real cyclotomic units and `2kp`-th logarithmic
derivatives; those local analytic objects are not currently formalized. -/
def VandiverLemmaTwo (K : Type) (p : ℕ)
    [Fact p.Prime] [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] : Prop :=
  ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ p) (u : (𝓞 K)ˣ),
    IsVandiverDeep hζ u →
      (∃ v : (𝓞 K)ˣ, u = v ^ p) ∨ BernoulliObstruction p

/-- Vandiver's source lemma gives the source-faithful Kummer unit-power
conclusion as soon as its exceptional Bernoulli alternative is ruled out. -/
theorem kummerUnitPowerConclusion_of_no_obstruction
    (hLemmaTwo : VandiverLemmaTwo K p)
    (hno : ¬BernoulliObstruction p) :
    VandiverCriterion.KummerUnitPowerConclusion K p := by
  intro ζ hζ u hu
  rcases hLemmaTwo hζ u hu with hpow | hobs
  · exact hpow
  · exact (hno hobs).elim

/-- The exact source lemma plus the finite Bernoulli condition gives the
source-faithful Kummer unit-power conclusion.  No plus-class-number
assumption is used here; that separate hypothesis belongs to Vandiver's
ideal principalization (Lemma 1), represented in this repository by
`RelevantIdealQuotientsPrincipal`. -/
theorem kummerUnitPowerConclusion_of_lemmaTwo
    (hp5 : 5 ≤ p)
    (hLemmaTwo : VandiverLemmaTwo K p)
    (hB : VandiverData.BernoulliCubeCondition p) :
    VandiverCriterion.KummerUnitPowerConclusion K p :=
  kummerUnitPowerConclusion_of_no_obstruction hLemmaTwo
    (not_bernoulliObstruction_of_bernoulliCubeCondition hp5 hB)

/-! ## Relation to the existing broader descent interface -/

/-- The antecedent used by the current descent interface: congruence to a
rational integer modulo the rational ideal `(p)`. -/
def IsSemiprimaryModuloP (p : ℕ) (u : (𝓞 K)ˣ) : Prop :=
  ∃ n : ℤ, (p : 𝓞 K) ∣ (u - n : 𝓞 K)

/-- The additional statement needed to pass from the current broad descent
interface to Vandiver's much deeper source hypothesis.

It is deliberately separate: divisibility by `(p) = (ζ-1)^(p-1)` does not
by itself imply congruence to a `p`-th power modulo `(ζ-1)^(2p)`. -/
def SemiprimaryDeepening (K : Type) (p : ℕ)
    [Fact p.Prime] [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] : Prop :=
  ∃ (ζ : K) (hζ : IsPrimitiveRoot ζ p),
    ∀ u : (𝓞 K)ˣ, IsSemiprimaryModuloP p u → IsVandiverDeep hζ u

/-- Strongest honest bridge to the repository's existing broad unit
interface.  The exact Vandiver lemma and Bernoulli data provide the deep
conclusion; `hdeepen` is precisely the extra hypothesis needed because the
interface asks about all units congruent modulo `(p)`. -/
theorem semiprimaryUnitPowerConclusion_of_vandiver
    (hp5 : 5 ≤ p)
    (hLemmaTwo : VandiverLemmaTwo K p)
    (hB : VandiverData.BernoulliCubeCondition p)
    (hdeepen : SemiprimaryDeepening K p) :
    VandiverCriterion.SemiprimaryUnitPowerConclusion K p := by
  obtain ⟨ζ, hζ, hdeep⟩ := hdeepen
  have hpower : VandiverCriterion.KummerUnitPowerConclusion K p :=
    kummerUnitPowerConclusion_of_lemmaTwo (K := K) (p := p)
      hp5 hLemmaTwo hB
  intro u hu
  exact hpower hζ u (hdeep u hu)

/-- Package the two logically separate local inputs used by Vandiver's
descent.  Principalization is the plus-class (Lemma 1) side; the unit-power
conclusion is the deep-congruence/Bernoulli (Lemma 2) side. -/
theorem localCriterionInputs_of_vandiver
    (hpodd : p ≠ 2)
    (hprincipal : VandiverCriterion.RelevantIdealQuotientsPrincipal
      (K := K) hpodd)
    (hp5 : 5 ≤ p)
    (hLemmaTwo : VandiverLemmaTwo K p)
    (hB : VandiverData.BernoulliCubeCondition p)
    (hdeepen : SemiprimaryDeepening K p) :
    VandiverCriterion.RelevantIdealQuotientsPrincipal (K := K) hpodd ∧
      VandiverCriterion.SemiprimaryUnitPowerConclusion K p :=
  ⟨hprincipal,
    semiprimaryUnitPowerConclusion_of_vandiver hp5 hLemmaTwo hB hdeepen⟩

/-! ## Discharging regular Bernoulli indices with Kummer -/

/-- With the now-proved Kummer congruence, only genuinely irregular indices
need a high-Bernoulli computation in order to establish Vandiver's finite
Bernoulli condition. -/
theorem bernoulliCubeCondition_of_irregular
    (hp5 : 5 ≤ p)
    (hIrregular : ∀ j ∈ VandiverData.indices p,
      (p : ℤ) ∣ (bernoulli j).num →
        ¬(p : ℤ) ^ 3 ∣ (bernoulli (j * p)).num) :
    VandiverData.BernoulliCubeCondition p := by
  apply VandiverData.bernoulliCubeCondition_of_kummer_of_irregular hp5
  · intro j hj
    have hj' : 2 ≤ j ∧ j ≤ p - 3 ∧ Even j := by
      simpa [VandiverData.indices, and_assoc] using hj
    exact KummerTheorem.kummerCongruenceModPrime_irregularRange
      hp5 hj'.1 hj'.2.1 hj'.2.2
  · exact hIrregular

end

end Fermat.Irregular.VandiverUnitLemma
