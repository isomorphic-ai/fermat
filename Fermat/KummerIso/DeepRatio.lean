import Fermat.KummerIso.WeightedSolution
import Fermat.KummerIso.UnitExtraction
import Fermat.GenericIrregular.LemmaTwo
import Fermat.Irregular.VandiverHistoricalPrime
import Fermat.Irregular.VandiverLemmaTwoBridge
import FltRegular.CaseII.InductionStep

/-!
# The exact unit ratio at the Kummer splice

There are two weighted equations in the repository which must not be
silently identified.

* `KummerIso.WeightedSolution` is the public shape of the weighted equation
  produced by the regular-style induction in `VandiverCriterion`.
  Its equation proves that `ε₁ / ε₂` is semiprimary modulo `(p)`.
  No existing theorem upgrades this particular ratio to Vandiver's depth
  `(1 - ζ) ^ (2 * p)`.
* `VandiverHistoricalPrime.WeightedReductionData` is the independently
  constructed source-faithful equation-(10) package.  Its
  `highCongruence` field proves the depth-`2p` statement for the literal
  quotient `epsilon₁ / epsilon₂`.

This file records both facts and composes the second one with the generic
primitive-relation calculation.  The remaining direct-splice input for the
regular-style witness stays visible as `RegularUnitRatioDeep`; it is not
stored as a power conclusion.
-/

namespace Fermat.KummerIso.DeepRatio

open scoped NumberField

open Fermat.Irregular
open Fermat.Irregular.VandiverHistoricalPrime
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma

noncomputable section

variable {K : Type} {p : ℕ} [Fact p.Prime]
  [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-! ## The regular-style weighted ratio -/

/-- The exact missing depth assertion for one regular-style weighted
solution.  This is deliberately a proposition about the displayed ratio,
not a field containing a `p`-th root. -/
def RegularUnitRatioDeep
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) {m : ℕ}
    (w : WeightedSolution (𝓞 K) p m
      ((hζ.unit' : 𝓞 K) - 1)) : Prop :=
  IsVandiverDeep hζ w.unitRatio

/-- The regular-style weighted equation proves the weaker statement which
the upstream Kummer proof actually extracts: its exact ratio is congruent
to a rational integer modulo `(p)`.

The rational integer produced here is itself a `p`-th power.  This theorem
therefore identifies precisely how far the existing regular induction gets
without claiming the unavailable depth-`2p` upgrade. -/
theorem regularUnitRatio_isSemiprimaryModuloP
    (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) {m : ℕ}
    (hm : 1 ≤ m)
    (w : WeightedSolution (𝓞 K) p m
      ((hζ.unit' : 𝓞 K) - 1)) :
    IsSemiprimaryModuloP (K := K) p w.unitRatio := by
  let π : 𝓞 K := (hζ.unit' : 𝓞 K) - 1
  have hmp : p - 1 ≤ m * p :=
    (Nat.sub_le _ _).trans
      ((le_of_eq (one_mul p).symm).trans
        (Nat.mul_le_mul_right p hm))
  have e' := w.equation
  change
    (w.ε₁ : 𝓞 K) * w.x ^ p + (w.ε₂ : 𝓞 K) * w.y ^ p =
      (w.ε₃ : 𝓞 K) * (π ^ m * w.z) ^ p at e'
  rw [mul_pow, ← pow_mul, mul_comm (w.ε₃ : 𝓞 K), mul_assoc,
    ← Nat.sub_add_cancel hmp, add_comm _ (p - 1), pow_add,
    mul_assoc] at e'
  simp only [π] at e'
  apply_fun Ideal.Quotient.mk
    (Ideal.span <| Set.singleton (p : 𝓞 K)) at e'
  have hzero :
      Ideal.Quotient.mk
          (Ideal.span <| Set.singleton (p : 𝓞 K))
          (((hζ.unit' : 𝓞 K) - 1) ^ (p - 1)) = 0 :=
    (Ideal.Quotient.eq_zero_iff_dvd _ _).mpr
      (associated_zeta_sub_one_pow_prime hζ).symm.dvd
  rw [map_mul, hzero, zero_mul] at e'
  have e'div :
      (p : 𝓞 K) ∣
        (w.ε₁ : 𝓞 K) * w.x ^ p +
          (w.ε₂ : 𝓞 K) * w.y ^ p :=
    (Ideal.Quotient.eq_zero_iff_dvd
      (p : 𝓞 K)
      ((w.ε₁ : 𝓞 K) * w.x ^ p +
        (w.ε₂ : 𝓞 K) * w.y ^ p)).mp e'
  obtain ⟨a, ha⟩ :=
    exists_solution'_aux hp2 hζ w.not_pi_dvd_x e'div
  obtain ⟨b, hb⟩ := exists_dvd_pow_sub_Int_pow hp2 a
  have hab := dvd_add ha hb
  rw [sub_add_sub_cancel, ← Int.cast_pow] at hab
  exact ⟨b ^ p, by simpa only [WeightedSolution.unitRatio] using hab⟩

section RegularUnitSystem

variable [NumberField.IsCMField K]

/-- Once the exact missing depth assertion is supplied for a regular-style
weighted witness, the generic logarithmic-derivative system applies to that
literal ratio. -/
theorem regularUnitRatio_cubeCongruences
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) {m : ℕ}
    (system : Fermat.GenericIrregular.LemmaTwo.LemmaTwoUnitSystem K p)
    (w : WeightedSolution (𝓞 K) p m
      ((hζ.unit' : 𝓞 K) - 1))
    (hdeep : RegularUnitRatioDeep hζ w) :
    PrimitiveRelationCubeCongruences p w.unitRatio
      (system.ambientFamily hζ) :=
  system.relationCubeCongruences hζ w.unitRatio hdeep

/-- Narrow relevant-unit provider for the regular induction.

This theorem performs all work after the genuinely missing input
`RegularUnitRatioDeep`: the primitive-relation congruences, normalized
correction isomorphism, and Bézout extraction produce a root for this exact
weighted ratio. -/
theorem regularUnitRatio_isPower
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) {m : ℕ}
    (system : Fermat.GenericIrregular.LemmaTwo.LemmaTwoUnitSystem K p)
    (hno : NoBernoulliObstruction p)
    (w : WeightedSolution (𝓞 K) p m
      ((hζ.unit' : 𝓞 K) - 1))
    (hdeep : RegularUnitRatioDeep hζ w) :
    ∃ v : (𝓞 K)ˣ, w.unitRatio = v ^ p :=
  Fermat.KummerIso.UnitExtraction.isPower_of_unitSystem_of_noBernoulliObstruction
    hp5 system hζ w.unitRatio hdeep hno

end RegularUnitSystem

/-! ## The source-faithful historical weighted ratio -/

section Historical

variable [NumberField.IsCMField K]

/-- The literal unit quotient in Vandiver's historical weighted equation. -/
def historicalUnitRatio
    {ζ : K} {hζ : IsPrimitiveRoot ζ p}
    {s : Fermat.Irregular.VandiverHistoricalDescent.HistoricalState hζ}
    (d : WeightedReductionData hζ s) : (𝓞 K)ˣ :=
  d.epsilon₁ / d.epsilon₂

omit [IsCyclotomicExtension {p} ℚ K] in
@[simp]
theorem historicalUnitRatio_eq
    {ζ : K} {hζ : IsPrimitiveRoot ζ p}
    {s : Fermat.Irregular.VandiverHistoricalDescent.HistoricalState hζ}
    (d : WeightedReductionData hζ s) :
    historicalUnitRatio (p := p) d = d.epsilon₁ / d.epsilon₂ :=
  rfl

omit [IsCyclotomicExtension {p} ℚ K] in
/-- Equation (10) closes the depth seam for the exact historical weighted
ratio.  Unlike `RegularUnitRatioDeep`, this theorem needs no additional
deepening premise. -/
theorem historicalUnitRatio_isVandiverDeep
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {s : Fermat.Irregular.VandiverHistoricalDescent.HistoricalState hζ}
    (d : WeightedReductionData hζ s) :
    IsVandiverDeep hζ (historicalUnitRatio (p := p) d) :=
  ⟨d.rationalBase, by
    simpa only [historicalUnitRatio] using d.highCongruence⟩

section UnitSystem

/-- The generic finite unit system turns the already-proved deep
congruence for the exact historical ratio into Vandiver's coefficientwise
primitive-relation cube congruences. -/
theorem historicalUnitRatio_cubeCongruences
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {s : Fermat.Irregular.VandiverHistoricalDescent.HistoricalState hζ}
    (system : Fermat.GenericIrregular.LemmaTwo.LemmaTwoUnitSystem K p)
    (d : WeightedReductionData hζ s) :
    PrimitiveRelationCubeCongruences p (historicalUnitRatio (p := p) d)
      (system.ambientFamily hζ) :=
  system.relationCubeCongruences hζ (historicalUnitRatio (p := p) d)
    (historicalUnitRatio_isVandiverDeep (p := p) hζ d)

/-- The exact historical ratio satisfies Vandiver's source alternative:
it is a `p`-th power unless the historical Bernoulli obstruction occurs. -/
theorem historicalUnitRatio_isPower_or_bernoulliObstruction
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {s : Fermat.Irregular.VandiverHistoricalDescent.HistoricalState hζ}
    (system : Fermat.GenericIrregular.LemmaTwo.LemmaTwoUnitSystem K p)
    (d : WeightedReductionData hζ s) :
    (∃ v : (𝓞 K)ˣ,
      historicalUnitRatio (p := p) d = v ^ p) ∨
      BernoulliObstruction p := by
  exact
    Fermat.KummerIso.UnitExtraction.vandiverLemmaTwo_of_unitSystem
      hp5 system hζ (historicalUnitRatio (p := p) d)
        (historicalUnitRatio_isVandiverDeep (p := p) hζ d)

/-- The complete relevant-unit provider for the historical route.

Its two inputs are genuinely upstream arithmetic data:

* a finite cyclotomic-unit system proving the primitive-relation
  congruences; and
* nonoccurrence of the lifted Bernoulli cube obstruction.

The conclusion for the exact ratio is then kernel-checked. -/
theorem historicalUnitRatio_isPower
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {s : Fermat.Irregular.VandiverHistoricalDescent.HistoricalState hζ}
    (system : Fermat.GenericIrregular.LemmaTwo.LemmaTwoUnitSystem K p)
    (hno : NoBernoulliObstruction p)
    (d : WeightedReductionData hζ s) :
    ∃ v : (𝓞 K)ˣ,
      historicalUnitRatio (p := p) d = v ^ p := by
  exact
    Fermat.KummerIso.UnitExtraction.isPower_of_unitSystem_of_noBernoulliObstruction
      hp5 system hζ (historicalUnitRatio (p := p) d)
      (historicalUnitRatio_isVandiverDeep (p := p) hζ d) hno

end UnitSystem

end Historical

end

end Fermat.KummerIso.DeepRatio
