import Fermat.Descent.GenericIrregular.DeepReality
import Fermat.Descent.Irregular.VandiverLemmaTwoBridge
import Fermat.Descent.Irregular.VandiverRealUnits

/-!
# A prime-generic finite-system form of Vandiver's Lemma II

The exponent-specific proofs all use the same assembly:

1. Vandiver's depth-`2p` hypothesis makes the ambient unit real;
2. a finite-index family of real cyclotomic units supplies a primitive
   relation;
3. the finite logarithmic-derivative computation supplies the
   coefficient-wise Bernoulli cube congruences;
4. the generic unit-power argument yields Vandiver's alternative.

`LemmaTwoUnitSystem` records only the exponent-dependent unit family and the
finite derivative output.  It deliberately does not contain
`VandiverLemmaTwo`, a unit-power conclusion, or a Fermat conclusion.
-/

open scoped BigOperators NumberField

namespace Fermat.GenericIrregular.LemmaTwo

noncomputable section

open Fermat.GenericIrregular.DeepReality
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma

variable {K : Type} {p : ℕ} [Fact p.Prime]
  [Field K] [NumberField K] [NumberField.IsCMField K]
  [IsCyclotomicExtension {p} ℚ K]

/-- The finite cyclotomic-unit and derivative data which vary with the
chosen prime.  Every field is strictly upstream of Vandiver's Lemma II. -/
structure LemmaTwoUnitSystem (K : Type) (p : ℕ)
    [Fact p.Prime] [Field K] [NumberField K]
    [NumberField.IsCMField K] [IsCyclotomicExtension {p} ℚ K] where
  /-- The diagonal unit family in the full cyclotomic integer ring. -/
  ambientFamily :
    ∀ {ζ : K}, IsPrimitiveRoot ζ p →
      SourceIndex p → (𝓞 K)ˣ
  /-- The same family, with reality included in its type. -/
  realFamily :
    ∀ {ζ : K}, IsPrimitiveRoot ζ p →
      SourceIndex p → NumberField.IsCMField.realUnits K
  /-- The two presentations are literally the same units. -/
  realFamily_coe :
    ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ p) (i : SourceIndex p),
      ((realFamily hζ i :
        NumberField.IsCMField.realUnits K) : (𝓞 K)ˣ) =
        ambientFamily hζ i
  /-- The exponent-specific residue determinant proves finite index. -/
  finiteIndex_realFamily :
    ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ p),
      (Subgroup.closure (Set.range (realFamily hζ))).FiniteIndex
  /-- Output of the finite polynomial/logarithmic-derivative calculation. -/
  relationCubeCongruences :
    ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ p)
      (u : (𝓞 K)ˣ), IsVandiverDeep hζ u →
        PrimitiveRelationCubeCongruences p u (ambientFamily hζ)

/-- Any honest finite unit system proves Vandiver's Lemma II uniformly in
the prime. -/
theorem vandiverLemmaTwo_of_unitSystem
    (hp5 : 5 ≤ p) (system : LemmaTwoUnitSystem K p) :
    VandiverLemmaTwo K p := by
  intro ζ hζ u hdeep
  let uReal : NumberField.IsCMField.realUnits K :=
    deepRealUnit hp5 hζ u hdeep
  have hcongAmbient :
      PrimitiveRelationCubeCongruences p u
        (system.ambientFamily hζ) :=
    system.relationCubeCongruences hζ u hdeep
  have hcongReal :
      PrimitiveRelationCubeCongruences p uReal
        (system.realFamily hζ) := by
    intro t a ht hrel hprimitive
    apply hcongAmbient t a ht
    · have hrel' := congrArg
          ((↑) : NumberField.IsCMField.realUnits K → (𝓞 K)ˣ) hrel
      simpa only [uReal, deepRealUnit_coe, system.realFamily_coe,
        Subgroup.coe_pow, Subgroup.coe_zpow,
        SubmonoidClass.coe_finsetProd] using hrel'
    · exact hprimitive
  letI :
      (Subgroup.closure
        (Set.range (system.realFamily hζ))).FiniteIndex :=
    system.finiteIndex_realFamily hζ
  have halternative :=
    Fermat.Irregular.VandiverLemmaTwoBridge.isPower_or_bernoulliObstruction
      (Fact.out : p.Prime)
      (Fermat.Irregular.VandiverRealUnits.odd_pow_injective
        (K := K) p
        ((Fact.out : p.Prime).odd_of_ne_two (by omega)))
      uReal (system.realFamily hζ) hcongReal
  rcases halternative with hpower | hobstruction
  · left
    obtain ⟨v, hv⟩ := hpower
    refine ⟨(v : (𝓞 K)ˣ), ?_⟩
    have hv' := congrArg
      ((↑) : NumberField.IsCMField.realUnits K → (𝓞 K)ˣ) hv
    simpa only [uReal, deepRealUnit_coe, Subgroup.coe_pow] using hv'
  · exact Or.inr hobstruction

end

end Fermat.GenericIrregular.LemmaTwo
