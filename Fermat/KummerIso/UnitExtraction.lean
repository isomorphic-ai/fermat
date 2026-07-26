import Fermat.GenericIrregular.ChannelCertificate
import Fermat.GenericIrregular.DeepReality
import Fermat.GenericIrregular.LemmaTwo
import Fermat.Irregular.VandiverRealUnits
import Fermat.KummerIso.Correction

/-!
# Unit extraction through the regularized Kummer correction

This file proves Vandiver's Lemma II from the generic finite unit system by
passing through the honest mixed Bernoulli correction in
`KummerIso.Correction`.

For a deeply congruent unit, the proof:

1. moves to the real-unit subgroup, where the odd `p`-power map is injective;
2. transports the primitive-relation cube congruences to that subgroup;
3. uses the actual normalized quotient by `p ^ 2` on every exceptional
   coordinate and the ordinary scalar argument elsewhere;
4. inverts the resulting diagonal automorphism and extracts a `p`-th root.

In particular, this proof does not delegate to
`GenericIrregular.LemmaTwo.vandiverLemmaTwo_of_unitSystem`.
-/

open scoped BigOperators NumberField

namespace Fermat.KummerIso.UnitExtraction

noncomputable section

open Fermat.GenericIrregular.ChannelCertificate
open Fermat.GenericIrregular.DeepReality
open Fermat.GenericIrregular.LemmaTwo
open Fermat.Irregular.VandiverLemmaTwoBridge
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma

variable {K : Type} {p : ℕ} [Fact p.Prime]
  [Field K] [NumberField K] [NumberField.IsCMField K]
  [IsCyclotomicExtension {p} ℚ K]

/-- The no-obstruction branch of Vandiver's unit argument, proved through
the normalized correction automorphism.

The finite-index relation and its logarithmic-derivative congruences come
from `system`; `hno` supplies precisely the assertion that no normalized
diagonal entry vanishes modulo `p`. -/
theorem isPower_of_unitSystem_of_noBernoulliObstruction
    (hp5 : 5 ≤ p)
    (system : LemmaTwoUnitSystem K p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (u : (𝓞 K)ˣ) (hdeep : IsVandiverDeep hζ u)
    (hno : NoBernoulliObstruction p) :
    ∃ v : (𝓞 K)ˣ, u = v ^ p := by
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
          ((↑) : NumberField.IsCMField.realUnits K → (𝓞 K)ˣ)
          hrel
      simpa only [uReal, deepRealUnit_coe, system.realFamily_coe,
        Subgroup.coe_pow, Subgroup.coe_zpow,
        SubmonoidClass.coe_finsetProd] using hrel'
    · exact hprimitive
  letI :
      (Subgroup.closure
        (Set.range (system.realFamily hζ))).FiniteIndex :=
    system.finiteIndex_realFamily hζ
  obtain ⟨v, hv⟩ :=
    Fermat.KummerIso.Correction.isPower_of_vandiver_regularized
      (Fact.out : p.Prime)
      (Fermat.Irregular.VandiverRealUnits.odd_pow_injective
        (K := K) p
        ((Fact.out : p.Prime).odd_of_ne_two (by omega)))
      uReal (system.realFamily hζ) hcongReal hno
  refine ⟨(v : (𝓞 K)ˣ), ?_⟩
  have hv' := congrArg
    ((↑) : NumberField.IsCMField.realUnits K → (𝓞 K)ˣ) hv
  simpa only [uReal, deepRealUnit_coe, Subgroup.coe_pow] using hv'

/-- Any honest finite unit system proves Vandiver's source-shaped
alternative, with the no-obstruction branch routed through the normalized
Kummer correction. -/
theorem vandiverLemmaTwo_of_unitSystem
    (hp5 : 5 ≤ p) (system : LemmaTwoUnitSystem K p) :
    VandiverLemmaTwo K p := by
  intro ζ hζ u hdeep
  by_cases hobs : BernoulliObstruction p
  · exact Or.inr hobs
  · exact Or.inl <|
      isPower_of_unitSystem_of_noBernoulliObstruction
        hp5 system hζ u hdeep
          (noBernoulliObstruction_iff.mpr hobs)

/-- Axis-8 channel data rule out the exceptional alternative and turn the
regularized Lemma II into the exact deep-unit power conclusion used by
Vandiver's descent. -/
theorem kummerUnitPowerConclusion_of_unitSystem_of_channels
    {N : ℕ}
    (hp5 : 5 ≤ p)
    (system : LemmaTwoUnitSystem K p)
    (channels : FixedChannelCertificate p N) :
    Fermat.Irregular.VandiverCriterion.KummerUnitPowerConclusion K p :=
  kummerUnitPowerConclusion_of_lemmaTwo hp5
    (vandiverLemmaTwo_of_unitSystem hp5 system)
    (channels.bernoulliCubeCondition hp5)

end

end Fermat.KummerIso.UnitExtraction
