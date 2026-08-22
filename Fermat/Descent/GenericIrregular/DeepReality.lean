import Fermat.Descent.Irregular.TakagiHistoricalPrime
import Fermat.Descent.Irregular.VandiverTakagiPairPrime
import Fermat.Descent.Irregular.VandiverUnitLemma

/-!
# Deep Vandiver units are real, uniformly in the prime

Vandiver's depth-`2p` congruence forces an ambient cyclotomic unit to be
fixed by complex conjugation.  The proof uses only the prime-generic
uniformizer and CM-unit lemmas already present in `Fermat.Irregular`.
-/

open scoped NumberField

namespace Fermat.GenericIrregular.DeepReality

noncomputable section

open Fermat.Irregular.VandiverUnitLemma

variable {K : Type} {p : ℕ} [Fact p.Prime]
  [Field K] [NumberField K] [NumberField.IsCMField K]
  [IsCyclotomicExtension {p} ℚ K]

/-- The depth-`2p` local hypothesis forces the unit to be real. -/
theorem isVandiverDeep_unitsComplexConj_eq
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (u : (𝓞 K)ˣ) (hdeep : IsVandiverDeep hζ u) :
    NumberField.IsCMField.unitsComplexConj K u = u := by
  obtain ⟨c, hc⟩ := hdeep
  have hbase :
      (hζ.unit' : 𝓞 K) - 1 ∣
        (1 : 𝓞 K) - hζ.unit' := by
    refine ⟨-1, ?_⟩
    ring
  have hsign :
      ((hζ.unit' : 𝓞 K) - 1) ^ (2 * p) ∣
        (u : 𝓞 K) - (c : 𝓞 K) ^ p :=
    (pow_dvd_pow_of_dvd hbase (2 * p)).trans hc
  have hconj :=
    Fermat.Irregular.VandiverTakagiPairPrime.zeta_sub_one_pow_dvd_conj_of_dvd
      hζ (2 * p) ((u : 𝓞 K) - (c : 𝓞 K) ^ p) hsign
  have hconj' :
      ((hζ.unit' : 𝓞 K) - 1) ^ (2 * p) ∣
        NumberField.IsCMField.ringOfIntegersComplexConj K
            (u : 𝓞 K) -
          (c : 𝓞 K) ^ p := by
    simpa only [map_sub, map_pow, map_intCast] using hconj
  have hdefect :
      ((hζ.unit' : 𝓞 K) - 1) ^ (2 * p) ∣
        (u : 𝓞 K) -
          NumberField.IsCMField.ringOfIntegersComplexConj K
            (u : 𝓞 K) := by
    convert dvd_sub hsign hconj' using 1
    ring
  have hdefect2 :
      ((hζ.unit' : 𝓞 K) - 1) ^ 2 ∣
        (u : 𝓞 K) -
          NumberField.IsCMField.ringOfIntegersComplexConj K
            (u : 𝓞 K) :=
    (pow_dvd_pow ((hζ.unit' : 𝓞 K) - 1) (by omega)).trans
      hdefect
  exact
    Fermat.Irregular.TakagiHistoricalPrime.unit_fixed_of_zeta_sub_one_sq_dvd_sub_conj
      (by omega) hζ u hdefect2

/-- A deeply congruent ambient unit, packaged in the real-unit subgroup. -/
def deepRealUnit
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (u : (𝓞 K)ˣ) (hdeep : IsVandiverDeep hζ u) :
    NumberField.IsCMField.realUnits K :=
  ⟨u, (NumberField.IsCMField.unitsComplexConj_eq_self_iff K u).mp
    (isVandiverDeep_unitsComplexConj_eq hp5 hζ u hdeep)⟩

@[simp]
theorem deepRealUnit_coe
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (u : (𝓞 K)ˣ) (hdeep : IsVandiverDeep hζ u) :
    ((deepRealUnit hp5 hζ u hdeep :
      NumberField.IsCMField.realUnits K) : (𝓞 K)ˣ) = u :=
  rfl

end

end Fermat.GenericIrregular.DeepReality
