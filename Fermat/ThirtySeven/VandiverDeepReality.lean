import Fermat.Irregular.CircularUnitIndex
import Fermat.ThirtySeven.VandiverRelationNormalization

/-!
# Deep Vandiver units are real at exponent 37

The group-theoretic core of Vandiver's Lemma II must be applied in the
real-unit subgroup, where the odd power map is injective.  This file proves
that the depth-74 local hypothesis itself forces an ambient cyclotomic unit
to be real.

Complex conjugation preserves divisibility by powers of `zeta - 1`.
Therefore a deeply congruent unit differs from its conjugate by a multiple
of `(zeta - 1)^2`.  The CM unit theorem writes the conjugation defect as
the square of a power of `zeta`; a nontrivial such power contains exactly
one uniformizer, not its square.  Hence the defect is one and the unit is
fixed by conjugation.

This module is independent of the historical descent development.
-/

open scoped NumberField

namespace Fermat.ThirtySeven.VandiverDeepReality

noncomputable section

open Fermat.Irregular.VandiverUnitLemma

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {37} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 37) K (by norm_num)

/-- Complex conjugation sends the integral unit attached to `zeta` to its
inverse. -/
theorem unitsComplexConj_zeta37 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) :
    NumberField.IsCMField.unitsComplexConj K hzeta.unit' =
      (hzeta.unit')⁻¹ := by
  apply Units.ext
  apply NumberField.RingOfIntegers.ext
  change NumberField.IsCMField.complexConj K zeta = zeta⁻¹
  exact Fermat.Irregular.CircularUnitIndex.complexConj_zeta37_inv hzeta

/-- Conjugation changes `zeta - 1` by the explicit unit `-zeta⁻¹`. -/
theorem ringOfIntegersComplexConj_zeta_sub_one37 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) :
    NumberField.IsCMField.ringOfIntegersComplexConj K
        ((hzeta.unit' : 𝓞 K) - 1) =
      ((-hzeta.unit'⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
        ((hzeta.unit' : 𝓞 K) - 1) := by
  rw [map_sub, map_one]
  have hconjzeta :
      NumberField.IsCMField.ringOfIntegersComplexConj K
          (hzeta.unit' : 𝓞 K) = (hzeta.unit'⁻¹ : (𝓞 K)ˣ) :=
    congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K)
      (unitsComplexConj_zeta37 hzeta)
  rw [hconjzeta]
  have hinv :
      (hzeta.unit'⁻¹ : (𝓞 K)ˣ) * (hzeta.unit' : 𝓞 K) = 1 := by
    rw [← Units.val_mul]
    simp
  simp only [Units.val_neg, neg_mul, mul_sub, hinv]
  ring

/-- Divisibility by a power of `zeta - 1` is preserved by complex
conjugation. -/
theorem zeta_sub_one_pow_dvd_conj_of_dvd37 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) (n : ℕ) (a : 𝓞 K)
    (h : ((hzeta.unit' : 𝓞 K) - 1) ^ n ∣ a) :
    ((hzeta.unit' : 𝓞 K) - 1) ^ n ∣
      NumberField.IsCMField.ringOfIntegersComplexConj K a := by
  obtain ⟨b, rfl⟩ := h
  rw [map_mul, map_pow,
    ringOfIntegersComplexConj_zeta_sub_one37, mul_pow]
  refine ⟨(((-hzeta.unit'⁻¹ : (𝓞 K)ˣ) ^ n : (𝓞 K)ˣ) : 𝓞 K) *
      NumberField.IsCMField.ringOfIntegersComplexConj K b, ?_⟩
  simp only [Units.val_pow_eq_pow_val]
  ring

/-- A square of a 37th root of unity which is `1` modulo
`(zeta - 1)^2` is literally `1`. -/
theorem zeta_pow_sq_eq_one_of_zeta_sub_one_sq_dvd37 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) (j : ℕ)
    (hdiv : ((hzeta.unit' : 𝓞 K) - 1) ^ 2 ∣
      ((((hzeta.unit' ^ j) ^ 2 : (𝓞 K)ˣ) : 𝓞 K) - 1)) :
    (hzeta.unit' ^ j) ^ 2 = 1 := by
  let k : ℕ := (2 * j) % 37
  have hklt : k < 37 := by
    dsimp [k]
    omega
  have hpowmod :
      ((((hzeta.unit' ^ j) ^ 2 : (𝓞 K)ˣ) : 𝓞 K)) =
        (hzeta.unit' : 𝓞 K) ^ k := by
    simp only [Units.val_pow_eq_pow_val]
    rw [← pow_mul]
    have hmod := pow_mod_orderOf (hzeta.unit' : 𝓞 K) (2 * j)
    rw [← hzeta.unit'_coe.eq_orderOf] at hmod
    simpa only [k, mul_comm] using hmod.symm
  by_cases hk : k = 0
  · apply Units.ext
    change ((((hzeta.unit' ^ j) ^ 2 : (𝓞 K)ˣ) : 𝓞 K)) = 1
    rw [hpowmod, hk, pow_zero]
  · have hknotdvd : ¬37 ∣ k := by
      intro h
      obtain ⟨t, ht⟩ := h
      apply hk
      omega
    have hkcoprime : k.Coprime 37 := by
      apply Nat.coprime_comm.mpr
      exact (show Nat.Prime 37 by norm_num).coprime_iff_not_dvd.mpr
        hknotdvd
    have hassoc : Associated
        ((hzeta.unit' : 𝓞 K) - 1)
        ((hzeta.unit' : 𝓞 K) ^ k - 1) :=
      hzeta.unit'_coe.associated_sub_one_pow_sub_one_of_coprime
        hkcoprime
    have hsquare : ((hzeta.unit' : 𝓞 K) - 1) ^ 2 ∣
        (hzeta.unit' : 𝓞 K) - 1 :=
      hassoc.dvd_iff_dvd_right.mpr
        (by simpa only [hpowmod] using hdiv)
    obtain ⟨c, hc⟩ := hsquare
    have hpi0 : (hzeta.unit' : 𝓞 K) - 1 ≠ 0 :=
      hzeta.unit'_coe.sub_one_ne_zero (by norm_num)
    have hone : (1 : 𝓞 K) =
        ((hzeta.unit' : 𝓞 K) - 1) * c := by
      apply mul_left_cancel₀ hpi0
      calc
        ((hzeta.unit' : 𝓞 K) - 1) * 1 =
            (hzeta.unit' : 𝓞 K) - 1 := by ring
        _ = ((hzeta.unit' : 𝓞 K) - 1) ^ 2 * c := hc
        _ = ((hzeta.unit' : 𝓞 K) - 1) *
            (((hzeta.unit' : 𝓞 K) - 1) * c) := by ring
    exact False.elim <| hzeta.zeta_sub_one_prime'.not_unit
      (isUnit_iff_dvd_one.mpr ⟨c, hone⟩)

/-- A unit whose conjugation defect contains the uniformizer square is
fixed by complex conjugation. -/
theorem unit_fixed_of_zeta_sub_one_sq_dvd_sub_conj37 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) (u : (𝓞 K)ˣ)
    (hdiv : ((hzeta.unit' : 𝓞 K) - 1) ^ 2 ∣
      (u : 𝓞 K) -
        NumberField.IsCMField.ringOfIntegersComplexConj K (u : 𝓞 K)) :
    NumberField.IsCMField.unitsComplexConj K u = u := by
  obtain ⟨j, hj⟩ :=
    unit_inv_conj_is_root_of_unity hzeta u (by norm_num)
  let cu : (𝓞 K)ˣ := NumberField.IsCMField.unitsComplexConj K u
  let r : (𝓞 K)ˣ := (hzeta.unit' ^ j) ^ 2
  have hu : u = r * cu := by
    calc
      u = (u * cu⁻¹) * cu := by simp
      _ = r * cu := by
        simpa only [cu, r] using congrArg (· * cu) hj
  have hu' := congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) hu
  have hfactor :
      (u : 𝓞 K) - (cu : 𝓞 K) =
        (((((hzeta.unit' ^ j) ^ 2 : (𝓞 K)ˣ) : 𝓞 K) - 1) *
          (cu : 𝓞 K)) := by
    change (u : 𝓞 K) - (cu : 𝓞 K) =
      ((r : 𝓞 K) - 1) * (cu : 𝓞 K)
    rw [hu']
    simp only [Units.val_mul]
    ring
  have hassoc : Associated
      (((((hzeta.unit' ^ j) ^ 2 : (𝓞 K)ˣ) : 𝓞 K)) - 1)
      ((u : 𝓞 K) - (cu : 𝓞 K)) :=
    ⟨cu, by simpa only [hfactor]⟩
  have hrootdiv : ((hzeta.unit' : 𝓞 K) - 1) ^ 2 ∣
      (((((hzeta.unit' ^ j) ^ 2 : (𝓞 K)ˣ) : 𝓞 K)) - 1) :=
    hassoc.dvd_iff_dvd_right.mpr (by simpa only [cu] using hdiv)
  have hroot :=
    zeta_pow_sq_eq_one_of_zeta_sub_one_sq_dvd37 hzeta j hrootdiv
  rw [hroot] at hj
  have hucu : u = cu := by
    calc
      u = (u * cu⁻¹) * cu := by simp
      _ = 1 * cu := by rw [hj]
      _ = cu := by simp
  exact hucu.symm

/-- The depth-74 hypothesis forces a unit to be real. -/
theorem isVandiverDeep_unitsComplexConj_eq {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) (u : (𝓞 K)ˣ)
    (hdeep : IsVandiverDeep (K := K) (p := 37) hzeta u) :
    NumberField.IsCMField.unitsComplexConj K u = u := by
  obtain ⟨c, hc⟩ := hdeep
  have hsign : ((hzeta.unit' : 𝓞 K) - 1) ^ 74 ∣
      (u : 𝓞 K) - (c : 𝓞 K) ^ 37 := by
    have hbase : (hzeta.unit' : 𝓞 K) - 1 ∣
        (1 : 𝓞 K) - hzeta.unit' := by
      refine ⟨-1, ?_⟩
      ring
    exact (pow_dvd_pow_of_dvd hbase 74).trans hc
  have hconj := zeta_sub_one_pow_dvd_conj_of_dvd37
    hzeta 74 ((u : 𝓞 K) - (c : 𝓞 K) ^ 37) hsign
  have hconj' : ((hzeta.unit' : 𝓞 K) - 1) ^ 74 ∣
      NumberField.IsCMField.ringOfIntegersComplexConj K (u : 𝓞 K) -
        (c : 𝓞 K) ^ 37 := by
    simpa only [map_sub, map_pow, map_intCast] using hconj
  have hdefect74 : ((hzeta.unit' : 𝓞 K) - 1) ^ 74 ∣
      (u : 𝓞 K) -
        NumberField.IsCMField.ringOfIntegersComplexConj K (u : 𝓞 K) := by
    convert dvd_sub hsign hconj' using 1
    ring
  have hdefect2 : ((hzeta.unit' : 𝓞 K) - 1) ^ 2 ∣
      (u : 𝓞 K) -
        NumberField.IsCMField.ringOfIntegersComplexConj K (u : 𝓞 K) :=
    (pow_dvd_pow ((hzeta.unit' : 𝓞 K) - 1) (by omega)).trans
      hdefect74
  exact unit_fixed_of_zeta_sub_one_sq_dvd_sub_conj37
    hzeta u hdefect2

/-- A deeply congruent ambient unit, packaged in the real-unit subgroup. -/
def deepRealUnit37 {zeta : K} (hzeta : IsPrimitiveRoot zeta 37)
    (u : (𝓞 K)ˣ)
    (hdeep : IsVandiverDeep (K := K) (p := 37) hzeta u) :
    NumberField.IsCMField.realUnits K :=
  ⟨u, (NumberField.IsCMField.unitsComplexConj_eq_self_iff K u).mp
    (isVandiverDeep_unitsComplexConj_eq hzeta u hdeep)⟩

@[simp]
theorem deepRealUnit37_coe {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) (u : (𝓞 K)ˣ)
    (hdeep : IsVandiverDeep (K := K) (p := 37) hzeta u) :
    ((deepRealUnit37 hzeta u hdeep :
      NumberField.IsCMField.realUnits K) : (𝓞 K)ˣ) = u := rfl

end

end Fermat.ThirtySeven.VandiverDeepReality
