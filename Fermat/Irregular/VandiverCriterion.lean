import Fermat.Cases
import FltRegular.CaseII.InductionStep
import FltRegular.CaseII.AuxLemmas

/-!
# A local-hypothesis form of the second-case criterion

The `flt-regular` proof of the second case uses regularity in exactly two
places. It principalizes certain quotients of the ideals constructed from a
hypothetical solution, and it turns one unit congruent to an integer modulo
`(p)` into a `p`-th power. This module exposes those two inputs directly and
reuses the remainder of the upstream descent.

The implication proved here is unconditional.  For an irregular prime,
establishing the two hypotheses below remains the singular-primary part of
the argument; the definitions themselves do not assert that work.

There is an important historical distinction. Vandiver's 1929 Lemma 2 uses
the deeper congruence modulo `(1 - ζ) ^ (2 * p)`, not merely congruence
modulo `(p)`. We record that source-faithful conclusion separately below.
The modern descent extracted here needs the stronger operational
`SemiprimaryUnitPowerConclusion`; no implication from Vandiver's deep lemma
to that premise is asserted.
-/

namespace Fermat.Irregular.VandiverCriterion

open scoped nonZeroDivisors NumberField
open Polynomial

variable {K : Type} {p : ℕ} [hpri : Fact p.Prime] [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]

/-- The precise ideal-class input used by the second-case descent: every
quotient `𝔞 η / 𝔞₀` arising from a hypothetical solution is
principal. -/
def RelevantIdealQuotientsPrincipal (hp : p ≠ 2) : Prop :=
  ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {x y z : 𝓞 K} {ε : (𝓞 K)ˣ} {m : ℕ}
    (e : x ^ p + y ^ p =
      ε * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.unit'.1 - 1 ∣ y)
    (η : nthRootsFinset p (1 : 𝓞 K)),
    Submodule.IsPrincipal
      (((root_div_zeta_sub_one_dvd_gcd (K := K) (p := p)
          (x := x) (y := y) (z := z) (ε := ε) (m := m) hp hζ e hy η) /
          (a_eta_zero_dvd_p_pow (K := K) (p := p)
            (x := x) (y := y) (z := z) (ε := ε) (m := m) hp hζ e hy) :
            FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)

/-- The source-faithful conclusion of Vandiver's 1929 Lemma 2: a unit
congruent to an integer `p`-th power modulo `(1 - ζ) ^ (2 * p)` is itself a
`p`-th power.

Vandiver derives this conclusion from the nondivisibility modulo `p ^ 3` of
the relevant indexed Bernoulli numbers. That arithmetic bridge is deliberately
not postulated here. -/
def KummerUnitPowerConclusion (K : Type) (p : ℕ)
    [NeZero p] [Field K] [NumberField K] : Prop :=
  ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ p) (u : (𝓞 K)ˣ),
    (∃ c : ℤ,
      ((1 : 𝓞 K) - hζ.unit') ^ (2 * p) ∣
        ((u : 𝓞 K) - (c : 𝓞 K) ^ p)) →
      ∃ v : (𝓞 K)ˣ, u = v ^ p

/-- The broader unit premise required by the modern `flt-regular` descent:
every unit congruent to an integer modulo `(p)` is a `p`-th power.

This is stronger than, and is not currently derived from, the
source-faithful `KummerUnitPowerConclusion`. In particular the available
Bernoulli cube computations alone do not discharge it. -/
def SemiprimaryUnitPowerConclusion (K : Type) (p : ℕ)
    [Field K] [NumberField K] : Prop :=
  ∀ u : (𝓞 K)ˣ,
    (∃ n : ℤ, (p : 𝓞 K) ∣ (u - n : 𝓞 K)) →
      ∃ v : (𝓞 K)ˣ, u = v ^ p

/-! ## The induction step with local principalization -/

section InductionStep

variable (hp : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
  {x y z : 𝓞 K} {ε₀ : (𝓞 K)ˣ} {m : ℕ}
  (e : x ^ p + y ^ p = ε₀ * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ p)
  (hy : ¬ hζ.unit'.1 - 1 ∣ y) (hz : ¬ hζ.unit'.1 - 1 ∣ z)
  (hprincipal : RelevantIdealQuotientsPrincipal (K := K) hp)

local notation3 "π" => Units.val (IsPrimitiveRoot.unit' hζ) - 1
local notation3 "𝔭" => Ideal.span {π}
local notation "η₀" => zeta_sub_one_dvd_root hp hζ e hy
local notation "𝔞" => root_div_zeta_sub_one_dvd_gcd hp hζ e hy
local notation "𝔞₀" => a_eta_zero_dvd_p_pow hp hζ e hy

private lemma exists_relevant_representatives
    (hz : ¬ π ∣ z)
    (hprincipal : RelevantIdealQuotientsPrincipal (K := K) hp)
    (η : nthRootsFinset p (1 : 𝓞 K)) (hη : η ≠ η₀) :
    ∃ a b : 𝓞 K, ¬ π ∣ a ∧ ¬ π ∣ b ∧
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a / b : K) = 𝔞 η / 𝔞₀ := by
  exact exists_not_dvd_spanSingleton_eq hζ.zeta_sub_one_prime'
    _ _ ((p_dvd_a_iff hp hζ e hy η).not.mpr hη)
      (not_p_div_a_zero hp hζ e hy hz)
      (hprincipal hζ e hy η)

private noncomputable def representativeNum
    (hz : ¬ π ∣ z)
    (hprincipal : RelevantIdealQuotientsPrincipal (K := K) hp)
    (η : nthRootsFinset p (1 : 𝓞 K)) (hη : η ≠ η₀) : 𝓞 K :=
  (exists_relevant_representatives hp hζ e hy hz hprincipal η hη).choose

private noncomputable def representativeDenom
    (hz : ¬ π ∣ z)
    (hprincipal : RelevantIdealQuotientsPrincipal (K := K) hp)
    (η : nthRootsFinset p (1 : 𝓞 K)) (hη : η ≠ η₀) : 𝓞 K :=
  (exists_relevant_representatives hp hζ e hy hz hprincipal η hη).choose_spec.choose

local notation "α" => fun η ↦ representativeNum hp hζ e hy hz hprincipal η
local notation "β" => fun η ↦ representativeDenom hp hζ e hy hz hprincipal η

private lemma representativeNum_spec
    (η : nthRootsFinset p (1 : 𝓞 K)) (hη : η ≠ η₀) : ¬ π ∣ α η hη :=
  (exists_relevant_representatives hp hζ e hy hz hprincipal η hη).choose_spec.choose_spec.1

private lemma representativeDenom_spec
    (η : nthRootsFinset p (1 : 𝓞 K)) (hη : η ≠ η₀) : ¬ π ∣ β η hη :=
  (exists_relevant_representatives hp hζ e hy hz hprincipal η hη).choose_spec.choose_spec.2.1

private lemma representative_eq
    (η : nthRootsFinset p (1 : 𝓞 K)) (hη : η ≠ η₀) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (α η hη / β η hη : K) = 𝔞 η / 𝔞₀ :=
  (exists_relevant_representatives hp hζ e hy hz hprincipal η hη).choose_spec.choose_spec.2.2

private lemma ideal_mul_denom_eq
    (η : nthRootsFinset p (1 : 𝓞 K)) (hη : η ≠ η₀) :
    𝔞 η * Ideal.span {β η hη} = 𝔞₀ * Ideal.span {α η hη} := by
  apply FractionalIdeal.coeIdeal_injective (K := K)
  simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton]
  rw [mul_comm (𝔞₀ : FractionalIdeal (𝓞 K)⁰ K), ← div_eq_div_iff,
    ← representative_eq hp hζ e hy hz hprincipal η hη,
    FractionalIdeal.spanSingleton_div_spanSingleton]
  · intro ha
    rw [FractionalIdeal.coeIdeal_eq_zero] at ha
    apply not_p_div_a_zero hp hζ e hy hz
    rw [ha]
    exact dvd_zero _
  · rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff,
      ← (algebraMap (𝓞 K) K).map_zero,
      (IsFractionRing.injective (𝓞 K) K).eq_iff]
    intro hβ
    apply representativeDenom_spec hp hζ e hy hz hprincipal η hη
    change π ∣ representativeDenom hp hζ e hy hz hprincipal η hη
    rw [hβ]
    exact dvd_zero _

private lemma associated_eta_zero
    (η : nthRootsFinset p (1 : 𝓞 K)) (hη : η ≠ η₀) :
    Associated ((x + y * η₀) * α η hη ^ p)
      ((x + y * η) * π ^ (m * p) * β η hη ^ p) := by
  simp_rw [← Ideal.span_singleton_eq_span_singleton,
    ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow,
    ← m_mul_c_mul_p hp hζ e hy, ← root_div_zeta_sub_one_dvd_gcd_spec,
    ← a_eta_zero_dvd_p_pow_spec]
  rw [mul_comm _ 𝔞₀, mul_pow]
  simp only [mul_assoc, mul_left_comm _ 𝔭]
  rw [mul_left_comm (𝔞 η ^ p), mul_left_comm (𝔞₀ ^ p), ← pow_mul,
    ← mul_pow, ← mul_pow, ideal_mul_denom_eq hp hζ e hy hz hprincipal η hη]

private noncomputable def associatedUnit
    (η : nthRootsFinset p (1 : 𝓞 K)) (hη : η ≠ η₀) : (𝓞 K)ˣ :=
  (associated_eta_zero hp hζ e hy hz hprincipal η hη).choose

local notation "ε" => fun η ↦ associatedUnit hp hζ e hy hz hprincipal η

private lemma associatedUnit_spec
    (η : nthRootsFinset p (1 : 𝓞 K)) (hη : η ≠ η₀) :
    ε η hη * (x + y * η₀) * α η hη ^ p =
      (x + y * η) * π ^ (m * p) * β η hη ^ p := by
  rw [mul_assoc, mul_comm (ε η hη : 𝓞 K)]
  exact (associated_eta_zero hp hζ e hy hz hprincipal η hη).choose_spec

private lemma formula
    (η₁ : nthRootsFinset p (1 : 𝓞 K)) (hη₁ : η₁ ≠ η₀)
    (η₂ : nthRootsFinset p (1 : 𝓞 K)) (hη₂ : η₂ ≠ η₀) :
    (η₂ - η₀ : 𝓞 K) * ε η₁ hη₁ * (α η₁ hη₁ * β η₂ hη₂) ^ p +
      (η₀ - η₁) * ε η₂ hη₂ * (α η₂ hη₂ * β η₁ hη₁) ^ p =
      (η₂ - η₁) * (π ^ m * (β η₁ hη₁ * β η₂ hη₂)) ^ p := by
  rw [← mul_right_inj' (x_plus_y_mul_ne_zero hp hζ e hz η₀), mul_add]
  simp_rw [mul_left_comm (x + y * η₀), mul_pow, mul_assoc,
    mul_left_comm (η₂ - η₀ : 𝓞 K), mul_left_comm (η₀ - η₁ : 𝓞 K),
    ← mul_assoc, associatedUnit_spec, mul_assoc,
    ← mul_left_comm (η₂ - η₀ : 𝓞 K),
    ← mul_left_comm (η₀ - η₁ : 𝓞 K), pow_mul, ← mul_pow,
    mul_comm (β η₂ hη₂), ← mul_assoc]
  rw [← add_mul]
  congr 1
  ring

include hp e hy hz hprincipal in
private lemma exists_weighted_solution :
    ∃ (x' y' z' : 𝓞 K) (ε₁ ε₂ ε₃ : (𝓞 K)ˣ),
      ¬ π ∣ x' ∧ ¬ π ∣ y' ∧ ¬ π ∣ z' ∧
        ε₁ * x' ^ p + ε₂ * y' ^ p = ε₃ * (π ^ m * z') ^ p := by
  have h₁ := mul_mem_nthRootsFinset (η₀ : _).prop
    (hζ.unit'_coe.mem_nthRootsFinset hpri.out.pos)
  rw [one_mul] at h₁
  let η₁ : nthRootsFinset p (1 : 𝓞 K) := ⟨η₀ * hζ.unit', h₁⟩
  have h₂ := mul_mem_nthRootsFinset (η₁ : _).prop
    (hζ.unit'_coe.mem_nthRootsFinset hpri.out.pos)
  rw [one_mul] at h₂
  let η₂ : nthRootsFinset p (1 : 𝓞 K) := ⟨η₀ * hζ.unit' * hζ.unit', h₂⟩
  have hη₁ : η₁ ≠ η₀ := by
    rw [← Subtype.coe_injective.ne_iff]
    change (η₀ * hζ.unit' : 𝓞 K) ≠ η₀
    rw [Ne, mul_right_eq_self₀, not_or]
    exact ⟨hζ.unit'_coe.ne_one hpri.out.one_lt,
      ne_zero_of_mem_nthRootsFinset one_ne_zero (η₀ : _).prop⟩
  have hη₂ : η₂ ≠ η₀ := by
    rw [← Subtype.coe_injective.ne_iff]
    change (η₀ * hζ.unit' * hζ.unit' : 𝓞 K) ≠ η₀
    rw [Ne, mul_assoc, ← pow_two, mul_right_eq_self₀, not_or]
    exact ⟨hζ.unit'_coe.pow_ne_one_of_pos_of_lt (by omega)
      (hpri.out.two_le.lt_or_eq.resolve_right hp.symm),
      ne_zero_of_mem_nthRootsFinset one_ne_zero (η₀ : _).prop⟩
  have hη : η₂ ≠ η₁ := by
    rw [← Subtype.coe_injective.ne_iff]
    change (η₀ * hζ.unit' * hζ.unit' : 𝓞 K) ≠ η₀ * hζ.unit'
    rw [Ne, mul_right_eq_self₀, not_or]
    exact ⟨hζ.unit'_coe.ne_one hpri.out.one_lt,
      mul_ne_zero (ne_zero_of_mem_nthRootsFinset one_ne_zero (η₀ : _).prop)
        (hζ.unit'_coe.ne_zero hpri.out.ne_zero)⟩
  obtain ⟨u₁, hu₁⟩ :=
    hζ.unit'_coe.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime hpri.out
      η₂.prop (η₀ : _).prop (Subtype.coe_injective.ne_iff.mpr hη₂)
  obtain ⟨u₂, hu₂⟩ :=
    hζ.unit'_coe.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime hpri.out
      (η₀ : _).prop η₁.prop (Subtype.coe_injective.ne_iff.mpr hη₁.symm)
  obtain ⟨u₃, hu₃⟩ :=
    hζ.unit'_coe.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime hpri.out
      η₂.prop (η₁ : _).prop (Subtype.coe_injective.ne_iff.mpr hη)
  have hformula := formula hp hζ e hy hz hprincipal η₁ hη₁ η₂ hη₂
  rw [← hu₁, ← hu₂, ← hu₃, mul_assoc _ (u₁ : 𝓞 K),
    mul_assoc _ (u₂ : 𝓞 K), mul_assoc _ (u₃ : 𝓞 K),
    mul_assoc π, mul_assoc π, ← mul_add,
    mul_right_inj' (hζ.unit'_coe.sub_one_ne_zero hpri.out.one_lt),
    ← Units.val_mul, ← Units.val_mul] at hformula
  refine ⟨_, _, _, _, _, _, ?_, ?_, ?_, hformula⟩
  · exact hζ.zeta_sub_one_prime'.not_dvd_mul
      (representativeNum_spec hp hζ e hy hz hprincipal η₁ hη₁)
      (representativeDenom_spec hp hζ e hy hz hprincipal η₂ hη₂)
  · exact hζ.zeta_sub_one_prime'.not_dvd_mul
      (representativeNum_spec hp hζ e hy hz hprincipal η₂ hη₂)
      (representativeDenom_spec hp hζ e hy hz hprincipal η₁ hη₁)
  · exact hζ.zeta_sub_one_prime'.not_dvd_mul
      (representativeDenom_spec hp hζ e hy hz hprincipal η₁ hη₁)
      (representativeDenom_spec hp hζ e hy hz hprincipal η₂ hη₂)

include hp e hy hz hprincipal in
private lemma exists_solution_step
    (hkummer : SemiprimaryUnitPowerConclusion K p) :
    ∃ (x' y' z' : 𝓞 K) (ε₃ : (𝓞 K)ˣ),
      ¬ π ∣ y' ∧ ¬ π ∣ z' ∧
        x' ^ p + y' ^ p = ε₃ * (π ^ m * z') ^ p := by
  obtain ⟨x', y', z', ε₁, ε₂, ε₃, hx', hy', hz', e'⟩ :=
    exists_weighted_solution hp hζ e hy hz hprincipal
  obtain ⟨ε', hε'⟩ : ∃ ε', ε₁ / ε₂ = ε' ^ p := by
    apply hkummer
    have hmp : p - 1 ≤ m * p := (Nat.sub_le _ _).trans
      ((le_of_eq (one_mul _).symm).trans
        (Nat.mul_le_mul_right p (one_le_m hp hζ e hy hz)))
    obtain ⟨u, hu⟩ := (associated_zeta_sub_one_pow_prime hζ).symm
    rw [mul_pow, ← pow_mul, mul_comm (ε₃ : 𝓞 K), mul_assoc,
      ← Nat.sub_add_cancel hmp, add_comm _ (p - 1), pow_add, mul_assoc] at e'
    apply_fun Ideal.Quotient.mk (Ideal.span <| singleton (p : 𝓞 K)) at e'
    rw [map_mul, (Ideal.Quotient.eq_zero_iff_dvd _ _).mpr
      (associated_zeta_sub_one_pow_prime hζ).symm.dvd, zero_mul,
      Ideal.Quotient.eq_zero_iff_dvd] at e'
    obtain ⟨a, ha⟩ := exists_solution'_aux hp hζ hx' e'
    obtain ⟨b, hb⟩ := exists_dvd_pow_sub_Int_pow hp a
    have hab := dvd_add ha hb
    rw [sub_add_sub_cancel, ← Int.cast_pow] at hab
    exact ⟨b ^ p, hab⟩
  refine ⟨ε' * x', y', z', ε₃ / ε₂, hy', hz', ?_⟩
  rwa [mul_pow, ← Units.val_pow_eq_pow_val, ← hε',
    ← mul_right_inj' ε₂.isUnit.ne_zero, mul_add, ← mul_assoc,
    ← Units.val_mul, mul_div_cancel, ← mul_assoc,
    ← Units.val_mul, mul_div_cancel]

end InductionStep

/-! ## Descent and the integer second case -/

private lemma not_exists_solution
    (hodd : p ≠ 2)
    (hprincipal : RelevantIdealQuotientsPrincipal (K := K) hodd)
    (hkummer : SemiprimaryUnitPowerConclusion K p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) {m : ℕ} (hm : 1 ≤ m) :
    ¬ ∃ (x' y' z' : 𝓞 K) (ε₃ : (𝓞 K)ˣ),
      ¬ (hζ.unit' : 𝓞 K) - 1 ∣ y' ∧
      ¬ (hζ.unit' : 𝓞 K) - 1 ∣ z' ∧
      x' ^ p + y' ^ p = ε₃ * (((hζ.unit' : 𝓞 K) - 1) ^ m * z') ^ p := by
  induction m, hm using Nat.le_induction with
  | base =>
      rintro ⟨x, y, z, ε₃, hy, hz, e⟩
      exact zero_lt_one.not_ge (one_le_m hodd hζ e hy hz)
  | succ m' _ IH =>
      rintro ⟨x, y, z, ε₃, hy, hz, e⟩
      exact IH (exists_solution_step hodd hζ e hy hz hprincipal hkummer)

private lemma not_exists_cyclotomic_solution
    (hodd : p ≠ 2)
    (hprincipal : RelevantIdealQuotientsPrincipal (K := K) hodd)
    (hkummer : SemiprimaryUnitPowerConclusion K p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    ¬ ∃ (x y z : 𝓞 K),
      ¬ (hζ.unit' : 𝓞 K) - 1 ∣ y ∧
      (hζ.unit' : 𝓞 K) - 1 ∣ z ∧ z ≠ 0 ∧
      x ^ p + y ^ p = z ^ p := by
  letI : WfDvdMonoid (𝓞 K) := IsNoetherianRing.wfDvdMonoid
  rintro ⟨x, y, z, hy, hz, hz', e⟩
  obtain ⟨m, z, hm, hz'', rfl⟩ :
      ∃ m z', 1 ≤ m ∧ ¬ ((hζ.unit' : 𝓞 K) - 1 ∣ z') ∧
        z = ((hζ.unit' : 𝓞 K) - 1) ^ m * z' := by
    classical
    have H : FiniteMultiplicity ((hζ.unit' : 𝓞 K) - 1) z :=
      FiniteMultiplicity.of_not_isUnit hζ.zeta_sub_one_prime'.not_unit hz'
    obtain ⟨z', hzfactor⟩ := pow_multiplicity_dvd ((hζ.unit' : 𝓞 K) - 1) z
    refine ⟨_, _, ?_, ?_, hzfactor⟩
    · rwa [← Nat.cast_le (α := ENat),
        ← FiniteMultiplicity.emultiplicity_eq_multiplicity H,
        ← pow_dvd_iff_le_emultiplicity, pow_one]
    · intro h'
      have hnext := mul_dvd_mul_left
        (((hζ.unit' : 𝓞 K) - 1) ^
          multiplicity ((hζ.unit' : 𝓞 K) - 1) z) h'
      rw [← pow_succ, ← hzfactor] at hnext
      refine not_pow_dvd_of_emultiplicity_lt ?_ hnext
      rw [FiniteMultiplicity.emultiplicity_eq_multiplicity H, Nat.cast_lt]
      exact Nat.lt_succ_self _
  refine not_exists_solution hodd hprincipal hkummer hζ hm
    ⟨x, y, z, 1, hy, hz'', ?_⟩
  rwa [Units.val_one, one_mul]

private lemma not_exists_int_solution
    (hodd : p ≠ 2)
    (hprincipal : RelevantIdealQuotientsPrincipal (K := K) hodd)
    (hkummer : SemiprimaryUnitPowerConclusion K p) :
    ¬ ∃ (x y z : ℤ),
      ¬ (p : ℤ) ∣ y ∧ (p : ℤ) ∣ z ∧ z ≠ 0 ∧
      x ^ p + y ^ p = z ^ p := by
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot
    ℚ (B := K) (Set.mem_singleton p) hpri.out.ne_zero
  have hdiv := fun n ↦ zeta_sub_one_dvd_Int_iff (K := K) hζ (n := n)
  simp_rw [← hdiv]
  rintro ⟨x, y, z, hy, hz, hz', e⟩
  refine not_exists_cyclotomic_solution hodd hprincipal hkummer hζ
    ⟨x, y, z, hy, hz, ?_, ?_⟩
  · rwa [ne_eq, Int.cast_eq_zero]
  · dsimp
    simp_rw [← Int.cast_pow, ← Int.cast_add, e]

private lemma not_exists_primitive_int_solution
    (hodd : p ≠ 2)
    (hprincipal : RelevantIdealQuotientsPrincipal (K := K) hodd)
    (hkummer : SemiprimaryUnitPowerConclusion K p) :
    ¬ ∃ (x y z : ℤ),
      ({x, y, z} : Finset ℤ).gcd id = 1 ∧ (p : ℤ) ∣ z ∧ z ≠ 0 ∧
      x ^ p + y ^ p = z ^ p := by
  rintro ⟨x, y, z, hgcd, hz, hz', e⟩
  refine not_exists_int_solution hodd hprincipal hkummer
    ⟨x, y, z, ?_, hz, hz', e⟩
  intro hy
  have hpow := dvd_sub (dvd_pow hz hpri.out.ne_zero) (dvd_pow hy hpri.out.ne_zero)
  rw [← e, add_sub_cancel_right] at hpow
  replace hpow := (Nat.prime_iff_prime_int.mp hpri.out).dvd_of_dvd_pow hpow
  apply (Nat.prime_iff_prime_int.mp hpri.out).not_unit
  rw [isUnit_iff_dvd_one, ← hgcd]
  simp [dvd_gcd_iff, hz, hy, hpow]

private lemma int_gcd_left_comm (a b c : ℤ) :
    Int.gcd a (Int.gcd b c) = Int.gcd b (Int.gcd a c) := by
  rw [← Int.gcd_assoc, ← Int.gcd_assoc, Int.gcd_comm a b]

/-- Exclude the second case from precisely the two local inputs used by the
cyclotomic descent.

For an irregular prime these hypotheses are not bookkeeping assumptions:
proving them is exactly the remaining singular-primary work. In particular,
the semiprimary-unit premise here is stronger than Vandiver's 1929 Lemma 2
and is not supplied by the current Bernoulli cube data. The theorem only
packages the unconditional implication from those obligations to the integer
second-case statement. -/
theorem secondCaseExcluded_of_local_hypotheses
    (hodd : p ≠ 2)
    (hprincipal : RelevantIdealQuotientsPrincipal (K := K) hodd)
    (hkummer : SemiprimaryUnitPowerConclusion K p) :
    Fermat.SecondCaseExcluded p := by
  intro a b c ha hb hc hgcd hcase e
  have hpodd := hpri.out.odd_of_ne_two hodd
  obtain hab | hpc := (Nat.prime_iff_prime_int.mp hpri.out).dvd_or_dvd hcase
  · obtain hpa | hpb := (Nat.prime_iff_prime_int.mp hpri.out).dvd_or_dvd hab
    · refine not_exists_primitive_int_solution hodd hprincipal hkummer
        ⟨b, -c, -a, ?_, ?_, ?_, ?_⟩
      · simp only [← hgcd, Finset.gcd_insert, id_eq, ← Int.coe_gcd,
          Int.neg_gcd, ← LawfulSingleton.insert_empty_eq, Finset.gcd_empty,
          int_gcd_left_comm _ a]
      · rwa [dvd_neg]
      · rwa [ne_eq, neg_eq_zero]
      · simp [hpodd.neg_pow, ← e]
    · refine not_exists_primitive_int_solution hodd hprincipal hkummer
        ⟨-c, a, -b, ?_, ?_, ?_, ?_⟩
      · simp only [← hgcd, Finset.gcd_insert, id_eq, ← Int.coe_gcd,
          Int.neg_gcd, ← LawfulSingleton.insert_empty_eq, Finset.gcd_empty,
          int_gcd_left_comm _ c]
      · rwa [dvd_neg]
      · rwa [ne_eq, neg_eq_zero]
      · simp [hpodd.neg_pow, ← e]
  · exact not_exists_primitive_int_solution hodd hprincipal hkummer
      ⟨a, b, c, hgcd, hpc, hc, e⟩

end Fermat.Irregular.VandiverCriterion
