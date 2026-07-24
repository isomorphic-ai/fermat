import Fermat.Irregular.VandiverEquationEightAGeneratorPrime
import Fermat.Irregular.VandiverRealNormalizationPrime

/-!
# Prime-generic real generator after Vandiver's equation (9)

Let `J ^ p = (q)`, where `q` is fixed by complex conjugation and `J` is
prime to the unique ramified ideal `(ζ - 1)`.  Nondivisibility of the plus
class number first makes `J` principal and conjugation-stable.  A generator
of `J` then has conjugation quotient `ζ ^ j`: the possible minus sign in
the CM-unit theorem is ruled out by reduction modulo `(ζ - 1)`.  Finally,
the inverse-of-two normalization makes the generator literally real.

This is the prime-generic content of the exponent-specific
`exists_realEquationNineGenerator587` and
`exists_realEquationNineGenerator691` theorems.
-/

namespace Fermat.Irregular.VandiverRealEquationNineGeneratorPrime

open scoped NumberField

open NumberField NumberField.IsCMField
open Fermat.Irregular.VandiverHistoricalPrime
open Fermat.Irregular.VandiverEquationEightAGeneratorPrime
open Fermat.Irregular.VandiverRealNormalizationPrime

noncomputable section

variable {K : Type} {p r : ℕ} [Fact p.Prime]
  [Field K] [NumberField K] [NumberField.IsCMField K]
  [IsCyclotomicExtension {p} ℚ K]

/-- Complex conjugation acts trivially modulo `(ζ - 1)` on every
cyclotomic integer. -/
lemma ringOfIntegersComplexConj_eq_mod_zeta_sub_one
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (a : 𝓞 K) :
    Ideal.Quotient.mk
        (Ideal.span ({(hζ.unit' : 𝓞 K) - 1} : Set (𝓞 K)))
        (ringOfIntegersComplexConj K a) =
      Ideal.Quotient.mk
        (Ideal.span ({(hζ.unit' : 𝓞 K) - 1} : Set (𝓞 K))) a := by
  have hp0 : 0 < p := (Fact.out : Nat.Prime p).pos
  have ha := hζ.integralPowerBasis.basis.sum_repr a
  let c := hζ.integralPowerBasis.basis.repr
  let phi := hζ.integralPowerBasis.dim
  simp_rw [PowerBasis.basis_eq_pow,
    IsPrimitiveRoot.integralPowerBasis_gen] at ha
  have ha' := congrArg (ringOfIntegersComplexConj K) ha
  replace ha' :
      ∑ x : Fin phi, (c a) x • ringOfIntegersComplexConj K
          (⟨ζ, hζ.isIntegral hp0⟩ ^ (x : ℕ)) =
        ringOfIntegersComplexConj K a := by
    refine Eq.trans ?_ ha'
    rw [map_sum]
    congr 1
    ext x
    congr 1
    rw [map_zsmul]
  have hpow : ∀ x : Fin phi,
      ringOfIntegersComplexConj K
          (⟨ζ, hζ.isIntegral hp0⟩ ^ (x : ℕ)) =
        ⟨ζ⁻¹, hζ.inv.isIntegral hp0⟩ ^ (x : ℕ) := by
    intro x
    ext
    change complexConj K (ζ ^ (x : ℕ)) = (ζ⁻¹) ^ (x : ℕ)
    rw [map_pow,
      Fermat.Irregular.CyclotomicDiscriminantPrime.complexConj_zeta_inv hζ]
  conv_lhs at ha' =>
    congr
    congr
    ext x
    rw [hpow x]
  have hconj := aux hζ hζ.inv ha'
  have horig := aux hζ hζ ha
  exact hconj.trans horig.symm

/-- A generator prime to `(ζ - 1)` of a conjugation-stable principal ideal
has conjugation quotient exactly `ζ ^ j`.  Reduction modulo `(ζ - 1)`
removes the possible minus sign in the CM-unit theorem. -/
lemma conjugation_eq_zeta_pow_of_stable_principal
    (hp2 : 2 < p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (a : 𝓞 K)
    (ha : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ a)
    (hstable : conjugateIdeal (Ideal.span {a}) = Ideal.span {a}) :
    ∃ j : ℕ, ringOfIntegersComplexConj K a =
      (hζ.unit' ^ j : (𝓞 K)ˣ) * a := by
  have hassoc : Associated (ringOfIntegersComplexConj K a) a := by
    rw [← Ideal.span_singleton_eq_span_singleton]
    rw [← conjugateIdeal_span]
    exact hstable
  obtain ⟨u, hu⟩ := hassoc
  let v : (𝓞 K)ˣ := u⁻¹
  have ha0 : a ≠ 0 := by
    intro h
    apply ha
    rw [h]
    exact dvd_zero _
  have hv : ringOfIntegersComplexConj K a = (v : 𝓞 K) * a := by
    change ringOfIntegersComplexConj K a = (u⁻¹ : (𝓞 K)ˣ) * a
    calc
      ringOfIntegersComplexConj K a =
          ringOfIntegersComplexConj K a * u *
            (u⁻¹ : (𝓞 K)ˣ) := by simp
      _ = (u⁻¹ : (𝓞 K)ˣ) * a := by
        rw [hu]
        ac_rfl
  have hvconj : unitsComplexConj K v = v⁻¹ := by
    have hc := congrArg (ringOfIntegersComplexConj K) hv
    rw [map_mul] at hc
    have hcc :
        ringOfIntegersComplexConj K
            (ringOfIntegersComplexConj K a) = a := by
      ext
      exact complexConj_apply_apply K a
    rw [hcc, hv] at hc
    have hnorm : unitsComplexConj K v * v = 1 := by
      apply Units.ext
      change ringOfIntegersComplexConj K (v : 𝓞 K) *
          (v : 𝓞 K) = 1
      apply mul_right_cancel₀ ha0
      calc
        (ringOfIntegersComplexConj K (v : 𝓞 K) *
              (v : 𝓞 K)) * a =
            ringOfIntegersComplexConj K (v : 𝓞 K) *
              ((v : 𝓞 K) * a) := by rw [mul_assoc]
        _ = a := hc.symm
        _ = (1 : 𝓞 K) * a := by simp
    exact mul_eq_one_iff_eq_inv.mp hnorm
  obtain ⟨j, hj⟩ :=
    unit_inv_conj_is_root_of_unity hζ v hp2
  have hv_sq : v ^ 2 = (hζ.unit' ^ j) ^ 2 := by
    simpa only [hvconj, inv_inv, pow_two] using hj
  rcases Units.eq_or_eq_neg_of_sq_eq_sq
      v (hζ.unit' ^ j) hv_sq with hjv | hjv
  · exact ⟨j, by simpa [hjv] using hv⟩
  · exfalso
    let P : Ideal (𝓞 K) :=
      Ideal.span ({(hζ.unit' : 𝓞 K) - 1} : Set (𝓞 K))
    let Q := 𝓞 K ⧸ P
    have hPprime : Prime P := by
      simpa only [P] using hζ.prime_span_sub_one
    have hP0 : P ≠ ⊥ := hPprime.ne_zero
    letI : P.IsPrime := (Ideal.prime_iff_isPrime hP0).mp hPprime
    have haQ : algebraMap (𝓞 K) Q a ≠ 0 := by
      change Ideal.Quotient.mk P a ≠ 0
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
      simpa only [P, Ideal.mem_span_singleton] using ha
    have hvQ : algebraMap (𝓞 K) Q (v : 𝓞 K) = 1 := by
      apply mul_right_cancel₀ haQ
      calc
        algebraMap (𝓞 K) Q (v : 𝓞 K) *
              algebraMap (𝓞 K) Q a =
            algebraMap (𝓞 K) Q ((v : 𝓞 K) * a) := by
          rw [map_mul]
        _ = algebraMap (𝓞 K) Q
              (ringOfIntegersComplexConj K a) := by rw [hv]
        _ = algebraMap (𝓞 K) Q a :=
          ringOfIntegersComplexConj_eq_mod_zeta_sub_one hζ a
        _ = 1 * algebraMap (𝓞 K) Q a := by rw [one_mul]
    have hneg : (1 : Q) = -1 := by
      calc
        (1 : Q) = algebraMap (𝓞 K) Q (v : 𝓞 K) := hvQ.symm
        _ = algebraMap (𝓞 K) Q
            (-((hζ.unit' ^ j : (𝓞 K)ˣ) : 𝓞 K)) := by
          rw [hjv]
          rfl
        _ = -1 := by
          change -(algebraMap (𝓞 K) Q
            (((hζ.unit' : 𝓞 K) ^ j))) = -1
          rw [map_pow]
          change
            -(algebraMap (𝓞 K) Q (hζ.unit' : 𝓞 K)) ^ j = -1
          rw [eq_one_mod_one_sub, one_pow]
    apply hζ.two_not_mem_one_sub_zeta hp2
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat,
      ← neg_one_eq_one_iff_two_eq_zero]
    exact hneg.symm

/-- A conjugation-stable principal ideal prime to `(ζ - 1)` admits a
generator with the exact cyclotomic conjugation exponent. -/
lemma exists_conjugation_power_generator
    (hp2 : 2 < p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (I : Ideal (𝓞 K))
    (hprincipal : Submodule.IsPrincipal
      (I : Submodule (𝓞 K) (𝓞 K)))
    (hprime : ¬ Ideal.span
      ({(hζ.unit' : 𝓞 K) - 1} : Set (𝓞 K)) ∣ I)
    (hstable : conjugateIdeal I = I) :
    ∃ (a : 𝓞 K) (j : ℕ),
      I = Ideal.span {a} ∧
      ¬ (hζ.unit' : 𝓞 K) - 1 ∣ a ∧
      ringOfIntegersComplexConj K a =
        (hζ.unit' ^ j : (𝓞 K)ˣ) * a := by
  obtain ⟨a, haI⟩ := hprincipal.principal
  change I = Ideal.span {a} at haI
  have ha : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ a := by
    intro ha
    apply hprime
    rw [haI, Ideal.dvd_span_singleton, Ideal.mem_span_singleton]
    exact ha
  have hstableA :
      conjugateIdeal (Ideal.span {a}) = Ideal.span {a} := by
    rw [← haI]
    exact hstable
  obtain ⟨j, hj⟩ :=
    conjugation_eq_zeta_pow_of_stable_principal hp2 hζ a ha hstableA
  exact ⟨a, j, haI, ha, hj⟩

/-- Multiplying by the inverse-of-two root of unity preserves association
with the original generator. -/
lemma realAdjustedGenerator_associated
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (a : 𝓞 K) (j : ℕ) :
    Associated (realAdjustedGenerator r hζ a j) a := by
  let v : (𝓞 K)ˣ := hζ.unit' ^ ((r + 1) * j)
  refine ⟨v⁻¹, ?_⟩
  change (v : 𝓞 K) * a * (v⁻¹ : (𝓞 K)ˣ) = a
  calc
    (v : 𝓞 K) * a * (v⁻¹ : (𝓞 K)ˣ) =
        a * ((v : 𝓞 K) * (v⁻¹ : (𝓞 K)ˣ)) := by ac_rfl
    _ = a := by
      rw [← Units.val_mul]
      simp

/-- The inverse-of-two adjustment gives a real associated generator. -/
lemma exists_real_associated_generator_of_conj_eq_zeta_pow
    (hr : p = 2 * r + 1)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (a : 𝓞 K) (j : ℕ)
    (ha : ringOfIntegersComplexConj K a =
      (hζ.unit' ^ j : (𝓞 K)ˣ) * a) :
    ∃ b : 𝓞 K, Associated b a ∧
      ringOfIntegersComplexConj K b = b := by
  exact
    ⟨realAdjustedGenerator r hζ a j,
      realAdjustedGenerator_associated hζ a j,
      realAdjustedGenerator_real hr hζ a j ha⟩

set_option maxRecDepth 50000 in
/-- The real-generator conclusion immediately after equation (9).

The only global arithmetic input is `p ∤ h⁺`; all remaining hypotheses
describe the odd prime and the displayed nonramified ideal power. -/
theorem exists_realEquationNineGenerator
    (hplus : PlusClassNondivisibility K p)
    (hp2 : 2 < p) (hcop2 : Nat.Coprime 2 p)
    (hr : p = 2 * r + 1)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (J : Ideal (𝓞 K)) (q : 𝓞 K)
    (hprime : ¬ Ideal.span
      ({(hζ.unit' : 𝓞 K) - 1} : Set (𝓞 K)) ∣ J)
    (hqreal : ringOfIntegersComplexConj K q = q)
    (hpow : J ^ p = Ideal.span {q}) :
    ∃ (mu : 𝓞 K) (eta : (𝓞 K)ˣ),
      J = Ideal.span {mu} ∧
      ringOfIntegersComplexConj K mu = mu ∧
      q = eta * mu ^ p := by
  obtain ⟨hprincipal, hstable⟩ :=
    ideal_isPrincipal_and_stable_of_real_pow
      hplus hcop2 J q hqreal hpow
  obtain ⟨a, j, hJa, -, hconj⟩ :=
    exists_conjugation_power_generator
      hp2 hζ J hprincipal hprime hstable
  obtain ⟨mu, hmua, hmureal⟩ :=
    exists_real_associated_generator_of_conj_eq_zeta_pow
      hr hζ a j hconj
  have hJmu : J = Ideal.span {mu} := by
    rw [hJa]
    exact Ideal.span_singleton_eq_span_singleton.mpr hmua.symm
  have hassoc_q : Associated (mu ^ p) q := by
    rw [← Ideal.span_singleton_eq_span_singleton,
      ← Ideal.span_singleton_pow, ← hJmu, hpow]
  obtain ⟨eta, heta⟩ := hassoc_q
  exact
    ⟨mu, eta, hJmu, hmureal,
      by simpa [mul_comm] using heta.symm⟩

end

end Fermat.Irregular.VandiverRealEquationNineGeneratorPrime
