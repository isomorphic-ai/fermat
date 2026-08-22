import Fermat.Descent.Irregular.VandiverHistoricalPrime

/-!
# Prime-generic generator extraction for Vandiver's equation (8a)

The distinguished real quotient in equation (8a) gives an integral ideal
identity

`J ^ p = (q)`

with `q` nonzero and fixed by complex conjugation.  Nondivisibility of the
plus class number makes `J ^ 2` principal through the relative norm.
Since `2` and `p` are coprime, `J` itself is principal.  Its stability
under conjugation then shows that the square of a chosen generator has
conjugation quotient a pure power of `ζ`; squaring removes the possible
minus sign in the CM unit theorem.

This is the prime-generic content of the exponent-specific
`exists_squaredConjugationGenerator_of_real_pow...` theorems.  Construction
of the particular equation-(8a) ideal and proof of its `p`-th-power
identity remain explicit historical inputs.
-/

namespace Fermat.Irregular.VandiverEquationEightAGeneratorPrime

open scoped NumberField

open NumberField NumberField.IsCMField
open Fermat.Irregular.VandiverHistoricalPrime

noncomputable section

variable {K : Type} {p : ℕ} [Fact p.Prime]
  [Field K] [NumberField K] [NumberField.IsCMField K]
  [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- The conjugate of an integral ideal under CM complex conjugation. -/
def conjugateIdeal (I : Ideal (𝓞 K)) : Ideal (𝓞 K) :=
  I.map (ringOfIntegersComplexConj K).toRingHom

/-- Conjugating a principal integral ideal conjugates its generator. -/
lemma conjugateIdeal_span (a : 𝓞 K) :
    conjugateIdeal (Ideal.span {a}) =
      Ideal.span {ringOfIntegersComplexConj K a} := by
  simp only [conjugateIdeal, Ideal.map_span, Set.image_singleton]
  rfl

/-- Squaring removes the possible minus sign from the conjugation quotient
of a generator of a stable principal ideal. -/
lemma conjugation_sq_eq_zeta_pow_of_stable_principal
    (hp2 : 2 < p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (a : 𝓞 K)
    (ha0 : a ≠ 0)
    (hstable : conjugateIdeal (Ideal.span {a}) = Ideal.span {a}) :
    ∃ j : ℕ, ringOfIntegersComplexConj K (a ^ 2) =
      (hζ.unit' ^ j : (𝓞 K)ˣ) * a ^ 2 := by
  have hassoc : Associated (ringOfIntegersComplexConj K a) a := by
    rw [← Ideal.span_singleton_eq_span_singleton]
    rw [← conjugateIdeal_span]
    exact hstable
  obtain ⟨u, hu⟩ := hassoc
  let v : (𝓞 K)ˣ := u⁻¹
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
  refine ⟨2 * j, ?_⟩
  rw [map_pow, hv, mul_pow, ← Units.val_pow_eq_pow_val, hv_sq]
  congr 1
  rw [← pow_mul, Nat.mul_comm]

set_option maxRecDepth 50000 in
/-- A real principal `p`-th ideal power makes its base ideal principal and
conjugation-stable.  The only class-number input is `p ∤ h⁺`. -/
theorem ideal_isPrincipal_and_stable_of_real_pow
    (hplus : PlusClassNondivisibility K p)
    (hcop2 : Nat.Coprime 2 p)
    (J : Ideal (𝓞 K)) (q : 𝓞 K)
    (hqreal : ringOfIntegersComplexConj K q = q)
    (hpow : J ^ p = Ideal.span {q}) :
    Submodule.IsPrincipal (J : Ideal (𝓞 K)) ∧
      conjugateIdeal J = J := by
  obtain ⟨ρ, ε, -, -, hnorm⟩ :=
    exists_equationSevenD_of_idealPower hplus J q hpow
  let ρK : 𝓞 K := algebraMap (𝓞 K⁺) (𝓞 K) ρ
  let εK : (𝓞 K)ˣ := Units.map
    (algebraMap (𝓞 K⁺) (𝓞 K)).toMonoidHom ε
  have hq_sq : q ^ 2 = (εK : 𝓞 K) * ρK ^ p := by
    change q ^ 2 =
      algebraMap (𝓞 K⁺) (𝓞 K) (ε : 𝓞 K⁺) *
        (algebraMap (𝓞 K⁺) (𝓞 K) ρ) ^ p
    simpa only [pow_two, hqreal] using hnorm
  have hassoc : Associated (q ^ 2) (ρK ^ p) := by
    refine ⟨εK⁻¹, ?_⟩
    rw [hq_sq]
    calc
      ((εK : 𝓞 K) * ρK ^ p) * (εK⁻¹ : (𝓞 K)ˣ) =
          ρK ^ p *
            ((εK : 𝓞 K) * (εK⁻¹ : (𝓞 K)ˣ)) := by
        ac_rfl
      _ = ρK ^ p := by
        rw [← Units.val_mul]
        simp
  have hspan : Ideal.span {q ^ 2} = Ideal.span {ρK ^ p} :=
    Ideal.span_singleton_eq_span_singleton.mpr hassoc
  have hpoweq : (J ^ 2) ^ p = (Ideal.span {ρK}) ^ p := by
    calc
      (J ^ 2) ^ p = (J ^ p) ^ 2 := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 p]
      _ = (Ideal.span {q}) ^ 2 := by rw [hpow]
      _ = Ideal.span {q ^ 2} := Ideal.span_singleton_pow q 2
      _ = Ideal.span {ρK ^ p} := hspan
      _ = (Ideal.span {ρK}) ^ p :=
        (Ideal.span_singleton_pow ρK p).symm
  have hJ2eq : J ^ 2 = Ideal.span {ρK} :=
    pow_left_injective (M := Ideal (𝓞 K))
      (Fact.out : Nat.Prime p).ne_zero hpoweq
  have hJ2 : Submodule.IsPrincipal (J ^ 2 : Ideal (𝓞 K)) := by
    rw [hJ2eq]
    infer_instance
  have hJp : Submodule.IsPrincipal (J ^ p : Ideal (𝓞 K)) := by
    rw [hpow]
    infer_instance
  have hJprincipal : Submodule.IsPrincipal (J : Ideal (𝓞 K)) :=
    Fermat.Irregular.VandiverCriterion.ideal_isPrincipal_of_coprime_powers
      (L := K) hcop2 J hJ2 hJp
  have hstable : conjugateIdeal J = J := by
    apply pow_left_injective (M := Ideal (𝓞 K))
      (Fact.out : Nat.Prime p).ne_zero
    calc
      conjugateIdeal J ^ p = conjugateIdeal (J ^ p) := by
        exact (Ideal.map_pow
          (ringOfIntegersComplexConj K).toRingHom J p).symm
      _ = conjugateIdeal (Ideal.span {q}) := by rw [hpow]
      _ = Ideal.span {ringOfIntegersComplexConj K q} :=
        conjugateIdeal_span q
      _ = Ideal.span {q} := by rw [hqreal]
      _ = J ^ p := hpow.symm
  exact ⟨hJprincipal, hstable⟩

set_option maxRecDepth 50000 in
/-- Prime-generic equation-(8a) generator extraction.

The theorem does not require the ideal to be prime to `ζ-1`.  It records
the square of the generator, for which the conjugation quotient is always
a pure power of `ζ`. -/
theorem exists_squaredConjugationGenerator_of_real_pow
    (hplus : PlusClassNondivisibility K p)
    (hp2 : 2 < p) (hcop2 : Nat.Coprime 2 p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (J : Ideal (𝓞 K)) (q : 𝓞 K) (hq0 : q ≠ 0)
    (hqreal : ringOfIntegersComplexConj K q = q)
    (hpow : J ^ p = Ideal.span {q}) :
    ∃ (ρ : 𝓞 K) (η : (𝓞 K)ˣ) (j : ℕ),
      J = Ideal.span {ρ} ∧
      q = η * ρ ^ p ∧
      ringOfIntegersComplexConj K (ρ ^ 2) =
        (hζ.unit' ^ j : (𝓞 K)ˣ) * ρ ^ 2 := by
  obtain ⟨hprincipal, hstable⟩ :=
    ideal_isPrincipal_and_stable_of_real_pow
      hplus hcop2 J q hqreal hpow
  obtain ⟨ρ, hJρ⟩ := hprincipal.principal
  change J = Ideal.span {ρ} at hJρ
  have hρ0 : ρ ≠ 0 := by
    intro hρ
    apply hq0
    rw [← Ideal.span_singleton_eq_bot]
    calc
      Ideal.span {q} = J ^ p := hpow.symm
      _ = (Ideal.span {ρ}) ^ p := by rw [hJρ]
      _ = 0 := by
        rw [hρ, Set.singleton_zero, Ideal.span_zero,
          ← Ideal.zero_eq_bot,
          zero_pow (Fact.out : Nat.Prime p).ne_zero]
  have hstableρ :
      conjugateIdeal (Ideal.span {ρ}) = Ideal.span {ρ} := by
    rw [← hJρ]
    exact hstable
  obtain ⟨j, hj⟩ :=
    conjugation_sq_eq_zeta_pow_of_stable_principal
      hp2 hζ ρ hρ0 hstableρ
  have hassoc_q : Associated (ρ ^ p) q := by
    rw [← Ideal.span_singleton_eq_span_singleton,
      ← Ideal.span_singleton_pow, ← hJρ, hpow]
  obtain ⟨η, hη⟩ := hassoc_q
  exact
    ⟨ρ, η, j, hJρ, by simpa [mul_comm] using hη.symm, hj⟩

end

end Fermat.Irregular.VandiverEquationEightAGeneratorPrime
