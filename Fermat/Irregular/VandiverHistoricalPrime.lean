import Fermat.Irregular.VandiverHistoricalDescent
import Fermat.Irregular.VandiverLemmaOne
import Fermat.Irregular.CyclotomicDiscriminantPrime
import FltRegular.NumberTheory.Cyclotomic.MoreLemmas

/-!
# Prime-generic algebra in Vandiver's historical descent

The exponent-specific historical files for `59`, `67`, `157`, `491`,
`587`, and `691` contain the same proofs after the substitutions

* `p`, `p - 1`, and `p - 2`;
* `2 * p` and `p ^ 2`; and
* `p / 2` and `p / 2 + 1`.

This module begins the shared implementation by extracting the parts which
depend only on the prime and on explicitly supplied historical inputs:

* nondivisibility of the plus class number;
* Vandiver's Lemma I;
* Vandiver's Lemma II and the Bernoulli cube condition.

Prime-specific finite certificates stay in the exponent namespaces.  They
are passed to the generic theorems only through these mathematical
interfaces.
-/

namespace Fermat.Irregular.VandiverHistoricalPrime

open scoped NumberField nonZeroDivisors

open Fermat.Irregular.VandiverCriterion
open Fermat.Irregular.VandiverHistoricalDescent

noncomputable section

variable {K : Type} {p : ℕ} [Fact p.Prime]
  [Field K] [NumberField K] [NumberField.IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- The exact plus-class input used in Vandiver's real-ideal steps. -/
def PlusClassNondivisibility (K : Type*) [Field K] [NumberField K]
    (p : ℕ) : Prop :=
  ¬ p ∣ NumberField.classNumber (NumberField.maximalRealSubfield K)

/-- For a prime `p ≥ 5`, the exponents `p - 2` and `p` are coprime.
This is the arithmetic fact behind the Bézout step from (7a),(7d) to (8). -/
theorem coprime_p_sub_two (hp5 : 5 ≤ p) : Nat.Coprime (p - 2) p := by
  have hp : p.Prime := Fact.out
  apply (hp.coprime_iff_not_dvd.mpr ?_).symm
  intro hdiv
  have hpos : 0 < p - 2 := by omega
  have hle : p ≤ p - 2 := Nat.le_of_dvd hpos hdiv
  omega

omit [NumberField.IsCMField K] in
/-- A fractional ideal of the maximal real field whose `p`-th power is
principal is principal when `p` does not divide the plus class number. -/
theorem realFractionalIdeal_isPrincipal_of_pow
    [IsCyclotomicExtension {p} ℚ K]
    (hplus : PlusClassNondivisibility K p)
    (I : FractionalIdeal (𝓞 K⁺)⁰ K⁺)
    (hpow : Submodule.IsPrincipal
      ((I ^ p : FractionalIdeal (𝓞 K⁺)⁰ K⁺) :
        Submodule (𝓞 K⁺) K⁺)) :
    Submodule.IsPrincipal (I : Submodule (𝓞 K⁺) K⁺) := by
  exact fractionalIdeal_isPrincipal_of_pow_of_not_dvd_classNumber
    Fact.out hplus I hpow

set_option maxRecDepth 50000 in
omit [NumberField.IsCMField K] in
/-- Element-level form of the plus-class calculation. -/
theorem exists_real_unit_mul_pow_generator
    [IsCyclotomicExtension {p} ℚ K]
    (hplus : PlusClassNondivisibility K p)
    (I : Ideal (𝓞 K⁺)) (a : 𝓞 K⁺)
    (hpow : I ^ p = Ideal.span {a}) :
    ∃ (ρ : 𝓞 K⁺) (ε : (𝓞 K⁺)ˣ),
      I = Ideal.span {ρ} ∧ a = ε * ρ ^ p := by
  exact exists_unit_mul_pow_eq_of_ideal_pow_eq_span
    (F := K⁺) (p := p) Fact.out hplus I a hpow

set_option maxRecDepth 50000 in
omit [NumberField.IsCMField K] in
/-- Relative-norm form of the real generator calculation used in (7b). -/
theorem exists_realGenerator_of_relativeNorm
    [IsCyclotomicExtension {p} ℚ K]
    (hplus : PlusClassNondivisibility K p)
    (J : Ideal (𝓞 K)) (a : 𝓞 K)
    (hpow : J ^ p = Ideal.span {a}) :
    ∃ (ρ : 𝓞 K⁺) (ε : (𝓞 K⁺)ˣ),
      Ideal.relNorm (𝓞 K⁺) J = Ideal.span {ρ} ∧
      Algebra.intNorm (𝓞 K⁺) (𝓞 K) a = ε * ρ ^ p := by
  apply exists_real_unit_mul_pow_generator hplus
    (Ideal.relNorm (𝓞 K⁺) J) (Algebra.intNorm (𝓞 K⁺) (𝓞 K) a)
  calc
    Ideal.relNorm (𝓞 K⁺) J ^ p =
        Ideal.relNorm (𝓞 K⁺) (J ^ p) := by
      rw [map_pow]
    _ = Ideal.relNorm (𝓞 K⁺) (Ideal.span {a}) := by rw [hpow]
    _ = Ideal.span {Algebra.intNorm (𝓞 K⁺) (𝓞 K) a} :=
      Ideal.relNorm_singleton (𝓞 K⁺) a

omit [Fact p.Prime] in
/-- In the quadratic CM extension, the integral norm is multiplication by
complex conjugation.  This statement is independent of primality of `p`. -/
theorem algebraMap_intNorm_eq_mul_conj
    [IsCyclotomicExtension {p} ℚ K]
    (a : 𝓞 K) :
    algebraMap (𝓞 K⁺) (𝓞 K) (Algebra.intNorm (𝓞 K⁺) (𝓞 K) a) =
      a * NumberField.IsCMField.ringOfIntegersComplexConj K a := by
  classical
  apply NumberField.RingOfIntegers.ext
  change algebraMap K⁺ K
      (algebraMap (𝓞 K⁺) K⁺ (Algebra.intNorm (𝓞 K⁺) (𝓞 K) a)) =
    (a : K) * NumberField.IsCMField.complexConj K (a : K)
  rw [Algebra.algebraMap_intNorm (A := 𝓞 K⁺) (K := K⁺) (L := K)
    (B := 𝓞 K)]
  rw [Algebra.norm_eq_prod_automorphisms]
  let c : Gal(K/K⁺) := NumberField.IsCMField.complexConj K
  have hc : (1 : Gal(K/K⁺)) ≠ c :=
    (NumberField.IsCMField.complexConj_ne_one K).symm
  have hcard : Fintype.card Gal(K/K⁺) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
      Algebra.IsQuadraticExtension.finrank_eq_two K⁺ K]
  have hpair : ({1, c} : Finset (Gal(K/K⁺))) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp [hcard, hc]
  rw [← hpair]
  simp [c, hc]

set_option maxRecDepth 50000 in
/-- Vandiver's equation (7d), parameterized by the plus-class
nondivisibility input. -/
theorem exists_equationSevenD_of_idealPower
    [IsCyclotomicExtension {p} ℚ K]
    (hplus : PlusClassNondivisibility K p)
    (J : Ideal (𝓞 K)) (a : 𝓞 K)
    (hpow : J ^ p = Ideal.span {a}) :
    ∃ (ρ : 𝓞 K⁺) (ε : (𝓞 K⁺)ˣ),
      Ideal.relNorm (𝓞 K⁺) J = Ideal.span {ρ} ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K
          (algebraMap (𝓞 K⁺) (𝓞 K) ρ) =
        algebraMap (𝓞 K⁺) (𝓞 K) ρ ∧
      a * NumberField.IsCMField.ringOfIntegersComplexConj K a =
        algebraMap (𝓞 K⁺) (𝓞 K) (ε : 𝓞 K⁺) *
          algebraMap (𝓞 K⁺) (𝓞 K) ρ ^ p := by
  obtain ⟨ρ, ε, hI, ha⟩ :=
    exists_realGenerator_of_relativeNorm hplus J a hpow
  refine ⟨ρ, ε, hI,
    (NumberField.IsCMField.ringOfIntegersComplexConj K).commutes ρ, ?_⟩
  rw [← algebraMap_intNorm_eq_mul_conj (p := p)]
  simpa only [map_mul, map_pow] using
    congrArg (algebraMap (𝓞 K⁺) (𝓞 K)) ha

set_option maxRecDepth 50000 in
/-- The prime-generic class-group Bézout step between equations (7a),
(7d), and (8). -/
theorem fractionalIdeal_isPrincipal_of_vandiverSeven
    {A L : Type*} [CommRing A] [IsDedekindDomain A]
    [Field L] [Algebra A L] [IsFractionRing A L]
    (hp5 : 5 ≤ p)
    {I J : FractionalIdeal A⁰ L} (hI0 : I ≠ 0) (hJ0 : J ≠ 0)
    (hJp : Submodule.IsPrincipal
      ((J ^ p : FractionalIdeal A⁰ L) : Submodule A L))
    (hsevenA : Submodule.IsPrincipal
      ((I * J ^ (p - 1) : FractionalIdeal A⁰ L) : Submodule A L))
    (hsevenD : Submodule.IsPrincipal
      ((I * J : FractionalIdeal A⁰ L) : Submodule A L)) :
    Submodule.IsPrincipal (I : Submodule A L) := by
  have hJpred : Submodule.IsPrincipal
      ((J ^ (p - 2) : FractionalIdeal A⁰ L) : Submodule A L) := by
    have hquot := fractionalIdeal_isPrincipal_div hsevenA hsevenD
    have heq : (I * J ^ (p - 1)) / (I * J) = J ^ (p - 2) := by
      apply (div_eq_iff (mul_ne_zero hI0 hJ0)).mpr
      rw [show p - 1 = (p - 2) + 1 by omega, pow_succ]
      ac_rfl
    rw [← heq]
    exact hquot
  have hJ : Submodule.IsPrincipal (J : Submodule A L) :=
    fractionalIdeal_isPrincipal_of_coprime_powers
      (coprime_p_sub_two hp5) J hJpred hJp
  have hquot := fractionalIdeal_isPrincipal_div hsevenD hJ
  have heq : (I * J) / J = I := by
    apply (div_eq_iff hJ0).mpr
    rfl
  rw [heq] at hquot
  exact hquot

set_option maxRecDepth 50000 in
omit [NumberField.IsCMField K] in
/-- Prime-generic passage from the two principal products in (7a),(7d)
to equation (8). -/
theorem exists_equationEight_of_sevenASevenD
    (hp5 : 5 ≤ p)
    (I J : Ideal (𝓞 K)) (a b r s : 𝓞 K)
    (hI0 : I ≠ 0) (hJ0 : J ≠ 0)
    (hIpow : I ^ p = Ideal.span {a})
    (hJpow : J ^ p = Ideal.span {b})
    (hsevenA : I * J ^ (p - 1) = Ideal.span {r})
    (hsevenD : I * J = Ideal.span {s}) :
    ∃ (ρ : 𝓞 K) (η : (𝓞 K)ˣ),
      I = Ideal.span {ρ} ∧ a = η * ρ ^ p := by
  let IF : FractionalIdeal (𝓞 K)⁰ K := I
  let JF : FractionalIdeal (𝓞 K)⁰ K := J
  have hIF0 : IF ≠ 0 := by
    dsimp [IF]
    intro h
    rw [FractionalIdeal.coeIdeal_eq_zero] at h
    exact hI0 h
  have hJF0 : JF ≠ 0 := by
    dsimp [JF]
    intro h
    rw [FractionalIdeal.coeIdeal_eq_zero] at h
    exact hJ0 h
  have hJp : Submodule.IsPrincipal
      ((JF ^ p : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
    rw [FractionalIdeal.isPrincipal_iff]
    refine ⟨(b : K), ?_⟩
    dsimp [JF]
    rw [← FractionalIdeal.coeIdeal_span_singleton, ← hJpow,
      FractionalIdeal.coeIdeal_pow]
  have h7a : Submodule.IsPrincipal
      ((IF * JF ^ (p - 1) : FractionalIdeal (𝓞 K)⁰ K) :
        Submodule (𝓞 K) K) := by
    rw [FractionalIdeal.isPrincipal_iff]
    refine ⟨(r : K), ?_⟩
    dsimp [IF, JF]
    rw [← FractionalIdeal.coeIdeal_span_singleton, ← hsevenA,
      FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_pow]
  have h7d : Submodule.IsPrincipal
      ((IF * JF : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
    rw [FractionalIdeal.isPrincipal_iff]
    refine ⟨(s : K), ?_⟩
    dsimp [IF, JF]
    rw [← FractionalIdeal.coeIdeal_span_singleton, ← hsevenD,
      FractionalIdeal.coeIdeal_mul]
  have hIF : Submodule.IsPrincipal (IF : Submodule (𝓞 K) K) :=
    fractionalIdeal_isPrincipal_of_vandiverSeven
      hp5 hIF0 hJF0 hJp h7a h7d
  have hIF' : Submodule.IsPrincipal
      ((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
    simpa only [IF] using hIF
  have hI : Submodule.IsPrincipal (I : Ideal (𝓞 K)) :=
    (IsFractionRing.coeSubmodule_isPrincipal (𝓞 K) K).mp hIF'
  exact exists_unit_mul_pow_eq_of_isPrincipal_ideal I a hI hIpow

set_option maxRecDepth 50000 in
omit [NumberField.IsCMField K] in
/-- Source-faithful assembly of Lemma I, equations (7a),(7d), and (8). -/
theorem exists_equationEight_of_lemmaOneSevenD
    [IsCyclotomicExtension {p} ℚ K]
    (hp5 : 5 ≤ p)
    (hlemma : Fermat.Irregular.VandiverLemmaOne.LemmaOne K p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (I J : Ideal (𝓞 K)) (a b s : 𝓞 K)
    (hI0 : I ≠ 0) (hJ0 : J ≠ 0)
    (hIpow : I ^ p = Ideal.span {a})
    (hJpow : J ^ p = Ideal.span {b})
    (hprimary :
      Fermat.Irregular.VandiverLemmaOne.IsKummerPrimary
        hζ (a * b ^ (p - 1)))
    (hsevenD : I * J = Ideal.span {s}) :
    ∃ (ρ : 𝓞 K) (η : (𝓞 K)ˣ),
      I = Ideal.span {ρ} ∧ a = η * ρ ^ p := by
  obtain ⟨r, hsevenA⟩ :=
    Fermat.Irregular.VandiverLemmaOne.exists_equationSevenA_generator
      hlemma hζ I J a b hIpow hJpow (by simpa using hprimary)
  exact exists_equationEight_of_sevenASevenD hp5
    I J a b r s hI0 hJ0 hIpow hJpow hsevenA hsevenD

set_option maxRecDepth 50000 in
omit [NumberField.IsCMField K] in
/-- Unit-normalized assembly of Lemma I, equations (7a),(7d), and (8). -/
theorem exists_equationEight_of_lemmaOneSevenDUnit
    [IsCyclotomicExtension {p} ℚ K]
    (hp5 : 5 ≤ p)
    (hlemma : Fermat.Irregular.VandiverLemmaOne.LemmaOne K p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (u : (𝓞 K)ˣ) (I J : Ideal (𝓞 K)) (a b s : 𝓞 K)
    (hI0 : I ≠ 0) (hJ0 : J ≠ 0)
    (hIpow : I ^ p = Ideal.span {a})
    (hJpow : J ^ p = Ideal.span {b})
    (hprimary :
      Fermat.Irregular.VandiverLemmaOne.IsKummerPrimary hζ
        ((u : 𝓞 K) * (a * b ^ (p - 1))))
    (hsevenD : I * J = Ideal.span {s}) :
    ∃ (ρ : 𝓞 K) (η : (𝓞 K)ˣ),
      I = Ideal.span {ρ} ∧ a = η * ρ ^ p := by
  obtain ⟨r, hsevenA⟩ :=
    Fermat.Irregular.VandiverLemmaOne.exists_equationSevenA_generator_of_unit
      hlemma hζ u I J a b hIpow hJpow (by simpa using hprimary)
  exact exists_equationEight_of_sevenASevenD hp5
    I J a b r s hI0 hJ0 hIpow hJpow hsevenA hsevenD

/-- The elementary equation-(8) elimination is independent of the prime
except for the common exponent. -/
lemma equationEight_pair_difference
    {R : Type*} [CommRing R]
    (p : ℕ) (t eta : Rˣ) (omega theta rhoa rhominus : R)
    (ha : omega + (t : R) * theta =
      (1 - (t : R)) * eta * rhoa ^ p)
    (hminus : omega + (t⁻¹ : Rˣ) * theta =
      (1 - (t⁻¹ : Rˣ)) * eta * rhominus ^ p) :
    (1 - (t : R)) * eta * (rhoa ^ p - rhominus ^ p) =
      (1 + (t : R)) * (omega + theta) := by
  have htinv : (t : R) * (t⁻¹ : Rˣ) = 1 := by
    rw [← Units.val_mul]
    simp
  have hcoef : (1 - (t : R)) =
      -(t : R) * (1 - (t⁻¹ : Rˣ)) := by
    linear_combination -htinv
  have hfirst : (1 - (t : R)) * eta * rhoa ^ p =
      omega + (t : R) * theta := ha.symm
  have hsecond : (1 - (t : R)) * eta * rhominus ^ p =
      -((t : R) * omega + theta) := by
    rw [hcoef]
    calc
      (-(t : R) * (1 - (t⁻¹ : Rˣ))) * eta * rhominus ^ p =
          -(t : R) *
            ((1 - (t⁻¹ : Rˣ)) * eta * rhominus ^ p) := by ring
      _ = -(t : R) *
            (omega + (t⁻¹ : Rˣ) * theta) := by rw [hminus]
      _ = -((t : R) * omega + theta) := by
        linear_combination -theta * htinv
  rw [mul_sub, hfirst, hsecond]
  ring

/-- The universal quadratic elimination in Vandiver's equation (10a). -/
lemma equationTenA_quadraticElimination
    {R : Type*} [CommRing R]
    (p : ℕ) (ω θ A B Ua Ub Uzero Xa Xb Xzero : R)
    (ha : ω ^ 2 + A * (ω * θ) + θ ^ 2 = Ua * Xa ^ p)
    (hb : ω ^ 2 + B * (ω * θ) + θ ^ 2 = Ub * Xb ^ p)
    (hzero : ω ^ 2 + 2 * (ω * θ) + θ ^ 2 = Uzero * Xzero) :
    (2 - B) * (Ua * Xa ^ p) - (2 - A) * (Ub * Xb ^ p) =
      (A - B) * (Uzero * Xzero) := by
  rw [← ha, ← hb, ← hzero]
  ring

omit [NumberField.IsCMField K] in
/-- Final prime-generic assembly with the historical construction,
Vandiver's Lemma II, and the finite Bernoulli input kept explicit. -/
theorem secondCaseExcluded_of_vandiverLemmaTwo
    [IsCyclotomicExtension {p} ℚ K]
    (hp5 : 5 ≤ p) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (admissible : HistoricalAdmissibility hζ)
    (hstart : SecondCaseStartsHistoricalDescent hζ admissible)
    (hreduce : EquationsSevenToTenReduction hζ admissible)
    (hLemmaTwo : Fermat.Irregular.VandiverUnitLemma.VandiverLemmaTwo K p)
    (hB : Fermat.Irregular.VandiverData.BernoulliCubeCondition p) :
    Fermat.SecondCaseExcluded p :=
  Fermat.Irregular.VandiverHistoricalDescent.secondCaseExcluded_of_vandiver_lemmaTwo
    (by omega) hp5 hζ admissible hstart hreduce hLemmaTwo hB

end

end Fermat.Irregular.VandiverHistoricalPrime
