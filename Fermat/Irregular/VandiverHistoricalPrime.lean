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

/-! ## Prime-generic historical-state reduction -/

/-- The source invariant used in Vandiver's historical construction:
the three integral entries and the coefficient unit are fixed by complex
conjugation.  The equation, nonvanishing, and coprimality hypotheses remain
fields of `HistoricalState` itself. -/
def RealSourceAdmissible {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    HistoricalAdmissibility hζ :=
  fun s ↦
    NumberField.IsCMField.ringOfIntegersComplexConj K s.omega = s.omega ∧
    NumberField.IsCMField.ringOfIntegersComplexConj K s.theta = s.theta ∧
    NumberField.IsCMField.ringOfIntegersComplexConj K s.xi = s.xi ∧
    NumberField.IsCMField.unitsComplexConj K s.eta = s.eta

/-- The finite support of the distinct prime-ideal factors of the principal
ideal generated by `x`.  This is the support whose cardinality is the
well-founded measure in the historical descent. -/
def primeIdealFactorSupport (x : 𝓞 K) : Finset (Ideal (𝓞 K)) :=
  (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {x})).toFinset

/-- The output of Vandiver's calculation through equation (10a), after the
three principal generators have been made literally real.  All finite,
prime-specific work remains visible in the fields of this structure. -/
structure WeightedReductionData {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (s : HistoricalState hζ) where
  x : 𝓞 K
  y : 𝓞 K
  z : 𝓞 K
  epsilon₁ : (𝓞 K)ˣ
  epsilon₂ : (𝓞 K)ˣ
  epsilon₃ : (𝓞 K)ˣ
  rationalBase : ℤ
  highCongruence :
    ((1 : 𝓞 K) - hζ.unit') ^ (2 * p) ∣
      (((epsilon₁ / epsilon₂ : (𝓞 K)ˣ) : 𝓞 K) -
        (rationalBase : 𝓞 K) ^ p)
  weightedEquation :
    epsilon₁ * x ^ p + epsilon₂ * y ^ p =
      epsilon₃ * (kappa hζ ^ (2 * s.m - 1) * z) ^ p
  z_ne_zero : z ≠ 0
  coprime_xy : IsCoprime x y
  coprime_yz : IsCoprime y z
  coprime_xz : IsCoprime x z
  real_x : NumberField.IsCMField.ringOfIntegersComplexConj K x = x
  real_y : NumberField.IsCMField.ringOfIntegersComplexConj K y = y
  real_z : NumberField.IsCMField.ringOfIntegersComplexConj K z = z
  real_eta : NumberField.IsCMField.unitsComplexConj K (epsilon₃ / epsilon₂) =
    epsilon₃ / epsilon₂
  factorSupport_strict :
    primeIdealFactorSupport z ⊂ primeIdealFactorSupport s.xi

/-- The same finite output before the three principal generators have been
normalized to be real.  Their exact conjugation quotients are explicit
powers of the chosen primitive root. -/
structure ConjugationPowerReductionData {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (s : HistoricalState hζ) where
  x : 𝓞 K
  y : 𝓞 K
  z : 𝓞 K
  epsilon₁ : (𝓞 K)ˣ
  epsilon₂ : (𝓞 K)ˣ
  epsilon₃ : (𝓞 K)ˣ
  rationalBase : ℤ
  highCongruence :
    ((1 : 𝓞 K) - hζ.unit') ^ (2 * p) ∣
      (((epsilon₁ / epsilon₂ : (𝓞 K)ˣ) : 𝓞 K) -
        (rationalBase : 𝓞 K) ^ p)
  weightedEquation :
    epsilon₁ * x ^ p + epsilon₂ * y ^ p =
      epsilon₃ * (kappa hζ ^ (2 * s.m - 1) * z) ^ p
  z_ne_zero : z ≠ 0
  coprime_xy : IsCoprime x y
  coprime_yz : IsCoprime y z
  coprime_xz : IsCoprime x z
  conjugationExponent_x : ℕ
  conjugationExponent_y : ℕ
  conjugationExponent_z : ℕ
  conjugation_x :
    NumberField.IsCMField.ringOfIntegersComplexConj K x =
      (hζ.unit' ^ conjugationExponent_x : (𝓞 K)ˣ) * x
  conjugation_y :
    NumberField.IsCMField.ringOfIntegersComplexConj K y =
      (hζ.unit' ^ conjugationExponent_y : (𝓞 K)ˣ) * y
  conjugation_z :
    NumberField.IsCMField.ringOfIntegersComplexConj K z =
      (hζ.unit' ^ conjugationExponent_z : (𝓞 K)ˣ) * z
  real_eta : NumberField.IsCMField.unitsComplexConj K (epsilon₃ / epsilon₂) =
    epsilon₃ / epsilon₂
  factorSupport_strict :
    primeIdealFactorSupport z ⊂ primeIdealFactorSupport s.xi

/-- The exact interface needed to normalize a generator whose conjugation
quotient is a power of `ζ`.  A concrete exponent supplies the multiplier
and proves the two mathematical facts used below: `p`-th powers are
unchanged, and the adjusted generator is real. -/
structure RealGeneratorNormalizer {ζ : K} (hζ : IsPrimitiveRoot ζ p) where
  multiplier : ℕ → (𝓞 K)ˣ
  power_eq :
    ∀ (a : 𝓞 K) (j : ℕ), ((multiplier j : 𝓞 K) * a) ^ p = a ^ p
  real :
    ∀ (a : 𝓞 K) (j : ℕ),
      NumberField.IsCMField.ringOfIntegersComplexConj K a =
        (hζ.unit' ^ j : (𝓞 K)ˣ) * a →
      NumberField.IsCMField.ringOfIntegersComplexConj K
          ((multiplier j : 𝓞 K) * a) =
        (multiplier j : 𝓞 K) * a

/-- Apply the unit multiplier supplied by a real-generator normalizer. -/
def RealGeneratorNormalizer.adjusted {ζ : K} {hζ : IsPrimitiveRoot ζ p}
    (normalizer : RealGeneratorNormalizer hζ)
    (a : 𝓞 K) (j : ℕ) : 𝓞 K :=
  (normalizer.multiplier j : 𝓞 K) * a

lemma RealGeneratorNormalizer.adjusted_associated
    {ζ : K} {hζ : IsPrimitiveRoot ζ p}
    (normalizer : RealGeneratorNormalizer hζ)
    (a : 𝓞 K) (j : ℕ) :
    Associated (normalizer.adjusted a j) a := by
  let v : (𝓞 K)ˣ := normalizer.multiplier j
  refine ⟨v⁻¹, ?_⟩
  change (v : 𝓞 K) * a * (v⁻¹ : (𝓞 K)ˣ) = a
  calc
    (v : 𝓞 K) * a * (v⁻¹ : (𝓞 K)ˣ) =
        a * ((v : 𝓞 K) * (v⁻¹ : (𝓞 K)ˣ)) := by ac_rfl
    _ = a := by rw [← Units.val_mul]; simp

/-- Normalize all three generators.  The proof is independent of the
concrete inverse-of-two exponent: it consumes only the explicit normalizer
interface and proves preservation of the equation, coprimality,
nonvanishing, and strict support descent. -/
noncomputable def weightedReductionData_of_conjugationPowers
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) {s : HistoricalState hζ}
    (normalizer : RealGeneratorNormalizer hζ)
    (d : ConjugationPowerReductionData hζ s) :
    WeightedReductionData hζ s where
  x := normalizer.adjusted d.x d.conjugationExponent_x
  y := normalizer.adjusted d.y d.conjugationExponent_y
  z := normalizer.adjusted d.z d.conjugationExponent_z
  epsilon₁ := d.epsilon₁
  epsilon₂ := d.epsilon₂
  epsilon₃ := d.epsilon₃
  rationalBase := d.rationalBase
  highCongruence := d.highCongruence
  weightedEquation := by
    change
      d.epsilon₁ *
          ((normalizer.multiplier d.conjugationExponent_x : 𝓞 K) * d.x) ^ p +
        d.epsilon₂ *
          ((normalizer.multiplier d.conjugationExponent_y : 𝓞 K) * d.y) ^ p =
      d.epsilon₃ *
        (kappa hζ ^ (2 * s.m - 1) *
          ((normalizer.multiplier d.conjugationExponent_z : 𝓞 K) * d.z)) ^ p
    rw [normalizer.power_eq, normalizer.power_eq, mul_pow,
      normalizer.power_eq, ← mul_pow]
    exact d.weightedEquation
  z_ne_zero :=
    (normalizer.adjusted_associated d.z d.conjugationExponent_z).ne_zero_iff.mpr
      d.z_ne_zero
  coprime_xy :=
    (isCoprime_mul_unit_left_left
      (normalizer.multiplier d.conjugationExponent_x).isUnit
      d.x
      (normalizer.adjusted d.y d.conjugationExponent_y)).mpr
      ((isCoprime_mul_unit_left_right
        (normalizer.multiplier d.conjugationExponent_y).isUnit
        d.x d.y).mpr d.coprime_xy)
  coprime_yz :=
    (isCoprime_mul_unit_left_left
      (normalizer.multiplier d.conjugationExponent_y).isUnit
      d.y
      (normalizer.adjusted d.z d.conjugationExponent_z)).mpr
      ((isCoprime_mul_unit_left_right
        (normalizer.multiplier d.conjugationExponent_z).isUnit
        d.y d.z).mpr d.coprime_yz)
  coprime_xz :=
    (isCoprime_mul_unit_left_left
      (normalizer.multiplier d.conjugationExponent_x).isUnit
      d.x
      (normalizer.adjusted d.z d.conjugationExponent_z)).mpr
      ((isCoprime_mul_unit_left_right
        (normalizer.multiplier d.conjugationExponent_z).isUnit
        d.x d.z).mpr d.coprime_xz)
  real_x := normalizer.real d.x d.conjugationExponent_x d.conjugation_x
  real_y := normalizer.real d.y d.conjugationExponent_y d.conjugation_y
  real_z := normalizer.real d.z d.conjugationExponent_z d.conjugation_z
  real_eta := d.real_eta
  factorSupport_strict := by
    have hsupp :
        primeIdealFactorSupport
            (normalizer.adjusted d.z d.conjugationExponent_z) =
          primeIdealFactorSupport d.z := by
      unfold primeIdealFactorSupport
      rw [Ideal.span_singleton_eq_span_singleton.mpr
        (normalizer.adjusted_associated d.z d.conjugationExponent_z)]
    rw [hsupp]
    exact d.factorSupport_strict

/-- The remaining prime-specific input between Lemma II and equation (10b):
every displayed `p`-th root of the real quotient unit can itself be chosen
real without changing its `p`-th power. -/
def RealUnitRootNormalization {ζ : K} (_hζ : IsPrimitiveRoot ζ p) : Prop :=
  ∀ (a v : (𝓞 K)ˣ), a = v ^ p →
    ∃ w : (𝓞 K)ˣ, a = w ^ p ∧
      NumberField.IsCMField.unitsComplexConj K w = w

private noncomputable def adjustedRoot
    {ζ : K} {hζ : IsPrimitiveRoot ζ p}
    (hroot : RealUnitRootNormalization hζ)
    (a v : (𝓞 K)ˣ) (hv : a = v ^ p) : (𝓞 K)ˣ :=
  (hroot a v hv).choose

private lemma adjustedRoot_pow
    {ζ : K} {hζ : IsPrimitiveRoot ζ p}
    (hroot : RealUnitRootNormalization hζ)
    (a v : (𝓞 K)ˣ) (hv : a = v ^ p) :
    a = adjustedRoot hroot a v hv ^ p :=
  (hroot a v hv).choose_spec.1

private lemma adjustedRoot_real
    {ζ : K} {hζ : IsPrimitiveRoot ζ p}
    (hroot : RealUnitRootNormalization hζ)
    (a v : (𝓞 K)ˣ) (hv : a = v ^ p) :
    NumberField.IsCMField.unitsComplexConj K
        (adjustedRoot hroot a v hv) =
      adjustedRoot hroot a v hv :=
  (hroot a v hv).choose_spec.2

private noncomputable def weightedNextState
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) {s : HistoricalState hζ}
    (hroot : RealUnitRootNormalization hζ)
    (d : WeightedReductionData hζ s)
    (v : (𝓞 K)ˣ) (hv : d.epsilon₁ / d.epsilon₂ = v ^ p) :
    HistoricalState hζ :=
  let w := adjustedRoot hroot (d.epsilon₁ / d.epsilon₂) v hv
  { omega := w * d.x
    theta := d.y
    xi := d.z
    eta := d.epsilon₃ / d.epsilon₂
    m := 2 * s.m - 1
    one_lt_m := by
      have hm := s.one_lt_m
      omega
    xi_ne_zero := d.z_ne_zero
    coprime_omega_theta :=
      (isCoprime_mul_unit_left_left w.isUnit d.x d.y).mpr d.coprime_xy
    coprime_theta_xi := d.coprime_yz
    coprime_omega_xi :=
      (isCoprime_mul_unit_left_left w.isUnit d.x d.z).mpr d.coprime_xz
    equation := by
      rw [mul_pow, ← Units.val_pow_eq_pow_val,
        ← adjustedRoot_pow hroot (d.epsilon₁ / d.epsilon₂) v hv,
        ← mul_right_inj' d.epsilon₂.isUnit.ne_zero, mul_add, ← mul_assoc,
        ← Units.val_mul, mul_div_cancel, ← mul_assoc,
        ← Units.val_mul, mul_div_cancel]
      exact d.weightedEquation }

private lemma weightedNextState_admissible
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) {s : HistoricalState hζ}
    (hroot : RealUnitRootNormalization hζ)
    (d : WeightedReductionData hζ s)
    (v : (𝓞 K)ˣ) (hv : d.epsilon₁ / d.epsilon₂ = v ^ p) :
    RealSourceAdmissible hζ (weightedNextState hζ hroot d v hv) := by
  let w := adjustedRoot hroot (d.epsilon₁ / d.epsilon₂) v hv
  have hwUnits : NumberField.IsCMField.unitsComplexConj K w = w :=
    adjustedRoot_real hroot (d.epsilon₁ / d.epsilon₂) v hv
  have hw : NumberField.IsCMField.ringOfIntegersComplexConj K (w : 𝓞 K) = w := by
    have h := congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) hwUnits
    exact h
  refine ⟨?_, d.real_y, d.real_z, d.real_eta⟩
  change NumberField.IsCMField.ringOfIntegersComplexConj K
      ((w : 𝓞 K) * d.x) = (w : 𝓞 K) * d.x
  rw [map_mul, hw, d.real_x]

/-- Equations (10) and (10a) imply the abstract historical reduction data.
The finite elimination and the real-root normalization are explicit inputs;
the construction of the successor state and the strict measure decrease are
proved once here for every prime. -/
noncomputable def equationSevenToTenData_of_weighted
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) {s : HistoricalState hζ}
    (hroot : RealUnitRootNormalization hζ)
    (d : WeightedReductionData hζ s) :
    EquationSevenToTenData hζ (RealSourceAdmissible hζ) s where
  quotientUnit := d.epsilon₁ / d.epsilon₂
  rationalBase := d.rationalBase
  highCongruence := d.highCongruence
  nextState := weightedNextState hζ hroot d
  next_admissible := weightedNextState_admissible hζ hroot d
  next_exponent := by intros; rfl
  factorCount_decreases := by
    intro v hv
    exact Finset.card_lt_card d.factorSupport_strict

/-- The source-faithful finite elimination boundary.  A prime-specific
implementation must construct the exact conjugation-power data for every
admissible historical state. -/
def RealPrincipalGeneratorElimination {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) : Prop :=
  ∀ s : HistoricalState hζ, RealSourceAdmissible hζ s →
    Nonempty (ConjugationPowerReductionData hζ s)

/-- A concrete generator normalizer, real-unit-root normalization, and
finite elimination package supply the full reduction relation required by
the well-founded historical descent. -/
theorem equationsSevenToTenReduction
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (normalizer : RealGeneratorNormalizer hζ)
    (hroot : RealUnitRootNormalization hζ)
    (heliminate : RealPrincipalGeneratorElimination hζ) :
    EquationsSevenToTenReduction hζ (RealSourceAdmissible hζ) := by
  intro s hs
  exact (heliminate s hs).map fun d ↦
    equationSevenToTenData_of_weighted hζ hroot
      (weightedReductionData_of_conjugationPowers hζ normalizer d)

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
