import Fermat.Irregular.VandiverHistoricalDescent
import Fermat.Irregular.CircularUnitIndex
import Fermat.ThirtySeven.DirectVandiverData
import Fermat.ThirtySeven.SinnottKummer
import FltRegular.NumberTheory.Cyclotomic.MoreLemmas

/-!
# Vandiver's historical descent at exponent 37

This file instantiates the source-faithful historical descent with the
concrete real-subfield invariant at exponent `37`. It first proves the
passage from a primitive rational second-case solution to Vandiver's
equation (6), using

`37 ~ (1 - ζ) ^ 36 ~ ((1 - ζ) * (1 - ζ⁻¹)) ^ 18`.

The subsequent sections expose the actual algebraic data in equations
(7b)--(10), reusing the repository's ideal-principalization interface and
leaving only the smallest unavailable real-ideal descent lemma explicit.
-/

namespace Fermat.ThirtySeven.VandiverHistorical

open scoped NumberField nonZeroDivisors

open Fermat.Irregular.VandiverHistoricalDescent
open Fermat.Irregular.VandiverCriterion

noncomputable section

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {37} ℚ K]

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 37) K (by norm_num)

/-- The concrete source invariant: all three entries and the coefficient
unit lie in the maximal real subfield. The remaining equation, nonvanishing,
and pairwise-coprimality conditions are fields of `HistoricalState` itself. -/
def RealSourceAdmissible {ζ : K} (hζ : IsPrimitiveRoot ζ 37) :
    HistoricalAdmissibility hζ :=
  fun s ↦
    NumberField.IsCMField.ringOfIntegersComplexConj K s.omega = s.omega ∧
    NumberField.IsCMField.ringOfIntegersComplexConj K s.theta = s.theta ∧
    NumberField.IsCMField.ringOfIntegersComplexConj K s.xi = s.xi ∧
    NumberField.IsCMField.unitsComplexConj K s.eta = s.eta

/-- Vandiver's `κ = (1 - ζ)(1 - ζ⁻¹)` is fixed by complex
conjugation. -/
lemma ringOfIntegersComplexConj_kappa {ζ : K}
    (hζ : IsPrimitiveRoot ζ 37) :
    NumberField.IsCMField.ringOfIntegersComplexConj K (kappa hζ) =
      kappa hζ := by
  apply NumberField.RingOfIntegers.ext
  change NumberField.IsCMField.complexConj K
      (((kappa hζ : 𝓞 K) : K)) = ((kappa hζ : 𝓞 K) : K)
  simp only [kappa, map_mul, map_sub, map_one]
  change (1 - NumberField.IsCMField.complexConj K ζ) *
      (1 - NumberField.IsCMField.complexConj K ζ⁻¹) =
    (1 - ζ) * (1 - ζ⁻¹)
  rw [Fermat.Irregular.CircularUnitIndex.complexConj_zeta37_inv hζ]
  simp only [map_inv₀]
  rw [Fermat.Irregular.CircularUnitIndex.complexConj_zeta37_inv hζ, inv_inv]
  ring

/-- Complex conjugation sends the integral unit attached to `ζ` to its
inverse. -/
lemma unitsComplexConj_zeta37 {ζ : K} (hζ : IsPrimitiveRoot ζ 37) :
    NumberField.IsCMField.unitsComplexConj K hζ.unit' = (hζ.unit')⁻¹ := by
  apply Units.ext
  apply NumberField.RingOfIntegers.ext
  change NumberField.IsCMField.complexConj K ζ = ζ⁻¹
  exact Fermat.Irregular.CircularUnitIndex.complexConj_zeta37_inv hζ

/-! ## Conjugation-compatible principal generators -/

/-! ### The exact plus/minus ideal-class split

The plus-class-number result does **not** by itself prove
`RelevantIdealQuotientsPrincipal` at the irregular prime `37`: a genuine
`37`-torsion minus class may remain.  The definitions and theorems below
make that obstruction literal.  For a relevant quotient `I`, its symmetric
component is `I * conj(I)` and its antisymmetric component is
`I / conj(I)`.  Since `I ^ 37` is already principal, once the symmetric
component is principal, principalizing `I` is equivalent to principalizing
the antisymmetric component.

This is the precise interface between the Sinnott--Kummer plus-class theorem
and Kummer's primary test on the remaining irregular minus component. -/

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- The exact class-group consequence of the exponent-`37`
Sinnott--Kummer theorem used by Vandiver in (7b) and again after (9): a
fractional ideal of the maximal real field whose `37`th power is principal
is already principal.

The fact that a particular conjugation-invariant ideal of `K` is the
extension of such a real ideal is a separate descent-of-ideals statement;
keeping the two steps separate prevents the plus-class computation from
being misapplied to an arbitrary ideal of the CM field. -/
theorem realFractionalIdeal_isPrincipal_of_pow37
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 37)
    (I : FractionalIdeal (𝓞 K⁺)⁰ K⁺)
    (hpow : Submodule.IsPrincipal
      ((I ^ 37 : FractionalIdeal (𝓞 K⁺)⁰ K⁺) :
        Submodule (𝓞 K⁺) K⁺)) :
    Submodule.IsPrincipal (I : Submodule (𝓞 K⁺) K⁺) := by
  exact fractionalIdeal_isPrincipal_of_pow_of_not_dvd_classNumber
    (by norm_num) (Fermat.ThirtySeven.SinnottKummer.not_dvd_classNumber hzeta)
    I hpow

set_option maxRecDepth 2000 in
/-- Element-level form of the same real-class calculation.  This is the
literal conclusion used in Vandiver's (7d) and after (9): if a real ideal
has `37`th power `(a)`, then it has a real generator `ρ`, and `a` differs
from `ρ ^ 37` by a real unit. -/
theorem exists_real_unit_mul_pow_generator37
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 37)
    (I : Ideal (𝓞 K⁺)) (a : 𝓞 K⁺)
    (hpow : I ^ 37 = Ideal.span {a}) :
    ∃ (ρ : 𝓞 K⁺) (ε : (𝓞 K⁺)ˣ),
      I = Ideal.span {ρ} ∧ a = ε * ρ ^ 37 := by
  exact exists_unit_mul_pow_eq_of_ideal_pow_eq_span
    (F := K⁺) (p := 37) (by norm_num)
    (Fermat.ThirtySeven.SinnottKummer.not_dvd_classNumber hzeta) I a hpow

set_option maxRecDepth 2000 in
/-- Vandiver's real-ideal step in the relative-norm form naturally
produced by (7b).  If `J ^ 37 = (a)` in the cyclotomic ring, multiplicativity
of the relative ideal norm gives

`Norm(J) ^ 37 = (intNorm(a))`

in the maximal real ring.  The unconditional result `37 ∤ h⁺` then
provides a real generator `ρ` and a real unit `ε` with
`intNorm(a) = ε * ρ ^ 37`.

This packages the class-number argument in (7b) without any general
descent theorem for conjugation-stable ideals. -/
theorem exists_realGenerator_of_relativeNorm37
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 37)
    (J : Ideal (𝓞 K)) (a : 𝓞 K)
    (hpow : J ^ 37 = Ideal.span {a}) :
    ∃ (ρ : 𝓞 K⁺) (ε : (𝓞 K⁺)ˣ),
      Ideal.relNorm (𝓞 K⁺) J = Ideal.span {ρ} ∧
      Algebra.intNorm (𝓞 K⁺) (𝓞 K) a = ε * ρ ^ 37 := by
  apply exists_real_unit_mul_pow_generator37 hzeta
    (Ideal.relNorm (𝓞 K⁺) J) (Algebra.intNorm (𝓞 K⁺) (𝓞 K) a)
  calc
    Ideal.relNorm (𝓞 K⁺) J ^ 37 =
        Ideal.relNorm (𝓞 K⁺) (J ^ 37) := by
      rw [map_pow]
    _ = Ideal.relNorm (𝓞 K⁺) (Ideal.span {a}) := by rw [hpow]
    _ = Ideal.span {Algebra.intNorm (𝓞 K⁺) (𝓞 K) a} :=
      Ideal.relNorm_singleton (𝓞 K⁺) a

/-- In the quadratic CM extension, the integral norm of a cyclotomic
integer is the product of that integer and its complex conjugate.

The proof makes the two automorphisms literal: the Galois group over the
maximal real field has cardinality two, and its elements are the identity
and `complexConj`. -/
theorem algebraMap_intNorm_eq_mul_conj37 (a : 𝓞 K) :
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

set_option maxRecDepth 2000 in
/-- Vandiver's equation (7d), derived directly from the ideal-power
factorization preceding (7b).

If `J ^ 37 = (a)`, relative ideal norm and `37 ∤ h⁺` produce a real
generator `ρ` and real unit `ε`; the quadratic norm identity above then
gives the exact cyclotomic-ring equation

`a * conj(a) = ε * ρ ^ 37`.

This is the complete class-number step of (7b)--(7d). -/
theorem exists_equationSevenD_of_idealPower37
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 37)
    (J : Ideal (𝓞 K)) (a : 𝓞 K)
    (hpow : J ^ 37 = Ideal.span {a}) :
    ∃ (ρ : 𝓞 K⁺) (ε : (𝓞 K⁺)ˣ),
      Ideal.relNorm (𝓞 K⁺) J = Ideal.span {ρ} ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K
          (algebraMap (𝓞 K⁺) (𝓞 K) ρ) =
        algebraMap (𝓞 K⁺) (𝓞 K) ρ ∧
      a * NumberField.IsCMField.ringOfIntegersComplexConj K a =
        algebraMap (𝓞 K⁺) (𝓞 K) (ε : 𝓞 K⁺) *
          algebraMap (𝓞 K⁺) (𝓞 K) ρ ^ 37 := by
  obtain ⟨ρ, ε, hI, ha⟩ :=
    exists_realGenerator_of_relativeNorm37 hzeta J a hpow
  refine ⟨ρ, ε, hI,
    (NumberField.IsCMField.ringOfIntegersComplexConj K).commutes ρ, ?_⟩
  rw [← algebraMap_intNorm_eq_mul_conj37]
  simpa only [map_mul, map_pow] using
    congrArg (algebraMap (𝓞 K⁺) (𝓞 K)) ha

/-- The conjugate of an integral ideal under CM complex conjugation. -/
def conjugateIdeal37 (I : Ideal (𝓞 K)) : Ideal (𝓞 K) :=
  I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingHom

/-- Extension of an ideal of the maximal real field to the full
cyclotomic ring. -/
def extendRealIdeal37 (I : Ideal (𝓞 K⁺)) : Ideal (𝓞 K) :=
  I.map (algebraMap (𝓞 K⁺) (𝓞 K))

/-- An extended real ideal is fixed by CM complex conjugation. -/
@[simp] theorem conjugateIdeal37_extendRealIdeal37
    (I : Ideal (𝓞 K⁺)) :
    conjugateIdeal37 (extendRealIdeal37 I) = extendRealIdeal37 I := by
  rw [conjugateIdeal37, extendRealIdeal37, Ideal.map_map]
  have hmap :
      (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingHom.comp
          (algebraMap (𝓞 K⁺) (𝓞 K)) =
        algebraMap (𝓞 K⁺) (𝓞 K) := by
    ext x
    exact congrArg ((↑) : 𝓞 K → K)
      ((NumberField.IsCMField.ringOfIntegersComplexConj K).commutes x)
  rw [hmap]

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K] in
/-- Extending a real principal ideal preserves its displayed generator. -/
theorem extendRealIdeal37_span (ρ : 𝓞 K⁺) :
    extendRealIdeal37 (Ideal.span {ρ}) =
      Ideal.span {algebraMap (𝓞 K⁺) (𝓞 K) ρ} := by
  simp only [extendRealIdeal37, Ideal.map_span, Set.image_singleton]

omit [IsCyclotomicExtension {37} ℚ K] in
/-- Extension from the real ring of integers is injective on ideals.  This
is faithful flatness for the finite integral extension
`𝓞 K⁺ → 𝓞 K`. -/
theorem extendRealIdeal37_injective :
    Function.Injective (extendRealIdeal37 (K := K)) := by
  intro I J hIJ
  have hcomap := congrArg
    (Ideal.comap (algebraMap (𝓞 K⁺) (𝓞 K))) hIJ
  simpa only [extendRealIdeal37,
    Ideal.comap_map_eq_self_of_faithfullyFlat] using hcomap

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K] in
/-- Extension commutes with ideal powers. -/
theorem extendRealIdeal37_pow (I : Ideal (𝓞 K⁺)) (n : ℕ) :
    extendRealIdeal37 (I ^ n) = extendRealIdeal37 I ^ n := by
  exact Ideal.map_pow (algebraMap (𝓞 K⁺) (𝓞 K)) I n

set_option maxRecDepth 2000 in
/-- The complete plus-class-number bridge needed at each of Vandiver's
real ideals in (7b) and (9).  A real ideal with 37th power `(a)` extends to
a conjugation-stable principal ideal of the cyclotomic ring, generated by
the image of a real integer `ρ`; the displayed element `a` is a real unit
times `ρ ^ 37`.

Thus a future construction only has to prove that its invariant ideal is
the extension of `I` and verify the 37th-power equality `hpow`; all class
number and generator extraction work is discharged here. -/
theorem exists_extendedRealGenerator37
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 37)
    (I : Ideal (𝓞 K⁺)) (a : 𝓞 K⁺)
    (hpow : I ^ 37 = Ideal.span {a}) :
    ∃ (ρ : 𝓞 K⁺) (ε : (𝓞 K⁺)ˣ),
      extendRealIdeal37 I =
          Ideal.span {algebraMap (𝓞 K⁺) (𝓞 K) ρ} ∧
      conjugateIdeal37 (extendRealIdeal37 I) = extendRealIdeal37 I ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K
          (algebraMap (𝓞 K⁺) (𝓞 K) ρ) =
        algebraMap (𝓞 K⁺) (𝓞 K) ρ ∧
      algebraMap (𝓞 K⁺) (𝓞 K) a =
        algebraMap (𝓞 K⁺) (𝓞 K) (ε : 𝓞 K⁺) *
          algebraMap (𝓞 K⁺) (𝓞 K) ρ ^ 37 := by
  obtain ⟨ρ, ε, hI, ha⟩ := exists_real_unit_mul_pow_generator37 hzeta I a hpow
  refine ⟨ρ, ε, ?_, conjugateIdeal37_extendRealIdeal37 I,
    (NumberField.IsCMField.ringOfIntegersComplexConj K).commutes ρ, ?_⟩
  · rw [hI, extendRealIdeal37_span]
  · rw [ha, map_mul, map_pow]

set_option maxRecDepth 2000 in
/-- Version of `exists_extendedRealGenerator37` whose 37th-power identity
is proved after extension to the cyclotomic ring, as it is in Vandiver's
factorizations (7b) and (9).  Faithful flatness reflects that identity back
to the real ideal, where `37 ∤ h⁺` supplies the generator. -/
theorem exists_extendedRealGenerator37_of_pow_eq_span
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 37)
    (I : Ideal (𝓞 K⁺)) (a : 𝓞 K⁺)
    (hpow : extendRealIdeal37 I ^ 37 =
      Ideal.span {algebraMap (𝓞 K⁺) (𝓞 K) a}) :
    ∃ (ρ : 𝓞 K⁺) (ε : (𝓞 K⁺)ˣ),
      extendRealIdeal37 I =
          Ideal.span {algebraMap (𝓞 K⁺) (𝓞 K) ρ} ∧
      conjugateIdeal37 (extendRealIdeal37 I) = extendRealIdeal37 I ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K
          (algebraMap (𝓞 K⁺) (𝓞 K) ρ) =
        algebraMap (𝓞 K⁺) (𝓞 K) ρ ∧
      algebraMap (𝓞 K⁺) (𝓞 K) a =
        algebraMap (𝓞 K⁺) (𝓞 K) (ε : 𝓞 K⁺) *
          algebraMap (𝓞 K⁺) (𝓞 K) ρ ^ 37 := by
  apply exists_extendedRealGenerator37 hzeta I a
  apply extendRealIdeal37_injective (K := K)
  rw [extendRealIdeal37_pow, extendRealIdeal37_span]
  exact hpow

/-- Complex conjugation preserves whether an integral ideal is zero. -/
@[simp] lemma conjugateIdeal37_eq_zero_iff (I : Ideal (𝓞 K)) :
    conjugateIdeal37 I = 0 ↔ I = 0 := by
  exact Ideal.map_eq_bot_iff_of_injective
    (NumberField.IsCMField.ringOfIntegersComplexConj K).injective

/-- Conjugate an integral-ideal quotient by conjugating numerator and
denominator. -/
def conjugateIdealQuotient37 (A B : Ideal (𝓞 K)) :
    FractionalIdeal (𝓞 K)⁰ K :=
  (conjugateIdeal37 A : FractionalIdeal (𝓞 K)⁰ K) /
    (conjugateIdeal37 B : FractionalIdeal (𝓞 K)⁰ K)

/-- The actual fractional ideal whose principality is requested by
`RelevantIdealQuotientsPrincipal` at exponent `37`. -/
noncomputable def relevantIdealQuotient37
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    {x y z : 𝓞 K} {ε₀ : (𝓞 K)ˣ} {m : ℕ}
    (e : x ^ 37 + y ^ 37 =
      ε₀ * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ 37)
    (hy : ¬ hζ.unit'.1 - 1 ∣ y)
    (η : Polynomial.nthRootsFinset 37 (1 : 𝓞 K)) :
    FractionalIdeal (𝓞 K)⁰ K :=
  (root_div_zeta_sub_one_dvd_gcd (K := K) (p := 37)
      (x := x) (y := y) (z := z) (ε := ε₀) (m := m)
        (by norm_num) hζ e hy η : FractionalIdeal (𝓞 K)⁰ K) /
    (a_eta_zero_dvd_p_pow (K := K) (p := 37)
      (x := x) (y := y) (z := z) (ε := ε₀) (m := m)
        (by norm_num) hζ e hy : FractionalIdeal (𝓞 K)⁰ K)

/-- The conjugate of the relevant exponent-`37` quotient. -/
noncomputable def conjugateRelevantIdealQuotient37
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    {x y z : 𝓞 K} {ε₀ : (𝓞 K)ˣ} {m : ℕ}
    (e : x ^ 37 + y ^ 37 =
      ε₀ * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ 37)
    (hy : ¬ hζ.unit'.1 - 1 ∣ y)
    (η : Polynomial.nthRootsFinset 37 (1 : 𝓞 K)) :
    FractionalIdeal (𝓞 K)⁰ K :=
  conjugateIdealQuotient37
    (root_div_zeta_sub_one_dvd_gcd (K := K) (p := 37)
      (x := x) (y := y) (z := z) (ε := ε₀) (m := m)
        (by norm_num) hζ e hy η)
    (a_eta_zero_dvd_p_pow (K := K) (p := 37)
      (x := x) (y := y) (z := z) (ε := ε₀) (m := m)
        (by norm_num) hζ e hy)

/-- Every symmetric relevant quotient class is principal.  This is the
ideal-theoretic plus-component statement to be supplied by the plus class
number through relative ideal norm and extension. -/
def RelevantIdealQuotientPlusComponentsPrincipal37 : Prop :=
  ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    {x y z : 𝓞 K} {ε₀ : (𝓞 K)ˣ} {m : ℕ}
    (e : x ^ 37 + y ^ 37 =
      ε₀ * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ 37)
    (hy : ¬ hζ.unit'.1 - 1 ∣ y)
    (η : Polynomial.nthRootsFinset 37 (1 : 𝓞 K)),
    Submodule.IsPrincipal
      (((relevantIdealQuotient37 hζ e hy η *
          conjugateRelevantIdealQuotient37 hζ e hy η) :
        FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)

/-- Every antisymmetric relevant quotient class is principal.  At `37`,
this is exactly the residual minus-component assertion that cannot follow
from `37 ∤ h⁺` alone. -/
def RelevantIdealQuotientMinusComponentsPrincipal37 : Prop :=
  ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    {x y z : 𝓞 K} {ε₀ : (𝓞 K)ˣ} {m : ℕ}
    (e : x ^ 37 + y ^ 37 =
      ε₀ * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ 37)
    (hy : ¬ hζ.unit'.1 - 1 ∣ y)
    (η : Polynomial.nthRootsFinset 37 (1 : 𝓞 K)),
    Submodule.IsPrincipal
      (((relevantIdealQuotient37 hζ e hy η /
          conjugateRelevantIdealQuotient37 hζ e hy η) :
        FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)

section RelevantIdealMinusComponent

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
  {x y z : 𝓞 K} {ε₀ : (𝓞 K)ˣ} {m : ℕ}
  (e : x ^ 37 + y ^ 37 =
    ε₀ * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ 37)
  (hy : ¬ hζ.unit'.1 - 1 ∣ y)

local notation "𝔞" =>
  root_div_zeta_sub_one_dvd_gcd (K := K) (p := 37)
    (x := x) (y := y) (z := z) (ε := ε₀) (m := m)
      (by norm_num) hζ e hy
local notation "𝔞₀" =>
  a_eta_zero_dvd_p_pow (K := K) (p := 37)
    (x := x) (y := y) (z := z) (ε := ε₀) (m := m)
      (by norm_num) hζ e hy

/-- A relevant quotient is zero exactly when its conjugate is zero. -/
lemma relevantIdealQuotient37_conjugate_eq_zero_iff
    (η : Polynomial.nthRootsFinset 37 (1 : 𝓞 K)) :
    ((𝔞 η / 𝔞₀ : FractionalIdeal (𝓞 K)⁰ K) = 0) ↔
      conjugateIdealQuotient37 (𝔞 η) 𝔞₀ = 0 := by
  simp only [conjugateIdealQuotient37, div_eq_mul_inv,
    mul_eq_zero, inv_eq_zero, FractionalIdeal.coeIdeal_eq_zero]
  constructor <;> rintro (h | h)
  · exact Or.inl ((conjugateIdeal37_eq_zero_iff _).mpr h)
  · exact Or.inr ((conjugateIdeal37_eq_zero_iff _).mpr h)
  · exact Or.inl ((conjugateIdeal37_eq_zero_iff _).mp h)
  · exact Or.inr ((conjugateIdeal37_eq_zero_iff _).mp h)

/-- After the symmetric plus component is principal, the original relevant
quotient is principal exactly when its antisymmetric minus component is.

The proof uses the unconditional fact that the quotient's `37`th power is
principal and the coprimality of `37` and `2`. -/
lemma relevantIdealQuotient37_isPrincipal_iff_minus
    (η : Polynomial.nthRootsFinset 37 (1 : 𝓞 K))
    (hplus : Submodule.IsPrincipal
      ((((𝔞 η / 𝔞₀ : FractionalIdeal (𝓞 K)⁰ K) *
          conjugateIdealQuotient37 (𝔞 η) 𝔞₀) :
        FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
    Submodule.IsPrincipal
        ((𝔞 η / 𝔞₀ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ↔
      Submodule.IsPrincipal
        (((𝔞 η / 𝔞₀ : FractionalIdeal (𝓞 K)⁰ K) /
            conjugateIdealQuotient37 (𝔞 η) 𝔞₀ :
          FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
  let I : FractionalIdeal (𝓞 K)⁰ K :=
    (𝔞 η : FractionalIdeal (𝓞 K)⁰ K) /
      (𝔞₀ : FractionalIdeal (𝓞 K)⁰ K)
  let J : FractionalIdeal (𝓞 K)⁰ K :=
    conjugateIdealQuotient37 (𝔞 η) 𝔞₀
  have hzero : I = 0 ↔ J = 0 :=
    relevantIdealQuotient37_conjugate_eq_zero_iff hζ e hy η
  change Submodule.IsPrincipal (I : Submodule (𝓞 K) K) ↔
    Submodule.IsPrincipal
      ((I / J : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
  by_cases hI0 : I = 0
  · have hJ0 : J = 0 := hzero.mp hI0
    rw [hI0, hJ0]
    simp only [zero_div, FractionalIdeal.coe_zero]
  · have hJ0 : J ≠ 0 := fun h ↦ hI0 (hzero.mpr h)
    apply fractionalIdeal_isPrincipal_iff_minus_of_plus (p := 37)
      (by norm_num) hI0 hJ0
    · exact relevantIdealQuotient_pow_isPrincipal
        (K := K) (p := 37) (by norm_num) hζ e hy η
    · exact hplus

end RelevantIdealMinusComponent

/-- Provided the symmetric plus components are principal, the old broad
principalization interface is equivalent—not merely implied—to eliminating
the explicit antisymmetric minus components. -/
theorem relevantIdealQuotientsPrincipal_iff_minus_of_plus37
    (hplus : RelevantIdealQuotientPlusComponentsPrincipal37 (K := K)) :
    RelevantIdealQuotientsPrincipal (K := K) (p := 37) (by norm_num) ↔
      RelevantIdealQuotientMinusComponentsPrincipal37 (K := K) := by
  constructor
  · intro hprincipal ζ hζ x y z ε₀ m e hy η
    have hI := hprincipal hζ e hy η
    have hiff := relevantIdealQuotient37_isPrincipal_iff_minus hζ e hy η
      (hplus hζ e hy η)
    simpa only [relevantIdealQuotient37,
      conjugateRelevantIdealQuotient37] using hiff.mp hI
  · intro hminus ζ hζ x y z ε₀ m e hy η
    have hiff := relevantIdealQuotient37_isPrincipal_iff_minus hζ e hy η
      (hplus hζ e hy η)
    apply hiff.mpr
    simpa only [relevantIdealQuotient37,
      conjugateRelevantIdealQuotient37] using hminus hζ e hy η

/-! ### Stable principal ideals have cyclotomic conjugation quotients -/

section StablePrincipalGenerator

open NumberField NumberField.IsCMField

/-- Complex conjugation acts trivially modulo the prime `(ζ - 1)` on every
cyclotomic integer.  The proof compares the power-basis expansions at `ζ`
and `ζ⁻¹`; both roots reduce to `1`. -/
lemma ringOfIntegersComplexConj_eq_mod_zeta_sub_one37
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37) (a : 𝓞 K) :
    Ideal.Quotient.mk
        (Ideal.span ({(hζ.unit' : 𝓞 K) - 1} : Set (𝓞 K)))
        (ringOfIntegersComplexConj K a) =
      Ideal.Quotient.mk
        (Ideal.span ({(hζ.unit' : 𝓞 K) - 1} : Set (𝓞 K))) a := by
  have ha := hζ.integralPowerBasis.basis.sum_repr a
  let c := hζ.integralPowerBasis.basis.repr
  let φn := hζ.integralPowerBasis.dim
  simp_rw [PowerBasis.basis_eq_pow,
    IsPrimitiveRoot.integralPowerBasis_gen] at ha
  have ha' := congrArg (ringOfIntegersComplexConj K) ha
  replace ha' : ∑ x : Fin φn, (c a) x • ringOfIntegersComplexConj K
      (⟨ζ, hζ.isIntegral (by norm_num)⟩ ^ (x : ℕ)) =
        ringOfIntegersComplexConj K a := by
    refine Eq.trans ?_ ha'
    rw [map_sum]
    congr 1
    ext x
    congr 1
    rw [map_zsmul]
  have hpow : ∀ x : Fin φn,
      ringOfIntegersComplexConj K
          (⟨ζ, hζ.isIntegral (by norm_num)⟩ ^ (x : ℕ)) =
        ⟨ζ⁻¹, hζ.inv.isIntegral (by norm_num)⟩ ^ (x : ℕ) := by
    intro x
    ext
    change complexConj K (ζ ^ (x : ℕ)) = (ζ⁻¹) ^ (x : ℕ)
    rw [map_pow,
      Fermat.Irregular.CircularUnitIndex.complexConj_zeta37_inv hζ]
  conv_lhs at ha' =>
    congr
    congr
    ext x
    rw [hpow x]
  have hconj := aux hζ hζ.inv ha'
  have horig := aux hζ hζ ha
  exact hconj.trans horig.symm

/-- Conjugating a principal integral ideal conjugates its generator. -/
lemma conjugateIdeal37_span (a : 𝓞 K) :
    conjugateIdeal37 (Ideal.span {a}) =
      Ideal.span {ringOfIntegersComplexConj K a} := by
  simp only [conjugateIdeal37, Ideal.map_span, Set.image_singleton]
  rfl

/-- A generator prime to `(ζ - 1)` of a conjugation-stable principal ideal
has conjugation quotient exactly `ζ ^ j`.

Stability first gives an arbitrary unit quotient `v`.  Applying conjugation
twice shows `conj(v) = v⁻¹`; the CM unit theorem then gives
`v = ±ζ^j`.  Since conjugation is the identity modulo `(ζ - 1)` and the
generator is nonzero in that quotient, `v ≡ 1`; this rules out `-ζ^j`
because `2 ∉ (ζ - 1)`. -/
lemma conjugation_eq_zeta_pow_of_stable_principal37
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37) (a : 𝓞 K)
    (ha : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ a)
    (hstable : conjugateIdeal37 (Ideal.span {a}) = Ideal.span {a}) :
    ∃ j : ℕ, ringOfIntegersComplexConj K a =
      (hζ.unit' ^ j : (𝓞 K)ˣ) * a := by
  have hassoc : Associated (ringOfIntegersComplexConj K a) a := by
    rw [← Ideal.span_singleton_eq_span_singleton]
    rw [← conjugateIdeal37_span]
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
          ringOfIntegersComplexConj K a * u * (u⁻¹ : (𝓞 K)ˣ) := by simp
      _ = (u⁻¹ : (𝓞 K)ˣ) * a := by rw [hu]; ac_rfl
  have hvconj : unitsComplexConj K v = v⁻¹ := by
    have hc := congrArg (ringOfIntegersComplexConj K) hv
    rw [map_mul] at hc
    have hcc : ringOfIntegersComplexConj K
        (ringOfIntegersComplexConj K a) = a := by
      ext
      exact complexConj_apply_apply K a
    rw [hcc] at hc
    rw [hv] at hc
    have hnorm : unitsComplexConj K v * v = 1 := by
      apply Units.ext
      change ringOfIntegersComplexConj K (v : 𝓞 K) * (v : 𝓞 K) = 1
      apply mul_right_cancel₀ ha0
      calc
        (ringOfIntegersComplexConj K (v : 𝓞 K) * (v : 𝓞 K)) * a =
            ringOfIntegersComplexConj K (v : 𝓞 K) *
              ((v : 𝓞 K) * a) := by rw [mul_assoc]
        _ = a := hc.symm
        _ = (1 : 𝓞 K) * a := by simp
    exact mul_eq_one_iff_eq_inv.mp hnorm
  obtain ⟨j, hj⟩ := unit_inv_conj_is_root_of_unity hζ v (by norm_num)
  have hv_sq : v ^ 2 = (hζ.unit' ^ j) ^ 2 := by
    simpa only [hvconj, inv_inv, pow_two] using hj
  rcases Units.eq_or_eq_neg_of_sq_eq_sq v (hζ.unit' ^ j) hv_sq with hjv | hjv
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
        algebraMap (𝓞 K) Q (v : 𝓞 K) * algebraMap (𝓞 K) Q a =
            algebraMap (𝓞 K) Q ((v : 𝓞 K) * a) := by rw [map_mul]
        _ = algebraMap (𝓞 K) Q (ringOfIntegersComplexConj K a) := by
          rw [hv]
        _ = algebraMap (𝓞 K) Q a :=
          ringOfIntegersComplexConj_eq_mod_zeta_sub_one37 hζ a
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
          change -(algebraMap (𝓞 K) Q (hζ.unit' : 𝓞 K)) ^ j = -1
          rw [eq_one_mod_one_sub, one_pow]
    apply hζ.two_not_mem_one_sub_zeta (by norm_num)
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat,
      ← neg_one_eq_one_iff_two_eq_zero]
    exact hneg.symm

/-- A conjugation-stable principal ideal prime to `(ζ - 1)` admits a
generator, still prime to `(ζ - 1)`, together with the exact cyclotomic
conjugation exponent required by `ConjugationPowerReductionData37`. -/
lemma exists_conjugation_power_generator37
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37) (I : Ideal (𝓞 K))
    (hprincipal : Submodule.IsPrincipal
      (I : Submodule (𝓞 K) (𝓞 K)))
    (hprime : ¬ Ideal.span
      ({(hζ.unit' : 𝓞 K) - 1} : Set (𝓞 K)) ∣ I)
    (hstable : conjugateIdeal37 I = I) :
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
  have hstableA : conjugateIdeal37 (Ideal.span {a}) =
      Ideal.span {a} := by
    rw [← haI]
    exact hstable
  obtain ⟨j, hj⟩ := conjugation_eq_zeta_pow_of_stable_principal37
    hζ a ha hstableA
  exact ⟨a, j, haI, ha, hj⟩

end StablePrincipalGenerator

/-- The inverse of 2 modulo 37, used to make a generator real. -/
def realGeneratorHalfExponent37 : ℕ := 19

theorem two_mul_realGeneratorHalfExponent37_mod :
    2 * realGeneratorHalfExponent37 % 37 = 1 := by
  decide

/-- The explicit adjustment of a principal generator by the half-power of
its cyclotomic conjugation quotient. -/
def realAdjustedGenerator37 {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    (a : 𝓞 K) (j : ℕ) : 𝓞 K :=
  (hζ.unit' ^ (realGeneratorHalfExponent37 * j) : (𝓞 K)ˣ) * a

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K] in
lemma realAdjustedGenerator37_associated {ζ : K}
    (hζ : IsPrimitiveRoot ζ 37) (a : 𝓞 K) (j : ℕ) :
    Associated (realAdjustedGenerator37 hζ a j) a := by
  let v : (𝓞 K)ˣ := hζ.unit' ^ (realGeneratorHalfExponent37 * j)
  refine ⟨v⁻¹, ?_⟩
  change (v : 𝓞 K) * a * (v⁻¹ : (𝓞 K)ˣ) = a
  calc
    (v : 𝓞 K) * a * (v⁻¹ : (𝓞 K)ˣ) =
        a * ((v : 𝓞 K) * (v⁻¹ : (𝓞 K)ˣ)) := by ac_rfl
    _ = a := by rw [← Units.val_mul]; simp

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K] in
lemma realAdjustedGenerator37_pow_thirtySeven {ζ : K}
    (hζ : IsPrimitiveRoot ζ 37) (a : 𝓞 K) (j : ℕ) :
    realAdjustedGenerator37 hζ a j ^ 37 = a ^ 37 := by
  rw [realAdjustedGenerator37, mul_pow]
  have hzpow : hζ.unit' ^ 37 = 1 := by
    ext
    exact hζ.pow_eq_one
  have hvpow :
      (hζ.unit' ^ (realGeneratorHalfExponent37 * j)) ^ 37 = 1 := by
    rw [← pow_mul]
    rw [show (realGeneratorHalfExponent37 * j) * 37 =
      37 * (realGeneratorHalfExponent37 * j) by omega]
    rw [pow_mul, hzpow, one_pow]
  rw [← Units.val_pow_eq_pow_val, hvpow]
  simp

lemma realAdjustedGenerator37_real
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37) (a : 𝓞 K) (j : ℕ)
    (ha : NumberField.IsCMField.ringOfIntegersComplexConj K a =
      (hζ.unit' ^ j : (𝓞 K)ˣ) * a) :
    NumberField.IsCMField.ringOfIntegersComplexConj K
      (realAdjustedGenerator37 hζ a j) =
        realAdjustedGenerator37 hζ a j := by
  let k := realGeneratorHalfExponent37 * j
  let v : (𝓞 K)ˣ := hζ.unit' ^ k
  have hzpow : hζ.unit' ^ 37 = 1 := by
    ext
    exact hζ.pow_eq_one
  have hv_sq : v ^ 2 = hζ.unit' ^ j := by
    dsimp [v, k, realGeneratorHalfExponent37]
    rw [← pow_mul]
    have hexp : (19 * j) * 2 = j + 37 * j := by omega
    rw [hexp, pow_add, pow_mul, hzpow, one_pow, mul_one]
  change NumberField.IsCMField.ringOfIntegersComplexConj K
      ((v : 𝓞 K) * a) = (v : 𝓞 K) * a
  rw [map_mul]
  have hvconj : NumberField.IsCMField.ringOfIntegersComplexConj K (v : 𝓞 K) =
      (v⁻¹ : (𝓞 K)ˣ) := by
    have hvconjU :
        NumberField.IsCMField.unitsComplexConj K v = v⁻¹ := by
      dsimp [v]
      rw [map_pow, unitsComplexConj_zeta37 hζ, inv_pow]
    exact congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) hvconjU
  rw [hvconj, ha]
  rw [← mul_assoc, ← Units.val_mul, ← hv_sq]
  congr 1
  rw [pow_two, ← mul_assoc]
  simp

/-- If complex conjugation changes a principal generator by a power
ζ ^ j, multiplying the generator by ζ ^ (19 * j) makes it real.

This is the explicit odd-order normalization in the real-generator step
behind Vandiver's equations (7b)--(10a): 19 is the inverse of 2 modulo
37, so

conj (ζ ^ (19*j) * a) = ζ ^ (j-19*j) * a = ζ ^ (19*j) * a.

The resulting generator is associated to the original one, hence generates
the same principal ideal. What remains in
RealPrincipalGeneratorElimination37 is to prove that the conjugation
quotients supplied by the relevant ideal calculation have precisely this
ζ ^ j form and then to carry out Vandiver's eliminations. -/
lemma exists_real_associated_generator_of_conj_eq_zeta_pow
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37) (a : 𝓞 K) (j : ℕ)
    (ha : NumberField.IsCMField.ringOfIntegersComplexConj K a =
      (hζ.unit' ^ j : (𝓞 K)ˣ) * a) :
    ∃ b : 𝓞 K, Associated b a ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K b = b := by
  exact ⟨realAdjustedGenerator37 hζ a j,
    realAdjustedGenerator37_associated hζ a j,
    realAdjustedGenerator37_real hζ a j ha⟩

/-- A `37`th root of a real unit can be adjusted by a power of `ζ`
without changing its `37`th power so that the root itself is real. This is
the real-root normalization used implicitly between Vandiver's equations
(10) and (10b). -/
lemma exists_real_unit_root_37 {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    (a v : (𝓞 K)ˣ)
    (hv : a = v ^ 37) :
    ∃ w : (𝓞 K)ˣ, a = w ^ 37 ∧
      NumberField.IsCMField.unitsComplexConj K w = w := by
  obtain ⟨j, hj⟩ := unit_inv_conj_is_root_of_unity hζ v (by norm_num)
  let w : (𝓞 K)ˣ := v / hζ.unit' ^ j
  refine ⟨w, ?_, ?_⟩
  · dsimp [w]
    rw [div_pow, ← hv]
    have hzpow : hζ.unit' ^ 37 = 1 := by
      ext
      exact hζ.pow_eq_one
    rw [← pow_mul, show j * 37 = 37 * j by omega, pow_mul, hzpow, one_pow,
      div_one]
  · dsimp [w]
    rw [map_div, map_pow, unitsComplexConj_zeta37 hζ]
    rw [← div_eq_mul_inv] at hj
    have hmul : v = (hζ.unit' ^ j) ^ 2 *
        NumberField.IsCMField.unitsComplexConj K v :=
      div_eq_iff_eq_mul.mp hj
    rw [inv_pow, div_inv_eq_mul]
    calc
      NumberField.IsCMField.unitsComplexConj K v * hζ.unit' ^ j =
          (hζ.unit' ^ j) ^ 2 *
              NumberField.IsCMField.unitsComplexConj K v / hζ.unit' ^ j := by
        symm
        rw [pow_two]
        calc
          (hζ.unit' ^ j * hζ.unit' ^ j) *
                NumberField.IsCMField.unitsComplexConj K v / hζ.unit' ^ j =
              (NumberField.IsCMField.unitsComplexConj K v * hζ.unit' ^ j) *
                hζ.unit' ^ j / hζ.unit' ^ j := by ac_rfl
          _ = NumberField.IsCMField.unitsComplexConj K v * hζ.unit' ^ j :=
            mul_div_cancel_right _ _
      _ = v / hζ.unit' ^ j := by rw [← hmul]

/-- At exponent `37`, Vandiver's `κ^18` is associated to the rational
prime `37`. -/
lemma kappa_pow_eighteen_associated_37 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 37) :
    Associated (kappa hζ ^ 18) (37 : 𝓞 K) := by
  have hleft : Associated
      ((1 : 𝓞 K) - hζ.unit') ((hζ.unit' : 𝓞 K) - 1) := by
    refine ⟨-1, ?_⟩
    simp
  have hright : Associated
      ((1 : 𝓞 K) - (hζ.unit')⁻¹) ((hζ.unit' : 𝓞 K) - 1) := by
    refine ⟨hζ.unit', ?_⟩
    simp [sub_mul]
  have hkappa : Associated (kappa hζ)
      (((hζ.unit' : 𝓞 K) - 1) ^ 2) := by
    simpa [kappa, pow_two] using hleft.mul_mul hright
  have hkappaPow := hkappa.pow_pow (n := 18)
  rw [← pow_mul] at hkappaPow
  norm_num at hkappaPow
  have hprime := associated_zeta_sub_one_pow_prime hζ
  norm_num at hprime
  exact hkappaPow.trans hprime

/-- A primitive rational second-case solution at exponent `37` gives
Vandiver's equation (6) with `m = 18`. This discharges the first abstract
boundary of `VandiverHistoricalDescent` for the concrete real invariant. -/
theorem secondCaseStartsHistoricalDescent_37 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 37) :
    SecondCaseStartsHistoricalDescent hζ (RealSourceAdmissible hζ) := by
  intro x y z hgcd hz hz0 e
  have hx : x ≠ 0 := by
    intro hx0
    have hyz : y = z := (show Odd 37 by norm_num).pow_injective (by simpa [hx0] using e)
    have h37one : (37 : ℤ) ∣ 1 := by
      rw [← hgcd, Finset.dvd_gcd_iff]
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · rw [hx0]
        exact dvd_zero _
      · rw [hyz]
        exact hz
      · exact hz
    norm_num at h37one
  have hy : y ≠ 0 := by
    intro hy0
    have hxz : x = z := (show Odd 37 by norm_num).pow_injective (by simpa [hy0] using e)
    have h37one : (37 : ℤ) ∣ 1 := by
      rw [← hgcd, Finset.dvd_gcd_iff]
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · rw [hxz]
        exact hz
      · rw [hy0]
        exact dvd_zero _
      · exact hz
    norm_num at h37one
  obtain ⟨hxy, hyz, hxz⟩ :=
    Fermat.pairwiseCoprime_of_primitive_solution (by norm_num) hx hy hz0 hgcd e
  obtain ⟨t, rfl⟩ := hz
  have ht0 : t ≠ 0 := by
    intro ht
    apply hz0
    simp [ht]
  obtain ⟨u, hu⟩ := kappa_pow_eighteen_associated_37 hζ
  have hkappa0 : kappa hζ ^ 18 ≠ 0 :=
    (kappa_pow_eighteen_associated_37 hζ).ne_zero_iff.mpr (by norm_num)
  have huReal :
      NumberField.IsCMField.ringOfIntegersComplexConj K (u : 𝓞 K) = u := by
    have hconj := congrArg
      (NumberField.IsCMField.ringOfIntegersComplexConj K) hu
    simp only [map_mul, map_pow, ringOfIntegersComplexConj_kappa hζ,
      map_ofNat] at hconj
    exact mul_left_cancel₀ hkappa0 (hconj.trans hu.symm)
  let ξ : 𝓞 K := (u : 𝓞 K) * (t : 𝓞 K)
  have hyt : IsCoprime (y : 𝓞 K) (t : 𝓞 K) := by
    have hcast := hyz.intCast (R := 𝓞 K)
    have hcast' : IsCoprime (y : 𝓞 K) (((37 : ℤ) : 𝓞 K) * (t : 𝓞 K)) := by
      simpa only [Int.cast_mul] using hcast
    exact hcast'.of_mul_right_right
  have hxt : IsCoprime (x : 𝓞 K) (t : 𝓞 K) := by
    have hcast := hxz.intCast (R := 𝓞 K)
    have hcast' : IsCoprime (x : 𝓞 K) (((37 : ℤ) : 𝓞 K) * (t : 𝓞 K)) := by
      simpa only [Int.cast_mul] using hcast
    exact hcast'.of_mul_right_right
  let s : HistoricalState hζ :=
    { omega := x
      theta := y
      xi := ξ
      eta := 1
      m := 18
      one_lt_m := by norm_num
      xi_ne_zero := by
        dsimp [ξ]
        exact mul_ne_zero u.isUnit.ne_zero (Int.cast_ne_zero.mpr ht0)
      coprime_omega_theta := hxy.intCast
      coprime_theta_xi := by
        dsimp [ξ]
        exact (isCoprime_mul_unit_left_right u.isUnit (y : 𝓞 K) (t : 𝓞 K)).mpr hyt
      coprime_omega_xi := by
        dsimp [ξ]
        exact (isCoprime_mul_unit_left_right u.isUnit (x : 𝓞 K) (t : 𝓞 K)).mpr hxt
      equation := by
        simp only [Units.val_one, one_mul]
        calc
          (x : 𝓞 K) ^ 37 + (y : 𝓞 K) ^ 37 =
              ((((37 : ℤ) * t : ℤ) : 𝓞 K)) ^ 37 := by exact_mod_cast e
          _ = ((37 : 𝓞 K) * (t : 𝓞 K)) ^ 37 := by norm_num
          _ = (kappa hζ ^ 18 * ((u : 𝓞 K) * (t : 𝓞 K))) ^ 37 := by
            congr 1
            rw [← mul_assoc, hu]
          _ = (kappa hζ ^ 18 * ξ) ^ 37 := rfl }
  refine ⟨s, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [s]
    simp
  · dsimp [s]
    simp
  · dsimp [s, ξ]
    simp [huReal]
  · dsimp [s]
    simp

/-! ## The algebraic passage from equation (10) to equation (10b) -/

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K] in
/-- Vandiver's elimination in equation (10a), separated from the
ideal-theoretic construction of its inputs.

Writing `S = ω² + θ²` and `T = ωθ`, the three equations immediately
before (10a) have left sides `S + A*T`, `S + B*T`, and `S + 2*T`.
Multiplying the first by `2-B`, the second by `2-A`, and subtracting
eliminates both `S` and `T` against the third equation:

`(2-B)(S+A*T) - (2-A)(S+B*T) = (A-B)(S+2*T)`.

In the paper, `A = ζ^a + ζ⁻ᵃ` and `B = ζ^b + ζ⁻ᵇ`.  The subsequent
cyclotomic-unit simplification turns this identity into equation (10b). -/
lemma equationTenA_quadraticElimination37
    (ω θ A B Ua Ub Uzero Xa Xb Xzero : 𝓞 K)
    (ha : ω ^ 2 + A * (ω * θ) + θ ^ 2 = Ua * Xa ^ 37)
    (hb : ω ^ 2 + B * (ω * θ) + θ ^ 2 = Ub * Xb ^ 37)
    (hzero : ω ^ 2 + 2 * (ω * θ) + θ ^ 2 = Uzero * Xzero) :
    (2 - B) * (Ua * Xa ^ 37) - (2 - A) * (Ub * Xb ^ 37) =
      (A - B) * (Uzero * Xzero) := by
  rw [← ha, ← hb, ← hzero]
  ring

/-- The actual finite support of the distinct prime-ideal factors of the
principal ideal `(x)`. -/
def primeIdealFactorSupport37 (x : 𝓞 K) : Finset (Ideal (𝓞 K)) :=
  (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {x})).toFinset

/-- The concrete output of Vandiver's ideal calculation through equation
(10a), before applying Lemma 2. It records the weighted Fermat equation,
the high-depth quotient-unit congruence, the real and coprimality invariants,
and the strict deletion of a prime-ideal factor from `ξ`.

The theorem below turns exactly this data into the abstract
`EquationSevenToTenData`; in particular, neither the Kummer conclusion nor
the rescaling to equation (10b) is assumed here. -/
structure WeightedReductionData37 {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    (s : HistoricalState hζ) where
  x : 𝓞 K
  y : 𝓞 K
  z : 𝓞 K
  epsilon₁ : (𝓞 K)ˣ
  epsilon₂ : (𝓞 K)ˣ
  epsilon₃ : (𝓞 K)ˣ
  rationalBase : ℤ
  highCongruence :
    ((1 : 𝓞 K) - hζ.unit') ^ ((2 * s.m - 2) * 37) ∣
      (((epsilon₁ / epsilon₂ : (𝓞 K)ˣ) : 𝓞 K) -
        (rationalBase : 𝓞 K) ^ 37)
  weightedEquation :
    epsilon₁ * x ^ 37 + epsilon₂ * y ^ 37 =
      epsilon₃ * (kappa hζ ^ (2 * s.m - 1) * z) ^ 37
  z_ne_zero : z ≠ 0
  coprime_xy : IsCoprime x y
  coprime_yz : IsCoprime y z
  coprime_xz : IsCoprime x z
  real_x : NumberField.IsCMField.ringOfIntegersComplexConj K x = x
  real_y : NumberField.IsCMField.ringOfIntegersComplexConj K y = y
  real_z : NumberField.IsCMField.ringOfIntegersComplexConj K z = z
  real_eta : NumberField.IsCMField.unitsComplexConj K (epsilon₃ / epsilon₂) =
    epsilon₃ / epsilon₂
  factorSupport_strict : primeIdealFactorSupport37 z ⊂ primeIdealFactorSupport37 s.xi

/-- The output of Vandiver's elimination before its three principal
generators have been made literally real.

Compared with WeightedReductionData37, this structure asks for the exact
cyclotomic conjugation quotients of x, y, and z. The theorem
weightedReductionData_of_conjugationPowers37 below performs the explicit
ζ^(19*j) adjustment and proves that it preserves the weighted equation,
coprimality, nonvanishing, and the strict prime-support descent. -/
structure ConjugationPowerReductionData37 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 37) (s : HistoricalState hζ) where
  x : 𝓞 K
  y : 𝓞 K
  z : 𝓞 K
  epsilon₁ : (𝓞 K)ˣ
  epsilon₂ : (𝓞 K)ˣ
  epsilon₃ : (𝓞 K)ˣ
  rationalBase : ℤ
  highCongruence :
    ((1 : 𝓞 K) - hζ.unit') ^ ((2 * s.m - 2) * 37) ∣
      (((epsilon₁ / epsilon₂ : (𝓞 K)ˣ) : 𝓞 K) -
        (rationalBase : 𝓞 K) ^ 37)
  weightedEquation :
    epsilon₁ * x ^ 37 + epsilon₂ * y ^ 37 =
      epsilon₃ * (kappa hζ ^ (2 * s.m - 1) * z) ^ 37
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
  factorSupport_strict : primeIdealFactorSupport37 z ⊂ primeIdealFactorSupport37 s.xi

/-- Normalize all three weighted generators by the explicit half powers of
their conjugation quotients. Since those multipliers are 37th roots of
unity, every 37th power in Vandiver's equation is unchanged. -/
noncomputable def weightedReductionData_of_conjugationPowers37
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37) {s : HistoricalState hζ}
    (d : ConjugationPowerReductionData37 hζ s) :
    WeightedReductionData37 hζ s where
  x := realAdjustedGenerator37 hζ d.x d.conjugationExponent_x
  y := realAdjustedGenerator37 hζ d.y d.conjugationExponent_y
  z := realAdjustedGenerator37 hζ d.z d.conjugationExponent_z
  epsilon₁ := d.epsilon₁
  epsilon₂ := d.epsilon₂
  epsilon₃ := d.epsilon₃
  rationalBase := d.rationalBase
  highCongruence := d.highCongruence
  weightedEquation := by
    simpa only [mul_pow, realAdjustedGenerator37_pow_thirtySeven] using
      d.weightedEquation
  z_ne_zero := by
    dsimp [realAdjustedGenerator37]
    exact mul_ne_zero
      (hζ.unit' ^ (realGeneratorHalfExponent37 *
        d.conjugationExponent_z)).isUnit.ne_zero d.z_ne_zero
  coprime_xy :=
    (isCoprime_mul_unit_left_left
      (hζ.unit' ^ (realGeneratorHalfExponent37 * d.conjugationExponent_x)).isUnit
      d.x
      (realAdjustedGenerator37 hζ d.y d.conjugationExponent_y)).mpr
      ((isCoprime_mul_unit_left_right
        (hζ.unit' ^ (realGeneratorHalfExponent37 * d.conjugationExponent_y)).isUnit
        d.x d.y).mpr d.coprime_xy)
  coprime_yz :=
    (isCoprime_mul_unit_left_left
      (hζ.unit' ^ (realGeneratorHalfExponent37 * d.conjugationExponent_y)).isUnit
      d.y
      (realAdjustedGenerator37 hζ d.z d.conjugationExponent_z)).mpr
      ((isCoprime_mul_unit_left_right
        (hζ.unit' ^ (realGeneratorHalfExponent37 * d.conjugationExponent_z)).isUnit
        d.y d.z).mpr d.coprime_yz)
  coprime_xz :=
    (isCoprime_mul_unit_left_left
      (hζ.unit' ^ (realGeneratorHalfExponent37 * d.conjugationExponent_x)).isUnit
      d.x
      (realAdjustedGenerator37 hζ d.z d.conjugationExponent_z)).mpr
      ((isCoprime_mul_unit_left_right
        (hζ.unit' ^ (realGeneratorHalfExponent37 * d.conjugationExponent_z)).isUnit
        d.x d.z).mpr d.coprime_xz)
  real_x :=
    realAdjustedGenerator37_real hζ d.x d.conjugationExponent_x d.conjugation_x
  real_y :=
    realAdjustedGenerator37_real hζ d.y d.conjugationExponent_y d.conjugation_y
  real_z :=
    realAdjustedGenerator37_real hζ d.z d.conjugationExponent_z d.conjugation_z
  real_eta := d.real_eta
  factorSupport_strict := by
    have hsupp :
        primeIdealFactorSupport37
            (realAdjustedGenerator37 hζ d.z d.conjugationExponent_z) =
          primeIdealFactorSupport37 d.z := by
      unfold primeIdealFactorSupport37
      rw [Ideal.span_singleton_eq_span_singleton.mpr
        (realAdjustedGenerator37_associated hζ d.z d.conjugationExponent_z)]
    rw [hsupp]
    exact d.factorSupport_strict

private noncomputable def adjustedRoot37 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 37) (a v : (𝓞 K)ˣ)
    (hv : a = v ^ 37) : (𝓞 K)ˣ :=
  (exists_real_unit_root_37 hζ a v hv).choose

private lemma adjustedRoot37_pow {ζ : K}
    (hζ : IsPrimitiveRoot ζ 37) (a v : (𝓞 K)ˣ)
    (hv : a = v ^ 37) :
    a = adjustedRoot37 hζ a v hv ^ 37 :=
  (exists_real_unit_root_37 hζ a v hv).choose_spec.1

private lemma adjustedRoot37_real {ζ : K}
    (hζ : IsPrimitiveRoot ζ 37) (a v : (𝓞 K)ˣ)
    (hv : a = v ^ 37) :
    NumberField.IsCMField.unitsComplexConj K (adjustedRoot37 hζ a v hv) =
      adjustedRoot37 hζ a v hv :=
  (exists_real_unit_root_37 hζ a v hv).choose_spec.2

private noncomputable def weightedNextState37 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 37) {s : HistoricalState hζ}
    (d : WeightedReductionData37 hζ s)
    (v : (𝓞 K)ˣ) (hv : d.epsilon₁ / d.epsilon₂ = v ^ 37) :
    HistoricalState hζ :=
  let w := adjustedRoot37 hζ (d.epsilon₁ / d.epsilon₂) v hv
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
        ← adjustedRoot37_pow hζ (d.epsilon₁ / d.epsilon₂) v hv,
        ← mul_right_inj' d.epsilon₂.isUnit.ne_zero, mul_add, ← mul_assoc,
        ← Units.val_mul, mul_div_cancel, ← mul_assoc,
        ← Units.val_mul, mul_div_cancel]
      exact d.weightedEquation }

private lemma weightedNextState37_admissible {ζ : K}
    (hζ : IsPrimitiveRoot ζ 37) {s : HistoricalState hζ}
    (d : WeightedReductionData37 hζ s)
    (v : (𝓞 K)ˣ) (hv : d.epsilon₁ / d.epsilon₂ = v ^ 37) :
    RealSourceAdmissible hζ (weightedNextState37 hζ d v hv) := by
  let w := adjustedRoot37 hζ (d.epsilon₁ / d.epsilon₂) v hv
  have hwUnits : NumberField.IsCMField.unitsComplexConj K w = w :=
    adjustedRoot37_real hζ (d.epsilon₁ / d.epsilon₂) v hv
  have hw : NumberField.IsCMField.ringOfIntegersComplexConj K (w : 𝓞 K) = w := by
    have := congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) hwUnits
    exact this
  refine ⟨?_, d.real_y, d.real_z, d.real_eta⟩
  change NumberField.IsCMField.ringOfIntegersComplexConj K
      ((w : 𝓞 K) * d.x) = (w : 𝓞 K) * d.x
  rw [map_mul, hw, d.real_x]

/-- Equations (10) and (10a) imply the abstract historical reduction data.
The proof performs the nontrivial source step after Lemma 2: it normalizes a
`37`th root to be real, absorbs it into the first summand, divides out the
second coefficient unit, and verifies every invariant of equation (10b). -/
noncomputable def equationSevenToTenData_of_weighted37 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 37) {s : HistoricalState hζ}
    (d : WeightedReductionData37 hζ s) :
    EquationSevenToTenData hζ (RealSourceAdmissible hζ) s where
  quotientUnit := d.epsilon₁ / d.epsilon₂
  rationalBase := d.rationalBase
  highCongruence := d.highCongruence
  nextState := weightedNextState37 hζ d
  next_admissible := weightedNextState37_admissible hζ d
  next_exponent := by intros; rfl
  factorCount_decreases := by
    intro v hv
    exact Finset.card_lt_card d.factorSupport_strict

/-! ## The remaining real-ideal construction seam -/

/-- The source-faithful remainder of Vandiver's equations (7b)--(10a).

The 1929 proof does **not** assume the broad modern predicate
`RelevantIdealQuotientsPrincipal`.  In (7b), only the conjugation-symmetric
product `𝔦ₐ 𝔦₋ₐ` is used; it belongs to the maximal real field.  After
(9), the paper explicitly observes that the new quotient is unchanged by
the substitution `ζ ↦ ζ⁻¹`, so its ideal again belongs to the real field.
For each of these two ideals, `exists_real_unit_mul_pow_generator37`
already derives the required real generator from the unconditional theorem
`37 ∤ h⁺`.

What remains here is therefore to construct those two real ideals from a
historical state, verify their displayed 37th-power identities, and carry
out (7a)--(9a) plus the cyclotomic-unit simplification surrounding (10a).
The purely quadratic elimination in (10a) is separately proved by
`equationTenA_quadraticElimination37`.

This boundary is deliberately below the descent conclusion: the high local
congruence, weighted equation, exact conjugation quotients, coprimality, and
strict support inclusion are concrete fields.  Making the generators real,
preserving their equation and supports, the Kummer step, equation (10b),
and the infinite descent are proved outside this hypothesis. -/
def RealPrincipalGeneratorElimination37 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 37) : Prop :=
  ∀ s : HistoricalState hζ, RealSourceAdmissible hζ s →
    Nonempty (ConjugationPowerReductionData37 hζ s)

/-- The concrete real-generator elimination supplies the full historical
reduction relation required by the abstract well-founded descent. -/
theorem equationsSevenToTenReduction_37
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    (heliminate : RealPrincipalGeneratorElimination37 hζ) :
    EquationsSevenToTenReduction hζ (RealSourceAdmissible hζ) := by
  intro s hs
  exact (heliminate s hs).map fun d ↦
    equationSevenToTenData_of_weighted37 hζ
      (weightedReductionData_of_conjugationPowers37 hζ d)

/-- The exponent-`37` historical second case, conditional only on the exact
deep unit conclusion and the remaining source-faithful construction through
equation (10a).  No global principalization of CM ideal quotients is used. -/
theorem secondCaseExcluded_37_of_historical
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    (heliminate : RealPrincipalGeneratorElimination37 hζ)
    (hkummer : KummerUnitPowerConclusion K 37) :
    Fermat.SecondCaseExcluded 37 :=
  secondCaseExcluded_of_historical_descent (by norm_num) hζ
    (RealSourceAdmissible hζ) (secondCaseStartsHistoricalDescent_37 hζ)
    (equationsSevenToTenReduction_37 hζ heliminate) hkummer

/-- Assemble the exact source statement of Vandiver's Lemma 2 with the
directly checked exponent-`37` Bernoulli cube data. No semiprimary deepening
hypothesis is used on this historical route. -/
theorem secondCaseExcluded_37_of_vandiverLemmaTwo
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    (heliminate : RealPrincipalGeneratorElimination37 hζ)
    (hLemmaTwo : Fermat.Irregular.VandiverUnitLemma.VandiverLemmaTwo K 37) :
    Fermat.SecondCaseExcluded 37 :=
  secondCaseExcluded_37_of_historical hζ heliminate
    (Fermat.Irregular.VandiverUnitLemma.kummerUnitPowerConclusion_of_lemmaTwo
      (by norm_num) hLemmaTwo
      Fermat.ThirtySeven.DirectVandiverData.bernoulliCubeCondition_thirtySeven_direct)

end

end Fermat.ThirtySeven.VandiverHistorical
