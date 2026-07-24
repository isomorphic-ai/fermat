import Fermat.Irregular.CyclotomicCharactersPrime
import Fermat.Irregular.IdealCount
import Fermat.Irregular.CharacterEulerFactor
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Artin coefficients for maximal real prime cyclotomic fields

This file constructs, uniformly for every odd prime p, the arithmetic
function predicted by the even Dirichlet characters modulo p.  It proves
the formal local Euler-factor formula and packages coefficientwise equality
as the standard Dedekind-zeta factorization.
-/

open scoped NumberField Classical BigOperators ArithmeticFunction.zeta

namespace Fermat.Irregular.CyclotomicZetaCoefficientsPrime

noncomputable section

set_option maxHeartbeats 800000

open Finset
open Fermat.Irregular.CyclotomicCharactersPrime
open Fermat.Irregular.LocalEulerFactor

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 < p)]

local instance : Fintype (RealResidueGroup p →* ℂˣ) := Fintype.ofFinite _

/-- The coefficient sequence of a Dedekind zeta function, normalized to
vanish at zero. -/
def idealCount (F : Type*) [Field F] [NumberField F] : ArithmeticFunction ℂ :=
  toArithmeticFunction (fun n ↦
    (Nat.card {I : Ideal (NumberField.RingOfIntegers F) //
      Ideal.absNorm I = n} : ℂ))

/-- Counting integral ideals by absolute norm is multiplicative. -/
theorem idealCount_isMultiplicative
    (F : Type*) [Field F] [NumberField F] :
    (idealCount F).IsMultiplicative := by
  exact Fermat.Irregular.IdealCount.idealCountArithmetic_isMultiplicative
    (S := NumberField.RingOfIntegers F)

/-- The arithmetic function belonging to a nontrivial even character
modulo p. -/
def characterCoefficient
    (χ : {χ : RealResidueGroup p →* ℂˣ // χ ≠ 1}) :
    ArithmeticFunction ℂ :=
  toArithmeticFunction
    ((quotientCharacterToDirichlet (p := p) χ ·) : ℕ → ℂ)

/-- The convolution product predicted by the local splitting law for the
maximal real cyclotomic field. -/
def expectedIdealCount : ArithmeticFunction ℂ :=
  ArithmeticFunction.zeta *
    ∏ χ : {χ : RealResidueGroup p →* ℂˣ // χ ≠ 1},
      characterCoefficient χ

/-- The product of all nontrivial even Dirichlet L-functions at s. -/
def evenLValueProductAt (s : ℂ) : ℂ :=
  ∏ χ : {χ : RealResidueGroup p →* ℂˣ // χ ≠ 1},
    (quotientCharacterToDirichlet (p := p) χ).LFunction s

/-- The standard Artin factorization statement on the half-plane of
absolute convergence. -/
def CyclotomicZetaFactorization
    (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] : Prop :=
  ∀ s : ℂ, 1 < s.re →
    NumberField.dedekindZeta (NumberField.maximalRealSubfield K) s =
      riemannZeta s * evenLValueProductAt (p := p) s

theorem characterCoefficient_isMultiplicative
    (χ : {χ : RealResidueGroup p →* ℂˣ // χ ≠ 1}) :
    (characterCoefficient χ).IsMultiplicative := by
  exact DirichletCharacter.isMultiplicative_toArithmeticFunction
    (quotientCharacterToDirichlet (p := p) χ)

theorem isMultiplicative_finset_prod
    {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → ArithmeticFunction ℂ)
    (hf : ∀ a ∈ S, (f a).IsMultiplicative) :
    (∏ a ∈ S, f a : ArithmeticFunction ℂ).IsMultiplicative := by
  induction S using Finset.induction_on with
  | empty => exact ArithmeticFunction.isMultiplicative_one
  | @insert a S ha ih =>
      rw [prod_insert ha]
      exact (hf a (mem_insert_self a S)).mul
        (ih (fun b hb ↦ hf b (mem_insert_of_mem hb)))

theorem expectedIdealCount_isMultiplicative :
    (expectedIdealCount (p := p)).IsMultiplicative := by
  rw [expectedIdealCount]
  exact ArithmeticFunction.isMultiplicative_zeta.natCast.mul
    (isMultiplicative_finset_prod univ characterCoefficient
      (fun χ _ ↦ characterCoefficient_isMultiplicative χ))

theorem dedekindZeta_eq_LSeries_idealCount
    (F : Type*) [Field F] [NumberField F] (s : ℂ) :
    NumberField.dedekindZeta F s = LSeries (idealCount F) s := by
  apply LSeries_congr
  intro n hn
  simp [idealCount, toArithmeticFunction, hn]

theorem characterCoefficient_LSeriesSummable
    (χ : {χ : RealResidueGroup p →* ℂˣ // χ ≠ 1})
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (characterCoefficient χ) s := by
  refine (LSeriesSummable_congr s (f := characterCoefficient χ)
    (g := ((quotientCharacterToDirichlet (p := p) χ ·) : ℕ → ℂ)) ?_).mpr
      (DirichletCharacter.LSeriesSummable_of_one_lt_re _ hs)
  intro n hn
  simp [characterCoefficient, toArithmeticFunction, hn]

theorem LSeriesSummable_oneArithmeticFunction (s : ℂ) :
    LSeriesSummable ((1 : ArithmeticFunction ℂ) : ℕ → ℂ) s := by
  have hone : ((1 : ArithmeticFunction ℂ) : ℕ → ℂ) = LSeries.delta :=
    ArithmeticFunction.one_eq_delta
  rw [hone, LSeriesSummable]
  have hterm : LSeries.term LSeries.delta s =
      (fun n : ℕ ↦ if n = 1 then (1 : ℂ) else 0) := by
    funext n
    exact LSeries.term_delta s n
  rw [hterm]
  exact (hasSum_ite_eq 1 (1 : ℂ)).summable

theorem LSeriesSummable_finset_prod
    {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → ArithmeticFunction ℂ) (s : ℂ)
    (hf : ∀ a ∈ S, LSeriesSummable (f a) s) :
    LSeriesSummable
      ((∏ a ∈ S, f a : ArithmeticFunction ℂ) : ℕ → ℂ) s := by
  induction S using Finset.induction_on with
  | empty => simpa using LSeriesSummable_oneArithmeticFunction s
  | @insert a S ha ih =>
      rw [prod_insert ha]
      exact ArithmeticFunction.LSeriesSummable_mul
        (hf a (mem_insert_self a S))
        (ih (fun b hb ↦ hf b (mem_insert_of_mem hb)))

theorem LSeries_finset_prod
    {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → ArithmeticFunction ℂ) (s : ℂ)
    (hf : ∀ a ∈ S, LSeriesSummable (f a) s) :
    LSeries
      ((∏ a ∈ S, f a : ArithmeticFunction ℂ) : ℕ → ℂ) s =
      ∏ a ∈ S, LSeries (f a) s := by
  induction S using Finset.induction_on with
  | empty => simp [ArithmeticFunction.one_eq_delta, LSeries_delta]
  | @insert a S ha ih =>
      rw [prod_insert ha, prod_insert ha]
      rw [ArithmeticFunction.LSeries_mul'
        (hf a (mem_insert_self a S))
        (LSeriesSummable_finset_prod S f s
          (fun b hb ↦ hf b (mem_insert_of_mem hb)))]
      rw [ih (fun b hb ↦ hf b (mem_insert_of_mem hb))]

theorem LSeries_characterCoefficient
    (χ : {χ : RealResidueGroup p →* ℂˣ // χ ≠ 1})
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (characterCoefficient χ) s =
      (quotientCharacterToDirichlet (p := p) χ).LFunction s := by
  rw [DirichletCharacter.LFunction_eq_LSeries _ hs]
  exact LSeries_congr (fun hn ↦
    (DirichletCharacter.apply_eq_toArithmeticFunction_apply
      (quotientCharacterToDirichlet (p := p) χ) hn).symm) s

theorem LSeries_expectedIdealCount {s : ℂ} (hs : 1 < s.re) :
    LSeries (expectedIdealCount (p := p)) s =
      riemannZeta s * evenLValueProductAt (p := p) s := by
  let P : ArithmeticFunction ℂ :=
    ∏ χ : {χ : RealResidueGroup p →* ℂˣ // χ ≠ 1},
      characterCoefficient χ
  have hz : LSeriesSummable
      (((ArithmeticFunction.zeta : ArithmeticFunction ℂ) :
        ArithmeticFunction ℂ) : ℕ → ℂ) s :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have hp : LSeriesSummable (P : ℕ → ℂ) s :=
    LSeriesSummable_finset_prod univ characterCoefficient s
      (fun χ _ ↦ characterCoefficient_LSeriesSummable χ hs)
  have hP : LSeries (P : ℕ → ℂ) s =
      ∏ χ : {χ : RealResidueGroup p →* ℂˣ // χ ≠ 1},
        LSeries (characterCoefficient χ) s :=
    LSeries_finset_prod univ characterCoefficient s
      (fun χ _ ↦ characterCoefficient_LSeriesSummable χ hs)
  have hLzeta : LSeries
      (((ArithmeticFunction.zeta : ArithmeticFunction ℂ) :
        ArithmeticFunction ℂ) : ℕ → ℂ) s = riemannZeta s := by
    calc
      LSeries
          (((ArithmeticFunction.zeta : ArithmeticFunction ℂ) :
            ArithmeticFunction ℂ) : ℕ → ℂ) s =
          LSeries (fun n ↦ (ArithmeticFunction.zeta n : ℂ)) s := by
            rfl
      _ = riemannZeta s :=
        ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs
  change LSeries
      (((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * P :
        ArithmeticFunction ℂ) : ℕ → ℂ) s = _
  rw [ArithmeticFunction.LSeries_mul' hz hp, hLzeta, hP]
  simp only [evenLValueProductAt, LSeries_characterCoefficient _ hs]

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- Coefficientwise equality implies the complete Artin factorization. -/
theorem cyclotomicZetaFactorization_of_idealCount_eq_expected
    (hcoeff : idealCount K⁺ = expectedIdealCount (p := p)) :
    CyclotomicZetaFactorization (p := p) K := by
  intro s hs
  rw [dedekindZeta_eq_LSeries_idealCount, hcoeff]
  exact LSeries_expectedIdealCount hs

omit [IsCyclotomicExtension {p} ℚ K] in
theorem idealCount_eq_expected_of_primePowers
    (hprime : ∀ q k : ℕ, q.Prime →
      idealCount K⁺ (q ^ k) =
        expectedIdealCount (p := p) (q ^ k)) :
    idealCount K⁺ = expectedIdealCount (p := p) := by
  exact (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
    (idealCount K⁺) (idealCount_isMultiplicative K⁺)
    (expectedIdealCount (p := p))
    expectedIdealCount_isMultiplicative).mpr hprime

/-- Prime-power coefficient identities imply the complete factorization. -/
theorem cyclotomicZetaFactorization_of_primePower_idealCounts
    (hprime : ∀ q k : ℕ, q.Prime →
      idealCount K⁺ (q ^ k) =
        expectedIdealCount (p := p) (q ^ k)) :
    CyclotomicZetaFactorization (p := p) K :=
  cyclotomicZetaFactorization_of_idealCount_eq_expected
    (idealCount_eq_expected_of_primePowers hprime)

theorem primePowerSeries_characterCoefficient_of_coprime
    (q : ℕ) (hq : q.Coprime p)
    (χ : {χ : RealResidueGroup p →* ℂˣ // χ ≠ 1}) :
    primePowerSeries q (characterCoefficient χ) =
      geometricSeries
        (((χ.1 (realResidueOfCoprime q hq) : ℂˣ) : ℂ)) := by
  have hq0 : q ≠ 0 := by
    intro h
    subst q
    simp only [Nat.coprime_zero_left] at hq
    have hpgt : 2 < p := Fact.out
    omega
  apply PowerSeries.ext
  intro k
  rw [coeff_primePowerSeries, coeff_geometricSeries]
  change (if q ^ k = 0 then 0 else
    quotientCharacterToDirichlet (p := p) χ
      ((q ^ k : ℕ) : ZMod p)) = _
  rw [if_neg (pow_ne_zero k hq0), Nat.cast_pow, map_pow,
    quotientCharacterToDirichlet_apply_nat_of_coprime (p := p) q hq]

theorem primePowerSeries_zeta (q : ℕ) (hq0 : q ≠ 0) :
    primePowerSeries q
        (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
          ArithmeticFunction ℂ)) =
      geometricSeries 1 := by
  apply PowerSeries.ext
  intro k
  rw [coeff_primePowerSeries, coeff_geometricSeries]
  rw [ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply_ne (pow_ne_zero k hq0)]
  simp

theorem primePowerSeries_expectedIdealCount_of_coprime
    (q : ℕ) (hqprime : q.Prime) (hq : q.Coprime p) :
    primePowerSeries q (expectedIdealCount (p := p)) =
      ∏ χ : RealResidueGroup p →* ℂˣ,
        geometricSeries
          (((χ (realResidueOfCoprime q hq) : ℂˣ) : ℂ)) := by
  rw [expectedIdealCount, primePowerSeries_mul hqprime,
    primePowerSeries_finset_prod hqprime univ]
  rw [primePowerSeries_zeta q hqprime.ne_zero]
  simp_rw [primePowerSeries_characterCoefficient_of_coprime q hq]
  exact geometricSeries_one_mul_prod_nontrivial_characters
    (realResidueOfCoprime q hq)

/-- The unramified local coefficient predicted by all even characters. -/
theorem expectedIdealCount_primePow_of_coprime
    (q k : ℕ) (hqprime : q.Prime) (hq : q.Coprime p) :
    expectedIdealCount (p := p) (q ^ k) =
      if orderOf (realResidueOfCoprime q hq) ∣ k then
        (Nat.multichoose
          (((p - 1) / 2) / orderOf (realResidueOfCoprime q hq))
          (k / orderOf (realResidueOfCoprime q hq)) : ℂ)
      else 0 := by
  rw [← coeff_primePowerSeries]
  rw [primePowerSeries_expectedIdealCount_of_coprime q hqprime hq]
  have h := coeff_prod_geometricSeries_characters
    (G := RealResidueGroup p) (realResidueOfCoprime q hq) k
  rw [card_realResidueGroup] at h
  exact h

end

end Fermat.Irregular.CyclotomicZetaCoefficientsPrime
