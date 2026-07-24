import Fermat.Irregular.CyclotomicSinnottBridge37
import Fermat.Irregular.IdealCount
import Fermat.Irregular.CharacterEulerFactor
import Mathlib.NumberTheory.LSeries.Dirichlet

open scoped NumberField Classical BigOperators ArithmeticFunction.zeta

namespace Fermat.Irregular.CyclotomicZetaCoefficients37

noncomputable section

open Finset
open Fermat.Irregular.CyclotomicLogDet
open Fermat.Irregular.CyclotomicDirichlet37
open Fermat.Irregular.CyclotomicSinnottBridge37
open Fermat.Irregular.LocalEulerFactor

local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance : Fintype (RealResidueGroup37 →* ℂˣ) := Fintype.ofFinite _

/-- The coefficient sequence of a Dedekind zeta function, normalized to vanish at zero. -/
def idealCount (F : Type*) [Field F] [NumberField F] : ArithmeticFunction ℂ :=
  toArithmeticFunction (fun n ↦
    (Nat.card {I : Ideal (NumberField.RingOfIntegers F) // Ideal.absNorm I = n} : ℂ))

/-- Counting integral ideals by absolute norm is multiplicative. -/
theorem idealCount_isMultiplicative
    (F : Type*) [Field F] [NumberField F] :
    (idealCount F).IsMultiplicative := by
  exact Fermat.Irregular.IdealCount.idealCountArithmetic_isMultiplicative
    (S := NumberField.RingOfIntegers F)

/-- The arithmetic function belonging to a nontrivial even character modulo 37. -/
def characterCoefficient
    (chi : {chi : RealResidueGroup37 →* ℂˣ // chi ≠ 1}) : ArithmeticFunction ℂ :=
  toArithmeticFunction ((quotientCharacterToDirichlet37 chi ·) : ℕ → ℂ)

/-- The convolution product predicted by the local splitting law for the real
cyclotomic field: the zeta coefficient and all 17 nontrivial even characters. -/
def expectedIdealCount : ArithmeticFunction ℂ :=
  ArithmeticFunction.zeta * ∏ chi : {chi : RealResidueGroup37 →* ℂˣ // chi ≠ 1},
    characterCoefficient chi

theorem characterCoefficient_isMultiplicative
    (chi : {chi : RealResidueGroup37 →* ℂˣ // chi ≠ 1}) :
    (characterCoefficient chi).IsMultiplicative := by
  exact DirichletCharacter.isMultiplicative_toArithmeticFunction
    (quotientCharacterToDirichlet37 chi)

theorem isMultiplicative_finset_prod
    {alpha : Type*} [DecidableEq alpha]
    (S : Finset alpha) (f : alpha → ArithmeticFunction ℂ)
    (hf : ∀ a ∈ S, (f a).IsMultiplicative) :
    (∏ a ∈ S, f a : ArithmeticFunction ℂ).IsMultiplicative := by
  induction S using Finset.induction_on with
  | empty => exact ArithmeticFunction.isMultiplicative_one
  | @insert a S ha ih =>
      rw [prod_insert ha]
      exact (hf a (mem_insert_self a S)).mul
        (ih (fun b hb ↦ hf b (mem_insert_of_mem hb)))

theorem expectedIdealCount_isMultiplicative :
    expectedIdealCount.IsMultiplicative := by
  rw [expectedIdealCount]
  exact ArithmeticFunction.isMultiplicative_zeta.natCast.mul
    (isMultiplicative_finset_prod univ characterCoefficient
      (fun chi _ ↦ characterCoefficient_isMultiplicative chi))

theorem dedekindZeta_eq_LSeries_idealCount
    (F : Type*) [Field F] [NumberField F] (s : ℂ) :
    NumberField.dedekindZeta F s = LSeries (idealCount F) s := by
  apply LSeries_congr
  intro n hn
  simp [idealCount, toArithmeticFunction, hn]

theorem characterCoefficient_LSeriesSummable
    (chi : {chi : RealResidueGroup37 →* ℂˣ // chi ≠ 1})
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (characterCoefficient chi) s := by
  refine (LSeriesSummable_congr s (f := characterCoefficient chi)
    (g := ((quotientCharacterToDirichlet37 chi ·) : ℕ → ℂ)) ?_).mpr
      (DirichletCharacter.LSeriesSummable_of_one_lt_re _ hs)
  intro n hn
  simp [characterCoefficient, toArithmeticFunction, hn]

theorem LSeriesSummable_oneArithmeticFunction (s : ℂ) :
    LSeriesSummable ((1 : ArithmeticFunction ℂ) : ℕ → ℂ) s := by
  have hone : ((1 : ArithmeticFunction ℂ) : ℕ → ℂ) = LSeries.delta :=
    ArithmeticFunction.one_eq_delta
  rw [hone]
  rw [LSeriesSummable]
  have hterm : LSeries.term LSeries.delta s =
      (fun n : ℕ ↦ if n = 1 then (1 : ℂ) else 0) := by
    funext n
    exact LSeries.term_delta s n
  rw [hterm]
  exact (hasSum_ite_eq 1 (1 : ℂ)).summable

theorem LSeriesSummable_finset_prod
    {alpha : Type*} [DecidableEq alpha]
    (S : Finset alpha) (f : alpha → ArithmeticFunction ℂ) (s : ℂ)
    (hf : ∀ a ∈ S, LSeriesSummable (f a) s) :
    LSeriesSummable ((∏ a ∈ S, f a : ArithmeticFunction ℂ) : ℕ → ℂ) s := by
  induction S using Finset.induction_on with
  | empty => simpa using LSeriesSummable_oneArithmeticFunction s
  | @insert a S ha ih =>
      rw [prod_insert ha]
      exact ArithmeticFunction.LSeriesSummable_mul (hf a (mem_insert_self a S))
        (ih (fun b hb ↦ hf b (mem_insert_of_mem hb)))

theorem LSeries_finset_prod
    {alpha : Type*} [DecidableEq alpha]
    (S : Finset alpha) (f : alpha → ArithmeticFunction ℂ) (s : ℂ)
    (hf : ∀ a ∈ S, LSeriesSummable (f a) s) :
    LSeries ((∏ a ∈ S, f a : ArithmeticFunction ℂ) : ℕ → ℂ) s =
      ∏ a ∈ S, LSeries (f a) s := by
  induction S using Finset.induction_on with
  | empty => simp [ArithmeticFunction.one_eq_delta, LSeries_delta]
  | @insert a S ha ih =>
      rw [prod_insert ha, prod_insert ha]
      rw [ArithmeticFunction.LSeries_mul'
        (hf a (mem_insert_self a S))
        (LSeriesSummable_finset_prod S f s (fun b hb ↦ hf b (mem_insert_of_mem hb)))]
      rw [ih (fun b hb ↦ hf b (mem_insert_of_mem hb))]

theorem LSeries_characterCoefficient
    (chi : {chi : RealResidueGroup37 →* ℂˣ // chi ≠ 1})
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (characterCoefficient chi) s =
      (quotientCharacterToDirichlet37 chi).LFunction s := by
  rw [DirichletCharacter.LFunction_eq_LSeries _ hs]
  exact LSeries_congr (fun hn ↦
    (DirichletCharacter.apply_eq_toArithmeticFunction_apply
      (quotientCharacterToDirichlet37 chi) hn).symm) s

theorem LSeries_expectedIdealCount {s : ℂ} (hs : 1 < s.re) :
    LSeries expectedIdealCount s = riemannZeta s * evenLValueProduct37At s := by
  let P : ArithmeticFunction ℂ :=
    ∏ chi : {chi : RealResidueGroup37 →* ℂˣ // chi ≠ 1}, characterCoefficient chi
  have hz : LSeriesSummable
      (((ArithmeticFunction.zeta : ArithmeticFunction ℂ) : ArithmeticFunction ℂ) : ℕ → ℂ) s :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have hp : LSeriesSummable (P : ℕ → ℂ) s := by
    exact LSeriesSummable_finset_prod univ characterCoefficient s
      (fun chi _ ↦ characterCoefficient_LSeriesSummable chi hs)
  have hP : LSeries (P : ℕ → ℂ) s =
      ∏ chi : {chi : RealResidueGroup37 →* ℂˣ // chi ≠ 1},
        LSeries (characterCoefficient chi) s := by
    exact LSeries_finset_prod univ characterCoefficient s
      (fun chi _ ↦ characterCoefficient_LSeriesSummable chi hs)
  have hLzeta : LSeries
      (((ArithmeticFunction.zeta : ArithmeticFunction ℂ) : ArithmeticFunction ℂ) : ℕ → ℂ) s =
      riemannZeta s := by
    calc
      LSeries
          (((ArithmeticFunction.zeta : ArithmeticFunction ℂ) : ArithmeticFunction ℂ) :
            ℕ → ℂ) s =
          LSeries (fun n ↦ (ArithmeticFunction.zeta n : ℂ)) s := by rfl
      _ = riemannZeta s := ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs
  change LSeries
      (((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * P : ArithmeticFunction ℂ) : ℕ → ℂ) s = _
  rw [ArithmeticFunction.LSeries_mul' hz hp,
    hLzeta, hP]
  simp only [evenLValueProduct37At, LSeries_characterCoefficient _ hs]

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {37} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- A coefficient-by-coefficient local splitting identity implies the complete
Artin factorization.  This is the exact algebraic seam left by the analytic proof. -/
theorem cyclotomicZetaFactorization37_of_idealCount_eq_expected
    (hcoeff : idealCount K⁺ = expectedIdealCount) :
    CyclotomicZetaFactorization37 K := by
  intro s hs
  rw [dedekindZeta_eq_LSeries_idealCount]
  rw [hcoeff]
  exact LSeries_expectedIdealCount hs

omit [IsCyclotomicExtension {37} ℚ K] in
/-- It is enough to prove that ideal counting is multiplicative and to identify
its value on powers of rational primes.  All global coefficient bookkeeping is
then automatic from unique factorization in `ℕ`. -/
theorem idealCount_eq_expected_of_multiplicative_of_primePowers
    (hmult : (idealCount K⁺).IsMultiplicative)
    (hprime : ∀ q k : ℕ, q.Prime →
      idealCount K⁺ (q ^ k) = expectedIdealCount (q ^ k)) :
    idealCount K⁺ = expectedIdealCount := by
  exact (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
    (idealCount K⁺) hmult expectedIdealCount expectedIdealCount_isMultiplicative).mpr hprime

omit [IsCyclotomicExtension {37} ℚ K] in
/-- The global coefficient identity follows from the prime-power splitting
formula; ideal-count multiplicativity is now unconditional. -/
theorem idealCount_eq_expected_of_primePowers
    (hprime : ∀ q k : ℕ, q.Prime →
      idealCount K⁺ (q ^ k) = expectedIdealCount (q ^ k)) :
    idealCount K⁺ = expectedIdealCount :=
  idealCount_eq_expected_of_multiplicative_of_primePowers
    (idealCount_isMultiplicative K⁺) hprime

/-- The complete Artin factorization now follows from the single local
prime-power ideal-count formula. -/
theorem cyclotomicZetaFactorization37_of_primePower_idealCounts
    (hprime : ∀ q k : ℕ, q.Prime →
      idealCount K⁺ (q ^ k) = expectedIdealCount (q ^ k)) :
    CyclotomicZetaFactorization37 K :=
  cyclotomicZetaFactorization37_of_idealCount_eq_expected
    (idealCount_eq_expected_of_primePowers hprime)

/-- The image in the real residue group of an integer prime to `37`. -/
def realResidueOfCoprime37 (q : ℕ) (hq : q.Coprime 37) : RealResidueGroup37 :=
  QuotientGroup.mk (ZMod.unitOfCoprime q hq)

theorem quotientCharacterToDirichlet37_apply_nat_of_coprime
    (q : ℕ) (hq : q.Coprime 37) (χ : RealResidueGroup37 →* ℂˣ) :
    quotientCharacterToDirichlet37 χ (q : ZMod 37) =
      ((χ (realResidueOfCoprime37 q hq) : ℂˣ) : ℂ) := by
  rw [show (q : ZMod 37) = ((ZMod.unitOfCoprime q hq : (ZMod 37)ˣ) : ZMod 37) by
    simp only [ZMod.coe_unitOfCoprime]]
  exact quotientCharacterToDirichlet37_apply_unit χ (ZMod.unitOfCoprime q hq)

theorem primePowerSeries_characterCoefficient_of_coprime
    (q : ℕ) (hq : q.Coprime 37)
    (χ : { χ : RealResidueGroup37 →* ℂˣ // χ ≠ 1 }) :
    primePowerSeries q (characterCoefficient χ) =
      geometricSeries (((χ.1 (realResidueOfCoprime37 q hq) : ℂˣ) : ℂ)) := by
  have hq0 : q ≠ 0 := by
    intro h
    subst q
    norm_num at hq
  apply PowerSeries.ext
  intro k
  rw [coeff_primePowerSeries, coeff_geometricSeries]
  change (if q ^ k = 0 then 0 else
    quotientCharacterToDirichlet37 χ ((q ^ k : ℕ) : ZMod 37)) = _
  rw [if_neg (pow_ne_zero k hq0)]
  rw [Nat.cast_pow, map_pow,
    quotientCharacterToDirichlet37_apply_nat_of_coprime q hq]

theorem primePowerSeries_zeta (q : ℕ) (hq0 : q ≠ 0) :
    primePowerSeries q
        (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)) =
      geometricSeries 1 := by
  apply PowerSeries.ext
  intro k
  rw [coeff_primePowerSeries, coeff_geometricSeries]
  rw [ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply_ne (pow_ne_zero k hq0)]
  simp

theorem primePowerSeries_expectedIdealCount_of_coprime
    (q : ℕ) (hqprime : q.Prime) (hq : q.Coprime 37) :
    primePowerSeries q expectedIdealCount =
      ∏ χ : RealResidueGroup37 →* ℂˣ,
        geometricSeries (((χ (realResidueOfCoprime37 q hq) : ℂˣ) : ℂ)) := by
  rw [expectedIdealCount, primePowerSeries_mul hqprime,
    primePowerSeries_finset_prod hqprime univ]
  rw [primePowerSeries_zeta q hqprime.ne_zero]
  simp_rw [primePowerSeries_characterCoefficient_of_coprime q hq]
  exact geometricSeries_one_mul_prod_nontrivial_characters
    (realResidueOfCoprime37 q hq)

/-- The unramified local coefficient predicted by the eighteen even characters. -/
theorem expectedIdealCount_primePow_of_coprime
    (q k : ℕ) (hqprime : q.Prime) (hq : q.Coprime 37) :
    expectedIdealCount (q ^ k) =
      if orderOf (realResidueOfCoprime37 q hq) ∣ k then
        (Nat.multichoose
          (18 / orderOf (realResidueOfCoprime37 q hq))
          (k / orderOf (realResidueOfCoprime37 q hq)) : ℂ)
      else 0 := by
  rw [← coeff_primePowerSeries]
  rw [primePowerSeries_expectedIdealCount_of_coprime q hqprime hq]
  have h := coeff_prod_geometricSeries_characters
    (G := RealResidueGroup37) (realResidueOfCoprime37 q hq) k
  rw [card_realResidueGroup37] at h
  exact h


end

end Fermat.Irregular.CyclotomicZetaCoefficients37
