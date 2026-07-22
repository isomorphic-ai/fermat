import Fermat.Irregular.CyclotomicDiscriminantPrime
import Fermat.Irregular.CyclotomicSeriesAtOnePrime
import Fermat.Irregular.CyclotomicZetaFactorizationPrime
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Sinnott--Kummer for odd prime cyclotomic fields

This file joins the generic finite Fourier calculation, the unconditional
chord-log formula at `s = 1`, the prime cyclotomic discriminant, and the
generic Artin factorization.  It proves the circular-unit index formula for
every odd-prime cyclotomic field.
-/

open scoped NumberField Classical BigOperators Topology

namespace Fermat.Irregular.CyclotomicSinnottBridgePrime

noncomputable section

open Filter Finset
open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitIndex
open Fermat.Irregular.SinnottIndex
open Fermat.Irregular.SinnottIndexPrime
open Fermat.Irregular.CyclotomicPlacesPrime
open Fermat.Irregular.CyclotomicLogDet
open Fermat.Irregular.CyclotomicCharactersPrime
open Fermat.Irregular.CyclotomicDirichletPrime
open Fermat.Irregular.CyclotomicSeriesAtOnePrime
open Fermat.Irregular.CyclotomicDiscriminantPrime
open Fermat.Irregular.CyclotomicZetaCoefficientsPrime
open Fermat.Irregular.CyclotomicZetaFactorizationPrime

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 < p)]
variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]

local instance : Fintype (RealResidueGroup p →* ℂˣ) := Fintype.ofFinite _

local notation3 "r" => (p - 3) / 2
local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- Product of all nontrivial even Dirichlet `L`-values at one. -/
def evenLValueProduct : ℂ :=
  ∏ χ : { χ : RealResidueGroup p →* ℂˣ // χ ≠ 1 },
    (quotientCharacterToDirichlet (p := p) χ).LFunction 1

theorem evenLValueProductAt_one :
    evenLValueProductAt (p := p) 1 = evenLValueProduct (p := p) := by
  rfl

theorem tendsto_ofReal_nhdsGT_one_nhds_one :
    Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] 1) (𝓝 1) := by
  have hc : ContinuousAt (fun s : ℝ ↦ (s : ℂ)) 1 := by fun_prop
  simpa using hc.tendsto.mono_left inf_le_left

theorem tendsto_ofReal_nhdsGT_one_punctured :
    Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] 1) (𝓝[≠] 1) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨tendsto_ofReal_nhdsGT_one_nhds_one, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Set.mem_Ioi] at hs
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  exact_mod_cast ne_of_gt hs

theorem quotientCharacterToDirichlet_ne_one
    (χ : { χ : RealResidueGroup p →* ℂˣ // χ ≠ 1 }) :
    quotientCharacterToDirichlet (p := p) χ ≠ 1 := by
  intro h
  apply χ.property
  exact (quotientCharacterToDirichlet_eq_one_iff (p := p) χ).mp h

theorem tendsto_evenLValueProductAt_one :
    Tendsto (fun s : ℝ ↦ evenLValueProductAt (p := p) (s : ℂ))
      (𝓝[>] 1) (𝓝 (evenLValueProduct (p := p))) := by
  simp only [evenLValueProduct, evenLValueProductAt]
  apply tendsto_finsetProd
  intro χ hχ
  exact ((DirichletCharacter.differentiable_LFunction
    (quotientCharacterToDirichlet_ne_one χ)).continuous.continuousAt.tendsto.comp
      tendsto_ofReal_nhdsGT_one_nhds_one)

/-- Pointwise Artin factorization implies the required residue identity. -/
theorem residue_eq_norm_evenLValueProduct
    (hfactor : CyclotomicZetaFactorization (p := p) K) :
    NumberField.dedekindZeta_residue K⁺ =
      ‖evenLValueProduct (p := p)‖ := by
  have hriemann : Tendsto (fun s : ℝ ↦
      ((s : ℂ) - 1) * riemannZeta (s : ℂ)) (𝓝[>] 1) (𝓝 1) :=
    riemannZeta_residue_one.comp tendsto_ofReal_nhdsGT_one_punctured
  have hright : Tendsto (fun s : ℝ ↦
      (((s : ℂ) - 1) * riemannZeta (s : ℂ)) *
        evenLValueProductAt (p := p) (s : ℂ))
      (𝓝[>] 1) (𝓝 (evenLValueProduct (p := p))) := by
    simpa using hriemann.mul (tendsto_evenLValueProductAt_one (p := p))
  have heq : (fun s : ℝ ↦
      ((s : ℂ) - 1) * NumberField.dedekindZeta K⁺ (s : ℂ)) =ᶠ[𝓝[>] 1]
      (fun s : ℝ ↦ (((s : ℂ) - 1) * riemannZeta (s : ℂ)) *
        evenLValueProductAt (p := p) (s : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hfactor (s : ℂ) (by simpa using hs)]
    ring
  have hleft : Tendsto (fun s : ℝ ↦
      ((s : ℂ) - 1) * NumberField.dedekindZeta K⁺ (s : ℂ))
      (𝓝[>] 1) (𝓝 (evenLValueProduct (p := p))) :=
    hright.congr' heq.symm
  have hresidue :
      ((NumberField.dedekindZeta_residue K⁺ : ℝ) : ℂ) =
        evenLValueProduct (p := p) :=
    tendsto_nhds_unique
      (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K⁺) hleft
  calc
    NumberField.dedekindZeta_residue K⁺ =
        ‖((NumberField.dedekindZeta_residue K⁺ : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real]
      exact (Real.norm_of_nonneg
        (NumberField.dedekindZeta_residue_pos K⁺).le).symm
    _ = ‖evenLValueProduct (p := p)‖ := congrArg norm hresidue

/-- The finite, archimedean, and discriminant factors cancel uniformly. -/
theorem explicitSineDet_div_sqrt_discr_eq_norm_evenLValueProduct :
    |(explicitSineMatrix (p := p)).det| /
        Real.sqrt |(NumberField.discr K⁺ : ℝ)| =
      ‖evenLValueProduct (p := p)‖ := by
  rw [abs_explicitSineDet_eq_sqrt_pow_mul_norm_prod_LFunction_unconditional,
    sqrt_abs_discr_maximalRealSubfield (p := p) (K := K)]
  simp only [evenLValueProduct]
  have hpReal : (0 : ℝ) < p := by
    exact_mod_cast Nat.Prime.pos (Fact.out : Nat.Prime p)
  have hsqrt : (Real.sqrt p) ^ r ≠ 0 :=
    pow_ne_zero _ (ne_of_gt (Real.sqrt_pos.2 hpReal))
  simp [hsqrt]

/-- The circular-unit index formula is equivalent to the Artin residue identity. -/
theorem circularUnit_realIndex_eq_classNumber_iff_residue_eq_norm_evenLValueProduct
    {zeta : K} (hzeta : IsPrimitiveRoot zeta p) :
    realUnitRelIndex
        (circularUnitFamily hzeta (prime_ne_two (p := p))) =
      NumberField.classNumber K⁺ ↔
    NumberField.dedekindZeta_residue K⁺ =
      ‖evenLValueProduct (p := p)‖ := by
  rw [circularUnit_realIndex_eq_classNumber_iff (p := p) (K := K) hzeta,
    circularUnit_regOfFamily_eq_explicitSineDet (p := p) (K := K) hzeta,
    explicitSineDet_div_sqrt_discr_eq_norm_evenLValueProduct (p := p) (K := K)]

theorem circularUnit_realIndex_eq_classNumber_of_zetaFactorization
    (hfactor : CyclotomicZetaFactorization (p := p) K)
    {zeta : K} (hzeta : IsPrimitiveRoot zeta p) :
    realUnitRelIndex
        (circularUnitFamily hzeta (prime_ne_two (p := p))) =
      NumberField.classNumber K⁺ := by
  rw [circularUnit_realIndex_eq_classNumber_iff_residue_eq_norm_evenLValueProduct
    (p := p) (K := K) hzeta]
  exact residue_eq_norm_evenLValueProduct (p := p) (K := K) hfactor

/-- Unconditional Sinnott--Kummer index formula for every odd prime. -/
theorem circularUnit_realIndex_eq_classNumber
    {zeta : K} (hzeta : IsPrimitiveRoot zeta p) :
    realUnitRelIndex
        (circularUnitFamily hzeta (prime_ne_two (p := p))) =
      NumberField.classNumber K⁺ :=
  circularUnit_realIndex_eq_classNumber_of_zetaFactorization
    (p := p) (K := K)
    (cyclotomicZetaFactorization_of_cyclotomic (L := K)) hzeta

/-- Version which constructs the canonical CM-field instance internally. -/
theorem circularUnit_realIndex_eq_classNumber_of_cyclotomic
    {q : ℕ} [Fact (Nat.Prime q)] [Fact (2 < q)]
    {L : Type*} [Field L] [NumberField L]
    [IsCyclotomicExtension {q} ℚ L]
    {zeta : L} (hzeta : IsPrimitiveRoot zeta q) :
    realUnitRelIndex
        (circularUnitFamily hzeta (prime_ne_two (p := q))) =
      NumberField.classNumber (NumberField.maximalRealSubfield L) := by
  letI : NumberField.IsCMField L :=
    cyclotomicPrime_isCMField (K := L)
      (Fact.out : Nat.Prime q) (by
        have hq : 2 < q := Fact.out
        omega)
  exact circularUnit_realIndex_eq_classNumber (p := q) (K := L) hzeta

end

end Fermat.Irregular.CyclotomicSinnottBridgePrime
