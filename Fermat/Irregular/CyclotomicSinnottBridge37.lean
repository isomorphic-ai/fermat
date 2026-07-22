import Fermat.Irregular.CyclotomicDiscriminant37
import Fermat.Irregular.CyclotomicSeriesAtOne37
import Fermat.Irregular.CyclotomicPlaces37
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The final Artin-factorization boundary for Sinnott--Kummer at 37

The finite Fourier calculation, the chord-log formula at `s = 1`, and the
real cyclotomic discriminant are already unconditional.  This file combines
them and proves that the circular-unit index formula is equivalent to the
single residue identity

`res_{s=1} ζ_{K⁺}(s) = ‖∏_{χ ≠ 1} L(1, χ)‖`.

It also formulates the standard pointwise Artin factorization on `Re(s) > 1`
and proves, by taking the right-hand residue at `s = 1`, that this
factorization implies the residue identity and hence the full exponent-37
Sinnott--Kummer index formula.  Thus the only remaining theorem is the local
Euler-factor identity encoded by `CyclotomicZetaFactorization37`.
-/

open scoped NumberField Classical BigOperators Topology

namespace Fermat.Irregular.CyclotomicSinnottBridge37

noncomputable section

open Filter Finset
open Fermat.Irregular.CircularUnitIndex
open Fermat.Irregular.SinnottIndex
open Fermat.Irregular.CyclotomicPlaces37
open Fermat.Irregular.CyclotomicLogDet
open Fermat.Irregular.CyclotomicDirichlet37
open Fermat.Irregular.CyclotomicSeriesAtOne37
open Fermat.Irregular.CyclotomicDiscriminant37

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {37} ℚ K]

local instance : NumberField.IsCMField K := cyclotomic37_isCMField (K := K)
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance : Fintype (RealResidueGroup37 →* ℂˣ) := Fintype.ofFinite _
local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- Product of the seventeen nontrivial even Dirichlet `L`-values at one. -/
def evenLValueProduct37 : ℂ :=
  ∏ χ : { χ : RealResidueGroup37 →* ℂˣ // χ ≠ 1 },
    (quotientCharacterToDirichlet37 χ).LFunction 1

/-- The same finite product at a complex parameter. -/
def evenLValueProduct37At (s : ℂ) : ℂ :=
  ∏ χ : { χ : RealResidueGroup37 →* ℂˣ // χ ≠ 1 },
    (quotientCharacterToDirichlet37 χ).LFunction s

/-- The exact remaining Artin factorization: on the half-plane of absolute
convergence, the maximal-real Dedekind zeta function is the Riemann zeta
function times all seventeen nontrivial even Dirichlet `L`-functions. -/
def CyclotomicZetaFactorization37 (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {37} ℚ K] : Prop :=
  ∀ s : ℂ, 1 < s.re →
    NumberField.dedekindZeta (NumberField.maximalRealSubfield K) s =
      riemannZeta s * evenLValueProduct37At s

theorem evenLValueProduct37At_one : evenLValueProduct37At 1 = evenLValueProduct37 := by
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

theorem quotientCharacterToDirichlet37_ne_one
    (χ : { χ : RealResidueGroup37 →* ℂˣ // χ ≠ 1 }) :
    quotientCharacterToDirichlet37 χ ≠ 1 := by
  intro h
  apply χ.property
  exact (quotientCharacterToDirichlet37_eq_one_iff χ).mp h

theorem tendsto_evenLValueProduct37At_one :
    Tendsto (fun s : ℝ ↦ evenLValueProduct37At (s : ℂ))
      (𝓝[>] 1) (𝓝 evenLValueProduct37) := by
  simp only [evenLValueProduct37, evenLValueProduct37At]
  apply tendsto_finsetProd
  intro χ hχ
  exact ((DirichletCharacter.differentiable_LFunction
    (quotientCharacterToDirichlet37_ne_one χ)).continuous.continuousAt.tendsto.comp
      tendsto_ofReal_nhdsGT_one_nhds_one)

/-- Pointwise Artin factorization implies the required residue factorization. -/
theorem residue_eq_norm_evenLValueProduct37
    (hfactor : CyclotomicZetaFactorization37 K) :
    NumberField.dedekindZeta_residue K⁺ = ‖evenLValueProduct37‖ := by
  have hriemann : Tendsto (fun s : ℝ ↦
      ((s : ℂ) - 1) * riemannZeta (s : ℂ)) (𝓝[>] 1) (𝓝 1) :=
    riemannZeta_residue_one.comp tendsto_ofReal_nhdsGT_one_punctured
  have hright : Tendsto (fun s : ℝ ↦
      (((s : ℂ) - 1) * riemannZeta (s : ℂ)) *
        evenLValueProduct37At (s : ℂ)) (𝓝[>] 1) (𝓝 evenLValueProduct37) := by
    simpa using hriemann.mul tendsto_evenLValueProduct37At_one
  have heq : (fun s : ℝ ↦
      ((s : ℂ) - 1) * NumberField.dedekindZeta K⁺ (s : ℂ)) =ᶠ[𝓝[>] 1]
      (fun s : ℝ ↦ (((s : ℂ) - 1) * riemannZeta (s : ℂ)) *
        evenLValueProduct37At (s : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hfactor (s : ℂ) (by simpa using hs)]
    ring
  have hleft : Tendsto (fun s : ℝ ↦
      ((s : ℂ) - 1) * NumberField.dedekindZeta K⁺ (s : ℂ))
      (𝓝[>] 1) (𝓝 evenLValueProduct37) :=
    hright.congr' heq.symm
  have hresidue : ((NumberField.dedekindZeta_residue K⁺ : ℝ) : ℂ) =
      evenLValueProduct37 :=
    tendsto_nhds_unique
      (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K⁺) hleft
  calc
    NumberField.dedekindZeta_residue K⁺ =
        ‖((NumberField.dedekindZeta_residue K⁺ : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real]
      exact (Real.norm_of_nonneg
        (NumberField.dedekindZeta_residue_pos K⁺).le).symm
    _ = ‖evenLValueProduct37‖ := congrArg norm hresidue

/-- All finite and archimedean factors cancel unconditionally. -/
theorem explicitSineDet_div_sqrt_discr_eq_norm_evenLValueProduct37 :
    |explicitSineMatrix37.det| / Real.sqrt |(NumberField.discr K⁺ : ℝ)| =
      ‖evenLValueProduct37‖ := by
  rw [abs_explicitSineDet_eq_sqrt_pow_mul_norm_prod_LFunction_unconditional,
    sqrt_abs_discr_maximalRealSubfield37]
  simp only [evenLValueProduct37]
  have hsqrt : (Real.sqrt 37) ^ 17 ≠ 0 := by positivity
  simp [hsqrt]

/-- Exact final equivalence: Sinnott--Kummer at 37 is now only the Dedekind
residue / Dirichlet-`L` product identity. -/
theorem circularUnit37_realIndex_eq_classNumber_iff_residue_eq_norm_evenLValueProduct37
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 37) :
    realUnitRelIndex (circularUnit37 hzeta) = NumberField.classNumber K⁺ ↔
      NumberField.dedekindZeta_residue K⁺ = ‖evenLValueProduct37‖ := by
  rw [circularUnit37_realIndex_eq_classNumber_iff_explicitSineDet hzeta,
    explicitSineDet_div_sqrt_discr_eq_norm_evenLValueProduct37]

/-- The standard Artin factorization closes the full exponent-37
Sinnott--Kummer circular-unit index formula. -/
theorem circularUnit37_realIndex_eq_classNumber_of_zetaFactorization
    (hfactor : CyclotomicZetaFactorization37 K)
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 37) :
    realUnitRelIndex (circularUnit37 hzeta) = NumberField.classNumber K⁺ := by
  rw [circularUnit37_realIndex_eq_classNumber_iff_residue_eq_norm_evenLValueProduct37 hzeta]
  exact residue_eq_norm_evenLValueProduct37 hfactor

end

end Fermat.Irregular.CyclotomicSinnottBridge37
