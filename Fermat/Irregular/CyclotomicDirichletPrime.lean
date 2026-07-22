import Fermat.Irregular.CyclotomicLogCofactorPrime
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Even Dirichlet characters and prime cyclotomic chord sums

Characters of the real residue quotient lift to even primitive Dirichlet
characters.  Their full chord-log sums are twice the corresponding Fourier
coefficients, and primitive Gauss sums have norm equal to the square root
of the conductor.
-/

open scoped Classical BigOperators

namespace Fermat.Irregular.CyclotomicDirichletPrime

noncomputable section

open Fermat.Irregular.CyclotomicLogDet
open Fermat.Irregular.CyclotomicLogDetPrime
open Fermat.Irregular.CyclotomicLogCofactorPrime
open Fermat.Irregular.CyclotomicPlacesPrime
open Fermat.Irregular.CyclotomicCharactersPrime
open Fermat.Irregular.SinnottIndexPrime

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 < p)]

local notation3 "r" => (p - 3) / 2
local notation3 "n" => r + 1

local instance : Fintype (RealResidueGroup p →* ℂˣ) :=
  Fintype.ofFinite _

theorem quotientCharacterToDirichlet_eq_one_iff
    (χ : RealResidueGroup p →* ℂˣ) :
    quotientCharacterToDirichlet (p := p) χ = 1 ↔ χ = 1 := by
  constructor
  · intro h
    apply MonoidHom.ext
    intro g
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective g
    have hu := congrArg
      (fun ψ : DirichletCharacter ℂ p ↦ ψ (u : ZMod p)) h
    simpa [quotientCharacterToDirichlet_apply_unit] using hu
  · rintro rfl
    apply MulChar.ext
    intro u
    simp [quotientCharacterToDirichlet]

theorem quotientCharacterToDirichlet_isPrimitive
    {χ : RealResidueGroup p →* ℂˣ} (hχ : χ ≠ 1) :
    DirichletCharacter.IsPrimitive
      (quotientCharacterToDirichlet (p := p) χ) := by
  rw [DirichletCharacter.isPrimitive_def]
  have hdvd := DirichletCharacter.conductor_dvd_level
    (quotientCharacterToDirichlet (p := p) χ)
  rcases (Nat.dvd_prime (Fact.out : Nat.Prime p)).mp hdvd with h | h
  · exfalso
    apply hχ
    rw [← quotientCharacterToDirichlet_eq_one_iff]
    rw [DirichletCharacter.eq_one_iff_conductor_eq_one]
    exact h
  · exact h

theorem standardUnit_injective :
    Function.Injective (standardUnit (p := p)) := by
  intro i j hij
  apply standardRealResidue_injective (p := p)
  rw [standardRealResidue, standardRealResidue, hij]

theorem standardUnit_ne_neg_standardUnit (i j : Fin n) :
    standardUnit (p := p) i ≠
      -standardUnit (p := p) j := by
  intro hu
  have hz : (i.val + 1 : ZMod p) =
      -(j.val + 1 : ZMod p) := by
    simpa [standardUnit] using congrArg Units.val hu
  have hzsum :
      (i.val + 1 + (j.val + 1) : ZMod p) = 0 := by
    rw [hz]
    ring
  have hzsum' :
      (((i.val + 1) + (j.val + 1) : ℕ) : ZMod p) = 0 := by
    push_cast
    exact hzsum
  have hdvd : p ∣ (i.val + 1) + (j.val + 1) :=
    (ZMod.natCast_eq_zero_iff _ _).mp hzsum'
  have hlt : (i.val + 1) + (j.val + 1) < p := by
    have hi := i.isLt
    have hj := j.isLt
    have hrank := half_rank_succ (p := p)
    have hpodd : Odd p := Nat.Prime.odd_of_ne_two
      (Fact.out : Nat.Prime p) (prime_ne_two (p := p))
    obtain ⟨m, hm⟩ := hpodd
    omega
  exact (Nat.not_dvd_of_pos_of_lt (by omega) hlt) hdvd

def signedStandardUnit : Fin n ⊕ Fin n → (ZMod p)ˣ
  | Sum.inl j => standardUnit (p := p) j
  | Sum.inr j => -standardUnit (p := p) j

theorem signedStandardUnit_injective :
    Function.Injective (signedStandardUnit (p := p)) := by
  rintro (i | i) (j | j) h
  · exact congrArg Sum.inl (standardUnit_injective h)
  · exact (standardUnit_ne_neg_standardUnit
      (p := p) i j h).elim
  · exact (standardUnit_ne_neg_standardUnit
      (p := p) j i h.symm).elim
  · exact congrArg Sum.inr
      (standardUnit_injective (neg_injective h))

def signedStandardUnitsEquiv :
    (Fin n ⊕ Fin n) ≃ (ZMod p)ˣ :=
  Equiv.ofBijective (signedStandardUnit (p := p))
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨signedStandardUnit_injective (p := p), by
        rw [Fintype.card_sum, ZMod.card_units p]
        simp only [Fintype.card_fin]
        have hsize :=
          Fermat.Irregular.CyclotomicSineProductPrime.two_half_add_one
            (p := p)
        omega⟩)

@[simp]
theorem signedStandardUnitsEquiv_inl (j : Fin n) :
    signedStandardUnitsEquiv (p := p) (Sum.inl j) =
      standardUnit (p := p) j := rfl

@[simp]
theorem signedStandardUnitsEquiv_inr (j : Fin n) :
    signedStandardUnitsEquiv (p := p) (Sum.inr j) =
      -standardUnit (p := p) j := rfl

theorem quotient_mk_neg_eq_mk (u : (ZMod p)ˣ) :
    (QuotientGroup.mk (-u) : RealResidueGroup p) =
      QuotientGroup.mk u := by
  rw [QuotientGroup.eq_iff_div_mem, signSubgroup_mem_iff]
  right
  rw [neg_div]
  simp

def dirichletChordLogSum
    (ψ : DirichletCharacter ℂ p) : ℂ :=
  ∑ u : (ZMod p)ˣ,
    (unitChordLog (p := p) u : ℂ) *
      (((ψ.toUnitHom u : ℂˣ) : ℂ))⁻¹

def fullDirichletChordLogSum
    (ψ : DirichletCharacter ℂ p) : ℂ :=
  ∑ a : ZMod p,
    (Real.log ‖1 - eta (p := p) ^ a.val‖ : ℂ) * ψ⁻¹ a

theorem fullDirichletChordLogSum_eq_dirichletChordLogSum
    (ψ : DirichletCharacter ℂ p) :
    fullDirichletChordLogSum (p := p) ψ =
      dirichletChordLogSum (p := p) ψ := by
  rw [fullDirichletChordLogSum]
  rw [← Finset.sum_erase_add _ _
    (Finset.mem_univ (0 : ZMod p))]
  have hzero :
      (Real.log ‖1 - eta (p := p) ^ (0 : ZMod p).val‖ : ℂ) *
        ψ⁻¹ 0 = 0 := by simp
  rw [hzero, add_zero]
  rw [Finset.sum_subtype
    (p := fun a : ZMod p ↦ a ≠ 0)
    (Finset.univ.erase 0) (by intro a; simp)]
  rw [← unitsEquivNeZero.sum_comp
    (fun a : {a : ZMod p // a ≠ 0} ↦
      (Real.log ‖1 - eta (p := p) ^ a.val.val‖ : ℂ) *
        ψ⁻¹ a.val)]
  rw [dirichletChordLogSum]
  apply Fintype.sum_congr
  intro u
  change (unitChordLog (p := p) u : ℂ) *
      ψ⁻¹ (u : ZMod p) =
    (unitChordLog (p := p) u : ℂ) *
      (((ψ.toUnitHom u : ℂˣ) : ℂ))⁻¹
  rw [MulChar.inv_apply_eq_inv', ← MulChar.coe_toUnitHom]

theorem dirichletChordLogSum_quotientCharacter
    (χ : RealResidueGroup p →* ℂˣ) :
    dirichletChordLogSum (p := p)
        (quotientCharacterToDirichlet (p := p) χ) =
      2 * fourierCoefficient
        (complexChordLogKernel (p := p)) χ := by
  rw [dirichletChordLogSum]
  simp_rw [MulChar.coe_toUnitHom,
    quotientCharacterToDirichlet_apply_unit]
  rw [← (signedStandardUnitsEquiv (p := p)).sum_comp
    (fun u : (ZMod p)ˣ ↦
      (unitChordLog (p := p) u : ℂ) *
        (((χ (QuotientGroup.mk u) : ℂˣ) : ℂ))⁻¹)]
  rw [Fintype.sum_sum_type]
  simp only [signedStandardUnitsEquiv_inl,
    signedStandardUnitsEquiv_inr]
  have hright :
      (∑ j : Fin n,
        (unitChordLog (p := p)
          (-standardUnit (p := p) j) : ℂ) *
        (((χ (QuotientGroup.mk
          (-standardUnit (p := p) j)) : ℂˣ) : ℂ))⁻¹) =
      ∑ j : Fin n,
        (unitChordLog (p := p)
          (standardUnit (p := p) j) : ℂ) *
        (((χ (QuotientGroup.mk
          (standardUnit (p := p) j)) : ℂˣ) : ℂ))⁻¹ := by
    apply Fintype.sum_congr
    intro j
    rw [unitChordLog_neg, quotient_mk_neg_eq_mk]
  rw [hright, ← two_mul]
  congr 1
  rw [fourierCoefficient]
  rw [← (standardRealResiduesEquiv (p := p)).sum_comp
    (fun g : RealResidueGroup p ↦
      complexChordLogKernel (p := p) g *
        (((χ g : ℂˣ) : ℂ))⁻¹)]
  apply Fintype.sum_congr
  intro j
  rw [standardRealResiduesEquiv_apply]
  rfl

theorem norm_gaussSum_inv_quotientCharacterToDirichlet
    {χ : RealResidueGroup p →* ℂˣ} (hχ : χ ≠ 1) :
    ‖gaussSum
        (quotientCharacterToDirichlet (p := p) χ)⁻¹
        (ZMod.stdAddChar (N := p))‖ =
      Real.sqrt p := by
  let ψ := quotientCharacterToDirichlet (p := p) χ
  have hψ : ψ ≠ 1 := by
    intro h
    exact hχ
      ((quotientCharacterToDirichlet_eq_one_iff
        (p := p) χ).mp h)
  have hprod := gaussSum_mul_gaussSum_eq_card
    (inv_ne_one.mpr hψ) (ZMod.isPrimitive_stdAddChar p)
  have hstar :=
    star_gaussSum_eq ψ⁻¹ (ZMod.stdAddChar (N := p))
  simp only [inv_inv] at hprod hstar
  rw [← hstar] at hprod
  have hnormsqC :
      (Complex.normSq
        (gaussSum ψ⁻¹ (ZMod.stdAddChar (N := p))) : ℂ) = p := by
    rw [← Complex.mul_conj]
    norm_num at hprod ⊢
    exact hprod
  have hsquare :
      ‖gaussSum ψ⁻¹ (ZMod.stdAddChar (N := p))‖ ^ 2 =
        (p : ℝ) := by
    rw [Complex.sq_norm]
    exact_mod_cast hnormsqC
  calc
    ‖gaussSum ψ⁻¹ (ZMod.stdAddChar (N := p))‖ =
        Real.sqrt
          (‖gaussSum ψ⁻¹ (ZMod.stdAddChar (N := p))‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt p := by rw [hsquare]

theorem card_quotientCharacters :
    Fintype.card (RealResidueGroup p →* ℂˣ) = n := by
  calc
    Fintype.card (RealResidueGroup p →* ℂˣ) =
        Fintype.card (RealResidueGroup p) :=
      (Fintype.card_congr
        (characterEquiv (G := RealResidueGroup p))).symm
    _ = n := by
      rw [card_realResidueGroup, half_rank_succ (p := p)]

theorem card_nontrivialQuotientCharacters :
    Fintype.card
      {χ : RealResidueGroup p →* ℂˣ // χ ≠ 1} = r := by
  have h := Fintype.card_subtype_compl
    (fun χ : RealResidueGroup p →* ℂˣ ↦ χ = 1)
  rw [Fintype.card_subtype_eq,
    card_quotientCharacters (p := p)] at h
  simpa using h

/-- The per-character chord-log identity. -/
def ChordLogLValueFormula : Prop :=
  ∀ (χ : RealResidueGroup p →* ℂˣ), χ ≠ 1 →
    fullDirichletChordLogSum (p := p)
      (quotientCharacterToDirichlet (p := p) χ) =
    -gaussSum
      (quotientCharacterToDirichlet (p := p) χ)⁻¹
      (ZMod.stdAddChar (N := p)) *
    (quotientCharacterToDirichlet (p := p) χ).LFunction 1

theorem norm_fourierCoefficient_eq_sqrt_div_two_mul_norm_LFunction
    (hlog : ChordLogLValueFormula (p := p))
    {χ : RealResidueGroup p →* ℂˣ} (hχ : χ ≠ 1) :
    ‖fourierCoefficient (complexChordLogKernel (p := p)) χ‖ =
      Real.sqrt p / 2 *
        ‖(quotientCharacterToDirichlet
          (p := p) χ).LFunction 1‖ := by
  have hfull :
      2 * fourierCoefficient
          (complexChordLogKernel (p := p)) χ =
        -gaussSum
          (quotientCharacterToDirichlet (p := p) χ)⁻¹
          (ZMod.stdAddChar (N := p)) *
        (quotientCharacterToDirichlet
          (p := p) χ).LFunction 1 := by
    rw [← dirichletChordLogSum_quotientCharacter,
      ← fullDirichletChordLogSum_eq_dirichletChordLogSum]
    exact hlog χ hχ
  have hnorm := congrArg norm hfull
  simp only [norm_mul, Complex.norm_ofNat, norm_neg] at hnorm
  rw [norm_gaussSum_inv_quotientCharacterToDirichlet
    (p := p) hχ] at hnorm
  calc
    ‖fourierCoefficient
      (complexChordLogKernel (p := p)) χ‖ =
        (Real.sqrt p *
          ‖(quotientCharacterToDirichlet
            (p := p) χ).LFunction 1‖) / 2 := by
      linarith
    _ = Real.sqrt p / 2 *
        ‖(quotientCharacterToDirichlet
          (p := p) χ).LFunction 1‖ := by ring

theorem abs_explicitSineDet_eq_sqrt_pow_mul_norm_prod_LFunction
    (hlog : ChordLogLValueFormula (p := p)) :
    |(explicitSineMatrix (p := p)).det| =
      (Real.sqrt p) ^ r *
      ‖∏ χ : {χ : RealResidueGroup p →* ℂˣ // χ ≠ 1},
        (quotientCharacterToDirichlet
          (p := p) χ).LFunction 1‖ := by
  rw [abs_explicitSineDet_eq_pow_mul_norm_prod_nontrivial_fourierCoefficient]
  rw [norm_prod]
  have hterm
      (χ : {χ : RealResidueGroup p →* ℂˣ // χ ≠ 1}) :
      ‖fourierCoefficient
        (complexChordLogKernel (p := p)) χ‖ =
        Real.sqrt p / 2 *
          ‖(quotientCharacterToDirichlet
            (p := p) χ).LFunction 1‖ :=
    norm_fourierCoefficient_eq_sqrt_div_two_mul_norm_LFunction
      hlog χ.property
  simp_rw [hterm]
  rw [Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, card_nontrivialQuotientCharacters]
  rw [← norm_prod]
  have hcancel : (1 / (2 : ℝ)) ^ r * 2 ^ r = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = ((Real.sqrt p) ^ r *
          ‖∏ χ : {χ : RealResidueGroup p →* ℂˣ // χ ≠ 1},
            (quotientCharacterToDirichlet
              (p := p) χ).LFunction 1‖) *
          ((1 / (2 : ℝ)) ^ r * 2 ^ r) := by ring
    _ = _ := by rw [hcancel, mul_one]

end

end Fermat.Irregular.CyclotomicDirichletPrime
