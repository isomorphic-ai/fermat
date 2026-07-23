import Fermat.Irregular.CyclotomicLogCofactor37
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Even Dirichlet characters and the exponent-37 chord sums

The characters of the real residue group `(ZMod 37)ˣ / {±1}` are exactly the even complex
Dirichlet characters modulo `37`.  This file constructs that equivalence explicitly and proves
that every nontrivial lifted character is primitive.

It then changes the finite Fourier coefficient used in the circular regulator into the classical
thirty-six-term Dirichlet chord sum.  The full sum is exactly twice the quotient-group coefficient,
and the relevant Gauss sum has norm `sqrt 37`.  Thus the remaining per-character analytic input
is isolated, with signs and conventions fixed, as `ChordLogLValueFormula37`:

`sum_a psi⁻¹(a) log |1 - zeta^a| = -tau(psi⁻¹) L(1, psi)`.

Assuming precisely this formula, the fixed sine determinant is proved to be `sqrt(37)^17` times
the norm of the product of the seventeen nontrivial even `L`-values.
-/

open scoped Classical BigOperators

namespace Fermat.Irregular.CyclotomicDirichlet37

noncomputable section

open Fermat.Irregular.CyclotomicLogDet
open Fermat.Irregular.CyclotomicLogCofactor37
open Fermat.Irregular.CyclotomicPlaces37

local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance : Fintype (RealResidueGroup37 →* ℂˣ) := Fintype.ofFinite _

/-- Even complex Dirichlet characters modulo `37`. -/
abbrev EvenDirichletCharacter37 :=
  {ψ : DirichletCharacter ℂ 37 // ψ.Even}

/-- Lift a character of the real residue quotient to a Dirichlet character modulo `37`. -/
def quotientCharacterToDirichlet37
    (χ : RealResidueGroup37 →* ℂˣ) : DirichletCharacter ℂ 37 :=
  MulChar.ofUnitHom (χ.comp (QuotientGroup.mk' signSubgroup37))

theorem quotientCharacterToDirichlet37_even
    (χ : RealResidueGroup37 →* ℂˣ) :
    (quotientCharacterToDirichlet37 χ).Even := by
  rw [DirichletCharacter.Even]
  have hneg : (-1 : (ZMod 37)ˣ) ∈ signSubgroup37 :=
    (signSubgroup37_mem_iff _).mpr (Or.inr rfl)
  rw [show (-1 : ZMod 37) = ((-1 : (ZMod 37)ˣ) : ZMod 37) by rfl]
  rw [quotientCharacterToDirichlet37, MulChar.ofUnitHom_coe]
  simp only [MonoidHom.comp_apply]
  have hq : (QuotientGroup.mk' signSubgroup37) (-1 : (ZMod 37)ˣ) = 1 :=
    (QuotientGroup.eq_one_iff (-1 : (ZMod 37)ˣ)).mpr hneg
  rw [hq]
  simp

theorem quotientCharacterToDirichlet37_apply_unit
    (χ : RealResidueGroup37 →* ℂˣ) (u : (ZMod 37)ˣ) :
    quotientCharacterToDirichlet37 χ (u : ZMod 37) =
      (χ (QuotientGroup.mk u) : ℂˣ) := by
  rw [quotientCharacterToDirichlet37, MulChar.ofUnitHom_coe]
  rfl

/-- Descend an even Dirichlet character through the sign quotient. -/
def evenDirichletCharacterToQuotient37
    (ψ : EvenDirichletCharacter37) : RealResidueGroup37 →* ℂˣ :=
  QuotientGroup.lift signSubgroup37 ψ.val.toUnitHom (by
    intro u hu
    rw [MonoidHom.mem_ker]
    rw [signSubgroup37_mem_iff] at hu
    rcases hu with rfl | rfl
    · exact map_one _
    · exact ψ.prop.toUnitHom_eval_neg_one)

theorem evenDirichletCharacterToQuotient37_mk
    (ψ : EvenDirichletCharacter37) (u : (ZMod 37)ˣ) :
    evenDirichletCharacterToQuotient37 ψ (QuotientGroup.mk u) = ψ.val.toUnitHom u := by
  exact QuotientGroup.lift_mk _ _ u

theorem evenDirichletCharacterToQuotient37_quotientCharacterToDirichlet37
    (χ : RealResidueGroup37 →* ℂˣ) :
    evenDirichletCharacterToQuotient37
      ⟨quotientCharacterToDirichlet37 χ, quotientCharacterToDirichlet37_even χ⟩ = χ := by
  apply MonoidHom.ext
  intro q
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
  rw [evenDirichletCharacterToQuotient37_mk]
  apply Units.ext
  change (((quotientCharacterToDirichlet37 χ).toUnitHom u : ℂˣ) : ℂ) = _
  rw [MulChar.coe_toUnitHom]
  rw [quotientCharacterToDirichlet37, MulChar.ofUnitHom_coe]
  rfl

theorem quotientCharacterToDirichlet37_evenDirichletCharacterToQuotient37
    (ψ : EvenDirichletCharacter37) :
    quotientCharacterToDirichlet37 (evenDirichletCharacterToQuotient37 ψ) = ψ.val := by
  apply MulChar.ext
  intro u
  rw [quotientCharacterToDirichlet37, MulChar.ofUnitHom_coe]
  simp only [MonoidHom.comp_apply]
  change ((evenDirichletCharacterToQuotient37 ψ (QuotientGroup.mk u) : ℂˣ) : ℂ) = _
  rw [evenDirichletCharacterToQuotient37_mk, MulChar.coe_toUnitHom]

/-- Characters of the real residue group are equivalent to even Dirichlet characters. -/
def quotientCharactersEquivEvenDirichlet37 :
    (RealResidueGroup37 →* ℂˣ) ≃ EvenDirichletCharacter37 where
  toFun χ := ⟨quotientCharacterToDirichlet37 χ, quotientCharacterToDirichlet37_even χ⟩
  invFun := evenDirichletCharacterToQuotient37
  left_inv := evenDirichletCharacterToQuotient37_quotientCharacterToDirichlet37
  right_inv ψ := by
    apply Subtype.ext
    exact quotientCharacterToDirichlet37_evenDirichletCharacterToQuotient37 ψ

@[simp] theorem quotientCharactersEquivEvenDirichlet37_apply_val
    (χ : RealResidueGroup37 →* ℂˣ) :
    (quotientCharactersEquivEvenDirichlet37 χ).val =
      quotientCharacterToDirichlet37 χ := rfl

@[simp] theorem quotientCharacterToDirichlet37_eq_one_iff
    (χ : RealResidueGroup37 →* ℂˣ) :
    quotientCharacterToDirichlet37 χ = 1 ↔ χ = 1 := by
  constructor
  · intro h
    apply (quotientCharactersEquivEvenDirichlet37.injective)
    apply Subtype.ext
    change quotientCharacterToDirichlet37 χ =
      quotientCharacterToDirichlet37 (1 : RealResidueGroup37 →* ℂˣ)
    rw [h]
    apply MulChar.ext
    intro u
    simp [quotientCharacterToDirichlet37]
  · rintro rfl
    apply MulChar.ext
    intro u
    simp [quotientCharacterToDirichlet37]

/-- Every nontrivial character lifted from the real quotient is primitive modulo the prime `37`. -/
theorem quotientCharacterToDirichlet37_isPrimitive
    {χ : RealResidueGroup37 →* ℂˣ} (hχ : χ ≠ 1) :
    DirichletCharacter.IsPrimitive (quotientCharacterToDirichlet37 χ) := by
  rw [DirichletCharacter.isPrimitive_def]
  have hdvd := DirichletCharacter.conductor_dvd_level
    (quotientCharacterToDirichlet37 χ)
  rcases (Nat.dvd_prime (by decide : Nat.Prime 37)).mp hdvd with h | h
  · exfalso
    apply hχ
    rw [← quotientCharacterToDirichlet37_eq_one_iff]
    rw [DirichletCharacter.eq_one_iff_conductor_eq_one]
    exact h
  · exact h

theorem standardUnit37_injective : Function.Injective standardUnit37 := by
  intro i j hij
  apply standardRealResidue37_injective
  rw [standardRealResidue37, standardRealResidue37, hij]

theorem standardUnit37_ne_neg_standardUnit37 (i j : Fin 18) :
    standardUnit37 i ≠ -standardUnit37 j := by
  intro hu
  have hz : (i.val + 1 : ZMod 37) = -(j.val + 1 : ZMod 37) := by
    simpa [standardUnit37] using congrArg Units.val hu
  have hzsum : (i.val + 1 + (j.val + 1) : ZMod 37) = 0 := by
    rw [hz]
    ring
  have hzsum' : (((i.val + 1) + (j.val + 1) : ℕ) : ZMod 37) = 0 := by
    push_cast
    exact hzsum
  have hdvd : 37 ∣ (i.val + 1) + (j.val + 1) :=
    (ZMod.natCast_eq_zero_iff _ _).mp hzsum'
  exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hdvd

/-- The thirty-six nonzero residues, ordered as the representatives `1, ..., 18` and their
negatives. -/
def signedStandardUnit37 : Fin 18 ⊕ Fin 18 → (ZMod 37)ˣ
  | Sum.inl j => standardUnit37 j
  | Sum.inr j => -standardUnit37 j

theorem signedStandardUnit37_injective : Function.Injective signedStandardUnit37 := by
  rintro (i | i) (j | j) h
  · exact congrArg Sum.inl (standardUnit37_injective h)
  · exact (standardUnit37_ne_neg_standardUnit37 i j h).elim
  · exact (standardUnit37_ne_neg_standardUnit37 j i h.symm).elim
  · exact congrArg Sum.inr (standardUnit37_injective (neg_injective h))

def signedStandardUnitsEquiv37 : (Fin 18 ⊕ Fin 18) ≃ (ZMod 37)ˣ :=
  Equiv.ofBijective signedStandardUnit37
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨signedStandardUnit37_injective, by
        rw [Fintype.card_sum, ZMod.card_units 37]
        norm_num⟩)

@[simp] theorem signedStandardUnitsEquiv37_inl (j : Fin 18) :
    signedStandardUnitsEquiv37 (Sum.inl j) = standardUnit37 j := rfl

@[simp] theorem signedStandardUnitsEquiv37_inr (j : Fin 18) :
    signedStandardUnitsEquiv37 (Sum.inr j) = -standardUnit37 j := rfl

theorem quotient_mk_neg_eq_mk37 (u : (ZMod 37)ˣ) :
    (QuotientGroup.mk (-u) : RealResidueGroup37) = QuotientGroup.mk u := by
  rw [QuotientGroup.eq_iff_div_mem, signSubgroup37_mem_iff]
  right
  rw [neg_div]
  simp

/-- The classical chord-log sum over the thirty-six nonzero residues. -/
def dirichletChordLogSum37 (ψ : DirichletCharacter ℂ 37) : ℂ :=
  ∑ u : (ZMod 37)ˣ, (unitChordLog37 u : ℂ) *
    (((ψ.toUnitHom u : ℂˣ) : ℂ))⁻¹

/-- The same sum over all residues; its zero term vanishes through the Dirichlet character. -/
def fullDirichletChordLogSum37 (ψ : DirichletCharacter ℂ 37) : ℂ :=
  ∑ a : ZMod 37, (Real.log ‖1 - eta37 ^ a.val‖ : ℂ) * ψ⁻¹ a

theorem fullDirichletChordLogSum37_eq_dirichletChordLogSum37
    (ψ : DirichletCharacter ℂ 37) :
    fullDirichletChordLogSum37 ψ = dirichletChordLogSum37 ψ := by
  rw [fullDirichletChordLogSum37]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod 37))]
  have hzero : (Real.log ‖1 - eta37 ^ (0 : ZMod 37).val‖ : ℂ) * ψ⁻¹ 0 = 0 := by
    simp
  rw [hzero, add_zero]
  rw [Finset.sum_subtype (p := fun a : ZMod 37 ↦ a ≠ 0)
    (Finset.univ.erase 0) (by intro a; simp)]
  rw [← unitsEquivNeZero.sum_comp
    (fun a : {a : ZMod 37 // a ≠ 0} ↦
      (Real.log ‖1 - eta37 ^ a.val.val‖ : ℂ) * ψ⁻¹ a.val)]
  rw [dirichletChordLogSum37]
  apply Fintype.sum_congr
  intro u
  change (unitChordLog37 u : ℂ) * ψ⁻¹ (u : ZMod 37) =
    (unitChordLog37 u : ℂ) * (((ψ.toUnitHom u : ℂˣ) : ℂ))⁻¹
  rw [MulChar.inv_apply_eq_inv', ← MulChar.coe_toUnitHom]

/-- The full Dirichlet chord sum is twice the quotient-group Fourier coefficient. -/
theorem dirichletChordLogSum37_quotientCharacter
    (χ : RealResidueGroup37 →* ℂˣ) :
    dirichletChordLogSum37 (quotientCharacterToDirichlet37 χ) =
      2 * fourierCoefficient complexChordLogKernel37 χ := by
  rw [dirichletChordLogSum37]
  simp_rw [MulChar.coe_toUnitHom, quotientCharacterToDirichlet37_apply_unit]
  rw [← signedStandardUnitsEquiv37.sum_comp
    (fun u : (ZMod 37)ˣ ↦ (unitChordLog37 u : ℂ) *
      (((χ (QuotientGroup.mk u) : ℂˣ) : ℂ))⁻¹)]
  rw [Fintype.sum_sum_type]
  simp only [signedStandardUnitsEquiv37_inl, signedStandardUnitsEquiv37_inr]
  have hright :
      (∑ j : Fin 18, (unitChordLog37 (-standardUnit37 j) : ℂ) *
          (((χ (QuotientGroup.mk (-standardUnit37 j)) : ℂˣ) : ℂ))⁻¹) =
        ∑ j : Fin 18, (unitChordLog37 (standardUnit37 j) : ℂ) *
          (((χ (QuotientGroup.mk (standardUnit37 j)) : ℂˣ) : ℂ))⁻¹ := by
    apply Fintype.sum_congr
    intro j
    rw [unitChordLog37_neg, quotient_mk_neg_eq_mk37]
  rw [hright, ← two_mul]
  congr 1
  rw [fourierCoefficient]
  rw [← standardRealResiduesEquiv37.sum_comp
    (fun g : RealResidueGroup37 ↦ complexChordLogKernel37 g *
      (((χ g : ℂˣ) : ℂ))⁻¹)]
  apply Fintype.sum_congr
  intro j
  rw [standardRealResiduesEquiv37_apply]
  rfl

/-- The Gauss sum of every nontrivial lifted inverse character has norm `sqrt 37`. -/
theorem norm_gaussSum_inv_quotientCharacterToDirichlet37
    {χ : RealResidueGroup37 →* ℂˣ} (hχ : χ ≠ 1) :
    ‖gaussSum (quotientCharacterToDirichlet37 χ)⁻¹
        (ZMod.stdAddChar (N := 37))‖ = Real.sqrt 37 := by
  let ψ := quotientCharacterToDirichlet37 χ
  have hψ : ψ ≠ 1 := by
    simpa [ψ] using hχ
  have hprod := gaussSum_mul_gaussSum_eq_card
    (inv_ne_one.mpr hψ) (ZMod.isPrimitive_stdAddChar 37)
  have hstar := star_gaussSum_eq ψ⁻¹ (ZMod.stdAddChar (N := 37))
  simp only [inv_inv] at hprod hstar
  rw [← hstar] at hprod
  have hnormsqC :
      (Complex.normSq (gaussSum ψ⁻¹ (ZMod.stdAddChar (N := 37))) : ℂ) = 37 := by
    rw [← Complex.mul_conj]
    norm_num at hprod ⊢
    exact hprod
  have hsquare : ‖gaussSum ψ⁻¹ (ZMod.stdAddChar (N := 37))‖ ^ 2 = (37 : ℝ) := by
    rw [Complex.sq_norm]
    exact_mod_cast hnormsqC
  calc
    ‖gaussSum ψ⁻¹ (ZMod.stdAddChar (N := 37))‖ =
        Real.sqrt (‖gaussSum ψ⁻¹ (ZMod.stdAddChar (N := 37))‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt 37 := by rw [hsquare]

theorem card_quotientCharacters37 :
    Fintype.card (RealResidueGroup37 →* ℂˣ) = 18 := by
  calc
    Fintype.card (RealResidueGroup37 →* ℂˣ) =
        Fintype.card RealResidueGroup37 :=
      (Fintype.card_congr (characterEquiv (G := RealResidueGroup37))).symm
    _ = 18 := card_realResidueGroup37

theorem card_nontrivialQuotientCharacters37 :
    Fintype.card {χ : RealResidueGroup37 →* ℂˣ // χ ≠ 1} = 17 := by
  have h := Fintype.card_subtype_compl
    (fun χ : RealResidueGroup37 →* ℂˣ ↦ χ = 1)
  rw [Fintype.card_subtype_eq, card_quotientCharacters37] at h
  simpa using h

/-- The remaining per-character analytic identity, with the additive-character convention and
Gauss-sum sign fixed explicitly. -/
def ChordLogLValueFormula37 : Prop :=
  ∀ (χ : RealResidueGroup37 →* ℂˣ), χ ≠ 1 →
    fullDirichletChordLogSum37 (quotientCharacterToDirichlet37 χ) =
      -gaussSum (quotientCharacterToDirichlet37 χ)⁻¹
          (ZMod.stdAddChar (N := 37)) *
        (quotientCharacterToDirichlet37 χ).LFunction 1

theorem norm_fourierCoefficient_eq_sqrt_div_two_mul_norm_LFunction
    (hlog : ChordLogLValueFormula37)
    {χ : RealResidueGroup37 →* ℂˣ} (hχ : χ ≠ 1) :
    ‖fourierCoefficient complexChordLogKernel37 χ‖ =
      Real.sqrt 37 / 2 * ‖(quotientCharacterToDirichlet37 χ).LFunction 1‖ := by
  have hfull :
      2 * fourierCoefficient complexChordLogKernel37 χ =
        -gaussSum (quotientCharacterToDirichlet37 χ)⁻¹
            (ZMod.stdAddChar (N := 37)) *
          (quotientCharacterToDirichlet37 χ).LFunction 1 := by
    rw [← dirichletChordLogSum37_quotientCharacter,
      ← fullDirichletChordLogSum37_eq_dirichletChordLogSum37]
    exact hlog χ hχ
  have hnorm := congrArg norm hfull
  simp only [norm_mul, Complex.norm_ofNat, norm_neg] at hnorm
  rw [norm_gaussSum_inv_quotientCharacterToDirichlet37 hχ] at hnorm
  calc
    ‖fourierCoefficient complexChordLogKernel37 χ‖ =
        (Real.sqrt 37 * ‖(quotientCharacterToDirichlet37 χ).LFunction 1‖) / 2 := by
      linarith
    _ = Real.sqrt 37 / 2 * ‖(quotientCharacterToDirichlet37 χ).LFunction 1‖ := by
      ring

/-- Conditional endpoint of the per-character chord formula: the fixed determinant is the
expected discriminant-scale factor times the product of nontrivial even `L(1)`-values. -/
theorem abs_explicitSineDet_eq_sqrt_pow_mul_norm_prod_LFunction
    (hlog : ChordLogLValueFormula37) :
    |explicitSineMatrix37.det| = (Real.sqrt 37) ^ 17 *
      ‖∏ χ : { χ : RealResidueGroup37 →* ℂˣ // χ ≠ 1 },
        (quotientCharacterToDirichlet37 χ).LFunction 1‖ := by
  rw [abs_explicitSineDet_eq_pow_mul_norm_prod_nontrivial_fourierCoefficient]
  rw [norm_prod]
  have hterm (χ : { χ : RealResidueGroup37 →* ℂˣ // χ ≠ 1 }) :
      ‖fourierCoefficient complexChordLogKernel37 χ‖ =
        Real.sqrt 37 / 2 *
          ‖(quotientCharacterToDirichlet37 χ).LFunction 1‖ :=
    norm_fourierCoefficient_eq_sqrt_div_two_mul_norm_LFunction hlog χ.property
  simp_rw [hterm]
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  rw [Finset.card_univ, card_nontrivialQuotientCharacters37]
  rw [← norm_prod]
  ring

end
end Fermat.Irregular.CyclotomicDirichlet37
