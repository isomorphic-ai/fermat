import Fermat.Irregular.CircularUnitIndex
import FltRegular.NumberTheory.Cyclotomic.UnitLemmas

/-!
# Prime-generic circular-unit residue certificates

This module turns the finite-field half of a circular-unit certificate into
actual linear functionals on the Dirichlet unit lattice.  A `Certificate`
contains only finite data:

* odd primes `p` and `q` with `q - 1 = s * p`;
* a primitive `p`th root in `ZMod q`;
* a square matrix over `ZMod p`; and
* entrywise certificates saying that the `s`th power-residue symbols of the
  canonical normalized circular units have the recorded discrete logs.

From this data the file constructs the reduction homomorphisms from a
`p`th cyclotomic field, corrects the raw character by the CM norm and the
factor `2⁻¹`, descends through roots of unity, and proves the full
evaluation-matrix identity.  A nonzero determinant then certifies relative
real-unit index prime to `p`.

The final Sinnott--Kummer passage from that index to the plus class number
is deliberately not part of the certificate.
-/

open scoped NumberField

namespace Fermat.Irregular.CircularUnitResidues

noncomputable section

open Polynomial
open Module
open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.CircularUnitIndex
open Fermat.Irregular.CircularUnits

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime]

def embeddingRoot (root : ZMod q) (j : Fin ((p - 3) / 2)) : ZMod q :=
  root ^ (j.val + 1)

theorem embeddingRoot_isPrimitive (hp2 : p ≠ 2)
    {root : ZMod q} (hroot : IsPrimitiveRoot root p)
    (j : Fin ((p - 3) / 2)) :
    IsPrimitiveRoot (embeddingRoot root j) p := by
  apply hroot.pow_of_coprime
  exact Nat.Coprime.symm <| Nat.coprime_of_lt_prime
    (by omega) (by
      have hp3 : 3 ≤ p :=
        (Fact.out : p.Prime).two_le.lt_or_eq.resolve_right hp2.symm
      omega) (Fact.out : p.Prime)

def normalizedUnitValue (root : ZMod q)
    (j i : Fin ((p - 3) / 2)) : ZMod q :=
  embeddingRoot root j ^
      canonicalNormalizationExponent (p := p) (i.val + 2) *
    (1 - embeddingRoot root j ^ (i.val + 2)) /
      (1 - embeddingRoot root j)

structure Certificate (p q : ℕ) [Fact p.Prime] [Fact q.Prime] where
  hp2 : p ≠ 2
  symbolExponent : ℕ
  q_sub_one : q - 1 = symbolExponent * p
  root : ZMod q
  root_isPrimitive : IsPrimitiveRoot root p
  matrix : Matrix (Fin ((p - 3) / 2)) (Fin ((p - 3) / 2)) (ZMod p)
  entry_certificate : ∀ j i,
    normalizedUnitValue root j i ^ symbolExponent =
      root ^ (matrix j i).val

namespace Certificate

variable (C : Certificate p q)

def rootUnit : (ZMod q)ˣ :=
  Units.mk0 C.root (C.root_isPrimitive.ne_zero (Fact.out : p.Prime).ne_zero)

theorem rootUnit_isPrimitive : IsPrimitiveRoot C.rootUnit p := by
  apply IsPrimitiveRoot.coe_units_iff.mp
  simpa [rootUnit] using C.root_isPrimitive

noncomputable def powerToRootPowers :
    (ZMod q)ˣ →* Subgroup.zpowers C.rootUnit where
  toFun u := ⟨u ^ C.symbolExponent, by
    rw [C.rootUnit_isPrimitive.zpowers_eq]
    rw [mem_rootsOfUnity]
    calc
      (u ^ C.symbolExponent) ^ p = u ^ (q - 1) := by
        rw [← pow_mul, C.q_sub_one]
      _ = 1 := ZMod.units_pow_card_sub_one_eq_one q u⟩
  map_one' := by ext; simp
  map_mul' u v := by ext; simp [mul_pow]

noncomputable def residueLog : Additive (ZMod q)ˣ →+ ZMod p :=
  C.rootUnit_isPrimitive.zmodEquivZPowers.symm.toAddMonoidHom.comp
    C.powerToRootPowers.toAdditive

theorem residueLog_eq_of_pow_eq (u : (ZMod q)ˣ) (m : ℕ)
    (h : ((u : ZMod q) ^ C.symbolExponent) = C.root ^ m) :
    C.residueLog (Additive.ofMul u) = (m : ZMod p) := by
  have hsub : C.powerToRootPowers u =
      (⟨C.rootUnit ^ m, m, rfl⟩ : Subgroup.zpowers C.rootUnit) := by
    unfold powerToRootPowers
    apply Subtype.ext
    change u ^ C.symbolExponent = C.rootUnit ^ m
    apply Units.ext
    simpa [rootUnit] using h
  change C.rootUnit_isPrimitive.zmodEquivZPowers.symm
    (Additive.ofMul (C.powerToRootPowers u)) = (m : ZMod p)
  rw [hsub, C.rootUnit_isPrimitive.zmodEquivZPowers_symm_apply_pow]

variable {K : Type*} [Field K] [NumberField K]
variable [IsCyclotomicExtension {p} ℚ K]
variable {zeta : K} (hzeta : IsPrimitiveRoot zeta p)

omit [IsCyclotomicExtension {p} ℚ K] in
private theorem minpoly_toInteger_eq_cyclotomic :
    minpoly ℤ hzeta.toInteger = cyclotomic p ℤ := by
  apply Polynomial.map_injective (algebraMap ℤ ℚ)
    (RingHom.injective_int (algebraMap ℤ ℚ))
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions ℚ K,
    show algebraMap (𝓞 K) K hzeta.toInteger = zeta from rfl,
    ← cyclotomic_eq_minpoly_rat hzeta (Fact.out : p.Prime).pos,
    map_cyclotomic]
  exact IsIntegralClosure.isIntegral _ K _

noncomputable def reductionHom (j : Fin ((p - 3) / 2)) :
    𝓞 K →+* ZMod q :=
  (hzeta.integralPowerBasis.lift (embeddingRoot C.root j) (by
    rw [hzeta.integralPowerBasis_gen, minpoly_toInteger_eq_cyclotomic hzeta]
    simpa [aeval_def, eval₂_eq_eval_map, map_cyclotomic, IsRoot.def] using
      (embeddingRoot_isPrimitive C.hp2 C.root_isPrimitive j).isRoot_cyclotomic
        (Fact.out : p.Prime).pos)).toRingHom

@[simp]
theorem reductionHom_zeta (j : Fin ((p - 3) / 2)) :
    C.reductionHom hzeta j hzeta.toInteger = embeddingRoot C.root j := by
  rw [reductionHom, ← hzeta.integralPowerBasis_gen]
  exact PowerBasis.lift_gen _ _ _

theorem reductionHom_circularUnitFamily (j i : Fin ((p - 3) / 2)) :
    C.reductionHom hzeta j (circularUnitFamily hzeta C.hp2 i : 𝓞 K) =
      normalizedUnitValue C.root j i := by
  rw [circularUnitFamily_val]
  simp only [map_mul, map_pow, map_sum, C.reductionHom_zeta]
  unfold normalizedUnitValue
  have htarget := embeddingRoot_isPrimitive C.hp2 C.root_isPrimitive j
  have hne : 1 - embeddingRoot C.root j ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (htarget.ne_one (by
      exact (Fact.out : p.Prime).one_lt)))
  apply mul_left_cancel₀ (a := 1 - embeddingRoot C.root j) hne
  rw [mul_div_cancel₀ _ hne]
  calc
    (1 - embeddingRoot C.root j) *
        (embeddingRoot C.root j ^
          canonicalNormalizationExponent (p := p) (i.val + 2) *
            ∑ x ∈ Finset.range (i.val + 2), embeddingRoot C.root j ^ x) =
        embeddingRoot C.root j ^
          canonicalNormalizationExponent (p := p) (i.val + 2) *
            ((1 - embeddingRoot C.root j) *
              ∑ x ∈ Finset.range (i.val + 2), embeddingRoot C.root j ^ x) := by
      ring
    _ = embeddingRoot C.root j ^
          canonicalNormalizationExponent (p := p) (i.val + 2) *
            (1 - embeddingRoot C.root j ^ (i.val + 2)) := by
      rw [show (1 - embeddingRoot C.root j) *
          ∑ x ∈ Finset.range (i.val + 2), embeddingRoot C.root j ^ x =
          1 - embeddingRoot C.root j ^ (i.val + 2) by
        calc
          (1 - embeddingRoot C.root j) *
              ∑ x ∈ Finset.range (i.val + 2), embeddingRoot C.root j ^ x =
              -((embeddingRoot C.root j - 1) *
                ∑ x ∈ Finset.range (i.val + 2), embeddingRoot C.root j ^ x) := by
            ring
          _ = -(embeddingRoot C.root j ^ (i.val + 2) - 1) := by
            rw [mul_geom_sum]
          _ = 1 - embeddingRoot C.root j ^ (i.val + 2) := by ring]

local instance : Module ℤ (UnitsModTorsion K) :=
  @AddCommGroup.toIntModule (UnitsModTorsion K) (inferInstance)

/-- The Dirichlet unit basis reindexed by the canonical circular-unit
columns. -/
def basisModTorsion : Basis (Fin ((p - 3) / 2)) ℤ (UnitsModTorsion K) :=
  (NumberField.Units.basisModTorsion K).reindex
    (finCongr (cyclotomicPrime_unitRank (K := K)
      (Fact.out : p.Prime) C.hp2))

section CM

variable [NumberField.IsCMField K]

/-- The CM norm on units.  It kills torsion and squares real units. -/
noncomputable def realUnitNorm : (𝓞 K)ˣ →* (𝓞 K)ˣ where
  toFun u := u * NumberField.IsCMField.unitsComplexConj K u
  map_one' := by simp
  map_mul' u v := by
    simp only [map_mul]
    ac_rfl

theorem realUnitNorm_eq_one_of_mem_torsion (u : (𝓞 K)ˣ)
    (hu : u ∈ NumberField.Units.torsion K) : realUnitNorm u = 1 := by
  have hconj : NumberField.IsCMField.unitsComplexConj K u = u⁻¹ := by
    simpa using
      (NumberField.IsCMField.unitsComplexConj_torsion (K := K)
        (⟨u, hu⟩ : NumberField.Units.torsion K))
  change u * NumberField.IsCMField.unitsComplexConj K u = 1
  rw [hconj, mul_inv_cancel]

omit [IsCyclotomicExtension {p} ℚ K] in
@[simp]
theorem realUnitNorm_circularUnitFamily (i : Fin ((p - 3) / 2)) :
    realUnitNorm (circularUnitFamily hzeta C.hp2 i) =
      circularUnitFamily hzeta C.hp2 i ^ 2 := by
  change circularUnitFamily hzeta C.hp2 i *
    NumberField.IsCMField.unitsComplexConj K
      (circularUnitFamily hzeta C.hp2 i) = _
  rw [(NumberField.IsCMField.unitsComplexConj_eq_self_iff K _).mpr
    (circularUnitFamily_mem_realUnits hzeta C.hp2 i)]
  exact (pow_two _).symm

/-- Multiplication by `2⁻¹` in the residue-character target. -/
def halfScale : ZMod p →+ ZMod p where
  toFun x := (2 : ZMod p)⁻¹ * x
  map_zero' := by simp
  map_add' x y := by ring

noncomputable def correctedResidueLog (j : Fin ((p - 3) / 2)) :
    Additive (𝓞 K)ˣ →+ ZMod p :=
  halfScale.comp <| C.residueLog.comp <|
    ((Units.map (C.reductionHom hzeta j)).comp
      (realUnitNorm (K := K))).toAdditive

theorem correctedResidueLog_eq_zero_of_mem_torsion
    (j : Fin ((p - 3) / 2)) (u : (𝓞 K)ˣ)
    (hu : u ∈ NumberField.Units.torsion K) :
    C.correctedResidueLog hzeta j (Additive.ofMul u) = 0 := by
  rw [correctedResidueLog]
  simp [realUnitNorm_eq_one_of_mem_torsion (K := K) u hu]

theorem correctedResidueLog_circularUnitFamily
    (j i : Fin ((p - 3) / 2)) :
    C.correctedResidueLog hzeta j
        (Additive.ofMul (circularUnitFamily hzeta C.hp2 i)) =
      C.matrix j i := by
  let u : (ZMod q)ˣ :=
    Units.map (C.reductionHom hzeta j)
      (realUnitNorm (circularUnitFamily hzeta C.hp2 i))
  have huval : (u : ZMod q) = normalizedUnitValue C.root j i ^ 2 := by
    dsimp [u]
    rw [realUnitNorm_circularUnitFamily C hzeta i]
    rw [Units.val_pow_eq_pow_val, map_pow,
      C.reductionHom_circularUnitFamily hzeta]
  have hpow : ((u : ZMod q) ^ C.symbolExponent) =
      C.root ^ ((C.matrix j i).val * 2) := by
    calc
      (u : ZMod q) ^ C.symbolExponent =
          (normalizedUnitValue C.root j i ^ 2) ^ C.symbolExponent := by
        rw [huval]
      _ = (normalizedUnitValue C.root j i ^ C.symbolExponent) ^ 2 := by
        simp only [← pow_mul]
        congr 1
        omega
      _ = (C.root ^ (C.matrix j i).val) ^ 2 := by
        rw [C.entry_certificate]
      _ = C.root ^ ((C.matrix j i).val * 2) := by rw [pow_mul]
  change (2 : ZMod p)⁻¹ * C.residueLog (Additive.ofMul u) = C.matrix j i
  rw [C.residueLog_eq_of_pow_eq u _ hpow]
  rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hpdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    rcases (Nat.dvd_prime Nat.prime_two).mp hpdiv with hp1 | hp2'
    · exact (Fact.out : p.Prime).ne_one hp1
    · exact C.hp2 hp2'
  calc
    (2 : ZMod p)⁻¹ * (C.matrix j i * 2) =
        (2⁻¹ * 2) * C.matrix j i := by ring
    _ = C.matrix j i := by rw [inv_mul_cancel₀ htwo, one_mul]

noncomputable def correctedResidueLogMul (j : Fin ((p - 3) / 2)) :
    (𝓞 K)ˣ →* Multiplicative (ZMod p) where
  toFun u := Multiplicative.ofAdd <|
    C.correctedResidueLog hzeta j (Additive.ofMul u)
  map_one' := by
    apply Multiplicative.toAdd.injective
    simp
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    exact map_add (C.correctedResidueLog hzeta j)
      (Additive.ofMul u) (Additive.ofMul v)

theorem torsion_le_correctedResidueLogMul_ker
    (j : Fin ((p - 3) / 2)) :
    NumberField.Units.torsion K ≤ (C.correctedResidueLogMul hzeta j).ker := by
  intro u hu
  rw [MonoidHom.mem_ker]
  apply Multiplicative.toAdd.injective
  exact C.correctedResidueLog_eq_zero_of_mem_torsion hzeta j u hu

noncomputable def quotientResidueLogMul (j : Fin ((p - 3) / 2)) :
    ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K) →*
      Multiplicative (ZMod p) :=
  QuotientGroup.lift (NumberField.Units.torsion K)
    (C.correctedResidueLogMul hzeta j)
    (C.torsion_le_correctedResidueLogMul_ker hzeta j)

noncomputable def quotientResidueLog (j : Fin ((p - 3) / 2)) :
    UnitsModTorsion K →+ ZMod p where
  toFun x := Multiplicative.toAdd (C.quotientResidueLogMul hzeta j x.toMul)
  map_zero' := by simp [quotientResidueLogMul]
  map_add' x y := by
    change Multiplicative.toAdd
      (C.quotientResidueLogMul hzeta j (x.toMul * y.toMul)) = _
    rw [map_mul]
    rfl

noncomputable def quotientResidueLinear (j : Fin ((p - 3) / 2)) :
    UnitsModTorsion K →ₗ[ℤ] ZMod p :=
  { C.quotientResidueLog hzeta j with
    map_smul' := fun n x ↦ (C.quotientResidueLog hzeta j).map_zsmul n x }

@[simp]
theorem quotientResidueLog_classOfUnit
    (j : Fin ((p - 3) / 2)) (u : (𝓞 K)ˣ) :
    C.quotientResidueLog hzeta j (classOfUnit u) =
      C.correctedResidueLog hzeta j (Additive.ofMul u) := by
  rfl

@[simp]
theorem quotientResidueLinear_circularUnitFamily
    (j i : Fin ((p - 3) / 2)) :
    C.quotientResidueLinear hzeta j
        (classOfUnit (circularUnitFamily hzeta C.hp2 i)) =
      C.matrix j i := by
  change C.quotientResidueLog hzeta j
    (classOfUnit (circularUnitFamily hzeta C.hp2 i)) = _
  rw [C.quotientResidueLog_classOfUnit]
  exact C.correctedResidueLog_circularUnitFamily hzeta j i

noncomputable def residueFunctionals :
    Fin ((p - 3) / 2) → UnitsModTorsion K →ₗ[ℤ] ZMod p :=
  fun j ↦ C.quotientResidueLinear hzeta j

theorem evalMatrix_circularUnitFamily :
    evalMatrix (classOfUnit ∘ circularUnitFamily hzeta C.hp2)
        (C.residueFunctionals hzeta) = C.matrix := by
  ext j i
  exact C.quotientResidueLinear_circularUnitFamily hzeta j i

/-- A nonsingular residue certificate gives full unit index prime to `p`. -/
theorem not_dvd_circularUnitFamily_full_index
    (hdet : C.matrix.det ≠ 0) :
    ¬p ∣ (Subgroup.closure
        (Set.range (circularUnitFamily hzeta C.hp2)) ⊔
      NumberField.Units.torsion K).index := by
  apply not_dvd_unitIndex_of_eval_det_ne_zero
    (C.basisModTorsion (K := K))
    (circularUnitFamily hzeta C.hp2) (C.residueFunctionals hzeta)
  rw [C.evalMatrix_circularUnitFamily hzeta]
  exact hdet

/-- A nonsingular residue certificate gives relative real-unit index prime
to `p`, the exact endpoint immediately before the Sinnott--Kummer formula. -/
theorem not_dvd_circularUnitFamily_real_index
    (hdet : C.matrix.det ≠ 0) :
    ¬p ∣ (Subgroup.closure
        (Set.range (circularUnitFamily hzeta C.hp2)) ⊔
      NumberField.Units.torsion K).relIndex
        (NumberField.IsCMField.realUnits K ⊔
          NumberField.Units.torsion K) := by
  apply not_dvd_realUnitRelIndex_of_eval_det_ne_zero
    (C.basisModTorsion (K := K))
    (circularUnitFamily hzeta C.hp2)
    (circularUnitFamily_mem_realUnits hzeta C.hp2)
    (C.residueFunctionals hzeta)
  rw [C.evalMatrix_circularUnitFamily hzeta]
  exact hdet

end CM

/-- Cyclotomic fields of odd prime conductor carry the required CM
structure automatically. -/
theorem not_dvd_circularUnitFamily_real_index_of_cyclotomic
    (hdet : C.matrix.det ≠ 0) :
    letI : NumberField.IsCMField K :=
      cyclotomicPrime_isCMField (K := K) (Fact.out : p.Prime) C.hp2
    ¬p ∣ (Subgroup.closure
        (Set.range (circularUnitFamily hzeta C.hp2)) ⊔
      NumberField.Units.torsion K).relIndex
        (NumberField.IsCMField.realUnits K ⊔
          NumberField.Units.torsion K) := by
  letI : NumberField.IsCMField K :=
    cyclotomicPrime_isCMField (K := K) (Fact.out : p.Prime) C.hp2
  exact C.not_dvd_circularUnitFamily_real_index hzeta hdet

end Certificate

end

end Fermat.Irregular.CircularUnitResidues
