import Fermat.Descent.Irregular.CircularUnitIndex
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

/-- The inversion-invariant weight attached to the even power-residue
exponent `2 * h`. -/
def evenSymbolWeight (h : ℕ) (x : ZMod q) : ZMod q :=
  (1 - x) ^ (2 * h) / x ^ h

/-- The normalized circular-unit symbol is a quotient of two values of the
even symbol weight. This is the auxiliary-prime-independent algebra behind
every cyclic phase receipt. -/
theorem normalizedUnitValue_pow_two_mul_eq_weight_ratio
    (hp2 : p ≠ 2) {root : ZMod q} (hroot : IsPrimitiveRoot root p)
    (j i : Fin ((p - 3) / 2)) :
    normalizedUnitValue root j i ^ (2 * h) =
      evenSymbolWeight h
          (embeddingRoot root j ^ (i.val + 2)) /
        evenSymbolWeight h (embeddingRoot root j) := by
  let x : ZMod q := embeddingRoot root j
  let a : ℕ := i.val + 2
  let e : ℕ := canonicalNormalizationExponent (p := p) a
  have hxprim : IsPrimitiveRoot x p :=
    embeddingRoot_isPrimitive hp2 hroot j
  have hx0 : x ≠ 0 := hxprim.ne_zero (Fact.out : p.Prime).ne_zero
  have hx1 : 1 - x ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (hxprim.ne_one (Fact.out : p.Prime).one_lt))
  have hnorm : 2 * e + a ≡ 1 [MOD p] :=
    canonicalNormalizationExponent_modEq hp2 a
  have hnormh : h * (2 * e + a) ≡ h * 1 [MOD p] :=
    hnorm.mul_left h
  have hexp : (2 * h) * e + h * a ≡ h [MOD p] := by
    simpa [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      hnormh
  have hpow : x ^ ((2 * h) * e + h * a) = x ^ h :=
    pow_eq_pow_of_modEq hexp hxprim.pow_eq_one
  change (x ^ e * (1 - x ^ a) / (1 - x)) ^ (2 * h) =
    evenSymbolWeight h (x ^ a) / evenSymbolWeight h x
  simp only [evenSymbolWeight, mul_pow, div_pow]
  field_simp [hx0, hx1]
  have hpow' : x ^ (e * (2 * h)) * x ^ (a * h) = x ^ h := by
    rw [← pow_add]
    simpa [Nat.mul_comm] using hpow
  calc
    _ = (x ^ (e * (2 * h)) * x ^ (a * h)) *
          (1 - x ^ a) ^ (2 * h) := by ring
    _ = x ^ h * (1 - x ^ a) ^ (2 * h) := by rw [hpow']
    _ = _ := by ring

/-- The even symbol weight descends through inversion. -/
theorem evenSymbolWeight_inv (x : ZMod q) (hx : x ≠ 0) :
    evenSymbolWeight h x⁻¹ = evenSymbolWeight h x := by
  unfold evenSymbolWeight
  have hsub : 1 - x⁻¹ = (x - 1) / x := by
    field_simp [hx]
  rw [hsub, div_pow]
  field_simp [hx]
  rw [one_div]
  field_simp [hx]
  ring_nf
  have hxpow : x ^ h ≠ 0 := pow_ne_zero h hx
  rw [pow_mul x h 2, inv_pow]
  rw [show (x ^ h) ^ 2 * (x ^ h)⁻¹ = x ^ h by
    field_simp [hxpow]]
  congr 1
  rw [pow_mul, pow_mul]
  have hneg : (-1 + x) ^ h = (-1 : ZMod q) ^ h * (1 - x) ^ h := by
    rw [show -1 + x = -(1 - x) by ring, neg_pow]
  rw [hneg]
  rw [mul_pow]
  have hsignsq : ((-1 : ZMod q) ^ h) ^ 2 = 1 := by
    calc
      ((-1 : ZMod q) ^ h) ^ 2 = (-1 : ZMod q) ^ (h * 2) :=
        (pow_mul (-1 : ZMod q) h 2).symm
      _ = (-1 : ZMod q) ^ (2 * h) := by rw [Nat.mul_comm]
      _ = ((-1 : ZMod q) ^ 2) ^ h := pow_mul (-1 : ZMod q) 2 h
      _ = 1 := by simp
  rw [hsignsq, one_mul]

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

/-- The power-residue exponent of an odd-prime split certificate is even. -/
theorem symbolExponent_even : Even C.symbolExponent := by
  have hq2 : q ≠ 2 := by
    intro hq
    subst q
    have heq : 1 = C.symbolExponent * p := by
      simpa using C.q_sub_one
    have hpdiv : p ∣ 1 := ⟨C.symbolExponent, by
      simpa [Nat.mul_comm] using heq⟩
    exact (Fact.out : Nat.Prime p).ne_one (Nat.dvd_one.mp hpdiv)
  have hpodd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two C.hp2
  have hqodd : Odd q := (Fact.out : Nat.Prime q).odd_of_ne_two hq2
  have hprod : Even (C.symbolExponent * p) := by
    rw [← C.q_sub_one]
    exact Nat.Odd.sub_odd hqodd odd_one
  rcases Nat.even_mul.mp hprod with hm | hp_even
  · exact hm
  · exact ((Nat.not_even_iff_odd.mpr hpodd) hp_even).elim

/-- Every even symbol weight of a nontrivial `p`th root is itself a `p`th
root of unity in the split residue field. -/
theorem evenSymbolWeight_pow_eq_one
    (hm : C.symbolExponent = 2 * h)
    (x : ZMod q) (hxp : x ^ p = 1) (hx1 : x ≠ 1) :
    evenSymbolWeight h x ^ p = 1 := by
  have hx0 : x ≠ 0 := by
    intro hx
    rw [hx, zero_pow (Fact.out : Nat.Prime p).ne_zero] at hxp
    exact zero_ne_one hxp
  have hsub0 : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  have hqexp : q - 1 = (2 * h) * p := by
    rw [C.q_sub_one, hm]
  unfold evenSymbolWeight
  rw [div_pow, ← pow_mul, ← pow_mul]
  have hnum : (1 - x) ^ ((2 * h) * p) = 1 := by
    rw [← hqexp]
    exact ZMod.pow_card_sub_one_eq_one hsub0
  have hden : x ^ (h * p) = 1 := by
    rw [Nat.mul_comm, pow_mul, hxp, one_pow]
  rw [hnum, hden, div_one]

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
