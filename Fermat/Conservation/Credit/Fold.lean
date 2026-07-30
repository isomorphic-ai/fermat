/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# C6: fold the two class-ledger views

The debit and receivable views of a class ledger are one matrix.  Complex
conjugation changes the viewing side, so on a conjugation-compatible ledger
it is represented by matrix transpose.  The relative norm is the fold that
adds an entry to that transposed view.

The final lemma is the group-theoretic net used in Vandiver's equations
(7a) and (7d).  It is deliberately independent of ideals and cyclotomic
fields: an odd-torsion class which the two equations identify both with
another class and with its negative must vanish.
-/
import Fermat.Conservation.Credit.Vacuum
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.Ideal.Norm.RelNorm

open scoped NumberField nonZeroDivisors
open Module

namespace Fermat.Conservation.Credit.Fold

universe u v

/-- An additive class value at every ordered pair of ledger nodes. -/
abbrev ClassLedger (Node : Type u) (Class : Type v) :=
  Matrix Node Node Class

/-- The conjugate view of a class ledger is its receivable-side transpose. -/
def conjugateTranspose {Node : Type u} {Class : Type v}
    (ledger : ClassLedger Node Class) : ClassLedger Node Class :=
  ledger.transpose

/-- A class ledger is compatible with a stated additive conjugation when
conjugating a debit entry gives the transposed receivable entry. -/
def ConjugationActsAsTranspose {Node : Type u} {Class : Type v}
    [AddCommGroup Class] (conjugate : Class →+ Class)
    (ledger : ClassLedger Node Class) : Prop :=
  ∀ debtor creditor,
    conjugate (ledger debtor creditor) = ledger creditor debtor

/-- The relative-norm fold adds the debit view to the transposed receivable
view. -/
def relativeNormFold {Node : Type u} {Class : Type v}
    [AddCommGroup Class] (ledger : ClassLedger Node Class) :
    ClassLedger Node Class :=
  ledger + conjugateTranspose ledger

/-- Relative norm on one class value: add it to its conjugate. -/
def relativeNormClass {Class : Type v} [AddCommGroup Class]
    (conjugate : Class →+ Class) (c : Class) : Class :=
  c + conjugate c

/-- The additive class of a nonzero fractional ideal.  Nonzeroness is kept
explicit because the class group contains only invertible fractional
ideals. -/
noncomputable def fractionalIdealClass
    {A L : Type*} [CommRing A] [IsDedekindDomain A]
    [Field L] [Algebra A L] [IsFractionRing A L]
    (I : FractionalIdeal A⁰ L) (hI : I ≠ 0) :
    Additive (ClassGroup A) :=
  Additive.ofMul (ClassGroup.mk L (Units.mk0 I hI))

@[simp]
theorem conjugateTranspose_apply {Node : Type u} {Class : Type v}
    (ledger : ClassLedger Node Class) (debtor creditor : Node) :
    conjugateTranspose ledger debtor creditor =
      ledger creditor debtor :=
  rfl

@[simp]
theorem conjugateTranspose_conjugateTranspose
    {Node : Type u} {Class : Type v}
    (ledger : ClassLedger Node Class) :
    conjugateTranspose (conjugateTranspose ledger) = ledger :=
  Matrix.transpose_transpose ledger

@[simp]
theorem relativeNormFold_apply {Node : Type u} {Class : Type v}
    [AddCommGroup Class] (ledger : ClassLedger Node Class)
    (debtor creditor : Node) :
    relativeNormFold ledger debtor creditor =
      ledger debtor creditor + ledger creditor debtor :=
  rfl

/-- On a conjugation-compatible ledger, the matrix fold is literally the
relative norm of its debit entry. -/
theorem relativeNormFold_apply_of_conjugation
    {Node : Type u} {Class : Type v} [AddCommGroup Class]
    (conjugate : Class →+ Class) (ledger : ClassLedger Node Class)
    (hconjugate : ConjugationActsAsTranspose conjugate ledger)
    (debtor creditor : Node) :
    relativeNormFold ledger debtor creditor =
      relativeNormClass conjugate (ledger debtor creditor) := by
  rw [relativeNormFold_apply, relativeNormClass,
    hconjugate debtor creditor]

/-- A nonzero fractional ideal has zero additive class exactly when it is
principal. -/
theorem fractionalIdealClass_eq_zero_iff
    {A L : Type*} [CommRing A] [IsDedekindDomain A]
    [Field L] [Algebra A L] [IsFractionRing A L]
    (I : FractionalIdeal A⁰ L) (hI : I ≠ 0) :
    fractionalIdealClass I hI = 0 ↔
      Submodule.IsPrincipal (I : Submodule A L) := by
  change ClassGroup.mk L (Units.mk0 I hI) = 1 ↔ _
  exact ClassGroup.mk_eq_one_iff

/-- Natural multiples of an additive ideal class are the classes of the
corresponding ideal powers. -/
theorem nsmul_fractionalIdealClass_eq_zero_iff
    {A L : Type*} [CommRing A] [IsDedekindDomain A]
    [Field L] [Algebra A L] [IsFractionRing A L]
    (I : FractionalIdeal A⁰ L) (hI : I ≠ 0) (n : ℕ) :
    n • fractionalIdealClass I hI = 0 ↔
      Submodule.IsPrincipal
        ((I ^ n : FractionalIdeal A⁰ L) : Submodule A L) := by
  change (ClassGroup.mk L (Units.mk0 I hI)) ^ n = 1 ↔ _
  rw [← map_pow, ClassGroup.mk_eq_one_iff]
  rfl

/-- Multiplication of nonzero fractional ideals is addition in the additive
class ledger. -/
theorem fractionalIdealClass_mul
    {A L : Type*} [CommRing A] [IsDedekindDomain A]
    [Field L] [Algebra A L] [IsFractionRing A L]
    (I J : FractionalIdeal A⁰ L) (hI : I ≠ 0) (hJ : J ≠ 0) :
    fractionalIdealClass (I * J) (mul_ne_zero hI hJ) =
      fractionalIdealClass I hI + fractionalIdealClass J hJ := by
  change ClassGroup.mk L (Units.mk0 (I * J) (mul_ne_zero hI hJ)) =
    ClassGroup.mk L (Units.mk0 I hI) *
      ClassGroup.mk L (Units.mk0 J hJ)
  rw [← map_mul]
  apply congrArg (ClassGroup.mk L)
  ext
  rfl

private noncomputable def integralIdealClass
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (I : Ideal R) (hI : I ≠ 0) :
    Additive (ClassGroup R) :=
  Additive.ofMul
    (ClassGroup.mk0
      ⟨I, mem_nonZeroDivisors_iff_ne_zero.2 hI⟩)

private theorem integralIdealClass_eq_zero_iff
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (I : Ideal R) (hI : I ≠ 0) :
    integralIdealClass I hI = 0 ↔ I.IsPrincipal := by
  change ClassGroup.mk0
      ⟨I, mem_nonZeroDivisors_iff_ne_zero.2 hI⟩ = 1 ↔ _
  exact ClassGroup.mk0_eq_one_iff (R := R)
    (mem_nonZeroDivisors_iff_ne_zero.2 hI)

private theorem nsmul_integralIdealClass_eq_zero_iff
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (I : Ideal R) (hI : I ≠ 0) (n : ℕ) :
    n • integralIdealClass I hI = 0 ↔ (I ^ n).IsPrincipal := by
  change (ClassGroup.mk0
      ⟨I, mem_nonZeroDivisors_iff_ne_zero.2 hI⟩) ^ n = 1 ↔ _
  rw [← map_pow, ClassGroup.mk0_eq_one_iff]
  rfl

/-- A relative norm is principal when the original ideal has principal
`p`th power and `p` is coprime to the base class-group cardinality.

This is the class-number half of Vandiver's relative-norm fold.  It kills
only the norm class of the selected ideal. -/
theorem relativeNorm_isPrincipal_of_coprime_card
    {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Finite R S] [IsTorsionFree R S]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Fintype (ClassGroup R)]
    {p : ℕ} (hp : p.Coprime (Fintype.card (ClassGroup R)))
    (I : Ideal S) (hI : I ≠ 0)
    (a : S) (hpow : I ^ p = Ideal.span {a}) :
    (Ideal.relNorm R I).IsPrincipal := by
  have hnorm_ne : Ideal.relNorm R I ≠ 0 := by
    intro hnorm
    apply hI
    exact Ideal.relNorm_eq_bot_iff.mp hnorm
  apply (integralIdealClass_eq_zero_iff
    (Ideal.relNorm R I) hnorm_ne).mp
  have hpowPrincipal : ((Ideal.relNorm R I) ^ p).IsPrincipal := by
    refine ⟨Algebra.intNorm R S a, ?_⟩
    change (Ideal.relNorm R I) ^ p =
      Ideal.span {Algebra.intNorm R S a}
    calc
      (Ideal.relNorm R I) ^ p =
          Ideal.relNorm R (I ^ p) :=
        (map_pow (Ideal.relNorm R) I p).symm
      _ = Ideal.relNorm R (Ideal.span {a}) := by rw [hpow]
      _ = Ideal.span {Algebra.intNorm R S a} :=
        Ideal.relNorm_singleton (R := R) a
  have hclassPow :
      p • integralIdealClass (Ideal.relNorm R I) hnorm_ne = 0 :=
    (nsmul_integralIdealClass_eq_zero_iff
      (R := R) (Ideal.relNorm R I) hnorm_ne p).mpr hpowPrincipal
  change ClassGroup.mk0
      ⟨Ideal.relNorm R I,
        mem_nonZeroDivisors_iff_ne_zero.2 hnorm_ne⟩ = 1
  rw [← orderOf_eq_one_iff]
  exact Nat.eq_one_of_dvd_coprimes hp
    (orderOf_dvd_iff_pow_eq_one.mpr hclassPow)
    orderOf_dvd_card

private theorem product_isPrincipal_of_relativeNormFold
    {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Finite R S] [IsTorsionFree R S]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Fintype (ClassGroup R)]
    {p : ℕ} (hp : p.Coprime (Fintype.card (ClassGroup R)))
    (I J : Ideal S) (hI : I ≠ 0)
    (a : S) (hpow : I ^ p = Ideal.span {a})
    (hfold :
      Ideal.map (algebraMap R S) (Ideal.relNorm R I) = I * J) :
    (I * J).IsPrincipal := by
  obtain ⟨b, hb⟩ :=
    relativeNorm_isPrincipal_of_coprime_card
      (R := R) (S := S) hp I hI a hpow
  refine ⟨algebraMap R S b, ?_⟩
  change I * J = Ideal.span {algebraMap R S b}
  calc
    I * J =
        Ideal.map (algebraMap R S) (Ideal.relNorm R I) :=
      hfold.symm
    _ = Ideal.map (algebraMap R S) (Ideal.span {b}) := by
      rw [hb]
    _ = Ideal.span {algebraMap R S b} := by
      rw [Ideal.map_span, Set.image_singleton]

/-- The ideal-theoretic relative norm realizes a zero class-ledger fold.

The arithmetic input is the concrete state equality identifying the
extension of `relNorm I` with the debit/receivable product `I * J`; the
theorem does not assume the desired class relation. -/
theorem relativeNormFold_class_eq_zero_of_coprime_card
    {R S L : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Finite R S] [IsTorsionFree R S]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Fintype (ClassGroup R)]
    [Field L] [Algebra S L] [IsFractionRing S L]
    {p : ℕ} (hp : p.Coprime (Fintype.card (ClassGroup R)))
    (I J : Ideal S) (hI : I ≠ 0) (hJ : J ≠ 0)
    (a : S) (hpow : I ^ p = Ideal.span {a})
    (hfold :
      Ideal.map (algebraMap R S) (Ideal.relNorm R I) = I * J) :
    fractionalIdealClass
        (I : FractionalIdeal S⁰ L)
        (FractionalIdeal.coeIdeal_ne_zero.mpr hI) +
      fractionalIdealClass
        (J : FractionalIdeal S⁰ L)
        (FractionalIdeal.coeIdeal_ne_zero.mpr hJ) = 0 := by
  rw [← fractionalIdealClass_mul]
  apply (fractionalIdealClass_eq_zero_iff _ _).mpr
  rw [← FractionalIdeal.coeIdeal_mul]
  exact (IsFractionRing.coeSubmodule_isPrincipal
    (R := S) (K := L) (I := I * J)).mpr
      (product_isPrincipal_of_relativeNormFold
        (R := R) (S := S) hp I J hI a hpow hfold)

noncomputable section CMRelativeNorm

variable {K : Type*} [Field K] [NumberField K]
  [NumberField.IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

local instance :
    Algebra (FractionRing (𝓞 K⁺)) (FractionRing (𝓞 K)) :=
  FractionRing.liftAlgebra (𝓞 K⁺) (FractionRing (𝓞 K))

private theorem algebraMap_intNorm_eq_mul_conj (a : 𝓞 K) :
    algebraMap (𝓞 K⁺) (𝓞 K)
        (Algebra.intNorm (𝓞 K⁺) (𝓞 K) a) =
      a * NumberField.IsCMField.ringOfIntegersComplexConj K a := by
  classical
  apply NumberField.RingOfIntegers.ext
  change algebraMap K⁺ K
      (algebraMap (𝓞 K⁺) K⁺
        (Algebra.intNorm (𝓞 K⁺) (𝓞 K) a)) =
    (a : K) * NumberField.IsCMField.complexConj K (a : K)
  rw [Algebra.algebraMap_intNorm
    (A := 𝓞 K⁺) (K := K⁺) (L := K) (B := 𝓞 K)]
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

private theorem map_relativeNorm_le_mul_conjugate
    (I : Ideal (𝓞 K)) :
    Ideal.map (algebraMap (𝓞 K⁺) (𝓞 K))
        (Ideal.relNorm (𝓞 K⁺) I) ≤
      I * I.map
        (NumberField.IsCMField.ringOfIntegersComplexConj K) := by
  rw [Ideal.map_relNorm, Ideal.span_le]
  rintro _ ⟨x, hx, rfl⟩
  rw [Function.comp_apply, algebraMap_intNorm_eq_mul_conj]
  exact Ideal.mul_mem_mul hx
    (Ideal.mem_map_of_mem
      (NumberField.IsCMField.ringOfIntegersComplexConj K) hx)

private theorem absNorm_map_conjugate (I : Ideal (𝓞 K)) :
    Ideal.absNorm
        (I.map (NumberField.IsCMField.ringOfIntegersComplexConj K)) =
      Ideal.absNorm I := by
  let σ :
      (𝓞 K) ≃ₐ[ℤ] (𝓞 K) :=
    (NumberField.IsCMField.ringOfIntegersComplexConj K).restrictScalars ℤ
  calc
    Ideal.absNorm
        (I.map (NumberField.IsCMField.ringOfIntegersComplexConj K)) =
        Ideal.absNorm (Ideal.relNorm ℤ
          (I.map (NumberField.IsCMField.ringOfIntegersComplexConj K))) :=
      (Ideal.absNorm_relNorm ℤ (𝓞 K) _).symm
    _ = Ideal.absNorm (Ideal.relNorm ℤ I) := by
      rw [show
        I.map (NumberField.IsCMField.ringOfIntegersComplexConj K) =
          I.map σ from rfl,
        Ideal.relNorm_map_algEquiv]
    _ = Ideal.absNorm I :=
      Ideal.absNorm_relNorm ℤ (𝓞 K) I

private theorem fractionRing_finrank_eq_two :
    Module.finrank
        (FractionRing (𝓞 K⁺)) (FractionRing (𝓞 K)) = 2 := by
  rw [Algebra.finrank_eq_of_equiv_equiv
    (FractionRing.algEquiv (𝓞 K⁺) K⁺).toRingEquiv
    (FractionRing.algEquiv (𝓞 K) K).toRingEquiv (by
      ext x
      exact IsFractionRing.algEquiv_commutes
        (FractionRing.algEquiv (𝓞 K⁺) K⁺)
        (FractionRing.algEquiv (𝓞 K) K) x)]
  exact Algebra.IsQuadraticExtension.finrank_eq_two K⁺ K

private theorem absNorm_map_relativeNorm (I : Ideal (𝓞 K)) :
    Ideal.absNorm
        (Ideal.map (algebraMap (𝓞 K⁺) (𝓞 K))
          (Ideal.relNorm (𝓞 K⁺) I)) =
      Ideal.absNorm I ^ 2 := by
  rw [Ideal.absNorm_algebraMap, fractionRing_finrank_eq_two,
    Ideal.absNorm_relNorm]

private theorem absNorm_mul_conjugate (I : Ideal (𝓞 K)) :
    Ideal.absNorm
        (I * I.map
          (NumberField.IsCMField.ringOfIntegersComplexConj K)) =
      Ideal.absNorm I ^ 2 := by
  rw [map_mul, absNorm_map_conjugate]
  simp [pow_two]

omit [NumberField.IsCMField K] in
private theorem ideal_eq_of_le_of_absNorm_eq
    {I J : Ideal (𝓞 K)} (hI : I ≠ 0)
    (hle : I ≤ J) (hnorm : Ideal.absNorm I = Ideal.absNorm J) :
    I = J := by
  have hdvd : J ∣ I := Ideal.dvd_iff_le.mpr hle
  obtain ⟨Q, hQ⟩ := hdvd
  have hJ : J ≠ 0 := by
    intro hz
    apply hI
    rw [hz, zero_mul] at hQ
    exact hQ
  have hnormJ : Ideal.absNorm J ≠ 0 := by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff]
    exact hJ
  have hmul :
      Ideal.absNorm J * Ideal.absNorm Q =
        Ideal.absNorm J * 1 := by
    rw [← map_mul, ← hQ, hnorm]
    simp
  have hQnorm : Ideal.absNorm Q = 1 :=
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hnormJ) hmul
  have hQtop : Q = ⊤ :=
    Ideal.absNorm_eq_one_iff.mp hQnorm
  rw [hQ, hQtop]
  simp

/-- In a CM field, extending the real relative norm of a nonzero ideal is
the product of that ideal with its complex-conjugate transpose. -/
theorem map_relativeNorm_eq_mul_conjugate
    (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    Ideal.map (algebraMap (𝓞 K⁺) (𝓞 K))
        (Ideal.relNorm (𝓞 K⁺) I) =
      I * I.map
        (NumberField.IsCMField.ringOfIntegersComplexConj K) := by
  apply ideal_eq_of_le_of_absNorm_eq
  · intro hz
    have hnormzero :
        Ideal.absNorm
            (Ideal.map (algebraMap (𝓞 K⁺) (𝓞 K))
              (Ideal.relNorm (𝓞 K⁺) I)) = 0 := by
      rw [hz]
      exact Ideal.absNorm_bot
    rw [absNorm_map_relativeNorm] at hnormzero
    have hnormI : Ideal.absNorm I ≠ 0 := by
      rw [ne_eq, Ideal.absNorm_eq_zero_iff]
      exact hI
    exact hnormI (Nat.pow_eq_zero.mp hnormzero).1
  · exact map_relativeNorm_le_mul_conjugate I
  · rw [absNorm_map_relativeNorm, absNorm_mul_conjugate]

/-- The concrete CM conjugate pair has zero folded class whenever the real
class-group order is coprime to `p` and the selected ideal has the allocated
principal `p`th power. -/
theorem conjugate_class_fold_eq_zero_of_coprime_card
    {p : ℕ}
    (hp :
      p.Coprime
        (Fintype.card (ClassGroup (𝓞 K⁺))))
    (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (a : 𝓞 K) (hpow : I ^ p = Ideal.span {a}) :
    fractionalIdealClass
        (I : FractionalIdeal (𝓞 K)⁰ K)
        (FractionalIdeal.coeIdeal_ne_zero.mpr hI) +
      fractionalIdealClass
        (I.map
            (NumberField.IsCMField.ringOfIntegersComplexConj K) :
          FractionalIdeal (𝓞 K)⁰ K)
        (FractionalIdeal.coeIdeal_ne_zero.mpr (by
          intro hz
          apply hI
          exact
            (Ideal.map_eq_bot_iff_of_injective
              (NumberField.IsCMField.ringOfIntegersComplexConj K).injective).mp
                hz)) =
      0 := by
  apply relativeNormFold_class_eq_zero_of_coprime_card
    (R := 𝓞 K⁺) (S := 𝓞 K) (L := K) hp
    I
    (I.map (NumberField.IsCMField.ringOfIntegersComplexConj K))
    hI
    (by
      intro hz
      apply hI
      exact
        (Ideal.map_eq_bot_iff_of_injective
          (NumberField.IsCMField.ringOfIntegersComplexConj K).injective).mp hz)
    a hpow
  exact map_relativeNorm_eq_mul_conjugate I hI

end CMRelativeNorm

/-- **Odd-torsion netting.** Vandiver's relations (7a) and (7d) kill the
two state classes without asserting that the whole class-group component
vanishes.

The `p`-torsion equation changes `(p - 1) • receivable` into
`-receivable`, so (7a) says the two classes agree.  The relative-norm fold
(7d) says they are negatives.  Oddness then eliminates the remaining
two-torsion state class. -/
theorem odd_torsion_netting
    {Class : Type v} [AddCommGroup Class] {p : ℕ}
    (hodd : Odd p) (debit receivable : Class)
    (htorsion : p • receivable = 0)
    (sevenA : debit + (p - 1) • receivable = 0)
    (sevenD : debit + receivable = 0) :
    debit = 0 ∧ receivable = 0 := by
  have hpred_add : (p - 1) • receivable + receivable = 0 := by
    calc
      (p - 1) • receivable + receivable =
          ((p - 1) + 1) • receivable := by
            rw [add_nsmul, one_nsmul]
      _ = p • receivable := by
        rw [Nat.sub_add_cancel (Nat.one_le_of_lt hodd.pos)]
      _ = 0 := htorsion
  have hpred : (p - 1) • receivable = -receivable :=
    eq_neg_of_add_eq_zero_left hpred_add
  have heq : debit = receivable := by
    apply sub_eq_zero.mp
    simpa only [sub_eq_add_neg, hpred] using sevenA
  have hneg : debit = -receivable :=
    eq_neg_of_add_eq_zero_left sevenD
  have hself_neg : receivable = -receivable :=
    heq.symm.trans hneg
  have htwo : 2 • receivable = 0 := by
    rw [two_nsmul]
    calc
      receivable + receivable = -receivable + receivable := by
        exact congrArg (fun c ↦ c + receivable) hself_neg
      _ = 0 := neg_add_cancel receivable
  obtain ⟨k, rfl⟩ := hodd
  have hreceivable : receivable = 0 := by
    simpa only [add_nsmul, mul_nsmul, htwo, nsmul_zero,
      zero_add, one_nsmul] using htorsion
  exact ⟨heq.trans hreceivable, hreceivable⟩

end Fermat.Conservation.Credit.Fold
