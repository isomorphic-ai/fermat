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
import Mathlib.RingTheory.ClassGroup.Basic

open scoped nonZeroDivisors

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
