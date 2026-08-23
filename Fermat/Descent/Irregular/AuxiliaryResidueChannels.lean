import Fermat.Descent.Irregular.CyclicDifferenceMatrixProjection
import Fermat.Descent.Irregular.SelectiveKummerSaturation
import Fermat.Descent.Irregular.CircularUnitResidues

/-!
# Auxiliary-prime residue channels

An auxiliary split prime supplies residue-symbol rows and a Fourier scalar.
The Bernoulli/Kummer character channel detected by those rows is intrinsic to
the exponent: it is a row of Kummer's canonical Vandermonde matrix and does
not depend on the auxiliary prime.

This module records that distinction explicitly. A `Factorization` packages
the exact equality

`q-dependent residue detector = q-dependent scalar * canonical channel`.

Consequently, any two auxiliary-prime detectors with nonzero scalars have
the same zero locus when they target the same canonical row.
-/

open scoped BigOperators Matrix

namespace Fermat.Irregular.AuxiliaryResidueChannels

noncomputable section

open Fermat.Irregular.CyclicDifferenceMatrix
open Fermat.Irregular.CircularUnitResidues
open KummerCriterion.CyclotomicUnits

/-- The canonical, auxiliary-prime-independent Kummer character channel. -/
def canonicalKummerChannel (p : ℕ) [Fact p.Prime] (hp_three : 3 ≤ p)
    (j : Fin (kummerLogRank p))
    (e : Fin (kummerLogRank p) → ZMod p) : ZMod p :=
  (vandermondeTeichmullerEvenSubOneMatrix (p := p) hp_three *ᵥ e) j

/-- A weighted residue functional for an auxiliary-prime certificate,
together with its factorization through one fixed canonical Kummer channel.

The `scalar` and `weights` may depend on `q`. The `channelRow` is a type
parameter, so two receipts can only be compared when they target exactly the
same intrinsic row. -/
structure Factorization (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp_three : 3 ≤ p) (C : Certificate p q)
    (channelRow : Fin (kummerLogRank p)) where
  weights : Fin (kummerLogRank p) → ZMod p
  scalar : ZMod p
  factors : ∀ e : Fin (kummerLogRank p) → ZMod p,
    dotProduct weights (C.matrix *ᵥ e) =
      scalar * canonicalKummerChannel p hp_three channelRow e

namespace Factorization

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
variable {hp_three : 3 ≤ p} {C : Certificate p q}
variable {channelRow : Fin (kummerLogRank p)}

/-- The actual `q`-dependent weighted residue detector. -/
def residueDetector (A : Factorization p q hp_three C channelRow)
    (e : Fin (kummerLogRank p) → ZMod p) : ZMod p :=
  dotProduct A.weights (C.matrix *ᵥ e)

/-- The residue detector is its auxiliary-prime scalar times the canonical
Kummer channel. -/
theorem residueDetector_eq_scalar_mul_canonical
    (A : Factorization p q hp_three C channelRow)
    (e : Fin (kummerLogRank p) → ZMod p) :
    A.residueDetector e =
      A.scalar * canonicalKummerChannel p hp_three channelRow e :=
  A.factors e

/-- A nonzero auxiliary scalar makes detector vanishing equivalent to
vanishing of the intrinsic Kummer channel. -/
theorem residueDetector_eq_zero_iff_canonical
    (A : Factorization p q hp_three C channelRow) (hscalar : A.scalar ≠ 0)
    (e : Fin (kummerLogRank p) → ZMod p) :
    A.residueDetector e = 0 ↔
      canonicalKummerChannel p hp_three channelRow e = 0 := by
  rw [A.residueDetector_eq_scalar_mul_canonical]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hs | hc
    · exact (hscalar hs).elim
    · exact hc
  · intro h
    rw [h, mul_zero]

/-- Projective naturality without a nonvanishing assumption: two
auxiliary-prime detectors on the same canonical channel agree after
cross-multiplication by their possibly different auxiliary scalars. -/
theorem cross_mul_residueDetectors
    {q₁ q₂ : ℕ} [Fact q₁.Prime] [Fact q₂.Prime]
    {C₁ : Certificate p q₁} {C₂ : Certificate p q₂}
    (A₁ : Factorization p q₁ hp_three C₁ channelRow)
    (A₂ : Factorization p q₂ hp_three C₂ channelRow)
    (e : Fin (kummerLogRank p) → ZMod p) :
    A₂.scalar * A₁.residueDetector e =
      A₁.scalar * A₂.residueDetector e := by
  rw [A₁.residueDetector_eq_scalar_mul_canonical,
    A₂.residueDetector_eq_scalar_mul_canonical]
  ring

/-- Two auxiliary-prime receipts on the same Kummer row have equivalent
zero loci as soon as their `q`-dependent scalars are nonzero. -/
theorem detectors_equivalent
    {q₁ q₂ : ℕ} [Fact q₁.Prime] [Fact q₂.Prime]
    {C₁ : Certificate p q₁} {C₂ : Certificate p q₂}
    (A₁ : Factorization p q₁ hp_three C₁ channelRow)
    (A₂ : Factorization p q₂ hp_three C₂ channelRow)
    (h₁ : A₁.scalar ≠ 0) (h₂ : A₂.scalar ≠ 0)
    (e : Fin (kummerLogRank p) → ZMod p) :
    A₁.residueDetector e = 0 ↔ A₂.residueDetector e = 0 := by
  rw [A₁.residueDetector_eq_zero_iff_canonical h₁,
    A₂.residueDetector_eq_zero_iff_canonical h₂]

end Factorization

/-- Generic cyclic constructor. The left Fourier row of a reindexed reduced
difference matrix is the Fourier scalar times the supplied canonical row. -/
theorem cyclic_reindexed_factorization
    {n : ℕ} [NeZero (n + 1)] {R : Type*} [CommRing R] [IsDomain R]
    (row column : Equiv.Perm (Fin n))
    (M : Matrix (Fin n) (Fin n) R)
    (f : Cyc n → R)
    (hM : M = Matrix.reindex row.symm column.symm (differenceMatrix n f))
    (omega : R) (homega : IsPrimitiveRoot omega (n + 1))
    (frequency : Fin n)
    (channel : Fin n → R)
    (halign : ∀ i : Fin n,
      inverseMomentMatrix omega homega.pow_eq_one frequency (column i) =
        channel i)
    (e : Fin n → R) :
    dotProduct
        (fun sourceRow ↦
          positiveMomentMatrix omega homega.pow_eq_one frequency
            (row sourceRow))
        (M *ᵥ e) =
      fourierCoeff omega homega.pow_eq_one f frequency *
        dotProduct channel e := by
  classical
  let P := positiveMomentMatrix omega homega.pow_eq_one
  let I := inverseMomentMatrix omega homega.pow_eq_one
  let eCyclic : Fin n → R := e ∘ column.symm
  have htransport : ∀ r : Fin n,
      (M *ᵥ e) (row.symm r) =
        (differenceMatrix n f *ᵥ eCyclic) r := by
    intro r
    rw [hM]
    exact mulVec_reindex_equiv row column (differenceMatrix n f) e r
  have hleft :
      dotProduct (fun sourceRow ↦ P frequency (row sourceRow)) (M *ᵥ e) =
        (P *ᵥ (differenceMatrix n f *ᵥ eCyclic)) frequency := by
    let L : Fin n → R := fun sourceRow ↦
      P frequency (row sourceRow) * (M *ᵥ e) sourceRow
    let G : Fin n → R := fun r ↦
      P frequency r * (M *ᵥ e) (row.symm r)
    change (∑ sourceRow : Fin n, L sourceRow) =
      ∑ r : Fin n, P frequency r * (differenceMatrix n f *ᵥ eCyclic) r
    calc
      (∑ sourceRow : Fin n, L sourceRow) =
          ∑ sourceRow : Fin n, G (row sourceRow) := by
        apply Finset.sum_congr rfl
        intro sourceRow _
        simp only [L, G, Equiv.symm_apply_apply]
      _ = ∑ r : Fin n, G r := Equiv.sum_comp row G
      _ = ∑ r : Fin n,
          P frequency r * (differenceMatrix n f *ᵥ eCyclic) r := by
        apply Finset.sum_congr rfl
        intro r _
        simp only [G]
        rw [htransport r]
  rw [hleft]
  calc
    (P *ᵥ (differenceMatrix n f *ᵥ eCyclic)) frequency =
        ((P * differenceMatrix n f) *ᵥ eCyclic) frequency := by
      rw [← Matrix.mulVec_mulVec]
    _ = ((Matrix.diagonal (fourierCoeff omega homega.pow_eq_one f) * I) *ᵥ
          eCyclic) frequency := by
      rw [positiveMomentMatrix_mul_differenceMatrix omega homega f]
    _ = fourierCoeff omega homega.pow_eq_one f frequency *
        (I *ᵥ eCyclic) frequency := by
      rw [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
    _ = fourierCoeff omega homega.pow_eq_one f frequency *
        dotProduct channel e := by
      congr 1
      change
        (∑ s : Fin n,
          inverseMomentMatrix omega homega.pow_eq_one frequency s *
            e (column.symm s)) =
          ∑ i : Fin n, channel i * e i
      let F : Fin n → R := fun s ↦
        inverseMomentMatrix omega homega.pow_eq_one frequency s *
          e (column.symm s)
      calc
        (∑ s : Fin n, F s) = ∑ i : Fin n, F (column i) :=
          (Equiv.sum_comp column F).symm
        _ = ∑ i : Fin n, channel i * e i := by
          apply Finset.sum_congr rfl
          intro i _
          dsimp only [F]
          rw [Equiv.symm_apply_apply, halign]

end

end Fermat.Irregular.AuxiliaryResidueChannels
