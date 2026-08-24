import Fermat.Descent.Irregular.CanonicalKummerChannel
import Fermat.Descent.Irregular.VandiverData
import KummerCriterion.CyclotomicUnits.KummerLogCoefficient.Basic

/-!
# Finite Bernoulli-channel supports

A complete low Bernoulli scan naturally produces a finite list of possible
irregular indices.  This module packages that list independently of every
lifted Bernoulli computation and auxiliary split prime, and turns it into the
corresponding family of canonical Kummer rows.

The resulting projection has type

`(Fin (kummerLogRank p) → ZMod p) → (Fin N → ZMod p)`.

Thus `N = 0`, `N = 1`, and arbitrary finite channel families use the same
interface.  Completeness is the one-way support statement needed by descent;
the optional exact wrapper separately records that every listed candidate is
genuinely irregular.
-/

namespace Fermat.Irregular

noncomputable section

open Fermat.Irregular.AuxiliaryResidueChannels
open KummerCriterion.CyclotomicUnits

/-- A finite, duplicate-free cover of every irregular Bernoulli index in the
classical range.  The listed indices need not themselves be proved irregular;
that stronger assertion is kept in `ExactBernoulliChannelSupport`. -/
structure BernoulliChannelSupport (p N : ℕ) [Fact p.Prime] where
  index : Fin N → ℕ
  index_mem : ∀ i, index i ∈ VandiverData.indices p
  index_injective : Function.Injective index
  complete : ∀ k, k ∈ VandiverData.indices p →
    (p : ℤ) ∣ (bernoulli k).num → ∃ i, index i = k

namespace BernoulliChannelSupport

variable {p N : ℕ} [Fact p.Prime]

/-- The zero-based Kummer row corresponding to a listed even Bernoulli
index `k`: mathematical Kummer row `k / 2`, hence Lean row `k / 2 - 1`. -/
def row (S : BernoulliChannelSupport p N) (i : Fin N) :
    Fin (kummerLogRank p) := by
  have hi : 2 ≤ S.index i ∧ S.index i ≤ p - 3 ∧ Even (S.index i) := by
    simpa [VandiverData.indices, and_assoc] using S.index_mem i
  refine ⟨S.index i / 2 - 1, ?_⟩
  have hhalf_pos : 0 < S.index i / 2 := by
    omega
  have hhalf_le : S.index i / 2 ≤ (p - 3) / 2 :=
    Nat.div_le_div_right hi.2.1
  change S.index i / 2 - 1 < (p - 3) / 2
  omega

/-- Converting a listed Bernoulli index to a Kummer row and back recovers the
exact original index. -/
@[simp] theorem two_mul_kummerLogRowIndex_row
    (S : BernoulliChannelSupport p N) (i : Fin N) :
    2 * kummerLogRowIndex (p := p) (S.row i) = S.index i := by
  have hi : 2 ≤ S.index i ∧ S.index i ≤ p - 3 ∧ Even (S.index i) := by
    simpa [VandiverData.indices, and_assoc] using S.index_mem i
  obtain ⟨k, hk⟩ := hi.2.2
  change 2 * (S.index i / 2 - 1 + 1) = S.index i
  omega

/-- Distinct listed Bernoulli indices select distinct Kummer rows. -/
theorem row_injective (S : BernoulliChannelSupport p N) :
    Function.Injective S.row := by
  intro i j hij
  apply S.index_injective
  rw [← S.two_mul_kummerLogRowIndex_row i,
    ← S.two_mul_kummerLogRowIndex_row j, hij]

/-- The Kummer rows selected by the finite Bernoulli support. -/
def ExceptionalRow (S : BernoulliChannelSupport p N)
    (j : Fin (kummerLogRank p)) : Prop :=
  ∃ i, S.row i = j

/-- Every Bernoulli-divisible Kummer row belongs to the listed support. -/
theorem exceptionalRow_of_dvd
    (S : BernoulliChannelSupport p N)
    (j : Fin (kummerLogRank p))
    (hdiv : (p : ℤ) ∣
      (bernoulli (2 * kummerLogRowIndex (p := p) j)).num) :
    S.ExceptionalRow j := by
  have hmem : 2 * kummerLogRowIndex (p := p) j ∈
      VandiverData.indices p := by
    simp only [VandiverData.indices, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by
      have := kummerLogRowIndex_one_le (p := p) j
      omega, two_mul_kummerLogRowIndex_le_sub_three (p := p) j⟩,
      even_two_mul _⟩
  obtain ⟨i, hi⟩ := S.complete _ hmem hdiv
  refine ⟨i, ?_⟩
  apply Fin.ext
  have hindex := S.two_mul_kummerLogRowIndex_row i
  rw [hi] at hindex
  simp only [kummerLogRowIndex] at hindex
  omega

/-- The vector of intrinsic Kummer-character projections selected by the
Bernoulli support.  Its output dimension is exactly the support size `N`. -/
def projection (S : BernoulliChannelSupport p N) (hp_three : 3 ≤ p)
    (e : Fin (kummerLogRank p) → ZMod p) : Fin N → ZMod p :=
  fun i ↦ canonicalKummerChannel p hp_three (S.row i) e

@[simp] theorem projection_apply
    (S : BernoulliChannelSupport p N) (hp_three : 3 ≤ p)
    (e : Fin (kummerLogRank p) → ZMod p) (i : Fin N) :
    S.projection hp_three e i =
      canonicalKummerChannel p hp_three (S.row i) e :=
  rfl

/-- Vector-valued projection vanishing is equivalent to vanishing of every
listed canonical Kummer channel. -/
theorem projection_eq_zero_iff
    (S : BernoulliChannelSupport p N) (hp_three : 3 ≤ p)
    (e : Fin (kummerLogRank p) → ZMod p) :
    S.projection hp_three e = 0 ↔
      ∀ i, canonicalKummerChannel p hp_three (S.row i) e = 0 := by
  constructor
  · intro h i
    exact congrFun h i
  · intro h
    funext i
    exact h i

end BernoulliChannelSupport

/-- A finite Bernoulli support known to be exact: completeness says that no
irregular index is omitted, while `sound` says that no listed index is a
false-positive candidate.  Descent needs only the underlying support. -/
structure ExactBernoulliChannelSupport (p N : ℕ) [Fact p.Prime] where
  support : BernoulliChannelSupport p N
  sound : ∀ i, (p : ℤ) ∣ (bernoulli (support.index i)).num

end

end Fermat.Irregular
