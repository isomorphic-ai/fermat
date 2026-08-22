/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The prime-parametric cyclic extension C_p → C_(p²) → C_p

For every prime `p`, this module constructs reduction from `C_(p²)` to
`C_p`, its standard-representative section, and the kernel embedding given
by multiplication by `p`.  It proves exactness and computes the failure of
the section to preserve multiplication as the same carry cocycle used by
`PrimeCyclicH2`.

These are symbolic arithmetic proofs.  No finite-prime `decide` computation,
local-field input, or liftability assumption occurs here.
-/
import Fermat.Experiments.Conservation.PrimeCyclicH2

noncomputable section

namespace Fermat.Conservation.PrimeCyclicExtension

open Fermat.Conservation.PrimeCyclicH2

variable (p : ℕ) [Fact p.Prime]

local instance : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
local instance : NeZero (p ^ 2) :=
  ⟨pow_ne_zero 2 (Fact.out : Nat.Prime p).ne_zero⟩

/-- The multiplicative cyclic group of order `p`. -/
abbrev CyclicGroup := Multiplicative (ZMod p)

/-- The multiplicative cyclic group of order `p²`. -/
abbrev CyclicGroupSquared := Multiplicative (ZMod (p ^ 2))

local instance : TopologicalSpace (CyclicGroup p) := ⊥
local instance : DiscreteTopology (CyclicGroup p) := ⟨rfl⟩
local instance : TopologicalSpace (CyclicGroupSquared p) := ⊥
local instance : DiscreteTopology (CyclicGroupSquared p) := ⟨rfl⟩

lemma p_dvd_p_sq (p : ℕ) : p ∣ p ^ 2 := by
  exact dvd_pow_self p (by omega)

/-- Reduction modulo `p` from the additive cyclic group of order `p²`. -/
def reduction : CyclicGroupSquared p →ₜ* CyclicGroup p where
  toFun x := Multiplicative.ofAdd
    (ZMod.castHom (p_dvd_p_sq p) (ZMod p) x.toAdd)
  map_one' := by simp
  map_mul' x y := by simp
  continuous_toFun := continuous_of_discreteTopology

/-- The least-nonnegative-representative section.  It is continuous but is
not generally a homomorphism. -/
def standardSection : C(CyclicGroup p, CyclicGroupSquared p) where
  toFun x := Multiplicative.ofAdd (x.toAdd.val : ZMod (p ^ 2))
  continuous_toFun := continuous_of_discreteTopology

/-- The underlying function of the kernel embedding, multiplication by
`p` on standard representatives. -/
def kernelEmbedValue : CyclicGroup p → CyclicGroupSquared p := fun x =>
  Multiplicative.ofAdd ((p * x.toAdd.val : ℕ) : ZMod (p ^ 2))

@[simp]
theorem reduction_standardSection (x : CyclicGroup p) :
    reduction p (standardSection p x) = x := by
  apply Multiplicative.toAdd.injective
  have hle : p ≤ p ^ 2 := by
    nlinarith [(Fact.out : Nat.Prime p).two_le]
  change ZMod.castHom (p_dvd_p_sq p) (ZMod p)
      (x.toAdd.val : ZMod (p ^ 2)) = x.toAdd
  rw [ZMod.castHom_apply, ← ZMod.cast_eq_val x.toAdd]
  exact ZMod.cast_cast_zmod_of_le hle x.toAdd

@[simp]
theorem reduction_kernelEmbedValue (x : CyclicGroup p) :
    reduction p (kernelEmbedValue p x) = 1 := by
  apply Multiplicative.toAdd.injective
  change ZMod.castHom (p_dvd_p_sq p) (ZMod p)
      ((p * x.toAdd.val : ℕ) : ZMod (p ^ 2)) = 0
  rw [ZMod.castHom_apply,
    ZMod.cast_natCast (R := ZMod p) (p_dvd_p_sq p)]
  rw [Nat.cast_mul, ZMod.natCast_self, zero_mul]

/-- Multiplication by `p` respects addition of representatives modulo
`p²`. -/
lemma cast_p_mul_val_add (x y : ZMod p) :
    ((p * (x + y).val : ℕ) : ZMod (p ^ 2)) =
      ((p * x.val : ℕ) : ZMod (p ^ 2)) +
        ((p * y.val : ℕ) : ZMod (p ^ 2)) := by
  by_cases h : p ≤ x.val + y.val
  · rw [ZMod.val_add_of_le h]
    have hp : p * p ≤ p * (x.val + y.val) :=
      Nat.mul_le_mul_left p h
    rw [Nat.mul_sub_left_distrib]
    rw [Nat.cast_sub hp]
    push_cast
    rw [show (p : ZMod (p ^ 2)) * p = 0 by
      rw [← Nat.cast_mul, ← pow_two, ZMod.natCast_self]]
    ring
  · have hlt : x.val + y.val < p := lt_of_not_ge h
    rw [ZMod.val_add_of_lt hlt]
    push_cast
    ring

/-- Multiplication by `p` embeds `C_p` continuously into `C_(p²)`. -/
def kernelEmbed : CyclicGroup p →ₜ* CyclicGroupSquared p where
  toFun := kernelEmbedValue p
  map_one' := by
    apply Multiplicative.toAdd.injective
    simp [kernelEmbedValue]
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    exact cast_p_mul_val_add p x.toAdd y.toAdd
  continuous_toFun := continuous_of_discreteTopology

/-- The defect of the standard section is exactly the prime-parametric carry
cocycle. -/
theorem standardSection_mul (x y : CyclicGroup p) :
    standardSection p x * standardSection p y =
      standardSection p (x * y) *
        kernelEmbed p
          (Multiplicative.ofAdd (carry p x.toAdd y.toAdd)) := by
  apply Multiplicative.toAdd.injective
  change ((x.toAdd.val : ℕ) : ZMod (p ^ 2)) +
      (y.toAdd.val : ℕ) =
    (((x.toAdd + y.toAdd).val : ℕ) : ZMod (p ^ 2)) +
      ((p * (carry p x.toAdd y.toAdd).val : ℕ) : ZMod (p ^ 2))
  by_cases h : p ≤ x.toAdd.val + y.toAdd.val
  · rw [ZMod.val_add_of_le h]
    simp only [carry, if_pos h, ZMod.val_one]
    have hp : p ≤ x.toAdd.val + y.toAdd.val := h
    rw [Nat.cast_sub hp]
    push_cast
    ring
  · have hlt : x.toAdd.val + y.toAdd.val < p := lt_of_not_ge h
    rw [ZMod.val_add_of_lt hlt]
    simp only [carry, if_neg h, ZMod.val_zero, mul_zero, Nat.cast_zero,
      add_zero]
    push_cast
    ring

/-- Divide a kernel element by `p` using standard representatives. -/
def kernelCoordinate (z : CyclicGroupSquared p) : CyclicGroup p :=
  Multiplicative.ofAdd ((z.toAdd.val / p : ℕ) : ZMod p)

/-- Re-embedding the coordinate of an element killed by reduction recovers
that element. -/
theorem kernelEmbed_kernelCoordinate
    (z : CyclicGroupSquared p) (hz : reduction p z = 1) :
    kernelEmbed p (kernelCoordinate p z) = z := by
  have hzero : (z.toAdd.val : ZMod p) = 0 := by
    have h := congrArg Multiplicative.toAdd hz
    change ZMod.castHom (p_dvd_p_sq p) (ZMod p) z.toAdd = 0 at h
    rw [ZMod.castHom_apply, ZMod.cast_eq_val] at h
    exact h
  have hdiv : p ∣ z.toAdd.val := by
    exact (ZMod.natCast_eq_zero_iff z.toAdd.val p).mp hzero
  apply Multiplicative.toAdd.injective
  change ((p * (((z.toAdd.val / p : ℕ) : ZMod p).val) : ℕ) :
      ZMod (p ^ 2)) = z.toAdd
  have hquotlt : z.toAdd.val / p < p := by
    have hzlt : z.toAdd.val < p ^ 2 := z.toAdd.val_lt
    apply (Nat.div_lt_iff_lt_mul (Fact.out : Nat.Prime p).pos).2
    simpa [pow_two] using hzlt
  rw [ZMod.val_natCast_of_lt hquotlt]
  rw [Nat.mul_div_cancel' hdiv, ZMod.natCast_zmod_val]

/-- Kernel coordinate is a left inverse to the embedding. -/
@[simp]
theorem kernelCoordinate_kernelEmbed (x : CyclicGroup p) :
    kernelCoordinate p (kernelEmbed p x) = x := by
  apply Multiplicative.toAdd.injective
  change (((((p * x.toAdd.val : ℕ) : ZMod (p ^ 2)).val / p : ℕ) :
      ZMod p)) = x.toAdd
  have hlt : p * x.toAdd.val < p ^ 2 := by
    rw [pow_two]
    exact Nat.mul_lt_mul_of_pos_left x.toAdd.val_lt
      (Fact.out : Nat.Prime p).pos
  rw [ZMod.val_natCast_of_lt hlt]
  rw [mul_comm p x.toAdd.val]
  rw [Nat.mul_div_left _ (Fact.out : Nat.Prime p).pos]
  exact ZMod.natCast_zmod_val x.toAdd

/-- The kernel embedding is injective. -/
theorem kernelEmbed_injective : Function.Injective (kernelEmbed p) := by
  intro x y hxy
  rw [← kernelCoordinate_kernelEmbed p x,
    ← kernelCoordinate_kernelEmbed p y, hxy]

/-- Reduction is surjective, with the standard section as a set-theoretic
right inverse. -/
theorem reduction_surjective : Function.Surjective (reduction p) := by
  intro x
  exact ⟨standardSection p x, reduction_standardSection p x⟩

/-- Pointwise exactness of the kernel embedding and reduction. -/
theorem reduction_eq_one_iff_exists_kernelEmbed
    (z : CyclicGroupSquared p) :
    reduction p z = 1 ↔ ∃ x : CyclicGroup p, kernelEmbed p x = z := by
  constructor
  · intro hz
    exact ⟨kernelCoordinate p z, kernelEmbed_kernelCoordinate p z hz⟩
  · rintro ⟨x, rfl⟩
    exact reduction_kernelEmbedValue p x

/-- The image of multiplication by `p` is exactly the kernel of reduction. -/
theorem kernelEmbed_range_eq_reduction_ker :
    (kernelEmbed p).toMonoidHom.range = (reduction p).toMonoidHom.ker := by
  ext z
  rw [MonoidHom.mem_range, MonoidHom.mem_ker]
  exact (reduction_eq_one_iff_exists_kernelEmbed p z).symm

end Fermat.Conservation.PrimeCyclicExtension
