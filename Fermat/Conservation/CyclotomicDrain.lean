/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# The generic prime-cyclotomic conservation drain

This file reuses the route-neutral absolute norm charge developed in the
seventh conservation spine.  For an arbitrary prime `p`, the ramified
element `λ = 1 - ζₚ` has charge `p`; consequently its `n`th power has charge
`p ^ n`, strictly increasing with `n`.

Only the narrow N7 spine is imported.  No fixed-exponent endpoint or
classical second-case implementation enters this cone.
-/
import Fermat.Seven.Conservation.Spine

open scoped NumberField

namespace Fermat.Conservation.CyclotomicDrain

noncomputable section

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K]
variable [IsCyclotomicExtension {p} ℚ K]
variable {ζ : K}

/-- The generic drain charge is literally the absolute integral norm charge
from the N7 stock spine. -/
abbrev charge (z : 𝓞 K) : ℕ :=
  Fermat.Seven.Conservation.charge z

/-- The prime-cyclotomic ramified element in the conservation orientation. -/
def lambda (hζ : IsPrimitiveRoot ζ p) : 𝓞 K :=
  1 - hζ.toInteger

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- Stock-spine orientation: the conservation drain differs from the
standard arithmetic prime `ζₚ - 1` only by the unit `-1`. -/
theorem lambda_eq_neg_zeta_sub_one (hζ : IsPrimitiveRoot ζ p) :
    lambda hζ = -(hζ.toInteger - 1) := by
  simp only [lambda]
  ring

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- Stock-spine reuse of multiplicative conservation on powers. -/
theorem charge_pow (z : 𝓞 K) (n : ℕ) :
    charge (z ^ n) = charge z ^ n :=
  Fermat.Seven.Conservation.charge_pow z n

/-- Stock-spine λ-charge law: at every prime conductor, one ramified
quantum has absolute integral norm charge exactly `p`. -/
theorem lambda_charge (hζ : IsPrimitiveRoot ζ p) :
    charge (lambda hζ) = p := by
  rw [lambda_eq_neg_zeta_sub_one]
  change
    Fermat.Seven.Conservation.charge (-(hζ.toInteger - 1)) = p
  rw [show -(hζ.toInteger - 1) =
      (-1 : 𝓞 K) * (hζ.toInteger - 1) by ring,
    Fermat.Seven.Conservation.charge_mul]
  have hneg : Fermat.Seven.Conservation.charge (-1 : 𝓞 K) = 1 := by
    simpa using
      Fermat.Seven.Conservation.charge_unit (K := K)
        (-1 : (𝓞 K)ˣ)
  rw [hneg, one_mul]
  simp only [Fermat.Seven.Conservation.charge]
  by_cases hp2 : p = 2
  · subst p
    rw [hζ.norm_toInteger_sub_one_of_eq_two]
    norm_num
  · rw [hζ.norm_toInteger_sub_one_of_prime_ne_two' hp2]
    simp

/-- The stock charge stored in `n` copies of the ramified quantum. -/
def drainCharge (hζ : IsPrimitiveRoot ζ p) (n : ℕ) : ℕ :=
  charge ((lambda hζ) ^ n)

/-- Stock-spine evaluation of the generic ramified drain:
`n` quanta carry charge `p ^ n`. -/
theorem drainCharge_eq (hζ : IsPrimitiveRoot ζ p) (n : ℕ) :
    drainCharge hζ n = p ^ n := by
  rw [drainCharge, charge_pow, lambda_charge]

/-- Stock-spine strict drain law: lowering ramified multiplicity strictly
lowers the corresponding absolute norm charge. -/
theorem drainCharge_strictMono (hζ : IsPrimitiveRoot ζ p) :
    StrictMono (drainCharge hζ) := by
  intro m n hmn
  rw [drainCharge_eq, drainCharge_eq]
  exact Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt hmn

/-- One stock-spine ramified step is a strict charge increase; read in the
descent direction, removing that step is a strict drain. -/
theorem drainCharge_step (hζ : IsPrimitiveRoot ζ p) (n : ℕ) :
    drainCharge hζ n < drainCharge hζ (n + 1) :=
  drainCharge_strictMono hζ (Nat.lt_succ_self n)

end

end Fermat.Conservation.CyclotomicDrain
