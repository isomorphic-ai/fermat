/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Native charged descent for exponent six

A primitive sixth-power solution seeds the neutral cubic-state transformer
directly on square coordinates.  This is a fold of state coordinates, not a
use of an exponent-three Fermat proposition: the two possible seeds are

* `(b², -c², a², -1)` when `3 ∣ a`;
* `(a², -c², b², -1)` when `3 ∣ b`.

The resulting oriented state is charged by the native sixth-cyclotomic
quantity `N((1 + ζ₆)^m) = 3^m`.  The neutral transformer lowers `m`, hence
strictly drains that native charge into the shared conservation floor.
-/
import Fermat.Six.Conservation.Entry
import Fermat.Conservation.CubicChargedDescent

namespace Fermat.Six.Conservation

open NumberField IsCyclotomicExtension.Rat.Three
open Fermat.Conservation.CubicChargedDescent

variable {K : Type*} [Field K]
variable {ζ : K} {hζ : IsPrimitiveRoot ζ 3}

local notation3 "λ" => hζ.toInteger - 1

/-- Nondivisibility by three downstairs gives nondivisibility of the square
of the corresponding integer by the ramified prime upstairs. -/
theorem lambda_not_dvd_intCast_sq
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {x : ℤ} (hx : ¬(3 : ℤ) ∣ x) :
    ¬λ ∣ (x : 𝓞 K) ^ 2 := by
  intro hsq
  apply hx
  have hx_upstairs : λ ∣ (x : 𝓞 K) :=
    (hζ.zeta_sub_one_prime'.dvd_pow_iff_dvd (by decide)).mp hsq
  rwa [← Ideal.norm_dvd_iff
      (hζ.prime_norm_toInteger_sub_one_of_prime_ne_two' (by decide)),
    hζ.norm_toInteger_sub_one_of_prime_ne_two' (by decide)] at hx_upstairs

/-- Divisibility by three downstairs puts the square of the corresponding
integer in the ramified channel upstairs. -/
theorem lambda_dvd_intCast_sq
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {x : ℤ} (hx : (3 : ℤ) ∣ x) :
    λ ∣ (x : 𝓞 K) ^ 2 := by
  obtain ⟨k, hk⟩ := hx
  exact dvd_pow
    (dvd_trans hζ.toInteger_sub_one_dvd_prime'
      ⟨k, by simp [hk]⟩)
    (by decide)

namespace PrimitiveSolution

/-- The direct cubic seed when the first sixth-power base carries the
ramified factor three. -/
noncomputable def rawState_of_three_dvd_a
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    (S : PrimitiveSolution)
    (ha : (3 : ℤ) ∣ S.a) (hb : ¬(3 : ℤ) ∣ S.b)
    (hc : ¬(3 : ℤ) ∣ S.c) :
    RawState hζ where
  a := (S.b : 𝓞 K) ^ 2
  b := -((S.c : 𝓞 K) ^ 2)
  c := (S.a : 𝓞 K) ^ 2
  u := -1
  ha := lambda_not_dvd_intCast_sq hb
  hb := fun h ↦ lambda_not_dvd_intCast_sq hc (dvd_neg.mp h)
  hc := pow_ne_zero 2 (by exact_mod_cast S.a_ne_zero)
  coprime :=
    ((IsCoprime.intCast S.pairwise_isCoprime.2.2).pow
      (m := 2) (n := 2)).neg_right
  hcdvd := lambda_dvd_intCast_sq ha
  equation := by
    have heq :
        (S.a : 𝓞 K) ^ 6 + (S.b : 𝓞 K) ^ 6 =
          (S.c : 𝓞 K) ^ 6 := by
      exact_mod_cast S.equation
    change
      ((S.b : 𝓞 K) ^ 2) ^ 3 +
          (-((S.c : 𝓞 K) ^ 2)) ^ 3 =
        (-1 : 𝓞 K) * ((S.a : 𝓞 K) ^ 2) ^ 3
    calc
      _ = (S.b : 𝓞 K) ^ 6 - (S.c : 𝓞 K) ^ 6 := by ring
      _ = -(S.a : 𝓞 K) ^ 6 := by rw [← heq]; ring
      _ = _ := by ring

/-- The direct cubic seed when the second sixth-power base carries the
ramified factor three. -/
noncomputable def rawState_of_three_dvd_b
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    (S : PrimitiveSolution)
    (hb : (3 : ℤ) ∣ S.b) (ha : ¬(3 : ℤ) ∣ S.a)
    (hc : ¬(3 : ℤ) ∣ S.c) :
    RawState hζ where
  a := (S.a : 𝓞 K) ^ 2
  b := -((S.c : 𝓞 K) ^ 2)
  c := (S.b : 𝓞 K) ^ 2
  u := -1
  ha := lambda_not_dvd_intCast_sq ha
  hb := fun h ↦ lambda_not_dvd_intCast_sq hc (dvd_neg.mp h)
  hc := pow_ne_zero 2 (by exact_mod_cast S.b_ne_zero)
  coprime :=
    ((IsCoprime.intCast S.pairwise_isCoprime.2.1).pow
      (m := 2) (n := 2)).neg_right
  hcdvd := lambda_dvd_intCast_sq hb
  equation := by
    have heq :
        (S.a : 𝓞 K) ^ 6 + (S.b : 𝓞 K) ^ 6 =
          (S.c : 𝓞 K) ^ 6 := by
      exact_mod_cast S.equation
    change
      ((S.a : 𝓞 K) ^ 2) ^ 3 +
          (-((S.c : 𝓞 K) ^ 2)) ^ 3 =
        (-1 : 𝓞 K) * ((S.b : 𝓞 K) ^ 2) ^ 3
    calc
      _ = (S.a : 𝓞 K) ^ 6 - (S.c : 𝓞 K) ^ 6 := by ring
      _ = -(S.b : 𝓞 K) ^ 6 := by rw [← heq]; ring
      _ = _ := by ring

/-- Every primitive sixth-power solution directly supplies a neutral raw
cubic state, without first proving or invoking a fixed-exponent theorem. -/
theorem rawState_nonempty
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    (S : PrimitiveSolution) :
    Nonempty (RawState hζ) := by
  rcases S.three_divisibility_pattern with
    ⟨ha, hb, hc⟩ | ⟨hb, ha, hc⟩
  · exact ⟨S.rawState_of_three_dvd_a (hζ := hζ) ha hb hc⟩
  · exact ⟨S.rawState_of_three_dvd_b (hζ := hζ) hb ha hc⟩

/-- The direct N6 seed can be put in the orientation required by the neutral
charged transformer. -/
theorem orientedState_nonempty
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    (S : PrimitiveSolution) :
    Nonempty (OrientedState hζ) := by
  obtain ⟨raw : RawState hζ⟩ :=
    S.rawState_nonempty (K := K) (hζ := hζ)
  obtain ⟨oriented, -⟩ := raw.exists_oriented
  exact ⟨oriented⟩

end PrimitiveSolution

/-- The native degree-six charge of an oriented neutral descent state. -/
noncomputable def orientedStateCharge
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    (state : OrientedState hζ) : ℕ :=
  drainCharge state.multiplicity

/-- Every oriented state carries positive native degree-six charge. -/
theorem orientedStateCharge_pos
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    (state : OrientedState hζ) :
    0 < orientedStateCharge state := by
  rw [orientedStateCharge, drainCharge_eq]
  positivity

/-- The neutral cubic transformer strictly drains the native degree-six
charge. -/
theorem exists_orientedStateCharge_lt
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    (state : OrientedState hζ) :
    ∃ next : OrientedState hζ,
      orientedStateCharge next < orientedStateCharge state := by
  obtain ⟨next, hlt⟩ := state.exists_multiplicity_lt
  exact ⟨next, drainCharge_lt hlt⟩

namespace PrimitiveSolution

set_option backward.isDefEq.respectTransparency false in
/-- A primitive sixth-power solution is impossible by direct native charged
conservation. -/
theorem impossible_conservation (S : PrimitiveSolution) : False := by
  classical
  let K := CyclotomicField 3 ℚ
  let hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have : NumberField K :=
    IsCyclotomicExtension.numberField {3} ℚ _
  obtain ⟨oriented⟩ := S.orientedState_nonempty (hζ := hζ)
  exact
    Fermat.Conservation.impossible_of_strict_charge_drain
      oriented
      orientedStateCharge
      orientedStateCharge_pos
      exists_orientedStateCharge_lt

end PrimitiveSolution

end Fermat.Six.Conservation
