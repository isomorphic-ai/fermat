/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# The conservation floor

Drain-mode conservation arguments may use different rings and different
charges, but they all stop at the same floor: a positive natural-valued
charge cannot decrease forever.

The only Mathlib import is `Order.WellFounded`, used solely for the
well-foundedness of `<` on `ℕ`. No fixed-exponent FLT theorem is imported.
-/
import Mathlib.Order.WellFounded

namespace Fermat.Conservation

/-- **The conservation floor.** There is no infinite sequence of positive
natural charges that drops strictly at every successor. -/
theorem noInfinitePositiveChargeDrain :
    ¬ ∃ q : ℕ → ℕ, (∀ n, 0 < q n) ∧ ∀ n, q (n + 1) < q n := by
  rintro ⟨q, -, hdrop⟩
  obtain ⟨n, hn⟩ :=
    WellFounded.not_rel_apply_succ (r := (· < ·)) q
  exact hn (hdrop n)

/-- **Impossible debt.** If every state has positive natural charge and
admits a strictly lower-charge successor, the conservation floor rules out
every initial state. -/
theorem impossible_of_strict_charge_drain
    {α : Type*} (start : α) (stateCharge : α → ℕ)
    (hpositive : ∀ state, 0 < stateCharge state)
    (hstep : ∀ state, ∃ next,
      stateCharge next < stateCharge state) :
    False := by
  classical
  let next : α → α := fun state => (hstep state).choose
  let sequence : ℕ → α :=
    fun n => Nat.rec start (fun _ state => next state) n
  apply noInfinitePositiveChargeDrain
  refine ⟨stateCharge ∘ sequence, ?_, ?_⟩
  · intro n
    exact hpositive (sequence n)
  · intro n
    change
      stateCharge (sequence (n + 1)) <
        stateCharge (sequence n)
    change
      stateCharge (next (sequence n)) <
        stateCharge (sequence n)
    exact (hstep (sequence n)).choose_spec

end Fermat.Conservation
