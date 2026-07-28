/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Exponent one, strictly as a conservation law

The n = 1 rung is the ledger's identity element. The **charge** is the
counting measure itself (`charge v = v ^ 1`), and the **coupling
channel** between any two charges is *identically* empty — linearity
has no cross term, so there is nothing to cancel and nothing to leak.
Where n = 2 balances conditionally (the channel must be emptied by
orthogonality) and n ≥ 3 never balances, n = 1 balances **always**:
the constant, always-true term of the Fermat series.

Consequently `Fermat.HoldsAt 1` is *false*, and constructively so —
every pair of positive integers is a witness, with hypotenuse their
sum. This rung contributes the **vacuum of the ledger**: balance with
no hypothesis, the zero point against which every later rung's
obstruction is measured.
-/
import Fermat.Statement.Basic

namespace Fermat.One

/-- The **charge** at exponent one: the counting measure itself. At
n = 1, charge *is* stock — a quantity with no shape to lose. -/
def charge (v : ℕ) : ℕ := v ^ 1

/-- The **coupling channel** at exponent one: whatever the ledger
expansion holds beyond the pure stocks. -/
def coupling (u v : ℕ) : ℕ := charge (u + v) - (charge u + charge v)

/-- **The channel is identically empty.** No orthogonality hypothesis,
no gauge, no floor: there is no interference term at exponent one. -/
theorem coupling_empty (u v : ℕ) : coupling u v = 0 := by
  simp [coupling, charge]

/-- **The ledger closes unconditionally**: the charge of a sum is the
sum of the charges, for every pair. Universal balance — the vacuum
mode of the conservation law. -/
theorem charge_ledger (u v : ℕ) :
    charge (u + v) = charge u + charge v := by
  simp [charge]

/-- **The Fermat equation at n = 1 is solvable everywhere**: the
hypotenuse of any pair is its sum. Balance needs no witness hunt. -/
theorem solvable (a b : ℕ) :
    a ^ 1 + b ^ 1 = (a + b) ^ 1 := by ring

/-- Every positive pair extends to a positive Fermat triple at n = 1:
the always-true term, stated as unconditional existence. -/
theorem always_balances (a b : ℕ) (ha : a ≠ 0) (_hb : b ≠ 0) :
    ∃ c : ℕ, c ≠ 0 ∧ a ^ 1 + b ^ 1 = c ^ 1 :=
  ⟨a + b, by positivity, solvable a b⟩

/-- `HoldsAt 1` is **false** — refuted by witness, not by contradiction
hunting: `1 + 1 = 2`. The failure of the Fermat obstruction at the
identity exponent *is* the unconditional balance of the ledger. -/
theorem not_holdsAt_one : ¬ Fermat.HoldsAt 1 := by
  intro h
  exact h 1 1 2 one_ne_zero one_ne_zero two_ne_zero (by norm_num)

end Fermat.One
