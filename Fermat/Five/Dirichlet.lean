import Fermat.Five.Initial
import Fermat.Five.Reduction

/-!
# Dirichlet's completed proof for exponent five

This module joins the historical entry equations, the two parity-sensitive
descents, and the outer reduction from a primitive Fermat counterexample.
-/

namespace Fermat.Five.Dirichlet

/-- If both of Dirichlet's normalized descent families are empty, then his
generalized fifth-power equation has no nonzero primitive solution.
-/
theorem fifthEquationImpossible_of_no_states
    (hodd : ∀ h t s w : ℕ, ¬OddState h t s w)
    (heven : ∀ g h t s w : ℕ, ¬EvenState g h t s w) :
    FifthEquationImpossible := by
  intro x y z d
  rcases d.exists_core with hcore | hcore
  · obtain ⟨q, r, z₀, c⟩ := hcore
    obtain ⟨t, s, w, hstate⟩ := c.exists_oddState
    exact hodd 4 t s w hstate
  · obtain ⟨q, r, z₀, c⟩ := hcore
    obtain ⟨t, s, w, hstate⟩ := c.exists_evenState
    exact heven 1 4 t s w hstate

/-- Dirichlet's two infinite descents rule out his generalized equation. -/
theorem fifthEquationImpossible : FifthEquationImpossible :=
  fifthEquationImpossible_of_no_states no_oddState no_evenState

/-- Fermat's Last Theorem for exponent five, following Dirichlet's completed
1828 proof and its two historical parity branches.
-/
theorem holdsAt_five_dirichlet : Fermat.HoldsAt 5 :=
  holdsAt_five_of_fifthEquationImpossible fifthEquationImpossible

end Fermat.Five.Dirichlet
