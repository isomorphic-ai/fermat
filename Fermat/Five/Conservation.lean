/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Fermat's Last Theorem at exponent five by conservation

This is the public assembly of the reconstructed Dirichlet descent.  No
module from the repository's earlier exponent-five route enters this import
cone.  A primitive integral counterexample is recorded as the golden norm
ledger, split honestly on `5 ∣ c`, and sent into the corresponding iterable
gauge-invariant charge drain.  Both branches stop only at the shared
conservation floor.
-/
import Fermat.Five.Conservation.ChargedDescent
import Fermat.Five.Conservation.Reduction

namespace Fermat.Five

/-- Fermat's Last Theorem at exponent five, proved by the golden-ring
conservation ledger, its gauge-invariant charge, Dirichlet's two case-tagged
strict descents, and the shared conservation floor. -/
theorem holdsAt_five_conservation : Fermat.HoldsAt 5 := by
  change FermatLastTheoremFor 5
  rw [fermatLastTheoremFor_iff_int]
  refine fermatLastTheoremWith_of_fermatLastTheoremWith_coprime
    (fun a b c ha hb hc hgcd heq ↦ ?_)
  obtain ⟨hab, hac, hbc⟩ :=
    Conservation.Reconstruction.Dirichlet.pairwise_isCoprime_of_gcd_eq_one
      hgcd heq
  let origin : Conservation.PrimitiveFifthSolution :=
    { a := a
      b := b
      c := c
      nonzero := mul_ne_zero (mul_ne_zero ha hb) hc
      coprime_ab := hab
      coprime_ac := hac
      coprime_bc := hbc
      ledger := Conservation.fermatEquation_five_ledger heq }
  by_cases hfive : (5 : ℤ) ∣ c
  · exact Conservation.five_dvd_c_impossible origin hfive
  · exact Conservation.not_five_dvd_c_impossible origin hfive

end Fermat.Five
