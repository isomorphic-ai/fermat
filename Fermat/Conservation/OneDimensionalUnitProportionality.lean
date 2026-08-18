/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Unit proportionality inside a one-dimensional line

This file isolates the pure linear-algebra step used after two arithmetic
readouts have been proved to occupy the same one-dimensional line.  It does
not construct that line, prove membership in it, or prove either readout
nonzero.
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace Fermat.Conservation

universe uK uV

variable {k : Type uK} [Field k]
variable {V : Type uV} [AddCommGroup V] [Module k V]

/-- Two nonzero vectors in the same one-dimensional submodule differ by a
unique unit scalar.

The nonvanishing assumptions have distinct jobs: `hpsi_ne` makes the scalar
unique, while `hphi_ne` proves that the scalar supplied by
one-dimensionality is a unit.  No finite-dimensionality assumption on the
ambient module is needed. -/
theorem existsUnique_unit_smul_of_mem_finrank_one
    (line : Submodule k V) (phi psi : V)
    (hphi_mem : phi ∈ line) (hpsi_mem : psi ∈ line)
    (hline : Module.finrank k line = 1)
    (hphi_ne : phi ≠ 0) (hpsi_ne : psi ≠ 0) :
    ∃! u : kˣ, phi = (u : k) • psi := by
  let phiLine : line := ⟨phi, hphi_mem⟩
  let psiLine : line := ⟨psi, hpsi_mem⟩
  have hpsiLine_ne : psiLine ≠ 0 := by
    intro h
    apply hpsi_ne
    exact congrArg Subtype.val h
  obtain ⟨c, hc⟩ :=
    exists_smul_eq_of_finrank_eq_one hline hpsiLine_ne phiLine
  have hc_value : c • psi = phi := congrArg Subtype.val hc
  have hc_ne : c ≠ 0 := by
    intro hzero
    apply hphi_ne
    rw [hzero, zero_smul] at hc_value
    exact hc_value.symm
  let u : kˣ := Units.mk0 c hc_ne
  refine ⟨u, hc_value.symm, ?_⟩
  intro v hv
  have hsmul : ((u : k) - (v : k)) • psi = 0 := by
    rw [sub_smul, show (u : k) = c by rfl, hc_value, ← hv, sub_self]
  exact Units.ext
    (sub_eq_zero.mp ((smul_eq_zero.mp hsmul).resolve_right hpsi_ne)).symm

end Fermat.Conservation
