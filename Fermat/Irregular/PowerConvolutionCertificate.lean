import Fermat.Irregular.FiniteCyclicCofactor
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Power-enumerated convolution certificates

This file is the executable companion to `FiniteCyclicCofactor`.  A
primitive generator identifies a finite cyclic group with
`Multiplicative (ZMod N)`, where multiplication is just modular addition
of exponents.  Finite inverse-kernel tables can therefore be checked in
that compact coordinate system and transported to the abstract real
residue group without evaluating quotient representatives.
-/

open scoped Classical BigOperators

namespace Fermat.Irregular.PowerConvolutionCertificate

noncomputable section

open Fermat.Irregular.FiniteCyclicCofactor

variable {G F : Type*} [CommGroup G] [Fintype G] [Field F]
variable {N : ℕ}

/-- A primitive element of a finite group with `N` elements gives a
multiplicative equivalence from additive exponents modulo `N`. -/
def powerMulEquiv (γ : G) (hγ : IsPrimitiveRoot γ N)
    (hcard : Nat.card G = N) :
    Multiplicative (ZMod N) ≃* G := by
  let htop : Subgroup.zpowers γ = ⊤ := by
    apply (Subgroup.card_eq_iff_eq_top (Subgroup.zpowers γ)).1
    rw [Nat.card_zpowers, ← hγ.eq_orderOf, hcard]
  apply zmodMulEquivOfGenerator (g := γ) ?_ hcard
  intro x
  rw [htop]
  exact Subgroup.mem_top x

/- Transport a kernel along a multiplicative equivalence. -/
variable {H : Type*} [CommGroup H] [Fintype H]

def transportKernel (e : H ≃* G) (f : H → F) : G → F :=
  fun x ↦ f (e.symm x)

/-- Convolution is invariant under multiplicative reindexing. -/
theorem convolution_transportKernel
    (e : H ≃* G) (f g : H → F) (x : H) :
    convolution (transportKernel e f) (transportKernel e g) (e x) =
      convolution f g x := by
  simp only [convolution, transportKernel]
  calc
    (∑ y : G,
        f (e.symm (e x * y⁻¹)) * g (e.symm y)) =
        ∑ y : H,
          f (e.symm (e x * (e y)⁻¹)) *
            g (e.symm (e y)) := by
      exact (Equiv.sum_comp e.toEquiv
        (fun y : G ↦
          f (e.symm (e x * y⁻¹)) * g (e.symm y))).symm
    _ = ∑ y : H, f (x * y⁻¹) * g y := by
      apply Finset.sum_congr rfl
      intro y _
      simp

/-- A compact inverse table in cyclic coordinates transports to an inverse
kernel on the abstract group. -/
theorem inverseKernel_transport
    (e : H ≃* G) {f g : H → F}
    (hinverse : ∀ x, convolution f g x = deltaKernel x) :
    ∀ x, convolution (transportKernel e f)
      (transportKernel e g) x = deltaKernel x := by
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  rw [convolution_transportKernel]
  simpa [deltaKernel] using hinverse y

/-- Combined compact certificate for the circular-unit determinant: an
inverse table in any cyclic power enumeration proves the transposed
real-residue cofactor nonsingular. -/
theorem transpose_realResidueCofactor_det_ne_zero_of_powerInverse
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 < p)]
    (e : H ≃* Fermat.Irregular.CyclotomicCharactersPrime.RealResidueGroup p)
    {f g : H → F}
    (hinverse : ∀ x, convolution f g x = deltaKernel x) :
    (Matrix.transpose
      (inverseAlignedRealResidueCofactor
        (transportKernel e f))).det ≠ 0 := by
  apply transpose_inverseAlignedRealResidueCofactor_det_ne_zero
    (g := transportKernel e g)
  exact inverseKernel_transport
    (G := Fermat.Irregular.CyclotomicCharactersPrime.RealResidueGroup p)
    (F := F) (e := e) (f := f) (g := g) hinverse

end

end Fermat.Irregular.PowerConvolutionCertificate
