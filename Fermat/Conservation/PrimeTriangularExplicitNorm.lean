/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Explicit norm of a triangular Kummer product

The finite triangular product is evaluated in a prime Kummer extension and
its actual field norm is computed factor by factor.  This converts the
polynomial factorization into an exact product of base-field terms
`1 + c_j^p * a^j`, which exposes their distinct valuation residues.
-/
import Fermat.Conservation.PrimeTriangularUnitFactorization
import Fermat.Conservation.PrimeKummerExplicitNorm

open Polynomial

noncomputable section

namespace Fermat.Conservation.PrimeTriangularExplicitNorm

open PrimeTriangularUnitFactorization
open PrimeKummerExplicitNorm
open PrimeKummerCyclicQuotient

variable (p : ℕ) [Fact p.Prime]
variable (F : Type) [Field F]
variable (zeta a : F)
variable (hzeta : IsPrimitiveRoot zeta p)
variable (ha : ∀ b : F, b ^ p ≠ a)

local notation "E" => kummerExtension p F a

local instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
local instance : IsSplittingField F E (kummerPolynomial p F a) :=
  kummerExtension_isSplittingField p F a
local instance : FiniteDimensional F E :=
  Polynomial.IsSplittingField.finiteDimensional E (kummerPolynomial p F a)

include zeta hzeta ha

/-- The actual norm of an evaluated triangular product is the product of
the explicit elementary Kummer norms. -/
theorem norm_aeval_triangularProduct
    (f : F[X]) (n : ℕ) (hn : n < p) (hp2 : p ≠ 2) :
    Algebra.norm F
        (aeval (selectedKummerRoot p F a) (triangularProduct f n)) =
      ∏ j ∈ Finset.Icc 1 n,
        (1 + triangularCoefficient f j ^ p * a ^ j) := by
  rw [triangularProduct_eq_prod]
  simp only [map_prod, map_add, map_one, map_mul, aeval_C, map_pow,
    aeval_X]
  apply Finset.prod_congr rfl
  intro j hj
  exact norm_one_add_smul_root_pow p F zeta a hzeta ha
    (triangularCoefficient f j) j
    (Finset.mem_Icc.mp hj).1
    ((Finset.mem_Icc.mp hj).2.trans_lt hn) hp2

end Fermat.Conservation.PrimeTriangularExplicitNorm
