import Fermat.Irregular.FiniteCharacterFactor
import Fermat.Irregular.LocalEulerFactor
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

open scoped Classical BigOperators

/-!
# Character local Euler factors

This file converts the finite-character polynomial identity into a formal Euler-factor
identity. The coefficient in degree `n` is a multichoose coefficient when the order of
the residue class divides `n`, and is zero otherwise.
-/

namespace Fermat.Irregular.LocalEulerFactor

noncomputable section

open Finset

/-- The formal geometric series with coefficient `a ^ n` in degree `n`. -/
def geometricSeries {R : Type*} [CommRing R] (a : R) : PowerSeries R :=
  PowerSeries.rescale a (PowerSeries.mk 1)

@[simp] theorem coeff_geometricSeries {R : Type*} [CommRing R] (a : R) (n : ℕ) :
    PowerSeries.coeff n (geometricSeries a) = a ^ n := by
  simp [geometricSeries]

theorem geometricSeries_mul_one_sub {R : Type*} [CommRing R] (a : R) :
    geometricSeries a * (1 - PowerSeries.C a * PowerSeries.X) = 1 := by
  have h := congrArg (PowerSeries.rescale a)
    (PowerSeries.mk_one_mul_one_sub_eq_one R)
  simpa [geometricSeries, map_mul, PowerSeries.rescale_X] using h

theorem coeff_invOneSubPow_val_eq_multichoose
    {R : Type*} [CommRing R] (d n : ℕ) :
    PowerSeries.coeff n (PowerSeries.invOneSubPow R d).val =
      (Nat.multichoose d n : R) := by
  rcases d with _ | d
  · rcases n with _ | n
    · simp [PowerSeries.invOneSubPow_zero]
    · simp [PowerSeries.invOneSubPow_zero]
  · rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
    simp only [PowerSeries.coeff_mk]
    rw [Nat.multichoose_eq, show d + 1 + n - 1 = d + n by omega]
    rw [Nat.choose_symm_add]

open Fermat.Irregular.FiniteCharacterFactor

variable {G : Type*} [CommGroup G] [Fintype G]

local instance : Fintype (G →* ℂˣ) := Fintype.ofFinite _
local instance : NeZero (Monoid.exponent G : ℂ) :=
  ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite (G := G)⟩

theorem geometricSeries_one_mul_prod_nontrivial_characters (g : G) :
    geometricSeries 1 *
        ∏ χ : { χ : G →* ℂˣ // χ ≠ 1 },
          geometricSeries (((χ.1 g : ℂˣ) : ℂ)) =
      ∏ χ : G →* ℂˣ, geometricSeries (((χ g : ℂˣ) : ℂ)) := by
  simpa only [MonoidHom.one_apply, Units.val_one] using
    (Fintype.prod_eq_mul_prod_subtype_ne
      (fun χ : G →* ℂˣ ↦ geometricSeries (((χ g : ℂˣ) : ℂ))) 1).symm

theorem prod_geometricSeries_characters (g : G) :
    (∏ χ : G →* ℂˣ, geometricSeries (((χ g : ℂˣ) : ℂ))) =
      PowerSeries.subst (PowerSeries.X ^ orderOf g)
        (PowerSeries.invOneSubPow ℂ (Fintype.card G / orderOf g)).val := by
  let D : PowerSeries ℂ :=
    ∏ χ : G →* ℂˣ, (1 - PowerSeries.C (((χ g : ℂˣ) : ℂ)) * PowerSeries.X)
  have hD : D =
      (1 - PowerSeries.X ^ orderOf g) ^ (Fintype.card G / orderOf g) := by
    have h := congrArg
      (Polynomial.coeToPowerSeries.ringHom : Polynomial ℂ →+* PowerSeries ℂ)
      (prod_characters_one_sub_C_mul_X (R := ℂ) g)
    simpa [D, map_prod, map_sub, map_one, map_mul, map_pow,
      Polynomial.coeToPowerSeries.ringHom_apply] using h
  have hleft :
      (∏ χ : G →* ℂˣ, geometricSeries (((χ g : ℂˣ) : ℂ))) * D = 1 := by
    dsimp only [D]
    rw [← Finset.prod_mul_distrib]
    simp only [geometricSeries_mul_one_sub, Finset.prod_const_one]
  have hord : orderOf g ≠ 0 := (orderOf_pos g).ne'
  have hright :
      PowerSeries.subst (PowerSeries.X ^ orderOf g)
          (PowerSeries.invOneSubPow ℂ (Fintype.card G / orderOf g)).val * D = 1 := by
    rw [hD]
    let φ : PowerSeries ℂ →ₐ[ℂ] PowerSeries ℂ :=
      PowerSeries.substAlgHom (.X_pow hord)
    have hφ (f : PowerSeries ℂ) :
        φ f = PowerSeries.subst (PowerSeries.X ^ orderOf g) f := by
      exact congrFun
        (PowerSeries.coe_substAlgHom (R := ℂ) (S := ℂ) (τ := Unit) (.X_pow hord)) f
    have hφX : φ PowerSeries.X = PowerSeries.X ^ orderOf g := by
      exact PowerSeries.substAlgHom_X (.X_pow hord)
    have hden :
        φ ((1 - PowerSeries.X : PowerSeries ℂ) ^
            (Fintype.card G / orderOf g)) =
          (1 - PowerSeries.X ^ orderOf g : PowerSeries ℂ) ^
            (Fintype.card G / orderOf g) := by
      rw [map_pow, map_sub, map_one, hφX]
    have hinv :
        (PowerSeries.invOneSubPow ℂ (Fintype.card G / orderOf g)).val *
            ((1 - PowerSeries.X : PowerSeries ℂ) ^
              (Fintype.card G / orderOf g)) = 1 := by
      rw [← PowerSeries.invOneSubPow_inv_eq_one_sub_pow]
      exact (PowerSeries.invOneSubPow ℂ (Fintype.card G / orderOf g)).val_inv
    rw [← hφ, ← hden, ← map_mul, hinv, map_one]
  calc
    (∏ χ : G →* ℂˣ, geometricSeries (((χ g : ℂˣ) : ℂ))) =
        (∏ χ : G →* ℂˣ, geometricSeries (((χ g : ℂˣ) : ℂ))) * 1 := by rw [mul_one]
    _ = (∏ χ : G →* ℂˣ, geometricSeries (((χ g : ℂˣ) : ℂ))) *
        (PowerSeries.subst (PowerSeries.X ^ orderOf g)
          (PowerSeries.invOneSubPow ℂ (Fintype.card G / orderOf g)).val * D) := by
        rw [hright]
    _ = PowerSeries.subst (PowerSeries.X ^ orderOf g)
          (PowerSeries.invOneSubPow ℂ (Fintype.card G / orderOf g)).val *
        ((∏ χ : G →* ℂˣ, geometricSeries (((χ g : ℂˣ) : ℂ))) * D) := by
        ac_rfl
    _ = PowerSeries.subst (PowerSeries.X ^ orderOf g)
        (PowerSeries.invOneSubPow ℂ (Fintype.card G / orderOf g)).val := by rw [hleft, mul_one]

theorem coeff_prod_geometricSeries_characters (g : G) (n : ℕ) :
    PowerSeries.coeff n
        (∏ χ : G →* ℂˣ, geometricSeries (((χ g : ℂˣ) : ℂ))) =
      if orderOf g ∣ n then
        (Nat.multichoose (Fintype.card G / orderOf g) (n / orderOf g) : ℂ)
      else 0 := by
  rw [prod_geometricSeries_characters]
  rw [PowerSeries.coeff_subst_X_pow (orderOf_pos g).ne']
  simp only [map_natCast, coeff_invOneSubPow_val_eq_multichoose]

end

end Fermat.Irregular.LocalEulerFactor
