/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Tame-place realization of the place-indexed pairing

This file is the valuation-bookkeeping bridge between the explicit tame
Hilbert symbol and the place-indexed pairing ledger.  At a tame place a
`PlaceIndexedTameRealization` identifies the local reading with
`TameSymbol.Context.modP` on the two Kummer classes.  This is the same
additive Kummer quotient that underlies Mathlib's
`IsDedekindDomain.HeightOneSpectrum.selmerGroup`; no parallel Selmer carrier
or cohomological pairing is introduced.

Mathlib Selmer membership records valuation zero modulo `p`, equivalently a
representative valuation divisible by `p`; it does not record literal integer
valuation zero.  The `Context.ordModP` conditions below retain exactly that
honest receipt on the Kummer quotient.  The explicit tame formula is already
silent when both mod-`p` valuations vanish, so no noncanonical unit
normalization or section of the Kummer quotient is introduced.

The final two theorems expose the intended audit split.  Tame rows are proved
from mod-`p` valuation receipts; any genuinely non-tame row remains a separate
residual hypothesis.  This keeps the wild place out of the explicit tame
construction.
-/
import Fermat.Conservation.TameSymbol
import Fermat.Conservation.TatePairing
import Fermat.Conservation.SelmerEigenspace

noncomputable section

namespace Fermat.Conservation.TamePlacePairing

open Fermat.Conservation.TameSymbol
open Fermat.Conservation.TatePairing
open Fermat.Conservation.LinkingInterfaces

universe uR uK uk uPlace uDelta uChi uDual

/-! ## Realizing one column by the explicit tame symbol -/

/-- A certificate that the place-indexed readings at the tame places are the
explicit tame Hilbert symbols of the two seated Kummer classes.

The residue field is allowed to vary with the place.  A `Context` is only
requested after a proof that the place is tame, since its cardinality and
residue-characteristic fields are false at the wild place in general. -/
structure PlaceIndexedTameRealization
    (p : ℕ) [Fact p.Prime]
    (Delta : Type uDelta) [CommGroup Delta]
    (omega chi : InvolutiveBase.Character (PadicInt p) Delta)
    (Place : Type uPlace) (SelmerChi : Type uChi)
    (DOmegaSelmerChiStar : Type uDual)
    [AddCommGroup SelmerChi]
    [Module (IntegralPadicGroupAlgebra p Delta) SelmerChi]
    [AddCommGroup DOmegaSelmerChiStar]
    [Module (IntegralPadicGroupAlgebra p Delta) DOmegaSelmerChiStar]
    (pairing : PlaceIndexedLocalPairing p Delta omega chi Place
      SelmerChi DOmegaSelmerChiStar)
    (K : Type uK) [Field K]
    (Residue : Place → Type uk)
    [∀ v, Fintype (Residue v)] [∀ v, Field (Residue v)]
    (IsTame : Place → Prop) where
  context : ∀ v, IsTame v → TameSymbol.Context p K (Residue v)
  primalClass : SelmerChi →+ TameSymbol.KummerClass p K
  dualClass : DOmegaSelmerChiStar →+ TameSymbol.KummerClass p K
  pairAt_eq_modP : ∀ v (hv : IsTame v) x y,
    pairing.pairAt v x y =
      (context v hv).modP (primalClass x) (dualClass y)

namespace PlaceIndexedTameRealization

variable {p : ℕ} [Fact p.Prime]
  {Delta : Type uDelta} [CommGroup Delta]
  {omega chi : InvolutiveBase.Character (PadicInt p) Delta}
  {Place : Type uPlace} {SelmerChi : Type uChi}
  {DOmegaSelmerChiStar : Type uDual}
  [AddCommGroup SelmerChi]
  [Module (IntegralPadicGroupAlgebra p Delta) SelmerChi]
  [AddCommGroup DOmegaSelmerChiStar]
  [Module (IntegralPadicGroupAlgebra p Delta) DOmegaSelmerChiStar]
  {pairing : PlaceIndexedLocalPairing p Delta omega chi Place
    SelmerChi DOmegaSelmerChiStar}
  {K : Type uK} [Field K]
  {Residue : Place → Type uk}
  [∀ v, Fintype (Residue v)] [∀ v, Field (Residue v)]
  {IsTame : Place → Prop}
  (realization : PlaceIndexedTameRealization p Delta omega chi Place
    SelmerChi DOmegaSelmerChiStar pairing K Residue IsTame)

/-- The two mod-`p` valuation receipts needed for one selected tame reading.
These are the additive form of Mathlib Selmer's
`valuationOfNeZeroMod p class = 1`. -/
structure SelectedValuationsZeroAt (v : Place) (hv : IsTame v)
    (x : SelmerChi) (y : DOmegaSelmerChiStar) where
  primal : (realization.context v hv).ordModP
    (realization.primalClass x) = 0
  dual : (realization.context v hv).ordModP
    (realization.dualClass y) = 0

/-- A tame reading with `p`-divisible representative valuations on both legs
is zero.  This is the quotient-level form of tame silence consumed by the
Selmer support audit. -/
theorem pairAt_eq_zero_of_p_dvd_ord
    {v : Place} {hv : IsTame v} {x : SelmerChi}
    {y : DOmegaSelmerChiStar}
    (valuations : realization.SelectedValuationsZeroAt v hv x y) :
    pairing.pairAt v x y = 0 := by
  rw [realization.pairAt_eq_modP v hv x y]
  exact (realization.context v hv).modP_eq_zero_of_ordModP_eq_zero
    (realization.primalClass x) (realization.dualClass y)
    valuations.primal valuations.dual

/-! ## Tame rows of a two-place support audit -/

/-- Valuation bookkeeping for the tame rows outside two distinguished
places.  No assertion is made about a non-tame place. -/
structure OutsideTwoTameBookkeeping
    (distinguished auxiliary : Place)
    (x : SelmerChi) (y : DOmegaSelmerChiStar) where
  valuationsZero : ∀ v (hv : IsTame v),
    v ≠ distinguished → v ≠ auxiliary →
      realization.SelectedValuationsZeroAt v hv x y

namespace OutsideTwoTameBookkeeping

variable {realization}
  {distinguished auxiliary : Place}
  {x : SelmerChi} {y : DOmegaSelmerChiStar}

/-- Every tame row outside the two retained places is proved silent by
valuation bookkeeping. -/
theorem outside_two_readings_at_tame_places
    (bookkeeping : realization.OutsideTwoTameBookkeeping
      distinguished auxiliary x y)
    (v : Place) (hv : IsTame v)
    (hdistinguished : v ≠ distinguished) (hauxiliary : v ≠ auxiliary) :
    pairing.pairAt v x y = 0 :=
  realization.pairAt_eq_zero_of_p_dvd_ord
    (bookkeeping.valuationsZero v hv hdistinguished hauxiliary)

/-- Combine the proved tame rows with a residual hypothesis mentioning only
non-tame places.  This is the exact logical split needed by a global support
condition: the explicit construction handles tame places and the wild
interface cannot leak back into those rows. -/
theorem outside_two_readings_of_tame_and_residual
    (bookkeeping : realization.OutsideTwoTameBookkeeping
      distinguished auxiliary x y)
    (residual : ∀ v, ¬IsTame v → v ≠ distinguished → v ≠ auxiliary →
      pairing.pairAt v x y = 0)
    (v : Place) (hdistinguished : v ≠ distinguished)
    (hauxiliary : v ≠ auxiliary) :
    pairing.pairAt v x y = 0 := by
  by_cases hv : IsTame v
  · exact bookkeeping.outside_two_readings_at_tame_places
      v hv hdistinguished hauxiliary
  · exact residual v hv hdistinguished hauxiliary

/-- Tame valuation bookkeeping plus the residual non-tame audit upgrades
global reciprocity to the exact two-place balance.  The auxiliary column is
retained rather than silently discarded. -/
theorem distinguished_eq_neg_auxiliary_of_reciprocity
    (bookkeeping : realization.OutsideTwoTameBookkeeping
      distinguished auxiliary x y)
    (reciprocity : GlobalReciprocityLaw pairing)
    (hne : distinguished ≠ auxiliary)
    (residual : ∀ v, ¬IsTame v → v ≠ distinguished → v ≠ auxiliary →
      pairing.pairAt v x y = 0) :
    pairing.pairAt distinguished x y =
      -pairing.pairAt auxiliary x y :=
  reciprocity.pairAt_eq_neg_pairAt_of_outside_two
    distinguished auxiliary hne x y
      (bookkeeping.outside_two_readings_of_tame_and_residual residual)

end OutsideTwoTameBookkeeping

end PlaceIndexedTameRealization

/-! ## A full ledger from the sole wild local interface -/

/-- The only local arithmetic interface left after the seated tame rows have
been proved: one bilinear reading at the distinguished wild place, with the
same `#`-adjoint law as `PlaceIndexedLocalPairing`.

The full place-indexed pairing below is obtained by putting this reading in a
single `Finsupp` column.  Thus finite support and every non-distinguished row
are constructed, not assumed. -/
structure WildLocalInterface
    (p : ℕ) [Fact p.Prime]
    (Delta : Type uDelta) [CommGroup Delta]
    (omega chi : InvolutiveBase.Character (PadicInt p) Delta)
    (Place : Type uPlace) (SelmerChi : Type uChi)
    (DOmegaSelmerChiStar : Type uDual)
    [AddCommGroup SelmerChi]
    [Module (IntegralPadicGroupAlgebra p Delta) SelmerChi]
    [AddCommGroup DOmegaSelmerChiStar]
    [Module (IntegralPadicGroupAlgebra p Delta) DOmegaSelmerChiStar]
    (distinguished : Place) where
  reading : SelmerChi →+ (DOmegaSelmerChiStar →+ ZMod p)
  adjoint_law : ∀ a x y,
    reading (a • x) y =
      reading x ((InvolutiveBase.hash omega a) • y)

namespace WildLocalInterface

variable {p : ℕ} [Fact p.Prime]
  {Delta : Type uDelta} [CommGroup Delta]
  {omega chi : InvolutiveBase.Character (PadicInt p) Delta}
  {Place : Type uPlace} {SelmerChi : Type uChi}
  {DOmegaSelmerChiStar : Type uDual}
  [AddCommGroup SelmerChi]
  [Module (IntegralPadicGroupAlgebra p Delta) SelmerChi]
  [AddCommGroup DOmegaSelmerChiStar]
  [Module (IntegralPadicGroupAlgebra p Delta) DOmegaSelmerChiStar]
  {distinguished : Place}

/-- Put the wild reading in its one distinguished `Finsupp` column. -/
def toPlaceIndexedLocalPairing
    (wild : WildLocalInterface p Delta omega chi Place SelmerChi
      DOmegaSelmerChiStar distinguished) :
    PlaceIndexedLocalPairing p Delta omega chi Place SelmerChi
      DOmegaSelmerChiStar where
  readings :=
    { toFun := fun x ↦
        (Finsupp.singleAddHom distinguished).comp (wild.reading x)
      map_zero' := by
        ext y v
        simp
      map_add' := by
        intro x₁ x₂
        ext y v
        simp }
  adjoint_law := by
    intro v a x y
    change Finsupp.single distinguished (wild.reading (a • x) y) v =
      Finsupp.single distinguished
        (wild.reading x ((InvolutiveBase.hash omega a) • y)) v
    rw [wild.adjoint_law]

@[simp]
theorem pairAt_distinguished
    (wild : WildLocalInterface p Delta omega chi Place SelmerChi
      DOmegaSelmerChiStar distinguished)
    (x : SelmerChi) (y : DOmegaSelmerChiStar) :
    wild.toPlaceIndexedLocalPairing.pairAt distinguished x y =
      wild.reading x y := by
  simp [toPlaceIndexedLocalPairing, PlaceIndexedLocalPairing.pairAt]

/-- Every non-distinguished row of the constructed global pairing is
definitionally silent. -/
theorem pairAt_eq_zero_of_ne
    (wild : WildLocalInterface p Delta omega chi Place SelmerChi
      DOmegaSelmerChiStar distinguished)
    {v : Place} (hv : v ≠ distinguished)
    (x : SelmerChi) (y : DOmegaSelmerChiStar) :
    wild.toPlaceIndexedLocalPairing.pairAt v x y = 0 := by
  simp [toPlaceIndexedLocalPairing, PlaceIndexedLocalPairing.pairAt, hv]

end WildLocalInterface

/-! ## Zero-premise specialization to the seated Selmer eigenspaces -/

namespace Seated

open Fermat.Conservation.SelmerEigenspace

variable {p : ℕ} [Fact p.Prime]
  {Delta : Type uDelta} [CommGroup Delta]
  {omega chi : InvolutiveBase.Character (PadicInt p) Delta}
  {R : Type uR} [CommRing R] [IsDedekindDomain R]
  {K : Type uK} [Field K] [Algebra R K] [IsFractionRing R K]
  {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
    (Delta := Delta)}

abbrev Place := IsDedekindDomain.HeightOneSpectrum R

abbrev Primal := SelmerChi rho chi

abbrev ReflectedDual := DOmegaSelmerChiStar rho omega chi

abbrev Pairing := PlaceIndexedLocalPairing p Delta omega chi
  (Place (R := R)) (Primal (rho := rho) (chi := chi))
    (ReflectedDual (rho := rho) (omega := omega) (chi := chi))

abbrev WildInterface (distinguished : Place (R := R)) :=
  WildLocalInterface p Delta omega chi (Place (R := R))
    (Primal (rho := rho) (chi := chi))
    (ReflectedDual (rho := rho) (omega := omega) (chi := chi))
    distinguished

/-- Mathlib's empty-support Selmer condition, translated from its
multiplicative quotient valuation to the additive `ordModP` of an explicit
tame context.  This helper is independent of any pairing realization. -/
theorem ordModP_toKummerClass_eq_zero_of_ord_eq_valuation
    {k : Type uk} [Fintype k] [Field k]
    (v : Place (R := R)) (ctx : TameSymbol.Context p K k)
    (ord_eq_valuation : ∀ a,
      ctx.ord (Additive.ofMul a) = (v.valuationOfNeZero a).toAdd)
    {eta : InvolutiveBase.Character (PadicInt p) Delta}
    (x : SelmerChi rho eta) :
    ctx.ordModP (SelmerEigenspace.toKummerClass x) = 0 := by
  let a : Kˣ := SelmerEigenspace.quotientRepresentative x
  have ha :
      Additive.ofMul
          (QuotientGroup.mk' (powMonoidHom p : Kˣ →* Kˣ).range a) =
        SelmerEigenspace.toKummerClass x := by
    rw [SelmerEigenspace.toKummerClass_apply]
    exact congrArg Additive.ofMul
      (SelmerEigenspace.quotientRepresentative_mk x)
  rw [← ha, TameSymbol.Context.ordModP_mk, ord_eq_valuation]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr
    (SelmerEigenspace.quotientRepresentative_valuation_dvd v x)

/-- A tame realization whose two carrier maps are fixed to the literal
Mathlib Selmer eigenspaces.

`ord_eq_valuation` is the only place/valuation glue: it says the order in the
explicit tame context is Mathlib's height-one valuation on field units.  The
reading equation then uses `SelmerEigenspace.toKummerClass` on both legs, so
there is no carrier supplied by a caller and no gap hidden by an equivalence. -/
structure Realization
    (pairing : Pairing (p := p) (Delta := Delta) (omega := omega)
      (chi := chi) (R := R) (K := K) (rho := rho))
    (Residue : Place (R := R) → Type uk)
    [∀ v, Fintype (Residue v)] [∀ v, Field (Residue v)]
    (IsTame : Place (R := R) → Prop) where
  context : ∀ v, IsTame v → TameSymbol.Context p K (Residue v)
  ord_eq_valuation : ∀ v (hv : IsTame v) a,
    (context v hv).ord (Additive.ofMul a) =
      (v.valuationOfNeZero a).toAdd
  pairAt_eq_modP : ∀ v (hv : IsTame v) x y,
    pairing.pairAt v x y =
      (context v hv).modP
        (SelmerEigenspace.toKummerClass x)
        (SelmerEigenspace.toKummerClass y)

namespace Realization

variable
  {pairing : Pairing (p := p) (Delta := Delta) (omega := omega)
    (chi := chi) (R := R) (K := K) (rho := rho)}
  {Residue : Place (R := R) → Type uk}
  [∀ v, Fintype (Residue v)] [∀ v, Field (Residue v)]
  {IsTame : Place (R := R) → Prop}
  (realization : Realization pairing Residue IsTame)

/-- Construct the complete seated tame realization from only the local
interface at the distinguished wild place.

The global pairing is the single-column pairing built by
`WildLocalInterface.toPlaceIndexedLocalPairing`.  At a tame place the left
side of the realization equation is zero because the place is not
distinguished; the explicit tame symbol on the right is zero because both
seated Selmer valuations vanish modulo `p`. -/
def ofWild
    {distinguished : Place (R := R)}
    (wild : WildInterface (p := p) (Delta := Delta) (omega := omega)
      (chi := chi) (R := R) (K := K) (rho := rho) distinguished)
    (context : ∀ v, IsTame v → TameSymbol.Context p K (Residue v))
    (ord_eq_valuation : ∀ v (hv : IsTame v) a,
      (context v hv).ord (Additive.ofMul a) =
        (v.valuationOfNeZero a).toAdd)
    (distinguished_not_tame : ¬IsTame distinguished) :
    Realization wild.toPlaceIndexedLocalPairing Residue IsTame where
  context := context
  ord_eq_valuation := ord_eq_valuation
  pairAt_eq_modP := by
    intro v hv x y
    have hvne : v ≠ distinguished := fun h ↦
      distinguished_not_tame (h ▸ hv)
    rw [wild.pairAt_eq_zero_of_ne hvne]
    symm
    apply (context v hv).modP_eq_zero_of_ordModP_eq_zero
    · exact ordModP_toKummerClass_eq_zero_of_ord_eq_valuation
        v (context v hv) (ord_eq_valuation v hv) x
    · exact ordModP_toKummerClass_eq_zero_of_ord_eq_valuation
        v (context v hv) (ord_eq_valuation v hv) y

/-- Forget only the seated spelling.  The resulting generic realization
still has the exact `toKummerClass` maps on both legs. -/
def toPlaceIndexedTameRealization :
    PlaceIndexedTameRealization p Delta omega chi
      (Place (R := R)) (Primal (rho := rho) (chi := chi))
      (ReflectedDual (rho := rho) (omega := omega) (chi := chi))
      pairing K Residue IsTame where
  context := realization.context
  primalClass := SelmerEigenspace.toKummerClass
  dualClass := SelmerEigenspace.toKummerClass
  pairAt_eq_modP := realization.pairAt_eq_modP

@[simp]
theorem toPlaceIndexedTameRealization_primalClass
    (x : Primal (rho := rho) (chi := chi)) :
    realization.toPlaceIndexedTameRealization.primalClass x =
      SelmerEigenspace.toKummerClass x :=
  rfl

@[simp]
theorem toPlaceIndexedTameRealization_dualClass
    (y : ReflectedDual (rho := rho) (omega := omega) (chi := chi)) :
    realization.toPlaceIndexedTameRealization.dualClass y =
      SelmerEigenspace.toKummerClass y :=
  rfl

/-- Empty-support Selmer membership makes the explicit context's quotient
valuation zero.  This is the named correspondence between Mathlib's
multiplicative `valuationOfNeZeroMod = 1` convention and the explicit
symbol's additive `ordModP = 0` convention. -/
theorem ordModP_toKummerClass_eq_zero
    {eta : InvolutiveBase.Character (PadicInt p) Delta}
    (v : Place (R := R)) (hv : IsTame v)
    (x : SelmerChi rho eta) :
    (realization.context v hv).ordModP
        (SelmerEigenspace.toKummerClass x) = 0 := by
  exact ordModP_toKummerClass_eq_zero_of_ord_eq_valuation
    v (realization.context v hv) (realization.ord_eq_valuation v hv) x

/-- Both seated Selmer legs have zero quotient valuation at every tame
height-one place. -/
def selectedValuationsZeroAt
    (v : Place (R := R)) (hv : IsTame v)
    (x : Primal (rho := rho) (chi := chi))
    (y : ReflectedDual (rho := rho) (omega := omega) (chi := chi)) :
    realization.toPlaceIndexedTameRealization.SelectedValuationsZeroAt
      v hv x y where
  primal := realization.ordModP_toKummerClass_eq_zero v hv x
  dual := realization.ordModP_toKummerClass_eq_zero v hv y

/-- **PROVEN tame row.** Every local reading of the two seated empty-support
Selmer eigenspaces is silent at a tame place. -/
theorem pairAt_eq_zero_at_tame_place
    (realization : Realization pairing Residue IsTame)
    (v : Place (R := R)) (hv : IsTame v)
    (x : Primal (rho := rho) (chi := chi))
    (y : ReflectedDual (rho := rho) (omega := omega) (chi := chi)) :
    pairing.pairAt v x y = 0 :=
  PlaceIndexedTameRealization.pairAt_eq_zero_of_p_dvd_ord
    (toPlaceIndexedTameRealization realization)
    (selectedValuationsZeroAt realization v hv x y)

/-- The two-place tame bookkeeping object is manufactured from the seated
Selmer predicate; it is not an additional support hypothesis. -/
def outsideTwoTameBookkeeping
    (distinguished auxiliary : Place (R := R))
    (x : Primal (rho := rho) (chi := chi))
    (y : ReflectedDual (rho := rho) (omega := omega) (chi := chi)) :
    realization.toPlaceIndexedTameRealization.OutsideTwoTameBookkeeping
      distinguished auxiliary x y where
  valuationsZero := fun v hv _ _ ↦
    realization.selectedValuationsZeroAt v hv x y

/-- **PROVEN tame part of `outside_two_readings`.** Only a proof that the
queried place is tame is needed; both Selmer valuation receipts come from the
literal seated carriers. -/
theorem outside_two_readings_at_tame_places
    (realization : Realization pairing Residue IsTame)
    (distinguished auxiliary : Place (R := R))
    (x : Primal (rho := rho) (chi := chi))
    (y : ReflectedDual (rho := rho) (omega := omega) (chi := chi))
    (v : Place (R := R)) (hv : IsTame v)
    (hdistinguished : v ≠ distinguished) (hauxiliary : v ≠ auxiliary) :
    pairing.pairAt v x y = 0 :=
  PlaceIndexedTameRealization.OutsideTwoTameBookkeeping.outside_two_readings_at_tame_places
      (outsideTwoTameBookkeeping realization distinguished auxiliary x y)
      v hv hdistinguished hauxiliary

/-- The full two-place support statement now asks only for residual non-tame
rows.  All tame rows are discharged by the preceding theorem. -/
theorem outside_two_readings_of_residual
    (realization : Realization pairing Residue IsTame)
    (distinguished auxiliary : Place (R := R))
    (x : Primal (rho := rho) (chi := chi))
    (y : ReflectedDual (rho := rho) (omega := omega) (chi := chi))
    (residual : ∀ v, ¬IsTame v → v ≠ distinguished → v ≠ auxiliary →
      pairing.pairAt v x y = 0)
    (v : Place (R := R)) (hdistinguished : v ≠ distinguished)
    (hauxiliary : v ≠ auxiliary) :
    pairing.pairAt v x y = 0 :=
  PlaceIndexedTameRealization.OutsideTwoTameBookkeeping.outside_two_readings_of_tame_and_residual
      (outsideTwoTameBookkeeping realization distinguished auxiliary x y)
      residual v hdistinguished hauxiliary

/-- For the seated Selmer eigenspaces, tame support bookkeeping is already
constructed.  Global reciprocity therefore identifies the distinguished
reading with the negative auxiliary reading once only the residual non-tame
rows are discharged. -/
theorem distinguished_eq_neg_auxiliary_of_reciprocity
    (realization : Realization pairing Residue IsTame)
    (reciprocity : GlobalReciprocityLaw pairing)
    (distinguished auxiliary : Place (R := R))
    (hne : distinguished ≠ auxiliary)
    (x : Primal (rho := rho) (chi := chi))
    (y : ReflectedDual (rho := rho) (omega := omega) (chi := chi))
    (residual : ∀ v, ¬IsTame v → v ≠ distinguished → v ≠ auxiliary →
      pairing.pairAt v x y = 0) :
    pairing.pairAt distinguished x y =
      -pairing.pairAt auxiliary x y :=
  reciprocity.pairAt_eq_neg_pairAt_of_outside_two
    distinguished auxiliary hne x y
      (realization.outside_two_readings_of_residual
        distinguished auxiliary x y residual)

end Realization

end Seated

end Fermat.Conservation.TamePlacePairing
