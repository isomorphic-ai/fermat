/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Conserve the fiber; process the quotient

For a linear readout `f`, the unknown is its kernel and the processed
coordinate is its range.  The canonical row

`0 → ker f → V → range f → 0`

is retained without choosing a section, complement, or product
decomposition.  A second readout acts only on `ker f`; its new processed
coordinate is the range of that restriction and its surviving unknown is
`ker f ∩ ker g`.

The fixed/steerable comparison below is deliberately bridged to the existing
`SteeringFiber` and `FocusConormal` algebra.  Equal kernels induce the
canonical equivalence of processed ranges through the common quotient; a
scalar proportionality is only its coordinate shadow.

Mega-mode: a proof does not eliminate the unknown; it processes one quotient
and transports the conserved fiber forward.
-/
import Fermat.Conservation.SteeringFiber
import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms

noncomputable section

namespace Fermat.Conservation.ReadoutLedger

universe uK uV uW uU uH uR

variable {K : Type uK} [Field K]
  {V : Type uV} [AddCommGroup V] [Module K V]
  {W : Type uW} [AddCommGroup W] [Module K W]
  {U : Type uU} [AddCommGroup U] [Module K U]
  {H : Type uH} [AddCommGroup H] [Module K H]
  {R : Type uR} [AddCommGroup R] [Module K R]

/-! ## One readout: the conserved exact row -/

/-- The part of the carrier still unknown after `f` is read. -/
abbrev unknown (f : V →ₗ[K] W) : Submodule K V :=
  f.ker

/-- The coordinate processed by `f`. -/
abbrev processed (f : V →ₗ[K] W) : Submodule K W :=
  LinearMap.range f

/-- The canonical inclusion of the conserved unknown. -/
def unknownInclusion (f : V →ₗ[K] W) : unknown f →ₗ[K] V :=
  f.ker.subtype

/-- The canonical surjection onto the processed range. -/
def processedProjection (f : V →ₗ[K] W) : V →ₗ[K] processed f :=
  f.rangeRestrict

theorem unknownInclusion_injective (f : V →ₗ[K] W) :
    Function.Injective (unknownInclusion f) :=
  Submodule.subtype_injective _

/-- Exactness at the original carrier: the projection forgets exactly the
conserved unknown and nothing else. -/
theorem exact_unknownInclusion_processedProjection (f : V →ₗ[K] W) :
    Function.Exact (unknownInclusion f) (processedProjection f) := by
  rw [LinearMap.exact_iff, processedProjection,
    LinearMap.ker_rangeRestrict, unknownInclusion, Submodule.range_subtype]

theorem processedProjection_surjective (f : V →ₗ[K] W) :
    Function.Surjective (processedProjection f) :=
  LinearMap.surjective_rangeRestrict f

/-- The complete unsplit short-exact receipt for one observation. -/
theorem conservedReadout_exactSequence (f : V →ₗ[K] W) :
    Function.Injective (unknownInclusion f) ∧
      Function.Exact (unknownInclusion f) (processedProjection f) ∧
      Function.Surjective (processedProjection f) :=
  ⟨unknownInclusion_injective f,
    exact_unknownInclusion_processedProjection f,
    processedProjection_surjective f⟩

section FiniteDimensional

variable [FiniteDimensional K V]

/-- The dimension shadow of the exact row.  It records conservation but
does not choose a splitting which realizes the sum. -/
theorem finrank_unknown_add_processed (f : V →ₗ[K] W) :
    Module.finrank K (unknown f) + Module.finrank K (processed f) =
      Module.finrank K V := by
  rw [Nat.add_comm]
  exact f.finrank_range_add_finrank_ker

end FiniteDimensional

/-! ## Two readouts: process only the first fiber -/

/-- The unknown retained after both readouts. -/
def secondUnknown (f : V →ₗ[K] W) (g : V →ₗ[K] U) :
    Submodule K V :=
  f.ker ⊓ g.ker

/-- The second readout restricted to the first conserved fiber. -/
def restrictedSecondReadout (f : V →ₗ[K] W) (g : V →ₗ[K] U) :
    f.ker →ₗ[K] U :=
  g.domRestrict f.ker

/-- The genuinely new coordinate processed by the second readout. -/
def newProcessed (f : V →ₗ[K] W) (g : V →ₗ[K] U) :
    Submodule K U :=
  LinearMap.range (restrictedSecondReadout f g)

/-- The second unknown as a submodule of the first unknown. -/
abbrev secondUnknownFiber (f : V →ₗ[K] W) (g : V →ₗ[K] U) :
    Submodule K f.ker :=
  (restrictedSecondReadout f g).ker

/-- The second row is again short exact, now inside the conserved first
fiber. -/
theorem secondReadout_exactSequence (f : V →ₗ[K] W)
    (g : V →ₗ[K] U) :
    Function.Injective (secondUnknownFiber f g).subtype ∧
      Function.Exact (secondUnknownFiber f g).subtype
        (restrictedSecondReadout f g).rangeRestrict ∧
      Function.Surjective (restrictedSecondReadout f g).rangeRestrict := by
  refine ⟨Submodule.subtype_injective _, ?_,
    LinearMap.surjective_rangeRestrict _⟩
  rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict,
    Submodule.range_subtype]

/-- Package the first readout as the surjective observation onto its actual
processed range. -/
def steeringProjection (f : V →ₗ[K] W) :
    SteeringFiber.SurjectiveLinearMap K V (processed f) where
  toLinearMap := processedProjection f
  surjective := processedProjection_surjective f

/-- The ambient second unknown is exactly the existing `SteeringFiber`
silent-fiber kernel with no extra silence constraint. -/
theorem secondUnknown_eq_steeringFiber
    (f : V →ₗ[K] W) (g : V →ₗ[K] U) :
    secondUnknown f g =
      SteeringFiber.K_T (steeringProjection f) g := by
  simp [secondUnknown, SteeringFiber.K_T, steeringProjection,
    processedProjection]

/-- The same bridge through the already-banked joint observation. -/
theorem secondUnknown_eq_ker_jointObservation
    (f : V →ₗ[K] W) (g : V →ₗ[K] U) :
    secondUnknown f g =
      (SteeringFiber.jointObservation (steeringProjection f) g).ker := by
  rw [SteeringFiber.ker_jointObservation]
  exact secondUnknown_eq_steeringFiber f g

/-- `FIXED`: the second readout vanishes on every direction left unknown by
the first. -/
def Fixed (f : V →ₗ[K] W) (g : V →ₗ[K] U) : Prop :=
  f.ker ≤ g.ker

/-- For a scalar second readout, the new processed range is literally the
existing `SteeringFiber.readingDirections` specialization. -/
theorem newProcessed_eq_readingDirections
    (f : V →ₗ[K] W) (g : V →ₗ[K] K) :
    newProcessed f g =
      SteeringFiber.readingDirections
        (steeringProjection f) (0 : V →ₗ[K] K) g := by
  simp [newProcessed, restrictedSecondReadout,
    SteeringFiber.readingDirections, SteeringFiber.K_T,
    steeringProjection, processedProjection]

/-- The ledger `FIXED` predicate is the old fixed-attention predicate on the
same conserved fiber. -/
theorem fixed_iff_steeringFixedAttention
    (f : V →ₗ[K] W) (g : V →ₗ[K] K) :
    Fixed f g ↔
      SteeringFiber.FixedAttention
        (steeringProjection f) (0 : V →ₗ[K] K) g := by
  simp [Fixed, SteeringFiber.FixedAttention, SteeringFiber.K_T,
    steeringProjection, processedProjection]

/-- Fixedness is exactly zero new processed information for readouts with an
arbitrary module-valued output. -/
theorem fixed_iff_newProcessed_eq_bot
    (f : V →ₗ[K] W) (g : V →ₗ[K] U) :
    Fixed f g ↔ newProcessed f g = ⊥ := by
  rw [newProcessed, LinearMap.range_eq_bot]
  constructor
  · intro fixed
    ext x
    exact LinearMap.mem_ker.mp (fixed x.property)
  · intro hzero x hx
    rw [LinearMap.mem_ker]
    have hvalue := LinearMap.congr_fun hzero ⟨x, hx⟩
    simpa [restrictedSecondReadout] using hvalue

/-- The scalar fixedness law is an export
of `SteeringFiber.readingDirections_eq_bot_iff_fixed`, not a parallel proof
of the two-readout dichotomy. -/
theorem fixed_iff_newProcessed_eq_bot_via_steeringFiber
    (f : V →ₗ[K] W) (g : V →ₗ[K] K) :
    Fixed f g ↔ newProcessed f g = ⊥ :=
  (fixed_iff_steeringFixedAttention f g).trans <|
    (SteeringFiber.readingDirections_eq_bot_iff_fixed
      (steeringProjection f) (0 : V →ₗ[K] K) g).symm.trans <| by
        rw [← newProcessed_eq_readingDirections f g]

/-- The same fixed condition is zero of the retained conormal class. -/
theorem fixed_iff_conormalClass_eq_zero
    (f : V →ₗ[K] W) (g : V →ₗ[K] K) :
    Fixed f g ↔ FocusConormal.conormalClass f g = 0 :=
  (FocusConormal.conormalClass_eq_zero_iff_ker_le f g).symm

/-- In the fixed branch a scalar second readout factors through the first
processed coordinate.  This is the existing conormal pullback law. -/
theorem fixed_iff_exists_pullback
    (f : V →ₗ[K] W) (g : V →ₗ[K] K) :
    Fixed f g ↔
      ∃ phi : Module.Dual K W, phi.comp f = g :=
  (fixed_iff_conormalClass_eq_zero f g).trans
    (FocusConormal.conormalClass_eq_zero_iff_exists_dual_pullback f g)

/-! ## Equal unknowns: the invariant processed-range comparison -/

/-- Two readouts conserve exactly the same unknown. -/
def SameUnknown (f : V →ₗ[K] W) (g : V →ₗ[K] U) : Prop :=
  f.ker = g.ker

theorem sameUnknown_iff_ker_eq
    (f : V →ₗ[K] W) (g : V →ₗ[K] U) :
    SameUnknown f g ↔ f.ker = g.ker :=
  Iff.rfl

/-- Equal kernels canonically identify the two processed ranges through the
common quotient of the original carrier. -/
noncomputable def processedRangeEquiv
    (f : V →ₗ[K] W) (g : V →ₗ[K] U)
    (hker : SameUnknown f g) : processed f ≃ₗ[K] processed g :=
  f.quotKerEquivRange.symm |>.trans <|
    (Submodule.quotEquivOfEq f.ker g.ker hker).trans
      g.quotKerEquivRange

/-- The canonical range equivalence sends the reading of `x` by `f` to the
reading of that same `x` by `g`. -/
@[simp]
theorem processedRangeEquiv_apply
    (f : V →ₗ[K] W) (g : V →ₗ[K] U)
    (hker : SameUnknown f g) (x : V) :
    processedRangeEquiv f g hker
        ⟨f x, LinearMap.mem_range_self f x⟩ =
      ⟨g x, LinearMap.mem_range_self g x⟩ := by
  apply Subtype.ext
  simp [processedRangeEquiv]

/-- **Same-unknown invariant.**  Equality of kernels is equivalent to the
existence of a unique processed-range equivalence commuting with both
readouts.  A bare equivalence of ranges would be too weak; the commuting law
is what makes this comparison canonical and recovers the common kernel. -/
theorem sameUnknown_iff_existsUnique_processedRangeEquiv
    (f : V →ₗ[K] W) (g : V →ₗ[K] U) :
    SameUnknown f g ↔
      ∃! Φ : processed f ≃ₗ[K] processed g,
        ∀ x : V,
          Φ ⟨f x, LinearMap.mem_range_self f x⟩ =
            ⟨g x, LinearMap.mem_range_self g x⟩ := by
  constructor
  · intro hker
    refine ⟨processedRangeEquiv f g hker,
      processedRangeEquiv_apply f g hker, ?_⟩
    intro Φ hΦ
    apply LinearEquiv.ext
    intro y
    rcases y.property with ⟨x, hx⟩
    have hy : y = ⟨f x, LinearMap.mem_range_self f x⟩ := by
      apply Subtype.ext
      exact hx.symm
    rw [hy, hΦ x, processedRangeEquiv_apply]
  · rintro ⟨Φ, hΦ, -⟩
    apply Submodule.ext
    intro x
    constructor
    · intro hx
      rw [LinearMap.mem_ker] at hx ⊢
      have hzero :
          (⟨f x, LinearMap.mem_range_self f x⟩ : processed f) = 0 := by
        apply Subtype.ext
        exact hx
      have h := hΦ x
      rw [hzero, map_zero] at h
      exact congrArg Subtype.val h.symm
    · intro hx
      rw [LinearMap.mem_ker] at hx ⊢
      have hzero :
          (⟨g x, LinearMap.mem_range_self g x⟩ : processed g) = 0 := by
        apply Subtype.ext
        exact hx
      have h := hΦ x
      rw [hzero] at h
      have hsource :
          (⟨f x, LinearMap.mem_range_self f x⟩ : processed f) = 0 := by
        apply Φ.injective
        simpa using h
      exact congrArg Subtype.val hsource

/-! ## A receipted normalized probe, with its full fiber retained -/

/-- The normalized fiber of a nonzero scalar readout. -/
def NormalizedFiber (q : R →ₗ[K] K) :=
  {y : R // q y = 1}

/-- The same normalized fiber as a set in the ambient carrier. -/
def normalizedFiberSet (q : R →ₗ[K] K) : Set R :=
  {y | q y = 1}

/-- The affine translate `y₀ + ker q`, expressed without choosing a
complement. -/
def affineKernelCoset (q : R →ₗ[K] K) (y₀ : R) : Set R :=
  {y | y - y₀ ∈ q.ker}

/-- A nonzero scalar readout has a normalized receipt.  The witness is
constructed by rescaling one point where the readout is nonzero. -/
theorem normalizedFiber_nonempty (q : R →ₗ[K] K) (hq : q ≠ 0) :
    Nonempty (NormalizedFiber q) := by
  have hexists : ∃ z : R, q z ≠ 0 := by
    by_contra h
    push Not at h
    apply hq
    ext z
    exact h z
  obtain ⟨z, hz⟩ := hexists
  refine ⟨⟨(q z)⁻¹ • z, ?_⟩⟩
  simp [hz]

/-- Every normalized point displays the whole normalized fiber as its
affine translate by the conserved kernel. -/
theorem normalizedFiberSet_eq_affineKernelCoset
    (q : R →ₗ[K] K) (y₀ : R) (hy₀ : q y₀ = 1) :
    normalizedFiberSet q = affineKernelCoset q y₀ := by
  ext y
  simp only [normalizedFiberSet, Set.mem_setOf_eq, affineKernelCoset,
    LinearMap.mem_ker, map_sub, hy₀]
  constructor
  · intro hy
    rw [hy, sub_self]
  · intro hy
    exact sub_eq_zero.mp hy

/-! ## Rank-one factorization along a scalar readout -/

/-- A functional lawful on the conserved fiber is constant on every readout
fiber.  This is exported through the existing `SteeringFiber` quotient
preimage-independence theorem. -/
theorem eq_of_readout_eq
    (q r : R →ₗ[K] K) (hker : q.ker ≤ r.ker)
    {y z : R} (hyz : q y = q z) :
    r y = r z := by
  apply SteeringFiber.scalarQuestionDual_preimage_independent q r hker
  apply (Submodule.Quotient.eq q.ker).2
  rw [LinearMap.mem_ker, map_sub, hyz, sub_self]

/-- A scalar functional whose kernel contains `ker q` has a unique
coefficient through `q`.  The existence proof deliberately passes through
the already-banked conormal kernel and pullback equivalences. -/
theorem existsUnique_rankOneFactorization
    (q r : R →ₗ[K] K) (hq : q ≠ 0) (hker : q.ker ≤ r.ker) :
    ∃! Λ : K, ∀ y : R, r y = Λ * q y := by
  have hclass : FocusConormal.conormalClass q r = 0 :=
    (FocusConormal.conormalClass_eq_zero_iff_ker_le q r).2 hker
  obtain ⟨phi, hphi⟩ :=
    (FocusConormal.conormalClass_eq_zero_iff_exists_dual_pullback q r).1
      hclass
  refine ⟨phi 1, ?_, ?_⟩
  · intro y
    calc
      r y = phi (q y) := by
        symm
        exact LinearMap.congr_fun hphi y
      _ = phi 1 * q y := by
        simpa [smul_eq_mul, mul_comm] using phi.map_smul (q y) (1 : K)
  · intro Λ hΛ
    have hexists : ∃ z : R, q z ≠ 0 := by
      by_contra h
      push Not at h
      apply hq
      ext z
      exact h z
    obtain ⟨z, hz⟩ := hexists
    apply mul_right_cancel₀ hz
    rw [← hΛ z]
    calc
      r z = phi (q z) := by
        symm
        exact LinearMap.congr_fun hphi z
      _ = phi 1 * q z := by
        simpa [smul_eq_mul, mul_comm] using phi.map_smul (q z) (1 : K)

/-- Bilinear rank-one factorization on every selected carrier.  No probe is
exported: a normalized receipt is used only inside the construction of the
unique linear coefficient `Λ`. -/
theorem existsUnique_bilinearRankOneFactorization
    (q : R →ₗ[K] K) (B : H →ₗ[K] R →ₗ[K] K) (hq : q ≠ 0)
    (hker : ∀ h : H, q.ker ≤ (B h).ker) :
    ∃! Λ : H →ₗ[K] K, ∀ h : H, ∀ y : R,
      B h y = Λ h * q y := by
  let y₀ : NormalizedFiber q := Classical.choice (normalizedFiber_nonempty q hq)
  let Λ : H →ₗ[K] K := (LinearMap.applyₗ y₀.1).comp B
  refine ⟨Λ, ?_, ?_⟩
  · intro h y
    obtain ⟨a, ha, -⟩ :=
      existsUnique_rankOneFactorization q (B h) hq (hker h)
    have hΛ : Λ h = a := by
      change B h y₀.1 = a
      calc
        B h y₀.1 = a * q y₀.1 := ha y₀.1
        _ = a := by rw [y₀.property, mul_one]
    simpa [hΛ] using ha y
  · intro Λ' hΛ'
    ext h
    change Λ' h = B h y₀.1
    calc
      Λ' h = Λ' h * q y₀.1 := by rw [y₀.property, mul_one]
      _ = B h y₀.1 := (hΛ' h y₀.1).symm

/-- For nonzero scalar readouts, equal unknowns have the familiar unique
nonzero proportionality coefficient.  This is only the one-coordinate
shadow of `processedRangeEquiv`. -/
theorem sameUnknown_iff_existsUnique_unitProportionality
    (f g : V →ₗ[K] K) (hf : f ≠ 0) (hg : g ≠ 0) :
    SameUnknown f g ↔
      ∃! u : K, u ≠ 0 ∧ ∀ x : V, g x = u * f x := by
  constructor
  · intro hker
    obtain ⟨u, hu, hu_unique⟩ :=
      existsUnique_rankOneFactorization f g hf hker.le
    have hu_ne : u ≠ 0 := by
      intro huz
      apply hg
      ext x
      simpa [huz] using hu x
    refine ⟨u, ⟨hu_ne, hu⟩, ?_⟩
    intro v hv
    exact hu_unique v hv.2
  · rintro ⟨u, ⟨hu_ne, hu⟩, -⟩
    apply Submodule.ext
    intro x
    rw [LinearMap.mem_ker, LinearMap.mem_ker, hu x]
    constructor
    · intro hx
      rw [hx, mul_zero]
    · intro hx
      exact (mul_eq_zero.mp hx).resolve_left hu_ne

end Fermat.Conservation.ReadoutLedger
