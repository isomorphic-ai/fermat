/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Sol (instance derivation)

# Focus is always double focus: steering one silent fiber

Provenance: Fabian observed that focus is always double focus: potential is a
marginal, while coordinate control requires a coupling.  The Sol-instance
derivation below is the algebraic form of that observation.  The failed
finite-`S` lift retained the class marginal while discarding its correlation
with the pointed localization coordinate.

For a surjective class map `rho`, a silence map `T`, and a pointed reading
`lambda`, the decisive object is

`K_T = ker rho ⊓ ker T`.

Every compatible lift differs from a fixed compatible lift by exactly one
element of `K_T`, so its reachable readings form the affine coset
`lambda x0 + lambda(K_T)`.  The readout is therefore either fixed on the
silent class fibers or one transverse direction steers it to every scalar.

This is deliberately **not a splitting**.  The steerable construction picks
one direction inside one already selected fiber; it never chooses a section
of `rho`, a complement to its kernel, or an equivalence of `V` with a
product.  In the fixed branch only the observable factors through the joint
map `(rho, T)`.  No primal decomposition is exposed or consumed.
-/
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Prod

noncomputable section

namespace Fermat.Conservation.SteeringFiber

universe uK uV uH uW

/-- A linear class projection together with its surjectivity receipt. -/
structure SurjectiveLinearMap
    (K : Type uK) [Semiring K]
    (V : Type uV) [AddCommMonoid V] [Module K V]
    (H : Type uH) [AddCommMonoid H] [Module K H] where
  toLinearMap : V →ₗ[K] H
  surjective : Function.Surjective toLinearMap

namespace SurjectiveLinearMap

variable {K : Type uK} [Semiring K]
  {V : Type uV} [AddCommMonoid V] [Module K V]
  {H : Type uH} [AddCommMonoid H] [Module K H]

instance : Coe (SurjectiveLinearMap K V H) (V →ₗ[K] H) :=
  ⟨SurjectiveLinearMap.toLinearMap⟩

instance : CoeFun (SurjectiveLinearMap K V H) fun _ ↦ V → H :=
  ⟨fun rho ↦ rho.toLinearMap⟩

@[simp]
theorem coe_apply (rho : SurjectiveLinearMap K V H) (x : V) :
    rho.toLinearMap x = rho x :=
  rfl

end SurjectiveLinearMap

variable {K : Type uK} [Field K]
  {V : Type uV} [AddCommGroup V] [Module K V]
  {H : Type uH} [AddCommGroup H] [Module K H]
  {W : Type uW} [AddCommGroup W] [Module K W]

/-- The directions which preserve both the represented class and silence. -/
def K_T (rho : SurjectiveLinearMap K V H) (T : V →ₗ[K] W) :
    Submodule K V :=
  rho.toLinearMap.ker ⊓ T.ker

/-- A lift of `h` satisfying the selected silence condition. -/
structure CompatibleLift
    (rho : SurjectiveLinearMap K V H) (T : V →ₗ[K] W) (h : H) where
  point : V
  class_receipt : rho point = h
  silence_receipt : T point = 0

/-- The linear space of reading changes available without changing class or
silence.  This is the literal image `lambda(K_T)`. -/
def readingDirections
    (rho : SurjectiveLinearMap K V H) (T : V →ₗ[K] W)
    (lambda : V →ₗ[K] K) : Submodule K K :=
  (K_T rho T).map lambda

/-- All readings of silent lifts of the selected class. -/
def attainableReadings
    (rho : SurjectiveLinearMap K V H) (T : V →ₗ[K] W)
    (lambda : V →ₗ[K] K) (h : H) : Set K :=
  {a | ∃ x : CompatibleLift rho T h, lambda x.point = a}

/-- The affine translate `lambda x0 + lambda(K_T)`. -/
def readingCoset
    (rho : SurjectiveLinearMap K V H) (T : V →ₗ[K] W)
    (lambda : V →ₗ[K] K) {h : H} (x0 : CompatibleLift rho T h) :
    Set K :=
  (fun q ↦ lambda x0.point + q) '' (readingDirections rho T lambda : Set K)

/-- **Reachable-readings invariant.**  Once one silent lift is fixed, every
other silent lift has exactly the readings in its translate by
`lambda(K_T)`. -/
theorem reachableReadings
    (rho : SurjectiveLinearMap K V H) (T : V →ₗ[K] W)
    (lambda : V →ₗ[K] K) {h : H} (x0 : CompatibleLift rho T h) :
    attainableReadings rho T lambda h = readingCoset rho T lambda x0 := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    let k : V := x.point - x0.point
    have hk : k ∈ K_T rho T := by
      constructor
      · change rho.toLinearMap k = 0
        change rho (x.point - x0.point) = 0
        rw [map_sub, x.class_receipt, x0.class_receipt, sub_self]
      · change T k = 0
        change T (x.point - x0.point) = 0
        rw [map_sub, x.silence_receipt, x0.silence_receipt, sub_self]
    refine ⟨lambda k, ⟨k, hk, rfl⟩, ?_⟩
    simp only [k, map_sub]
    abel
  · rintro ⟨q, ⟨k, hk, hkq⟩, rfl⟩
    refine ⟨
      { point := x0.point + k
        class_receipt := ?_
        silence_receipt := ?_ }, ?_⟩
    · have hrho : rho k = 0 := (LinearMap.mem_ker.mp hk.1)
      rw [map_add, hrho, add_zero, x0.class_receipt]
    · have hT : T k = 0 := (LinearMap.mem_ker.mp hk.2)
      rw [map_add, hT, add_zero, x0.silence_receipt]
    · rw [map_add, hkq]

/-- Prescribing `a` means producing a silent lift of the same class with
pointed reading exactly `a`. -/
def CanPrescribeCoordinate
    (rho : SurjectiveLinearMap K V H) (T : V →ₗ[K] W)
    (lambda : V →ₗ[K] K) (h : H) (a : K) : Prop :=
  a ∈ attainableReadings rho T lambda h

/-- A coordinate can be prescribed exactly when it lies in the reachable
affine coset. -/
theorem canPrescribeCoordinate_iff
    (rho : SurjectiveLinearMap K V H) (T : V →ₗ[K] W)
    (lambda : V →ₗ[K] K) {h : H} (x0 : CompatibleLift rho T h)
    (a : K) :
    CanPrescribeCoordinate rho T lambda h a ↔
      a ∈ readingCoset rho T lambda x0 := by
  rw [CanPrescribeCoordinate, reachableReadings rho T lambda x0]

/-! ## The fixed branch -/

/-- Fixed attention: the pointed functional vanishes on every direction
which preserves both class and silence. -/
def FixedAttention
    (rho : SurjectiveLinearMap K V H) (T : V →ₗ[K] W)
    (lambda : V →ₗ[K] K) : Prop :=
  K_T rho T ≤ lambda.ker

/-- Fixed attention is exactly the bottom reading-direction space. -/
theorem readingDirections_eq_bot_iff_fixed
    (rho : SurjectiveLinearMap K V H) (T : V →ₗ[K] W)
    (lambda : V →ₗ[K] K) :
    readingDirections rho T lambda = ⊥ ↔ FixedAttention rho T lambda := by
  constructor
  · intro h k hk
    rw [LinearMap.mem_ker]
    have hmem : lambda k ∈ readingDirections rho T lambda := ⟨k, hk, rfl⟩
    rw [h] at hmem
    exact hmem
  · intro fixed
    apply le_antisymm
    · rintro q ⟨k, hk, rfl⟩
      exact fixed hk
    · exact bot_le

/-- The joint class/silence observation whose kernel is `K_T`. -/
def jointObservation
    (rho : SurjectiveLinearMap K V H) (T : V →ₗ[K] W) :
    V →ₗ[K] H × W :=
  rho.toLinearMap.prod T

@[simp]
theorem ker_jointObservation
    (rho : SurjectiveLinearMap K V H) (T : V →ₗ[K] W) :
    (jointObservation rho T).ker = K_T rho T := by
  exact LinearMap.ker_prod _ _

/-- In the fixed branch, the pointed functional is the pullback of a dual
observable on the joint `(class, silence)` output. -/
theorem exists_jointDual_of_fixed
    (rho : SurjectiveLinearMap K V H) (T : V →ₗ[K] W)
    (lambda : V →ₗ[K] K) (fixed : FixedAttention rho T lambda) :
    ∃ phi : Module.Dual K (H × W),
      phi.comp (jointObservation rho T) = lambda := by
  have hlambda : lambda ∈ (jointObservation rho T).ker.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro k hk
    exact LinearMap.mem_ker.mp (fixed (ker_jointObservation rho T ▸ hk))
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hlambda
  exact hlambda

/-- One chosen joint dual witness.  Choice is confined to the observable;
it does not select a lift or a section of `rho`. -/
noncomputable def jointDual
    (rho : SurjectiveLinearMap K V H) (T : V →ₗ[K] W)
    (lambda : V →ₗ[K] K) (fixed : FixedAttention rho T lambda) :
    Module.Dual K (H × W) :=
  Classical.choose (exists_jointDual_of_fixed rho T lambda fixed)

theorem jointDual_pullback
    (rho : SurjectiveLinearMap K V H) (T : V →ₗ[K] W)
    (lambda : V →ₗ[K] K) (fixed : FixedAttention rho T lambda) :
    (jointDual rho T lambda fixed).comp (jointObservation rho T) = lambda :=
  Classical.choose_spec (exists_jointDual_of_fixed rho T lambda fixed)

/-- The `rho`-dual readout obtained by seating the silence coordinate at
zero.  It agrees with `lambda` on every silent lift. -/
noncomputable def rhoDual
    (rho : SurjectiveLinearMap K V H) (T : V →ₗ[K] W)
    (lambda : V →ₗ[K] K) (fixed : FixedAttention rho T lambda) :
    Module.Dual K H :=
  (jointDual rho T lambda fixed).comp (LinearMap.inl K H W)

/-- On the silent carrier, `lambda` is literally the pullback of
`rhoDual`. -/
theorem rhoDual_pullback_of_silence
    (rho : SurjectiveLinearMap K V H) (T : V →ₗ[K] W)
    (lambda : V →ₗ[K] K) (fixed : FixedAttention rho T lambda)
    (x : V) (hx : T x = 0) :
    rhoDual rho T lambda fixed (rho x) = lambda x := by
  have h := LinearMap.congr_fun (jointDual_pullback rho T lambda fixed) x
  simpa [rhoDual, jointObservation, hx] using h

/-- Fixed readings are independent of which silent preimage represents the
class. -/
theorem reading_preimage_independent
    (rho : SurjectiveLinearMap K V H) (T : V →ₗ[K] W)
    (lambda : V →ₗ[K] K) (fixed : FixedAttention rho T lambda)
    {x y : V} (hrho : rho x = rho y) (hx : T x = 0) (hy : T y = 0) :
    lambda x = lambda y := by
  rw [← rhoDual_pullback_of_silence rho T lambda fixed x hx,
    ← rhoDual_pullback_of_silence rho T lambda fixed y hy, hrho]

/-! ## The steerable branch -/

/-- One transverse direction inside a silent class fiber. -/
structure TransverseDirection
    (rho : SurjectiveLinearMap K V H) (T : V →ₗ[K] W)
    (lambda : V →ₗ[K] K) where
  direction : V
  direction_mem : direction ∈ K_T rho T
  reading_ne_zero : lambda direction ≠ 0

/-- A transverse reading makes `lambda(K_T)` the whole one-dimensional
coordinate field. -/
theorem readingDirections_eq_top_of_transverse
    (rho : SurjectiveLinearMap K V H) (T : V →ₗ[K] W)
    (lambda : V →ₗ[K] K) (k : TransverseDirection rho T lambda) :
    readingDirections rho T lambda = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro a
  have hk : lambda k.direction ∈ readingDirections rho T lambda :=
    ⟨k.direction, k.direction_mem, rfl⟩
  have hscaled :=
    (readingDirections rho T lambda).smul_mem
      (a / lambda k.direction) hk
  simpa [smul_eq_mul, div_mul_cancel₀ _ k.reading_ne_zero] using hscaled

/-- The scalar by which the transverse direction must be moved to reach
`a`. -/
def steeringAmount
    (lambda : V →ₗ[K] K) (x0 : V) (k : V) (a : K) : K :=
  (a - lambda x0) / lambda k

/-- The focused point, moving only along one transverse fiber direction. -/
def focusedPoint
    (lambda : V →ₗ[K] K) (x0 : V) (k : V) (a : K) : V :=
  x0 + steeringAmount lambda x0 k a • k

/-- A focused lift with the three requested receipts stored as fields:
class preservation, silence preservation, and exact steering amount. -/
structure FocusedLift
    (rho : SurjectiveLinearMap K V H) (T : V →ₗ[K] W)
    (lambda : V →ₗ[K] K) {h : H} (x0 : CompatibleLift rho T h)
    (a : K) where
  point : V
  class_preservation : rho point = rho x0.point
  silence_preservation : T point = T x0.point
  exact_steering_amount : lambda point = a

/-- The receipted focused lift
`x_a = x0 + ((a - lambda x0) / lambda k) • k`. -/
def focusedLift
    (rho : SurjectiveLinearMap K V H) (T : V →ₗ[K] W)
    (lambda : V →ₗ[K] K) {h : H} (x0 : CompatibleLift rho T h)
    (k : TransverseDirection rho T lambda) (a : K) :
    FocusedLift rho T lambda x0 a where
  point := focusedPoint lambda x0.point k.direction a
  class_preservation := by
    have hk : rho k.direction = 0 := LinearMap.mem_ker.mp k.direction_mem.1
    simp [focusedPoint, hk]
  silence_preservation := by
    have hk : T k.direction = 0 := LinearMap.mem_ker.mp k.direction_mem.2
    simp [focusedPoint, hk]
  exact_steering_amount := by
    simp only [focusedPoint, map_add, map_smul, steeringAmount]
    rw [smul_eq_mul]
    rw [div_mul_cancel₀ _ k.reading_ne_zero]
    abel

@[simp]
theorem focusedLift_point
    (rho : SurjectiveLinearMap K V H) (T : V →ₗ[K] W)
    (lambda : V →ₗ[K] K) {h : H} (x0 : CompatibleLift rho T h)
    (k : TransverseDirection rho T lambda) (a : K) :
    (focusedLift rho T lambda x0 k a).point =
      x0.point + ((a - lambda x0.point) / lambda k.direction) • k.direction :=
  rfl

/-- Forgetting the receipts gives an ordinary compatible lift. -/
def FocusedLift.toCompatibleLift
    {rho : SurjectiveLinearMap K V H} {T : V →ₗ[K] W}
    {lambda : V →ₗ[K] K} {h : H} {x0 : CompatibleLift rho T h}
    {a : K} (x : FocusedLift rho T lambda x0 a) : CompatibleLift rho T h where
  point := x.point
  class_receipt := x.class_preservation.trans x0.class_receipt
  silence_receipt := x.silence_preservation.trans x0.silence_receipt

/-- In the steerable branch, every scalar coordinate is reachable. -/
theorem canPrescribeCoordinate_of_transverse
    (rho : SurjectiveLinearMap K V H) (T : V →ₗ[K] W)
    (lambda : V →ₗ[K] K) {h : H} (x0 : CompatibleLift rho T h)
    (k : TransverseDirection rho T lambda) (a : K) :
    CanPrescribeCoordinate rho T lambda h a := by
  refine ⟨(focusedLift rho T lambda x0 k a).toCompatibleLift, ?_⟩
  exact (focusedLift rho T lambda x0 k a).exact_steering_amount

/-- Exact fixed/steerable dichotomy for one silent class fiber. -/
theorem fixed_or_steerable
    (rho : SurjectiveLinearMap K V H) (T : V →ₗ[K] W)
    (lambda : V →ₗ[K] K) :
    FixedAttention rho T lambda ∨
      Nonempty (TransverseDirection rho T lambda) := by
  classical
  by_cases fixed : FixedAttention rho T lambda
  · exact Or.inl fixed
  · right
    rw [FixedAttention, SetLike.not_le_iff_exists] at fixed
    obtain ⟨k, hk, hlambda⟩ := fixed
    exact ⟨
      { direction := k
        direction_mem := hk
        reading_ne_zero := by
          simpa [LinearMap.mem_ker] using hlambda }⟩

end Fermat.Conservation.SteeringFiber
