import CRNT.Dynamics.OmegaLimitOrderConvex
import CRNT.Dynamics.Monotone
import CRNT.Dynamics.LaSalle
import CRNT.Dynamics.LaSalleConvergence
import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.Flow
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Separation.Hausdorff

/-!
# Strong-order separation and conditional omega-limit convexity

Strong-order and separator arguments complement the monotone comparison
results. Displayed comparability/separation hypotheses remain inputs.
The LaSalle/unique-equilibrium wrappers in `LaSalleConvergence` and
`OmegaLimitOrderConvex` do not establish Hirsch generic convergence.
-/

open Set Filter Topology
open scoped BigOperators NNReal CRNT

namespace CRNT

section StrongOrder

variable {S : Type} [Fintype S]

/-- **The strong order** `≪` of Hirsch–Smith (*Monotone Dynamical Systems*, Handbook of
Differential Equations vol. 2, 2002): `x ≪ y` iff `x ≤ y` and `x` lies in the *interior* of the
down-set `↓ y = {w | w ≤ y}`, i.e. the gap `y − x` is strictly positive in every coordinate.

For a finite species set this is literally the interior condition: `int (↓ y) = {x | ∀ s, x s < y s}`
in the product topology on `S → ℝ`. -/
def StronglyBelow (x y : Concentration S) : Prop := x ≤ y ∧ ∀ s, x s < y s

/-- **The strong order with a uniform gap**: `x ≪ y` iff there is `δ > 0` with `x + δ ≤ y`
coordinatewise.  For a finite nonempty species set this is equivalent to `StronglyBelow`; the
uniform version is the one used in the monotone-systems literature, where `≪` expresses that the
orbit *cannot approach the boundary* of the down-set. -/
def StronglyBelowGap (x y : Concentration S) : Prop := ∃ δ > 0, ∀ s, x s + δ ≤ y s

/-- Notation for the strong order.  It is scoped (`CRNT`) so that it does not clash with the
`≪` of `MeasureTheory` (which denotes absolute continuity). -/
scoped[CRNT] infixl:50 " ≪ " => StronglyBelow

omit [Fintype S] in
theorem StronglyBelow.le {x y : Concentration S} (h : x ≪ y) : x ≤ y := h.1

omit [Fintype S] in
theorem StronglyBelow.lt {x y : Concentration S} (h : x ≪ y) (s : S) : x s < y s := h.2 s

omit [Fintype S] in
/-- The strong order is transitive. -/
theorem StronglyBelow.trans {x y z : Concentration S} (h₁ : x ≪ y) (h₂ : y ≪ z) : x ≪ z :=
  ⟨fun s => le_trans (h₁.1 s) (h₂.1 s), fun s => lt_of_lt_of_le (h₁.2 s) (h₂.1 s)⟩

omit [Fintype S] in
/-- A uniform gap implies the strong order. -/
theorem StronglyBelow.of_gap {x y : Concentration S} (h : StronglyBelowGap x y) : x ≪ y := by
  obtain ⟨δ, hδ, hδ'⟩ := h
  refine ⟨fun s => le_trans (le_add_of_nonneg_right (le_of_lt hδ)) (hδ' s), fun s => ?_⟩
  have h' := hδ' s
  linarith

end StrongOrder

section StrongOrderNonempty

variable {S : Type} [Fintype S] [Nonempty S]

omit [Fintype S] in
/-- The strong order is a strict order: `x ≪ y` forces `x ≠ y`. -/
theorem StronglyBelow.ne {x y : Concentration S} (h : x ≪ y) : x ≠ y := by
  intro hxy
  subst hxy
  exact lt_irrefl _ (h.2 (Classical.choice (inferInstance : Nonempty S)))

omit [Fintype S] in
/-- The strong order implies the strict comparison `x ≤ y ∧ x ≠ y`. -/
theorem StronglyBelow.strictlyBelow {x y : Concentration S} (h : x ≪ y) : x ≤ y ∧ x ≠ y :=
  ⟨h.1, h.ne⟩

omit [Fintype S] in
/-- The strong order is asymmetric. -/
theorem StronglyBelow.asymm {x y : Concentration S} (h : x ≪ y) : ¬ (y ≪ x) := by
  intro h₂
  exact (not_lt_of_ge (h₂.1 (Classical.choice (inferInstance : Nonempty S))) (h.2 _)).elim

omit [Fintype S] in
/-- The strong order is irreflexive. -/
theorem StronglyBelow.irrefl {x : Concentration S} : ¬ (x ≪ x) :=
  fun h => (StronglyBelow.asymm h h).elim

omit [Fintype S] [Nonempty S] in
/-- Points below a strongly-below point are strongly below it as well. -/
theorem StronglyBelow.lt_of_le {x y z : Concentration S} (h : x ≪ y) (hz : z ≤ x) : z ≪ y :=
  ⟨fun s => le_trans (hz s) (h.1 s), fun s => lt_of_le_of_lt (hz s) (h.2 s)⟩

/-- **A uniform margin exists.**  If `x ≪ y` and the species set is finite and nonempty, there is
`δ > 0` with `x + δ ≤ y` coordinatewise: the gap `y − x` is bounded away from zero in every
coordinate. -/
theorem StronglyBelow.gap {x y : Concentration S} (h : x ≪ y) : StronglyBelowGap x y := by
  classical
  set m : ℝ := (Finset.univ.image (fun s => x s - y s)).max'
    (Finset.image_nonempty.mpr Finset.univ_nonempty) with hm
  have hgreat : IsGreatest ((Finset.univ.image (fun s => x s - y s)) : Set ℝ) m := by
    rw [hm]
    exact Finset.isGreatest_max' _ _
  have hmle : ∀ s, x s - y s ≤ m := fun s =>
    hgreat.2 (Finset.mem_image_of_mem (fun s => x s - y s) (Finset.mem_univ s))
  have hmneg : m < 0 := by
    obtain ⟨s, -, hs⟩ := Finset.mem_image.mp
      (show m ∈ (Finset.univ.image (fun s => x s - y s)) by rw [hm]; exact Finset.max'_mem _ _)
    have h1 : x s - y s < 0 := by linarith [h.2 s]
    linarith
  refine ⟨(-m) / 2, ?_, fun s => ?_⟩
  · linarith
  · have h1 := hmle s
    linarith

/-- The strong order and the uniform-gap strong order coincide for a finite nonempty species set. -/
theorem stronglyBelow_iff_gap {x y : Concentration S} :
    (x ≪ y) ↔ StronglyBelowGap x y :=
  ⟨StronglyBelow.gap, StronglyBelow.of_gap⟩

end StrongOrderNonempty

section Separators

variable {S : Type} [Fintype S]

/-- A continuous functional `φ` is a **monotone separating functional** for the point `z` if it is
order-monotone (increasing), vanishes at `z`, separates `z` from the points that are not below `z`,
and is *strictly* separating in the strong order: `φ y < 0` forces `y ≪ z`.

These are exactly the properties used by the classical non-ordering argument: the separating
functional detects the strong order, and the strong order is incompatible with an orbit that is
incomparable with `z`. -/
def IsMonotoneSeparator (z : Concentration S) (φ : Concentration S → ℝ) : Prop :=
  Continuous φ ∧ (∀ x y : Concentration S, x ≤ y → φ x ≤ φ y) ∧ φ z = 0 ∧
    (∀ y : Concentration S, φ y ≤ 0 ↔ y ≤ z) ∧ (∀ y : Concentration S, φ y < 0 → y ≪ z)

end Separators

section SeparatorsExplicit

variable {S : Type} [Fintype S] [Nonempty S]

/-- **The monotone separating functional** of Hirsch–Smith, in the "above" direction:
`sepAbove z y = max_s (y s − z s)`.  It is continuous and order-monotone (increasing), vanishes at
`z`, and is *positive* exactly at the points which are **not** below `z`. -/
noncomputable def sepAbove (z y : Concentration S) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun s => y s - z s)

/-- **The monotone separating functional**, in the "below" direction (the dual of `sepAbove`):
`sepBelow z y = max_s (z s − y s)`.  It is continuous and order-*anti*-monotone, vanishes at `z`,
and is *positive* exactly at the points which are **not** above `z`. -/
noncomputable def sepBelow (z y : Concentration S) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun s => z s - y s)

theorem sepAbove_continuous (z : Concentration S) : Continuous (sepAbove z) := by
  unfold sepAbove
  exact Continuous.finset_sup'_apply Finset.univ_nonempty
    (fun s _ => (continuous_apply s).sub continuous_const)

theorem sepBelow_continuous (z : Concentration S) : Continuous (sepBelow z) := by
  unfold sepBelow
  exact Continuous.finset_sup'_apply Finset.univ_nonempty
    (fun s _ => (continuous_const.sub (continuous_apply s)))

theorem sepAbove_mono {z x y : Concentration S} (h : x ≤ y) : sepAbove z x ≤ sepAbove z y := by
  unfold sepAbove
  rw [Finset.sup'_le_iff]
  intro s _
  have h1 := h s
  calc x s - z s ≤ y s - z s := by linarith
    _ ≤ Finset.univ.sup' Finset.univ_nonempty (fun s' => y s' - z s') :=
        Finset.le_sup' (fun s' => y s' - z s') (Finset.mem_univ s)

theorem sepBelow_antimono {z x y : Concentration S} (h : x ≤ y) : sepBelow z x ≥ sepBelow z y := by
  unfold sepBelow
  rw [ge_iff_le]
  rw [Finset.sup'_le_iff]
  intro s _
  have h1 := h s
  calc z s - y s ≤ z s - x s := by linarith
    _ ≤ Finset.univ.sup' Finset.univ_nonempty (fun s' => z s' - x s') :=
        Finset.le_sup' (fun s' => z s' - x s') (Finset.mem_univ s)

theorem sepAbove_self (z : Concentration S) : sepAbove z z = 0 := by
  unfold sepAbove
  exact Finset.sup'_eq_of_forall Finset.univ_nonempty (fun s => z s - z s) (fun s _ => by simp)

theorem sepBelow_self (z : Concentration S) : sepBelow z z = 0 := by
  unfold sepBelow
  exact Finset.sup'_eq_of_forall Finset.univ_nonempty (fun s => z s - z s) (fun s _ => by simp)

theorem sepAbove_pos_iff {z y : Concentration S} : 0 < sepAbove z y ↔ ∃ s, y s > z s := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have h' : sepAbove z y ≤ 0 := by
      unfold sepAbove
      exact (Finset.sup'_le_iff Finset.univ_nonempty (fun s => y s - z s)).mpr
        (fun s _ => by have := hcon s; linarith)
    linarith
  · rintro ⟨s, hs⟩
    have h1 : y s - z s ≤ sepAbove z y := by
      unfold sepAbove
      exact Finset.le_sup' (fun s' => y s' - z s') (Finset.mem_univ s)
    linarith

theorem sepAbove_le_zero_iff {z y : Concentration S} : sepAbove z y ≤ 0 ↔ y ≤ z := by
  constructor
  · intro h s
    have h1 : y s - z s ≤ sepAbove z y := by
      unfold sepAbove
      exact Finset.le_sup' (fun s' => y s' - z s') (Finset.mem_univ s)
    linarith
  · intro h
    unfold sepAbove
    refine (Finset.sup'_le_iff Finset.univ_nonempty (fun s => y s - z s)).mpr ?_
    intro s _
    have h1 := h s
    linarith

theorem sepBelow_pos_iff {z y : Concentration S} : 0 < sepBelow z y ↔ ∃ s, z s > y s := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have h' : sepBelow z y ≤ 0 := by
      unfold sepBelow
      exact (Finset.sup'_le_iff Finset.univ_nonempty (fun s => z s - y s)).mpr
        (fun s _ => by have := hcon s; linarith)
    linarith
  · rintro ⟨s, hs⟩
    have h1 : z s - y s ≤ sepBelow z y := by
      unfold sepBelow
      exact Finset.le_sup' (fun s' => z s' - y s') (Finset.mem_univ s)
    linarith

theorem sepBelow_le_zero_iff {z y : Concentration S} : sepBelow z y ≤ 0 ↔ z ≤ y := by
  constructor
  · intro h s
    have h1 : z s - y s ≤ sepBelow z y := by
      unfold sepBelow
      exact Finset.le_sup' (fun s' => z s' - y s') (Finset.mem_univ s)
    linarith
  · intro h
    unfold sepBelow
    refine (Finset.sup'_le_iff Finset.univ_nonempty (fun s => z s - y s)).mpr ?_
    intro s _
    have h1 := h s
    linarith

/-- The canonical monotone separating functional `sepAbove z` satisfies `IsMonotoneSeparator`. -/
theorem isMonotoneSeparator_sepAbove (z : Concentration S) : IsMonotoneSeparator z (sepAbove z) := by
  refine ⟨sepAbove_continuous z, fun x y hxy => sepAbove_mono hxy, sepAbove_self z,
    fun y => sepAbove_le_zero_iff, ?_⟩
  intro y hy
  refine ⟨fun s => ?_, fun s => ?_⟩
  · have h1 : y s - z s ≤ sepAbove z y := by
      unfold sepAbove
      exact Finset.le_sup' (fun s' => y s' - z s') (Finset.mem_univ s)
    linarith
  · have h1 : y s - z s ≤ sepAbove z y := by
      unfold sepAbove
      exact Finset.le_sup' (fun s' => y s' - z s') (Finset.mem_univ s)
    linarith

end SeparatorsExplicit

section OmegaLimitSeparation

variable {S : Type} [Fintype S]

/-- **One-sided separation of the ω-limit set (below).**  If the forward orbit of `x₀` never goes
below `z` — i.e. there is no `t` with `ϕ t x₀ ≤ z` — then every point `y` of the ω-limit set has a
coordinate `s` with `y s ≥ z s`; in other words `z` is *not* above `y`.

*Proof.*  The orbit is contained in the closed set `{w | ∃ s, w s ≥ z s}` (a finite union of closed
half-spaces), and the ω-limit set is contained in the closure of every tail of the orbit. -/
theorem omegaLimit_exists_ge_of_incomparable_below
    (ϕ : Flow ℝ≥0 (Concentration S)) (x₀ : Concentration S) (z : Concentration S)
    (h : ¬ ∃ t : ℝ≥0, ϕ t x₀ ≤ z) :
    ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∃ s, y s ≥ z s := by
  intro y hy
  have hmem : ∀ t : ℝ≥0, ∃ s, (ϕ t x₀) s ≥ z s := by
    intro t
    by_contra hcon
    push Not at hcon
    exact h ⟨t, fun s => le_of_lt (hcon s)⟩
  have hsub : Set.image2 ϕ (Set.Ici 0) {x₀} ⊆ {w : Concentration S | ∃ s, w s ≥ z s} := by
    intro w hw
    obtain ⟨t, ht, b, hb, heq⟩ := hw
    have hb' : b = x₀ := Set.mem_singleton_iff.mp hb
    obtain ⟨s, hs⟩ := hmem t
    exact ⟨s, by rw [← heq, hb']; exact hs⟩
  have hC : IsClosed {w : Concentration S | ∃ s, w s ≥ z s} := by
    have h2 : {w : Concentration S | ∃ s, w s ≥ z s} =
        Set.iUnion (fun s : S => {w : Concentration S | z s ≤ w s}) := by
      ext w
      constructor
      · intro hw
        obtain ⟨s, hws⟩ := Set.mem_ofPred.mp hw
        exact Set.mem_iUnion.mpr ⟨s, show z s ≤ w s from hws⟩
      · intro hw
        obtain ⟨s, hws⟩ := Set.mem_iUnion.mp hw
        exact Set.mem_ofPred.mpr ⟨s, show w s ≥ z s from hws⟩
    rw [h2]
    exact isClosed_iUnion_of_finite fun s =>
      isClosed_le (continuous_const : Continuous fun _ : Concentration S => z s)
        (continuous_apply s)
  have hy' : y ∈ closure (Set.image2 ϕ (Set.Ici 0) {x₀}) :=
    (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) (u := Set.Ici 0)
      (Ici_mem_atTop 0)) hy
  exact closure_minimal subset_rfl hC (closure_mono hsub hy')

/-- **One-sided separation of the ω-limit set (above).**  If the forward orbit of `x₀` never goes
above `z` — i.e. there is no `t` with `z ≤ ϕ t x₀` — then every point `y` of the ω-limit set has a
coordinate `s` with `z s ≥ y s`; in other words `z` is *not* below `y`. -/
theorem omegaLimit_exists_le_of_incomparable_above
    (ϕ : Flow ℝ≥0 (Concentration S)) (x₀ : Concentration S) (z : Concentration S)
    (h : ¬ ∃ t : ℝ≥0, z ≤ ϕ t x₀) :
    ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∃ s, z s ≥ y s := by
  intro y hy
  have hmem : ∀ t : ℝ≥0, ∃ s, z s ≥ (ϕ t x₀) s := by
    intro t
    by_contra hcon
    push Not at hcon
    exact h ⟨t, fun s => le_of_lt (hcon s)⟩
  have hsub : Set.image2 ϕ (Set.Ici 0) {x₀} ⊆ {w : Concentration S | ∃ s, z s ≥ w s} := by
    intro w hw
    obtain ⟨t, ht, b, hb, heq⟩ := hw
    have hb' : b = x₀ := Set.mem_singleton_iff.mp hb
    obtain ⟨s, hs⟩ := hmem t
    exact ⟨s, by rw [← heq, hb']; exact hs⟩
  have hC : IsClosed {w : Concentration S | ∃ s, z s ≥ w s} := by
    have h2 : {w : Concentration S | ∃ s, z s ≥ w s} =
        Set.iUnion (fun s : S => {w : Concentration S | w s ≤ z s}) := by
      ext w
      constructor
      · intro hw
        obtain ⟨s, hws⟩ := Set.mem_ofPred.mp hw
        exact Set.mem_iUnion.mpr ⟨s, show w s ≤ z s from hws⟩
      · intro hw
        obtain ⟨s, hws⟩ := Set.mem_iUnion.mp hw
        exact Set.mem_ofPred.mpr ⟨s, show z s ≥ w s from hws⟩
    rw [h2]
    exact isClosed_iUnion_of_finite fun s =>
      isClosed_le (continuous_apply s)
        (continuous_const : Continuous fun _ : Concentration S => z s)
  have hy' : y ∈ closure (Set.image2 ϕ (Set.Ici 0) {x₀}) :=
    (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) (u := Set.Ici 0)
      (Ici_mem_atTop 0)) hy
  exact closure_minimal subset_rfl hC (closure_mono hsub hy')

/-- **The ω-limit set straddles an incomparable point.**  If the orbit of `x₀` is not comparable with
`z` — neither `x(t) ≤ z` nor `z ≤ x(t)` ever holds — then every ω-limit point `y` has a coordinate
above `z` and a coordinate below `z`: the ω-limit set cannot be separated from `z` by the order. -/
theorem omegaLimit_straddles_of_incomparable
    (ϕ : Flow ℝ≥0 (Concentration S)) (x₀ : Concentration S) (z : Concentration S)
    (h₁ : ¬ ∃ t : ℝ≥0, ϕ t x₀ ≤ z) (h₂ : ¬ ∃ t : ℝ≥0, z ≤ ϕ t x₀) :
    ∀ y ∈ omegaLimit atTop ϕ {x₀}, (∃ s, y s ≥ z s) ∧ (∃ t, z t ≥ y t) := by
  intro y hy
  exact ⟨omegaLimit_exists_ge_of_incomparable_below ϕ x₀ z h₁ y hy,
    omegaLimit_exists_le_of_incomparable_above ϕ x₀ z h₂ y hy⟩

/-- **The strong order is excluded in the incomparable-orbit case (below).**  If the orbit never
goes below `z`, no ω-limit point is *strongly* below `z`: the strong order `y ≪ z` would require
`y s < z s` in every coordinate, contradicting the one-sided separation above. -/
theorem omegaLimit_not_stronglyBelow_of_incomparable_below
    (ϕ : Flow ℝ≥0 (Concentration S)) (x₀ : Concentration S) (z : Concentration S)
    (h : ¬ ∃ t : ℝ≥0, ϕ t x₀ ≤ z) :
    ∀ y ∈ omegaLimit atTop ϕ {x₀}, ¬ (y ≪ z) := by
  intro y hy hstrong
  obtain ⟨s, hs⟩ := omegaLimit_exists_ge_of_incomparable_below ϕ x₀ z h y hy
  exact (not_lt_of_ge hs (hstrong.2 s)).elim

/-- **The strong order is excluded in the incomparable-orbit case (above).**  If the orbit never
goes above `z`, no ω-limit point is *strongly* above `z`. -/
theorem omegaLimit_not_stronglyAbove_of_incomparable_above
    (ϕ : Flow ℝ≥0 (Concentration S)) (x₀ : Concentration S) (z : Concentration S)
    (h : ¬ ∃ t : ℝ≥0, z ≤ ϕ t x₀) :
    ∀ y ∈ omegaLimit atTop ϕ {x₀}, ¬ (z ≪ y) := by
  intro y hy hstrong
  obtain ⟨s, hs⟩ := omegaLimit_exists_le_of_incomparable_above ϕ x₀ z h y hy
  exact (not_lt_of_ge hs (hstrong.2 s)).elim

/-- **A ω-limit point below an incomparable point touches it.**  If the orbit never goes below `z`
and `y ≤ z` with `y ∈ Ω`, then `y` and `z` agree in at least one coordinate: the inequality cannot
be strict in every coordinate. -/
theorem omegaLimit_touch_of_le_of_incomparable_below
    (ϕ : Flow ℝ≥0 (Concentration S)) (x₀ : Concentration S) (z : Concentration S)
    (h : ¬ ∃ t : ℝ≥0, ϕ t x₀ ≤ z)
    (y : Concentration S) (hy : y ∈ omegaLimit atTop ϕ {x₀}) (hyz : y ≤ z) :
    ∃ s, y s = z s := by
  obtain ⟨s, hs⟩ := omegaLimit_exists_ge_of_incomparable_below ϕ x₀ z h y hy
  exact ⟨s, le_antisymm (hyz s) hs⟩

/-- **A ω-limit point above an incomparable point touches it.** -/
theorem omegaLimit_touch_of_ge_of_incomparable_above
    (ϕ : Flow ℝ≥0 (Concentration S)) (x₀ : Concentration S) (z : Concentration S)
    (h : ¬ ∃ t : ℝ≥0, z ≤ ϕ t x₀)
    (y : Concentration S) (hy : y ∈ omegaLimit atTop ϕ {x₀}) (hyz : z ≤ y) :
    ∃ s, y s = z s := by
  obtain ⟨s, hs⟩ := omegaLimit_exists_le_of_incomparable_above ϕ x₀ z h y hy
  exact ⟨s, le_antisymm hs (hyz s)⟩

/-- **The strong order forces comparability of the orbit.**  If `y` is a ω-limit point which is
*strongly* below `z` (`y ≪ z`), then the forward orbit of `x₀` *is* comparable with `z`: there is a
time `t` with `ϕ t x₀ ≤ z` or with `z ≤ ϕ t x₀`.

This is the contrapositive of `omegaLimit_not_stronglyBelow_of_incomparable_below`, and it is the
form in which the classical non-ordering statement is usually quoted: the strong order cannot
occur in the incomparable-orbit case. -/
theorem comparable_orbit_of_stronglyBelow
    (ϕ : Flow ℝ≥0 (Concentration S)) (x₀ : Concentration S) (z : Concentration S)
    (y : Concentration S) (hy : y ∈ omegaLimit atTop ϕ {x₀}) (hstrong : y ≪ z) :
    (∃ t : ℝ≥0, ϕ t x₀ ≤ z) ∨ (∃ t : ℝ≥0, z ≤ ϕ t x₀) := by
  by_cases hcmp : (∃ t : ℝ≥0, ϕ t x₀ ≤ z) ∨ (∃ t : ℝ≥0, z ≤ ϕ t x₀)
  · exact hcmp
  · exact False.elim ((omegaLimit_not_stronglyBelow_of_incomparable_below ϕ x₀ z
      (fun h => hcmp (Or.inl h)) y hy) hstrong)

/-- **The strong order forces comparability of the orbit (dual).**  If `y` is a ω-limit point which
is *strongly* above `z` (`z ≪ y`), then the forward orbit of `x₀` is comparable with `z`. -/
theorem comparable_orbit_of_stronglyAbove
    (ϕ : Flow ℝ≥0 (Concentration S)) (x₀ : Concentration S) (z : Concentration S)
    (y : Concentration S) (hy : y ∈ omegaLimit atTop ϕ {x₀}) (hstrong : z ≪ y) :
    (∃ t : ℝ≥0, ϕ t x₀ ≤ z) ∨ (∃ t : ℝ≥0, z ≤ ϕ t x₀) := by
  by_cases hcmp : (∃ t : ℝ≥0, ϕ t x₀ ≤ z) ∨ (∃ t : ℝ≥0, z ≤ ϕ t x₀)
  · exact hcmp
  · exact False.elim ((omegaLimit_not_stronglyAbove_of_incomparable_above ϕ x₀ z
      (fun h => hcmp (Or.inr h)) y hy) hstrong)

end OmegaLimitSeparation

section OrderConvexity

variable {S : Type} [Fintype S]

omit [Fintype S] in
/-- **Order-convexity of the ω-limit set: the comparable-orbit case.**

Let `ϕ : Flow ℝ≥0 (Concentration S)` be a monotone forward semiflow, `x₀` a point whose forward
orbit is eventually absorbed by a compact set `K`, and `Ω = omegaLimit atTop ϕ {x₀}`.  Assume

* `hΩE` : every point of `Ω` is an equilibrium of the flow;
* `hEq` : the equilibrium set of the flow is order-convex.

Then a point `z` lying between two ω-limit points (`p ≤ z ≤ q` with `p, q ∈ Ω`) belongs to `Ω`,
**provided the orbit is comparable with `z`** (there is a `t` with `ϕ t x₀ ≤ z` or with
`z ≤ ϕ t x₀`).

This is the sandwich argument of `CRNT.omegaLimit_orderConvex_of_monotone_flow`, but with the
comparability hypothesis required only for the point under test instead of for *every* point. -/
theorem omegaLimit_orderConvex_of_monotone_flow_of_comparable_orbit
    (ϕ : Flow ℝ≥0 (Concentration S))
    (hmono : CRNT.Monotone.IsMonotoneFlow ϕ)
    (x₀ : Concentration S)
    (hΩE : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ≥0, ϕ t y = y)
    (hEq : ∀ p q z : Concentration S,
      (∀ t : ℝ≥0, ϕ t p = p) → (∀ t : ℝ≥0, ϕ t q = q) → p ≤ z → z ≤ q → ∀ t : ℝ≥0, ϕ t z = z)
    (p q z : Concentration S)
    (hp : p ∈ omegaLimit atTop ϕ {x₀}) (hq : q ∈ omegaLimit atTop ϕ {x₀})
    (hpz : p ≤ z) (hzq : z ≤ q)
    (hcmp : (∃ t : ℝ≥0, ϕ t x₀ ≤ z) ∨ (∃ t : ℝ≥0, z ≤ ϕ t x₀)) :
    z ∈ omegaLimit atTop ϕ {x₀} := by
  have hp_eq : ∀ t : ℝ≥0, ϕ t p = p := hΩE p hp
  have hq_eq : ∀ t : ℝ≥0, ϕ t q = q := hΩE q hq
  have hz_eq : ∀ t : ℝ≥0, ϕ t z = z := hEq p q z hp_eq hq_eq hpz hzq
  rcases hcmp with h1 | h2
  · -- the orbit is eventually below `z`: then every ω-limit point is `≤ z`
    obtain ⟨t₀, ht₀⟩ := h1
    have hhalf : Set.image2 ϕ (Set.Ici t₀) {x₀} ⊆ {w | w ≤ z} := by
      intro w hw
      obtain ⟨t, ht, b, hb, heq⟩ := hw
      have hb' : b = x₀ := Set.mem_singleton_iff.mp hb
      obtain ⟨s, hs⟩ := nnReal_exists_eq_add_of_le t₀ t ht
      have hshift : ϕ t x₀ = ϕ s (ϕ t₀ x₀) := by
        have hcomm : s + t₀ = t₀ + s := add_comm _ _
        rw [← Flow.map_add, hcomm, hs]
      have hval : w = ϕ s (ϕ t₀ x₀) := by rw [← heq, hb', hshift]
      rw [hval]
      have hmon' : ϕ s (ϕ t₀ x₀) ≤ ϕ s z := (hmono s) ht₀
      simpa [hz_eq s] using hmon'
    have hle : ∀ y ∈ omegaLimit atTop ϕ {x₀}, y ≤ z := by
      intro y hy
      have hy' : y ∈ closure (Set.image2 ϕ (Set.Ici t₀) {x₀}) :=
        (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) (u := Set.Ici t₀)
          (Ici_mem_atTop t₀)) hy
      have hy'' : y ∈ closure {w | w ≤ z} := closure_mono hhalf hy'
      exact closure_minimal subset_rfl (isClosed_le continuous_id continuous_const) hy''
    have hqz : q ≤ z := hle q hq
    have hqp : q = z := le_antisymm hqz hzq
    rw [← hqp]
    exact hq
  · -- the orbit is eventually above `z`: then every ω-limit point is `≥ z`
    obtain ⟨t₀, ht₀⟩ := h2
    have hhalf : Set.image2 ϕ (Set.Ici t₀) {x₀} ⊆ {w | z ≤ w} := by
      intro w hw
      obtain ⟨t, ht, b, hb, heq⟩ := hw
      have hb' : b = x₀ := Set.mem_singleton_iff.mp hb
      obtain ⟨s, hs⟩ := nnReal_exists_eq_add_of_le t₀ t ht
      have hshift : ϕ t x₀ = ϕ s (ϕ t₀ x₀) := by
        have hcomm : s + t₀ = t₀ + s := add_comm _ _
        rw [← Flow.map_add, hcomm, hs]
      have hval : w = ϕ s (ϕ t₀ x₀) := by rw [← heq, hb', hshift]
      rw [hval]
      have hmon' : ϕ s z ≤ ϕ s (ϕ t₀ x₀) := (hmono s) ht₀
      simpa [hz_eq s] using hmon'
    have hle : ∀ y ∈ omegaLimit atTop ϕ {x₀}, z ≤ y := by
      intro y hy
      have hy' : y ∈ closure (Set.image2 ϕ (Set.Ici t₀) {x₀}) :=
        (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) (u := Set.Ici t₀)
          (Ici_mem_atTop t₀)) hy
      have hy'' : y ∈ closure {w | z ≤ w} := closure_mono hhalf hy'
      exact closure_minimal subset_rfl (isClosed_le continuous_const continuous_id) hy''
    have hzp : z ≤ p := hle p hp
    have hpq : p = z := le_antisymm hpz hzp
    rw [← hpq]
    exact hp

/-- **Order-convexity of the ω-limit set: the strong-order case.**

Same hypotheses as `omegaLimit_orderConvex_of_monotone_flow_of_comparable_orbit`, but **no
comparability hypothesis**: if one of the two inequalities `p ≤ z ≤ q` is a strong one (`p ≪ z` or
`z ≪ q`), then `z ∈ Ω`.

*Proof.*  The strong order forces comparability of the orbit with `z`
(`comparable_orbit_of_stronglyBelow`), and the sandwich argument applies. -/
theorem omegaLimit_orderConvex_of_monotone_flow_of_strongOrder
    (ϕ : Flow ℝ≥0 (Concentration S))
    (hmono : CRNT.Monotone.IsMonotoneFlow ϕ)
    (x₀ : Concentration S)
    (hΩE : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ≥0, ϕ t y = y)
    (hEq : ∀ p q z : Concentration S,
      (∀ t : ℝ≥0, ϕ t p = p) → (∀ t : ℝ≥0, ϕ t q = q) → p ≤ z → z ≤ q → ∀ t : ℝ≥0, ϕ t z = z)
    (p q z : Concentration S)
    (hp : p ∈ omegaLimit atTop ϕ {x₀}) (hq : q ∈ omegaLimit atTop ϕ {x₀})
    (hpz : p ≤ z) (hzq : z ≤ q)
    (hstrong : p ≪ z ∨ z ≪ q) :
    z ∈ omegaLimit atTop ϕ {x₀} := by
  rcases hstrong with hstrong | hstrong
  · have hcmp := comparable_orbit_of_stronglyBelow ϕ x₀ z p hp hstrong
    exact omegaLimit_orderConvex_of_monotone_flow_of_comparable_orbit ϕ hmono x₀ hΩE hEq
      p q z hp hq hpz hzq hcmp
  · have hcmp := comparable_orbit_of_stronglyAbove ϕ x₀ z q hq hstrong
    exact omegaLimit_orderConvex_of_monotone_flow_of_comparable_orbit ϕ hmono x₀ hΩE hEq
      p q z hp hq hpz hzq hcmp

/-- **Order-convexity of the ω-limit set: the general statement.**

Same hypotheses as `omegaLimit_orderConvex_of_monotone_flow_of_comparable_orbit`.  For
`p, q ∈ Ω` with `p ≤ z ≤ q` one has `z ∈ Ω`, **unless** the orbit is incomparable with `z` *and* the
strong order is excluded in both directions — that is, unless the two inequalities `p ≤ z` and
`z ≤ q` are merely "touching" (they agree in one coordinate, by
`omegaLimit_touch_of_le_of_incomparable_below`). -/
theorem omegaLimit_orderConvex_of_monotone_flow_general
    (ϕ : Flow ℝ≥0 (Concentration S))
    (hmono : CRNT.Monotone.IsMonotoneFlow ϕ)
    (x₀ : Concentration S)
    (hΩE : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ≥0, ϕ t y = y)
    (hEq : ∀ p q z : Concentration S,
      (∀ t : ℝ≥0, ϕ t p = p) → (∀ t : ℝ≥0, ϕ t q = q) → p ≤ z → z ≤ q → ∀ t : ℝ≥0, ϕ t z = z)
    (p q z : Concentration S)
    (hp : p ∈ omegaLimit atTop ϕ {x₀}) (hq : q ∈ omegaLimit atTop ϕ {x₀})
    (hpz : p ≤ z) (hzq : z ≤ q) :
    (z ∈ omegaLimit atTop ϕ {x₀}) ∨
      ((¬ ∃ t : ℝ≥0, ϕ t x₀ ≤ z) ∧ (¬ ∃ t : ℝ≥0, z ≤ ϕ t x₀) ∧ ¬ (p ≪ z) ∧ ¬ (z ≪ q)) := by
  by_cases hcmp : (∃ t : ℝ≥0, ϕ t x₀ ≤ z) ∨ (∃ t : ℝ≥0, z ≤ ϕ t x₀)
  · exact Or.inl (omegaLimit_orderConvex_of_monotone_flow_of_comparable_orbit ϕ hmono x₀
      hΩE hEq p q z hp hq hpz hzq hcmp)
  · refine Or.inr ⟨?_, ?_, ?_, ?_⟩
    · intro h
      exact hcmp (Or.inl h)
    · intro h
      exact hcmp (Or.inr h)
    · intro hstrong
      exact (omegaLimit_not_stronglyBelow_of_incomparable_below ϕ x₀ z
        (fun h => hcmp (Or.inl h)) p hp) hstrong
    · intro hstrong
      exact (omegaLimit_not_stronglyAbove_of_incomparable_above ϕ x₀ z
        (fun h => hcmp (Or.inr h)) q hq) hstrong

/-- **The classical sufficient condition: a monotone separating functional.**

Let `ϕ` be a monotone flow, `Ω = omegaLimit atTop ϕ {x₀}`, `p, q ∈ Ω` with `p ≤ z ≤ q`, and let `φ`
be a **monotone separating functional** for `z` (continuous, order-monotone, `φ z = 0`, and
`φ y < 0` forces `y ≪ z`).  If `φ p < φ z < φ q`, then `z ∈ Ω`.

*Proof.*  `φ p < φ z = 0` forces `p ≪ z`; the strong order forces comparability of the orbit with
`z`; the sandwich argument then gives `z = q ∈ Ω` (or `z = p`).  Note that the second inequality
`φ z < φ q` is part of the classical hypothesis but is not needed for the conclusion. -/
theorem omegaLimit_mem_of_separating_functional
    (ϕ : Flow ℝ≥0 (Concentration S))
    (hmono : CRNT.Monotone.IsMonotoneFlow ϕ)
    (x₀ : Concentration S)
    (hΩE : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ≥0, ϕ t y = y)
    (hEq : ∀ p q z : Concentration S,
      (∀ t : ℝ≥0, ϕ t p = p) → (∀ t : ℝ≥0, ϕ t q = q) → p ≤ z → z ≤ q → ∀ t : ℝ≥0, ϕ t z = z)
    (φ : Concentration S → ℝ) (hφ : IsMonotoneSeparator z φ)
    (p q : Concentration S)
    (hp : p ∈ omegaLimit atTop ϕ {x₀}) (hq : q ∈ omegaLimit atTop ϕ {x₀})
    (hpz : p ≤ z) (hzq : z ≤ q)
    (hφpq : φ p < φ z) (hφqz : φ z < φ q) :
    z ∈ omegaLimit atTop ϕ {x₀} := by
  have hφz : φ z = 0 := hφ.2.2.1
  have hφqz' : φ z < φ q := hφqz
  have hφp0 : φ p < 0 := by rw [← hφz]; exact hφpq
  have hstrong : p ≪ z := hφ.2.2.2.2 p hφp0
  have hcmp := comparable_orbit_of_stronglyBelow ϕ x₀ z p hp hstrong
  exact omegaLimit_orderConvex_of_monotone_flow_of_comparable_orbit ϕ hmono x₀ hΩE hEq
    p q z hp hq hpz hzq hcmp

/-- **The classical sufficient condition with an incomparable orbit.**

Same as `omegaLimit_mem_of_separating_functional`, with the additional hypothesis that the orbit is
not comparable with `z`.  The hypotheses are then contradictory — the strong order forced by
`φ p < φ z` is incompatible with an incomparable orbit — and the conclusion follows.  This is the
form in which the classical non-ordering argument is usually recorded. -/
theorem omegaLimit_mem_of_separating_functional_of_incomparable
    (ϕ : Flow ℝ≥0 (Concentration S))
    (hmono : CRNT.Monotone.IsMonotoneFlow ϕ)
    (x₀ : Concentration S)
    (hΩE : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ≥0, ϕ t y = y)
    (hEq : ∀ p q z : Concentration S,
      (∀ t : ℝ≥0, ϕ t p = p) → (∀ t : ℝ≥0, ϕ t q = q) → p ≤ z → z ≤ q → ∀ t : ℝ≥0, ϕ t z = z)
    (φ : Concentration S → ℝ) (hφ : IsMonotoneSeparator z φ)
    (p q : Concentration S)
    (hp : p ∈ omegaLimit atTop ϕ {x₀}) (hq : q ∈ omegaLimit atTop ϕ {x₀})
    (hpz : p ≤ z) (hzq : z ≤ q)
    (hφpq : φ p < φ z) (hφqz : φ z < φ q)
    (hincomp : ¬ ∃ t : ℝ≥0, ϕ t x₀ ≤ z) (hincomp' : ¬ ∃ t : ℝ≥0, z ≤ ϕ t x₀) :
    z ∈ omegaLimit atTop ϕ {x₀} := by
  have hφz : φ z = 0 := hφ.2.2.1
  have hφp0 : φ p < 0 := by rw [← hφz]; exact hφpq
  have hstrong : p ≪ z := hφ.2.2.2.2 p hφp0
  -- the orbit is not comparable with `z`
  have hnot : ¬ ((∃ t : ℝ≥0, ϕ t x₀ ≤ z) ∨ (∃ t : ℝ≥0, z ≤ ϕ t x₀)) :=
    fun h => h.elim hincomp hincomp'
  -- the strong order is incompatible with an incomparable orbit: this is where the
  -- incomparability hypothesis is used
  have hcontra : False :=
    (omegaLimit_not_stronglyBelow_of_incomparable_below ϕ x₀ z (fun h => hnot (Or.inl h)) p hp)
      hstrong
  -- the conclusion follows from the separating functional alone
  exact omegaLimit_mem_of_separating_functional ϕ hmono x₀ hΩE hEq φ hφ p q hp hq hpz hzq
    hφpq hφqz

end OrderConvexity

section MassAction

variable {S : Type} [Fintype S] [DecidableEq S]

/-- **Order-convexity of the ω-limit set of a mass-action network with an order-preserving field:
the general statement.**  This is `CRNT.massAction_omegaLimit_orderConvex_of_monotone_field`
without the comparability hypothesis `hcmp`, the incomparable-orbit case being covered by the
strong-order alternative. -/
theorem massAction_omegaLimit_orderConvex_of_monotone_field_general
    (N : Network S) (κ : N.RateConstants)
    (hmonoF : ∀ x y : Concentration S, x ≤ y →
      N.massActionVectorField κ x ≤ N.massActionVectorField κ y)
    (ϕ : Flow ℝ≥0 (Concentration S)) (hmonFlow : CRNT.Monotone.IsMonotoneFlow ϕ)
    (hEqFlow : ∀ y : Concentration S, (∀ t : ℝ≥0, ϕ t y = y) ↔ N.massActionVectorField κ y = 0)
    (x₀ : Concentration S)
    (hΩE : ∀ y ∈ omegaLimit atTop ϕ {x₀}, N.massActionVectorField κ y = 0)
    (p q z : Concentration S)
    (hp : p ∈ omegaLimit atTop ϕ {x₀}) (hq : q ∈ omegaLimit atTop ϕ {x₀})
    (hpz : p ≤ z) (hzq : z ≤ q) :
    (z ∈ omegaLimit atTop ϕ {x₀}) ∨
      ((¬ ∃ t : ℝ≥0, ϕ t x₀ ≤ z) ∧ (¬ ∃ t : ℝ≥0, z ≤ ϕ t x₀) ∧ ¬ (p ≪ z) ∧ ¬ (z ≪ q)) := by
  -- the zero set of an order-preserving field is order-convex
  have hEz : ∀ a b c : Concentration S,
      (∀ t : ℝ≥0, ϕ t a = a) → (∀ t : ℝ≥0, ϕ t b = b) → a ≤ c → c ≤ b → ∀ t : ℝ≥0, ϕ t c = c := by
    intro a b c ha hb hac hcb
    have ha' : N.massActionVectorField κ a = 0 := (hEqFlow a).mp ha
    have hb' : N.massActionVectorField κ b = 0 := (hEqFlow b).mp hb
    have hmem : c ∈ {x | N.massActionVectorField κ x = 0} :=
      monotone_equilibrium_orderConvex hmonoF {x | N.massActionVectorField κ x = 0}
        (fun x => Iff.rfl) a b c (by simp [ha']) (by simp [hb']) hac hcb
    exact (hEqFlow c).mpr hmem
  -- the ω-limit set consists of equilibria of the flow
  have hΩEflow : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ≥0, ϕ t y = y := by
    intro y hy t
    exact (hEqFlow y).mpr (hΩE y hy) t
  exact omegaLimit_orderConvex_of_monotone_flow_general ϕ hmonFlow x₀ hΩEflow hEz
    p q z hp hq hpz hzq

/-- **Order-convexity of the ω-limit set of a mass-action network with an order-preserving field:
the strong-order case.**  No comparability hypothesis is needed. -/
theorem massAction_omegaLimit_orderConvex_of_monotone_field_of_strongOrder
    (N : Network S) (κ : N.RateConstants)
    (hmonoF : ∀ x y : Concentration S, x ≤ y →
      N.massActionVectorField κ x ≤ N.massActionVectorField κ y)
    (ϕ : Flow ℝ≥0 (Concentration S)) (hmonFlow : CRNT.Monotone.IsMonotoneFlow ϕ)
    (hEqFlow : ∀ y : Concentration S, (∀ t : ℝ≥0, ϕ t y = y) ↔ N.massActionVectorField κ y = 0)
    (x₀ : Concentration S)
    (hΩE : ∀ y ∈ omegaLimit atTop ϕ {x₀}, N.massActionVectorField κ y = 0)
    (p q z : Concentration S)
    (hp : p ∈ omegaLimit atTop ϕ {x₀}) (hq : q ∈ omegaLimit atTop ϕ {x₀})
    (hpz : p ≤ z) (hzq : z ≤ q)
    (hstrong : p ≪ z ∨ z ≪ q) :
    z ∈ omegaLimit atTop ϕ {x₀} := by
  -- the zero set of an order-preserving field is order-convex
  have hEz : ∀ a b c : Concentration S,
      (∀ t : ℝ≥0, ϕ t a = a) → (∀ t : ℝ≥0, ϕ t b = b) → a ≤ c → c ≤ b → ∀ t : ℝ≥0, ϕ t c = c := by
    intro a b c ha hb hac hcb
    have ha' : N.massActionVectorField κ a = 0 := (hEqFlow a).mp ha
    have hb' : N.massActionVectorField κ b = 0 := (hEqFlow b).mp hb
    have hmem : c ∈ {x | N.massActionVectorField κ x = 0} :=
      monotone_equilibrium_orderConvex hmonoF {x | N.massActionVectorField κ x = 0}
        (fun x => Iff.rfl) a b c (by simp [ha']) (by simp [hb']) hac hcb
    exact (hEqFlow c).mpr hmem
  -- the ω-limit set consists of equilibria of the flow
  have hΩEflow : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ≥0, ϕ t y = y := by
    intro y hy t
    exact (hEqFlow y).mpr (hΩE y hy) t
  exact omegaLimit_orderConvex_of_monotone_flow_of_strongOrder ϕ hmonFlow x₀ hΩEflow hEz
    p q z hp hq hpz hzq hstrong

end MassAction

end CRNT
