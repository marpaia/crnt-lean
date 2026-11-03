import CRNT.Dynamics.LaSalleConvergence
import CRNT.Dynamics.Monotone
import CRNT.Dynamics.LaSalle
import CRNT.Dynamics.CooperativeNetworks
import CRNT.Dynamics.OrthantMonotone
import CRNT.Dynamics.StrongMonotone
import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.Flow
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue

/-!
# Omega-limit topology and conditional order convexity

Compactness, connectedness, and invariance of omega-limit sets, with additional
order-convexity and convergence lemmas under their displayed hypotheses.
The convergence wrappers use the LaSalle/unique-equilibrium argument of
`LaSalleConvergence`, including its increasing-operator condition. They do not
establish the classical generic convergence theorem for strongly monotone flows.
Some order-convexity lemmas take order convexity as an explicit premise.
-/

open Set Filter Topology
open scoped BigOperators NNReal

namespace CRNT

section OmegaLimitStructure

variable {S : Type} [Fintype S]

omit [Fintype S] in
/-- The ω-limit set of a forward trajectory absorbed by `K` is contained in `K`. -/
theorem omegaLimit_subset_absorbing (ϕ : Flow ℝ≥0 (Concentration S)) (x₀ : Concentration S)
    (K : Set (Concentration S))
    (habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K) :
    omegaLimit atTop ϕ {x₀} ⊆ K := by
  obtain ⟨v, hv, hvK⟩ := habs
  exact (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) (u := v) hv).trans hvK

omit [Fintype S] in
/-- **The ω-limit set of a bounded forward trajectory is compact.**  It is closed (Mathlib's
`isClosed_omegaLimit`) and contained in the compact absorbing set `K`. -/
theorem omegaLimit_compact_of_absorbed (ϕ : Flow ℝ≥0 (Concentration S)) (x₀ : Concentration S)
    (K : Set (Concentration S)) (hK : IsCompact K)
    (habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K) :
    IsCompact (omegaLimit atTop ϕ {x₀}) :=
  hK.of_isClosed_subset (isClosed_omegaLimit (f := atTop) (ϕ := ϕ) (s := {x₀}))
    (omegaLimit_subset_absorbing ϕ x₀ K habs)

omit [Fintype S] in
/-- **The ω-limit set of a bounded forward trajectory is connected.**

This is the classical connectedness of ω-limit sets of continuous semiflows: the orbit segment
`{ϕ t x₀ | t ≥ T}` is the continuous image of the connected interval `[T, ∞)`, hence connected,
and its closure is connected; the ω-limit set is the intersection of these nested compact
connected closures, hence connected.

The proof below is the classical separation argument.  Assume `Ω` splits into two disjoint closed
(nonempty) sets `A` and `B`.  Being closed subsets of the compact set `Ω`, they are compact, and
being disjoint they have disjoint open neighbourhoods `U` and `V`.  The ω-limit set is contained in
`U ∪ V`, and compactness of `K` forces a tail of the orbit to be contained in `U ∪ V`; that tail
is connected, so it lies entirely in `U` or entirely in `V`, which contradicts `A ≠ ∅` and
`B ≠ ∅` simultaneously. -/
theorem omegaLimit_connected_of_absorbed (ϕ : Flow ℝ≥0 (Concentration S)) (x₀ : Concentration S)
    (K : Set (Concentration S)) (hK : IsCompact K)
    (habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K) :
    IsConnected (omegaLimit atTop ϕ {x₀}) := by
  have hΩclosed : IsClosed (omegaLimit atTop ϕ {x₀}) :=
    isClosed_omegaLimit (f := atTop) (ϕ := ϕ) (s := {x₀})
  have hΩcompact : IsCompact (omegaLimit atTop ϕ {x₀}) :=
    omegaLimit_compact_of_absorbed ϕ x₀ K hK habs
  -- every tail of the orbit is connected
  have htail : ∀ T : ℝ≥0, IsConnected (closure ((fun t : ℝ≥0 => ϕ t x₀) '' Set.Ici T)) := by
    intro T
    have hcont : ContinuousOn (fun t : ℝ≥0 => ϕ t x₀) (Set.Ici T) :=
      (ϕ.continuous continuous_id continuous_const).continuousOn
    exact (isConnected_Ici.image (fun t : ℝ≥0 => ϕ t x₀) hcont).closure
  have hpre : IsPreconnected (omegaLimit atTop ϕ {x₀}) := by
    rw [isPreconnected_iff_subset_of_fully_disjoint_closed hΩclosed]
    intro u v hu hv hcover hdisj
    by_cases hA : omegaLimit atTop ϕ {x₀} ∩ u = ∅
    · have : omegaLimit atTop ϕ {x₀} ⊆ v := by
        intro x hx
        have hxn : x ∉ u := by
          intro hxu
          have hmem : x ∈ omegaLimit atTop ϕ {x₀} ∩ u := ⟨hx, hxu⟩
          rw [hA] at hmem
          simp at hmem
        by_contra hxv
        exact hxn ((hcover hx).resolve_right hxv)
      exact Or.inr this
    by_cases hB : omegaLimit atTop ϕ {x₀} ∩ v = ∅
    · have : omegaLimit atTop ϕ {x₀} ⊆ u := by
        intro x hx
        have hxn : x ∉ v := by
          intro hxv
          have hmem : x ∈ omegaLimit atTop ϕ {x₀} ∩ v := ⟨hx, hxv⟩
          rw [hB] at hmem
          simp at hmem
        by_contra hxu
        exact hxn ((hcover hx).resolve_left hxu)
      exact Or.inl this
    -- the two closed pieces are compact and disjoint: separate them by open sets
    have hAclosed : IsClosed (omegaLimit atTop ϕ {x₀} ∩ u) := hΩclosed.inter hu
    have hBclosed : IsClosed (omegaLimit atTop ϕ {x₀} ∩ v) := hΩclosed.inter hv
    have hAcompact : IsCompact (omegaLimit atTop ϕ {x₀} ∩ u) :=
      hΩcompact.of_isClosed_subset hAclosed (fun _ hx => hx.1)
    have hBcompact : IsCompact (omegaLimit atTop ϕ {x₀} ∩ v) :=
      hΩcompact.of_isClosed_subset hBclosed (fun _ hx => hx.1)
    have hABdisj : Disjoint (omegaLimit atTop ϕ {x₀} ∩ u) (omegaLimit atTop ϕ {x₀} ∩ v) := by
      refine Set.disjoint_left.2 fun x hx hx' => ?_
      exact (Set.disjoint_left.1 hdisj hx.2) hx'.2
    obtain ⟨U, V, hUopen, hVopen, hAU, hBV, hUV⟩ :=
      SeparatedNhds.of_isCompact_isCompact hAcompact hBcompact hABdisj
    have hcoverUV : omegaLimit atTop ϕ {x₀} ⊆ U ∪ V := by
      intro x hx
      by_cases hxu : x ∈ u
      · exact Or.inl (hAU ⟨hx, hxu⟩)
      · have hxv : x ∈ v := by
          by_contra hxv'
          exact (hcover hx).elim hxu hxv'
        exact Or.inr (hBV ⟨hx, hxv⟩)
    -- a tail of the orbit is eventually contained in `U ∪ V`
    obtain ⟨w, hw, hwUV⟩ :=
      eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset'
        atTop ϕ {x₀} hK habs (n := U ∪ V) (IsOpen.union hUopen hVopen) hcoverUV
    obtain ⟨T, hTw⟩ := Filter.mem_atTop_sets.1 hw
    -- the closure of the tail `T` is connected and contained in `U ∪ V`
    have hC : IsConnected (closure ((fun t : ℝ≥0 => ϕ t x₀) '' Set.Ici T)) := htail T
    have himg : (fun t : ℝ≥0 => ϕ t x₀) '' Set.Ici T = Set.image2 ϕ (Set.Ici T) {x₀} :=
      Set.image2_singleton_right.symm
    have hCsub : closure ((fun t : ℝ≥0 => ϕ t x₀) '' Set.Ici T) ⊆ U ∪ V := by
      have hsub : Set.image2 ϕ (Set.Ici T) {x₀} ⊆ Set.image2 ϕ w {x₀} := by
        intro y hy
        obtain ⟨a, ha, b, hb, h⟩ := hy
        exact ⟨a, hTw a ha, b, hb, h⟩
      rw [himg]
      exact closure_mono hsub |>.trans hwUV
    rcases hC.isPreconnected.subset_or_subset hUopen hVopen hUV hCsub with hCU | hCV
    · have hΩU : omegaLimit atTop ϕ {x₀} ⊆ U := by
        intro x hx
        have hx'' : x ∈ closure (Set.image2 ϕ (Set.Ici T) {x₀}) :=
          (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) (u := Set.Ici T)
            (Ici_mem_atTop T)) hx
        have hx' : x ∈ closure ((fun t : ℝ≥0 => ϕ t x₀) '' Set.Ici T) := by rwa [← himg] at hx''
        exact hCU hx'
      have hBne : (omegaLimit atTop ϕ {x₀} ∩ v).Nonempty := by
        by_contra hne
        exact hB (Set.not_nonempty_iff_eq_empty.mp hne)
      obtain ⟨y, hy⟩ := hBne
      exact absurd (hBV hy) (Set.disjoint_left.1 hUV (hΩU hy.1))
    · have hΩV : omegaLimit atTop ϕ {x₀} ⊆ V := by
        intro x hx
        have hx'' : x ∈ closure (Set.image2 ϕ (Set.Ici T) {x₀}) :=
          (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) (u := Set.Ici T)
            (Ici_mem_atTop T)) hx
        have hx' : x ∈ closure ((fun t : ℝ≥0 => ϕ t x₀) '' Set.Ici T) := by rwa [← himg] at hx''
        exact hCV hx'
      have hAne : (omegaLimit atTop ϕ {x₀} ∩ u).Nonempty := by
        by_contra hne
        exact hA (Set.not_nonempty_iff_eq_empty.mp hne)
      obtain ⟨y, hy⟩ := hAne
      exact absurd (hAU hy) (Set.disjoint_left.1 hUV.symm (hΩV hy.1))
  refine ⟨?_, hpre⟩
  exact nonempty_omegaLimit_of_isCompact_absorbing atTop ϕ {x₀} hK habs (Set.singleton_nonempty x₀)

omit [Fintype S] in
/-- **The ω-limit set of a bounded forward trajectory is forward invariant.**  This is
Mathlib's `isInvariant_omegaLimit`, phrased for forward semiflows. -/
theorem omegaLimit_forwardInvariant_of_absorbed (ϕ : Flow ℝ≥0 (Concentration S))
    (x₀ : Concentration S) :
    IsForwardInvariant ϕ (omegaLimit atTop ϕ {x₀}) :=
  (Flow.isInvariant_omegaLimit atTop ϕ {x₀}
    (fun _t => tendsto_atTop_mono (fun _ => le_add_self) tendsto_id)).isForwardInvariant

end OmegaLimitStructure

section OrderConvexity

variable {S : Type} [Fintype S]

/-- **Decomposition of a tail of `ℝ≥0` as a translate.**  If `t₀ ≤ t` then `t = t₀ + s` for some
`s ≥ 0`.  This is the elementary arithmetic fact needed to compare the orbit of a monotone flow
with an equilibrium at a later time. -/
theorem nnReal_exists_eq_add_of_le (t₀ t : ℝ≥0) (h : t₀ ≤ t) : ∃ s : ℝ≥0, t = t₀ + s := by
  have h' : (t₀ : ℝ) ≤ (t : ℝ) := by exact_mod_cast h
  have hsub : 0 ≤ (t : ℝ) - (t₀ : ℝ) := sub_nonneg.mpr h'
  refine ⟨Real.toNNReal ((t : ℝ) - (t₀ : ℝ)), ?_⟩
  apply NNReal.coe_injective
  rw [NNReal.coe_add]
  have hc : (Real.toNNReal ((t : ℝ) - (t₀ : ℝ)) : ℝ) = (t : ℝ) - (t₀ : ℝ) := Real.coe_toNNReal _ hsub
  rw [hc]
  linarith

omit [Fintype S] in
/-- **Order-convexity of the equilibrium set of a monotone field.**  If `f` is order-preserving and
`p`, `q` are equilibria with `p ≤ z ≤ q`, then `z` is an equilibrium as well: monotonicity gives
`0 = f p ≤ f z ≤ f q = 0`.

This is the hypothesis-free version of `CRNT.stronglyMonotoneOperator_equilibrium_orderConvex`, whose proof
only ever used the monotonicity of the field. -/
theorem monotone_equilibrium_orderConvex {f : Concentration S → Concentration S}
    (hmono : ∀ x y : Concentration S, x ≤ y → f x ≤ f y) (E : Set (Concentration S))
    (hE : ∀ x : Concentration S, x ∈ E ↔ f x = 0) :
    ∀ x y z : Concentration S, x ∈ E → y ∈ E → x ≤ z → z ≤ y → z ∈ E := by
  intro x y z hx hy hxz hzy
  have hfx : f x = 0 := (hE x).mp hx
  have hfy : f y = 0 := (hE y).mp hy
  have h1 : f x ≤ f z := hmono x z hxz
  have h2 : f z ≤ f y := hmono z y hzy
  rw [hfx] at h1
  rw [hfy] at h2
  have hz : ∀ s, f z s = 0 := by
    intro s
    have a : 0 ≤ f z s := h1 s
    have b : f z s ≤ 0 := h2 s
    linarith
  exact (hE z).mpr (funext fun s => hz s)

omit [Fintype S] in
/-- **Order-convexity of the ω-limit set of a bounded trajectory of a monotone flow.**

Let `ϕ : Flow ℝ≥0 (Concentration S)` be a monotone forward semiflow (each time-`t` map is
order-preserving), let `x₀` be a point whose forward orbit is eventually absorbed by a compact set
`K`, and let `Ω = omegaLimit atTop ϕ {x₀}`.  Assume

* `hΩE` : every point of `Ω` is an equilibrium of the flow;
* `hEq` : the equilibrium set of the flow is order-convex;
* `hcmp` : the forward orbit of `x₀` is order-comparable with the point under test.

Then `Ω` is order-convex: whenever `p, q ∈ Ω` and `p ≤ z ≤ q`, one has `z ∈ Ω`.

*Proof.*  Suppose `ϕ t₀ x₀ ≤ z`.  Since `z` is an equilibrium and the flow is monotone, the
inequality propagates: `ϕ t x₀ ≤ z` for all `t ≥ t₀`.  Every ω-limit point is in the closure of
every tail, hence in the closure of the `≤ z` half-space, which is closed; so every ω-limit point
is `≤ z`.  In particular `q ≤ z`, and together with `z ≤ q` this gives `q = z ∈ Ω`.  The case
`z ≤ ϕ t₀ x₀` is symmetric and gives `p = z ∈ Ω`. -/
theorem omegaLimit_orderConvex_of_monotone_flow
    (ϕ : Flow ℝ≥0 (Concentration S))
    (hmono : CRNT.Monotone.IsMonotoneFlow ϕ)
    (x₀ : Concentration S) (K : Set (Concentration S)) (hK : IsCompact K)
    (habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K)
    (hΩE : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ≥0, ϕ t y = y)
    (hEq : ∀ p q z : Concentration S,
      (∀ t : ℝ≥0, ϕ t p = p) → (∀ t : ℝ≥0, ϕ t q = q) → p ≤ z → z ≤ q → ∀ t : ℝ≥0, ϕ t z = z)
    (hcmp : ∀ z : Concentration S, (∃ t : ℝ≥0, ϕ t x₀ ≤ z) ∨ (∃ t : ℝ≥0, z ≤ ϕ t x₀)) :
    ∀ p q z : Concentration S,
      p ∈ omegaLimit atTop ϕ {x₀} → q ∈ omegaLimit atTop ϕ {x₀} →
      p ≤ z → z ≤ q → z ∈ omegaLimit atTop ϕ {x₀} := by
  -- the absorbing compact set makes the ω-limit set compact and connected
  have hΩcompact : IsCompact (omegaLimit atTop ϕ {x₀}) :=
    omegaLimit_compact_of_absorbed ϕ x₀ K hK habs
  have hΩconnected : IsConnected (omegaLimit atTop ϕ {x₀}) :=
    omegaLimit_connected_of_absorbed ϕ x₀ K hK habs
  intro p q z hp hq hpz hzq
  have hp_eq : ∀ t : ℝ≥0, ϕ t p = p := hΩE p hp
  have hq_eq : ∀ t : ℝ≥0, ϕ t q = q := hΩE q hq
  have hz_eq : ∀ t : ℝ≥0, ϕ t z = z := hEq p q z hp_eq hq_eq hpz hzq
  rcases hcmp z with h1 | h2
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
      have : y ∈ {w | w ≤ z} :=
        closure_minimal (s := {w | w ≤ z}) (t := {w | w ≤ z}) subset_rfl
          (isClosed_le continuous_id continuous_const) hy''
      exact this
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
      have : y ∈ {w | z ≤ w} :=
        closure_minimal (s := {w | z ≤ w}) (t := {w | z ≤ w}) subset_rfl
          (isClosed_le continuous_const continuous_id) hy''
      exact this
    have hzp : z ≤ p := hle p hp
    have hpq : p = z := le_antisymm hpz hzp
    rw [← hpq]
    exact hp

/-- **Order-convexity of the ω-limit set of a bounded trajectory of a strongly monotone field.**

If the field `f` is strongly monotone (in the sense of `CRNT.OrderPreservingStronglyMonotoneOperator`) and the ω-limit set
of the trajectory consists of equilibria, then the ω-limit set is a *single* point — two distinct
equilibria contradict strong monotonicity — and a singleton is trivially order-convex.  No
comparability hypothesis on the orbit is needed here. -/
theorem omegaLimit_orderConvex_of_stronglyMonotoneOperator
    [DecidableEq S]
    (f : Concentration S → Concentration S) (ϕ : Flow ℝ≥0 (Concentration S))
    (hc : ℝ) (hsm : OrderPreservingStronglyMonotoneOperator f hc) (hcpos : 0 < hc)
    (x₀ : Concentration S) (K : Set (Concentration S)) (hK : IsCompact K)
    (habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K)
    (hΩE : ∀ y ∈ omegaLimit atTop ϕ {x₀}, f y = 0) :
    ∀ p q z : Concentration S,
      p ∈ omegaLimit atTop ϕ {x₀} → q ∈ omegaLimit atTop ϕ {x₀} →
      p ≤ z → z ≤ q → z ∈ omegaLimit atTop ϕ {x₀} := by
  -- the absorbing compact set makes the ω-limit set compact and connected
  have hΩcompact : IsCompact (omegaLimit atTop ϕ {x₀}) :=
    omegaLimit_compact_of_absorbed ϕ x₀ K hK habs
  have hΩconnected : IsConnected (omegaLimit atTop ϕ {x₀}) :=
    omegaLimit_connected_of_absorbed ϕ x₀ K hK habs
  intro p q z hp hq hpz hzq
  have hp0 : f p = 0 := hΩE p hp
  have hq0 : f q = 0 := hΩE q hq
  have hpq : p = q :=
    stronglyMonotoneOperator_unique_equilibrium (f := f) (c := hc) (a := p) (b := q) hcpos hsm hp0 hq0
  subst hpq
  have : z = p := le_antisymm hzq hpz
  rwa [this]

end OrderConvexity

section LaSalleWrappers

variable {S : Type} [Fintype S] [DecidableEq S]

/-- **LaSalle convergence with a unique equilibrium with the order-convexity of the ω-limit set *derived*.**

This is `CRNT.converges_of_lasalle_of_stronglyMonotoneOperator` with its `hωoc` hypothesis replaced by the order-convexity
`omegaLimit_orderConvex_of_monotone_flow`, which is *proved* from the hypotheses `hΩE` (the
ω-limit set consists of equilibria), `hEq` (the equilibrium set of the flow is order-convex) and
`hcmp` (the orbit is order-comparable with the test point). -/
theorem converges_of_lasalle_of_stronglyMonotoneOperator_with_orderConvex
    (ϕ : Flow ℝ≥0 (Concentration S)) (f : Concentration S → Concentration S)
    (V : Concentration S → ℝ) (hV : Continuous V) (x₀ : Concentration S)
    (K : Set (Concentration S)) (hK : IsCompact K)
    (habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K)
    (hmonoV : ∀ s t : ℝ≥0, s ≤ t → V (ϕ t x₀) ≤ V (ϕ s x₀))
    (hVcrit : ∀ y ∈ K, (∀ t : ℝ≥0, V (ϕ t y) = V y) → f y = 0)
    (hc : ℝ) (hsm : OrderPreservingStronglyMonotoneOperator f hc) (hcpos : 0 < hc)
    (hmonFlow : CRNT.Monotone.IsMonotoneFlow ϕ)
    -- the order-convexity of the ω-limit set is *derived* from the next three hypotheses
    (hΩE : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ≥0, ϕ t y = y)
    (hEq : ∀ p q z : Concentration S,
      (∀ t : ℝ≥0, ϕ t p = p) → (∀ t : ℝ≥0, ϕ t q = q) → p ≤ z → z ≤ q → ∀ t : ℝ≥0, ϕ t z = z)
    (hcmp : ∀ z : Concentration S, (∃ t : ℝ≥0, ϕ t x₀ ≤ z) ∨ (∃ t : ℝ≥0, z ≤ ϕ t x₀)) :
    ∃ xstar : Concentration S, f xstar = 0 ∧
      Tendsto (fun t : ℝ≥0 => ϕ t x₀) atTop (𝓝 xstar) := by
  have hωoc : ∀ a b z : Concentration S,
      a ∈ omegaLimit atTop ϕ {x₀} → b ∈ omegaLimit atTop ϕ {x₀} →
      a ≤ z → z ≤ b → z ∈ omegaLimit atTop ϕ {x₀} :=
    omegaLimit_orderConvex_of_monotone_flow ϕ hmonFlow x₀ K hK habs hΩE hEq hcmp
  exact converges_of_lasalle_of_stronglyMonotoneOperator ϕ f V hV x₀ K hK habs hmonoV hVcrit hc hsm hcpos hωoc hmonFlow

/-- **LaSalle convergence with a unique equilibrium without any order-convexity hypothesis.**

This is `CRNT.converges_of_lasalle_of_stronglyMonotoneOperator` with the hypothesis `hωoc` (the order-convexity of the
ω-limit set) *removed*.  It is legitimate to remove it: the hypothesis was not used in the proof of
`CRNT.converges_of_lasalle_of_stronglyMonotoneOperator`, because the order-convexity of the ω-limit set is a
consequence of the LaSalle hypotheses (`hmonoV`, `hVcrit`), which make the ω-limit set a set of
equilibria, together with strong monotonicity, which makes it a *singleton* — and a singleton is
order-convex.  This is the classical content of LaSalle convergence with a unique equilibrium theorem for
strongly monotone systems. -/
theorem converges_of_lasalle_of_stronglyMonotoneOperator_of_monotone
    (ϕ : Flow ℝ≥0 (Concentration S)) (f : Concentration S → Concentration S)
    (V : Concentration S → ℝ) (hV : Continuous V) (x₀ : Concentration S)
    (K : Set (Concentration S)) (hK : IsCompact K)
    (habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K)
    (hmonoV : ∀ s t : ℝ≥0, s ≤ t → V (ϕ t x₀) ≤ V (ϕ s x₀))
    (hVcrit : ∀ y ∈ K, (∀ t : ℝ≥0, V (ϕ t y) = V y) → f y = 0)
    (hc : ℝ) (hsm : OrderPreservingStronglyMonotoneOperator f hc) (hcpos : 0 < hc)
    (hmonFlow : CRNT.Monotone.IsMonotoneFlow ϕ) :
    ∃ xstar : Concentration S, f xstar = 0 ∧
      Tendsto (fun t : ℝ≥0 => ϕ t x₀) atTop (𝓝 xstar) := by
  -- LaSalle: the ω-limit set consists of equilibria of the field
  have hΩEf : ∀ y ∈ omegaLimit atTop ϕ {x₀}, f y = 0 :=
    omegaLimit_subset_equilibria ϕ f V hV x₀ K hK habs hmonoV hVcrit
  -- strong monotonicity: the ω-limit set is a singleton, hence order-convex
  have hωoc : ∀ a b z : Concentration S,
      a ∈ omegaLimit atTop ϕ {x₀} → b ∈ omegaLimit atTop ϕ {x₀} →
      a ≤ z → z ≤ b → z ∈ omegaLimit atTop ϕ {x₀} :=
    omegaLimit_orderConvex_of_stronglyMonotoneOperator f ϕ hc hsm hcpos x₀ K hK habs hΩEf
  exact converges_of_lasalle_of_stronglyMonotoneOperator ϕ f V hV x₀ K hK habs hmonoV hVcrit hc hsm hcpos hωoc hmonFlow

end LaSalleWrappers

section MassAction

variable {S : Type} [Fintype S] [DecidableEq S]

/-- **LaSalle convergence with a unique equilibrium for a cooperative mass-action network, without the
order-convexity hypothesis.**  This is `CRNT.massAction_converges_of_lasalle_of_stronglyMonotoneOperator` with `hωoc` removed;
see `converges_of_lasalle_of_stronglyMonotoneOperator_of_monotone`. -/
theorem massAction_converges_of_lasalle_of_stronglyMonotoneOperator_of_cooperative (N : Network S) (κ : N.RateConstants)
    {c : ℝ} (hc : 0 < c) (hsm : OrderPreservingStronglyMonotoneOperator (N.massActionVectorField κ) c)
    (ϕ : Flow ℝ≥0 (Concentration S)) (f : Concentration S → Concentration S)
    (V : Concentration S → ℝ) (hV : Continuous V) (x₀ : Concentration S)
    (K : Set (Concentration S)) (hK : IsCompact K)
    (habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K)
    (hmonoV : ∀ s t : ℝ≥0, s ≤ t → V (ϕ t x₀) ≤ V (ϕ s x₀))
    (hVcrit : ∀ y ∈ K, (∀ t : ℝ≥0, V (ϕ t y) = V y) → f y = 0)
    (hmonFlow : CRNT.Monotone.IsMonotoneFlow ϕ)
    (hf : f = N.massActionVectorField κ) :
    ∃ xstar : Concentration S, N.massActionVectorField κ xstar = 0 ∧
      Tendsto (fun t : ℝ≥0 => ϕ t x₀) atTop (𝓝 xstar) := by
  have hsm' : OrderPreservingStronglyMonotoneOperator f c := by rw [hf]; exact hsm
  obtain ⟨xstar, hxstar0, htend⟩ :=
    converges_of_lasalle_of_stronglyMonotoneOperator_of_monotone ϕ f V hV x₀ K hK habs hmonoV hVcrit c hsm' hc hmonFlow
  refine ⟨xstar, ?_, htend⟩
  rw [hf] at hxstar0
  exact hxstar0

/-- **The ω-limit set of a bounded trajectory of a cooperative mass-action network with a strongly
monotone field is order-convex.**  No order-convexity hypothesis is needed: the ω-limit set is a
single point (`omegaLimit_orderConvex_of_stronglyMonotoneOperator`). -/
theorem massAction_omegaLimit_orderConvex_of_cooperative (N : Network S) (κ : N.RateConstants)
    {c : ℝ} (hc : 0 < c) (hsm : OrderPreservingStronglyMonotoneOperator (N.massActionVectorField κ) c)
    (ϕ : Flow ℝ≥0 (Concentration S)) (x₀ : Concentration S) (K : Set (Concentration S))
    (hK : IsCompact K)
    (habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K)
    (hΩE : ∀ y ∈ omegaLimit atTop ϕ {x₀}, N.massActionVectorField κ y = 0) :
    ∀ a b z : Concentration S,
      a ∈ omegaLimit atTop ϕ {x₀} → b ∈ omegaLimit atTop ϕ {x₀} →
      a ≤ z → z ≤ b → z ∈ omegaLimit atTop ϕ {x₀} :=
  omegaLimit_orderConvex_of_stronglyMonotoneOperator (N.massActionVectorField κ) ϕ c hsm hc x₀ K hK habs hΩE

/-- **The ω-limit set of a bounded trajectory of a mass-action network whose field is monotone is
order-convex.**

Here the field `N.massActionVectorField κ` is assumed to be *order-preserving* (which is stronger
than the Kamke condition of `CRNT.Network.massAction_kamkeOn_of_cooperative`), the flow `ϕ` is
assumed to be the flow of that field (`hEqFlow`), and the orbit is assumed to be order-comparable
with the test point (`hcmp`).  The order-convexity of the equilibrium set of the flow is then
*derived* from the order-convexity of the zero set of a monotone field
(`monotone_equilibrium_orderConvex`). -/
theorem massAction_omegaLimit_orderConvex_of_monotone_field (N : Network S) (κ : N.RateConstants)
    (hmonoF : ∀ x y : Concentration S, x ≤ y →
      N.massActionVectorField κ x ≤ N.massActionVectorField κ y)
    (ϕ : Flow ℝ≥0 (Concentration S)) (hmonFlow : CRNT.Monotone.IsMonotoneFlow ϕ)
    (hEqFlow : ∀ y : Concentration S, (∀ t : ℝ≥0, ϕ t y = y) ↔ N.massActionVectorField κ y = 0)
    (x₀ : Concentration S) (K : Set (Concentration S)) (hK : IsCompact K)
    (habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K)
    (hΩE : ∀ y ∈ omegaLimit atTop ϕ {x₀}, N.massActionVectorField κ y = 0)
    (hcmp : ∀ z : Concentration S, (∃ t : ℝ≥0, ϕ t x₀ ≤ z) ∨ (∃ t : ℝ≥0, z ≤ ϕ t x₀)) :
    ∀ a b z : Concentration S,
      a ∈ omegaLimit atTop ϕ {x₀} → b ∈ omegaLimit atTop ϕ {x₀} →
      a ≤ z → z ≤ b → z ∈ omegaLimit atTop ϕ {x₀} := by
  -- the zero set of a monotone field is order-convex
  have hEz : ∀ p q r : Concentration S,
      (∀ t : ℝ≥0, ϕ t p = p) → (∀ t : ℝ≥0, ϕ t q = q) → p ≤ r → r ≤ q → ∀ t : ℝ≥0, ϕ t r = r := by
    intro p q r hp hq hpr hrq
    have hpr' : N.massActionVectorField κ p = 0 := (hEqFlow p).mp hp
    have hqr' : N.massActionVectorField κ q = 0 := (hEqFlow q).mp hq
    have hmem : r ∈ {x | N.massActionVectorField κ x = 0} :=
      monotone_equilibrium_orderConvex hmonoF {x | N.massActionVectorField κ x = 0}
        (fun x => Iff.rfl) p q r (by simp [hpr']) (by simp [hqr']) hpr hrq
    exact (hEqFlow r).mpr hmem
  -- the ω-limit set consists of equilibria of the flow
  have hΩEflow : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ≥0, ϕ t y = y := by
    intro y hy t
    exact (hEqFlow y).mpr (hΩE y hy) t
  exact omegaLimit_orderConvex_of_monotone_flow ϕ hmonFlow x₀ K hK habs hΩEflow hEz hcmp

end MassAction

end CRNT
