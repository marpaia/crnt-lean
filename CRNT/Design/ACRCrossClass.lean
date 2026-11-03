import CRNT.Design.ACRUnconditional
import CRNT.Deficiency.LogMonomialRatio
import CRNT.Graph.LinkageClass
import CRNT.Stoich.Subspace
import CRNT.LinearAlgebra.OrthogonalComplement
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The toric cross-class bridge for absolute concentration robustness

The Shinar–Feinberg ACR theorem of `CRNT.Design.ACRUnconditional` is reduced to a single
named cross-class input `ShinarFeinbergHypotheses.CrossClassRatioPinned`: the log-monomial
ratio `Φ` agrees at the two non-terminal complexes, which lie in distinct linkage classes.
This module analyses that input through the *toric* condition, the orthogonality of the
log-ratio vector `μ_s = log x_s − log y_s` to the stoichiometric subspace, characterised by
`logRatio_mem_orthSum_iff`.

* `ToricRelated x y` names that orthogonality predicate, `μ ∈ orthSum S`.
* `logMonomialRatio_const_along_reaction_of_toric` is the per-reaction constancy of `Φ`
  read directly off `logRatio_mem_orthSum_iff`.
* `logMonomialRatio_eqOn_linked` is the keystone: under `ToricRelated`, `Φ` is constant on
  every linkage class — `Φ(c) = Φ(d)` whenever `c` and `d` are linked — obtained by
  reflexive-transitive induction along undirected edges from the per-reaction constancy.
* `crossClassRatio_eq_iff_robust` isolates the residual obligation precisely: for two
  complexes differing only at the species `s`, the cross-class equality `Φ(c) = Φ(d)` holds
  **iff** `x s = y s`. The toric condition forces no cross-class equality on its own; the
  difference `Φ(c) − Φ(d)` collapses to the single coordinate `(c_s − d_s)·μ_s`, so
  cross-class `Φ`-equality is *exactly* robustness of species `s`.
* `HasACR.of_speciesRobust` re-derives unconditional `HasACR s` from a precisely-named
  robustness hypothesis — `x s = y s` for every pair of toric-related positive steady states
  — by feeding the assembled `CrossClassRatioPinned` into `HasACR.of_crossClassRatioGap`.

The genuine Shinar–Feinberg derivation — forcing robustness from non-terminality and the
deficiency-one cut structure — is *not* established here; this module reduces it to the crisp
statement `x s = y s` and proves everything surrounding it.

Depends on: `CRNT.Design.ACRUnconditional`,
`CRNT.Deficiency.LogMonomialRatio`, `CRNT.Graph.LinkageClass`, `CRNT.Stoich.Subspace`,
`CRNT.LinearAlgebra.OrthogonalComplement`, `Mathlib.Analysis.SpecialFunctions.Log.Basic`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The toric/orthogonality relation between two positive concentrations.** The log-ratio
vector `μ_s = log x_s − log y_s` lies in the orthogonal complement of the stoichiometric
subspace. By `logRatio_mem_orthSum_iff` this is exactly constancy of the log-monomial ratio
`Φ` along every reaction. -/
def ToricRelated (N : Network S) (x y : Concentration S) : Prop :=
  (fun s => Real.log (x s) - Real.log (y s)) ∈ orthSum N.stoichSubspace

/-- The log-monomial ratio of a raw complex value `c : Complex S`, agreeing with
`logMonomialRatio` on every complex index via `.val`. Stated on complex values so the
linkage-class induction runs over `Complex S` without carrying membership proofs. -/
noncomputable def logRatioVal (_N : Network S) (x y : Concentration S) (c : Complex S) : ℝ :=
  Real.log (c.massActionMonomial x) - Real.log (c.massActionMonomial y)

theorem logRatioVal_eq_logMonomialRatio (N : Network S) (x y : Concentration S)
    (c : N.ComplexIdx) : N.logRatioVal x y c.val = N.logMonomialRatio x y c :=
  rfl

/-- **Per-reaction constancy from the toric condition.** Under `ToricRelated x y`, the
log-monomial ratio `Φ` agrees at the source and target of every reaction. -/
theorem logMonomialRatio_const_along_reaction_of_toric (N : Network S) {x y : Concentration S}
    (hx : x.Positive) (hy : y.Positive) (h : N.ToricRelated x y) (r : N.R) :
    N.logMonomialRatio x y (N.targetIdx r) = N.logMonomialRatio x y (N.sourceIdx r) :=
  (N.logRatio_mem_orthSum_iff hx hy).mp h r

/-- Per-reaction constancy phrased on raw complex values: `Φ` agrees at the reaction's
source and target as elements of `Complex S`. -/
theorem logRatioVal_const_along_reaction_of_toric (N : Network S) {x y : Concentration S}
    (hx : x.Positive) (hy : y.Positive) (h : N.ToricRelated x y) (r : N.R) :
    N.logRatioVal x y (N.reaction r).target = N.logRatioVal x y (N.reaction r).source :=
  N.logMonomialRatio_const_along_reaction_of_toric hx hy h r

/-- **`Φ` is constant across every undirected edge.** A single undirected step relates two
complex values whose `Φ` agree. -/
theorem logRatioVal_eq_of_undirectedEdge (N : Network S) {x y : Concentration S}
    (hx : x.Positive) (hy : y.Positive) (h : N.ToricRelated x y) {c d : Complex S}
    (hcd : N.UndirectedEdge c d) :
    N.logRatioVal x y c = N.logRatioVal x y d := by
  rcases hcd with ⟨r, hs, ht⟩ | ⟨r, hs, ht⟩
  · rw [← hs, ← ht]; exact (N.logRatioVal_const_along_reaction_of_toric hx hy h r).symm
  · rw [← hs, ← ht]; exact N.logRatioVal_const_along_reaction_of_toric hx hy h r

/-- **Keystone: `Φ` is constant on every linkage class under the toric condition.** For
linked complex values `c` and `d`, the log-monomial ratio agrees. Proved by
reflexive-transitive induction along undirected edges from per-reaction constancy. -/
theorem logRatioVal_eqOn_linked (N : Network S) {x y : Concentration S}
    (hx : x.Positive) (hy : y.Positive) (h : N.ToricRelated x y) {c d : Complex S}
    (hcd : N.Linked c d) :
    N.logRatioVal x y c = N.logRatioVal x y d := by
  induction hcd with
  | refl => rfl
  | tail _ hef ih => exact ih.trans (N.logRatioVal_eq_of_undirectedEdge hx hy h hef)

/-- **Keystone, indexed form.** For two complex indices `c`, `d` whose underlying complexes
are linked, the log-monomial ratio `Φ` agrees, under the toric condition. This is the export
a downstream module consumes for network-wide same-class `Φ`-constancy from one orthogonality
hypothesis. -/
theorem logMonomialRatio_eqOn_linked (N : Network S) {x y : Concentration S}
    (hx : x.Positive) (hy : y.Positive) (h : N.ToricRelated x y) {c d : N.ComplexIdx}
    (hcd : N.Linked c.val d.val) :
    N.logMonomialRatio x y c = N.logMonomialRatio x y d := by
  rw [← N.logRatioVal_eq_logMonomialRatio x y c, ← N.logRatioVal_eq_logMonomialRatio x y d]
  exact N.logRatioVal_eqOn_linked hx hy h hcd

/-- **The cross-class equality reduces to species robustness.** For two complex indices `c`,
`d` agreeing away from a species `s` and differing at `s`, the cross-class `Φ`-equality holds
iff `x s = y s`. The difference `Φ(c) − Φ(d)` collapses to the single coordinate
`(c_s − d_s)·(log x_s − log y_s)`; with `c_s ≠ d_s` this vanishes iff `log x_s = log y_s`,
i.e. `x s = y s` by injectivity of `log` on the positives. -/
theorem crossClassRatio_eq_iff_robust (N : Network S) {x y : Concentration S}
    (hx : x.Positive) (hy : y.Positive) {s : S} {c d : N.ComplexIdx}
    (hdiff : ∀ t, t ≠ s → c.val t = d.val t) (hne : c.val s ≠ d.val s) :
    N.logMonomialRatio x y c = N.logMonomialRatio x y d ↔ x s = y s :=
  -- Deduplicated: the argument now lives at its natural home in
  -- `Deficiency/LogMonomialRatio.lean`, next to `logMonomialRatio_eq`, where the
  -- deficiency-one side of the tree can reach it without importing `Design`.
  N.logMonomialRatio_eq_iff_of_differOnlyAt hx hy hdiff (by exact_mod_cast hne)

/-- **The cross-class `Φ`-equality exponentiates to the pinned monomial ratio.** For the two
non-terminal complexes of the Shinar–Feinberg hypotheses, `Φ(c) = Φ(d)` rearranges and
exponentiates to `c.mono x · d.mono y = c.mono y · d.mono x`, the shape `pin_of_pinned_ratio`
consumes. -/
theorem monomial_cross_of_logMonomialRatio_eq {N : Network S} {s : S}
    (H : N.ShinarFeinbergHypotheses s) {x y : Concentration S}
    (hxpos : x.Positive) (hypos : y.Positive)
    (hΦ : N.logMonomialRatio x y ⟨H.c, H.hc⟩ = N.logMonomialRatio x y ⟨H.d, H.hd⟩) :
    H.c.massActionMonomial x * H.d.massActionMonomial y
      = H.c.massActionMonomial y * H.d.massActionMonomial x := by
  have hxc : (0 : ℝ) < H.c.massActionMonomial x := Complex.massActionMonomial_pos hxpos H.c
  have hyc : (0 : ℝ) < H.c.massActionMonomial y := Complex.massActionMonomial_pos hypos H.c
  have hxd : (0 : ℝ) < H.d.massActionMonomial x := Complex.massActionMonomial_pos hxpos H.d
  have hyd : (0 : ℝ) < H.d.massActionMonomial y := Complex.massActionMonomial_pos hypos H.d
  simp only [logMonomialRatio, complexMonomialVector_apply] at hΦ
  have hlog : Real.log (H.c.massActionMonomial x) + Real.log (H.d.massActionMonomial y)
      = Real.log (H.c.massActionMonomial y) + Real.log (H.d.massActionMonomial x) := by
    linarith [hΦ]
  rw [← Real.log_mul hxc.ne' hyd.ne', ← Real.log_mul hyc.ne' hxd.ne'] at hlog
  have := congrArg Real.exp hlog
  rwa [Real.exp_log (mul_pos hxc hyd), Real.exp_log (mul_pos hyc hxd)] at this

/-- **Unconditional ACR from species robustness.** Given the Shinar–Feinberg hypotheses in
species `s`, a precisely-named robustness hypothesis — every pair of toric-related positive
mass-action steady states agrees at `s`, across any two rate constants — and the toric relation
holding between any two such states, together with a witness positive steady state, the network
has full `HasACR s`. The robustness hypothesis is fed through `crossClassRatio_eq_iff_robust` to
the cross-class `Φ`-equality, exponentiated to the pinned monomial ratio, and propagated by the
pinning lever `pin_of_pinned_ratio`. This is the final bridge: the opaque cross-class input is
replaced by the crisp obligation `x s = y s`. -/
theorem HasACR.of_speciesRobust {N : Network S} {s : S}
    (H : N.ShinarFeinbergHypotheses s)
    (htoric : ∀ (κ₁ κ₂ : RateConstants N) (x y : Concentration S),
      x.Positive → N.IsMassActionSteadyState κ₁ x →
      y.Positive → N.IsMassActionSteadyState κ₂ y →
      N.ToricRelated x y)
    (hrob : ∀ (κ₁ κ₂ : RateConstants N) (x y : Concentration S),
      x.Positive → N.IsMassActionSteadyState κ₁ x →
      y.Positive → N.IsMassActionSteadyState κ₂ y →
      N.ToricRelated x y → x s = y s)
    (hne : ∃ (κ : RateConstants N) (x : Concentration S),
      x.Positive ∧ N.IsMassActionSteadyState κ x) :
    N.HasACR s := by
  -- Assemble the pinned ratio across arbitrary rate constants from robustness.
  have hpin : H.PinnedRatio := by
    intro κ₁ κ₂ x y hxpos hxss hypos hyss
    have htor : N.ToricRelated x y := htoric κ₁ κ₂ x y hxpos hxss hypos hyss
    have hxy : x s = y s := hrob κ₁ κ₂ x y hxpos hxss hypos hyss htor
    have hΦ : N.logMonomialRatio x y ⟨H.c, H.hc⟩ = N.logMonomialRatio x y ⟨H.d, H.hd⟩ :=
      (N.crossClassRatio_eq_iff_robust hxpos hypos
        (c := ⟨H.c, H.hc⟩) (d := ⟨H.d, H.hd⟩) H.differOnlyAt H.differAt).mpr hxy
    exact monomial_cross_of_logMonomialRatio_eq H hxpos hypos hΦ
  exact HasACR.of_pinnedRatio H hpin hne
