import CRNT.Dynamics.EscapeSiphonFace
import CRNT.Dynamics.GACOmegaPositive

/-!
# Siphon-dimension descent to an interior ω-limit point

This module is the scaffold of Anderson's siphon-dimension descent (David F. Anderson, "A proof of
the global attractor conjecture in the single linkage class case"). For a precompact positive
mass-action trajectory the boundary ω-limit points are pinned to critical-siphon faces
(`CriticalSiphonOmega`, `EscapeSiphonFace`); the descent organises those faces by the *cardinality*
of the underlying critical siphon and walks downward until the siphon is gone, at which point the
ω-limit set meets the open positive orthant and `omegaLimit_eq_singleton_of_mem_positive` collapses
it to `{x*}`.

## Carrier of a siphon

`Network.SiphonCarried ϕ x₀ P` records that the species set `P` is the zero set of *some* ω-limit
point of the trajectory through `x₀`. A boundary ω-point supplies such a carrier directly, and the
escape geometry of `exists_escape_forwardLimit_criticalSiphonFace` produces carriers inside the
forward limit of any escaping ω-point (those forward limits are subsets of the ω-limit set). A
nonempty carried set is a critical siphon (`isCriticalSiphon_zeroSet_of_mem_omegaLimit`).

## The descent

The single genuinely analytic ingredient — Anderson's comparable-growth Lyapunov-family estimate,
which forbids the trajectory from cycling among boundary faces and forces each boundary excursion to
strip away at least one species — is isolated as the predicate `Network.ComparableGrowthDescent`. It
asserts exactly one thing: every nonempty carried critical siphon `P` either coexists with a
strictly positive ω-limit point or yields another carried critical siphon `Q` with `Q.card < P.card`.
Nothing about the underlying real-analysis estimate is assumed beyond this strict-decrease step; its
proof needs near-facet influx and Lyapunov-comparison infrastructure that is not developed here.

Given that predicate the descent is finite: a critical siphon is nonempty, so its cardinality is at
least one, and a strictly decreasing chain of cardinalities cannot continue forever. Strong induction
on the cardinality (`omegaLimit_positive_of_comparableGrowthDescent`) therefore terminates in the
strictly positive ω-limit point, which `omegaLimit_eq_singleton_of_mem_positive` turns into the
global attractor conclusion `ω = {x*}` (`omegaLimit_eq_singleton_of_comparableGrowthDescent`).

The Butler–McGehee escape that manufactures the smaller-face carrier in the analytic proof is exposed
separately as `siphonCarried_of_escape`: an ω-limit set not contained in an isolated invariant set
yields an escaping ω-point whose forward limit carries a critical siphon, hence a `SiphonCarried`
witness.

The comparable-growth descent is the sole carried hypothesis.
Depends on: `CRNT.Dynamics.EscapeSiphonFace`, `CRNT.Dynamics.GACOmegaPositive`.
-/

open Filter Topology
open scoped BigOperators NNReal Topology

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **A species set carried as the zero set of an ω-limit point.** `P` is *carried* by the
trajectory through `x₀` when some ω-limit point `w ∈ ω{x₀}` vanishes exactly on `P`. Boundary
ω-points and the forward limits of escaping ω-points both furnish carriers; a nonempty carrier is a
critical siphon. -/
def SiphonCarried (_N : Network S) (ϕ : Flow ℝ≥0 (Concentration S)) (x₀ : Concentration S)
    (P : Finset S) : Prop :=
  ∃ w ∈ omegaLimit atTop ϕ {x₀}, ∀ s, s ∈ P ↔ w s = 0

/-- A nonempty carried species set is a critical siphon. This is
`isCriticalSiphon_zeroSet_of_mem_omegaLimit` read through the carrier: the witness `w` is an ω-limit
point whose zero set is exactly `P`. -/
theorem isCriticalSiphon_of_siphonCarried (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S} (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, (y : Concentration S).Nonnegative)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx0pos : x₀.Positive) {P : Finset S} (hPne : P.Nonempty) (hP : N.SiphonCarried ϕ x₀ P) :
    N.IsCriticalSiphon P := by
  obtain ⟨w, hw, hwP⟩ := hP
  exact N.isCriticalSiphon_zeroSet_of_mem_omegaLimit κ hϕγ hK hmaps hωnn hgenω hωaff hx0pos hw
    hwP hPne

/-- **Butler–McGehee escape supplies a carried critical siphon.** If the ω-limit set is not contained
in the isolated invariant set `M` (the maximal invariant subset of its isolating neighborhood
`Nbhd`), `exists_escape_forwardLimit_criticalSiphonFace` produces an escaping ω-point `q` whose
forward limit `ω{q}` is a subset of `ω{x₀}` on which every nonempty zero set is a critical siphon. If
that forward limit holds a boundary point `w` — a coordinate `w s₁ = 0` — its zero set is a nonempty
critical siphon carried by the trajectory through `x₀`. This is the step that, in Anderson's proof,
manufactures the smaller-face carrier the descent consumes. -/
theorem siphonCarried_of_escape (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S} (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hKcl : IsClosed K)
    (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, (y : Concentration S).Nonnegative)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx0pos : x₀.Positive) {M Nbhd : Set (Concentration S)}
    (hMisol : maximalInvariantSubset ϕ Nbhd = M) (hMN : M ⊆ Nbhd)
    (hΩM : ¬ omegaLimit atTop ϕ {x₀} ⊆ M)
    -- a boundary point of the escaping forward limit, located by its escaping ω-point
    (hbdry : ∀ q ∈ omegaLimit atTop ϕ {x₀}, q ∉ M →
      ∃ w ∈ omegaLimit atTop ϕ {q}, ∃ s, w s = 0) :
    ∃ P : Finset S, P.Nonempty ∧ N.IsCriticalSiphon P ∧ N.SiphonCarried ϕ x₀ P := by
  classical
  obtain ⟨q, hq, hqM, _hne, _hcpt, _hinv, hsubq, hface⟩ :=
    N.exists_escape_forwardLimit_criticalSiphonFace κ hϕγ hK hKcl hmaps hωnn hgenω hωaff hx0pos
      hMisol hMN hΩM
  obtain ⟨w, hwq, s₁, hs₁⟩ := hbdry q hq hqM
  set P : Finset S := Finset.univ.filter (fun s => w s = 0) with hPdef
  have hwP : ∀ s, s ∈ P ↔ w s = 0 := fun s => by
    rw [hPdef, Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ s, h⟩⟩
  have hPne : P.Nonempty := ⟨s₁, (hwP s₁).mpr hs₁⟩
  exact ⟨P, hPne, hface w hwq P hwP hPne, w, hsubq hwq, hwP⟩

/-- **Anderson's comparable-growth descent (carried analytic step).** The sole hypothesis isolating
the genuinely-hard analytic content. It asserts that the trajectory cannot cycle among boundary
faces: every nonempty *carried critical siphon* `P` either coexists with a strictly positive ω-limit
point, or produces a *strictly smaller* carried critical siphon `Q` (with `Q.card < P.card`). In the
analytic proof the strict shrinking is forced by comparing the growth of the relative-entropy
Lyapunov family across an escape from the face `SiphonFace P`; that estimate is the content not
formalised here. The descent walks the strictly decreasing cardinalities down to the empty siphon,
i.e. to the strictly positive ω-limit point. -/
structure ComparableGrowthDescent (N : Network S) (ϕ : Flow ℝ≥0 (Concentration S))
    (x₀ : Concentration S) : Prop where
  /-- Every nonempty carried critical siphon `P` either coexists with a positive ω-limit point or
  yields a carried critical siphon of strictly smaller cardinality. -/
  descend : ∀ P : Finset S, P.Nonempty → N.IsCriticalSiphon P → N.SiphonCarried ϕ x₀ P →
    (∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive) ∨
      (∃ Q : Finset S, Q.Nonempty ∧ N.IsCriticalSiphon Q ∧ Q.card < P.card ∧
        N.SiphonCarried ϕ x₀ Q)

/-- **The descent reaches a positive ω-limit point from any carried critical siphon.** Strong
induction on the siphon cardinality: a carried critical siphon either already exposes a positive
ω-limit point or, by `ComparableGrowthDescent`, hands off a strictly smaller carried critical siphon,
and a chain of strictly decreasing cardinalities terminates. -/
theorem omegaLimit_positive_of_descend (N : Network S)
    {ϕ : Flow ℝ≥0 (Concentration S)} {x₀ : Concentration S}
    (hdesc : N.ComparableGrowthDescent ϕ x₀)
    {P₀ : Finset S} (hP₀ne : P₀.Nonempty) (hP₀crit : N.IsCriticalSiphon P₀)
    (hP₀carr : N.SiphonCarried ϕ x₀ P₀) :
    ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive := by
  -- strong induction on the cardinality of the carried critical siphon
  suffices h : ∀ n : ℕ, ∀ P : Finset S, P.card = n → P.Nonempty → N.IsCriticalSiphon P →
      N.SiphonCarried ϕ x₀ P → ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive by
    exact h P₀.card P₀ rfl hP₀ne hP₀crit hP₀carr
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P hPcard hPne hPcrit hPcarr
    rcases hdesc.descend P hPne hPcrit hPcarr with hpos | ⟨Q, hQne, hQcrit, hQlt, hQcarr⟩
    · exact hpos
    · exact ih Q.card (hPcard ▸ hQlt) Q rfl hQne hQcrit hQcarr

/-- **A boundary ω-limit point launches the descent.** If some ω-limit point `w` lies on the
boundary — a coordinate `w s₁ = 0` — its zero set is a nonempty critical siphon carried by the
trajectory, so the comparable-growth descent delivers a strictly positive ω-limit point. -/
theorem omegaLimit_positive_of_boundary_point (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S} (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, (y : Concentration S).Nonnegative)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx0pos : x₀.Positive) (hdesc : N.ComparableGrowthDescent ϕ x₀)
    {w : Concentration S} (hw : w ∈ omegaLimit atTop ϕ {x₀}) {s₁ : S} (hs₁ : w s₁ = 0) :
    ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive := by
  classical
  -- the zero set of the boundary ω-point is a nonempty carried critical siphon
  set P : Finset S := Finset.univ.filter (fun s => w s = 0) with hPdef
  have hP : ∀ s, s ∈ P ↔ w s = 0 := fun s => by
    rw [hPdef, Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ s, h⟩⟩
  have hPne : P.Nonempty := ⟨s₁, (hP s₁).mpr hs₁⟩
  have hcarr : N.SiphonCarried ϕ x₀ P := ⟨w, hw, hP⟩
  have hcrit : N.IsCriticalSiphon P :=
    N.isCriticalSiphon_of_siphonCarried κ hϕγ hK hmaps hωnn hgenω hωaff hx0pos hPne hcarr
  exact N.omegaLimit_positive_of_descend hdesc hPne hcrit hcarr

/-- **The comparable-growth descent produces a positive ω-limit point.** Either every ω-limit point
is already strictly positive — and the ω-limit set is nonempty for a trajectory absorbed by the
compact closed region `K` — or some ω-limit point sits on the boundary and
`omegaLimit_positive_of_boundary_point` runs the descent to a positive ω-limit point. Either way an
interior ω-limit point exists. -/
theorem omegaLimit_positive_of_comparableGrowthDescent (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S} (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hKcl : IsClosed K)
    (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, (y : Concentration S).Nonnegative)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx0pos : x₀.Positive) (hdesc : N.ComparableGrowthDescent ϕ x₀) :
    ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive := by
  classical
  by_cases hall : ∀ w ∈ omegaLimit atTop ϕ {x₀}, w.Positive
  · -- the ω-limit set of a precompact orbit is nonempty
    have hsubK : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ K := by
      rintro z ⟨t, -, x, hx, rfl⟩; rw [Set.mem_singleton_iff] at hx; subst hx; exact hmaps t
    have habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K :=
      ⟨Set.univ, univ_mem, hKcl.closure_subset_iff.mpr hsubK⟩
    obtain ⟨w, hw⟩ :=
      nonempty_omegaLimit_of_isCompact_absorbing atTop ϕ {x₀} hK habs (Set.singleton_nonempty x₀)
    exact ⟨w, hw, hall w hw⟩
  · -- otherwise some ω-point is on the boundary; launch the descent
    obtain ⟨w, hw, hwnp⟩ : ∃ w ∈ omegaLimit atTop ϕ {x₀}, ¬ w.Positive := by
      by_contra h
      exact hall fun w hw => not_not.mp fun hwp => h ⟨w, hw, hwp⟩
    have hwnn : w.Nonnegative := hωnn w hw
    obtain ⟨s₁, hs₁⟩ : ∃ s, ¬ 0 < w s := not_forall.mp hwnp
    have hs₁0 : w s₁ = 0 := le_antisymm (not_lt.mp hs₁) (hwnn s₁)
    exact N.omegaLimit_positive_of_boundary_point κ hϕγ hK hmaps hωnn hgenω hωaff hx0pos hdesc
      hw hs₁0

/-- **Siphon-dimension descent ⇒ the global attractor conclusion.** Combining the comparable-growth
descent with `omegaLimit_eq_singleton_of_mem_positive`: for a weakly reversible network with a
positive complex-balanced reference `x*` and a positive start `x₀` in its class, the standard LaSalle
data of the mass-action semiflow together with the carried descent hypothesis force the ω-limit set
to be the single equilibrium `{x*}`. The descent supplies the strictly positive ω-limit point; the
relative-entropy Lyapunov stack collapses the whole ω-limit set to `{x*}`.

This is the shape of Anderson's single-linkage-class theorem with the comparable-growth Lyapunov
estimate isolated as `ComparableGrowthDescent`. -/
theorem omegaLimit_eq_singleton_of_comparableGrowthDescent
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0compat : N.StoichCompatible x₀ xstar)
    (hγ0 : ∀ x, γ x 0 = x) (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hKcl : IsClosed K)
    (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    {c : ℝ} (hωc : ∀ z ∈ omegaLimit atTop ϕ {x₀}, relEntropy xstar z = c)
    (hposorbit : ∀ p ∈ omegaLimit atTop ϕ {x₀}, Concentration.Positive p →
      ∀ t : ℝ, 0 ≤ t → Concentration.Positive (γ p t))
    (hx0pos : x₀.Positive) (hdesc : N.ComparableGrowthDescent ϕ x₀) :
    omegaLimit atTop ϕ {x₀} = {xstar} :=
  N.omegaLimit_eq_singleton_of_mem_positive hwr κ hxs hcb hx0compat hγ0 hϕγ hgenω hωnn hωaff hωc
    hposorbit
    (N.omegaLimit_positive_of_comparableGrowthDescent κ hϕγ hK hKcl hmaps hωnn hgenω hωaff hx0pos
      hdesc)

/-! ## Branch (I) of the high-codimension residue: where the descent iteration actually stops

Branch (I) of the residue of `CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace`
is the trichotomy's second disjunct: a carried critical siphon `Q` with `Q.card < Pmax.card`
exists (`hzcard` does not refute it — it only bounds zero sets from above).  `Q` is not itself a
positive ω-point, so the obvious rescue is to iterate: run the induction of
`omegaLimit_positive_of_descend` from `Pmax` to `Q`, `Q'`, … down to the empty siphon.  The lemmas
below pin down exactly what such an iteration can and cannot do; all five are pure combinatorics
of the carried/critical data — no orbit hypotheses are needed.

* `descendStep_of_carried_card_lt`: above any carried critical siphon of strictly smaller
  cardinality the descent step's right disjunct is available **for free** — the smaller siphon
  itself is the witness.  Branch (I) therefore supplies the descent step at `Pmax` (and at every
  carried critical siphon of cardinality strictly above the minimum, by `Pm` below).
* `exists_cardMinimal_carried_siphon`: cardinalities of carried critical siphons are a nonempty
  set of naturals, so a cardinality-minimal carried critical siphon `Pm` exists.
* `exists_cardMinimal_carried_siphon_lt`: under branch (I) relative to a carried critical `P₀`
  (in the residual, `P₀ = Pmax`, carried by `wmax`), that minimum satisfies `Pm.card < P₀.card`.
* `descendStep_iff_omegaPointPositive_of_cardMinimal`: **at the minimum the descent step is the
  goal itself.**  Its right disjunct would need a carried critical siphon of cardinality strictly
  below `Pm.card`, which minimality forbids, so the disjunction collapses to its left disjunct —
  byte-identical to this theorem's conclusion.  Unconditional.
* `comparableGrowthDescent_iff_omegaPointPositive`: consequently the *whole* structure
  `N.ComparableGrowthDescent ϕ x₀` is equivalent to the goal once a single carried critical
  siphon is in hand: `→` is `omegaLimit_positive_of_descend`, `←` is `Or.inl`.

**Verdict for branch (I).**  Read against the in-tree proof of `omegaLimit_positive_of_descend`:
under a failed goal its induction can only follow *right* disjuncts, each strictly decreasing the
cardinality of a carried critical siphon; cardinalities are naturals, so the chain reaches a
cardinality-minimal `Pm`, and the next (final) call of `descend` there can neither recurse — no
strictly smaller carried siphon exists — nor fire its left disjunct without *being* the goal.
Hence neither "iterate the argument at `Q, Q', …`" nor "prove `descend` only at the specific
siphons the residual produces" can discharge branch (I) without already proving the conclusion:
the specific siphons always include a cardinality-minimal one, and there `descend` is literally
this theorem's statement (`descendStep_iff_omegaPointPositive_of_cardMinimal`), while assembling
the full structure is the statement itself (`comparableGrowthDescent_iff_omegaPointPositive`).
Closing branch (I) therefore requires *excluding* it (a dynamical argument under the genuine
orbit hypotheses) or an argument that does not route through `ComparableGrowthDescent`. -/

/-- **A strictly smaller carried critical siphon supplies the descent step's right disjunct at any
larger siphon — no further hypotheses.** -/
theorem descendStep_of_carried_card_lt (N : Network S)
    {ϕ : Flow ℝ≥0 (Concentration S)} {x₀ : Concentration S} {P Q : Finset S}
    (hQne : Q.Nonempty) (hQcrit : N.IsCriticalSiphon Q) (hQcarr : N.SiphonCarried ϕ x₀ Q)
    (hlt : Q.card < P.card) :
    (∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive) ∨
      (∃ R : Finset S, R.Nonempty ∧ N.IsCriticalSiphon R ∧ R.card < P.card ∧
        N.SiphonCarried ϕ x₀ R) :=
  Or.inr ⟨Q, hQne, hQcrit, hlt, hQcarr⟩

/-- **A cardinality-minimal carried critical siphon exists.**  The cardinalities realized by
nonempty carried critical siphons form a nonempty set of natural numbers, so `Nat.find` realizes
the minimum. -/
theorem exists_cardMinimal_carried_siphon (N : Network S)
    {ϕ : Flow ℝ≥0 (Concentration S)} {x₀ : Concentration S}
    (h : ∃ P : Finset S, N.IsCriticalSiphon P ∧ N.SiphonCarried ϕ x₀ P) :
    ∃ m : ℕ, ∃ Pm : Finset S,
      N.IsCriticalSiphon Pm ∧ N.SiphonCarried ϕ x₀ Pm ∧ Pm.card = m ∧
        ∀ Q : Finset S, N.IsCriticalSiphon Q → N.SiphonCarried ϕ x₀ Q → m ≤ Q.card := by
  classical
  obtain ⟨P₀, hP₀crit, hP₀carr⟩ := h
  let hm : ∃ n : ℕ, ∃ Q : Finset S,
      N.IsCriticalSiphon Q ∧ N.SiphonCarried ϕ x₀ Q ∧ Q.card = n :=
    ⟨P₀.card, P₀, hP₀crit, hP₀carr, rfl⟩
  obtain ⟨Pm, hPmcrit, hPmcarr, hPmcard⟩ :
      ∃ Q : Finset S, N.IsCriticalSiphon Q ∧ N.SiphonCarried ϕ x₀ Q ∧
        Q.card = Nat.find hm :=
    Nat.find_spec hm
  refine ⟨Nat.find hm, Pm, hPmcrit, hPmcarr, hPmcard, fun Q hQcrit hQcarr => ?_⟩
  by_contra hle
  push Not at hle
  exact Nat.find_min hm hle ⟨Q, hQcrit, hQcarr, rfl⟩

/-- **Branch (I) produces a cardinality-minimal carried critical siphon strictly below the
reference siphon.**  In the residual the reference is `P₀ = Pmax` (carried by `wmax`, critical by
`isCriticalSiphon_of_siphonCarried`), and the branch-(I) witness `Q` with `Q.card < Pmax.card`
bounds the minimum from above. -/
theorem exists_cardMinimal_carried_siphon_lt (N : Network S)
    {ϕ : Flow ℝ≥0 (Concentration S)} {x₀ : Concentration S} {P₀ : Finset S}
    (hI : ∃ Q : Finset S, N.IsCriticalSiphon Q ∧ N.SiphonCarried ϕ x₀ Q ∧ Q.card < P₀.card) :
    ∃ Pm : Finset S,
      N.IsCriticalSiphon Pm ∧ N.SiphonCarried ϕ x₀ Pm ∧ Pm.card < P₀.card ∧
        ∀ Q : Finset S, N.IsCriticalSiphon Q → N.SiphonCarried ϕ x₀ Q → Pm.card ≤ Q.card := by
  obtain ⟨Q, hQcrit, hQcarr, hlt⟩ := hI
  obtain ⟨m, Pm, hPmcrit, hPmcarr, hPmcard, hmin⟩ :=
    N.exists_cardMinimal_carried_siphon ⟨Q, hQcrit, hQcarr⟩
  have hPmlt : Pm.card < P₀.card := by
    rw [hPmcard]
    exact lt_of_le_of_lt (hmin Q hQcrit hQcarr) hlt
  exact ⟨Pm, hPmcrit, hPmcarr, hPmlt, fun R hRcrit hRcarr => by
    rw [hPmcard]
    exact hmin R hRcrit hRcarr⟩

/-- **At a cardinality-minimal carried critical siphon the descent step is the goal itself.**

The hypothesis `hmin` says `P` realizes the minimum cardinality among carried critical siphons —
exactly the invariant `exists_cardMinimal_carried_siphon` establishes.  The step's right disjunct
would exhibit a carried critical siphon of cardinality strictly below that minimum, so under
`hmin` the disjunction reduces to its left disjunct, which is this theorem's conclusion
verbatim; the reverse implication is `Or.inl`. -/
theorem descendStep_iff_omegaPointPositive_of_cardMinimal (N : Network S)
    {ϕ : Flow ℝ≥0 (Concentration S)} {x₀ : Concentration S} {P : Finset S}
    (hmin : ∀ Q : Finset S, N.IsCriticalSiphon Q → N.SiphonCarried ϕ x₀ Q → P.card ≤ Q.card) :
    ((∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive) ∨
      (∃ Q : Finset S, Q.Nonempty ∧ N.IsCriticalSiphon Q ∧ Q.card < P.card ∧
        N.SiphonCarried ϕ x₀ Q)) ↔
      (∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive) := by
  constructor
  · intro h
    rcases h with h | ⟨Q, _, hQcrit, hlt, hQcarr⟩
    · exact h
    · exact absurd hlt (not_lt.mpr (hmin Q hQcrit hQcarr))
  · exact Or.inl

/-- **The full descent structure is the conclusion.**  Given any nonempty carried critical siphon
(in the residual: `Pmax`, nonempty by `hPmaxne`, critical by
`isCriticalSiphon_of_siphonCarried`, carried by `⟨wmax, hwmax, hzeroMax⟩`),
`N.ComparableGrowthDescent ϕ x₀` holds **iff** a strictly positive ω-point exists: `→` is
`omegaLimit_positive_of_descend` launched at that siphon, `←` fills every `descend` instance with
the left disjunct.  So no proof can assemble the structure — fully or for any set of siphons
covering a cardinality-minimal one — as a strictly weaker stepping stone to the goal. -/
theorem comparableGrowthDescent_iff_omegaPointPositive (N : Network S)
    {ϕ : Flow ℝ≥0 (Concentration S)} {x₀ : Concentration S} {P₀ : Finset S}
    (hP₀crit : N.IsCriticalSiphon P₀) (hP₀carr : N.SiphonCarried ϕ x₀ P₀) :
    N.ComparableGrowthDescent ϕ x₀ ↔
      (∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive) := by
  constructor
  · intro hdesc
    exact N.omegaLimit_positive_of_descend hdesc hP₀crit.1 hP₀crit hP₀carr
  · intro h
    exact ⟨fun _P _hne _hcrit _hcarr => Or.inl h⟩

end Network

end CRNT
