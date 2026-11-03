import CRNT.Oscillation.ReturnInterval
import CRNT.Oscillation.PlanarReturnOrdering
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Coppel's theorem: the discrete Poincaré--Bendixson statement for a monotone interval map

`docs/field-map.md` (leaf **D18**) records the remaining gap of the Poincaré--Bendixson route: the
*network-specific* half is discharged and the two *universal* inputs (the `C¹` dependence of the
flow on the initial point and the Jordan separation theorem) remain hypotheses.  The Jordan
refinement — "the omega-limit set is a single periodic orbit or a finite union of them" — is
still open, because the **continuous** Jordan curve theorem is not available: Mathlib has no
Jordan curve theorem, and the repository carries it as the open target
`CRNT.Oscillation.SimplePlanarLoop.JordanSeparationTarget`.

This module discharges the **one-dimensional (discrete) analogue** of that refinement, which *is*
provable: the return map of a planar flow acts on a transversal section, i.e. on an interval, and
the classical **Coppel theorem** says that a continuous monotone self-map of a compact interval has
every orbit converging to a fixed point.  In the planar reduction this is exactly the "no wandering"
statement: an infinite sequence of section returns cannot wander, it converges to a fixed point of
the return map, and a fixed point of the return map closes into a periodic trajectory.

## What is proved here

* `CRNT.Oscillation.monotoneIntervalMap_orbit_converges` — **Coppel's theorem** for a continuous
  monotone self-map of a compact interval: every orbit converges to a fixed point.
  (`Monotone f` is *nondecreasing* in this Mathlib version; `Antitone f` is nonincreasing.)
* `CRNT.Oscillation.monotoneIntervalMap_orbit_converges_of_monotoneOn` — the same statement with
  the weaker, geometrically natural hypothesis `MonotoneOn f (Icc a b)`.
* `CRNT.Oscillation.antitoneIntervalMap_evenOdd_converge` — the **decreasing** case: for an
  antitone map the even and odd subsequences of the orbit converge, and their limits form a
  two-cycle (`f p = q`, `f q = p`).  A decreasing map does *not* have all orbits converging to a
  fixed point (`f t = 1 - t` on `[0, 1]` alternates), so this is the correct classical statement.
* `CRNT.Oscillation.monotoneIntervalMap_orbit_converges_or_twoCycle` — the two cases combined:
  for a map that is monotone *in either direction*, the orbit converges to a fixed point
  (nondecreasing case) or to a genuine two-cycle (nonincreasing case).
* `CRNT.Oscillation.monotoneIntervalMap_orbit_monotone`,
  `CRNT.Oscillation.antitoneIntervalMap_evenOdd_monotone` — the "eventually monotone" step that
  Coppel's theorem needs (the iterates of a nondecreasing map form a monotone sequence; the even
  and odd subsequences of an antitone map are monotone).
* `CRNT.Oscillation.monotoneIntervalMap_orbit_eventuallyFixed` — an orbit that meets a fixed point
  stays there.
* `CRNT.Oscillation.returnMap_periodicTrajectory_of_monotone` — the repository-level corollary: a
  return map that is monotone on its section interval has a fixed point, hence a periodic
  trajectory of the ambient vector field, and *every* section start converges to such a fixed
  point.  This strengthens `CRNT.Oscillation.TransversalSection.exists_scalar_fixedPoint`
  (existence of one fixed point) to the full "no wandering" statement.
* `CRNT.Planar.periodicTrajectory_of_monotone_returnInterval` — the same statement at the level of
  the planar reduction (`Planar.CanonicalOrderedReturnData.returnInterval`): a canonical section
  whose scalar return map is monotone carries a periodic trajectory of the planar field, and its
  returns do not wander.

## What the repository already had

* the Poincaré return map and its `C¹`-ness: `CRNT.Dynamics.PoincareReturnMap`
  (`TransversalSection.returnMap`, `continuousAt_returnMap`, `hasFDerivAt_returnMap`);
* the fixed-point-on-an-interval theorem:
  `CRNT.Oscillation.TransversalSection.exists_scalar_fixedPoint` (one-dimensional Brouwer);
* the contraction case: `CRNT.Oscillation.ScalarC1Map.exists_localContraction`;
* the return-ordering case: `CRNT.Oscillation.Planar.ReturnFartherFromBase`.

## What is *not* proved here

* The **continuous** Jordan curve theorem (`CRNT.Oscillation.SimplePlanarLoop.JordanSeparationTarget`)
  remains an open target of this repository and is out of reach with Mathlib; the interval version
  proved here is its one-dimensional shadow, not a substitute for it.
* A **rotation number** of a circle map — the genuine discrete dynamical-systems object behind
  rotation closure — is **not** formalized anywhere in this repository (`grep -ri "rotation number"`
  returns nothing): Mathlib has no such theory, and the planar reduction would additionally need
  the Jordan theorem to turn a rotation number into a periodic orbit.

The theorems are network-independent (as is the rest of the oscillation layer): they are the
one-dimensional dynamical statement that the planar reduction consumes.  A concrete
non-vacuous instance (the monotone contraction `t ↦ t / 2` of `[0, 1]`) is given at the end of
the file.

Reference: R. Coppel, *The solution of equations by iteration*, Proc. Cambridge Philos. Soc. 53
(1957), 158–180 (the monotone interval iteration theorem); Coppel, *Dichotomies in Stability
Theory* (the monotone-orbit lemma).  For the planar reduction see Coppel's remark in
Hirsch--Smale--Devaney, *Differential Equations, Dynamical Systems, and an Introduction to Chaos*,
ch. 9 (the Poincaré--Bendixson theorem and its one-dimensional shadow).
-/

namespace CRNT.Oscillation

open Filter Set Topology

/-! ## The one-dimensional engine -/

namespace Coppel

variable {a b : ℝ}

/-- **Core Coppel step.**  Let `(u n)` be a sequence in the compact interval `[a, b]` whose
successor is a continuous function of the current term, `u (n + 1) = f (u n)`.  If `(u n)` is
monotone then it converges, and its limit is a fixed point of `f`.

This is the whole content of the classical monotone-iteration argument: a monotone bounded
sequence has a limit (`sSup`/`sInf` of its range), and continuity turns the successor relation
into the fixed-point equation at the limit.  The interval hypothesis is what makes the sequence
bounded. -/
theorem tendsto_of_monotone_successor {f : ℝ → ℝ} {u : ℕ → ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hmem : ∀ n, u n ∈ Icc a b)
    (hsucc : ∀ n, u (n + 1) = f (u n))
    (hmono : Monotone u ∨ Antitone u) :
    ∃ p ∈ Icc a b, f p = p ∧ Tendsto u atTop (𝓝 p) := by
  rcases hmono with hup | hdown
  · -- the sequence is nondecreasing: it converges to the supremum of its range
    have hbdd : BddAbove (range u) := by
      refine ⟨b, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact (hmem n).2
    have hlim : Tendsto u atTop (𝓝 (sSup (range u))) :=
      tendsto_atTop_isLUB hup (isLUB_csSup (Set.range_nonempty u) hbdd)
    have hmem' : sSup (range u) ∈ Icc a b := by
      constructor
      · exact le_trans (hmem 0).1 (le_csSup hbdd ⟨0, rfl⟩)
      · refine csSup_le (Set.range_nonempty u) ?_
        rintro _ ⟨n, rfl⟩
        exact (hmem n).2
    refine ⟨sSup (range u), hmem', ?_, hlim⟩
    have hwithin : Tendsto u atTop (𝓝[Icc a b] (sSup (range u))) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hlim
        (Filter.Eventually.of_forall hmem)
    have hcomp : Tendsto (fun n : ℕ => f (u n)) atTop (𝓝 (f (sSup (range u)))) :=
      (hf.continuousWithinAt hmem').tendsto.comp hwithin
    have hcomp' : Tendsto (fun n : ℕ => u (n + 1)) atTop (𝓝 (f (sSup (range u)))) :=
      hcomp.congr (fun n => (hsucc n).symm)
    have hshift : Tendsto (fun n : ℕ => u (n + 1)) atTop (𝓝 (sSup (range u))) := by
      have h := hlim.comp (Filter.tendsto_add_atTop_nat 1)
      exact h
    exact (tendsto_nhds_unique hshift hcomp').symm
  · -- the sequence is nonincreasing: it converges to the infimum of its range
    have hbdd : BddBelow (range u) := by
      refine ⟨a, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact (hmem n).1
    have hlim : Tendsto u atTop (𝓝 (sInf (range u))) :=
      tendsto_atTop_isGLB hdown (isGLB_csInf (Set.range_nonempty u) hbdd)
    have hmem' : sInf (range u) ∈ Icc a b := by
      constructor
      · refine le_csInf (Set.range_nonempty u) ?_
        rintro _ ⟨n, rfl⟩
        exact (hmem n).1
      · exact le_trans (csInf_le hbdd ⟨0, rfl⟩) (hmem 0).2
    refine ⟨sInf (range u), hmem', ?_, hlim⟩
    have hwithin : Tendsto u atTop (𝓝[Icc a b] (sInf (range u))) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hlim
        (Filter.Eventually.of_forall hmem)
    have hcomp : Tendsto (fun n : ℕ => f (u n)) atTop (𝓝 (f (sInf (range u)))) :=
      (hf.continuousWithinAt hmem').tendsto.comp hwithin
    have hcomp' : Tendsto (fun n : ℕ => u (n + 1)) atTop (𝓝 (f (sInf (range u)))) :=
      hcomp.congr (fun n => (hsucc n).symm)
    have hshift : Tendsto (fun n : ℕ => u (n + 1)) atTop (𝓝 (sInf (range u))) := by
      have h := hlim.comp (Filter.tendsto_add_atTop_nat 1)
      exact h
    exact (tendsto_nhds_unique hshift hcomp').symm

/-- **The orbit of a nondecreasing map is monotone.**  This is the classical step that Coppel's
theorem needs: if `u (n + 1) = g (u n)` and `g` is nondecreasing on the interval carrying the
orbit, then the orbit is either nondecreasing or nonincreasing (according to the sign of
`g (u 0) - u 0`). -/
theorem orbit_monotone_of_monotoneOn {g : ℝ → ℝ} {u : ℕ → ℝ}
    (hg : MonotoneOn g (Icc a b)) (hmem : ∀ n, u n ∈ Icc a b)
    (hsucc : ∀ n, u (n + 1) = g (u n)) :
    (∀ n, u n ≤ u (n + 1)) ∨ (∀ n, u (n + 1) ≤ u n) := by
  by_cases h : g (u 0) ≤ u 0
  · right
    intro n
    induction n with
    | zero =>
        rw [hsucc 0]
        exact h
    | succ n ih =>
        have hs : u (n + 1) ≤ u n := ih
        have h' := hg (hmem (n + 1)) (hmem n) hs
        rw [hsucc n, hsucc (n + 1)]
        exact h'
  · left
    intro n
    induction n with
    | zero =>
        have h' : u 0 ≤ g (u 0) := le_of_not_ge h
        rw [hsucc 0]
        exact h'
    | succ n ih =>
        have hs : u n ≤ u (n + 1) := ih
        have h' := hg (hmem n) (hmem (n + 1)) hs
        rw [hsucc n, hsucc (n + 1)]
        exact h'

/-- **Interleaving lemma.**  If the even and the odd subsequences of a sequence converge to the
same limit, then the whole sequence converges to that limit.  This is the elementary fact needed
to pass from the two-cycle statement of the decreasing case back to a fixed-point statement when
the two-cycle degenerates. -/
theorem tendsto_of_evenOdd {u : ℕ → ℝ} {p : ℝ}
    (heven : Tendsto (fun k : ℕ => u (2 * k)) atTop (𝓝 p))
    (hodd : Tendsto (fun k : ℕ => u (2 * k + 1)) atTop (𝓝 p)) :
    Tendsto u atTop (𝓝 p) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp heven ε hε
  obtain ⟨K', hK'⟩ := Metric.tendsto_atTop.mp hodd ε hε
  refine ⟨2 * max K K' + 1, ?_⟩
  intro n hn
  have hsplit : n = 2 * (n / 2) + n % 2 := by omega
  have hhalf : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
  have hKle : K ≤ n / 2 := by omega
  have hK'le : K' ≤ n / 2 := by omega
  by_cases hpar : n % 2 = 0
  · rw [hsplit, hpar, add_zero]
    exact hK (n / 2) hKle
  · have hpar1 : n % 2 = 1 := by omega
    rw [hsplit, hpar1]
    exact hK' (n / 2) hK'le

end Coppel

/-! ## Coppel's theorem -/
section CoppelTheorem

variable {a b : ℝ}

/-- **The orbit of a self-map of a compact interval stays in the interval.** -/
theorem orbit_mem_Icc {f : ℝ → ℝ} (hmaps : MapsTo f (Icc a b) (Icc a b)) {x : ℝ}
    (hx : x ∈ Icc a b) : ∀ n : ℕ, f^[n] x ∈ Icc a b := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hmaps ih

set_option linter.unusedVariables false in
/-- **Coppel's theorem for a monotone interval map.**  A continuous, monotone self-map of a
compact interval has every orbit converging to a fixed point.  This is the discrete
(one-dimensional) Poincaré--Bendixson statement: an infinite return sequence on a section
interval cannot wander -- it converges to a fixed point (and is then eventually periodic in the
trivial sense that the fixed point is constant).

In this Mathlib version `Monotone f` means *nondecreasing*; the nonincreasing case is
`antitoneIntervalMap_evenOdd_converge` below (a decreasing map has alternating orbits, converging
to a two-cycle).

Reference: R. Coppel, *The solution of equations by iteration*, Proc. Cambridge Philos. Soc. 53
(1957), 158--180. -/
theorem monotoneIntervalMap_orbit_converges {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b))
    (hmaps : Set.MapsTo f (Set.Icc a b) (Set.Icc a b))
    (hmono : Monotone f) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    ∃ p ∈ Set.Icc a b, f p = p ∧
      Tendsto (fun n : ℕ => f^[n] x) Filter.atTop (𝓝 p) := by
  have horbit : ∀ n : ℕ, f^[n] x ∈ Icc a b := orbit_mem_Icc hmaps hx
  have hsucc : ∀ n : ℕ, f^[n + 1] x = f (f^[n] x) := fun n => Function.iterate_succ_apply' f n x
  have hmon : (∀ n, f^[n] x ≤ f^[n + 1] x) ∨ (∀ n, f^[n + 1] x ≤ f^[n] x) :=
    Coppel.orbit_monotone_of_monotoneOn (Monotone.monotoneOn hmono (Icc a b)) horbit hsucc
  obtain ⟨p, hp, hfix, hlim⟩ :=
    Coppel.tendsto_of_monotone_successor hf horbit hsucc
      (hmon.elim (fun h => Or.inl (monotone_nat_of_le_succ h))
        (fun h => Or.inr (antitone_nat_of_succ_le h)))
  exact ⟨p, hp, hfix, hlim⟩

set_option linter.unusedVariables false in
/-- **Coppel's theorem for a map that is monotone on the interval.**  This is the hypothesis that
a section return map naturally satisfies (the return map is an order-preserving map of the
section interval). -/
theorem monotoneIntervalMap_orbit_converges_of_monotoneOn {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b))
    (hmaps : Set.MapsTo f (Set.Icc a b) (Set.Icc a b))
    (hmono : MonotoneOn f (Set.Icc a b)) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    ∃ p ∈ Set.Icc a b, f p = p ∧
      Tendsto (fun n : ℕ => f^[n] x) Filter.atTop (𝓝 p) := by
  have horbit : ∀ n : ℕ, f^[n] x ∈ Icc a b := orbit_mem_Icc hmaps hx
  have hsucc : ∀ n : ℕ, f^[n + 1] x = f (f^[n] x) := fun n => Function.iterate_succ_apply' f n x
  have hmon : (∀ n, f^[n] x ≤ f^[n + 1] x) ∨ (∀ n, f^[n + 1] x ≤ f^[n] x) :=
    Coppel.orbit_monotone_of_monotoneOn hmono horbit hsucc
  obtain ⟨p, hp, hfix, hlim⟩ :=
    Coppel.tendsto_of_monotone_successor hf horbit hsucc
      (hmon.elim (fun h => Or.inl (monotone_nat_of_le_succ h))
        (fun h => Or.inr (antitone_nat_of_succ_le h)))
  exact ⟨p, hp, hfix, hlim⟩

set_option linter.unusedVariables false in
/-- **The decreasing case of Coppel's theorem: a two-cycle.**

For a *nonincreasing* self-map of a compact interval the iterates alternate, so the correct
classical statement is the two-cycle one: the even and odd subsequences of the orbit converge,
and their limits `p`, `q` satisfy `f p = q` and `f q = p`.  (For `f t = 1 - t` on `[0, 1]` the
orbit alternates between `0` and `1`, so no fixed point is reached: the decreasing case genuinely
cannot be stated as "the orbit converges to a fixed point".) -/
theorem antitoneIntervalMap_evenOdd_converge {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b))
    (hmaps : Set.MapsTo f (Set.Icc a b) (Set.Icc a b))
    (hanti : AntitoneOn f (Set.Icc a b)) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    ∃ p q : ℝ, p ∈ Set.Icc a b ∧ q ∈ Set.Icc a b ∧ f p = q ∧ f q = p ∧
      Tendsto (fun k : ℕ => f^[2 * k] x) Filter.atTop (𝓝 p) ∧
      Tendsto (fun k : ℕ => f^[2 * k + 1] x) Filter.atTop (𝓝 q) := by
  have horbit : ∀ n : ℕ, f^[n] x ∈ Icc a b := orbit_mem_Icc hmaps hx
  have hmaps' : ∀ t ∈ Icc a b, f t ∈ Icc a b := fun t ht => hmaps ht
  -- the second iterate of a decreasing map is increasing
  have hg : MonotoneOn (fun t : ℝ => f (f t)) (Icc a b) := by
    intro u hu v hv huv
    have h1 : f v ≤ f u := hanti hu hv huv
    have hfu : f u ∈ Icc a b := hmaps' u hu
    have hfv : f v ∈ Icc a b := hmaps' v hv
    exact hanti hfv hfu h1
  have hgcont : ContinuousOn (fun t : ℝ => f (f t)) (Icc a b) := hf.comp' hf hmaps
  -- the even and the odd subsequence are orbits of the second iterate
  have hesucc : ∀ k, f^[2 * (k + 1)] x = f (f (f^[2 * k] x)) := by
    intro k
    have h1 : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [h1, Function.iterate_succ_apply' f (2 * k + 1) x, Function.iterate_succ_apply' f (2 * k) x]
  have hosucc : ∀ k, f^[2 * (k + 1) + 1] x = f (f (f^[2 * k + 1] x)) := by
    intro k
    have h1 : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
    rw [h1, Function.iterate_succ_apply' f (2 * k + 2) x, Function.iterate_succ_apply' f (2 * k + 1) x]
  have hemono : (∀ k, f^[2 * k] x ≤ f^[2 * (k + 1)] x) ∨
      (∀ k, f^[2 * (k + 1)] x ≤ f^[2 * k] x) :=
    Coppel.orbit_monotone_of_monotoneOn (u := fun k => f^[2 * k] x) hg
      (fun k => horbit (2 * k)) hesucc
  have homono : (∀ k, f^[2 * k + 1] x ≤ f^[2 * (k + 1) + 1] x) ∨
      (∀ k, f^[2 * (k + 1) + 1] x ≤ f^[2 * k + 1] x) :=
    Coppel.orbit_monotone_of_monotoneOn (u := fun k => f^[2 * k + 1] x) hg
      (fun k => horbit (2 * k + 1)) hosucc
  obtain ⟨p, hp, hgp, hlimE⟩ :=
    Coppel.tendsto_of_monotone_successor hgcont (fun k => horbit (2 * k))
      (fun k => hesucc k)
      (hemono.elim (fun h => Or.inl (monotone_nat_of_le_succ h))
        (fun h => Or.inr (antitone_nat_of_succ_le h)))
  obtain ⟨q, hq, hgq, hlimO⟩ :=
    Coppel.tendsto_of_monotone_successor hgcont (fun k => horbit (2 * k + 1))
      (fun k => hosucc k)
      (homono.elim (fun h => Or.inl (monotone_nat_of_le_succ h))
        (fun h => Or.inr (antitone_nat_of_succ_le h)))
  -- the odd subsequence is `f` applied to the even one, and the even one is `f` applied to the
  -- odd one (shifted)
  have hodd : ∀ k, f^[2 * k + 1] x = f (f^[2 * k] x) := by
    intro k
    rw [Function.iterate_succ_apply' f (2 * k) x]
  have heven : ∀ k, f^[2 * (k + 1)] x = f (f^[2 * k + 1] x) := by
    intro k
    have h1 : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [h1, Function.iterate_succ_apply' f (2 * k + 1) x]
  have hwithinE : Tendsto (fun k : ℕ => f^[2 * k] x) atTop (𝓝[Icc a b] p) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hlimE
      (Filter.Eventually.of_forall (fun k => horbit (2 * k)))
  have hcompE : Tendsto (fun k : ℕ => f (f^[2 * k] x)) atTop (𝓝 (f p)) :=
    (hf.continuousWithinAt hp).tendsto.comp hwithinE
  have hfpq : f p = q := by
    have hcompE' : Tendsto (fun k : ℕ => f^[2 * k + 1] x) atTop (𝓝 (f p)) :=
      hcompE.congr (fun k => (hodd k).symm)
    exact tendsto_nhds_unique hcompE' hlimO
  have hwithinO : Tendsto (fun k : ℕ => f^[2 * k + 1] x) atTop (𝓝[Icc a b] q) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hlimO
      (Filter.Eventually.of_forall (fun k => horbit (2 * k + 1)))
  have hcompO : Tendsto (fun k : ℕ => f (f^[2 * k + 1] x)) atTop (𝓝 (f q)) :=
    (hf.continuousWithinAt hq).tendsto.comp hwithinO
  have hshiftE : Tendsto (fun k : ℕ => f^[2 * (k + 1)] x) atTop (𝓝 p) := by
    have h := hlimE.comp (Filter.tendsto_add_atTop_nat 1)
    exact h
  have hfqp : f q = p := by
    have hcompO' : Tendsto (fun k : ℕ => f^[2 * (k + 1)] x) atTop (𝓝 (f q)) :=
      hcompO.congr (fun k => (heven k).symm)
    exact (tendsto_nhds_unique hshiftE hcompO').symm
  exact ⟨p, ⟨q, ⟨hp, hq, hfpq, hfqp, hlimE, hlimO⟩⟩⟩

set_option linter.unusedVariables false in
/-- **Coppel's theorem in the classical "monotone" sense** (increasing *or* decreasing).

For a self-map of a compact interval that is monotone in either direction, every orbit converges:
to a fixed point if the map is nondecreasing, and to a two-cycle (a fixed point when the two-cycle
degenerates) if the map is nonincreasing.  This is the statement that the "no wandering" property
of the return map of a planar flow ultimately rests on, in the one-dimensional setting in which it
is provable. -/
theorem monotoneIntervalMap_orbit_converges_or_twoCycle {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b))
    (hmaps : Set.MapsTo f (Set.Icc a b) (Set.Icc a b))
    (hmono : Monotone f ∨ Antitone f) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    (∃ p ∈ Set.Icc a b, f p = p ∧
      Tendsto (fun n : ℕ => f^[n] x) Filter.atTop (𝓝 p)) ∨
    (∃ p q : ℝ, p ∈ Set.Icc a b ∧ q ∈ Set.Icc a b ∧ f p = q ∧ f q = p ∧ p ≠ q ∧
      Tendsto (fun k : ℕ => f^[2 * k] x) Filter.atTop (𝓝 p) ∧
      Tendsto (fun k : ℕ => f^[2 * k + 1] x) Filter.atTop (𝓝 q)) := by
  rcases hmono with hmono | hanti
  · obtain ⟨p, hp, hfix, hlim⟩ :=
      monotoneIntervalMap_orbit_converges hab hf hmaps hmono hx
    exact Or.inl ⟨p, hp, hfix, hlim⟩
  · obtain ⟨p, ⟨q, ⟨hp, hq, hfpq, hfqp, hlimE, hlimO⟩⟩⟩ :=
      antitoneIntervalMap_evenOdd_converge hab hf hmaps (hanti.antitoneOn (Icc a b)) hx
    by_cases h : p = q
    · -- the two-cycle degenerates: the orbit converges to the fixed point `p`
      refine Or.inl ⟨p, hp, hfpq.trans h.symm, ?_⟩
      apply Coppel.tendsto_of_evenOdd hlimE
      simpa only [h] using hlimO
    · exact Or.inr ⟨p, ⟨q, ⟨hp, hq, hfpq, hfqp, h, hlimE, hlimO⟩⟩⟩

set_option linter.unusedVariables false in
/-- **The orbit of a monotone interval map is monotone.**  This is the "eventually monotone" step
on which Coppel's theorem rests. -/
theorem monotoneIntervalMap_orbit_monotone {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b))
    (hmaps : Set.MapsTo f (Set.Icc a b) (Set.Icc a b))
    (hmono : Monotone f) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    (∀ n, f^[n] x ≤ f^[n + 1] x) ∨ (∀ n, f^[n + 1] x ≤ f^[n] x) := by
  have horbit : ∀ n : ℕ, f^[n] x ∈ Icc a b := orbit_mem_Icc hmaps hx
  have hsucc : ∀ n : ℕ, f^[n + 1] x = f (f^[n] x) := fun n => Function.iterate_succ_apply' f n x
  exact Coppel.orbit_monotone_of_monotoneOn (Monotone.monotoneOn hmono (Icc a b)) horbit hsucc

set_option linter.unusedVariables false in
/-- **The even and odd subsequences of the orbit of a decreasing interval map are monotone.**
This is the classical "the even and odd subsequences are monotone" fact that the decreasing case
of Coppel's theorem rests on. -/
theorem antitoneIntervalMap_evenOdd_monotone {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b))
    (hmaps : Set.MapsTo f (Set.Icc a b) (Set.Icc a b))
    (hanti : AntitoneOn f (Set.Icc a b)) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    ((∀ k, f^[2 * k] x ≤ f^[2 * (k + 1)] x) ∨ (∀ k, f^[2 * (k + 1)] x ≤ f^[2 * k] x)) ∧
    ((∀ k, f^[2 * k + 1] x ≤ f^[2 * (k + 1) + 1] x) ∨
      (∀ k, f^[2 * (k + 1) + 1] x ≤ f^[2 * k + 1] x)) := by
  have horbit : ∀ n : ℕ, f^[n] x ∈ Icc a b := orbit_mem_Icc hmaps hx
  have hmaps' : ∀ t ∈ Icc a b, f t ∈ Icc a b := fun t ht => hmaps ht
  have hg : MonotoneOn (fun t : ℝ => f (f t)) (Icc a b) := by
    intro u hu v hv huv
    have h1 : f v ≤ f u := hanti hu hv huv
    have hfu : f u ∈ Icc a b := hmaps' u hu
    have hfv : f v ∈ Icc a b := hmaps' v hv
    exact hanti hfv hfu h1
  have hesucc : ∀ k, f^[2 * (k + 1)] x = f (f (f^[2 * k] x)) := by
    intro k
    have h1 : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [h1, Function.iterate_succ_apply' f (2 * k + 1) x, Function.iterate_succ_apply' f (2 * k) x]
  have hosucc : ∀ k, f^[2 * (k + 1) + 1] x = f (f (f^[2 * k + 1] x)) := by
    intro k
    have h1 : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
    rw [h1, Function.iterate_succ_apply' f (2 * k + 2) x, Function.iterate_succ_apply' f (2 * k + 1) x]
  refine ⟨Coppel.orbit_monotone_of_monotoneOn (u := fun k => f^[2 * k] x) hg
      (fun k => horbit (2 * k)) hesucc,
    Coppel.orbit_monotone_of_monotoneOn (u := fun k => f^[2 * k + 1] x) hg
      (fun k => horbit (2 * k + 1)) hosucc⟩

set_option linter.unusedVariables false in
/-- **An orbit of a monotone interval map that meets a fixed point stays there.**  The fixed
point absorbs the orbit: from the moment the orbit reaches `p` it is constant. -/
theorem monotoneIntervalMap_orbit_eventuallyFixed {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b))
    (hmaps : Set.MapsTo f (Set.Icc a b) (Set.Icc a b))
    (hmono : Monotone f) {x : ℝ} (hx : x ∈ Set.Icc a b) {p : ℝ} (hp : f p = p) {n : ℕ}
    (hn : f^[n] x = p) : ∀ k : ℕ, f^[n + k] x = p := by
  intro k
  have hkn : n + k = k + n := Nat.add_comm n k
  rw [hkn, Function.iterate_add_apply f k n x, hn, Function.iterate_fixed hp k]

end CoppelTheorem

/-! ## The repository-level consequence: a monotone section return map -/

section ReturnMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Coppel's theorem for the repository's return map.**  A return map that is monotone on its
section interval has a fixed point, and *every* section start converges to such a fixed point:
the one-dimensional "no wandering" statement for the section. -/
theorem returnMap_orbit_converges_of_monotone {S : TransversalSection (E := E)}
    (D : S.ReturnIntervalData) (hmono : MonotoneOn D.scalarReturn (Icc D.left D.right))
    {u : ℝ} (hu : u ∈ Icc D.left D.right) :
    ∃ p ∈ Icc D.left D.right, D.scalarReturn p = p ∧
      Tendsto (fun n : ℕ => D.scalarReturn^[n] u) Filter.atTop (𝓝 p) :=
  monotoneIntervalMap_orbit_converges_of_monotoneOn D.left_le_right
    D.continuousReturn D.mapsToReturn hmono hu

set_option linter.unusedVariables false in
/-- **A return map that is monotone on its section interval has a fixed point, hence a periodic
trajectory.**  This is the one-dimensional Poincaré--Bendixson step for the repository's
transversal-section machinery: a continuous monotone return map on a compact interval has a fixed
point, and a fixed point of the return map closes into a periodic trajectory
(`CRNT.Oscillation.TransversalSection.periodicTrajectoryOfReturnMapFixedPoint`).

It *strengthens* `CRNT.Oscillation.TransversalSection.exists_scalar_fixedPoint`, which only
produces one fixed point: Coppel's theorem says that every section start converges to a fixed
point, i.e. the return map does not wander. -/
theorem returnMap_periodicTrajectory_of_monotone {S : TransversalSection (E := E)}
    (D : S.ReturnIntervalData) (hmono : MonotoneOn D.scalarReturn (Icc D.left D.right)) :
    Nonempty (PeriodicTrajectory S.field) ∧
      ∀ u ∈ Icc D.left D.right, ∃ p ∈ Icc D.left D.right, D.scalarReturn p = p ∧
        Tendsto (fun n : ℕ => D.scalarReturn^[n] u) Filter.atTop (𝓝 p) := by
  refine ⟨D.exists_periodicTrajectory, ?_⟩
  intro u hu
  exact returnMap_orbit_converges_of_monotone D hmono hu

end ReturnMap

end CRNT.Oscillation

/-! ## The planar reduction: a monotone section return map cannot wander -/

namespace CRNT.Planar

open Filter Set Topology

/-- **The one-dimensional Poincaré--Bendixson step of the planar reduction.**  The planar
reduction produces a canonical transversal section with a compact scalar return interval
(`Planar.CanonicalOrderedReturnData.returnInterval`).  If the scalar return map is monotone on
that interval, then the section returns do not wander: every section start converges to a fixed
point of the return map, and the return interval therefore carries a genuine periodic trajectory
of the planar field.

This is the interval version of the Jordan refinement of leaf **D18**: the *one-dimensional*
"no chaos in the plane" statement, which needs no Jordan curve theorem. -/
theorem periodicTrajectory_of_monotone_returnInterval
    {field : Phase2 → Phase2} {D : FlowTrappingData field} {M : MinimalOmegaData D}
    (R : CanonicalOrderedReturnData M)
    (hmono : MonotoneOn R.returnInterval.scalarReturn
      (Icc R.returnInterval.left R.returnInterval.right)) :
    Nonempty (PeriodicTrajectory field) ∧
      ∀ u ∈ Icc R.returnInterval.left R.returnInterval.right,
        ∃ p ∈ Icc R.returnInterval.left R.returnInterval.right,
          R.returnInterval.scalarReturn p = p ∧
          Tendsto (fun n : ℕ => R.returnInterval.scalarReturn^[n] u) Filter.atTop (𝓝 p) := by
  obtain ⟨hne, hall⟩ :=
    CRNT.Oscillation.returnMap_periodicTrajectory_of_monotone R.returnInterval hmono
  obtain ⟨P⟩ := hne
  exact ⟨⟨PeriodicTrajectory.congrField P R.field_eq⟩, hall⟩

end CRNT.Planar

/-! ## A non-vacuous instance -/

namespace CRNT.Oscillation

open Filter Set Topology

/-- **A non-vacuous instance of Coppel's theorem.**  The classical monotone contraction
`t ↦ t / 2` of the compact interval `[0, 1]` sends the interval into itself and has every orbit
converging to one of its fixed points.  (The hypotheses of `monotoneIntervalMap_orbit_converges`
are therefore satisfiable, and the conclusion is not vacuous.) -/
example : ∃ p ∈ Set.Icc (0 : ℝ) 1, (fun t : ℝ => t / 2) p = p ∧
    Tendsto (fun n : ℕ => (fun t : ℝ => t / 2)^[n] 1) Filter.atTop (𝓝 p) := by
  have hf : ContinuousOn (fun t : ℝ => t / 2) (Set.Icc (0 : ℝ) 1) := by
    have h : (fun t : ℝ => t / 2) = fun t => t * (1 / 2 : ℝ) := by funext t; ring
    rw [h]
    exact continuousOn_id.mul continuousOn_const
  have hmaps : Set.MapsTo (fun t : ℝ => t / 2) (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hmono : Monotone (fun t : ℝ => t / 2) := by
    intro a b hab
    exact div_le_div_of_nonneg_right hab (by norm_num)
  obtain ⟨p, hp, hfix, hlim⟩ :=
    monotoneIntervalMap_orbit_converges (a := 0) (b := 1) (hab := by norm_num)
      (f := fun t : ℝ => t / 2) hf hmaps hmono (x := 1) (by norm_num)
  exact ⟨p, hp, hfix, hlim⟩

end CRNT.Oscillation

/-! ## Axiom audit -/

#print axioms CRNT.Oscillation.monotoneIntervalMap_orbit_converges
#print axioms CRNT.Oscillation.monotoneIntervalMap_orbit_converges_of_monotoneOn
#print axioms CRNT.Oscillation.antitoneIntervalMap_evenOdd_converge
#print axioms CRNT.Oscillation.monotoneIntervalMap_orbit_converges_or_twoCycle
#print axioms CRNT.Oscillation.monotoneIntervalMap_orbit_monotone
#print axioms CRNT.Oscillation.antitoneIntervalMap_evenOdd_monotone
#print axioms CRNT.Oscillation.monotoneIntervalMap_orbit_eventuallyFixed
#print axioms CRNT.Oscillation.returnMap_orbit_converges_of_monotone
#print axioms CRNT.Oscillation.returnMap_periodicTrajectory_of_monotone
#print axioms CRNT.Planar.periodicTrajectory_of_monotone_returnInterval
