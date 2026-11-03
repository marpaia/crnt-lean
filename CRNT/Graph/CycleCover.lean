import CRNT.Graph.WeakReversibility

/-!
# The weakly-reversible cycle cover

The toric-embedding argument of Craciun, _Toric differential inclusions and a proof of
the global attractor conjecture_, assembles the multi-cycle velocity embedding from the
graph fact that a weakly-reversible reaction graph is *covered by directed cycles*: every
reaction `y → y'` lies on a directed cycle, because weak reversibility returns a directed
path from `y'` back to `y`. This module records that cycle-cover at the reachability level,
which the `NetworkCycleDecomposition` of `CRNT.Dynamics.ToricEmbeddingWR` consumes.

## What lands here

* `OnDirectedCycle` — a reaction lies on a directed cycle when its target reaches its
  source (closing `source → target ⇝ source`).
* `WeaklyReversible.onDirectedCycle` — the **core graph lemma**: under weak reversibility
  every reaction lies on a directed cycle.
* `exists_reactionWalk_iff_reaches` — every propositional reachability witness reifies as an
  explicit finite reaction list.
* `WeaklyReversible.reaches_self_through` — the closed-walk statement: the source of every
  reaction reaches itself through that reaction (`source ⇝ source` factoring through
  `target`).
* `WeaklyReversible.reaches_comm` — weak reversibility makes reachability *symmetric*: if
  `c` reaches `d` then `d` reaches `c`, so each connected component of the reaction graph is
  strongly connected. This is the strong-connectivity characterization of weak reversibility
  at the reachability level.

## Scope

Established here: under `WeaklyReversible` every reaction lies on a directed cycle, each
reaction's source reaches itself through it, reachability is symmetric (strong connectivity of
components), and every return path can be represented by a finite reaction list.

Not constructed here: assembling the full `NetworkCycleDecomposition` (the per-cycle reaction
sequences `e`/`u`/`vec` with a correct velocity sum). The `mono`/`cmin` fields of
`NetworkCycleDecomposition` are a separate analytic projection-ordering matter, not graph
theory.

Depends on: `CRNT.Graph.WeakReversibility`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- `N.OnDirectedCycle r` holds when the reaction `r` lies on a directed cycle: its target
reaches its source, so the directed edge `source → target` closes back to a cycle through
`r`. -/
def OnDirectedCycle (N : Network S) (r : N.R) : Prop :=
  N.Reaches (N.reaction r).target (N.reaction r).source

/-- A finite list-coded directed reaction walk from `c` to `d`. The empty list is the
length-zero walk; a nonempty list starts with a reaction whose source is `c`, then continues from
that reaction's target. -/
def ReactionWalk (N : Network S) (c : Complex S) : List N.R → Complex S → Prop
  | [], d => c = d
  | r :: rs, d =>
      (N.reaction r).source = c ∧ N.ReactionWalk (N.reaction r).target rs d

/-- Propositional reaction-graph reachability has an explicit finite-list witness. This converts
the reflexive-transitive closure used by weak reversibility into data suitable for finite cycle
constructions. -/
theorem exists_reactionWalk_iff_reaches (N : Network S) (c d : Complex S) :
    N.Reaches c d ↔ ∃ rs : List N.R, N.ReactionWalk c rs d := by
  constructor
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨[], rfl⟩
    | @head a b hab _ ih =>
        obtain ⟨r, hrs, hrt⟩ := hab
        obtain ⟨rs, hwalk⟩ := ih
        refine ⟨r :: rs, ?_⟩
        change (N.reaction r).source = a ∧
          N.ReactionWalk (N.reaction r).target rs d
        rw [hrs, hrt]
        exact ⟨rfl, hwalk⟩
  · rintro ⟨rs, hwalk⟩
    induction rs generalizing c d with
    | nil =>
        simp only [ReactionWalk] at hwalk
        rw [hwalk]
    | cons r rs ih =>
        simp only [ReactionWalk] at hwalk
        obtain ⟨hsource, htail⟩ := hwalk
        rw [← hsource]
        exact (N.reaches_of_reaction r).trans
          (ih (N.reaction r).target d htail)

/-- **Core graph lemma — weak reversibility covers every reaction by a directed cycle.** Under
`WeaklyReversible`, each reaction `r` lies on a directed cycle: the target reaches the source,
closing the edge `source → target` into a cycle. This is `WeaklyReversible` restated as the
cycle-cover the toric-embedding assembly consumes. -/
theorem WeaklyReversible.onDirectedCycle {N : Network S} (h : N.WeaklyReversible)
    (r : N.R) : N.OnDirectedCycle r :=
  h r

/-- Weak reversibility gives an explicit return reaction list for every reaction. Together with
the reaction itself, this is a finite closed walk based at its source. -/
theorem WeaklyReversible.exists_returnReactionWalk {N : Network S}
    (h : N.WeaklyReversible) (r : N.R) :
    ∃ rs : List N.R,
      N.ReactionWalk (N.reaction r).target rs (N.reaction r).source :=
  (N.exists_reactionWalk_iff_reaches _ _).mp (h r)

/-- The edge followed by its weak-reversibility return list is an explicit closed reaction walk. -/
theorem WeaklyReversible.exists_cycleWalk {N : Network S}
    (h : N.WeaklyReversible) (r : N.R) :
    ∃ rs : List N.R,
      N.ReactionWalk (N.reaction r).source (r :: rs) (N.reaction r).source := by
  obtain ⟨rs, hreturn⟩ := h.exists_returnReactionWalk r
  refine ⟨rs, ?_⟩
  change (N.reaction r).source = (N.reaction r).source ∧
    N.ReactionWalk (N.reaction r).target rs (N.reaction r).source
  exact ⟨rfl, hreturn⟩

/-- The cycle-cover is equivalent to weak reversibility: a network is weakly reversible iff
every reaction lies on a directed cycle. -/
theorem weaklyReversible_iff_onDirectedCycle (N : Network S) :
    N.WeaklyReversible ↔ ∀ r : N.R, N.OnDirectedCycle r :=
  Iff.rfl

/-- **The closed walk through a reaction.** Under weak reversibility, the source of every
reaction reaches itself through that reaction: the edge `source → target` followed by the
return path `target ⇝ source` is a directed closed walk based at `source`. -/
theorem WeaklyReversible.reaches_self_through {N : Network S} (h : N.WeaklyReversible)
    (r : N.R) : N.Reaches (N.reaction r).source (N.reaction r).source :=
  (N.reaches_of_reaction r).trans (h r)

/-- The same closed walk, based at the target: under weak reversibility the target of every
reaction reaches itself through that reaction (`target ⇝ source → target`). -/
theorem WeaklyReversible.reaches_self_through_target {N : Network S} (h : N.WeaklyReversible)
    (r : N.R) : N.Reaches (N.reaction r).target (N.reaction r).target :=
  (h r).trans (N.reaches_of_reaction r)

/-- **Strong connectivity of components.** Weak reversibility makes directed reachability
symmetric: if `c` reaches `d` then `d` reaches `c`. Consequently every connected component of
the reaction graph is strongly connected, the standard graph characterization of weak
reversibility. Proved by induction along the path `c ⇝ d`, returning along each edge by the
weak-reversibility return path. -/
theorem WeaklyReversible.reaches_comm {N : Network S} (h : N.WeaklyReversible)
    {c d : Complex S} (hcd : N.Reaches c d) : N.Reaches d c := by
  induction hcd using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head a b hab _ ih =>
    obtain ⟨r, hrs, hrt⟩ := hab
    -- `a → b` is reaction `r`; the return path `b ⇝ a` is `b ⇝ a` via weak reversibility,
    -- and `d ⇝ b` is `ih`, so `d ⇝ b ⇝ a`.
    have hba : N.Reaches b a := by
      have := h r
      rw [hrs, hrt] at this
      exact this
    exact ih.trans hba

/-- Under weak reversibility, the source and target of every reaction reach each other in both
directions, recovering `WeaklyReversible.reaches_symm` as a consequence of strong
connectivity. -/
theorem WeaklyReversible.reaches_both {N : Network S} (h : N.WeaklyReversible) (r : N.R) :
    N.Reaches (N.reaction r).source (N.reaction r).target ∧
      N.Reaches (N.reaction r).target (N.reaction r).source :=
  ⟨N.reaches_of_reaction r, h r⟩

end Network

end CRNT
