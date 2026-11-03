import CRNT.Multistationarity.TrueSREarCase1
import CRNT.Multistationarity.TrueSRParityRR
import CRNT.Multistationarity.TrueSRPath
import CRNT.Multistationarity.TrueSRSSGlueCPairs

/-!
# Case 2 of Lemma A.6: a species-to-species ear is impossible (Fig. 7(c)–Fig. 8)

Shinar--Feinberg (arXiv:1203.6560, Appendix A.3) rule out, at every stage `Gᵢ` of the directed
ear decomposition of a sign-causality source block, an ear joining two vertices of the stage
cycle.  `TrueSREarCase1.lean` discharges **Case 1** (an ear from a stage species to a stage
reaction).  This file discharges **Case 2**: the ear `Pᵢ` joins two distinct stage species
`S*` (the vertex it leaves) and `S**` (the vertex it enters).

By Lemma A.6's standing hypothesis no stage species is adjacent to more than two stage edges, so
the second ear of Fig. 7(c) — Proposition A.1 supplies a directed ear of the cycle `S**AS*BS**`
inside `Gᵢ` whenever that cycle is not the whole stage — can only close on two stage *reactions*;
call them `R_O` (where it leaves the cycle) and `R_I` (where it re-enters).  The stage then holds
two vertex-disjoint directed ears of one directed cycle:

* `C` : the reaction-to-reaction ear (`R_O → R_I`), and
* `P` : the species-to-species ear (`S_O → S_I`), the ear `Pᵢ` itself.

## The six arrangements, and how this file extracts a pair from each

Cutting the directed cycle at the four attachment vertices leaves four arcs `a₁ a₂ a₃ a₄` in
cyclic order starting from `R_O`.  Anchoring the rotation at `R_O`, the remaining three
attachments (`R_I`, `S_O`, `S_I`) occur in one of `3! = 6` orders — exactly the six drawings of
Fig. 8.  Write `p`, `q` for the two cycle arcs between `R_O` and `R_I` (`p` runs `R_O → R_I`
along the cycle, `q` the complementary way round) and `u`, `v` for the two cycle arcs between
`S_O` and `S_I` (`u` runs `S_O → S_I`, `v` the other way).  Each arc is presented **in its
natural direction from the shared start** — both `p` and `q` start at `R_O`, both `u` and `v`
start at `S_O` — which is what `RRGluable`/`SSGluable` demand; `TrueSRPath.glueCycle` walks its
second argument backwards, so the glued cycle is still a coherent traversal of the union of the
two arcs, and the edge *set* (all that `ContainsEdge`, `isCPair` and `Even` see) never depends
on the presentation order.

For each arrangement one extracts two cycles — one closing `C` along a cycle arc, the other
closing `P` along a cycle arc — and the arrangement is exactly the choice of *which* arcs close
them so that the common-edge subgraph consists of one-R-one-S pieces only:

| # | cyclic order after `R_O` | closed pair | common edges |
|---|---|---|---|
| 1 | `R_I, S_O, S_I` | `C ∪ q`, `P ∪ v` | `arc(R_I,S_O) ∪ arc(S_I,R_O)` |
| 2 | `R_I, S_I, S_O` | `C ∪ q`, `P ∪ u` | `arc(R_I,S_I) ∪ arc(S_O,R_O)` |
| 3 | `S_O, R_I, S_I` | `C ∪ q`, `P ∪ v` | `arc(S_I,R_O)` |
| 4 | `S_O, S_I, R_I` | `C ∪ p`, `P ∪ v` | `arc(R_O,S_O) ∪ arc(S_I,R_I)` |
| 5 | `S_I, R_I, S_O` | `C ∪ q`, `P ∪ v` | `arc(R_I,S_O)` |
| 6 | `S_I, S_O, R_I` | `C ∪ p`, `P ∪ u` | `arc(R_O,S_I) ∪ arc(S_O,R_I)` |

The alternative pairings for arrangements 1, 2, 4 and 6 are genuinely unusable: an exhaustive
enumeration of the simple cycles of `K ∪ C ∪ P` (the cycle, the two ears, and the cycle glued
through both ears) shows every S-to-R pair leaves **two** common components there, and the other
pairings leave an R-to-R, an S-to-S, or an empty common subgraph.  Arrangements 3 and 5 (the two
*alternating* orders) admit a single common component and share one statement,
`lemmaA6_case2_interleaved`, discharged through the single-path consumer
`no_shared_path_of_trueSRCriterion`.  The four two-component arrangements are discharged through
a `componentCount = 2` witness `TrueSRCycle.sToRIntersectionOfTwoPaths` feeding `hSR.2` directly
— `no_shared_path_of_trueSRCriterion` cannot express a disconnected common subgraph by
construction (its `hcov` quantifies over one path).

## Evenness

The directed cycles are even by `TrueSRCycle.even_of_signChange` (Shinar--Feinberg Lemma 5.4),
packaged here as the single hypothesis `C.SignDirected σ`.  The two cycles that are *not*
directed get their evenness from the Appendix A.2 parity lemmas, exactly as the paper says
("each of these cycles is even, either because the cycle is directed or as a consequence of
Lemma A.4 or A.5"):

* `C ∪ p` — `rr_three_glued_even_of_two` on the three reaction-to-reaction paths `C`, `q`, `p`
  (`C ∪ q` and `q ∪ p` are the two directed inputs, `C ∪ p` the output);
* `P ∪ u` — the public S-to-S transfer `ssGlueCycle_even_iff_even` on the three
  species-to-species paths `P`, `u`, `v`, with the parity of `u + v` pulled back from the
  directed cycle `u ∪ v`.  (`ssGlueCycle P Q` and `ssGlueCycle Q P` are two presentations of
  one cycle; the transfer is stated with `P` first, so `Y₁` is built as `ssGlueCycle v P`
  … in fact the statement below keeps `P` first throughout and takes `u ∪ v` as
  `ssGlueCycle u v`; both are fine because `ssGlueCycle_numCPairs` is a symmetric sum.)

## What is hypothesis and what is proved

Proved here, from the ear data: the two extracted cycles (as `rrGluedCycle`/`ssGlueCycle` of the
ear and the chosen arc), their evenness, `hcov` (every common edge of the two cycles lies on one
of the extracted S-to-R component paths), and the `SToRIntersection`/criterion contradiction.

Hypotheses, i.e. obligations of the caller (Prop A.3's ear data plus the stage's arc
decomposition):

* the ears and arcs as paths — `C`, `q` (resp. `p`) are `TrueSRPathRR`s starting at `R_O` and
  ending at `R_I`; `P`, `v` (resp. `u`) are `TrueSRSSPath`s from `S_O` to `S_I`;
  `liftRelPathToTrueSRPathRev`/`arcFwd`-style builders turn the stage cycle's arcs into these;
* `RRGluable`/`SSGluable` of the pairs — complementary arcs of a simple cycle, and the ear
  against each arc;
* freshness — the R-ear shares no edge with the S-ear nor with the closing arc, and the closing
  R-arc shares no edge with the S-ear (they live in the stage cycle, the ears are new edges);
* `harr : q.HasEdge e ∧ v.HasEdge e ↔ c₁.HasEdge e ∨ c₂.HasEdge e` — the *arrangement datum*:
  the two closing arcs meet exactly in the listed component paths.  Discharging it is the
  cut-the-cycle-at-the-four-attachments computation, whose answer per arrangement is the table
  above;
* `hsep` — the two components share no vertex (`components_separated`);
* `SignDirected σ` for each cycle that is closed along the arc whose traversal follows the
  stage-cycle direction (the lemma's title's "directed" cycles).

Note the components are `TrueSRPath`s, so "species at one end, reaction at the other" — the
S-to-R shape of every component — is enforced by the type, not assumed.
-/

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

open TrueSRPath TrueSRSSPath TrueSRPathRR TrueSREdge

/-! ### Edge sets of paths -/

/-- The edge set of a reaction-to-reaction path, as an edge predicate.  The presentation order
of the path never matters to `SameIncidence`-based statements; this is the predicate the
arrangement data below are phrased in. -/
def TrueSRPathRR.HasEdge {j : ℕ} (A : N.TrueSRPathRR j) (e : N.TrueSREdge) : Prop :=
  ∃ k : Fin (2 * j + 2), e.SameIncidence (A.edgeAt k)

/-- The edge set of a species-to-species path, as an edge predicate. -/
def TrueSRSSPath.HasEdge {L : ℕ} (P : N.TrueSRSSPath L) (e : N.TrueSREdge) : Prop :=
  ∃ k : Fin L, e.SameIncidence (P.edge k)

/-- The edge set of a species-to-reaction path, as an edge predicate. -/
def TrueSRPath.HasEdge {L : ℕ} (P : N.TrueSRPath L) (e : N.TrueSREdge) : Prop :=
  ∃ k : Fin L, e.SameIncidence (P.edge k)

/-! ### Directedness under a sign pattern

Shinar--Feinberg Lemma 5.4: a cycle that is a union of causal units has an even number of
c-pairs, because c-pairs are exactly the sign changes of a nonvanishing species sign pattern
around the cycle, and a closed loop has an even number of sign changes.  The repository states
the two clauses as separate hypotheses (`TrueSRCycle.even_of_signChange`, proved in
`TrueSREarCase1.lean`); this file bundles them, since a Case 2 extraction carries up to four
directed cycles.
-/

/-- A sign pattern σ that is nonvanishing on the cycle's species and whose sign changes are
exactly the cycle's c-pairs — the hypothesis under which a *directed* cycle is even. -/
def TrueSRCycle.SignDirected {n : ℕ} (C : N.TrueSRCycle n) (σ : S → ℝ) : Prop :=
  (∀ i, σ (C.species i) ≠ 0) ∧
    (∀ i, C.isCPair i ↔ σ (C.species i) * σ (C.species (finRotate n i)) < 0)

/-- A sign-directed cycle is even (Shinar--Feinberg Lemma 5.4). -/
theorem TrueSRCycle.even_of_signDirected {n : ℕ} (C : N.TrueSRCycle n) {σ : S → ℝ}
    (h : C.SignDirected σ) : C.Even :=
  TrueSRCycle.even_of_signChange C σ h.1 h.2

/-! ### The glued cycles contain exactly their two arcs -/

/-- The cycle `rrGluedCycle X Y` consists of exactly the edges of `X` and of `Y`. -/
theorem TrueSRPathRR.rrGluedCycle_containsEdge_iff {a b : ℕ}
    (X : N.TrueSRPathRR a) (Y : N.TrueSRPathRR b) (h : RRGluable X Y)
    (e : N.TrueSREdge) :
    (rrGluedCycle X Y h).ContainsEdge e ↔ (X.HasEdge e ∨ Y.HasEdge e) := by
  rw [rrGluedCycle_eq, glueCycle_containsEdge_iff]
  constructor
  · rintro (⟨i, hi⟩ | ⟨q, hq⟩)
    · left
      rw [X.tail_edge i] at hi
      exact ⟨⟨i.1 + 1, by omega⟩, hi⟩
    · rcases Nat.eq_zero_or_pos q.1 with h0 | hp
      · left
        rw [glueArc_edge_zero X Y h q (by omega)] at hq
        exact ⟨⟨0, by omega⟩, by rw [X.edgeAt_zero]; exact hq⟩
      · right
        rw [glueArc_edge_pos X Y h q hp] at hq
        exact ⟨⟨q.1 - 1, by omega⟩, hq⟩
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · rcases Nat.eq_zero_or_pos k.1 with h0 | hp
      · right
        have hk0 : k = (⟨0, by omega⟩ : Fin (2 * a + 2)) := Fin.ext h0
        rw [hk0, X.edgeAt_zero] at hk
        exact ⟨⟨0, by omega⟩,
          by rw [glueArc_edge_zero X Y h ⟨0, by omega⟩ (by omega)]; exact hk⟩
      · left
        rw [X.edgeAt_pos k hp] at hk
        exact ⟨⟨k.1 - 1, by omega⟩, hk⟩
    · right
      have hkb : k.1 < 2 * b + 2 := k.isLt
      have hwit : k.1 + 1 < 2 * (b + 1) + 1 := by omega
      have hpos : 0 < k.1 + 1 := by omega
      refine ⟨⟨k.1 + 1, hwit⟩, ?_⟩
      rw [glueArc_edge_pos X Y h ⟨k.1 + 1, hwit⟩ hpos]
      exact hk

/-- The cycle `ssGlueCycle P Q` consists of exactly the edges of `P` and of `Q`.  (The same
statement exists as a `private` lemma of `TrueChemistrySRCriterion.lean`; it is re-proved here
so that this file does not import that module.) -/
theorem TrueSRSSPath.ssGlueCycle_containsEdge_iff {i j : ℕ}
    (P : N.TrueSRSSPath (2 * j + 2)) (Q : N.TrueSRSSPath (2 * i + 2))
    (h : SSGluable P Q) (e : N.TrueSREdge) :
    (ssGlueCycle P Q h).ContainsEdge e ↔ (P.HasEdge e ∨ Q.HasEdge e) := by
  rw [ssGlueCycle_eq, glueCycle_containsEdge_iff]
  constructor
  · rintro (⟨p, hp⟩ | ⟨q, hq⟩)
    · left
      exact ⟨⟨p.1, by have := p.isLt; have := P.two_le_length; omega⟩, by
        simpa [TrueSRSSPath.toPath_edge] using hp⟩
    · rw [TrueSRSSPath.partner] at hq
      by_cases hlt : q.1 < 2 * i + 2
      · right
        rw [TrueSRSSPath.extend_edge_lt Q P.lastEdge (TrueSRSSPath.extend_hes P Q h)
          (TrueSRSSPath.extend_hnew P Q h) (TrueSRSSPath.extend_hedge P Q h) q hlt] at hq
        exact ⟨⟨q.1, by omega⟩, hq⟩
      · left
        rw [TrueSRSSPath.extend_edge_last Q P.lastEdge (TrueSRSSPath.extend_hes P Q h)
          (TrueSRSSPath.extend_hnew P Q h) (TrueSRSSPath.extend_hedge P Q h) q hlt] at hq
        rw [TrueSRSSPath.lastEdge] at hq
        exact ⟨⟨(2 * j + 2) - 1, by omega⟩, hq⟩
  · rintro (⟨p, hp⟩ | ⟨q, hq⟩)
    · by_cases hlt : p.1 < 2 * j + 1
      · left
        exact ⟨⟨p.1, by omega⟩, by
          simpa [TrueSRSSPath.toPath_edge] using hp⟩
      · right
        have hlast : p.1 = 2 * j + 1 := by
          have := p.isLt
          omega
        refine ⟨⟨2 * i + 2, by omega⟩, ?_⟩
        let r : Fin (2 * i + 2 + 1) := Fin.last (2 * i + 2)
        have hr : r = (⟨2 * i + 2, by omega⟩ : Fin (2 * i + 2 + 1)) := by
          apply Fin.ext
          rfl
        rw [← hr]
        rw [TrueSRSSPath.partner,
          TrueSRSSPath.extend_edge_last Q P.lastEdge (TrueSRSSPath.extend_hes P Q h)
            (TrueSRSSPath.extend_hnew P Q h) (TrueSRSSPath.extend_hedge P Q h) r (by simp [r]),
          TrueSRSSPath.lastEdge]
        have hlastEdge : p = (⟨2 * j + 1, by omega⟩ : Fin (2 * j + 2)) := Fin.ext hlast
        rw [hlastEdge] at hp
        simpa using hp
    · right
      have hqL : q.1 < 2 * i + 2 := q.isLt
      rw [TrueSRSSPath.partner]
      refine ⟨⟨q.1, Nat.lt_succ_of_lt hqL⟩, ?_⟩
      rw [TrueSRSSPath.extend_edge_lt Q P.lastEdge (TrueSRSSPath.extend_hes P Q h)
        (TrueSRSSPath.extend_hnew P Q h) (TrueSRSSPath.extend_hedge P Q h)
        ⟨q.1, Nat.lt_succ_of_lt hqL⟩ hqL]
      exact hq

/-! ### A two-component S-to-R intersection certificate

`TrueSRSingleSharedEdge.sToRIntersectionOfPath` builds the `componentCount = 1` witness from a
single common S-to-R path.  Four of the six arrangements of Fig. 8 leave *two* common
components, and `TrueSRCycle.SToRIntersection` allows a disconnected common subgraph as long as
every component is a simple S-to-R path, the components are pairwise vertex-separated, and all
common edges are covered.  This is that builder for two components.
-/

/-- Two common S-to-R paths, vertex-separated from each other and together covering every
common edge, witness `C.SToRIntersection D`. -/
noncomputable def TrueSRCycle.sToRIntersectionOfTwoPaths {m n L₁ L₂ : ℕ}
    (C : N.TrueSRCycle m) (D : N.TrueSRCycle n)
    (c₁ : N.TrueSRPath L₁) (c₂ : N.TrueSRPath L₂)
    (h₁C : ∀ i, C.ContainsEdge (c₁.edge i)) (h₁D : ∀ i, D.ContainsEdge (c₁.edge i))
    (h₂C : ∀ i, C.ContainsEdge (c₂.edge i)) (h₂D : ∀ i, D.ContainsEdge (c₂.edge i))
    (hcov : ∀ f : N.TrueSREdge, C.ContainsEdge f → D.ContainsEdge f →
      c₁.HasEdge f ∨ c₂.HasEdge f)
    (hsep : ∀ i j, ¬ (c₁.edge i).ShareVertex (c₂.edge j)) :
    C.SToRIntersection D := by
  let len : Fin 2 → ℕ := fun c => if c = 0 then L₁ else L₂
  have hlen0 : len 0 = L₁ := rfl
  have hlen1 : len 1 = L₂ := rfl
  let edg : ∀ c : Fin 2, Fin (len c) → N.TrueSREdge := fun c i =>
    if h : c = 0 then c₁.edge ⟨i.1, by
        have hi : i.1 < (if c = 0 then L₁ else L₂) := i.isLt
        rw [if_pos h] at hi
        exact hi⟩
    else c₂.edge ⟨i.1, by
        have hi : i.1 < (if c = 0 then L₁ else L₂) := i.isLt
        rw [if_neg h] at hi
        exact hi⟩
  let vtx : ∀ c : Fin 2, Fin (len c + 1) → N.TrueSRVertex := fun c i =>
    if h : c = 0 then c₁.vertex ⟨i.1, by
        have hi : i.1 < (if c = 0 then L₁ else L₂) + 1 := i.isLt
        rw [if_pos h] at hi
        exact hi⟩
    else c₂.vertex ⟨i.1, by
        have hi : i.1 < (if c = 0 then L₁ else L₂) + 1 := i.isLt
        rw [if_neg h] at hi
        exact hi⟩
  have hcases : ∀ c : Fin 2, c.1 = 0 ∨ c.1 = 1 := by
    intro c
    have := c.isLt
    omega
  refine
    { componentCount := 2
      componentCount_pos := Nat.zero_lt_two
      componentLength := len
      componentLength_pos := ?_
      edge := edg
      vertex := vtx
      edge_on_C := ?_
      edge_on_D := ?_
      connects := ?_
      edge_simple := ?_
      vertex_simple := ?_
      starts_at_species := ?_
      ends_at_reaction := ?_
      covers_common := ?_
      components_separated := ?_ }
  · -- component lengths are positive
    intro c
    rcases hcases c with h | h
    · have hc : c = 0 := Fin.ext h
      subst hc
      exact c₁.length_pos
    · have hc : c = 1 := Fin.ext h
      subst hc
      exact c₂.length_pos
  · -- every listed edge lies on `C`
    intro c
    rcases hcases c with h | h
    · have hc : c = 0 := Fin.ext h
      subst hc
      intro i
      exact h₁C i
    · have hc : c = 1 := Fin.ext h
      subst hc
      intro i
      exact h₂C i
  · -- every listed edge lies on `D`
    intro c
    rcases hcases c with h | h
    · have hc : c = 0 := Fin.ext h
      subst hc
      intro i
      exact h₁D i
    · have hc : c = 1 := Fin.ext h
      subst hc
      intro i
      exact h₂D i
  · -- consecutive vertices are joined by the corresponding edge
    intro c
    rcases hcases c with h | h
    · have hc : c = 0 := Fin.ext h
      subst hc
      intro i
      exact c₁.connects i
    · have hc : c = 1 := Fin.ext h
      subst hc
      intro i
      exact c₂.connects i
  · -- edges within a component are pairwise distinct
    intro c
    rcases hcases c with h | h
    · have hc : c = 0 := Fin.ext h
      subst hc
      intro i j hij
      exact c₁.edge_simple hij
    · have hc : c = 1 := Fin.ext h
      subst hc
      intro i j hij
      exact c₂.edge_simple hij
  · -- vertices within a component are pairwise distinct
    intro c
    rcases hcases c with h | h
    · have hc : c = 0 := Fin.ext h
      subst hc
      intro a b hab
      exact c₁.vertex_simple hab
    · have hc : c = 1 := Fin.ext h
      subst hc
      intro a b hab
      exact c₂.vertex_simple hab
  · -- each component starts at a species
    intro c
    rcases hcases c with h | h
    · have hc : c = 0 := Fin.ext h
      subst hc
      exact c₁.starts_at_species
    · have hc : c = 1 := Fin.ext h
      subst hc
      exact c₂.starts_at_species
  · -- each component ends at a reaction
    intro c
    rcases hcases c with h | h
    · have hc : c = 0 := Fin.ext h
      subst hc
      exact c₁.ends_at_reaction
    · have hc : c = 1 := Fin.ext h
      subst hc
      exact c₂.ends_at_reaction
  · -- the two components cover every common edge
    intro f hfC hfD
    rcases hcov f hfC hfD with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact ⟨0, i, hi⟩
    · exact ⟨1, i, hi⟩
  · -- the two components share no vertex
    intro c d hcd
    rcases hcases c with h | h
    · have hc : c = 0 := Fin.ext h
      subst hc
      rcases hcases d with h' | h'
      · have hd : d = 0 := Fin.ext h'
        subst hd
        intro i j
        exact absurd rfl hcd
      · have hd : d = 1 := Fin.ext h'
        subst hd
        intro i j
        exact hsep i j
    · have hc : c = 1 := Fin.ext h
      subst hc
      rcases hcases d with h' | h'
      · have hd : d = 0 := Fin.ext h'
        subst hd
        intro i j hv
        apply hsep j i
        rcases hv with hv | hv
        · exact Or.inl hv.symm
        · exact Or.inr hv.symm
      · have hd : d = 1 := Fin.ext h'
        subst hd
        intro i j
        exact absurd rfl hcd

/-! ### The criterion discharge

Both core theorems below take the two extracted cycles, their evenness, the *decomposition* of
each cycle into "the ear plus the closing arc" (as edge predicates `CE`/`QE` for `X = C ∪ q`,
`PE`/`VE` for `Y = P ∪ v`), the freshness of the ears against each other and against the
closing arc, and the arrangement datum `harr` (the two closing arcs meet exactly in the listed
S-to-R component paths).  From these they derive `hcov` and contradict `hSR`.
-/

/-- **Core of Lemma A.6 Case 2, two-component form.**  See `lemmaA6_case2_oneComponent` for
the single-component variant. -/
theorem lemmaA6_case2_twoComponents (N : Network S) (hSR : N.TrueSRStrongCriterion)
    {m n L₁ L₂ : ℕ} (X : N.TrueSRCycle m) (Y : N.TrueSRCycle n)
    (c₁ : N.TrueSRPath L₁) (c₂ : N.TrueSRPath L₂)
    (CE QE PE VE : N.TrueSREdge → Prop)
    (hXE : X.Even) (hYE : Y.Even)
    (hdecX : ∀ e, X.ContainsEdge e ↔ (CE e ∨ QE e))
    (hdecY : ∀ e, Y.ContainsEdge e ↔ (PE e ∨ VE e))
    (hCP : ∀ e, ¬ (CE e ∧ PE e))
    (hCV : ∀ e, ¬ (CE e ∧ VE e))
    (hQP : ∀ e, ¬ (QE e ∧ PE e))
    (harr : ∀ e, QE e ∧ VE e ↔ (c₁.HasEdge e ∨ c₂.HasEdge e))
    (hsep : ∀ i j, ¬ (c₁.edge i).ShareVertex (c₂.edge j)) :
    False := by
  have hcov : ∀ f, X.ContainsEdge f → Y.ContainsEdge f →
      (c₁.HasEdge f ∨ c₂.HasEdge f) := by
    intro f hfX hfY
    rcases (hdecX f).1 hfX with hCE | hQE
    · rcases (hdecY f).1 hfY with hPE | hVE
      · exact absurd ⟨hCE, hPE⟩ (hCP f)
      · exact absurd ⟨hCE, hVE⟩ (hCV f)
    · rcases (hdecY f).1 hfY with hPE | hVE
      · exact absurd ⟨hQE, hPE⟩ (hQP f)
      · exact (harr f).1 ⟨hQE, hVE⟩
  refine hSR.2 X Y hXE hYE ⟨?_⟩
  exact TrueSRCycle.sToRIntersectionOfTwoPaths X Y c₁ c₂
    (fun i => (hdecX (c₁.edge i)).2 (Or.inr ((harr (c₁.edge i)).2
      (Or.inl ⟨i, TrueSREdge.SameIncidence.refl _⟩)).1))
    (fun i => (hdecY (c₁.edge i)).2 (Or.inr ((harr (c₁.edge i)).2
      (Or.inl ⟨i, TrueSREdge.SameIncidence.refl _⟩)).2))
    (fun i => (hdecX (c₂.edge i)).2 (Or.inr ((harr (c₂.edge i)).2
      (Or.inr ⟨i, TrueSREdge.SameIncidence.refl _⟩)).1))
    (fun i => (hdecY (c₂.edge i)).2 (Or.inr ((harr (c₂.edge i)).2
      (Or.inr ⟨i, TrueSREdge.SameIncidence.refl _⟩)).2))
    hcov hsep

/-- **Core of Lemma A.6 Case 2, single-component form.**  The variant used when the two
closing arcs meet in one S-to-R path (the alternating orders of Fig. 8), discharged through
`no_shared_path_of_trueSRCriterion`. -/
theorem lemmaA6_case2_oneComponent (N : Network S) (hSR : N.TrueSRStrongCriterion)
    {m n L : ℕ} (X : N.TrueSRCycle m) (Y : N.TrueSRCycle n) (c₁ : N.TrueSRPath L)
    (CE QE PE VE : N.TrueSREdge → Prop)
    (hXE : X.Even) (hYE : Y.Even)
    (hdecX : ∀ e, X.ContainsEdge e ↔ (CE e ∨ QE e))
    (hdecY : ∀ e, Y.ContainsEdge e ↔ (PE e ∨ VE e))
    (hCP : ∀ e, ¬ (CE e ∧ PE e))
    (hCV : ∀ e, ¬ (CE e ∧ VE e))
    (hQP : ∀ e, ¬ (QE e ∧ PE e))
    (harr : ∀ e, QE e ∧ VE e ↔ c₁.HasEdge e) :
    False := by
  have hcov : ∀ f, X.ContainsEdge f → Y.ContainsEdge f →
      ∃ i, f.SameIncidence (c₁.edge i) := by
    intro f hfX hfY
    rcases (hdecX f).1 hfX with hCE | hQE
    · rcases (hdecY f).1 hfY with hPE | hVE
      · exact absurd ⟨hCE, hPE⟩ (hCP f)
      · exact absurd ⟨hCE, hVE⟩ (hCV f)
    · rcases (hdecY f).1 hfY with hPE | hVE
      · exact absurd ⟨hQE, hPE⟩ (hQP f)
      · exact (harr f).1 ⟨hQE, hVE⟩
  exact no_shared_path_of_trueSRCriterion N hSR X Y hXE hYE c₁
    (fun i => (hdecX (c₁.edge i)).2 (Or.inr ((harr (c₁.edge i)).2
      (⟨i, TrueSREdge.SameIncidence.refl _⟩ : c₁.HasEdge (c₁.edge i))).1))
    (fun i => (hdecY (c₁.edge i)).2 (Or.inr ((harr (c₁.edge i)).2
      (⟨i, TrueSREdge.SameIncidence.refl _⟩ : c₁.HasEdge (c₁.edge i))).2))
    hcov

/-- Freshness of a reaction-to-reaction path against a species-to-species path, transported to
the edge-predicate form the cores use. -/
theorem fresh_rr_ss {j L : ℕ} (A : N.TrueSRPathRR j) (B : N.TrueSRSSPath L)
    (h : ∀ k l, ¬ (A.edgeAt k).SameIncidence (B.edge l)) :
    ∀ e, ¬ (A.HasEdge e ∧ B.HasEdge e) := by
  rintro e ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
  exact h k l (TrueSREdge.SameIncidence.trans (TrueSREdge.SameIncidence.symm hk) hl)

/-- **The S-to-S parity transfer** (Shinar--Feinberg Lemma A.5): if the cycles `P ∪ v` and
`u ∪ v` are even, so is `P ∪ u`.  `u ∪ v` and `P ∪ v` being directed cycles supplies the two
inputs; `ssGlueCycle_even_iff_even` compares the c-pair counts of the three glues. -/
theorem ssGlueCycle_even_of_partner {i j k : ℕ}
    (P : N.TrueSRSSPath (2 * j + 2)) (u : N.TrueSRSSPath (2 * i + 2))
    (v : N.TrueSRSSPath (2 * k + 2))
    (hPu : SSGluable P u) (hPv : SSGluable P v) (huv : SSGluable u v)
    (hK : (ssGlueCycle u v huv).Even) (hY : (ssGlueCycle P v hPv).Even) :
    (ssGlueCycle P u hPu).Even := by
  have hsum : Even (ssNumCPairs u + ssNumCPairs v) := by
    rw [← ssGlueCycle_numCPairs u v huv]
    exact hK
  have hmod : (ssNumCPairs u + ssNumCPairs v) % 2 = 0 := Nat.even_iff.mp hsum
  exact (ssGlueCycle_even_iff_even P u v hPu hPv hmod).mpr hY

/-! ### The six arrangements of Fig. 8

Six drawings collapse to five statement shapes: the two alternating orders (Fig. 8, orders
`R_O S_O R_I S_I` and `R_O S_I R_I S_O`) admit the *same* pair `C ∪ q`, `P ∪ v` with a single
S-to-R common component, so one theorem covers both.  In every statement the caller supplies
the stage's arcs as paths presented from their shared start, the gluing/freshness data, the
arrangement identity `harr`, component separation, and `SignDirected σ` for each cycle that is
closed along an arc whose traversal follows the stage-cycle direction.
-/

/-- **Fig. 8, cyclic order `R_O, R_I, S_O, S_I`.**  Extract `X = C ∪ q` and `Y = P ∪ v`; their
common edges are `arc(R_I,S_O) ∪ arc(S_I,R_O)`, both one-R-one-S.  Both cycles are directed. -/
theorem lemmaA6_case2_arrangement1 (N : Network S) (hSR : N.TrueSRStrongCriterion)
    {a b c d L₁ L₂ : ℕ} (σ : S → ℝ)
    (C : N.TrueSRPathRR a) (q : N.TrueSRPathRR b)
    (P : N.TrueSRSSPath (2 * c + 2)) (v : N.TrueSRSSPath (2 * d + 2))
    (c₁ : N.TrueSRPath L₁) (c₂ : N.TrueSRPath L₂)
    (hCq : RRGluable C q) (hPv : SSGluable P v)
    (harr : ∀ e : N.TrueSREdge, q.HasEdge e ∧ v.HasEdge e ↔
      (c₁.HasEdge e ∨ c₂.HasEdge e))
    (hCP : ∀ k l, ¬ (C.edgeAt k).SameIncidence (P.edge l))
    (hCv : ∀ k l, ¬ (C.edgeAt k).SameIncidence (v.edge l))
    (hqP : ∀ k l, ¬ (q.edgeAt k).SameIncidence (P.edge l))
    (hsep : ∀ i j, ¬ (c₁.edge i).ShareVertex (c₂.edge j))
    (hX : (rrGluedCycle C q hCq).SignDirected σ)
    (hY : (ssGlueCycle P v hPv).SignDirected σ) :
    False :=
  lemmaA6_case2_twoComponents N hSR (rrGluedCycle C q hCq) (ssGlueCycle P v hPv) c₁ c₂
    C.HasEdge q.HasEdge P.HasEdge v.HasEdge
    (TrueSRCycle.even_of_signDirected _ hX) (TrueSRCycle.even_of_signDirected _ hY)
    (rrGluedCycle_containsEdge_iff C q hCq) (ssGlueCycle_containsEdge_iff P v hPv)
    (fresh_rr_ss C P hCP) (fresh_rr_ss C v hCv) (fresh_rr_ss q P hqP)
    harr hsep

/-- **Fig. 8, cyclic order `R_O, R_I, S_I, S_O`.**  Extract `X = C ∪ q` and `Y = P ∪ u`;
their common edges are `arc(R_I,S_I) ∪ arc(S_O,R_O)`, both one-R-one-S.  `X` is directed;
`Y` is even by the Lemma A.5 transfer from the directed cycles `P ∪ v` and `u ∪ v`. -/
theorem lemmaA6_case2_arrangement2 (N : Network S) (hSR : N.TrueSRStrongCriterion)
    {a b c d e L₁ L₂ : ℕ} (σ : S → ℝ)
    (C : N.TrueSRPathRR a) (q : N.TrueSRPathRR b)
    (P : N.TrueSRSSPath (2 * c + 2)) (u : N.TrueSRSSPath (2 * d + 2))
    (v : N.TrueSRSSPath (2 * e + 2))
    (c₁ : N.TrueSRPath L₁) (c₂ : N.TrueSRPath L₂)
    (hCq : RRGluable C q) (hPu : SSGluable P u) (hPv : SSGluable P v)
    (huv : SSGluable u v)
    (harr : ∀ f : N.TrueSREdge, q.HasEdge f ∧ u.HasEdge f ↔
      (c₁.HasEdge f ∨ c₂.HasEdge f))
    (hCP : ∀ k l, ¬ (C.edgeAt k).SameIncidence (P.edge l))
    (hCu : ∀ k l, ¬ (C.edgeAt k).SameIncidence (u.edge l))
    (hqP : ∀ k l, ¬ (q.edgeAt k).SameIncidence (P.edge l))
    (hsep : ∀ i j, ¬ (c₁.edge i).ShareVertex (c₂.edge j))
    (hX : (rrGluedCycle C q hCq).SignDirected σ)
    (hY : (ssGlueCycle P v hPv).SignDirected σ)
    (hK : (ssGlueCycle u v huv).SignDirected σ) :
    False := by
  have hY1 := TrueSRCycle.even_of_signDirected _ hY
  have hKs := TrueSRCycle.even_of_signDirected _ hK
  exact lemmaA6_case2_twoComponents N hSR (rrGluedCycle C q hCq)
    (ssGlueCycle P u hPu) c₁ c₂
    C.HasEdge q.HasEdge P.HasEdge u.HasEdge
    (TrueSRCycle.even_of_signDirected _ hX)
    (ssGlueCycle_even_of_partner P u v hPu hPv huv hKs hY1)
    (rrGluedCycle_containsEdge_iff C q hCq) (ssGlueCycle_containsEdge_iff P u hPu)
    (fresh_rr_ss C P hCP) (fresh_rr_ss C u hCu) (fresh_rr_ss q P hqP)
    harr hsep

/-- **Fig. 8, the two alternating orders `R_O, S_O, R_I, S_I` and `R_O, S_I, R_I, S_O`**
(Fig. 8's interleaved drawings).  Both admit the pair `X = C ∪ q`, `Y = P ∪ v` with a
*single* S-to-R common component (`arc(S_I,R_O)` in the first order, `arc(R_I,S_O)` in the
second), discharged through `no_shared_path_of_trueSRCriterion`.  Both cycles are directed. -/
theorem lemmaA6_case2_interleaved (N : Network S) (hSR : N.TrueSRStrongCriterion)
    {a b c d L : ℕ} (σ : S → ℝ)
    (C : N.TrueSRPathRR a) (q : N.TrueSRPathRR b)
    (P : N.TrueSRSSPath (2 * c + 2)) (v : N.TrueSRSSPath (2 * d + 2))
    (c₁ : N.TrueSRPath L)
    (hCq : RRGluable C q) (hPv : SSGluable P v)
    (harr : ∀ e : N.TrueSREdge, q.HasEdge e ∧ v.HasEdge e ↔ c₁.HasEdge e)
    (hCP : ∀ k l, ¬ (C.edgeAt k).SameIncidence (P.edge l))
    (hCv : ∀ k l, ¬ (C.edgeAt k).SameIncidence (v.edge l))
    (hqP : ∀ k l, ¬ (q.edgeAt k).SameIncidence (P.edge l))
    (hX : (rrGluedCycle C q hCq).SignDirected σ)
    (hY : (ssGlueCycle P v hPv).SignDirected σ) :
    False :=
  lemmaA6_case2_oneComponent N hSR (rrGluedCycle C q hCq) (ssGlueCycle P v hPv) c₁
    C.HasEdge q.HasEdge P.HasEdge v.HasEdge
    (TrueSRCycle.even_of_signDirected _ hX) (TrueSRCycle.even_of_signDirected _ hY)
    (rrGluedCycle_containsEdge_iff C q hCq) (ssGlueCycle_containsEdge_iff P v hPv)
    (fresh_rr_ss C P hCP) (fresh_rr_ss C v hCv) (fresh_rr_ss q P hqP)
    harr

/-- **Fig. 8, cyclic order `R_O, S_O, S_I, R_I`.**  Extract `X = C ∪ p` and `Y = P ∪ v`;
their common edges are `arc(R_O,S_O) ∪ arc(S_I,R_I)`, both one-R-one-S.  `Y` is directed;
`X` is even by Lemma A.4 (`rr_three_glued_even_of_two`) from the directed cycles `C ∪ q`
and `q ∪ p`. -/
theorem lemmaA6_case2_arrangement4 (N : Network S) (hSR : N.TrueSRStrongCriterion)
    {a b cq d L₁ L₂ : ℕ} (σ : S → ℝ)
    (C : N.TrueSRPathRR a) (p : N.TrueSRPathRR b) (q : N.TrueSRPathRR cq)
    (P : N.TrueSRSSPath (2 * c + 2)) (v : N.TrueSRSSPath (2 * d + 2))
    (c₁ : N.TrueSRPath L₁) (c₂ : N.TrueSRPath L₂)
    (hCq : RRGluable C q) (hCp : RRGluable C p) (hqp : RRGluable q p)
    (hPv : SSGluable P v)
    (harr : ∀ f : N.TrueSREdge, p.HasEdge f ∧ v.HasEdge f ↔
      (c₁.HasEdge f ∨ c₂.HasEdge f))
    (hCP : ∀ k l, ¬ (C.edgeAt k).SameIncidence (P.edge l))
    (hCv : ∀ k l, ¬ (C.edgeAt k).SameIncidence (v.edge l))
    (hpP : ∀ k l, ¬ (p.edgeAt k).SameIncidence (P.edge l))
    (hsep : ∀ i j, ¬ (c₁.edge i).ShareVertex (c₂.edge j))
    (hX1 : (rrGluedCycle C q hCq).SignDirected σ)
    (hK : (rrGluedCycle q p hqp).SignDirected σ)
    (hY : (ssGlueCycle P v hPv).SignDirected σ) :
    False := by
  have hX2 := rr_three_glued_even_of_two C q p hCq hCp hqp
    (TrueSRCycle.even_of_signDirected _ hX1)
    (TrueSRCycle.even_of_signDirected _ hK)
  exact lemmaA6_case2_twoComponents N hSR (rrGluedCycle C p hCp)
    (ssGlueCycle P v hPv) c₁ c₂
    C.HasEdge p.HasEdge P.HasEdge v.HasEdge
    hX2 (TrueSRCycle.even_of_signDirected _ hY)
    (rrGluedCycle_containsEdge_iff C p hCp) (ssGlueCycle_containsEdge_iff P v hPv)
    (fresh_rr_ss C P hCP) (fresh_rr_ss C v hCv) (fresh_rr_ss p P hpP)
    harr hsep

/-- **Fig. 8, cyclic order `R_O, S_I, S_O, R_I`.**  Extract `X = C ∪ p` and `Y = P ∪ u`;
their common edges are `arc(R_O,S_I) ∪ arc(S_O,R_I)`, both one-R-one-S.  `X` is even by
Lemma A.4 and `Y` by Lemma A.5, both from the directed cycles `C ∪ q`, `q ∪ p`, `P ∪ v`,
`u ∪ v`. -/
theorem lemmaA6_case2_arrangement6 (N : Network S) (hSR : N.TrueSRStrongCriterion)
    {a b cq d e L₁ L₂ : ℕ} (σ : S → ℝ)
    (C : N.TrueSRPathRR a) (p : N.TrueSRPathRR b) (q : N.TrueSRPathRR cq)
    (P : N.TrueSRSSPath (2 * c + 2)) (u : N.TrueSRSSPath (2 * d + 2))
    (v : N.TrueSRSSPath (2 * e + 2))
    (c₁ : N.TrueSRPath L₁) (c₂ : N.TrueSRPath L₂)
    (hCq : RRGluable C q) (hCp : RRGluable C p) (hqp : RRGluable q p)
    (hPu : SSGluable P u) (hPv : SSGluable P v) (huv : SSGluable u v)
    (harr : ∀ f : N.TrueSREdge, p.HasEdge f ∧ u.HasEdge f ↔
      (c₁.HasEdge f ∨ c₂.HasEdge f))
    (hCP : ∀ k l, ¬ (C.edgeAt k).SameIncidence (P.edge l))
    (hCu : ∀ k l, ¬ (C.edgeAt k).SameIncidence (u.edge l))
    (hpP : ∀ k l, ¬ (p.edgeAt k).SameIncidence (P.edge l))
    (hsep : ∀ i j, ¬ (c₁.edge i).ShareVertex (c₂.edge j))
    (hX1 : (rrGluedCycle C q hCq).SignDirected σ)
    (hKrr : (rrGluedCycle q p hqp).SignDirected σ)
    (hY1 : (ssGlueCycle P v hPv).SignDirected σ)
    (hKss : (ssGlueCycle u v huv).SignDirected σ) :
    False := by
  have hX2 := rr_three_glued_even_of_two C q p hCq hCp hqp
    (TrueSRCycle.even_of_signDirected _ hX1)
    (TrueSRCycle.even_of_signDirected _ hKrr)
  have hY2 := ssGlueCycle_even_of_partner P u v hPu hPv huv
    (TrueSRCycle.even_of_signDirected _ hKss)
    (TrueSRCycle.even_of_signDirected _ hY1)
  exact lemmaA6_case2_twoComponents N hSR (rrGluedCycle C p hCp)
    (ssGlueCycle P u hPu) c₁ c₂
    C.HasEdge p.HasEdge P.HasEdge u.HasEdge
    hX2 hY2
    (rrGluedCycle_containsEdge_iff C p hCp) (ssGlueCycle_containsEdge_iff P u hPu)
    (fresh_rr_ss C P hCP) (fresh_rr_ss C u hCu) (fresh_rr_ss p P hpP)
    harr hsep

end CRNT.Network
