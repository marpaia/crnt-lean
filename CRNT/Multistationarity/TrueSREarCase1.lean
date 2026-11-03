import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Analysis.Normed.Group.Real
import CRNT.Multistationarity.TrueSRTwoGluedCycles

/-!
# Case 1 of Lemma A.6: a fresh species-to-reaction ear is impossible

Shinar--Feinberg (arXiv:1203.6560, Appendix A.3, Lemma A.6) rule out, at every stage `Gᵢ` of the
directed ear decomposition of a sign-causality source block, an ear joining a species vertex of
`Gᵢ` to a reaction vertex of `Gᵢ`.  This file formalises **Case 1**, where the ear `Pᵢ` runs from
the stage species `s*` to the stage reaction `ρ*` (the opposite orientation is the symmetric
instance).  Because the stage is strongly connected it carries a path `A` from `s*` to `ρ*` and a
path `B` from `ρ*` back to `s*`.  Then

* `A`·`B` (stage cycle) and `Pᵢ`·`B` (ear cycle) are both directed, hence **even**, and
* their common edges are exactly the edges of `B` — a species-to-reaction path —

so `CRNT.no_shared_path_of_trueSRCriterion` (condition (ii) of Theorem 2.1) yields `False`.

## Formal shape

* All three paths are `TrueSRPath`s.  A `TrueSRPath` always runs from a species to a reaction, so
  the return path `B` (which runs `ρ* → s*` in the paper) is supplied **reversed**: its
  species-to-reaction reading is exactly the orientation the consumer wants.  Consequently the
  glue traversal `glueCycle A B` — walk `A` forward from `s*` to `ρ*`, then `B` backwards from
  `ρ*` to `s*` — is the paper's cycle `A`·`B`, and `glueCycle E B` is the ear followed by `B`.
  No path-reversal combinator is needed: the reversal is baked into how `B` is supplied.
* Freshness of the ear against the stage is stated over a stage vertex set `T : Finset
  N.TrueSRVertex`: every vertex of `A` lies in `T`, while no ear edge has both of its endpoints
  in `T` (in the bipartite sign-causality graph every ear edge touches an interior ear vertex,
  and the interior lies outside `T`).  From these two facts the proof derives that **no ear edge
  is an `A`-edge**, which is precisely what collapses the two cycles' common edge set to `B`.
* "Directed, hence even" is Shinar--Feinberg Lemma 5.4: a cycle that is a union of causal units
  has an even number of c-pairs, because c-pairs are exactly the species-sign changes around the
  cycle and an even number of sign changes occurs around a closed loop.  The repository's copy
  of that fact (`trueSRCycle_even_of_signChange`) is `private` to `TrueChemistrySRCriterion`, so
  `TrueSRCycle.even_of_signChange` re-proves it here.
* `Gluable A B` packages that the two stage paths share their two endpoints and have disjoint
  interiors and edge sets — the vertex-disjoint configuration of the paper's Figure 6(a); the
  overlapping case of Figure 6(b) reduces to it by trimming `A` and `B` to their first common
  interior vertex, which is a graph-level operation outside this statement.  `Gluable E B`
  packages the analogous facts for the ear and `B`.
-/

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S]

open TrueSRPath TrueSREdge

/-! ### Directed cycles are even

The next three lemmas are re-proved here (they exist only as `private` declarations of
`TrueChemistrySRCriterion.lean`, which this file does not import): a product of ±1-values is
`(-1)` to the number of factors equal to `-1`; hence an even number of `-1` factors when the
product is `1`; hence an even number of sign changes of a nonvanishing sequence around a cycle.
-/

private theorem prod_pm_one_eq_neg_one_pow_card_neg
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ)
    (hpm : ∀ i ∈ s, f i = 1 ∨ f i = -1) :
    ∏ i ∈ s, f i = (-1 : ℝ) ^ (s.filter (fun i => f i = -1)).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hfa := hpm a (by simp)
      have hs : ∀ i ∈ s, f i = 1 ∨ f i = -1 := fun i hi => hpm i (by simp [hi])
      rw [ih hs]
      rcases hfa with h1 | hn
      · norm_num [Finset.filter_insert, h1]
      · simp [Finset.filter_insert, hn, ha, pow_succ, mul_comm]

private theorem even_card_neg_of_prod_one
    {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (hpm : ∀ i, f i = 1 ∨ f i = -1)
    (hprod : ∏ i, f i = 1) :
    Even ((Finset.univ.filter (fun i => f i = -1)).card) := by
  classical
  have h := prod_pm_one_eq_neg_one_pow_card_neg Finset.univ f (by simpa using hpm)
  rw [hprod] at h
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)).mp h.symm

private theorem cyclic_sign_changes_even {n : ℕ} [NeZero n] (a : Fin n → ℝ)
    (hne : ∀ i, a i ≠ 0) :
    Even ((Finset.univ.filter (fun i => a i * a (finRotate n i) < 0)).card) := by
  classical
  let g : Fin n → ℝ := fun i => if 0 < a i then 1 else -1
  let f : Fin n → ℝ := fun i => g i * g (finRotate n i)
  have hg : ∀ i, g i = 1 ∨ g i = -1 := by
    intro i
    simp only [g]
    split <;> simp
  have hf : ∀ i, f i = 1 ∨ f i = -1 := by
    intro i
    rcases hg i with hi | hi <;> rcases hg (finRotate n i) with hj | hj
    · left; change g i * g (finRotate n i) = 1; rw [hi, hj]; norm_num
    · right; change g i * g (finRotate n i) = -1; rw [hi, hj]; norm_num
    · right; change g i * g (finRotate n i) = -1; rw [hi, hj]; norm_num
    · left; change g i * g (finRotate n i) = 1; rw [hi, hj]; norm_num
  have hrot : (∏ i, g (finRotate n i)) = ∏ i, g i := Equiv.prod_comp _ _
  have hprodg : (∏ i, g i) = 1 ∨ (∏ i, g i) = -1 := by
    have hp := prod_pm_one_eq_neg_one_pow_card_neg Finset.univ g (by simpa using hg)
    rw [hp]
    rcases Nat.even_or_odd ((Finset.univ.filter (fun i => g i = -1)).card) with he | ho
    · left; simp [Even.neg_one_pow he]
    · right; simpa using Odd.neg_one_pow ho
  have hprod : ∏ i, f i = 1 := by
    rw [show (∏ i, f i) = (∏ i, g i) * (∏ i, g (finRotate n i)) by
      simp [f, Finset.prod_mul_distrib], hrot]
    rcases hprodg with h | h <;> rw [h] <;> norm_num
  have he := even_card_neg_of_prod_one f hf hprod
  have hfilter : (Finset.univ.filter (fun i => f i = -1)) =
      Finset.univ.filter (fun i => a i * a (finRotate n i) < 0) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hai := hne i
    have haj := hne (finRotate n i)
    rcases lt_or_gt_of_ne hai with hi | hi <;> rcases lt_or_gt_of_ne haj with hj | hj
    · have hgi : g i = -1 := if_neg (not_lt.mpr hi.le)
      have hgj : g (finRotate n i) = -1 := if_neg (not_lt.mpr hj.le)
      have hp : 0 < a i * a (finRotate n i) := mul_pos_of_neg_of_neg hi hj
      change (g i * g (finRotate n i) = -1 ↔ a i * a (finRotate n i) < 0)
      rw [hgi, hgj]
      norm_num
      exact (by simpa only [finRotate_apply] using hp.le)
    · have hgi : g i = -1 := if_neg (not_lt.mpr hi.le)
      have hgj : g (finRotate n i) = 1 := if_pos hj
      have hp : a i * a (finRotate n i) < 0 := mul_neg_of_neg_of_pos hi hj
      change (g i * g (finRotate n i) = -1 ↔ a i * a (finRotate n i) < 0)
      rw [hgi, hgj]
      norm_num
      exact (by simpa only [finRotate_apply] using hp)
    · have hgi : g i = 1 := if_pos hi
      have hgj : g (finRotate n i) = -1 := if_neg (not_lt.mpr hj.le)
      have hp : a i * a (finRotate n i) < 0 := mul_neg_of_pos_of_neg hi hj
      change (g i * g (finRotate n i) = -1 ↔ a i * a (finRotate n i) < 0)
      rw [hgi, hgj]
      norm_num
      exact (by simpa only [finRotate_apply] using hp)
    · have hgi : g i = 1 := if_pos hi
      have hgj : g (finRotate n i) = 1 := if_pos hj
      have hp : 0 < a i * a (finRotate n i) := mul_pos hi hj
      change (g i * g (finRotate n i) = -1 ↔ a i * a (finRotate n i) < 0)
      rw [hgi, hgj]
      norm_num
      exact (by simpa only [finRotate_apply] using hp.le)
  rwa [hfilter] at he

/-- **A directed cycle is even** (Shinar--Feinberg Lemma 5.4).

A cycle of the sign-causality graph that is a union of causal units has a c-pair at a position
exactly when the species signs differ between the two edges of that position (Remark 5.2 of the
paper), and an even number of sign changes occurs around any closed loop of a nonvanishing sign
pattern — hence an even number of c-pairs.  The sign pattern `σ` is required to be nonvanishing
on the cycle's species. -/
theorem TrueSRCycle.even_of_signChange {n : ℕ} {N : Network S}
    (C : N.TrueSRCycle n) (σ : S → ℝ)
    (hσ : ∀ i, σ (C.species i) ≠ 0)
    (hpair : ∀ i, C.isCPair i ↔
      σ (C.species i) * σ (C.species (finRotate n i)) < 0) : C.Even := by
  classical
  let a : Fin n → ℝ := fun i => σ (C.species i)
  haveI : NeZero n := ⟨by have := C.nontrivial; omega⟩
  have hne : ∀ i, a i ≠ 0 := hσ
  have hEven := cyclic_sign_changes_even a hne
  rw [TrueSRCycle.Even, TrueSRCycle.numCPairs]
  rw [show (Finset.univ.filter C.isCPair) =
      Finset.univ.filter (fun i => a i * a (finRotate n i) < 0) by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, a]
    exact hpair i]
  exact hEven

/-! ### Case 1 of Lemma A.6 -/

/-- **Case 1 of Lemma A.6 (Shinar--Feinberg, Appendix A.3) contradicts the true-SR criterion.**

A fresh directed ear `E` joins the stage species `s*` to the stage reaction `ρ*`; the stage
carries a path `A` from `s*` to `ρ*` and a path `B` from `ρ*` to `s*`, the latter supplied
reversed as a species-to-reaction `TrueSRPath`.  Hypotheses:

* `hAstage` / `hfresh` — the stage vertex set `T` contains every `A`-vertex, but no ear edge has
  both endpoints in `T`; from these the proof derives that no ear edge is an `A`-edge, so the
  common edges of the two glued cycles are exactly `B`'s;
* `hAB` — the two stage paths share their endpoints and are interior- and edge-disjoint
  (the vertex-disjoint case of the paper's Figure 6);
* `hEB` — likewise for the ear and `B` (the ear's interior avoids the stage vertices of `B`);
* `hσ1`/`hdir1`, `hσ2`/`hdir2` — both glued cycles are **directed**: `σ` is nonvanishing on their
  species and a c-pair at a cycle position occurs exactly when `σ` changes sign between the two
  species flanking that position (the union-of-causal-units condition of Lemma 5.4), so both
  cycles are even.

The two even cycles `A`·`B` and `E`·`B` then intersect in the species-to-reaction path `B`,
which is what `no_shared_path_of_trueSRCriterion` forbids. -/
theorem lemmaA6_case1 (N : Network S) (hSR : N.TrueSRStrongCriterion) {i j k : ℕ}
    (T : Finset N.TrueSRVertex)
    (A : N.TrueSRPath (2 * j + 1))
    (B : N.TrueSRPath (2 * i + 1))
    (E : N.TrueSRPath (2 * k + 1))
    (hAstage : ∀ p : Fin (2 * j + 2), A.vertex p ∈ T)
    (hfresh : ∀ p : Fin (2 * k + 1),
      ¬ (Sum.inl (E.edge p).species ∈ T ∧
        Sum.inr ⟨(E.edge p).reaction, (E.edge p).internal⟩ ∈ T))
    (hAB : Gluable A B) (hEB : Gluable E B)
    (hn1 : 2 ≤ i + j + 1) (hn2 : 2 ≤ i + k + 1)
    (σ : S → ℝ)
    (hσ1 : ∀ t : Fin (i + j + 1),
      σ ((glueCycle A B hAB hn1).species t) ≠ 0)
    (hdir1 : ∀ t : Fin (i + j + 1),
      (glueCycle A B hAB hn1).isCPair t ↔
        σ ((glueCycle A B hAB hn1).species t) *
          σ ((glueCycle A B hAB hn1).species (finRotate (i + j + 1) t)) < 0)
    (hσ2 : ∀ t : Fin (i + k + 1),
      σ ((glueCycle E B hEB hn2).species t) ≠ 0)
    (hdir2 : ∀ t : Fin (i + k + 1),
      (glueCycle E B hEB hn2).isCPair t ↔
        σ ((glueCycle E B hEB hn2).species t) *
          σ ((glueCycle E B hEB hn2).species (finRotate (i + k + 1) t)) < 0) :
    False := by
  classical
  -- Freshness against the stage: no ear edge is an `A`-edge.  An `A`-edge has both of its
  -- endpoints in `T` (all `A`-vertices lie there), a fresh ear edge does not.
  have hAE : ∀ a : Fin (2 * j + 1), ∀ e : Fin (2 * k + 1),
      ¬ (A.edge a).SameIncidence (E.edge e) := by
    intro a e hae
    have hsp : Sum.inl (A.edge a).species ∈ T := by
      rcases A.connects a with ⟨h1, _⟩ | ⟨_, h1⟩
      · rw [← h1]; exact hAstage (Fin.castSucc a)
      · rw [← h1]; exact hAstage a.succ
    have hre : Sum.inr ⟨(A.edge a).reaction, (A.edge a).internal⟩ ∈ T := by
      rcases A.connects a with ⟨_, h2⟩ | ⟨h2, _⟩
      · rw [← h2]; exact hAstage a.succ
      · rw [← h2]; exact hAstage (Fin.castSucc a)
    refine hfresh e ⟨?_, ?_⟩
    · rw [← hae.1]; exact hsp
    · -- the reaction vertices coincide: the reaction fields agree and the proof fields are
      -- irrelevant, so rewrite the whole `Sum.inr`-vertex (rewriting the dependent pair's
      -- first component alone would break the motive)
      have hk :
          (Sum.inr ⟨(E.edge e).reaction, (E.edge e).internal⟩ : N.TrueSRVertex) =
            Sum.inr ⟨(A.edge a).reaction, (A.edge a).internal⟩ :=
        congrArg (Sum.inr : N.InternalTrueReaction → N.TrueSRVertex)
          (Subtype.ext hae.2.1.symm :
            (⟨(E.edge e).reaction, (E.edge e).internal⟩ : N.InternalTrueReaction) =
              ⟨(A.edge a).reaction, (A.edge a).internal⟩)
      rw [hk]; exact hre
  refine no_shared_path_of_trueSRCriterion N hSR
    (glueCycle A B hAB hn1) (glueCycle E B hEB hn2) ?_ ?_ B ?_ ?_ ?_
  -- both glued cycles are directed, hence even
  · exact TrueSRCycle.even_of_signChange (glueCycle A B hAB hn1) σ hσ1 hdir1
  · exact TrueSRCycle.even_of_signChange (glueCycle E B hEB hn2) σ hσ2 hdir2
  -- every edge of `B` lies on the stage cycle `A`·`B` ...
  · intro b
    exact (glueCycle_containsEdge_iff A B hAB hn1 (B.edge b)).mpr
      (Or.inr ⟨b, SameIncidence.refl _⟩)
  -- ... and on the ear cycle `E`·`B`
  · intro b
    exact (glueCycle_containsEdge_iff E B hEB hn2 (B.edge b)).mpr
      (Or.inr ⟨b, SameIncidence.refl _⟩)
  -- an edge common to both cycles is a `B`-edge: `(A ∪ B) ∩ (E ∪ B) = B`, since `A ∩ E = ∅`
  · intro f hf1 hf2
    rcases (glueCycle_containsEdge_iff A B hAB hn1 f).mp hf1 with ⟨a, ha⟩ | ⟨p, hp⟩
    · rcases (glueCycle_containsEdge_iff E B hEB hn2 f).mp hf2 with ⟨e, he⟩ | ⟨p, hp⟩
      · exact absurd (SameIncidence.trans (SameIncidence.symm ha) he) (hAE a e)
      · exact ⟨p, hp⟩
    · exact ⟨p, hp⟩

end CRNT.Network