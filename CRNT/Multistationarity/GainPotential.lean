import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Lattice
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Feasible multipliers for a gain-weighted digraph

Shinar--Feinberg's Proposition 5.12 needs, for a reaction block of the sign-causality graph with
no stoichiometrically expansive directed cycle, a positive multiplier per species satisfying

    G v w * M w  ≤  M v

on every causal unit `v → w`, where `G v w` is the edge gain.  This is the multiplicative form of
the classical statement that a system of difference constraints is feasible when no cycle has
negative total weight, and the witness is the extremal (shortest-path) solution.

This module proves the finite graph multiplier result in both closed-walk and simple-cycle
forms (`exists_feasible_multipliers` and `exists_feasible_multipliers_of_simple`).  The proof
uses bounded-walk maxima, finite cycle deletion, and factorization of closed walks into simple
cycles.  The remaining work in the CRNT theorem is network-specific: identify the relevant
reaction blocks and transfer the true-SR hypotheses to their causal gains.

`CRNT.Network.multiplier_chain` shows why an arbitrary feasible solution will not do: chaining the
relation along a path bounds the multiplier at the start from *above* in terms of the one at the
end, so extending multipliers across a new directed ear — the obvious induction, along
Shinar--Feinberg's own ear decomposition — needs a lower bound it cannot supply.  Hence the
extremal solution, and hence the bounded-walk maximum defined here.

`gainIter G k v` is the largest gain product over directed walks of length at most `k` leaving
`v`.  It is monotone in `k` and at least `1` (the empty walk).  The key fact is
`gainIter_feasible_of_stable`: as soon as one iteration fails to increase the value, the current
value *is* a feasible multiplier assignment.

What remains for a full Proposition 5.12 is the stabilization step: the iteration stops growing by
step `|V|`, because a walk longer than `|V|` repeats a vertex and so contains a directed cycle,
which by non-expansiveness cannot increase the gain product.  That argument needs a walk API with
cycle deletion and is the one outstanding piece.

Depends on: Mathlib only.
-/

namespace CRNT

variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]

/-- Bounded-walk gain maximum: `gainIter G k v` is the largest gain product over directed walks
of length at most `k` starting at `v`, with the empty walk contributing `1`. -/
noncomputable def gainIter (G : V → V → ℝ) : ℕ → V → ℝ
  | 0 => fun _ => 1
  | k + 1 => fun v =>
      max (gainIter G k v)
        (Finset.univ.sup' Finset.univ_nonempty (fun w => G v w * gainIter G k w))

@[simp] theorem gainIter_zero (G : V → V → ℝ) (v : V) : gainIter G 0 v = 1 := rfl

theorem gainIter_succ (G : V → V → ℝ) (k : ℕ) (v : V) :
    gainIter G (k + 1) v =
      max (gainIter G k v)
        (Finset.univ.sup' Finset.univ_nonempty (fun w => G v w * gainIter G k w)) := rfl

/-- The bounded-walk maximum is monotone in the length bound: longer walks are still walks. -/
theorem gainIter_mono (G : V → V → ℝ) (k : ℕ) (v : V) :
    gainIter G k v ≤ gainIter G (k + 1) v := by
  rw [gainIter_succ]
  exact le_max_left _ _

/-- Every value is at least `1`, witnessed by the empty walk.  In particular the multipliers
produced here are automatically positive. -/
theorem one_le_gainIter (G : V → V → ℝ) (k : ℕ) (v : V) : 1 ≤ gainIter G k v := by
  induction k with
  | zero => simp
  | succ k ih => exact le_trans ih (gainIter_mono G k v)

theorem gainIter_pos (G : V → V → ℝ) (k : ℕ) (v : V) : 0 < gainIter G k v :=
  lt_of_lt_of_le zero_lt_one (one_le_gainIter G k v)

/-- **Stabilization gives feasibility.**  Once one iteration fails to increase any value, the
current values satisfy the multiplier relation on every edge.  This is the half of Proposition
5.12 that does not need the walk-decomposition argument. -/
theorem gainIter_feasible_of_stable (G : V → V → ℝ) {k : ℕ}
    (hstab : ∀ v, gainIter G (k + 1) v = gainIter G k v) (v w : V) :
    G v w * gainIter G k w ≤ gainIter G k v := by
  have hle : G v w * gainIter G k w ≤
      Finset.univ.sup' Finset.univ_nonempty (fun u => G v u * gainIter G k u) :=
    Finset.le_sup' (fun u => G v u * gainIter G k u) (Finset.mem_univ w)
  have hmax := le_max_right (gainIter G k v)
    (Finset.univ.sup' Finset.univ_nonempty (fun u => G v u * gainIter G k u))
  rw [← gainIter_succ, hstab v] at hmax
  exact le_trans hle hmax

/-- Packaged form: a stabilized iteration is exactly a positive feasible multiplier assignment,
which is what `weighted_source_inequalities_infeasible` consumes. -/
theorem exists_feasible_multipliers_of_stable (G : V → V → ℝ) {k : ℕ}
    (hstab : ∀ v, gainIter G (k + 1) v = gainIter G k v) :
    ∃ M : V → ℝ, (∀ v, 0 < M v) ∧ ∀ v w, G v w * M w ≤ M v :=
  ⟨gainIter G k, gainIter_pos G k, gainIter_feasible_of_stable G hstab⟩

/-- Gain product along a directed walk, given as its start vertex and the list of subsequent
vertices.  The empty list is the trivial walk, of gain `1`. -/
noncomputable def pathGain (G : V → V → ℝ) : V → List V → ℝ
  | _, [] => 1
  | v, x :: xs => G v x * pathGain G x xs

@[simp] theorem pathGain_nil (G : V → V → ℝ) (v : V) : pathGain G v [] = 1 := rfl

@[simp] theorem pathGain_cons (G : V → V → ℝ) (v x : V) (xs : List V) :
    pathGain G v (x :: xs) = G v x * pathGain G x xs := rfl

/-- The bounded-walk maximum dominates every walk within the length bound. -/
theorem pathGain_le_gainIter (G : V → V → ℝ) (hG : ∀ v w, 0 ≤ G v w) :
    ∀ (k : ℕ) (v : V) (l : List V), l.length ≤ k → pathGain G v l ≤ gainIter G k v := by
  intro k
  induction k with
  | zero =>
      intro v l hl
      have : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
      subst this
      simp
  | succ k ih =>
      intro v l hl
      match l with
      | [] => simpa using one_le_gainIter G (k + 1) v
      | x :: xs =>
          have hxs : xs.length ≤ k := by
            simpa using Nat.succ_le_succ_iff.mp hl
          have h1 : pathGain G x xs ≤ gainIter G k x := ih x xs hxs
          have h2 : G v x * pathGain G x xs ≤ G v x * gainIter G k x :=
            mul_le_mul_of_nonneg_left h1 (hG v x)
          have h3 : G v x * gainIter G k x ≤
              Finset.univ.sup' Finset.univ_nonempty (fun w => G v w * gainIter G k w) :=
            Finset.le_sup' (fun w => G v w * gainIter G k w) (Finset.mem_univ x)
          have h4 := le_max_right (gainIter G k v)
            (Finset.univ.sup' Finset.univ_nonempty (fun w => G v w * gainIter G k w))
          rw [← gainIter_succ] at h4
          simpa using le_trans h2 (le_trans h3 h4)

/-- The bounded-walk maximum is attained by an actual walk within the bound. -/
theorem exists_pathGain_eq_gainIter (G : V → V → ℝ) :
    ∀ (k : ℕ) (v : V), ∃ l : List V, l.length ≤ k ∧ gainIter G k v = pathGain G v l := by
  intro k
  induction k with
  | zero => intro v; exact ⟨[], le_rfl, by simp⟩
  | succ k ih =>
      intro v
      rw [gainIter_succ]
      rcases le_total (Finset.univ.sup' Finset.univ_nonempty
          (fun w => G v w * gainIter G k w)) (gainIter G k v) with hcase | hcase
      · obtain ⟨l, hlen, hval⟩ := ih v
        exact ⟨l, le_trans hlen (Nat.le_succ k), by rw [max_eq_left hcase, hval]⟩
      · obtain ⟨w, -, hw⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
          (fun u => G v u * gainIter G k u)
        obtain ⟨l, hlen, hval⟩ := ih w
        refine ⟨w :: l, ?_, ?_⟩
        · simpa using Nat.succ_le_succ hlen
        · rw [max_eq_right hcase, hw, hval, pathGain_cons]

/-- **Stabilization from a shortening property.**

If every walk of length at least `K` can be replaced by a strictly shorter walk of at least the
same gain, the bounded-walk maximum stops growing at `K`, and `gainIter_feasible_of_stable` then
yields feasible multipliers.

This isolates the one remaining ingredient of Proposition 5.12 in general.  The shortening
property is the cycle-deletion argument: a walk with at least `Fintype.card V` steps visits some
vertex twice, so it contains a directed cycle, and when no cycle is stoichiometrically expansive
that cycle has gain at most one and can be excised without decreasing the total. -/
theorem gainIter_stabilizes_of_shortening (G : V → V → ℝ) (hG : ∀ v w, 0 ≤ G v w) {K : ℕ}
    (hshort : ∀ (v : V) (l : List V), K ≤ l.length →
      ∃ l' : List V, l'.length < l.length ∧ pathGain G v l ≤ pathGain G v l') (v : V) :
    gainIter G (K + 1) v = gainIter G K v := by
  refine le_antisymm ?_ (gainIter_mono G K v)
  obtain ⟨l, hlen, hval⟩ := exists_pathGain_eq_gainIter G (K + 1) v
  rcases Nat.lt_or_ge l.length (K + 1) with hlt | hge
  · rw [hval]
    exact pathGain_le_gainIter G hG K v l (Nat.lt_succ_iff.mp hlt)
  · have hK : K ≤ l.length := le_trans (Nat.le_succ K) hge
    obtain ⟨l', hshorter, hgain⟩ := hshort v l hK
    have hl'len : l'.length ≤ K := by
      have : l.length ≤ K + 1 := hlen
      omega
    rw [hval]
    exact le_trans hgain (pathGain_le_gainIter G hG K v l' hl'len)

/-- Packaged: the shortening property yields the positive feasible multipliers that
`weighted_source_inequalities_infeasible` consumes. -/
theorem exists_feasible_multipliers_of_shortening (G : V → V → ℝ) (hG : ∀ v w, 0 ≤ G v w)
    {K : ℕ}
    (hshort : ∀ (v : V) (l : List V), K ≤ l.length →
      ∃ l' : List V, l'.length < l.length ∧ pathGain G v l ≤ pathGain G v l') :
    ∃ M : V → ℝ, (∀ v, 0 < M v) ∧ ∀ v w, G v w * M w ≤ M v :=
  exists_feasible_multipliers_of_stable G (gainIter_stabilizes_of_shortening G hG hshort)


/-- A list in which some element occurs at least twice splits around two of its occurrences. -/
theorem exists_double_split {x : V} :
    ∀ L : List V, 2 ≤ L.count x → ∃ p q r : List V, L = p ++ x :: q ++ x :: r := by
  intro L
  induction L with
  | nil => intro h; simp at h
  | cons a L' ih =>
      intro h
      by_cases hax : a = x
      · subst hax
        rw [List.count_cons_self] at h
        have h1 : 1 ≤ L'.count a := by omega
        have hmem : a ∈ L' := List.count_pos_iff.mp h1
        obtain ⟨q, r, hqr⟩ := List.mem_iff_append.mp hmem
        exact ⟨[], q, r, by simp [hqr]⟩
      · rw [List.count_cons_of_ne hax] at h
        obtain ⟨p, q, r, hpqr⟩ := ih h
        exact ⟨a :: p, q, r, by simp [hpqr]⟩


/-- Gain along a vertex sequence, with the start vertex included in the list.  This is the shape
that list surgery acts on. -/
noncomputable def seqGain (G : V → V → ℝ) : List V → ℝ
  | [] => 1
  | [_] => 1
  | u :: v :: rest => G u v * seqGain G (v :: rest)

@[simp] theorem seqGain_nil (G : V → V → ℝ) : seqGain G ([] : List V) = 1 := rfl
@[simp] theorem seqGain_singleton (G : V → V → ℝ) (v : V) : seqGain G [v] = 1 := rfl
@[simp] theorem seqGain_cons_cons (G : V → V → ℝ) (u v : V) (rest : List V) :
    seqGain G (u :: v :: rest) = G u v * seqGain G (v :: rest) := rfl

theorem seqGain_eq_pathGain (G : V → V → ℝ) :
    ∀ (v : V) (l : List V), seqGain G (v :: l) = pathGain G v l := by
  intro v l
  induction l generalizing v with
  | nil => simp
  | cons x xs ih => simp [ih x]

theorem seqGain_nonneg (G : V → V → ℝ) (hG : ∀ v w, 0 ≤ G v w) :
    ∀ L : List V, 0 ≤ seqGain G L := by
  intro L
  induction L with
  | nil => simp
  | cons u rest ih =>
      match rest with
      | [] => simp
      | v :: rest' =>
          simp only [seqGain_cons_cons]
          exact mul_nonneg (hG u v) ih

/-- Gains multiply when a sequence is cut at a repeated vertex. -/
theorem seqGain_append_cons (G : V → V → ℝ) :
    ∀ (p : List V) (x : V) (s : List V),
      seqGain G (p ++ x :: s) = seqGain G (p ++ [x]) * seqGain G (x :: s) := by
  intro p x s
  induction p with
  | nil => simp
  | cons a p' ih =>
      match p' with
      | [] => simp [seqGain_cons_cons]
      | b :: p'' =>
          simp only [List.cons_append, seqGain_cons_cons] at *
          rw [ih]
          ring

/-- Cutting a repeated vertex out of a sequence cannot lower the gain, provided every closed
walk has gain at most one. -/
theorem seqGain_le_of_split (G : V → V → ℝ) (hG : ∀ v w, 0 ≤ G v w)
    (hcyc : ∀ (x : V) (q : List V), seqGain G (x :: q ++ [x]) ≤ 1)
    (p q r : List V) (x : V) :
    seqGain G (p ++ x :: q ++ x :: r) ≤ seqGain G (p ++ x :: r) := by
  have h1 : seqGain G (p ++ x :: q ++ x :: r) =
      seqGain G (p ++ [x]) * seqGain G (x :: (q ++ x :: r)) := by
    have h := seqGain_append_cons G p x (q ++ x :: r)
    simpa using h
  have h2 : seqGain G (x :: (q ++ x :: r)) =
      seqGain G ((x :: q) ++ [x]) * seqGain G (x :: r) := by
    have := seqGain_append_cons G (x :: q) x r
    simpa using this
  have h3 : seqGain G (p ++ x :: r) = seqGain G (p ++ [x]) * seqGain G (x :: r) :=
    seqGain_append_cons G p x r
  have hA : 0 ≤ seqGain G (p ++ [x]) := seqGain_nonneg G hG _
  have hB : 0 ≤ seqGain G (x :: r) := seqGain_nonneg G hG _
  have hC : seqGain G ((x :: q) ++ [x]) ≤ 1 := by simpa using hcyc x q
  rw [h1, h2, h3]
  have : seqGain G ((x :: q) ++ [x]) * seqGain G (x :: r) ≤ 1 * seqGain G (x :: r) :=
    mul_le_mul_of_nonneg_right hC hB
  calc seqGain G (p ++ [x]) * (seqGain G ((x :: q) ++ [x]) * seqGain G (x :: r))
      ≤ seqGain G (p ++ [x]) * (1 * seqGain G (x :: r)) :=
        mul_le_mul_of_nonneg_left this hA
    _ = seqGain G (p ++ [x]) * seqGain G (x :: r) := by ring


/-- **Cycle deletion: a long walk can always be shortened without losing gain.**

A walk with at least `Fintype.card V` steps visits some vertex twice, so it contains a closed
sub-walk; when every closed walk has gain at most one, excising it leaves a strictly shorter walk
of at least the same gain.  This is the shortening property that
`gainIter_stabilizes_of_shortening` asks for. -/
theorem exists_shorter_of_card_le (G : V → V → ℝ) (hG : ∀ v w, 0 ≤ G v w)
    (hcyc : ∀ (x : V) (q : List V), seqGain G (x :: q ++ [x]) ≤ 1)
    (v : V) (l : List V) (hl : Fintype.card V ≤ l.length) :
    ∃ l' : List V, l'.length < l.length ∧ pathGain G v l ≤ pathGain G v l' := by
  have hlen : Fintype.card V < (v :: l).length := by simp; omega
  have hnd : ¬ (v :: l).Nodup := by
    intro hn
    exact absurd (List.Nodup.length_le_card hn) (by omega)
  obtain ⟨x, hx⟩ := List.exists_duplicate_iff_not_nodup.mpr hnd
  have hcount : 2 ≤ (v :: l).count x := List.duplicate_iff_two_le_count.mp hx
  obtain ⟨p, q, r, hsplit⟩ := exists_double_split (v :: l) hcount
  match p, hsplit with
  | [], hsplit =>
      -- the repeat starts at the walk's own origin
      have hv : v = x ∧ l = q ++ x :: r := by
        simpa using hsplit
      obtain ⟨hvx, hlq⟩ := hv
      refine ⟨r, ?_, ?_⟩
      · rw [hlq]; simp; omega
      · have hstep := seqGain_le_of_split G hG hcyc [] q r x
        rw [← seqGain_eq_pathGain, ← seqGain_eq_pathGain, hvx, hlq]
        simpa using hstep
  | a :: p', hsplit =>
      have hv : v = a ∧ l = p' ++ x :: q ++ x :: r := by
        simpa using hsplit
      obtain ⟨hva, hlp⟩ := hv
      refine ⟨p' ++ x :: r, ?_, ?_⟩
      · rw [hlp]; simp
      · have hstep := seqGain_le_of_split G hG hcyc (a :: p') q r x
        rw [← seqGain_eq_pathGain, ← seqGain_eq_pathGain, hva, hlp]
        simpa using hstep

/-- **Proposition 5.12.**  A gain-weighted digraph in which every closed walk has gain at most one
admits positive multipliers satisfying `G v w * M w ≤ M v` on every edge.

This is the existence result Shinar--Feinberg use for reaction blocks, and it is what
`weighted_source_inequalities_infeasible` consumes. -/
theorem exists_feasible_multipliers (G : V → V → ℝ) (hG : ∀ v w, 0 ≤ G v w)
    (hcyc : ∀ (x : V) (q : List V), seqGain G (x :: q ++ [x]) ≤ 1) :
    ∃ M : V → ℝ, (∀ v, 0 < M v) ∧ ∀ v w, G v w * M w ≤ M v :=
  exists_feasible_multipliers_of_shortening G hG
    (K := Fintype.card V) (fun v l hl => exists_shorter_of_card_le G hG hcyc v l hl)

/-- Every closed walk factors, gain-wise, into two strictly shorter closed walks as soon as its
vertex list repeats. -/
theorem closed_walk_le_one_of_simple (G : V → V → ℝ) (hG : ∀ v w, 0 ≤ G v w)
    (hsimple : ∀ (x : V) (q : List V), (x :: q).Nodup → seqGain G (x :: q ++ [x]) ≤ 1) :
    ∀ (n : ℕ) (x : V) (q : List V), q.length ≤ n → seqGain G (x :: q ++ [x]) ≤ 1 := by
  intro n
  induction n with
  | zero =>
      intro x q hq
      have : q = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hq)
      subst this
      exact hsimple x [] (by simp)
  | succ n ih =>
      intro x q hq
      by_cases hnd : (x :: q).Nodup
      · exact hsimple x q hnd
      · obtain ⟨y, hy⟩ := List.exists_duplicate_iff_not_nodup.mpr hnd
        have hcount : 2 ≤ (x :: q).count y := List.duplicate_iff_two_le_count.mp hy
        obtain ⟨p, m, t, hsplit⟩ := exists_double_split (x :: q) hcount
        -- cut the closed walk at the two occurrences of `y`
        have hW : seqGain G ((x :: q) ++ [x]) =
            seqGain G (p ++ [y]) * (seqGain G (y :: m ++ [y]) *
              seqGain G (y :: (t ++ [x]))) := by
          rw [hsplit]
          have h1 : seqGain G ((p ++ y :: m ++ y :: t) ++ [x]) =
              seqGain G (p ++ y :: (m ++ y :: (t ++ [x]))) := by
            simp
          rw [h1, seqGain_append_cons G p y (m ++ y :: (t ++ [x]))]
          congr 1
          have h2 := seqGain_append_cons G (y :: m) y (t ++ [x])
          simpa using h2
        have hW' : seqGain G ((p ++ y :: t) ++ [x]) =
            seqGain G (p ++ [y]) * seqGain G (y :: (t ++ [x])) := by
          have h3 : seqGain G ((p ++ y :: t) ++ [x]) =
              seqGain G (p ++ y :: (t ++ [x])) := by simp
          rw [h3, seqGain_append_cons G p y (t ++ [x])]
        -- lengths of the two smaller closed walks
        have hlenq : q.length = p.length + m.length + t.length + 1 := by
          have := congrArg List.length hsplit
          simp at this
          omega
        -- the middle closed walk at `y`
        have hmid : seqGain G (y :: m ++ [y]) ≤ 1 := ih y m (by omega)
        -- the recombined closed walk, rebased at `x`
        have hrec : seqGain G ((p ++ y :: t) ++ [x]) ≤ 1 := by
          match p, hsplit with
          | [], hs =>
              obtain ⟨hxy, hqe⟩ : x = y ∧ q = m ++ y :: t := by simpa using hs
              subst hxy
              have hlen2 : t.length ≤ n := by
                have := congrArg List.length hqe
                simp at this
                omega
              have heq : seqGain G ((([] : List V) ++ x :: t) ++ [x]) =
                  seqGain G (x :: t ++ [x]) := by simp
              rw [heq]
              exact ih x t hlen2
          | a :: p', hs =>
              obtain ⟨hxa, hqe⟩ : x = a ∧ q = p' ++ y :: m ++ y :: t := by simpa using hs
              subst hxa
              have hlen2 : (p' ++ y :: t).length ≤ n := by
                have := congrArg List.length hqe
                simp at this
                simp
                omega
              have heq : seqGain G (((x :: p') ++ y :: t) ++ [x]) =
                  seqGain G (x :: (p' ++ y :: t) ++ [x]) := by simp
              rw [heq]
              exact ih x (p' ++ y :: t) hlen2
        have hApos : 0 ≤ seqGain G (p ++ [y]) := seqGain_nonneg G hG _
        have hBpos : 0 ≤ seqGain G (y :: (t ++ [x])) := seqGain_nonneg G hG _
        have hmidpos : 0 ≤ seqGain G (y :: m ++ [y]) := seqGain_nonneg G hG _
        rw [hW]
        calc seqGain G (p ++ [y]) * (seqGain G (y :: m ++ [y]) *
                seqGain G (y :: (t ++ [x])))
            = seqGain G (y :: m ++ [y]) *
                (seqGain G (p ++ [y]) * seqGain G (y :: (t ++ [x]))) := by ring
          _ ≤ 1 * (seqGain G (p ++ [y]) * seqGain G (y :: (t ++ [x]))) := by
              exact mul_le_mul_of_nonneg_right hmid (mul_nonneg hApos hBpos)
          _ = seqGain G ((p ++ y :: t) ++ [x]) := by rw [hW']; ring
          _ ≤ 1 := hrec


/-- **Proposition 5.12 from the simple-cycle hypothesis.**  This is the form Shinar--Feinberg
state: it is enough that no *simple* directed cycle is stoichiometrically expansive.  Closed
walks factor gain-wise into simple cycles, so the closed-walk hypothesis of
`exists_feasible_multipliers` follows. -/
theorem exists_feasible_multipliers_of_simple (G : V → V → ℝ) (hG : ∀ v w, 0 ≤ G v w)
    (hsimple : ∀ (x : V) (q : List V), (x :: q).Nodup → seqGain G (x :: q ++ [x]) ≤ 1) :
    ∃ M : V → ℝ, (∀ v, 0 < M v) ∧ ∀ v w, G v w * M w ≤ M v :=
  exists_feasible_multipliers G hG
    (fun x q => closed_walk_le_one_of_simple G hG hsimple q.length x q le_rfl)

/-- **Restriction of a strict sum inequality to a subset (Shinar--Feinberg 5.4, Remark 5.6).**

Dropping terms that are nonpositive cannot destroy a strict positivity statement.  This is the
step that takes the global kernel inequality at a species to the inequality restricted to the
reactions of a single sign-causality source: every reaction outside the source, and every term
inside it that is not causal for the species' sign, contributes with the opposing sign. -/
theorem sum_subset_pos_of_nonpos_outside {R : Type} [Fintype R] [DecidableEq R]
    (a : R → ℝ) (S : Finset R) (hout : ∀ r ∈ Finset.univ \ S, a r ≤ 0)
    (hpos : 0 < ∑ r, a r) :
    0 < ∑ r ∈ S, a r := by
  classical
  have hsplit : (∑ r, a r) = (∑ r ∈ S, a r) + ∑ r ∈ Finset.univ \ S, a r := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff)]
    congr 1
    exact (Finset.union_sdiff_of_subset (Finset.subset_univ S)).symm
  have hle : (∑ r ∈ Finset.univ \ S, a r) ≤ 0 :=
    Finset.sum_nonpos (fun r hr => hout r hr)
  rw [hsplit] at hpos
  linarith

end CRNT

namespace CRNT
variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]

end CRNT
