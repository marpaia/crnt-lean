import CRNT.Multistationarity.TrueSRCycleSplit
import CRNT.Multistationarity.TrueSRParityRR
import CRNT.Multistationarity.TrueSRReactionArc

/-!
# Reaction-to-reaction arcs of a true-SR cycle

**This closes the construction left open in `TrueSRReactionArc.lean` (DEAD-ENDS B-12).**

A `TrueSRCycle n` has `leftEdge i : x_i — ρ_i` and `rightEdge i : ρ_i — x_{i+1 mod n}`, so its
graph is the chain

```
ρ_0 —rightEdge 0— x_1 —leftEdge 1— ρ_1 —rightEdge 1— x_2 — ⋯ —leftEdge m— ρ_m
```

That walk is the forward reaction-to-reaction arc `ρ_0 ⇝ ρ_m`, and this file builds it as a
`TrueSRPathRR` — the `TrueSRPathRR` counterpart of `speciesArc`
(`TrueSRSpeciesPath.lean:645`), and the object Shinar--Feinberg's Lemma A.4 three-path parity
argument (`rr_three_glued_even_of_two`, `TrueSRParityRR.lean:775`) consumes.  Round 1
(DEAD-ENDS B-12) established that the repository had **no** reaction-flavour arc builder at all,
so this ear could not even be typed.

Its first edge (`rightEdge 0`) is split off into `TrueSRPathRR.first` and the remaining
`2 * m - 1` edges form the tail, so the path parameter is `j = m - 1` and the whole arc has
`2 * (m - 1) + 2 = 2 * m` edges — even, as the bipartition of the true-SR graph forces.

## Why the tail is an arc of `C.rotate 1`

`initialArcPath` reads an arc starting at position `0`; starting at `x_1` is achieved by rotating
the cycle by `1`.  The rotation makes the `% n` in `right_species` never wrap, because every
cycle index the tail touches is `q / 2 + 1` for a tail position `q`, and

```
1 ≤ q / 2 + 1 ≤ m < n.
```

That single fact (`idx_le` below) is the whole of the index arithmetic; everything else is
cycle injectivity.

## The two structure obligations

* `first_ne_tail_edge` — no tail edge shares incidence with `rightEdge 0`.  An even tail position
  carries `leftEdge (q/2 + 1)` and an odd one `rightEdge (q/2 + 1)`.  A cycle never has a left edge
  sharing incidence with a right edge (`C.not_sameIncidence_left_right`); two right edges sharing
  incidence force equal indices (`C.sameIncidence_rightEdge_iff`), i.e. `0 = q/2 + 1`, excluded
  by `idx_pos`.
* `first_ne_tail_vertex` — the start reaction `ρ_0` does not recur.  An even tail position carries
  a species vertex (so `Sum.inl ≠ Sum.inr`); an odd one carries `reaction (q/2 + 1)`, and
  `C.reaction_injective` again forces `0 = q/2 + 1`.

## Reusable trick

`TrueSRCycle.rotate_species` (`TrueSRRotate.lean:67`) is `rfl` **and is stated at `⟨i, ?proof⟩`**,
so it does not rewrite against a goal whose index carries a different proof term.  The four
lemmas `rot1_species_at` / `rot1_reaction_at` / `rot1_leftEdge_at` / `rot1_rightEdge_at` below
restate it at an arbitrary index `q` and discharge the `% n` wrap by hand.  That single
reformulation removes essentially all of the `Fin`-index friction of assembling the arc, and is
worth reusing for any further rotated-arc construction.

Two further mechanical notes, both hit here:

* `rw` through `initialArcPath_edge_even/odd` and `initialArcPath_vertex_even/odd` fails with
  *"motive is not type correct"*, because their index is `⟨q.1 / 2, by omega⟩` and abstracting
  over the `Fin.mk` proof field breaks the motive.  `simp only [...]` with the same explicit
  arguments works.
* `congrArg Fin.val` on a `Fin n` equality yields `⟨a, _⟩.1 = ⟨b, _⟩.1`, which `omega` does **not**
  reduce to `a = b`; `simp only at hv` first is required.
-/

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

namespace TrueSRCycle

variable {n : ℕ}

section ReactionArc

variable {C : N.TrueSRCycle n} {m : ℕ} {hMn : m < n} {hMpos : 0 < m}

/-- Every cycle index the tail touches is `q / 2 + 1` for a tail position `q`, and lies in
`1 … m ⊂ 1 … n - 1`: never `0`, and never wrapping. -/
private theorem idx_le (hmp : 0 < m) {q : ℕ} (hq : q < 2 * (m - 1) + 2) : q / 2 + 1 ≤ m := by
  have h2 : (0 : ℕ) < 2 := by omega
  have h : q / 2 ≤ m - 1 := by
    rw [Nat.div_le_iff_le_mul h2]
    omega
  omega

private theorem idx_lt_n (hmp : 0 < m) (hm : m < n) {q : ℕ} (hq : q < 2 * (m - 1) + 2) :
    q / 2 + 1 < n := by
  have h := idx_le hmp hq
  omega

/-- `q / 2` is itself a valid cycle index. -/
private theorem idx_half_lt (hmp : 0 < m) (hm : m < n) {q : ℕ} (hq : q < 2 * (m - 1) + 2) :
    q / 2 < n :=
  Nat.lt_trans (Nat.lt_succ_self (q / 2)) (idx_lt_n hmp hm hq)

private theorem idx_pos {q : ℕ} : 0 < q / 2 + 1 := by omega

/-- `(C.rotate 1)` has species `C.species (q/2 + 1)` at position `q`. -/
private theorem rot1_species_at (hmp : 0 < m) (hm : m < n) {q : ℕ} (hq : q < 2 * (m - 1) + 2) :
    (C.rotate 1).species ⟨q / 2, idx_half_lt hmp hm hq⟩ =
      C.species ⟨q / 2 + 1, idx_lt_n hmp hm hq⟩ := by
  rw [TrueSRCycle.rotate_species]
  apply congrArg C.species
  apply Fin.ext
  show (q / 2 + 1) % n = q / 2 + 1
  exact Nat.mod_eq_of_lt (idx_lt_n hmp hm hq)

/-- `(C.rotate 1)` has reaction `C.reaction (q/2 + 1)` at position `q`. -/
private theorem rot1_reaction_at (hmp : 0 < m) (hm : m < n) {q : ℕ} (hq : q < 2 * (m - 1) + 2) :
    (C.rotate 1).reaction ⟨q / 2, idx_half_lt hmp hm hq⟩ =
      C.reaction ⟨q / 2 + 1, idx_lt_n hmp hm hq⟩ := by
  rw [TrueSRCycle.rotate_reaction]
  apply congrArg C.reaction
  apply Fin.ext
  show (q / 2 + 1) % n = q / 2 + 1
  exact Nat.mod_eq_of_lt (idx_lt_n hmp hm hq)

/-- `(C.rotate 1)` has left edge `C.leftEdge (q/2 + 1)` at position `q`. -/
private theorem rot1_leftEdge_at (hmp : 0 < m) (hm : m < n) {q : ℕ} (hq : q < 2 * (m - 1) + 2) :
    (C.rotate 1).leftEdge ⟨q / 2, idx_half_lt hmp hm hq⟩ =
      C.leftEdge ⟨q / 2 + 1, idx_lt_n hmp hm hq⟩ := by
  rw [TrueSRCycle.rotate_leftEdge]
  apply congrArg C.leftEdge
  apply Fin.ext
  show (q / 2 + 1) % n = q / 2 + 1
  exact Nat.mod_eq_of_lt (idx_lt_n hmp hm hq)

/-- `(C.rotate 1)` has right edge `C.rightEdge (q/2 + 1)` at position `q`. -/
private theorem rot1_rightEdge_at (hmp : 0 < m) (hm : m < n) {q : ℕ} (hq : q < 2 * (m - 1) + 2) :
    (C.rotate 1).rightEdge ⟨q / 2, idx_half_lt hmp hm hq⟩ =
      C.rightEdge ⟨q / 2 + 1, idx_lt_n hmp hm hq⟩ := by
  rw [TrueSRCycle.rotate_rightEdge]
  apply congrArg C.rightEdge
  apply Fin.ext
  show (q / 2 + 1) % n = q / 2 + 1
  exact Nat.mod_eq_of_lt (idx_lt_n hmp hm hq)

/-- **The forward reaction-to-reaction arc `ρ_0 ⇝ ρ_m`** of `C`. -/
noncomputable def reactionArcFwd : N.TrueSRPathRR (m - 1) :=
  have hk : m - 1 < n := by omega
  { first := C.rightEdge ⟨0, by omega⟩
    tail := (C.rotate 1).initialArcPath (m - 1) hk
    first_species := by
      have h0 : (⟨0, by omega⟩ : Fin (2 * (m - 1) + 2)).1 % 2 = 0 := by
        show (0 : ℕ) % 2 = 0; omega
      have hz : (0 : ℕ) < 2 * (m - 1) + 2 := by omega
      have hv := (C.rotate 1).initialArcPath_vertex_even (m - 1) hk
        (⟨0, by omega⟩ : Fin (2 * (m - 1) + 2)) h0
      rw [hv, rot1_species_at hMpos hMn hz]
      apply congrArg Sum.inl
      rw [C.right_species ⟨0, by omega⟩]
      exact congrArg C.species
        (Fin.ext (by
          show (0 + 1) % n = 0 / 2 + 1
          have h1 : 1 < n := by omega
          rw [Nat.mod_eq_of_lt h1, Nat.add_zero]
          ))
    first_ne_tail_edge := by
      intro i
      have hi := i.isLt
      have hi' : i.1 < 2 * (m - 1) + 2 := by omega
      intro hs
      by_cases hpar : i.1 % 2 = 0
      · simp only [TrueSRCycle.initialArcPath_edge_even (C.rotate 1) (m - 1) hk i hpar,
          rot1_leftEdge_at hMpos hMn hi'] at hs
        exact C.not_sameIncidence_left_right ⟨i.1 / 2 + 1, idx_lt_n hMpos hMn hi'⟩ ⟨0, by omega⟩
          (TrueSREdge.SameIncidence.symm hs)
      · simp only [TrueSRCycle.initialArcPath_edge_odd (C.rotate 1) (m - 1) hk i hpar,
          rot1_rightEdge_at hMpos hMn hi'] at hs
        have hidx := C.sameIncidence_rightEdge_iff ⟨0, by omega⟩
          ⟨i.1 / 2 + 1, idx_lt_n hMpos hMn hi'⟩ hs
        have hv := congrArg Fin.val hidx
        simp only at hv
        have hpos := idx_pos (q := i.1)
        omega
    first_ne_tail_vertex := by
      intro i
      have hi := i.isLt
      have hi' : i.1 < 2 * (m - 1) + 2 := by omega
      intro hs
      by_cases hpar : i.1 % 2 = 0
      · simp only [TrueSRCycle.initialArcPath_vertex_even (C.rotate 1) (m - 1) hk i hpar,
          rot1_species_at hMpos hMn hi'] at hs
        exact absurd hs.symm (by simp)
      · simp only [TrueSRCycle.initialArcPath_vertex_odd (C.rotate 1) (m - 1) hk i hpar,
          rot1_reaction_at hMpos hMn hi'] at hs
        have hval := congrArg Subtype.val (Sum.inr.inj hs)
        have hr : C.reaction ⟨0, by omega⟩ =
            C.reaction ⟨i.1 / 2 + 1, idx_lt_n hMpos hMn hi'⟩ :=
          (C.right_reaction ⟨0, by omega⟩).symm.trans hval
        have hidx := C.reaction_injective hr
        have hv := congrArg Fin.val hidx
        simp only at hv
        have hpos := idx_pos (q := i.1)
        omega }

end ReactionArc

end TrueSRCycle

end CRNT.Network

#print axioms CRNT.Network.TrueSRCycle.reactionArcFwd