import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

/-!
# The `hopp` first-hop forcing argument at the `leftEdge-final` residue

This module isolates, states and machine-checks exactly what the residue comment at
`CRNT/Multistationarity/TrueChemistrySRCriterion.lean:8600-8607` calls *"`k = 1` is forced by
`hopp`"*.

The module is deliberately free of any `CRNT` import: it is pure `Fin n`/real combinatorics, so
it can be imported by `TrueChemistrySRCriterion.lean` (or by any sibling route) without an import
cycle and without perturbing the shared dependency graph.

## What `hopp` is

`hopp` is **not** a statement about paths.  It is a pointwise sign condition on the aggregate
internal class flux at the cycle's own left incidences.  At the residue it is the binder
introduced at `TrueChemistrySRCriterion.lean:8039`:

```lean
have hopp : ∀ i,
    (N.trueInternalClassFlux α (C.reaction (finRotate n i)) (C.species (finRotate n i))) *
      σ (C.species (finRotate n i)) < 0 := by
  intro i
  exact hneg (finRotate n i)
```

and it is consumed downstream at `TrueChemistrySRCriterion.lean:8497-8499`, where it supplies the
single sign fact needed to close one case of the final edge of a reversed path.

The aggregate causal graph it lives in is `Network.TrueInternalAggregateCausalEdge`
(`TrueChemistrySRCriterion.lean:4691`), whose species-to-reaction branch is

```lean
| Sum.inl s, Sum.inr ρ => (N.trueInternalClassFlux α ρ.1 s.1) * σ s.1 < 0
```

Because `C.leftEdge j` has species `C.species j` and reaction `C.reaction j`
(`TrueChemistrySRGraph.lean:141-144`), the hypothesis `hopp` re-indexed by
`(finRotate n).symm` says precisely

> the cycle's **left** edge at index `j` is a *species-to-reaction* aggregate causal edge
> `C.species j → C.reaction j`.

## What this module proves

Write `φ a b := N.trueInternalClassFlux α (C.reaction a) (C.species b)` and
`σs b := σ (C.species b)`, so that `φ` is the class-flux matrix of the cycle species and `σs` their
signs.  The three hypotheses that are genuinely in scope at the residue are

| binder | source line | statement |
| --- | --- | --- |
| `hopp` | `TrueChemistrySRCriterion.lean:8039` | `∀ i, φ (finRotate n i) (finRotate n i) * σs (finRotate n i) < 0` |
| `hcausal` | `TrueChemistrySRCriterion.lean:8036` | `∀ i, 0 < φ i (finRotate n i) * σs (finRotate n i)` |
| `hnc` (negated) | `TrueChemistrySRCriterion.lean:8537` | `∀ a b, a ≠ b → b ≠ (a+1) % n → φ a b * σs b = 0`; this is `nonAdjacent_cycleClassFlux_eq_zero`, `TrueChemistrySRCriterion.lean:6979` |

Results:

1. `hopp_at` / `hopp_of_hopp_at` — the two index conventions for `hopp` are equivalent.
2. `firstHop_forced_leftEdge` — **the forcing statement.**  If an aggregate causal hop out of the
   cycle species `s_j` lands on the cycle reaction `r_a`, then `a = j`.  *`hopp` is not used.*
3. `hop_backward_forced` — the mirror: a hop from a cycle reaction into the cycle species `s_j`
   comes from `r_{(finRotate n).symm j}`.  *Here `hopp` is used* (it kills the self hop).
4. `two_hop_onCycle` — the induced aggregate causal graph on the cycle vertices is the
   **directed** cycle `s_j → r_j → s_{finRotate n j} → r_{finRotate n j} → …`.
5. `no_hop_to_cycle_predecessor` — **machine-checked refutation of the residue comment as
   literally worded.**  There is *no* aggregate causal hop `C.species j → C.reaction
   ((finRotate n).symm j)`.
6. `hopp_alone_insufficient` — **machine-checked counterexample** (exact, on `Fin 3`) showing that
   `hopp` *alone* forces nothing.
7. `shortest_hop_is_leftEdge` — the combined statement: at every cycle species `s_j` the aggregate
   causal out-neighbours among the cycle reactions form the singleton `{C.reaction j}`, and that
   neighbour is attained in one hop.
-/

namespace CRNT

section FirstHop

variable {n : ℕ}

/-- The value of the cycle rotation, in the form used everywhere in
`TrueChemistrySRCriterion.lean`. -/
theorem val_finRotate (i : Fin n) : (finRotate n i).1 = (i.1 + 1) % n := by
  have h := congrArg Fin.val (finRotate_apply i)
  rw [Fin.val_add] at h
  simpa using h

/-- `e.symm b = a` implies `b = e a`. -/
theorem rot_of_symm_apply {e : Fin n ≃ Fin n} {a b : Fin n} (h : e.symm b = a) : b = e a := by
  calc b = e (e.symm b) := (Equiv.apply_symm_apply e b).symm
    _ = e a := congrArg e h

/-- `e a = b` implies `e.symm b = a`. -/
theorem symm_apply_of_apply {e : Fin n ≃ Fin n} {a b : Fin n} (h : e a = b) : e.symm b = a := by
  calc e.symm b = e.symm (e a) := congrArg e.symm h.symm
    _ = a := Equiv.symm_apply_apply e a

/-- `finRotate` has no fixed point on `Fin n` as soon as the cycle is nontrivial. -/
theorem finRotate_ne_self (hn2 : 2 ≤ n) (i : Fin n) : finRotate n i ≠ i := by
  intro h
  have hv := val_finRotate i
  have hv' : (finRotate n i).1 = i.1 := congrArg Fin.val h
  have heq : i.1 = (i.1 + 1) % n := hv'.symm.trans hv
  by_cases hlt : i.1 + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at heq
    omega
  · have hge : n ≤ i.1 + 1 := Nat.le_of_not_gt hlt
    have hle : i.1 + 1 ≤ n := Nat.succ_le_of_lt i.isLt
    have hn : i.1 + 1 = n := le_antisymm hle hge
    rw [hn, Nat.mod_self] at heq
    omega

/-- Re-indexed `hopp`: the cycle's left incidence at `j` carries a strictly negative
species-times-flux term, i.e. the leftEdge at `j` is a species-to-reaction causal edge. -/
theorem hopp_at {φ : Fin n → Fin n → ℝ} {σs : Fin n → ℝ}
    (hopp : ∀ i : Fin n, φ (finRotate n i) (finRotate n i) * σs (finRotate n i) < 0)
    (j : Fin n) : φ j j * σs j < 0 := by
  have h := hopp ((finRotate n).symm j)
  rw [Equiv.apply_symm_apply] at h
  exact h

/-- The converse of `hopp_at`: the diagonal formulation of `hopp` implies the rotated one. -/
theorem hopp_of_hopp_at {φ : Fin n → Fin n → ℝ} {σs : Fin n → ℝ}
    (hd : ∀ j : Fin n, φ j j * σs j < 0) (i : Fin n) :
    φ (finRotate n i) (finRotate n i) * σs (finRotate n i) < 0 := hd (finRotate n i)

/-- Turn the residue's negated non-neighbour-flux test into the vanishing form used below.

At `TrueChemistrySRCriterion.lean:8537` the residue establishes
`hnc : ¬ ∃ (a b : Fin n), a.1 ≠ b.1 ∧ b.1 ≠ (a.1 + 1) % n ∧ φ a b * σs b ≠ 0`;
this is exactly the hypothesis needed by `firstHop_forced_leftEdge`, one classical step away. -/
theorem firstHopZero_of_hnc {φ : Fin n → Fin n → ℝ} {σs : Fin n → ℝ}
    (hnc : ¬ ∃ (a b : Fin n), a.1 ≠ b.1 ∧ b.1 ≠ (a.1 + 1) % n ∧ φ a b * σs b ≠ 0)
    (a b : Fin n) (h1 : a.1 ≠ b.1) (h2 : b.1 ≠ (a.1 + 1) % n) : φ a b * σs b = 0 := by
  by_contra hz
  exact hnc ⟨a, b, h1, h2, hz⟩

/-- **The first-hop forcing lemma.**

If a species-to-reaction aggregate causal hop leaves the cycle species `C.species j` and lands on
the cycle reaction `C.reaction a`, then `a = j`: the hop is the cycle's *left*Edge step.

`hopp` is deliberately *not* a hypothesis: the forcing is entirely due to the vanishing of
non-neighbour cycle-class fluxes (`nonAdjacent_cycleClassFlux_eq_zero`,
`TrueChemistrySRCriterion.lean:6979`, i.e. the negated `hnc` at line 8537) together with the strict
positivity `hcausal` at the cycle successor. -/
theorem firstHop_forced_leftEdge {φ : Fin n → Fin n → ℝ} {σs : Fin n → ℝ}
    (hz : ∀ a b : Fin n, a.1 ≠ b.1 → b.1 ≠ (a.1 + 1) % n → φ a b * σs b = 0)
    (hcausal : ∀ i : Fin n, 0 < φ i (finRotate n i) * σs (finRotate n i))
    (j a : Fin n) (h : φ a j * σs j < 0) : a = j := by
  by_contra hab
  have hav : a.1 ≠ j.1 := fun hv => hab (Fin.ext hv)
  by_cases hsucc : j.1 = (a.1 + 1) % n
  · have hfa : finRotate n a = j := Fin.ext (by rw [val_finRotate]; exact hsucc.symm)
    have hpos := hcausal a
    rw [hfa] at hpos
    exact lt_irrefl _ (lt_of_lt_of_le h (le_of_lt hpos))
  · have hzab := hz a j hav hsucc
    rw [hzab] at h
    exact lt_irrefl 0 h

/-- **Mirror forcing lemma.**  A reaction-to-species aggregate causal hop landing on the cycle
species `C.species j` must come from the cycle reaction `C.reaction ((finRotate n).symm j)`, i.e.
the cycle's *right*Edge step.  Here `hopp` **is** load-bearing: it rules out the self hop
`C.reaction j → C.species j`, whose flux sign would otherwise be unconstrained. -/
theorem hop_backward_forced {φ : Fin n → Fin n → ℝ} {σs : Fin n → ℝ}
    (hz : ∀ a b : Fin n, a.1 ≠ b.1 → b.1 ≠ (a.1 + 1) % n → φ a b * σs b = 0)
    (hopp : ∀ i : Fin n, φ (finRotate n i) (finRotate n i) * σs (finRotate n i) < 0)
    (j a : Fin n) (h : 0 < φ a j * σs j) : a = (finRotate n).symm j := by
  have hpj : φ j j * σs j < 0 := hopp_at hopp j
  by_contra hab
  have hsym : a ≠ (finRotate n).symm j := hab
  by_cases heq : a = j
  · subst heq
    exact lt_irrefl _ (lt_of_lt_of_le hpj (le_of_lt h))
  · have hav : a.1 ≠ j.1 := fun hv => heq (Fin.ext hv)
    by_cases hsucc : j.1 = (a.1 + 1) % n
    · have hfa : finRotate n a = j := Fin.ext (by rw [val_finRotate]; exact hsucc.symm)
      exact hsym (symm_apply_of_apply hfa).symm
    · have hzab := hz a j hav hsucc
      rw [hzab] at h
      exact lt_irrefl 0 h

/-- **On-cycle two-hop.**  A causal hop out of `s_j` onto `r_a` followed by a causal hop out of
`r_a` onto `s_b` forces `a = j` and `b = finRotate n j`.

So the aggregate causal graph restricted to the cycle vertices is the *directed* cycle

```
s_j → r_j → C.species (finRotate n j) → C.reaction (finRotate n j) → …
```

i.e. `hopp` and `hcausal` orient the cycle consistently and every on-cycle step advances the
cycle index by one.  Consequently an on-cycle walk of length `2t` starting at `s_j` ends at
`C.species ((finRotate n)^[t] j)` and one of length `2t + 1` ends at
`C.reaction ((finRotate n)^[t] j)`; in particular the on-cycle route from
`C.species (finRotate n i)` to `C.reaction i` has length `2n - 1`, never `1`. -/
theorem two_hop_onCycle {φ : Fin n → Fin n → ℝ} {σs : Fin n → ℝ}
    (hz : ∀ a b : Fin n, a.1 ≠ b.1 → b.1 ≠ (a.1 + 1) % n → φ a b * σs b = 0)
    (hcausal : ∀ i : Fin n, 0 < φ i (finRotate n i) * σs (finRotate n i))
    (hopp : ∀ i : Fin n, φ (finRotate n i) (finRotate n i) * σs (finRotate n i) < 0)
    (j a b : Fin n) (h1 : φ a j * σs j < 0) (h2 : 0 < φ a b * σs b) :
    a = j ∧ b = finRotate n j := by
  have ha : a = j := firstHop_forced_leftEdge hz hcausal j a h1
  refine ⟨ha, ?_⟩
  rw [ha] at h2
  have hj : j = (finRotate n).symm b := hop_backward_forced hz hopp b j h2
  exact rot_of_symm_apply hj.symm


/-- The forward double hop of an on-cycle walk is forced: a species→reaction hop followed by a
reaction→species hop at the same reaction class advances the cycle index by exactly one.  This
is the stepping rule `onCycle_walk_index` iterates. -/
theorem onCycle_double_step {φ : Fin n → Fin n → ℝ} {σs : Fin n → ℝ}
    (hz : ∀ a b : Fin n, a.1 ≠ b.1 → b.1 ≠ (a.1 + 1) % n → φ a b * σs b = 0)
    (hcausal : ∀ i : Fin n, 0 < φ i (finRotate n i) * σs (finRotate n i))
    (hopp : ∀ i : Fin n, φ (finRotate n i) (finRotate n i) * σs (finRotate n i) < 0)
    (j a b : Fin n) (h1 : φ a j * σs j < 0) (h2 : 0 < φ a b * σs b) :
    a = j ∧ b = finRotate n j :=
  two_hop_onCycle hz hcausal hopp j a b h1 h2

/-- **Refutation of the residue comment as literally worded.**

`TrueChemistrySRCriterion.lean:8603` asserts that the first hop of a shortest species-to-reaction
route from `s₀` is "`s₀ → C.reaction (pos s₀)`", with `pos` fixed by the residue's own
convention (`s₀ = C.species (finRotate n i)` at line 8052 with path endpoint
`qC.1 = C.reaction i` at line 8219, so `pos (C.species j) = (finRotate n).symm j`).  Under that
convention the asserted hop does not exist: the only one-hop target is `C.reaction j`, never
`C.reaction ((finRotate n).symm j)`. -/
theorem no_hop_to_cycle_predecessor {φ : Fin n → Fin n → ℝ} {σs : Fin n → ℝ}
    (hz : ∀ a b : Fin n, a.1 ≠ b.1 → b.1 ≠ (a.1 + 1) % n → φ a b * σs b = 0)
    (hcausal : ∀ i : Fin n, 0 < φ i (finRotate n i) * σs (finRotate n i))
    (hn2 : 2 ≤ n) (j : Fin n) :
    ¬ (φ ((finRotate n).symm j) j * σs j < 0) := by
  intro h
  have hsym : (finRotate n).symm j = j := firstHop_forced_leftEdge hz hcausal j _ h
  have hj : finRotate n j = j := (rot_of_symm_apply hsym).symm
  exact finRotate_ne_self hn2 j hj

/-- **The exact contents of "`k = 1` is forced by `hopp`", in one statement.**

At the cycle species `s_j` the aggregate causal out-neighbours that lie on the cycle form the
singleton `{C.reaction j}`, and that neighbour is attained by a single hop, namely the cycle's
leftEdge step.  Consequently a shortest directed species-to-reaction path from `s_j` to a cycle
reaction has length exactly `1` **iff** its target is `C.reaction j`; for every other cycle
reaction `C.reaction a` a one-hop path does not exist at all (see
`no_hop_to_cycle_predecessor` and `two_hop_onCycle`). -/
theorem shortest_hop_is_leftEdge {φ : Fin n → Fin n → ℝ} {σs : Fin n → ℝ}
    (hz : ∀ a b : Fin n, a.1 ≠ b.1 → b.1 ≠ (a.1 + 1) % n → φ a b * σs b = 0)
    (hcausal : ∀ i : Fin n, 0 < φ i (finRotate n i) * σs (finRotate n i))
    (hopp : ∀ i : Fin n, φ (finRotate n i) (finRotate n i) * σs (finRotate n i) < 0)
    (j : Fin n) :
    (∃ a : Fin n, φ a j * σs j < 0) ∧
      (∀ a : Fin n, φ a j * σs j < 0 → a = j) :=
  ⟨⟨j, hopp_at hopp j⟩, fun a h => firstHop_forced_leftEdge hz hcausal j a h⟩

/-- A flux matrix for the counterexample of `hopp_alone_insufficient`: `-1` on the diagonal, `-1`
at the off-diagonal entry `(1, 2)`, `0` elsewhere. -/
def badFlux (a b : Fin 3) : ℝ :=
  if a.1 = b.1 then -1 else if a.1 = 1 ∧ b.1 = 2 then -1 else 0

/-- **Machine-checked counterexample (diagonal form of `hopp`).**

`hopp` is a pure pointwise sign condition and by itself forces no uniqueness at all.  On `Fin 3`,
with `σs ≡ 1` and flux matrix

```
       b=0   b=1   b=2
 a=0    -1     0     0
 a=1     0    -1    -1
 a=2     0     0    -1
```

every diagonal term is `-1 < 0` (so `hopp` holds), yet `badFlux 1 2 = -1 < 0` with `1 ≠ 2`. -/
theorem hopp_alone_insufficient_diag :
    ∃ (φ : Fin 3 → Fin 3 → ℝ) (σs : Fin 3 → ℝ),
      (∀ j : Fin 3, φ j j * σs j < 0) ∧
        ¬ (∀ a j : Fin 3, φ a j * σs j < 0 → a = j) := by
  refine ⟨badFlux, fun _ => (1 : ℝ), ?_, ?_⟩
  · intro j
    norm_num [badFlux]
  · intro hall
    have hne : ¬ ((1 : Fin 3) = (2 : Fin 3)) := by decide
    refine hne (hall (1 : Fin 3) (2 : Fin 3) ?_)
    norm_num [badFlux]

/-- **Machine-checked counterexample in the exact `hopp` formulation of
`TrueChemistrySRCriterion.lean:8039`.**  Same witness, transported through
`hopp_of_hopp_at`. -/
theorem hopp_alone_insufficient :
    ∃ (φ : Fin 3 → Fin 3 → ℝ) (σs : Fin 3 → ℝ),
      (∀ i : Fin 3, φ (finRotate 3 i) (finRotate 3 i) * σs (finRotate 3 i) < 0) ∧
        ¬ (∀ a j : Fin 3, φ a j * σs j < 0 → a = j) := by
  obtain ⟨φ, σs, hd, hfail⟩ := hopp_alone_insufficient_diag
  exact ⟨φ, σs, fun i => hopp_of_hopp_at hd i, hfail⟩

end FirstHop

end CRNT