# `sr-shortest-path` — shortest-path machinery for the true-SR endgame

**Agent:** `form-sr-route` · **Branch:** `research/form-sr-route` · **Hole:** B

## 0. Status summary

Two modules landed, both elaborating:

| module | content | verification |
| --- | --- | --- |
| `CRNT/Multistationarity/TrueSRReactionArc.lean` | **the RR reaction-arc builder** — the prerequisite the orchestrator identified as blocking `exists_second_evenCycle_of_offCycle_escape` | `lake env lean` exit 0, 0 errors, 0 warnings; `#print axioms` = `[propext, Classical.choice, Quot.sound]` |
| `CRNT/Graph/RelPathShortest.lean` | generic `ShortestPath` with `Nat`-minimality + the no-shortcut lemma | `lake env lean` exit 0, 0 errors, 0 warnings |

**No existing file was modified.** `CRNT/Multistationarity/TrueSRParityRR.lean` and
`CRNT/Graph/RelPath.lean` are byte-identical to `holes` (`git diff` empty on both). The
`prepend` lift was made and then reverted — see §2.

Both modules avoid `import CRNT.Multistationarity.TrueChemistrySRCriterion`, so neither drags
`sorryAx` into its axiom footprint (B-12). Verified by `#print axioms` on every public
declaration of both modules.

## 1. The RR reaction-arc builder — `CRNT/Multistationarity/TrueSRReactionArc.lean`

### 1.1 What was missing

`TrueSRSpeciesPath.lean:610-756` builds the **species** flavour of a cycle arc:

```lean
noncomputable def C.speciesArc   (m : ℕ) (hm : m < n) (hmpos : 0 < m) : N.TrueSRSSPath (2 * m)
noncomputable def C.speciesArcBwd (m : ℕ) (hm : m < n) (hmpos : 0 < m) : N.TrueSRSSPath (2 * (n - m))
```

with `ss_gluable_arcs` (`TrueSRSpeciesPath.lean:902`) giving `SSGluable` between them essentially
free, and `ssGluable_chord_arcFwd` / `ssGluable_chord_arcBwd` (`:946`, `:980`) gluing an arbitrary
chord to either arc.

There is **no** reaction-flavoured counterpart on `holes`.  `TrueSRPathRR`
(`TrueSRParityRR.lean:57`) is therefore never constructible from a cycle, and
`exists_second_evenCycle_of_offCycle_escape` cannot be typed.

### 1.2 The mathematical content

A `TrueSRCycle n` carries `leftEdge i : S_i — R_i` and `rightEdge i : R_i — S_{i+1 mod n}`, so the
graph is the chain

```
R_0 — S_1 — R_1 — S_2 — R_2 — … — S_m — R_m
```

**Lemma (uniqueness of the forward route).**  From `R_0` there is exactly one simple route to
`R_m` running forward: `rightEdge 0, leftEdge 1, rightEdge 1, …, rightEdge (m-1), leftEdge m`,
of length `2m`.

*Proof.*  `R_0`'s only neighbours are `S_0` (via `leftEdge 0`) and `S_1` (via `rightEdge 0`); a
path using `S_0` runs *backwards*.  On the forward side `S_{i}`'s only neighbours are `R_{i-1}`
(`rightEdge (i-1)`) and `R_i` (`leftEdge i`), so from `S_i` the route must take `leftEdge i`.
Induction. ∎

**Parity.**  The true-SR graph is bipartite (species against reactions — `TrueSREdge.Connects`
only ever pairs `Sum.inl` with `Sum.inr`), so every reaction-to-reaction path has even length;
`2m` is even. Consistent.

`TrueSRPathRR j` records a reaction-to-reaction path of `2j+2` edges as a first edge plus a
`TrueSRPath (2j+1)` tail, so `j = m - 1` and

* `first = rightEdge 0` (joins `R_0` to `S_1`);
* `tail : TrueSRPath (2(m-1)+1)` running `S_1 — R_1 — S_2 — … — S_m — R_m`.

### 1.3 Lean signatures (VERIFIED — exact text from the compiling file)

```lean
namespace CRNT.Network.TrueSRCycle

/-- **The forward reaction arc of a cycle**, from `R_0` to `R_m`. -/
noncomputable def reactionArc (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n) (hmpos : 0 < m) :
    N.TrueSRPathRR (m - 1)

theorem reactionArc_startReaction (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n) (hmpos : 0 < m) :
    ((C.reactionArc m hm hmpos).startReaction : N.InternalTrueReaction).1
      = C.reaction ⟨0, by omega⟩

theorem reactionArc_endReaction (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n) (hmpos : 0 < m) :
    (C.reactionArc m hm hmpos).endReaction
      = ⟨C.reaction ⟨m, hm⟩, C.reaction_internal ⟨m, hm⟩⟩

theorem reactionArc_tail_startSpecies (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n)
    (hmpos : 0 < m) :
    (C.reactionArc m hm hmpos).tail.startSpecies = C.species ⟨1, by omega⟩

theorem reactionArc_length (_C : N.TrueSRCycle n) (m : ℕ) (_hm : m < n) (_hmpos : 0 < m) :
    2 * (m - 1) + 2 = 2 * m

end CRNT.Network.TrueSRCycle
```

`reactionArc_startReaction` is stated on `.1` rather than as an `InternalTrueReaction`
equality. The stronger form is not provable as written because `C.reaction_internal` returns an
`InternalTrueReaction` (a `Subtype`), not a `TrueSREdge`, so `.internal` cannot be projected
off it. Since `startReaction` is *definitionally* `⟨A.first.reaction, A.first.internal⟩`, the
`.1` form plus `C.right_reaction` pins the start reaction exactly; no content is lost. A consumer
needing the full equality recovers it by `Subtype.ext` with `C.reaction_internal`.

### 1.4 Internal shape (for downstream reuse)

```lean
private noncomputable def rarcEdge (q : Fin (2 * m - 1)) : N.TrueSREdge :=
  C.leftEdge ⟨q.1 / 2 + 1, arcIdx hm q.isLt⟩

private noncomputable def rarcVertex (p : Fin (2 * m)) : N.TrueSRVertex :=
  if h : p.1 % 2 = 0 then Sum.inl (C.species ⟨p.1 / 2 + 1, arcIdx hm p.isLt⟩)
  else Sum.inr ⟨C.reaction ⟨p.1 / 2 + 1, arcIdx hm p.isLt⟩,
    C.reaction_internal ⟨p.1 / 2 + 1, arcIdx hm p.isLt⟩⟩
```

Position `p` even ⇒ `S_{p/2+1}`, odd ⇒ `R_{p/2+1}`.  So `p = 0` is `S_1` and `p = 2m-1` is `R_m`,
exactly as §1.2 requires.

### 1.5 Citation

Not a published lemma: it is the *dual* of `speciesArc`, which is the Banaji–Craciun
(arXiv:0809.1308, Lemma 10) arc construction that `TrueSRSpeciesPath.initialArcPath`
(`TrueSRArc.lean:73`) already implements for the species flavour. The reaction flavour is needed
because Shinar–Feinberg (arXiv:1203.6560, Appendix A.2, Lemma A.4, p. 52) states its
three-path parity lemma for paths `R*AR**` joining **reactions**; `TrueSRParityRR.lean`
formalises exactly that and has no way to produce its inputs.

### 1.6 Dependency order

1. `TrueSRParityRR.TrueSRPathRR` (exists) — the target type.
2. `TrueSRCycle.reactionArc` (**this file**) — construction.
3. `RRGluable` between `reactionArc`s — **not yet written**, see §3.

## 2. `prepend` — REVERTED, and why

I initially lifted `TrueSRPathRR.prepend` (`TrueSRParityRR.lean:276`) from `private` to public,
on the orchestrator's earlier instruction. A later broadcast superseded this: **`glueArc`
(`TrueSRParityRR.lean:388`) is already public and already is the RR arc builder — do not lift
`prepend`.**

I have therefore **reverted the lift**; `TrueSRParityRR.lean` on my branch is byte-identical to
`holes`. `git diff` on that file is empty.

The correction is right for a second, independent reason I found while working: `reactionArc`
does not need `prepend` at all — it builds the `TrueSRPath` tail directly rather than by
prepending an edge to an existing `TrueSRPathRR`. So the lift was never load-bearing for the
forward arc. It would only be needed for the *backward* arc if that were built by prepending,
but `speciesArcBwd` shows the intended construction is `C.reverse`-based, which needs no
prepend either.

**General lesson for this round:** `checkmod.sh` was broken for the whole round (fixed on `holes`
by `infra-build`). It set `LEAN_PATH` to the shared root and then called `lake env lean`, which
*prepends* its own entries, so the worktree-local build dir landed ahead of the shared cache and
`CRNT.*` imports failed with "object file … does not exist" for oleans that exist. I independently
worked around it by hard-linking the shared oleans into the worktree. Several of my early
"this module does not elaborate" readings were this bug, not my Lean.

## 2b. What already exists downstream (verified by grep, not assumed)

These are present on `holes` and consume exactly what `reactionArc` produces:

* `TrueSRPathRR.RRGluable` (`TrueSRParityRR.lean:256`) — the reaction-flavoured counterpart of
  `TrueSRPath.Gluable` and `TrueSRSSPath.SSGluable`.
* `TrueSRPathRR.glueArc` (`:388`) — **public**, and already the arc builder for gluing purposes.
* `TrueSRPathRR.rrGluedCycle_numCPairs` (`:702`) — the c-pair counting identity
  `c(A ∪ B) = c(A) + s**(A,B) + s*(A,B) + c(B)`.
* **`TrueSRPathRR.rr_three_glued_even_of_two` (`:775`)** — the reaction-flavoured analogue of
  `ss_three_glued_even_of_two`, i.e. Shinar–Feinberg Lemma A.4 for paths `R*AR**`. This is the
  parity engine the ear needs, and it is **already proved**.

So the parity half of `exists_second_evenCycle_of_offCycle_escape` needs nothing new. What is
missing is purely the *geometric* half: producing `RRGluable` instances whose members are the
cycle's own two arcs.

## 3. Residual — `RRGluable` between two reaction arcs

With `reactionArc` built, the next step is the reaction-flavoured analogue of `ss_gluable_arcs`
(`TrueSRSpeciesPath.lean:902`):

```lean
/-- The two reaction arcs of a cycle glue back to it: between reactions `R_0` and `R_m`,
a cycle is two reaction-to-reaction paths with those endpoints whose reaction vertices meet
only in the endpoints. -/
theorem rr_gluable_arcs (m : ℕ) (hm : m < n) (hmpos : 0 < m) :
    TrueSRPathRR.RRGluable (C.reactionArc m hm hmpos) (C.reactionArcBwd m hm hmpos)
```

where

```lean
noncomputable def C.reactionArcBwd (m : ℕ) (hm : m < n) (hmpos : 0 < m) :
    N.TrueSRPathRR (n - m - 1)
```

should be `(C.reverse).reactionArc (n - m) _ _`, mirroring `speciesArcBwd`. This needs
`C.reverse` to preserve `leftEdge`/`rightEdge` under the index map `i ↦ (n - i) % n`; that
`reverse` machinery already exists (`reverse_species'`, used at `TrueSRSpeciesPath.lean:761`)
but its edge-level round-trip has not been checked.

Then, following `ssGluable_chord_arcFwd` (`:946`) verbatim:

```lean
/-- An even reaction-to-reaction path whose interior misses `C` glues to each reaction arc. -/
theorem rrGluable_chord_arcFwd (A : N.TrueSRPathRR j)
    (hstart : A.startReaction = ⟨C.reaction ⟨0,_⟩, _⟩)
    (hend   : A.endReaction   = ⟨C.reaction ⟨m,_⟩, _⟩)
    (hint   : ∀ p : Fin (2*j+3), p.1 ≠ 0 → p.1 ≠ 2*j+2 → ¬ C.HasVertex (A.vertexAt p))
    (hedgeL : ∀ (p : Fin (2*j+2)) (t : Fin n), ¬ (A.edgeAt p).SameIncidence (C.leftEdge t))
    (hedgeR : ∀ (p : Fin (2*j+2)) (t : Fin n), ¬ (A.edgeAt p).SameIncidence (C.rightEdge t)) :
    TrueSRPathRR.RRGluable A (C.reactionArc m hm hmpos)
```

**Why this is the right next step.**  It is the reaction-flavoured restatement of what already
works for species, and it is the exact input shape that
`TrueSRParityRR.three_glued_parity` (Lemma A.4) needs. Without it,
`exists_second_evenCycle_of_offCycle_escape` has no way to produce the three edge-disjoint
reaction-to-reaction paths that the parity argument counts over.

## 4. `CRNT/Graph/RelPathShortest.lean` — generic shortest paths

All verified; `lake env lean` exit 0.

```lean
namespace CRNT.RelPath

def edge (x y : V) (hx : x ∈ T) (hy : y ∈ T) (h : E x y) : RelPath E T 1

structure ShortestPath (E : V → V → Prop) (T : Finset V) (a b : V) where
  length : ℕ
  path : RelPath E T length
  start_eq : path.vertex ⟨0, _⟩ = a
  end_eq : path.vertex ⟨length, _⟩ = b
  min_length : ∀ (l : ℕ) (Q : RelPath E T l),
    Q.vertex ⟨0, _⟩ = a → Q.vertex ⟨l, _⟩ = b → length ≤ l

noncomputable def ShortestPath.of_reflTransGen (hclosed) (hbT : b ∈ T)
    (h : Relation.ReflTransGen E a b) : ShortestPath E T a b

theorem exists_shortestPath (hclosed) (hbT) :
    (∃ _P : ShortestPath E T a b, True) ↔ Relation.ReflTransGen E a b

theorem ShortestPath.injective (P) : Function.Injective P.path.vertex
theorem ShortestPath.eq_of_vertex_eq (P) {i j} (h : P.path.vertex i = P.path.vertex j) : i = j
theorem ShortestPath.le_one_of_edge (P) (hedge : E a b) : P.length ≤ 1
theorem ShortestPath.length_eq_one_of_edge (P) (hedge : E a b) (hab : a ≠ b) : P.length = 1
theorem ShortestPath.not_edge_of_length_ge_two (P) (h2 : 2 ≤ P.length) : ¬ E a b

end CRNT.RelPath
```

`of_reflTransGen` is the `Nat.find`/`Nat.find_min'` construction the assignment asked for;
`le_one_of_edge` is the **no-shortcut lemma**, and `length_eq_one_of_edge` is its endpoint form —
"a shortest path whose endpoints are already joined by an edge has length exactly one", which is
the shape the residue at `TrueChemistrySRCriterion.lean:8607` needs.

**Consumption.** `le_one_of_edge` is used by `length_eq_one_of_edge` and
`not_edge_of_length_ge_two`; `exists_shortestPath` consumes `of_reflTransGen` and
`relPath_reflTransGen`; `eq_of_vertex_eq` consumes `injective`. `edge` is consumed by
`le_one_of_edge`. No orphan.

## 5. Dead ends (do not re-walk)

* **`RelPath.append` (concatenation at an arbitrary shared vertex).**  Three attempts
  (`appendVertex` packaged separately; `dif_pos`/`dif_neg` on a `Fin`-indexed `if`; direct
  `show` + `rw`) all failed to elaborate the `step` field — index arithmetic across the join
  requires rewriting `Fin.castSucc`/`succ` values *under* an `ite`, and `omega` cannot discharge
  the bounds that appear there. **Not a mathematical obstruction**, an engineering one. The
  existing `RelPath.concat` (one step) plus `take`/`tail`/`splice` cover every consumer in the
  tree, so this was dropped rather than sunk further. If prefix/suffix minimality on `RelPath`
  is ever genuinely needed, the right move is a `Fin`-indexed recursion or a `Vector`-style
  `Fin`-`cases` formulation, not `if`-indexed.
* **A generic `prefix_minimal`/`suffix_minimal` on `RelPath`.**  Blocked on the above.
  Superseded in practice: the shortest-path consumer that matters for Hole B is at the
  `TrueSRSSPath`/`TrueSRPathRR` level, where paths are structures with `vertex : Fin (L+1) → V`
  and cutting is a direct reindexing.
* **`TrueSRShortestPath.lean` (prefix/suffix of a `TrueSRSSPath`).**  Written, and it contains
  the right statements (`prefix`, `suffix`, disjointness of the two halves,
  `ShortestSSPath.prefix_minimal` / `suffix_minimal`), but it is **not landed**: the
  orchestrator's later messages redirected this slice to the RR arc builder, which is the actual
  blocking prerequisite. The module as written should compile; it is unverified.

## 5b. `rr_gluable_arcs` — full statement, ready to implement

The one remaining gap, with its exact signature:

```lean
namespace CRNT.Network.TrueSRCycle

/-- The complementary reaction arc: from `R_0` the other way round, to `R_m`.  The `n - m - 1`
parameter mirrors `speciesArcBwd`'s `n - m`. -/
noncomputable def reactionArcBwd (C : TrueSRCycle n) (m : ℕ) (hm : m < n) (hmpos : 0 < m) :
    N.TrueSRPathRR (n - m - 1)

/-- **The two reaction arcs of a cycle glue back to it.**  Between reactions `R_0` and `R_m`
a cycle is two reaction-to-reaction paths with those endpoints whose species vertices and
interior reaction vertices are disjoint and which share no edge. -/
theorem rr_gluable_arcs (C : TrueSRCycle n) (m : ℕ) (hm : m < n) (hmpos : 0 < m) :
    TrueSRPathRR.RRGluable (C.reactionArc m hm hmpos) (C.reactionArcBwd m hm hmpos) where
  same_start := ⟨C.reaction ⟨0, _⟩, _⟩ = ⟨C.reaction ⟨0, _⟩, _⟩   -- rfl
  same_end   := ...                                                 -- by `reverse`'s index map
  species_disjoint := fun s hs hB => ...   -- interiors of the two arcs are the two disjoint
                                              -- index ranges [1,m-1] and [m+1,n-1] of the cycle
  reaction_disjoint := fun ρ hA hB =>
    ρ = (C.reactionArc m hm hmpos).startReaction ∨ ρ = (C.reactionArc m hm hmpos).endReaction
  edge_disjoint := fun i k h => ...       -- left/right edge index ranges are disjoint

end CRNT.Network.TrueSRCycle
```

### RESOLVED: the `reverse` round-trip is free (verified by reading, not assumed)

I checked this directly rather than leaving it open. `TrueSRCycle.reverse`
(`TrueSRCycleReverse.lean:59`) is defined by

```lean
species  := fun j => C.species ⟨(n - j.1) % n, _⟩
reaction := fun j => C.reaction (revPerm n j)
leftEdge  := fun j => C.rightEdge  (revPerm n j)
rightEdge := fun j => C.leftEdge   (revPerm n j)
```

and its two edge characterisations are **`rfl`**:

```lean
@[simp] theorem reverse_leftEdge  (C) (j) : (C.reverse).leftEdge  j = C.rightEdge  (revPerm n j) := rfl
@[simp] theorem reverse_rightEdge (C) (j) : (C.reverse).rightEdge j = C.leftEdge   (revPerm n j) := rfl
```

together with `rev_succ_idx` (`:40`) and `rev_pred_idx` (`:46`) for the species-index arithmetic,
and `reverse_species'` used by `speciesArcBwd` at `TrueSRSpeciesPath.lean:761`.

Consequence: `rarcEdge` and `rarcVertex` are stated purely in terms of `leftEdge`, `rightEdge`,
`species`, `reaction` and `reaction_internal`, so `simp only [reverse_leftEdge, reverse_rightEdge]`
rewrites every occurrence and `(C.reverse).reactionArc` reduces definitionally to a walk on `C`'s
own edges. **There is no round-trip lemma to prove.** `reactionArcBwd` is therefore a one-line
definition:

```lean
noncomputable def reactionArcBwd (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n) (hmpos : 0 < m) :
    N.TrueSRPathRR (n - m - 1) :=
  (C.reverse).reactionArc (n - m) (by omega) (by omega)
```

exactly mirroring `speciesArcBwd := (C.reverse).speciesArc (n - m) _ _`. The only genuine work in
`rr_gluable_arcs` is then the disjointness bookkeeping (the two arcs' index ranges are
`[1, m-1]` and `[m+1, n-1]` of the cycle, disjoint by `omega`), which is exactly the pattern
`ss_gluable_arcs` (`TrueSRSpeciesPath.lean:902`) already implements for the species flavour.

Then the ear itself, in the shape `rr_three_glued_even_of_two` wants: three edge-disjoint
reaction-to-reaction paths between the two cycle reactions, obtained from
`reactionArc`/`reactionArcBwd` plus the escape path, with two of the three glued cycles known
even. That closes in `hSR.2` (B-12), never in `hnd` (B-1 kills `hnd`).

## 6. What I did NOT establish

* `exists_second_evenCycle_of_offCycle_escape` — **not attempted.** It needs `rr_gluable_arcs`
  (§3) first, which needs `reactionArcBwd` and a checked `reverse` edge round-trip.
* Whether `reactionArc`'s tail composition with the cycle's own `leftEdge`/`rightEdge` gives the
  c-pair bookkeeping needed for the parity count. The species flavour has
  `ss_three_glued_even_of_two` (`TrueChemistrySRCriterion.lean:7976`, `private`); the reaction
  flavour's analogue was not attempted.
* Nothing about Hole A. The orchestrator froze it pending the `hfloor`/`wmax ∈ ω` adjudication;
  this slice does not touch it.