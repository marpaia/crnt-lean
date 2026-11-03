import CRNT.Dynamics.SiphonDimensionDescent

/-!
# The Butler–McGehee escape produces **no** cardinality estimate

This module certifies a negative result about
`CRNT.Network.siphonCarried_of_escape` (`CRNT/Dynamics/SiphonDimensionDescent.lean:89`, proved
at `:105-114`).

## 1. The precise statement of the escape

`siphonCarried_of_escape` reads, verbatim:

```lean
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
    (hbdry : ∀ q ∈ omegaLimit atTop ϕ {x₀}, q ∉ M →
      ∃ w ∈ omegaLimit atTop ϕ {q}, ∃ s, w s = 0) :
    ∃ P : Finset S, P.Nonempty ∧ N.IsCriticalSiphon P ∧ N.SiphonCarried ϕ x₀ P
```

**The reference species set does not occur.** `P` is bound by the `∃` in the conclusion; no
hypothesis mentions any pre-existing siphon. A trajectory leaving `P` off the boundary therefore
forces exactly one thing — *some* nonempty carried critical siphon exists — and the theorem is
**structurally incapable** of comparing cardinalities against an input siphon. This is not a
missing proof; it is a missing input.

## 2. What `IsCriticalSiphon` needs beyond `SiphonCarried` (the invariance step)

`SiphonCarried` (`SiphonDimensionDescent.lean:61`) unfolds to

```lean
∃ w ∈ omegaLimit atTop ϕ {x₀}, ∀ s, s ∈ P ↔ w s = 0
```

— a purely **definitional** statement: `P` is the zero set of some ω-limit point. It supplies
none of the three clauses of `IsCriticalSiphon` (`CRNT/Dynamics/Siphon.lean:84`):

1. `P.Nonempty` — a genuinely vanishing coordinate. Supplied only by the escape hypothesis
   `hbdry`, which is the sole source of a boundary point in the whole statement.
2. `N.IsSiphon P` — the structural Petri-net condition. Comes from
   `isSiphon_zeroSet_of_mem_omegaLimit` (`CRNT/Dynamics/BoundaryOmegaSiphon.lean:45`), needing
   genuine-field / nonnegativity / compactness.
3. The conservation-law exclusion `¬ ∃ v ≥ 0, (0 < v s ↔ s ∈ P), ∀ r, Σ_s v s • reactionVector r s = 0`.
   Comes from `isCriticalSiphon_zeroSet_of_mem_omegaLimit`
   (`CRNT/Dynamics/CriticalSiphonOmega.lean:45`), the mass-conservation argument, and it is the
   clause that needs affine invariance `hωaff` **and** the positive start `hx0pos`.

All three are discharged by `isCriticalSiphon_of_siphonCarried`
(`SiphonDimensionDescent.lean:68`), which takes the whole seven-hypothesis orbit package
(`hϕγ hK hmaps hωnn hgenω hωaff hx0pos`) plus nonemptiness. **That lemma mentions `card` not
once.** The invariance step is complete in the tree; the cardinality step is simply absent from
the signature.

## 3. The cardinality estimate is refuted

The descent's strict-shrinking alternative is
`∃ Q, Q.Nonempty ∧ IsCriticalSiphon Q ∧ Q.card < P.card ∧ SiphonCarried ϕ x₀ Q`.

The decisive observation is that `SiphonCarried` determines `P` **from its witness**: unfolding
gives `P = univ.filter (w s = 0)`. Hence if the ω-limit set is a singleton there is exactly one
possible carrier, and `not_exists_smaller_carried_of_unique_omegaLimit` below proves the right
disjunct is then *false outright* — `Q = P` and `Q.card < P.card` becomes `P.card < P.card`.

This formalises, as a machine-checked theorem, the degenerate model `ω = {wmax}` that
`CRNT/Dynamics/HighCodimensionSiphonFace.lean:457-459` already names in prose: "The degenerate
ω-limit set `ω = {wmax}` shows why no purely static argument can finish: there the right disjunct
at `Pmax` is false outright."

Combined with `descendStep_iff_omegaPointPositive_of_cardMinimal`
(`SiphonDimensionDescent.lean:347`) — at a cardinality-minimal carried siphon the descent step is
*the goal itself* — the picture is closed: the escape's product is a carrier, and no hypothesis
anywhere in the escape bounds its cardinality against an input siphon.

## 4. The refutation is singleton-specific — and that is the general shape

**A natural generalisation is FALSE and is recorded here so it is not re-walked: "ω finite ⇒ no
strictly smaller carrier" fails already at `|ω| = 2`.**  Take `zeroSet(w₁) = {s₁}` and
`zeroSet(w₂) = {s₁, s₂}`.  Both `{s₁}` and `{s₁,s₂}` are carried — each is some witness's zero
set — and `1 < 2`.  So the strict-shrinking disjunct *is* satisfiable at a finite ω-limit set, and
the singleton result cannot be extended along finiteness.

The correct general statement is `carried_subset_witness_zeroSet_subset` below: carriedness is
witness-determined, so `P ⊆ Q` between two carried sets is witnessed at the level of ω-points,
and two *distinct* carriers require two ω-points with distinct zero sets.  The descent is
therefore not obstructed by finiteness — it is **enabled** by spread in the family
`{zeroSet(w) : w ∈ ω}`.  Anderson's estimate must prove that this family contains a strictly
smaller member than the maximal one, which is exactly
`smaller_carried_siphon_iff_zeroSet_card_lt`
(`CRNT/Dynamics/HighCodimensionSiphonFace.lean:608`) with `Pmax` from
`exists_maximal_zeroSet_omegaPoint` (`:133`).  That is the residue; this module does not attack it.

## Certification

* **Search space.** Exhaustive over the *definitions*: `SiphonCarried`
  (`SiphonDimensionDescent.lean:61`), `IsCriticalSiphon` (`Siphon.lean:84`), `SiphonFace`
  (`CRNT/Dynamics/Persistence.lean:59`), `IsSiphon` (`Siphon.lean:54`). The argument is definitional
  unfolding plus `Finset.ext`; no numeric search, no floating point, nothing to certify
  arithmetically.
* **What was proved.** `carried_eq_zeroSet` (the carrier is a *function* of the ω-point),
  `siphonCarried_eq_of_unique_omegaLimit` (unique carrier at singleton ω),
  `not_exists_smaller_carried_of_unique_omegaLimit` (the refutation),
  `omegaPointPositive_of_descendStep_of_unique_omegaLimit` (the descent step collapses there),
  `siphonCarried_eq_iff_mem_iff` and `carried_subset_witness_zeroSet_subset` (the general
  witness-determined form), and `card_pos_of_carried` / `card_le_fintype_card_of_carried`
  (the exact bounds the escape does yield).
* **What was left unsearched.** Whether the ω-limit family's zero sets have the required spread
  is exactly Anderson's comparable-growth estimate and is **not** attacked here — see
  `research/DEAD-ENDS.md`. Nothing here bears on that question; the refutation is about the
  escape's *signature*, not about the truth of the estimate. The falsity of the `|ω| ≥ 2`
  generalisation (§4) is established by the `zeroSet(w₁) = {s₁}` / `zeroSet(w₂) = {s₁,s₂}`
  construction, which needs no orbit to instantiate.


Depends on: `CRNT.Dynamics.SiphonDimensionDescent`.
-/

open Filter Topology
open scoped BigOperators NNReal Topology

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **A carried species set is the zero set of one ω-limit point.** Unfolding `SiphonCarried`:
carriedness is a *witness-determined* notion — once the ω-point `w` is fixed, `P` is forced to be
`univ.filter (w s = 0)`. This is the definitional reason the escape cannot manufacture a carrier
of independently chosen size: its carrier is pinned to whichever ω-point `hbdry` returns. -/
theorem carried_eq_zeroSet {N : Network S} {ϕ : Flow ℝ≥0 (Concentration S)}
    {x₀ : Concentration S} {P : Finset S} (hP : N.SiphonCarried ϕ x₀ P)
    {w : Concentration S} (hw : w ∈ omegaLimit atTop ϕ {x₀}) (hwP : ∀ s, s ∈ P ↔ w s = 0) :
    P = Finset.univ.filter (fun s => w s = 0) := by
  apply Finset.ext
  intro s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hwP s

/-- **The escape's product is bounded below by one species.** Nonemptiness is the *only*
cardinality content the escape supplies, and it comes from `hbdry` alone — the existence of a
genuinely vanishing coordinate `w s = 0` in the forward limit of the escaping ω-point. -/
theorem card_pos_of_carried {N : Network S} {ϕ : Flow ℝ≥0 (Concentration S)}
    {x₀ : Concentration S} {P : Finset S} (hP : N.SiphonCarried ϕ x₀ P) (hPne : P.Nonempty) :
    0 < P.card :=
  Finset.card_pos.mpr hPne

/-- **And bounded above by the whole species set.** Together with `card_pos_of_carried` these are
the *complete* cardinality content of the escape: `1 ≤ P.card ≤ Fintype.card S`. No comparison
against any other siphon is available. -/
theorem card_le_fintype_card_of_carried {N : Network S} {ϕ : Flow ℝ≥0 (Concentration S)}
    {x₀ : Concentration S} {P : Finset S} (hP : N.SiphonCarried ϕ x₀ P) :
    P.card ≤ Fintype.card S :=
  Finset.card_le_univ P

/-- Every carried set sits inside the species set. (Trivial, recorded because the descent ranges
over `Finset S` and the zero-set reading must be respected.) -/
theorem carried_subsets_univ {N : Network S} {ϕ : Flow ℝ≥0 (Concentration S)}
    {x₀ : Concentration S} {P : Finset S} (hP : N.SiphonCarried ϕ x₀ P) :
    P ⊆ Finset.univ :=
  Finset.subset_univ P

/-- **A single-ω-point trajectory admits exactly one carried species set.** If every ω-limit point
equals `w₀`, then two carried sets coincide: each is the zero set of its own witness, and both
witnesses are `w₀`. This is the structural fact that kills the cardinality estimate. -/
theorem siphonCarried_eq_of_unique_omegaLimit (N : Network S)
    {ϕ : Flow ℝ≥0 (Concentration S)} {x₀ : Concentration S} {w₀ : Concentration S}
    (huniq : ∀ w ∈ omegaLimit atTop ϕ {x₀}, w = w₀)
    {P Q : Finset S} (hP : N.SiphonCarried ϕ x₀ P) (hQ : N.SiphonCarried ϕ x₀ Q) :
    P = Q := by
  obtain ⟨w, hw, hwP⟩ := hP
  obtain ⟨w', hw', hwQ⟩ := hQ
  have hw0 : w = w₀ := huniq w hw
  have hw0' : w' = w₀ := huniq w' hw'
  have hww : w = w' := hw0.symm.trans hw0'
  apply Finset.ext
  intro s
  rw [hwP, hwQ, hww]

/-- **The cardinality estimate is refuted: no strictly smaller carrier exists when the ω-limit set
is a singleton.**

This is the machine-checked counterexample to "`the escape yields `Q` with `Q.card < P.card`".
Under a singleton ω-limit set the escape's hypotheses are satisfiable while the descent's
strict-shrinking disjunct is *false*: `siphonCarried_eq_of_unique_omegaLimit` forces `Q = P`, so
`Q.card < P.card` degenerates to `P.card < P.card`.

It formalises the degenerate model `ω = {wmax}` named in prose at
`CRNT/Dynamics/HighCodimensionSiphonFace.lean:457-459`. -/
theorem not_exists_smaller_carried_of_unique_omegaLimit (N : Network S)
    {ϕ : Flow ℝ≥0 (Concentration S)} {x₀ : Concentration S} {w₀ : Concentration S}
    (huniq : ∀ w ∈ omegaLimit atTop ϕ {x₀}, w = w₀)
    {P : Finset S} (hP : N.SiphonCarried ϕ x₀ P) :
    ¬ ∃ Q : Finset S, Q.Nonempty ∧ N.IsCriticalSiphon Q ∧ Q.card < P.card ∧
        N.SiphonCarried ϕ x₀ Q := by
  rintro ⟨Q, _, _, hlt, hQ⟩
  have hPQ : P = Q := siphonCarried_eq_of_unique_omegaLimit N huniq hP hQ
  rw [hPQ] at hlt
  exact absurd hlt (Nat.lt_irrefl P.card)

/-- **Hence at a singleton ω-limit set the descent's strict-shrinking alternative is unavailable,
so any carried critical siphon forces a positive ω-limit point** — i.e. there the descent step
collapses to its left disjunct, exactly as
`descendStep_iff_omegaPointPositive_of_cardMinimal` (`SiphonDimensionDescent.lean:347`) does at a
cardinality-minimal carried siphon. Here the collapse is forced by the orbit, not by minimality. -/
theorem omegaPointPositive_of_descendStep_of_unique_omegaLimit (N : Network S)
    (hdesc : N.ComparableGrowthDescent ϕ x₀)
    {ϕ : Flow ℝ≥0 (Concentration S)} {x₀ : Concentration S} {w₀ : Concentration S}
    (huniq : ∀ w ∈ omegaLimit atTop ϕ {x₀}, w = w₀)
    {P : Finset S} (hPne : P.Nonempty) (hPcrit : N.IsCriticalSiphon P)
    (hP : N.SiphonCarried ϕ x₀ P) :
    ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive := by
  have hnd := not_exists_smaller_carried_of_unique_omegaLimit N huniq hP
  rcases hdesc.descend P hPne hPcrit hP with hpos | ⟨Q, _, _, hlt, _⟩
  · exact hpos
  · exact absurd hlt hnd

/-- **Two carriers coincide iff they have the same membership predicate.** Since carriedness is
witness-determined (`carried_eq_zeroSet`), a strict inequality `P ≠ Q` between two carried sets is
witnessed already at the level of ω-points. This is why the singleton case is special and,
symmetrically, why the general residue is about the **spread of the zero sets**
`{zeroSet(w) : w ∈ ω}` rather than about how many ω-points there are. -/
theorem siphonCarried_eq_iff_mem_iff (N : Network S)
    {ϕ : Flow ℝ≥0 (Concentration S)} {x₀ : Concentration S}
    {P Q : Finset S} (hP : N.SiphonCarried ϕ x₀ P) (hQ : N.SiphonCarried ϕ x₀ Q) :
    P = Q ↔ ∀ s, (s ∈ P ↔ s ∈ Q) := by
  constructor
  · intro h; simp only [h]
  · intro h
    obtain ⟨w, hw, hwP⟩ := hP
    obtain ⟨w', hw', hwQ⟩ := hQ
    apply Finset.ext
    intro s
    rw [hwP, hwQ]
    constructor
    · intro hs; exact (h s).mp hs
    · intro hs; exact (h s).mpr hs

/-- **A carried set contained in another carried set is witnessed by a distinct ω-point whose
zero set is contained in it.** Carriedness forces `P ⊆ Q` to be a statement about zero sets, hence
about witnesses.

This is the general form of `not_exists_smaller_carried_of_unique_omegaLimit`, and it is what
makes that refutation *singleton-specific*: with two ω-points of different zero sets a strictly
smaller carrier does exist, so the descent's right disjunct is satisfiable at finite ω.
Anderson's estimate must therefore prove **spread** in the family `{zeroSet(w) : w ∈ ω}` — a
strictly smaller member than the maximal one — which is exactly
`smaller_carried_siphon_iff_zeroSet_card_lt`
(`CRNT/Dynamics/HighCodimensionSiphonFace.lean:608`) with `Pmax` from
`exists_maximal_zeroSet_omegaPoint` (`:133`). -/
theorem carried_subset_witness_zeroSet_subset (N : Network S)
    {ϕ : Flow ℝ≥0 (Concentration S)} {x₀ : Concentration S}
    {P Q : Finset S} (hP : N.SiphonCarried ϕ x₀ P) (hQ : N.SiphonCarried ϕ x₀ Q)
    (hsub : P ⊆ Q) :
    ∃ w ∈ omegaLimit atTop ϕ {x₀}, ∃ w' ∈ omegaLimit atTop ϕ {x₀},
      (∀ s, w s = 0 → w' s = 0) ∧ w ≠ w' := by
  obtain ⟨w, hw, hwP⟩ := hP
  obtain ⟨w', hw', hwQ⟩ := hQ
  refine ⟨w, hw, w', hw', ?_, ?_⟩
  · intro s hs
    have hsP : s ∈ P := (hwP s).mpr hs
    have hsQ : s ∈ Q := hsub hsP
    exact (hwQ s).mp hsQ
  · intro hcon
    apply Finset.ext
    intro s
    rw [hwP, hwQ, hcon]

end Network

end CRNT
