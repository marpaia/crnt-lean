import CRNT.Multistationarity.TrueSRSSGlueCPairs

/-!
# The two species-arcs of a cycle partition its c-pairs

For a true-SR cycle `C` of length `n` and `0 < m < n`, the two species-arcs

* `C.speciesArc m` (species `x₀` to species `x_m`, forwards), of length `2 * m`, and
* `C.speciesArcBwd m` (species `x₀` round the other way to species `x_m`), of length
  `2 * (n - m)`,

see, at each of their reaction vertices, exactly the two cycle edges of `C` at that vertex.
Hence the c-pair at index `r` of `C` is realised by `C.speciesArc m` exactly when `r < m`, and
by `C.speciesArcBwd m` (at index `n - 1 - r`) exactly when `m ≤ r`.  The two species-arcs
therefore *partition* the c-pairs of `C`, and their total count is `C.numCPairs`.

Consequence: if `C.Even` then the two species-arcs have the same c-pair count modulo `2`.

`ssCPairAt`/`ssNumCPairs` from `TrueSRSSGlueCPairs.lean` are typed at `2 * j + 2`, i.e. on the
reaction positions `0, …, j` of a path of length `2 * j + 2`; a species-arc of length `2 * m`
is *not* of that form definitionally (`2 * m` versus `2 * (m - 1) + 2`), so statements in that
vocabulary are made at `m = k + 1` (where `2 * (k + 1)` *is* definitionally `2 * k + 2`) or via
an explicit index equation.  The counting itself is done with `ssNumCPairsH`, which is indexed
by the half-positions and hence accepts any length `2 * L`.
-/

namespace CRNT.Network.TrueSRSSPath

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {n : ℕ}

/-- A c-pair of a species-to-species path of length `2 * L`, read off at the half-position
`r`: edge `2 * r` (a left edge) against edge `2 * r + 1` (its right edge). -/
def ssCPairAtH {L : ℕ} (P : N.TrueSRSSPath (2 * L)) (r : Fin L) : Prop :=
  (P.edge ⟨2 * r.1, by have := r.isLt; omega⟩).endpoint
    = (P.edge ⟨2 * r.1 + 1, by have := r.isLt; omega⟩).endpoint

/-- The number of c-pairs of a species-to-species path of length `2 * L`. -/
noncomputable def ssNumCPairsH {L : ℕ} (P : N.TrueSRSSPath (2 * L)) : ℕ := by
  classical
  exact (Finset.univ.filter (ssCPairAtH P)).card

/-- At length `2 * (j + 1)` — which is definitionally `2 * j + 2` — this is exactly
`ssNumCPairs`. -/
theorem ssNumCPairsH_eq {j : ℕ} (P : N.TrueSRSSPath (2 * (j + 1))) :
    ssNumCPairsH P = ssNumCPairs P := by
  classical
  unfold ssNumCPairsH ssNumCPairs
  apply congrArg Finset.card
  exact Finset.filter_congr fun r _ => Iff.rfl

end CRNT.Network.TrueSRSSPath

namespace CRNT.Network.TrueSRCycle

open Classical

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {n : ℕ}

/-- The c-pairs of `C` at indices `< m`: those seen by the forward species-arc. -/
noncomputable def cPairsBelow (C : N.TrueSRCycle n) (m : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter C.isCPair).filter fun i => i.1 < m

/-- The c-pairs of `C` at indices `≥ m`: those seen by the backward species-arc. -/
noncomputable def cPairsAbove (C : N.TrueSRCycle n) (m : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter C.isCPair).filter fun i => ¬ i.1 < m

private theorem mem_cPairsBelow (C : N.TrueSRCycle n) (m : ℕ) (i : Fin n)
    (h1 : C.isCPair i) (h2 : i.1 < m) : i ∈ cPairsBelow C m :=
  Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩, h2⟩

private theorem mem_cPairsAbove (C : N.TrueSRCycle n) (m : ℕ) (i : Fin n)
    (h1 : C.isCPair i) (h2 : ¬ i.1 < m) : i ∈ cPairsAbove C m :=
  Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩, h2⟩

/-- The reversed index of the `r`-th reaction of the backward arc is `≥ m`. -/
private theorem revPerm_ge_m (n m : ℕ) (hm : m < n) (r : Fin (n - m)) :
    m ≤ n - 1 - r.1 := by
  have hrl := r.isLt
  omega

/-- The c-pairs of `C` at indices `< m`, counted on the short index type `Fin m`, are
exactly `cPairsBelow C m`. -/
theorem cPairsBelow_short (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n)
    (s : Finset (Fin m)) (hiff : ∀ r : Fin m,
      (r ∈ s) ↔ C.isCPair ⟨r.1, Nat.lt_trans r.isLt hm⟩) :
    s.card = (cPairsBelow C m).card := by
  refine Finset.card_bij
    (s := s) (t := cPairsBelow C m) (fun r _ => ⟨r.1, Nat.lt_trans r.isLt hm⟩) ?_ ?_ ?_
  · intro r ha
    exact mem_cPairsBelow C m _ ((hiff r).mp ha) r.2
  · intro a _ b _ h
    exact Fin.ext (Fin.mk.inj h)
  · rintro b hb
    have hb1 : b ∈ Finset.univ.filter C.isCPair ∧ b.1 < m := Finset.mem_filter.mp hb
    have hb' : C.isCPair b ∧ b.1 < m := ⟨(Finset.mem_filter.mp hb1.1).2, hb1.2⟩
    refine ⟨⟨b.1, hb'.2⟩, (hiff ⟨b.1, hb'.2⟩).mpr hb'.1, ?_⟩
    apply Fin.ext
    rfl

/-- The c-pairs of `C` at indices `≥ m`, counted on the index type `Fin (n - m)`, are exactly
`cPairsAbove C m`. -/
theorem cPairsAbove_short (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n)
    (s : Finset (Fin (n - m))) (hiff : ∀ r : Fin (n - m),
      (r ∈ s) ↔ C.isCPair (revPerm n ⟨r.1, by omega⟩)) :
    s.card = (cPairsAbove C m).card := by
  refine Finset.card_bij
    (s := s) (t := cPairsAbove C m) (fun r _ => revPerm n ⟨r.1, by omega⟩) ?_ ?_ ?_
  · intro r ha
    exact mem_cPairsAbove C m _ ((hiff r).mp ha) (Nat.not_lt_of_ge (revPerm_ge_m n m hm r))
  · intro a _ b _ h
    exact Fin.ext (Fin.mk.inj ((revPerm n).symm.injective h))
  · rintro b hb
    have hbn := b.isLt
    have hb1 : b ∈ Finset.univ.filter C.isCPair ∧ ¬ b.1 < m := Finset.mem_filter.mp hb
    have hb' : C.isCPair b ∧ ¬ b.1 < m := ⟨(Finset.mem_filter.mp hb1.1).2, hb1.2⟩
    have hrl : n - 1 - b.1 < n - m := by omega
    have hbnd : n - 1 - b.1 < n := by omega
    have h2 : (revPerm n ⟨n - 1 - b.1, hbnd⟩ : Fin n) = b := by
      apply Fin.ext
      show n - 1 - (n - 1 - b.1) = b.1
      omega
    have hmem : C.isCPair (revPerm n ⟨n - 1 - b.1, hbnd⟩) := by rw [h2]; exact hb'.1
    exact ⟨⟨n - 1 - b.1, hrl⟩, (hiff _).mpr hmem, h2⟩

/-! ### The forward arc -/

/-- **The c-pair at the `r`-th reaction of the forward species-arc is the c-pair at `r`
of `C`.** -/
theorem ssCPairAtH_speciesArc (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n) (hmpos : 0 < m)
    (r : Fin m) :
    TrueSRSSPath.ssCPairAtH (C.speciesArc m hm hmpos) r
      ↔ C.isCPair ⟨r.1, Nat.lt_trans r.isLt hm⟩ := by
  have hq0 : (2 * r.1) % 2 = 0 := by omega
  have hq1 : (2 * r.1 + 1) % 2 ≠ 0 := by omega
  have hdiv0 : (2 * r.1) / 2 = r.1 := by omega
  have hdiv1 : (2 * r.1 + 1) / 2 = r.1 := by omega
  have he0 : (C.speciesArc m hm hmpos).edge ⟨2 * r.1, by omega⟩
      = C.leftEdge ⟨r.1, Nat.lt_trans r.isLt hm⟩ := by
    rw [speciesArc_edge_even C m hm hmpos ⟨2 * r.1, by omega⟩ hq0]
    exact congrArg _ (Fin.ext hdiv0)
  have he1 : (C.speciesArc m hm hmpos).edge ⟨2 * r.1 + 1, by omega⟩
      = C.rightEdge ⟨r.1, Nat.lt_trans r.isLt hm⟩ := by
    rw [speciesArc_edge_odd C m hm hmpos ⟨2 * r.1 + 1, by omega⟩ hq1]
    exact congrArg _ (Fin.ext hdiv1)
  constructor
  · intro h
    unfold TrueSRSSPath.ssCPairAtH at h
    rw [he0, he1] at h
    exact h
  · intro h
    unfold TrueSRSSPath.ssCPairAtH
    rw [he0, he1]
    exact h

/-- **The forward species-arc sees precisely the c-pairs of `C` at indices `< m`.** -/
theorem ssNumCPairsH_speciesArc (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n) (hmpos : 0 < m) :
    TrueSRSSPath.ssNumCPairsH (C.speciesArc m hm hmpos)
      = (Finset.univ.filter fun r : Fin m => C.isCPair ⟨r.1, Nat.lt_trans r.isLt hm⟩).card := by
  unfold TrueSRSSPath.ssNumCPairsH
  apply congrArg Finset.card
  exact Finset.filter_congr fun r _ => ssCPairAtH_speciesArc C m hm hmpos r

/-! ### The backward arc -/

/-- **The c-pair at the `r`-th reaction of the backward species-arc is the c-pair of `C` at
the reversed index `revPerm n r`.**  The two edges come out in the opposite order, so this
uses the symmetry of the endpoint equality. -/
theorem ssCPairAtH_speciesArcBwd (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n) (hmpos : 0 < m)
    (r : Fin (n - m)) :
    TrueSRSSPath.ssCPairAtH (C.speciesArcBwd m hm hmpos) r
      ↔ C.isCPair (revPerm n ⟨r.1, by omega⟩) := by
  have hrn : r.1 < n := by omega
  have hq0 : (2 * r.1) % 2 = 0 := by omega
  have hq1 : (2 * r.1 + 1) % 2 ≠ 0 := by omega
  have hdiv0 : (2 * r.1) / 2 = r.1 := by omega
  have hdiv1 : (2 * r.1 + 1) / 2 = r.1 := by omega
  have he0 : (C.speciesArcBwd m hm hmpos).edge ⟨2 * r.1, by omega⟩
      = C.rightEdge (revPerm n ⟨r.1, hrn⟩) := by
    rw [speciesArcBwd_edge_even C m hm hmpos ⟨2 * r.1, by omega⟩ hq0,
      show (revPerm n ⟨(2 * r.1) / 2, by omega⟩ : Fin n) = revPerm n ⟨r.1, hrn⟩ from
        congrArg _ (Fin.ext hdiv0)]
  have he1 : (C.speciesArcBwd m hm hmpos).edge ⟨2 * r.1 + 1, by omega⟩
      = C.leftEdge (revPerm n ⟨r.1, hrn⟩) := by
    rw [speciesArcBwd_edge_odd C m hm hmpos ⟨2 * r.1 + 1, by omega⟩ hq1,
      show (revPerm n ⟨(2 * r.1 + 1) / 2, by omega⟩ : Fin n) = revPerm n ⟨r.1, hrn⟩ from
        congrArg _ (Fin.ext hdiv1)]
  constructor
  · intro h
    unfold TrueSRSSPath.ssCPairAtH at h
    rw [he0, he1] at h
    exact h.symm
  · intro h
    unfold TrueSRSSPath.ssCPairAtH
    rw [he0, he1]
    exact h.symm

/-- **The backward species-arc sees precisely the c-pairs of `C` at indices `≥ m`.** -/
theorem ssNumCPairsH_speciesArcBwd (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n) (hmpos : 0 < m) :
    TrueSRSSPath.ssNumCPairsH (C.speciesArcBwd m hm hmpos)
      = (Finset.univ.filter fun r : Fin (n - m) =>
          C.isCPair (revPerm n ⟨r.1, by omega⟩)).card := by
  unfold TrueSRSSPath.ssNumCPairsH
  apply congrArg Finset.card
  exact Finset.filter_congr fun r _ => ssCPairAtH_speciesArcBwd C m hm hmpos r

/-! ### The partition -/

/-- The two index ranges `r < m` and `¬ r < m` partition the c-pairs of `C`. -/
theorem cPairsBelow_card_add (C : N.TrueSRCycle n) (m : ℕ) :
    (cPairsBelow C m).card + (cPairsAbove C m).card = C.numCPairs := by
  unfold cPairsBelow cPairsAbove TrueSRCycle.numCPairs
  exact Finset.card_filter_add_card_filter_not (s := Finset.univ.filter C.isCPair)
    (fun i : Fin n => i.1 < m)

/-- **The two species-arcs partition the c-pairs of `C`.** -/
theorem ssNumCPairsH_speciesArcs_add (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n) (hmpos : 0 < m) :
    TrueSRSSPath.ssNumCPairsH (C.speciesArc m hm hmpos)
      + TrueSRSSPath.ssNumCPairsH (C.speciesArcBwd m hm hmpos) = C.numCPairs := by
  rw [ssNumCPairsH_speciesArc, ssNumCPairsH_speciesArcBwd]
  have h1 : (Finset.univ.filter fun r : Fin m =>
      TrueSRSSPath.ssCPairAtH (C.speciesArc m hm hmpos) r).card = (cPairsBelow C m).card := by
    refine cPairsBelow_short C m hm _ (fun r => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ssCPairAtH_speciesArc C m hm hmpos r
  have h2 : (Finset.univ.filter fun r : Fin (n - m) =>
      TrueSRSSPath.ssCPairAtH (C.speciesArcBwd m hm hmpos) r).card = (cPairsAbove C m).card := by
    refine cPairsAbove_short C m hm _ (fun r => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ssCPairAtH_speciesArcBwd C m hm hmpos r
  have h3 : (Finset.univ.filter fun r : Fin m => TrueSRSSPath.ssCPairAtH (C.speciesArc m hm hmpos) r).card
      = (Finset.univ.filter fun r : Fin m => C.isCPair ⟨r.1, Nat.lt_trans r.isLt hm⟩).card := by
    apply congrArg Finset.card
    exact Finset.filter_congr fun r _ => ssCPairAtH_speciesArc C m hm hmpos r
  have h4 : (Finset.univ.filter fun r : Fin (n - m) => TrueSRSSPath.ssCPairAtH (C.speciesArcBwd m hm hmpos) r).card
      = (Finset.univ.filter fun r : Fin (n - m) => C.isCPair (revPerm n ⟨r.1, by omega⟩)).card := by
    apply congrArg Finset.card
    exact Finset.filter_congr fun r _ => ssCPairAtH_speciesArcBwd C m hm hmpos r
  calc (Finset.univ.filter fun r : Fin m => C.isCPair ⟨r.1, Nat.lt_trans r.isLt hm⟩).card
      + (Finset.univ.filter fun r : Fin (n - m) =>
          C.isCPair (revPerm n ⟨r.1, by omega⟩)).card
      = (cPairsBelow C m).card + (cPairsAbove C m).card :=
        (congrArg₂ (fun x y => x + y) h3.symm h4.symm).trans
          (congrArg₂ (fun x y => x + y) h1 h2)
    _ = C.numCPairs := cPairsBelow_card_add C m

/-! ### The `ssNumCPairs` vocabulary

`ssNumCPairs` is typed at `2 * j + 2`, and a species-arc of length `2 * m` is not of that form
definitionally.  Writing `m = k + 1` makes the *forward* arc fit (`2 * (k + 1)` is
definitionally `2 * k + 2`); for the backward arc one needs an explicit index equation, or
one keeps the length-agnostic `ssNumCPairsH` used above. -/

/-- **The two species-arcs partition the c-pairs of `C`, in the `ssNumCPairsH` count.** -/
theorem ssNumCPairsH_speciesArcs_add_succ (C : N.TrueSRCycle n) (k : ℕ) (hk : k + 1 < n) :
    TrueSRSSPath.ssNumCPairsH (C.speciesArc (k + 1) hk (by omega))
      + TrueSRSSPath.ssNumCPairsH (C.speciesArcBwd (k + 1) hk (by omega)) = C.numCPairs :=
  ssNumCPairsH_speciesArcs_add C (k + 1) hk (by omega)

/-- The forward species-arc's count is literally `ssNumCPairs`, at `m = k + 1`. -/
theorem ssNumCPairs_speciesArc_succ (C : N.TrueSRCycle n) (k : ℕ) (hk : k + 1 < n) :
    TrueSRSSPath.ssNumCPairs (C.speciesArc (k + 1) hk (by omega))
      = (cPairsBelow C (k + 1)).card := by
  rw [← TrueSRSSPath.ssNumCPairsH_eq]
  refine cPairsBelow_short C (k + 1) hk _ (fun r => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ssCPairAtH_speciesArc C (k + 1) hk (by omega) r

/-- **The two species-arcs partition the c-pairs of `C`** — the forward arc in the
`ssNumCPairs` vocabulary (at `m = k + 1`), the backward arc in `ssNumCPairsH`. -/
theorem ssNumCPairs_speciesArc_add (C : N.TrueSRCycle n) (k : ℕ) (hk : k + 1 < n) :
    TrueSRSSPath.ssNumCPairs (C.speciesArc (k + 1) hk (by omega))
      + TrueSRSSPath.ssNumCPairsH (C.speciesArcBwd (k + 1) hk (by omega)) = C.numCPairs := by
  rw [ssNumCPairs_speciesArc_succ C k hk]
  have hc := ssNumCPairsH_speciesArcBwd C (k + 1) hk (by omega)
  rw [hc]
  have habove : (Finset.univ.filter fun r : Fin (n - (k + 1)) =>
      C.isCPair (revPerm n ⟨r.1, by omega⟩)).card = (cPairsAbove C (k + 1)).card := by
    refine cPairsAbove_short C (k + 1) hk _ (fun r => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (congrArg₂ (fun x y => x + y) rfl habove).trans (cPairsBelow_card_add C (k + 1))

/-- **If `C` is an e-cycle, the two species-arcs have c-pair counts of the same parity**, in
the `ssNumCPairs`/`ssNumCPairsH` mix. -/
theorem speciesArcs_sum_even (C : N.TrueSRCycle n) (k : ℕ) (hk : k + 1 < n) (hC : C.Even) :
    (TrueSRSSPath.ssNumCPairs (C.speciesArc (k + 1) hk (by omega))
      + TrueSRSSPath.ssNumCPairsH (C.speciesArcBwd (k + 1) hk (by omega))) % 2 = 0 := by
  rw [ssNumCPairs_speciesArc_add C k hk]
  exact Nat.even_iff.mp hC

/-- **If `C` is an e-cycle, the two species-arcs have c-pair counts of the same parity.** -/
theorem speciesArcs_sum_evenH (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n) (hmpos : 0 < m)
    (hC : C.Even) :
    (TrueSRSSPath.ssNumCPairsH (C.speciesArc m hm hmpos)
      + TrueSRSSPath.ssNumCPairsH (C.speciesArcBwd m hm hmpos)) % 2 = 0 := by
  rw [ssNumCPairsH_speciesArcs_add]
  exact Nat.even_iff.mp hC

/-- **The backward species-arc's count is the number of c-pairs of `C` at indices `≥ m`.**
This is the single place where the `Fin (n - m)` index type of the backward arc is converted
into `cPairsAbove`'s `Fin n` index type; every downstream statement about the parity of the
backward arc goes through it. -/
theorem ssNumCPairsH_speciesArcBwd_eq_cPairsAbove (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n)
    (hmpos : 0 < m) :
    TrueSRSSPath.ssNumCPairsH (C.speciesArcBwd m hm hmpos) = (cPairsAbove C m).card := by
  refine cPairsAbove_short C m hm _ (fun r => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ssCPairAtH_speciesArcBwd C m hm hmpos r

/-! ### The parity transfer

`TrueSRSSPath.ssNumCPairsH_eq ` needs the path at `2 * (j + 1)`, and a transport `L = L'` therefore has to be
absorbed.  It is absorbed by `cases h; rfl`: the length index is what `▸` rewrites, so after
the equation is gone the two paths are the same term. -/

/-- `ssNumCPairsH` is invariant under transport of the length index. -/
theorem TrueSRSSPath.ssNumCPairsH_cast  {L L' : ℕ} (P : N.TrueSRSSPath (2 * L)) (h : L = L') :
    TrueSRSSPath.ssNumCPairsH (L := L') (h ▸ P) = TrueSRSSPath.ssNumCPairsH (L := L) P := by
  cases h
  rfl

/-- **The species-to-species parity transfer.**  Gluing a species-to-species path `P` to the
two species-arcs of an e-cycle `C` gives two cycles that are either both even or both odd:
`TrueSRSSPath.ssGlueCycle_even_iff_even` compares them modulo `2`, and the two arcs' c-pair counts sum to
`C.numCPairs ≡ 0`. -/
theorem TrueSRSSPath.ssGlueCycle_even_iff_even_arcs {S : Type} [DecidableEq S] [Fintype S]
    {N : Network S} {n : ℕ} (C : N.TrueSRCycle n) (k i₂ : ℕ) (hk : k + 1 < n)
    (hj : n - (k + 1) = i₂ + 1)
    (h₁ : TrueSRSSPath.SSGluable (C.speciesArc (k + 1) hk (by omega)) (C.speciesArc (k + 1) hk (by omega)))
    (h₂ : TrueSRSSPath.SSGluable (C.speciesArc (k + 1) hk (by omega))
      (hj ▸ (C.speciesArcBwd (k + 1) hk (by omega))))
    (hC : C.Even) :
    (TrueSRSSPath.ssGlueCycle (C.speciesArc (k + 1) hk (by omega))
        (C.speciesArc (k + 1) hk (by omega)) h₁).Even
      ↔ (TrueSRSSPath.ssGlueCycle (C.speciesArc (k + 1) hk (by omega))
        (hj ▸ (C.speciesArcBwd (k + 1) hk (by omega))) h₂).Even := by
  have hQ : (TrueSRSSPath.ssNumCPairs (C.speciesArc (k + 1) hk (by omega))
      + TrueSRSSPath.ssNumCPairs (hj ▸ (C.speciesArcBwd (k + 1) hk (by omega)))) % 2 = 0 := by
    have hH := speciesArcs_sum_evenH C (k + 1) hk (by omega) hC
    have e1 := (TrueSRSSPath.ssNumCPairsH_eq  (j := k) (C.speciesArc (k + 1) hk (by omega))).symm
    have e2 := (TrueSRSSPath.ssNumCPairsH_eq  (j := i₂)
      (hj ▸ (C.speciesArcBwd (k + 1) hk (by omega)))).symm
    have e3 : TrueSRSSPath.ssNumCPairsH (hj ▸ (C.speciesArcBwd (k + 1) hk (by omega)))
        = TrueSRSSPath.ssNumCPairsH (C.speciesArcBwd (k + 1) hk (by omega)) :=
      TrueSRSSPath.ssNumCPairsH_cast  _ hj
    rw [e1, e2, e3]
    exact hH
  exact TrueSRSSPath.ssGlueCycle_even_iff_even _ _ _ h₁ h₂ hQ

end CRNT.Network.TrueSRCycle