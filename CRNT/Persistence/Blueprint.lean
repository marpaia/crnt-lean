import CRNT.Persistence.NestedEnvelope
import CRNT.Persistence.Arrangement
import CRNT.Persistence.ColumnSegments
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD

/-!
# Construction of the blueprint tree

Given a tower of affine arrangements `A j` (on `j + 1` coordinates) whose projections land in the
level below and which contains the walls `p₀ = 1`, `p_j = p_{j-1}`, `build` produces a blueprint
tree of depth `d`.  Over a base point `b` with feature-size bound `lam`, the column consists of a
section segment of half-width `w = θ c lam / (1 + L)` around every section value of `A j` in
`[wall, B + 1]`, band pieces of length at most `θ w / (1 + L)` in between, and a top segment.
Section children get feature size `c lam / (1 + L)` (gap lemma), band children `w / (1 + L)`.

`build_spec` proves, by induction on the depth, that the tree is well formed for the envelope
argument, proper (every reachable column ends with a top segment beyond `B + 1/2`), has positive
sibling gaps with all basepoints in `[0, B + 3]`, and that at every leaf reached through
non-top nodes the accumulated radius is at most half of a feature-size bound of the leaf
basepoint in the top arrangement.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Persistence

open Finset BTree

/-- The wall functional at level `j`. -/
noncomputable def wallFn (j : ℕ) : Aff :=
  if j = 0 then ⟨fun l => if l = 0 then 1 else 0, -1⟩
  else ⟨fun l => if l = j then 1 else if l + 1 = j then -1 else 0, 0⟩

theorem wallFn_α (j : ℕ) : (wallFn j).α j = 1 := by
  unfold wallFn; split_ifs with h <;> simp [h]

theorem sec_wallFn (j : ℕ) (b : ℕ → ℝ) :
    Aff.sec j (wallFn j) b = if j = 0 then 1 else b (j - 1) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [Aff.sec, wallFn]
  · rw [if_neg hj.ne']
    unfold Aff.sec
    rw [wallFn_α, div_one]
    simp only [wallFn, if_neg hj.ne']
    have : ∑ l ∈ range j, (if l = j then (1:ℝ) else if l + 1 = j then -1 else 0) * b l =
        -b (j - 1) := by
      rw [Finset.sum_eq_single (j - 1)]
      · rw [if_neg (by omega), if_pos (by omega)]; ring
      · intro l hl hne
        rw [if_neg (by simp at hl; omega), if_neg (by omega), zero_mul]
      · intro h; simp at h; omega
    rw [this]; ring

/-- Hypotheses on the tower. -/
structure TowerOK (A : ℕ → List Aff) (m : ℕ) (c L : ℝ) : Prop where
  proj_sub : ∀ j, j + 1 < m → ∀ g ∈ proj (j + 1) (A (j + 1)), g ∈ A j
  wall_mem : ∀ j, j < m → wallFn j ∈ A j
  c_pos : 0 < c
  c_le : c ≤ 1
  L_ge : 1 ≤ L
  gap : ∀ j, j < m → ∀ g ∈ A j, ∀ g' ∈ A j,
      (0 < Aff.norm1 j (Aff.diff j g g') → c ≤ Aff.norm1 j (Aff.diff j g g')) ∧
      ((Aff.diff j g g').c ≠ 0 → c ≤ |(Aff.diff j g g').c|)
  slope : ∀ j, j < m → ∀ g ∈ A j, g.α j ≠ 0 → Aff.norm1 j g ≤ L * |g.α j|

/-- The scale constants: `ν 0 = 1/2`, `ν (d+1) = ν d ^ 2 * c / (2 (1 + L)^2)`. -/
noncomputable def nu (c L : ℝ) : ℕ → ℝ
  | 0 => 1 / 2
  | d + 1 => nu c L d ^ 2 * c / (2 * (1 + L) ^ 2)

theorem nu_pos {c L : ℝ} (hc : 0 < c) (hL : 1 ≤ L) : ∀ d, 0 < nu c L d
  | 0 => by simp [nu]
  | d + 1 => by have := nu_pos hc hL d; simp only [nu]; positivity

theorem nu_le_half {c L : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hL : 1 ≤ L) :
    ∀ d, nu c L d ≤ 1 / 2
  | 0 => by simp [nu]
  | d + 1 => by
      have h := nu_le_half hc hc1 hL d
      have hp := nu_pos hc hL d
      simp only [nu]
      rw [div_le_iff₀ (by positivity)]
      have : nu c L d ^ 2 ≤ 1 / 4 := by nlinarith
      have h2 : 1 ≤ (1 + L) ^ 2 := by nlinarith
      nlinarith

/-- A chain of single-node columns (used under top segments). -/
noncomputable def chainTree : (d : ℕ) → ℝ → BTree d
  | 0, _ => .leaf
  | d + 1, v => .node 1 (fun _ => v) (fun _ => v) (fun _ => v) (fun _ => chainTree d v)

noncomputable instance : DecidableEq Aff := Classical.decEq _

/-- The wall value of the column at level `j` over `b`. -/
noncomputable def wallVal (j : ℕ) (b : ℕ → ℝ) : ℝ := if j = 0 then 1 else b (j - 1)

/-- The sorted section values strictly above the wall and at most `B + 1`. -/
noncomputable def secVals (A : ℕ → List Aff) (B : ℝ) (j : ℕ) (b : ℕ → ℝ) : List ℝ :=
  ((((A j).toFinset.filter fun g => g.α j ≠ 0 ∧ wallVal j b < Aff.sec j g b ∧
      Aff.sec j g b ≤ B + 1)).image fun g => Aff.sec j g b).sort

/-- The column list. -/
noncomputable def colList (A : ℕ → List Aff) (B : ℝ) (j : ℕ) (b : ℕ → ℝ) (w ℓ : ℝ) :
    List Seg :=
  colSegs w ℓ (max ((wallVal j b :: secVals A B j b).getLast (by simp) + w) (B + 1 / 2))
    (wallVal j b :: secVals A B j b)

/-- The blueprint tree. -/
noncomputable def build (A : ℕ → List Aff) (B c L : ℝ) :
    (d : ℕ) → ℕ → (ℕ → ℝ) → ℝ → ℝ → BTree d
  | 0, _, _, _, _ => .leaf
  | d + 1, j, b, lam, ρ =>
      let w := nu c L d * c * lam / (1 + L)
      let segs := colList A B j b w (nu c L d * w / (1 + L))
      let sg := fun i => segs.getD i (topSeg 0)
      .node segs.length (fun i => (sg i).β) (fun i => (sg i).lo) (fun i => (sg i).hi)
        (fun i => if (sg i).kind = SegKind.top then chainTree d (sg i).β
          else build A B c L d (j + 1) (Function.update b j (sg i).β)
            (if (sg i).kind = SegKind.sec then c * lam / (1 + L) else w / (1 + L))
            (nodeRad ρ segs.length (fun i => (sg i).β) (fun i => (sg i).hi) i))

/-! ### Properties along paths -/

/-- Proper: every reachable column has at least two nodes and ends beyond `B + 1/2`. -/
def Proper (B : ℝ) : {d : ℕ} → BTree d → Prop
  | _, .leaf => True
  | _, .node n _ _ hi sub => 2 ≤ n ∧ B + 1 / 2 ≤ hi (n - 2) ∧ ∀ i, i + 1 < n → Proper B (sub i)

/-- A property `Q` of the accumulated basepoint and radius at every leaf reached through
non-last nodes. -/
def LeafProp (Q : (ℕ → ℝ) → ℝ → Prop) : {d : ℕ} → ℕ → (ℕ → ℝ) → ℝ → BTree d → Prop
  | _, _, b, ρ, .leaf => Q b ρ
  | _, j, b, ρ, .node n β _ hi sub => ∀ i, i + 1 < n →
      LeafProp Q (j + 1) (Function.update b j (β i)) (nodeRad ρ n β hi i) (sub i)

/-- All sibling gaps are positive and all basepoint values lie in `[0, Bβ]`. -/
def GapsPos (Bβ : ℝ) : {d : ℕ} → BTree d → Prop
  | _, .leaf => True
  | _, .node n β _ _ sub => (∀ i, i < n → 0 ≤ β i ∧ β i ≤ Bβ) ∧
      (∀ i, i + 1 < n → β i < β (i + 1)) ∧ ∀ i, i < n → GapsPos Bβ (sub i)

theorem Bounded.mono {Bβ Δ Δ' : ℝ} (hΔ : Δ' ≤ Δ) : ∀ {d : ℕ} (t : BTree d),
    Bounded Bβ Δ t → Bounded Bβ Δ' t
  | _, .leaf, _ => trivial
  | _, .node n β lo hi sub, h =>
      ⟨h.1, fun i hi' => le_trans hΔ (h.2.1 i hi'), fun i hi' => Bounded.mono hΔ (sub i) (h.2.2 i hi')⟩

theorem exists_bounded_of_gapsPos {Bβ : ℝ} : ∀ {d : ℕ} (t : BTree d), GapsPos Bβ t →
    ∃ Δ, 0 < Δ ∧ Bounded Bβ Δ t
  | _, .leaf, _ => ⟨1, one_pos, trivial⟩
  | _, .node n β lo hi sub, h => by
      have hsub : ∀ i, i < n → ∃ Δ, 0 < Δ ∧ Bounded Bβ Δ (sub i) :=
        fun i hi' => exists_bounded_of_gapsPos (sub i) (h.2.2 i hi')
      choose! Δs hΔs using hsub
      obtain ⟨Δ, hΔ, _, hle⟩ := exists_pos_le_of_forall_pos (List.range n)
        (fun i => min (Δs i) (if i + 1 < n then β (i + 1) - β i else 1)) (by
          intro i hi'
          simp at hi'
          refine lt_min (hΔs i hi').1 ?_
          split_ifs with h' <;> [linarith [h.2.1 i h']; exact one_pos])
      refine ⟨Δ, hΔ, h.1, fun i hi' => ?_, fun i hi' => ?_⟩
      · have := hle i (by simp; omega)
        rw [if_pos hi'] at this
        exact le_trans this (min_le_right _ _)
      · have := hle i (by simpa using hi')
        exact Bounded.mono (le_trans this (min_le_left _ _)) _ (hΔs i hi').2

theorem chainTree_props (Bβ : ℝ) : ∀ (d : ℕ) (v ρ : ℝ), 0 ≤ v → v ≤ Bβ →
    WF (chainTree d v) v ρ ∧ GapsPos Bβ (chainTree d v)
  | 0, _, _, _, _ => ⟨trivial, trivial⟩
  | d + 1, v, ρ, h0, h1 => by
      refine ⟨⟨le_rfl, rfl, fun i hi => by omega, fun h => by omega, fun i hi => ?_⟩,
        ⟨fun i _ => ⟨h0, h1⟩, fun i hi => by omega, fun i hi => ?_⟩⟩
      · exact (chainTree_props Bβ d v _ h0 h1).1
      · exact (chainTree_props Bβ d v 0 h0 h1).2


theorem mem_secVals {A : ℕ → List Aff} {B : ℝ} {j : ℕ} {b : ℕ → ℝ} {z : ℝ} :
    z ∈ secVals A B j b ↔ ∃ g ∈ A j, g.α j ≠ 0 ∧ wallVal j b < Aff.sec j g b ∧
      Aff.sec j g b ≤ B + 1 ∧ Aff.sec j g b = z := by
  simp only [secVals, Finset.mem_sort, Finset.mem_image, Finset.mem_filter, List.mem_toFinset]
  constructor
  · rintro ⟨g, ⟨hg, h1, h2, h3⟩, rfl⟩; exact ⟨g, hg, h1, h2, h3, rfl⟩
  · rintro ⟨g, hg, h1, h2, h3, rfl⟩; exact ⟨g, ⟨hg, h1, h2, h3⟩, rfl⟩

theorem wallVal_eq_sec (j : ℕ) (b : ℕ → ℝ) : wallVal j b = Aff.sec j (wallFn j) b := by
  rw [sec_wallFn]; rfl

/-- Everything we need to know about one column. -/
theorem col_facts {A : ℕ → List Aff} {m : ℕ} {B c L : ℝ} (hT : TowerOK A m c L) (hB : 1 ≤ B)
    {j : ℕ} (hj : j < m) {b : ℕ → ℝ} {lam θ : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2)
    (hwall : 1 ≤ wallVal j b ∧ wallVal j b ≤ B + 1)
    (hlfs : LfsGe j (proj j (A j)) b lam) :
    let w := θ * c * lam / (1 + L)
    let segs := colList A B j b w (θ * w / (1 + L))
    List.IsChain SegRel segs ∧ segs.head? = some (secSeg w (wallVal j b)) ∧
    (∃ T, B + 1 / 2 ≤ T ∧ T ≤ B + 2 ∧ ∃ Lst, segs = Lst ++ [topSeg T] ∧
      ∀ s ∈ Lst, s.kind ≠ SegKind.top) ∧
    (∀ s ∈ segs, s.kind = SegKind.sec →
      LfsGe (j + 1) (A j) (Function.update b j s.β) (c * lam / (1 + L)) ∧
      s.lo = s.β - w ∧ s.hi = s.β + w ∧ 1 ≤ s.β ∧ s.β ≤ B + 1) ∧
    (∀ s ∈ segs, s.kind = SegKind.band →
      LfsGe (j + 1) (A j) (Function.update b j s.β) (w / (1 + L)) ∧
      s.hi - s.lo ≤ θ * w / (1 + L) ∧ 2 * s.β = s.lo + s.hi ∧ s.lo < s.β ∧ s.β < s.hi ∧
      1 ≤ s.β ∧ s.β ≤ B + 1) ∧
    (∀ s ∈ segs, 0 ≤ s.β ∧ s.β ≤ B + 3) := by
  intro w segs
  have hc := hT.c_pos; have hc1 := hT.c_le; have hL := hT.L_ge
  have h1L : 0 < 1 + L := by linarith
  have hw0 : 0 < w := by positivity
  have hw4 : 4 * w ≤ c * lam := by
    show 4 * (θ * c * lam / (1 + L)) ≤ c * lam
    rw [mul_div_assoc', div_le_iff₀ h1L]; nlinarith [mul_pos hc hlam0]
  have hwq : w ≤ 1 / 4 := by
    have : c * lam ≤ 1 := by nlinarith
    linarith
  have hℓ0 : 0 < θ * w / (1 + L) := by positivity
  set v0 := wallVal j b with hv0
  set vals := secVals A B j b with hvals
  -- every element of `v0 :: vals` is a section value of a non-vertical functional
  have hsecof : ∀ z ∈ v0 :: vals, ∃ g ∈ A j, g.α j ≠ 0 ∧ Aff.sec j g b = z ∧ z ≤ B + 1 := by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨wallFn j, hT.wall_mem j hj, by rw [wallFn_α]; norm_num,
        (wallVal_eq_sec j b).symm, hwall.2⟩
    · obtain ⟨g, hg, h1, _, h3, h4⟩ := mem_secVals.mp hz
      exact ⟨g, hg, h1, h4, h4 ▸ h3⟩
  have hge_v0 : ∀ z ∈ v0 :: vals, v0 ≤ z := by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact le_rfl
    · obtain ⟨g, _, _, h2, _, h4⟩ := mem_secVals.mp hz; rw [← h4]; exact h2.le
  have hgap : ∀ z ∈ v0 :: vals, ∀ z' ∈ v0 :: vals, z ≠ z' → c * lam ≤ |z - z'| := by
    intro z hz z' hz' hne
    obtain ⟨g, hg, hgv, rfl, _⟩ := hsecof z hz
    obtain ⟨g', hg', hgv', rfl, _⟩ := hsecof z' hz'
    exact gap_ge (hT.gap j hj) hc.le hlam1 hlam0.le hlfs hg hg' hne
  have hchain : List.IsChain (fun a b => a + 4 * w ≤ b) (v0 :: vals) := by
    have hlt : List.IsChain (· < ·) (v0 :: vals) := by
      have hp : List.Pairwise (· < ·) vals :=
        List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort _)
      refine List.Pairwise.isChain (List.pairwise_cons.mpr ⟨?_, hp⟩)
      intro z hz
      obtain ⟨g, _, _, h2, _, h4⟩ := mem_secVals.mp hz; rw [← h4]; exact h2
    refine List.IsChain.imp_of_mem_imp ?_ hlt
    intro a a' ha ha' hlt'
    have := hgap a ha a' ha' hlt'.ne
    rw [abs_of_neg (by linarith)] at this; linarith
  set T := max ((v0 :: vals).getLast (by simp) + w) (B + 1 / 2) with hTdef
  have hlastT : (v0 :: vals).getLast (by simp) + w ≤ T := le_max_left _ _
  have hlastB : (v0 :: vals).getLast (by simp) ≤ B + 1 := by
    obtain ⟨_, _, _, _, h⟩ := hsecof _ (List.getLast_mem (l := v0 :: vals) (by simp)); exact h
  have hTB : B + 1 / 2 ≤ T := le_max_right _ _
  have hTB2 : T ≤ B + 2 := max_le (by linarith) (by linarith)
  have hsegs : segs = colSegs w (θ * w / (1 + L)) T (v0 :: vals) := rfl
  obtain ⟨pc, ph, ⟨Lst, hLst, hLtop⟩, psec, pband, pβ⟩ :=
    colSegs_props w (θ * w / (1 + L)) T hw0 hℓ0 v0 vals hchain hlastT
  rw [← hsegs] at pc ph hLst psec pband pβ
  refine ⟨pc, ph, ⟨T, hTB, hTB2, Lst, hLst, hLtop⟩, ?_, ?_, ?_⟩
  · intro s hs hk
    obtain ⟨hmem, hlo, hhi⟩ := psec s hs hk
    obtain ⟨g0, hg0, hg0v, hg0s, hle⟩ := hsecof _ hmem
    refine ⟨?_, hlo, hhi, le_trans hwall.1 (hge_v0 _ hmem), hle⟩
    have hupd := lfsGe_update (k := j) (A := A j) (b' := b) (lam := lam) (d0 := c * lam)
      (L := L) (β := s.β) (by linarith) (by positivity) (hT.slope j hj) hlfs (by
        intro g hg hgv hne
        rw [← hg0s, abs_sub_comm]
        exact gap_ge (hT.gap j hj) hc.le hlam1 hlam0.le hlfs hg hg0 (by rw [hg0s]; exact hne))
    refine hupd.mono (le_min ?_ le_rfl)
    rw [div_le_iff₀ h1L]; nlinarith
  · intro s hs hk
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := pband s hs hk
    have hβB : s.β ≤ B + 1 - w := by
      rcases h8 with h8 | h8
      · linarith
      · have hTgt : (v0 :: vals).getLast (by simp) + w < T := by linarith
        have hTeq : T = B + 1 / 2 := by
          rcases le_total ((v0 :: vals).getLast (by simp) + w) (B + 1 / 2) with h | h
          · rw [hTdef, max_eq_right h]
          · rw [hTdef, max_eq_left h] at hTgt; linarith
        linarith
    refine ⟨?_, h5, h6, h2, h3, by linarith [hwall.1, hw0], by linarith⟩
    have hupd := lfsGe_update (k := j) (A := A j) (b' := b) (lam := lam) (d0 := w)
      (L := L) (β := s.β) (by linarith) hw0.le (hT.slope j hj) hlfs (by
        intro g hg hgv hne
        by_cases hlow : Aff.sec j g b ≤ v0
        · rw [abs_of_nonneg (by linarith)]; linarith
        · push Not at hlow
          by_cases hhigh : Aff.sec j g b ≤ B + 1
          · exact h7 _ (List.mem_cons_of_mem _ (mem_secVals.mpr ⟨g, hg, hgv, hlow, hhigh, rfl⟩))
          · push Not at hhigh
            rw [abs_of_neg (by linarith)]; linarith)
    refine hupd.mono (le_min ?_ le_rfl)
    show θ * c * lam / (1 + L) / (1 + L) ≤ lam
    rw [div_div, div_le_iff₀ (by positivity)]
    have : (1:ℝ) ≤ (1 + L) * (1 + L) := by nlinarith
    nlinarith [mul_pos hθ0 hc]
  · intro s hs
    have hβ0 := pβ s hs
    refine ⟨by linarith [hwall.1], ?_⟩
    rw [hLst] at hs
    rcases List.mem_append.mp hs with hs | hs
    · have hk := hLtop s hs
      have hs' : s ∈ segs := by rw [hLst]; exact List.mem_append_left _ hs
      cases hkind : s.kind with
      | sec =>
          obtain ⟨hmem, _⟩ := psec s hs' hkind
          obtain ⟨_, _, _, _, h⟩ := hsecof _ hmem
          linarith
      | band =>
          obtain ⟨_, _, h3, h4, _, _, _, _⟩ := pband s hs' hkind
          linarith
      | top => exact absurd hkind hk
    · simp at hs; subst hs; simp [topSeg]; linarith


/-- The leaf feature-size factor. -/
noncomputable def lamFactor (c L : ℝ) : ℕ → ℝ
  | 0 => 1
  | d + 1 => nu c L d * c / (1 + L) ^ 2 * lamFactor c L d

theorem lamFactor_pos {c L : ℝ} (hc : 0 < c) (hL : 1 ≤ L) : ∀ d, 0 < lamFactor c L d
  | 0 => one_pos
  | d + 1 => by
      have := nu_pos hc hL d; have := lamFactor_pos hc hL d
      simp only [lamFactor]; positivity

theorem LeafProp.mono {Q Q' : (ℕ → ℝ) → ℝ → Prop} (hQ : ∀ b ρ, Q b ρ → Q' b ρ) :
    ∀ {d : ℕ} (j : ℕ) (b : ℕ → ℝ) (ρ : ℝ) (t : BTree d), LeafProp Q j b ρ t →
      LeafProp Q' j b ρ t
  | _, _, b, ρ, .leaf, h => hQ b ρ h
  | _, j, b, ρ, .node n β lo hi sub, h => fun i hi' => LeafProp.mono hQ _ _ _ (sub i) (h i hi')

/-- The base arrangement of level `j`. -/
def Abase (A : ℕ → List Aff) (j : ℕ) : List Aff := if j = 0 then [] else A (j - 1)

theorem lfsGe_zero (A : List Aff) (b : ℕ → ℝ) (lam : ℝ) : LfsGe 0 A b lam := by
  intro g _ _; simp [Aff.norm1]

theorem lfsGe_of_subset {k : ℕ} {A A' : List Aff} (h : ∀ g ∈ A', g ∈ A) {b : ℕ → ℝ} {lam : ℝ}
    (hL : LfsGe k A b lam) : LfsGe k A' b lam := fun g hg hne => hL g (h g hg) hne

theorem nodeRad_le {ρ r : ℝ} {n : ℕ} {β hi : ℕ → ℝ} {i : ℕ} (hρ : ρ ≤ r) (hr : 0 ≤ r)
    (h1 : i + 1 < n → hi i - β i ≤ r) (h2 : 0 < i → β i - hi (i - 1) ≤ r) :
    nodeRad ρ n β hi i ≤ r := by
  unfold nodeRad
  refine max_le hρ (max_le ?_ ?_)
  · split_ifs with h <;> [exact h1 h; exact hr]
  · split_ifs with h <;> [exact h2 h; exact hr]

theorem build_spec {A : ℕ → List Aff} {m : ℕ} {B c L : ℝ} (hT : TowerOK A m c L)
    (hB : 1 ≤ B) (hm : 1 ≤ m) :
    ∀ (d j : ℕ), j + d = m → ∀ (b : ℕ → ℝ) (lam ρ : ℝ),
    LfsGe j (Abase A j) b lam → 0 < lam → lam ≤ 1 → 0 ≤ ρ → ρ ≤ nu c L d * lam →
    1 ≤ wallVal j b → wallVal j b ≤ B + 1 →
    WF (build A B c L d j b lam ρ) (wallVal j b) ρ ∧ Proper B (build A B c L d j b lam ρ) ∧
    GapsPos (B + 3) (build A B c L d j b lam ρ) ∧
    LeafProp (fun b' ρ' => ∃ lam', lam * lamFactor c L d ≤ lam' ∧
        LfsGe m (A (m - 1)) b' lam' ∧ ρ' ≤ lam' / 2) j b ρ (build A B c L d j b lam ρ) := by
  have hc := hT.c_pos; have hc1 := hT.c_le; have hL := hT.L_ge
  have h1L : 0 < 1 + L := by linarith
  intro d
  induction d with
  | zero =>
      intro j hj b lam ρ hlfs hlam0 hlam1 hρ0 hρ _ _
      simp only [Nat.add_zero] at hj; subst hj
      refine ⟨trivial, trivial, trivial, ⟨lam, by simp [lamFactor], ?_, by simp only [nu] at hρ; linarith⟩⟩
      have : Abase A j = A (j - 1) := by simp [Abase]; omega
      rwa [this] at hlfs
  | succ d ih =>
      intro j hj b lam ρ hlfs hlam0 hlam1 hρ0 hρ hw1 hw2
      have hjm : j < m := by omega
      set θ := nu c L d with hθdef
      have hθ0 : 0 < θ := nu_pos hc hL d
      have hθ : θ ≤ 1 / 2 := nu_le_half hc hc1 hL d
      have hlfs' : LfsGe j (proj j (A j)) b lam := by
        rcases Nat.eq_zero_or_pos j with h0 | hpos
        · subst h0; exact lfsGe_zero _ _ _
        · have hAb : Abase A j = A (j - 1) := by simp [Abase]; omega
          rw [hAb] at hlfs
          refine lfsGe_of_subset ?_ hlfs
          intro g hg
          have := hT.proj_sub (j - 1) (by omega) g
          rw [Nat.sub_add_cancel hpos] at this
          exact this hg
      obtain ⟨pc, ph, ⟨T, hTB, hTB2, Lst, hLst, hLtop⟩, psec, pband, pβ⟩ :=
        col_facts hT hB hjm hlam0 hlam1 hθ0 hθ ⟨hw1, hw2⟩ hlfs'
      set w := θ * c * lam / (1 + L) with hwdef
      have hw0 : 0 < w := by positivity
      set ℓ := θ * w / (1 + L) with hℓdef
      set segs := colList A B j b w ℓ with hsegsdef
      have hρw : ρ ≤ w / 2 := by
        have e : nu c L (d + 1) * lam = (w / 2) * (θ / (1 + L)) := by
          simp only [nu, ← hθdef, hwdef]; field_simp
        have hq : θ / (1 + L) ≤ 1 := by rw [div_le_one h1L]; linarith
        have hw2 : 0 ≤ w / 2 := by positivity
        calc ρ ≤ _ := hρ
          _ = _ := e
          _ ≤ w / 2 * 1 := mul_le_mul_of_nonneg_left hq hw2
          _ = w / 2 := mul_one _
      have hρℓ : ρ ≤ ℓ / 2 := by
        refine le_trans hρ (le_of_eq ?_)
        simp only [nu, ← hθdef, hℓdef, hwdef]; field_simp
      -- indexing
      have hlen : 2 ≤ segs.length := by
        rw [hLst, List.length_append, List.length_singleton]
        rcases Lst with _ | ⟨s0, Lst'⟩
        · exfalso; rw [hLst] at ph; simp [topSeg, secSeg] at ph
        · simp
      set n := segs.length with hn
      set sg := fun i => segs.getD i (topSeg 0) with hsg
      have hget : ∀ i (hi : i < n), sg i = segs[i] := fun i hi => List.getD_eq_getElem (l := segs) (d := topSeg 0) hi
      have hmemi : ∀ i, i < n → sg i ∈ segs := fun i hi => by rw [hget i hi]; exact List.getElem_mem _
      have hrel : ∀ i, i + 1 < n → SegRel (sg i) (sg (i + 1)) := by
        intro i hi
        rw [hget i (by omega), hget (i + 1) hi]
        exact List.isChain_iff_getElem.mp pc i hi
      have hlast : sg (n - 1) = topSeg T := by
        rw [hget (n - 1) (by omega)]
        simp only [hn, hLst]
        rw [List.getElem_append_right (by simp)]
        simp
      have hnontop : ∀ i, i + 1 < n → (sg i).kind ≠ SegKind.top := by
        intro i hi
        rw [hget i (by omega)]
        have hiL : i < Lst.length := by
          have : n = Lst.length + 1 := by simp [hn, hLst]
          omega
        simp only [hLst]
        rw [List.getElem_append_left hiL]
        exact hLtop _ (List.getElem_mem _)
      have hsg0 : sg 0 = secSeg w (wallVal j b) := by
        rw [hget 0 (by omega)]
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at ph
        exact Option.some.inj ph
      -- the radius of each non-top child
      have hrad : ∀ i, i < n → (sg i).kind ≠ SegKind.top →
          nodeRad ρ n (fun i => (sg i).β) (fun i => (sg i).hi) i ≤
            θ * (if (sg i).kind = SegKind.sec then c * lam / (1 + L) else w / (1 + L)) := by
        intro i hi hk
        have hlo : 0 < i → (sg (i - 1)).hi = (sg i).lo := by
          intro hpos
          have := (hrel (i - 1) (by omega)).1
          rwa [Nat.sub_add_cancel hpos] at this
        cases hkind : (sg i).kind with
        | top => exact absurd hkind hk
        | sec =>
            obtain ⟨_, hlo', hhi', _⟩ := psec (sg i) (hmemi i hi) hkind
            rw [if_pos rfl]
            have hr : θ * (c * lam / (1 + L)) = w := by rw [hwdef]; ring
            rw [hr]
            refine nodeRad_le (by linarith) hw0.le (fun _ => by linarith) ?_
            intro hpos; rw [hlo hpos]; linarith
        | band =>
            obtain ⟨_, h5, h6, _, _, _⟩ := pband (sg i) (hmemi i hi) hkind
            rw [if_neg (by simp)]
            have hr : θ * (w / (1 + L)) = ℓ := by rw [hℓdef]; ring
            rw [hr]
            have hℓ0 : 0 < ℓ := by positivity
            refine nodeRad_le (by linarith) hℓ0.le (fun _ => by linarith) ?_
            intro hpos; rw [hlo hpos]; linarith
      -- the invariants of each non-top child
      have hchild : ∀ i, i < n → (sg i).kind ≠ SegKind.top →
          let lam' := if (sg i).kind = SegKind.sec then c * lam / (1 + L) else w / (1 + L)
          let b' := Function.update b j (sg i).β
          LfsGe (j + 1) (Abase A (j + 1)) b' lam' ∧ 0 < lam' ∧ lam' ≤ 1 ∧
          0 ≤ nodeRad ρ n (fun i => (sg i).β) (fun i => (sg i).hi) i ∧
          nodeRad ρ n (fun i => (sg i).β) (fun i => (sg i).hi) i ≤ θ * lam' ∧
          1 ≤ wallVal (j + 1) b' ∧ wallVal (j + 1) b' ≤ B + 1 ∧
          lam * (θ * c / (1 + L) ^ 2) ≤ lam' := by
        intro i hi hk lam' b'
        have hAb : Abase A (j + 1) = A j := by simp [Abase]
        have hwv : wallVal (j + 1) b' = (sg i).β := by
          simp [wallVal, b']
        rw [hAb, hwv]
        have hr0 : 0 ≤ nodeRad ρ n (fun i => (sg i).β) (fun i => (sg i).hi) i :=
          le_trans hρ0 (le_nodeRad _ _ _ _ _)
        cases hkind : (sg i).kind with
        | top => exact absurd hkind hk
        | sec =>
            obtain ⟨hL', _, _, h1, h2⟩ := psec (sg i) (hmemi i hi) hkind
            have hrad' := hrad i hi hk
            simp only [lam', hkind, if_true] at hrad' ⊢
            refine ⟨hL', by positivity, ?_, hr0, hrad', h1, h2, ?_⟩
            · rw [div_le_iff₀ h1L]; nlinarith
            · have e : lam * (θ * c / (1 + L) ^ 2) = (c * lam / (1 + L)) * (θ / (1 + L)) := by
                field_simp
              have hq : θ / (1 + L) ≤ 1 := by rw [div_le_one h1L]; linarith
              rw [e]
              calc c * lam / (1 + L) * (θ / (1 + L)) ≤ c * lam / (1 + L) * 1 :=
                    mul_le_mul_of_nonneg_left hq (by positivity)
                _ = _ := mul_one _
        | band =>
            obtain ⟨hL', _, _, _, _, h1, h2⟩ := pband (sg i) (hmemi i hi) hkind
            have hrad' := hrad i hi hk
            simp only [lam', hkind, reduceCtorEq, ↓reduceIte] at hrad' ⊢
            refine ⟨hL', by positivity, ?_, hr0, hrad', h1, h2, le_of_eq ?_⟩
            · rw [hwdef, div_div, div_le_iff₀ (by positivity)]
              have : (1:ℝ) ≤ (1 + L) * (1 + L) := by nlinarith
              nlinarith [mul_pos hθ0 hc]
            · rw [hwdef]; field_simp
      -- assemble
      have hbuild : build A B c L (d + 1) j b lam ρ =
          BTree.node n (fun i => (sg i).β) (fun i => (sg i).lo) (fun i => (sg i).hi)
            (fun i => if (sg i).kind = SegKind.top then chainTree d (sg i).β
              else build A B c L d (j + 1) (Function.update b j (sg i).β)
                (if (sg i).kind = SegKind.sec then c * lam / (1 + L) else w / (1 + L))
                (nodeRad ρ n (fun i => (sg i).β) (fun i => (sg i).hi) i)) := rfl
      rw [hbuild]
      refine ⟨⟨by omega, by show (sg 0).β = _; rw [hsg0]; rfl,
        fun i hi => ⟨(hrel i hi).2.1, (hrel i hi).2.2.1⟩,
        fun _ => by show _ ≤ (sg 0).hi; rw [hsg0]; simp only [secSeg]; linarith, fun i hi => ?_⟩,
        ⟨hlen, ?_, fun i hi => ?_⟩, ⟨fun i hi => pβ _ (hmemi i hi), fun i hi => (hrel i hi).2.2.2,
        fun i hi => ?_⟩, fun i hi => ?_⟩
      · -- WF of children
        by_cases hk : (sg i).kind = SegKind.top
        · simp only [hk, if_true]
          exact (chainTree_props (B + 3) d _ _ (pβ _ (hmemi i hi)).1 (pβ _ (hmemi i hi)).2).1
        · simp only [hk, if_false]
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, _⟩ := hchild i hi hk
          have := (ih (j + 1) (by omega) _ _ _ h1 h2 h3 h4 h5 h6 h7).1
          have hwv : wallVal (j + 1) (Function.update b j (sg i).β) = (sg i).β := by
            simp [wallVal]
          rwa [hwv] at this
      · -- the last breakpoint
        have h1 := (hrel (n - 2) (by omega)).1
        have : n - 2 + 1 = n - 1 := by omega
        rw [this, hlast] at h1
        show B + 1 / 2 ≤ (sg (n - 2)).hi
        rw [h1]; simpa [topSeg] using hTB
      · have hk := hnontop i hi
        simp only [hk, if_false]
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, _⟩ := hchild i (by omega) hk
        exact (ih (j + 1) (by omega) _ _ _ h1 h2 h3 h4 h5 h6 h7).2.1
      · by_cases hk : (sg i).kind = SegKind.top
        · simp only [hk, if_true]
          exact (chainTree_props (B + 3) d _ 0 (pβ _ (hmemi i hi)).1 (pβ _ (hmemi i hi)).2).2
        · simp only [hk, if_false]
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, _⟩ := hchild i hi hk
          exact (ih (j + 1) (by omega) _ _ _ h1 h2 h3 h4 h5 h6 h7).2.2.1
      · have hk := hnontop i hi
        simp only [hk, if_false]
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hchild i (by omega) hk
        refine LeafProp.mono ?_ _ _ _ _ (ih (j + 1) (by omega) _ _ _ h1 h2 h3 h4 h5 h6 h7).2.2.2
        rintro b' ρ' ⟨lam'', hle, hL'', hρ''⟩
        refine ⟨lam'', le_trans ?_ hle, hL'', hρ''⟩
        have hf := (lamFactor_pos hc hL d).le
        calc lam * lamFactor c L (d + 1) = lam * (θ * c / (1 + L) ^ 2) * lamFactor c L d := by
              simp only [lamFactor, ← hθdef]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right h8 hf

end Persistence
end CRNT
