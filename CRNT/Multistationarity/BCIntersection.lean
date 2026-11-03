import CRNT.Multistationarity.BCCycleBridge

/-!
# Two cycles built from one channel assignment meet in an S-to-R intersection

Let `c ≠ d` be cyclic permutations of the species that share a species, both admissible for
the same channel assignment `ch` (`CycleChannels`), with the channel classes injective across
the two supports.  In the true-SR cycles `cycleOfPerm` of `c` and `d`, every shared species `y`
carries the *same* left edge `y — [ch y]`, and the reaction `[ch y]` lies on a cycle exactly when
`y` does.  Consequently every connected component of the common subgraph starts at a species
`z` whose predecessors in `c` and `d` differ, runs `z, c z, c² z, …` while `c` and `d` agree, and
ends at the reaction `[ch (c^M z)]` where they first disagree.  Each component is therefore a
simple path from a species to a reaction, which is exactly a
`TrueSRCycle.SToRIntersection` certificate (`sToRIntersection_of_pair`).

This is the step where condition (ii) of the true-SR criterion is used in the Banaji--Craciun
argument: two distinct negative cycles of a normalized minor can never intersect.

Nothing here is an axiom or a `sorry`.
-/

open Equiv Finset

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## Cycle-level facts -/

theorem cycle_eq_of_agree {c d : Perm S} (hc : c.IsCycle) (hd : d.IsCycle) {z : S}
    (hz : z ∈ c.support) (h : ∀ k : ℕ, c ((c ^ k) z) = d ((c ^ k) z)) : c = d := by
  have hpow : ∀ i : ℕ, (d ^ i) z = (c ^ i) z := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ', Perm.mul_apply, ih, ← h i, pow_succ', Perm.mul_apply]
  ext x
  by_cases hx : x ∈ c.support
  · obtain ⟨k, _, hk⟩ := cycle_exists_pow_lt hc hz hx
    rw [← hk]
    exact h k
  · have hcx : c x = x := Perm.notMem_support.mp hx
    rw [hcx]
    by_contra hdx
    have hdz : d z ≠ z := by
      have h0 := h 0
      simp only [pow_zero, Perm.one_apply] at h0
      rw [← h0]
      exact Perm.mem_support.mp hz
    obtain ⟨i, hi⟩ := hd.exists_pow_eq hdz (Ne.symm hdx)
    rw [hpow i] at hi
    apply hx
    rw [← hi]
    exact Perm.pow_apply_mem_support.mpr hz

theorem pow_apply_inv_pow_apply (c : Perm S) (k : ℕ) (w : S) :
    (c ^ k) (((c⁻¹) ^ k) w) = w := by
  rw [inv_pow, ← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]

/-! ## The pair setting -/

/-- Two distinct cycles admissible for one channel assignment, with the channel classes
injective across both supports. -/
structure CyclePair (N : Network S) (c d : Perm S) (ch : S → N.R) : Prop where
  hc : N.CycleChannels c ch
  hd : N.CycleChannels d ch
  cross : ∀ y ∈ c.support, ∀ y' ∈ d.support,
    N.trueReaction (ch y) = N.trueReaction (ch y') → y = y'
  ne : c ≠ d

namespace CyclePair

variable {N : Network S} {c d : Perm S} {ch : S → N.R}

theorem exists_disagree (P : N.CyclePair c d ch) {z : S} (hz : z ∈ c.support) :
    ∃ k : ℕ, c ((c ^ k) z) ≠ d ((c ^ k) z) := by
  by_contra h
  push_neg at h
  exact P.ne (cycle_eq_of_agree P.hc.isCycle P.hd.isCycle hz h)

open Classical in
/-- The length parameter of the component starting at `z`: the first disagreement. -/
noncomputable def M (P : N.CyclePair c d ch) {z : S} (hz : z ∈ c.support) : ℕ :=
  Nat.find (P.exists_disagree hz)

theorem agree_of_lt (P : N.CyclePair c d ch) {z : S} (hz : z ∈ c.support) {k : ℕ}
    (hk : k < P.M hz) : c ((c ^ k) z) = d ((c ^ k) z) := by
  classical
  have := Nat.find_min (P.exists_disagree hz) (m := k) (by unfold M at hk; convert hk)
  exact not_not.mp this

theorem disagree_M (P : N.CyclePair c d ch) {z : S} (hz : z ∈ c.support) :
    c ((c ^ P.M hz) z) ≠ d ((c ^ P.M hz) z) := by
  classical
  have := Nat.find_spec (P.exists_disagree hz)
  unfold M
  convert this

theorem M_le_of_agree (P : N.CyclePair c d ch) {z : S} (hz : z ∈ c.support) {B : ℕ}
    (h : ∀ k < B, c ((c ^ k) z) = d ((c ^ k) z)) : B ≤ P.M hz := by
  by_contra hlt
  push_neg at hlt
  exact P.disagree_M hz (h _ hlt)

theorem M_lt_card (P : N.CyclePair c d ch) {z : S} (hz : z ∈ c.support) :
    P.M hz < #c.support := by
  by_contra hge
  push_neg at hge
  apply P.ne
  apply cycle_eq_of_agree P.hc.isCycle P.hd.isCycle hz
  intro k
  have hlt : k % #c.support < #c.support :=
    Nat.mod_lt _ (by have := P.hc.isCycle.two_le_card_support; omega)
  have := P.agree_of_lt hz (lt_of_lt_of_le hlt hge)
  rwa [cycle_pow_mod P.hc.isCycle] at this

theorem d_step (P : N.CyclePair c d ch) {z : S} (hz : z ∈ c.support) {k : ℕ}
    (hk : k < P.M hz) : d ((c ^ k) z) = (c ^ (k + 1)) z := by
  rw [← P.agree_of_lt hz hk, pow_succ', Perm.mul_apply]

theorem shared (P : N.CyclePair c d ch) {z : S} (hz : z ∈ c.support) (hzd : z ∈ d.support)
    {k : ℕ} (hk : k ≤ P.M hz) : (c ^ k) z ∈ d.support := by
  induction k with
  | zero => simpa using hzd
  | succ k ih =>
    rw [← P.d_step hz (by omega)]
    exact Perm.apply_mem_support.mpr (ih (by omega))

theorem inv_eq (P : N.CyclePair c d ch) {z : S} (hz : z ∈ c.support) {k : ℕ}
    (hk0 : 0 < k) (hk : k ≤ P.M hz) : c⁻¹ ((c ^ k) z) = d⁻¹ ((c ^ k) z) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h1 : c⁻¹ ((c ^ (j + 1)) z) = (c ^ j) z := by
    rw [pow_succ', Perm.mul_apply]; simp
  have h2 : d⁻¹ ((c ^ (j + 1)) z) = (c ^ j) z := by
    rw [← P.d_step hz (by omega)]; simp
  rw [h1, h2]

/-- The entry species: shared, with distinct predecessors in `c` and `d`. -/
def entries (_P : N.CyclePair c d ch) : Finset S :=
  (c.support ∩ d.support).filter (fun z => c⁻¹ z ≠ d⁻¹ z)

theorem mem_entries {P : N.CyclePair c d ch} {z : S} :
    z ∈ P.entries ↔ z ∈ c.support ∧ z ∈ d.support ∧ c⁻¹ z ≠ d⁻¹ z := by
  simp [entries, and_assoc]

/-- Two components cannot overlap. -/
theorem entry_unique (P : N.CyclePair c d ch) {z z' : S} (hz : z ∈ P.entries)
    (hz' : z' ∈ P.entries) {k k' : ℕ} (hk : k ≤ P.M (mem_entries.mp hz).1)
    (hk' : k' ≤ P.M (mem_entries.mp hz').1) (h : (c ^ k) z = (c ^ k') z') : z = z' := by
  have hzc := (mem_entries.mp hz).1
  have hzc' := (mem_entries.mp hz').1
  rcases le_total k k' with hkk | hkk
  · obtain ⟨m, rfl⟩ : ∃ m, k' = k + m := ⟨k' - k, by omega⟩
    have hz_eq : z = (c ^ m) z' := by
      have : (c ^ k) z = (c ^ k) ((c ^ m) z') := by
        rw [h, pow_add, Perm.mul_apply]
      exact (c ^ k).injective this
    rcases Nat.eq_zero_or_pos m with hm | hm
    · rw [hz_eq, hm]; rfl
    · exfalso
      have := P.inv_eq hzc' hm (by omega)
      rw [← hz_eq] at this
      exact (mem_entries.mp hz).2.2 this
  · obtain ⟨m, rfl⟩ : ∃ m, k = k' + m := ⟨k - k', by omega⟩
    have hz_eq : z' = (c ^ m) z := by
      have : (c ^ k') z' = (c ^ k') ((c ^ m) z) := by
        rw [← h, pow_add, Perm.mul_apply]
      exact (c ^ k').injective this
    rcases Nat.eq_zero_or_pos m with hm | hm
    · rw [hz_eq, hm]; rfl
    · exfalso
      have := P.inv_eq hzc hm (by omega)
      rw [← hz_eq] at this
      exact (mem_entries.mp hz').2.2 this

/-- Every shared species lies on some component (walk backward to an entry). -/
theorem exists_entry (P : N.CyclePair c d ch) {y : S} (hyc : y ∈ c.support)
    (hyd : y ∈ d.support) :
    ∃ z, ∃ hz : z ∈ P.entries, ∃ k, k ≤ P.M (mem_entries.mp hz).1 ∧ (c ^ k) z = y ∧
      (c y = d y → k < P.M (mem_entries.mp hz).1) := by
  classical
  set u : ℕ → S := fun j => ((c⁻¹) ^ j) y with hu
  have hu_succ : ∀ j, u (j + 1) = c⁻¹ (u j) := by
    intro j; simp only [hu, pow_succ', Perm.mul_apply]
  have hu0 : u 0 = y := by simp only [hu, pow_zero, Perm.one_apply]
  have hck : ∀ k m, (c ^ k) (u (k + m)) = u m := by
    intro k m
    simp only [hu]
    rw [pow_add, Perm.mul_apply, pow_apply_inv_pow_apply]
  have hu_mem : ∀ j, u j ∈ c.support := by
    intro j
    simp only [hu]
    have : ((c⁻¹) ^ j) y ∈ (c⁻¹).support := Perm.pow_apply_mem_support.mpr (by
      rw [Perm.support_inv]; exact hyc)
    rwa [Perm.support_inv] at this
  -- if no entry is ever met, `c⁻¹ = d⁻¹`
  have hshare : ∀ B, (∀ j < B, u j ∉ P.entries) → ∀ j ≤ B, u j ∈ d.support ∧
      (j < B → c⁻¹ (u j) = d⁻¹ (u j)) := by
    intro B hB j hj
    induction j with
    | zero =>
      refine ⟨by rw [hu0]; exact hyd, fun h0 => ?_⟩
      have hn := hB 0 h0
      rw [mem_entries] at hn
      push_neg at hn
      exact hn (hu_mem 0) (by rw [hu0]; exact hyd)
    | succ j ih =>
      obtain ⟨hjd, hjeq⟩ := ih (by omega)
      have heq := hjeq (by omega)
      have hmem : u (j + 1) ∈ d.support := by
        rw [hu_succ, heq]
        have : d⁻¹ (u j) ∈ (d⁻¹).support := Perm.apply_mem_support.mpr (by
          rw [Perm.support_inv]; exact hjd)
        rwa [Perm.support_inv] at this
      refine ⟨hmem, fun hlt => ?_⟩
      have hn := hB (j + 1) hlt
      rw [mem_entries] at hn
      push_neg at hn
      exact hn (hu_mem _) hmem
  have hex : ∃ B, u B ∈ P.entries := by
    by_contra hnone
    push_neg at hnone
    apply P.ne
    have hinv : c⁻¹ = d⁻¹ := by
      apply cycle_eq_of_agree P.hc.isCycle.inv P.hd.isCycle.inv
        (by rw [Perm.support_inv]; exact hyc)
      intro k
      exact (hshare (k + 1) (fun j _ => hnone j) k (by omega)).2 (by omega)
    exact inv_injective hinv
  set B := Nat.find hex with hBdef
  have hBmem : u B ∈ P.entries := Nat.find_spec hex
  have hBmin : ∀ j < B, u j ∉ P.entries := fun j hj => Nat.find_min hex hj
  have hsh := hshare B hBmin
  refine ⟨u B, hBmem, B, ?_, ?_, ?_⟩
  · apply P.M_le_of_agree
    intro k hk
    obtain ⟨m, hm⟩ : ∃ m, B = k + (m + 1) := ⟨B - k - 1, by omega⟩
    rw [hm, hck k]
    have heq := (hsh m (by omega)).2 (by omega)
    have h1 : c (u (m + 1)) = u m := by rw [hu_succ]; simp
    have h2 : d (u (m + 1)) = u m := by rw [hu_succ, heq]; simp
    rw [h1, h2]
  · have := hck B 0
    rwa [Nat.add_zero, hu0] at this
  · intro hcd
    have hle : B ≤ P.M (mem_entries.mp hBmem).1 := by
      apply P.M_le_of_agree
      intro k hk
      obtain ⟨m, hm⟩ : ∃ m, B = k + (m + 1) := ⟨B - k - 1, by omega⟩
      rw [hm, hck k]
      have heq := (hsh m (by omega)).2 (by omega)
      have h1 : c (u (m + 1)) = u m := by rw [hu_succ]; simp
      have h2 : d (u (m + 1)) = u m := by rw [hu_succ, heq]; simp
      rw [h1, h2]
    rcases lt_or_eq_of_le hle with hlt | heqB
    · exact hlt
    · exfalso
      have hy : (c ^ B) (u B) = y := by
        have := hck B 0
        rwa [Nat.add_zero, hu0] at this
      have := P.disagree_M (mem_entries.mp hBmem).1
      rw [← heqB, hy] at this
      exact this hcd

end CyclePair

end Network
end CRNT
