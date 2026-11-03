import CRNT.Multistationarity.BCIntersection

/-!
# The S-to-R intersection certificate for two permutation cycles

Continuation of `CRNT.Multistationarity.BCIntersection`: the components of the common subgraph
of the true-SR cycles of `c` and `d` are listed explicitly and assembled into a
`TrueSRCycle.SToRIntersection` (`CyclePair.sToRIntersection`).

The component starting at an entry species `z` has vertices
`z, [ch z], c z, [ch (c z)], …, c^M z, [ch (c^M z)]` (`vertexAt`) and edges alternating between
the left edge of `c^k z` and the right edge of `c^k z` (`edgeAt`), with `M` the first
disagreement of `c` and `d` along the orbit of `z`.

Nothing here is an axiom or a `sorry`.
-/

open Equiv Finset

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

namespace CycleChannels

variable {N : Network S} {c : Perm S} {ch : S → N.R}

theorem containsEdge_iff (h : N.CycleChannels c ch) {x₀ : S} (hx₀ : x₀ ∈ c.support)
    (e : N.TrueSREdge) :
    (h.toCycle x₀ hx₀).ContainsEdge e ↔
      ∃ y, ∃ hy : y ∈ c.support,
        e.SameIncidence (h.leftAt y hy) ∨ e.SameIncidence (h.rightAt y hy) := by
  constructor
  · rintro (⟨j, hj⟩ | ⟨j, hj⟩)
    · exact ⟨_, h.sp_mem hx₀ j, Or.inl hj⟩
    · exact ⟨_, h.sp_mem hx₀ j, Or.inr hj⟩
  · rintro ⟨y, hy, hl | hr⟩
    · obtain ⟨j, rfl⟩ := h.sp_surj hx₀ hy
      exact Or.inl ⟨j, hl⟩
    · obtain ⟨j, rfl⟩ := h.sp_surj hx₀ hy
      exact Or.inr ⟨j, hr⟩

end CycleChannels

theorem TrueSREdge.sameIncidence_trans {N : Network S} {e f g : N.TrueSREdge}
    (h1 : e.SameIncidence f) (h2 : f.SameIncidence g) : e.SameIncidence g :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩

theorem TrueSREdge.sameIncidence_symm {N : Network S} {e f : N.TrueSREdge}
    (h : e.SameIncidence f) : f.SameIncidence e :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

namespace CyclePair

variable {N : Network S} {c d : Perm S} {ch : S → N.R}

/-- Edge `i` of the component starting at `z`. -/
def edgeAt (P : N.CyclePair c d ch) {z : S} (hz : z ∈ c.support) (i : ℕ) : N.TrueSREdge :=
  if i % 2 = 0 then P.hc.leftAt ((c ^ (i / 2)) z) (Perm.pow_apply_mem_support.mpr hz)
  else P.hc.rightAt ((c ^ (i / 2)) z) (Perm.pow_apply_mem_support.mpr hz)

/-- Vertex `i` of the component starting at `z`. -/
def vertexAt (P : N.CyclePair c d ch) {z : S} (hz : z ∈ c.support) (i : ℕ) :
    N.TrueSRVertex :=
  if i % 2 = 0 then Sum.inl ((c ^ (i / 2)) z)
  else Sum.inr ⟨N.trueReaction (ch ((c ^ (i / 2)) z)),
    P.hc.nonflow _ (Perm.pow_apply_mem_support.mpr hz)⟩

theorem edgeAt_reaction (P : N.CyclePair c d ch) {z : S} (hz : z ∈ c.support) (i : ℕ) :
    (P.edgeAt hz i).reaction = N.trueReaction (ch ((c ^ (i / 2)) z)) := by
  unfold edgeAt; split_ifs <;> rfl

theorem edgeAt_species_even (P : N.CyclePair c d ch) {z : S} (hz : z ∈ c.support) {i : ℕ}
    (hi : i % 2 = 0) : (P.edgeAt hz i).species = (c ^ (i / 2)) z := by
  unfold edgeAt; rw [if_pos hi]; rfl

theorem edgeAt_species_odd (P : N.CyclePair c d ch) {z : S} (hz : z ∈ c.support) {i : ℕ}
    (hi : i % 2 = 1) : (P.edgeAt hz i).species = c ((c ^ (i / 2)) z) := by
  unfold edgeAt; rw [if_neg (by omega)]; rfl

theorem edgeAt_sameIncidence_left (P : N.CyclePair c d ch) {z : S} (hz : z ∈ c.support)
    {i : ℕ} (hi : i % 2 = 0) (hy : (c ^ (i / 2)) z ∈ d.support) :
    (P.edgeAt hz i).SameIncidence (P.hd.leftAt ((c ^ (i / 2)) z) hy) := by
  unfold edgeAt; rw [if_pos hi]; exact ⟨rfl, rfl, rfl⟩

theorem edgeAt_sameIncidence_right (P : N.CyclePair c d ch) {z : S} (hz : z ∈ c.support)
    {i : ℕ} (hi : i % 2 = 1) (hy : (c ^ (i / 2)) z ∈ d.support)
    (hcd : c ((c ^ (i / 2)) z) = d ((c ^ (i / 2)) z)) :
    (P.edgeAt hz i).SameIncidence (P.hd.rightAt ((c ^ (i / 2)) z) hy) := by
  unfold edgeAt; rw [if_neg (by omega)]
  refine ⟨hcd, rfl, ?_⟩
  change N.bcEndpoint _ _ = N.bcEndpoint _ _
  rw [hcd]

theorem leftAt_sameIncidence_edgeAt (P : N.CyclePair c d ch) {z : S} (hz : z ∈ c.support)
    {i : ℕ} (hi : i % 2 = 0) {y : S} (hy : y ∈ c.support) (hyz : y = (c ^ (i / 2)) z) :
    (P.hc.leftAt y hy).SameIncidence (P.edgeAt hz i) := by
  subst hyz; unfold edgeAt; rw [if_pos hi]; exact ⟨rfl, rfl, rfl⟩

theorem rightAt_sameIncidence_edgeAt (P : N.CyclePair c d ch) {z : S} (hz : z ∈ c.support)
    {i : ℕ} (hi : i % 2 = 1) {y : S} (hy : y ∈ c.support) (hyz : y = (c ^ (i / 2)) z) :
    (P.hc.rightAt y hy).SameIncidence (P.edgeAt hz i) := by
  subst hyz; unfold edgeAt; rw [if_neg (by omega)]; exact ⟨rfl, rfl, rfl⟩

theorem edgeAt_on_C (P : N.CyclePair c d ch) {z : S} (hz : z ∈ c.support) {x₀ : S}
    (hx₀ : x₀ ∈ c.support) (i : ℕ) : (P.hc.toCycle x₀ hx₀).ContainsEdge (P.edgeAt hz i) := by
  rw [P.hc.containsEdge_iff]
  refine ⟨(c ^ (i / 2)) z, Perm.pow_apply_mem_support.mpr hz, ?_⟩
  unfold edgeAt
  split_ifs
  · exact Or.inl ⟨rfl, rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl, rfl⟩

theorem edgeAt_on_D (P : N.CyclePair c d ch) {z : S} (hz : z ∈ c.support)
    (hzd : z ∈ d.support) {x₁ : S} (hx₁ : x₁ ∈ d.support) {i : ℕ}
    (hi : i < 2 * P.M hz + 1) : (P.hd.toCycle x₁ hx₁).ContainsEdge (P.edgeAt hz i) := by
  rw [P.hd.containsEdge_iff]
  have hy : (c ^ (i / 2)) z ∈ d.support := P.shared hz hzd (by omega)
  refine ⟨(c ^ (i / 2)) z, hy, ?_⟩
  rcases Nat.mod_two_eq_zero_or_one i with he | ho
  · exact Or.inl (P.edgeAt_sameIncidence_left hz he hy)
  · exact Or.inr (P.edgeAt_sameIncidence_right hz ho hy (P.agree_of_lt hz (by omega)))

theorem vertexAt_even (P : N.CyclePair c d ch) {z : S} (hz : z ∈ c.support) {i : ℕ}
    (hi : i % 2 = 0) : P.vertexAt hz i = Sum.inl ((c ^ (i / 2)) z) := by
  unfold vertexAt; rw [if_pos hi]

theorem vertexAt_odd_val (P : N.CyclePair c d ch) {z : S} (hz : z ∈ c.support) {i : ℕ}
    (hi : i % 2 = 1) : ∃ ρ : N.InternalTrueReaction, P.vertexAt hz i = Sum.inr ρ ∧
      ρ.1 = N.trueReaction (ch ((c ^ (i / 2)) z)) := by
  unfold vertexAt; rw [if_neg (by omega)]
  exact ⟨_, rfl, rfl⟩

theorem connects (P : N.CyclePair c d ch) {z : S} (hz : z ∈ c.support) (i : ℕ) :
    (P.edgeAt hz i).Connects (P.vertexAt hz i) (P.vertexAt hz (i + 1)) := by
  rcases Nat.mod_two_eq_zero_or_one i with he | ho
  · left
    refine ⟨by rw [P.vertexAt_even hz he, P.edgeAt_species_even hz he], ?_⟩
    obtain ⟨ρ, hρ, hρv⟩ := P.vertexAt_odd_val hz (i := i + 1) (by omega)
    rw [hρ]
    congr 1
    apply Subtype.ext
    show ρ.1 = (P.edgeAt hz i).reaction
    rw [hρv, P.edgeAt_reaction]
    rw [show (i + 1) / 2 = i / 2 by omega]
  · right
    refine ⟨?_, ?_⟩
    · obtain ⟨ρ, hρ, hρv⟩ := P.vertexAt_odd_val hz ho
      rw [hρ]
      congr 1
      apply Subtype.ext
      show ρ.1 = (P.edgeAt hz i).reaction
      rw [hρv, P.edgeAt_reaction]
    · rw [P.vertexAt_even hz (i := i + 1) (by omega), P.edgeAt_species_odd hz ho,
        show (i + 1) / 2 = i / 2 + 1 by omega, pow_succ', Perm.mul_apply]

theorem pow_inj_le (P : N.CyclePair c d ch) {z : S} (hz : z ∈ c.support) {a b : ℕ}
    (ha : a ≤ P.M hz) (hb : b ≤ P.M hz) (h : (c ^ a) z = (c ^ b) z) : a = b :=
  cycle_pow_inj P.hc.isCycle hz (by have := P.M_lt_card hz; omega)
    (by have := P.M_lt_card hz; omega) h

theorem class_eq_imp (P : N.CyclePair c d ch) {z : S} (hz : z ∈ c.support) {z' : S}
    (hz' : z' ∈ c.support) {a b : ℕ}
    (h : N.trueReaction (ch ((c ^ a) z)) = N.trueReaction (ch ((c ^ b) z'))) :
    (c ^ a) z = (c ^ b) z' :=
  P.hc.class_inj _ (Perm.pow_apply_mem_support.mpr hz) _ (Perm.pow_apply_mem_support.mpr hz') h

theorem edge_simple (P : N.CyclePair c d ch) {z : S} (hz : z ∈ c.support) {i j : ℕ}
    (hi : i < 2 * P.M hz + 1) (hj : j < 2 * P.M hz + 1)
    (h : (P.edgeAt hz i).SameIncidence (P.edgeAt hz j)) : i = j := by
  have hr := h.2.1
  rw [P.edgeAt_reaction, P.edgeAt_reaction] at hr
  have hk : i / 2 = j / 2 := P.pow_inj_le hz (by omega) (by omega) (P.class_eq_imp hz hz hr)
  have hs := h.1
  rcases Nat.mod_two_eq_zero_or_one i with hie | hio <;>
    rcases Nat.mod_two_eq_zero_or_one j with hje | hjo
  · omega
  · exfalso
    rw [P.edgeAt_species_even hz hie, P.edgeAt_species_odd hz hjo, hk] at hs
    exact Perm.mem_support.mp (Perm.pow_apply_mem_support.mpr hz) hs.symm
  · exfalso
    rw [P.edgeAt_species_odd hz hio, P.edgeAt_species_even hz hje, hk] at hs
    exact Perm.mem_support.mp (Perm.pow_apply_mem_support.mpr hz) hs
  · omega

theorem vertex_simple (P : N.CyclePair c d ch) {z : S} (hz : z ∈ c.support) {i j : ℕ}
    (hi : i < 2 * P.M hz + 2) (hj : j < 2 * P.M hz + 2)
    (h : P.vertexAt hz i = P.vertexAt hz j) : i = j := by
  rcases Nat.mod_two_eq_zero_or_one i with hie | hio <;>
    rcases Nat.mod_two_eq_zero_or_one j with hje | hjo
  · rw [P.vertexAt_even hz hie, P.vertexAt_even hz hje] at h
    have := P.pow_inj_le hz (by omega) (by omega) (Sum.inl_injective h)
    omega
  · exfalso
    obtain ⟨ρ, hρ, _⟩ := P.vertexAt_odd_val hz hjo
    rw [P.vertexAt_even hz hie, hρ] at h
    exact Sum.inl_ne_inr h
  · exfalso
    obtain ⟨ρ, hρ, _⟩ := P.vertexAt_odd_val hz hio
    rw [P.vertexAt_even hz hje, hρ] at h
    exact Sum.inr_ne_inl h
  · obtain ⟨ρ, hρ, hρv⟩ := P.vertexAt_odd_val hz hio
    obtain ⟨ρ', hρ', hρv'⟩ := P.vertexAt_odd_val hz hjo
    rw [hρ, hρ'] at h
    have hv := congrArg Subtype.val (Sum.inr_injective h)
    rw [hρv, hρv'] at hv
    have := P.pow_inj_le hz (by omega) (by omega) (P.class_eq_imp hz hz hv)
    omega

/-- Species of an edge of a component lie on the component. -/
theorem edgeAt_species_on (P : N.CyclePair c d ch) {z : S} (hz : z ∈ c.support) {i : ℕ}
    (hi : i < 2 * P.M hz + 1) : ∃ k ≤ P.M hz, (P.edgeAt hz i).species = (c ^ k) z := by
  rcases Nat.mod_two_eq_zero_or_one i with hie | hio
  · exact ⟨i / 2, by omega, P.edgeAt_species_even hz hie⟩
  · refine ⟨i / 2 + 1, by omega, ?_⟩
    rw [P.edgeAt_species_odd hz hio, pow_succ', Perm.mul_apply]

/-! ## The certificate -/

/-- The index of a component. -/
noncomputable def zOf (P : N.CyclePair c d ch) (k : Fin P.entries.card) : S :=
  (P.entries.equivFin.symm k).1

theorem zOf_mem (P : N.CyclePair c d ch) (k : Fin P.entries.card) : P.zOf k ∈ P.entries :=
  (P.entries.equivFin.symm k).2

theorem zOf_memC (P : N.CyclePair c d ch) (k : Fin P.entries.card) :
    P.zOf k ∈ c.support := (mem_entries.mp (P.zOf_mem k)).1

theorem zOf_memD (P : N.CyclePair c d ch) (k : Fin P.entries.card) :
    P.zOf k ∈ d.support := (mem_entries.mp (P.zOf_mem k)).2.1

theorem zOf_injective (P : N.CyclePair c d ch) : Function.Injective P.zOf := by
  intro a b h
  apply P.entries.equivFin.symm.injective
  exact Subtype.ext h

theorem exists_zOf (P : N.CyclePair c d ch) {z : S} (hz : z ∈ P.entries) :
    ∃ k, P.zOf k = z :=
  ⟨P.entries.equivFin ⟨z, hz⟩, by simp [zOf]⟩

/-- **The S-to-R intersection of two intersecting cycles with a common channel
assignment.** -/
noncomputable def sToRIntersection (P : N.CyclePair c d ch) {x₀ x₁ : S}
    (hx₀ : x₀ ∈ c.support) (hx₁ : x₁ ∈ d.support)
    (hshare : ∃ x, x ∈ c.support ∧ x ∈ d.support) :
    (P.hc.toCycle x₀ hx₀).SToRIntersection (P.hd.toCycle x₁ hx₁) where
  componentCount := P.entries.card
  componentCount_pos := by
    obtain ⟨x, hxc, hxd⟩ := hshare
    obtain ⟨z, hz, -⟩ := P.exists_entry hxc hxd
    exact Finset.card_pos.mpr ⟨z, hz⟩
  componentLength := fun k => 2 * P.M (P.zOf_memC k) + 1
  componentLength_pos := fun _ => by omega
  edge := fun k i => P.edgeAt (P.zOf_memC k) i.1
  vertex := fun k i => P.vertexAt (P.zOf_memC k) i.1
  edge_on_C := fun k i => P.edgeAt_on_C _ hx₀ i.1
  edge_on_D := fun k i => P.edgeAt_on_D _ (P.zOf_memD k) hx₁ i.2
  connects := fun k i => by
    simp only [Fin.coe_castSucc, Fin.val_succ]
    exact P.connects _ i.1
  edge_simple := by
    intro k i j h
    exact Fin.ext (P.edge_simple _ i.2 j.2 h)
  vertex_simple := by
    intro k i j h
    exact Fin.ext (P.vertex_simple _ i.2 j.2 h)
  starts_at_species := fun k => ⟨P.zOf k, by
    simp only [Fin.val_zero]
    rw [P.vertexAt_even _ (by norm_num)]
    simp⟩
  ends_at_reaction := fun k => by
    obtain ⟨ρ, hρ, -⟩ := P.vertexAt_odd_val (P.zOf_memC k)
      (i := 2 * P.M (P.zOf_memC k) + 1) (by omega)
    exact ⟨ρ, by simpa using hρ⟩
  covers_common := by
    intro e hC hD
    rw [P.hc.containsEdge_iff] at hC
    rw [P.hd.containsEdge_iff] at hD
    obtain ⟨y, hy, hCl | hCr⟩ := hC <;> obtain ⟨y', hy', hDl | hDr⟩ := hD
    · -- left/left: a shared species and its left edge
      have hyy : y = y' := hCl.1.symm.trans hDl.1
      subst hyy
      obtain ⟨z, hz, kk, hk, hkz, -⟩ := P.exists_entry hy hy'
      obtain ⟨comp, rfl⟩ := P.exists_zOf hz
      refine ⟨comp, ⟨2 * kk, by
        have : kk ≤ P.M (P.zOf_memC comp) := hk
        omega⟩, ?_⟩
      refine TrueSREdge.sameIncidence_trans hCl ?_
      exact P.leftAt_sameIncidence_edgeAt (P.zOf_memC comp) (i := 2 * kk) (by omega) hy
        (by rw [show 2 * kk / 2 = kk by omega]; exact hkz.symm)
    · -- left/right: impossible
      exfalso
      have hcls : N.trueReaction (ch y) = N.trueReaction (ch y') := hCl.2.1.symm.trans hDr.2.1
      have hyy := P.cross y hy y' hy' hcls
      subst hyy
      have hsp : y = d y := hCl.1.symm.trans hDr.1
      exact Perm.mem_support.mp hy' hsp.symm
    · -- right/left: impossible
      exfalso
      have hcls : N.trueReaction (ch y) = N.trueReaction (ch y') := hCr.2.1.symm.trans hDl.2.1
      have hyy := P.cross y hy y' hy' hcls
      subst hyy
      have hsp : c y = y := hCr.1.symm.trans hDl.1
      exact Perm.mem_support.mp hy hsp
    · -- right/right: a shared species where `c` and `d` agree
      have hcls : N.trueReaction (ch y) = N.trueReaction (ch y') := hCr.2.1.symm.trans hDr.2.1
      have hyy := P.cross y hy y' hy' hcls
      subst hyy
      have hcd : c y = d y := hCr.1.symm.trans hDr.1
      obtain ⟨z, hz, kk, -, hkz, hlt⟩ := P.exists_entry hy hy'
      have hlt' := hlt hcd
      obtain ⟨comp, rfl⟩ := P.exists_zOf hz
      refine ⟨comp, ⟨2 * kk + 1, by
        have : kk < P.M (P.zOf_memC comp) := hlt'
        omega⟩, ?_⟩
      refine TrueSREdge.sameIncidence_trans hCr ?_
      exact P.rightAt_sameIncidence_edgeAt (P.zOf_memC comp) (i := 2 * kk + 1) (by omega) hy
        (by rw [show (2 * kk + 1) / 2 = kk by omega]; exact hkz.symm)
  components_separated := by
    intro k k' hkk i j hshv
    apply hkk
    apply P.zOf_injective
    rcases hshv with hsp | hrx
    · obtain ⟨a, ha, hae⟩ := P.edgeAt_species_on (P.zOf_memC k) i.2
      obtain ⟨b, hb, hbe⟩ := P.edgeAt_species_on (P.zOf_memC k') j.2
      rw [hae, hbe] at hsp
      exact P.entry_unique (P.zOf_mem k) (P.zOf_mem k') ha hb hsp
    · rw [P.edgeAt_reaction, P.edgeAt_reaction] at hrx
      have := P.class_eq_imp (P.zOf_memC k) (P.zOf_memC k') hrx
      have hi := i.2
      have hj := j.2
      exact P.entry_unique (P.zOf_mem k) (P.zOf_mem k')
        (by change i.1 < 2 * P.M (P.zOf_memC k) + 1 at hi; omega)
        (by change j.1 < 2 * P.M (P.zOf_memC k') + 1 at hj; omega) this

end CyclePair

end Network
end CRNT
