import CRNT.Multistationarity.TrueChemistrySRGraph
import CRNT.Multistationarity.StrongConcordance
import CRNT.Multistationarity.BCDetCycleCancellation

/-!
# From cyclic permutations to true-SR cycles

The Banaji--Craciun determinant argument reads the Leibniz terms of a normalized submatrix of
the stoichiometric matrix as cycles of the true species--reaction graph.  This module builds
that dictionary.

Fix a cyclic permutation `c` of the species and a channel assignment `ch : S → N.R` such that,
for every `y` in the support of `c`, the channel `ch y` is not a flow channel and has nonzero
stoichiometry at both `y` and `c y`.  Then

* `cycleOfPerm` is the true-SR cycle `y —(ch y)— c y —(ch (c y))— c² y — …`, enumerated from a
  base point `x₀` of the support (species `j` is `(c ^ j) x₀`, reaction `j` is the class of
  `ch` at species `j`, the left edge is the incidence of species `j` with that reaction, the
  right edge the incidence of species `j + 1`);
* `signed_weight_eq` computes the signed product
  `sign c * ∏_{y ∈ supp c} ν_{ch y}(c y) / ν_{ch y}(y)` as
  `-(-1) ^ numCPairs * (∏ right labels) / (∏ left labels)` under reactant/product separation.

Consequently a negative signed product forces an even cycle, and for an even s-cycle the signed
product is exactly `-1` (`weight_eq_neg_one_of_sCycle`).

Nothing here is an axiom or a `sorry`.
-/

open Equiv Finset

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## Edges selected by a channel and a species -/

/-- The endpoint complex of channel `r` containing species `s`: the source if `s` is a reactant,
otherwise the target. -/
def bcEndpoint (N : Network S) (r : N.R) (s : S) : Complex S :=
  if (N.reaction r).source s ≠ 0 then (N.reaction r).source else (N.reaction r).target

/-- The true-SR edge between species `s` and the class of the non-flow channel `r`. -/
def bcEdge (N : Network S) (r : N.R) (hr : ¬ N.IsFlowChannel r) (s : S)
    (hs : N.reactionVector r s ≠ 0) : N.TrueSREdge where
  species := s
  reaction := N.trueReaction r
  internal := hr
  endpoint := N.bcEndpoint r s
  representative := r
  representative_class := rfl
  endpoint_is_source_or_target := by
    unfold bcEndpoint
    split_ifs <;> simp
  occurs := by
    unfold bcEndpoint
    split_ifs with h
    · exact h
    · intro ht
      apply hs
      have h0 : (N.reaction r).source s = 0 := by simpa using h
      simp [reactionVector_apply, h0, ht]

theorem bcEdge_species (N : Network S) (r : N.R) (hr) (s : S) (hs) :
    (N.bcEdge r hr s hs).species = s := rfl

theorem bcEdge_reaction (N : Network S) (r : N.R) (hr) (s : S) (hs) :
    (N.bcEdge r hr s hs).reaction = N.trueReaction r := rfl

theorem bcEdge_endpoint (N : Network S) (r : N.R) (hr) (s : S) (hs) :
    (N.bcEdge r hr s hs).endpoint = N.bcEndpoint r s := rfl

/-- Under separation the label of `bcEdge` is the absolute stoichiometric coefficient. -/
theorem bcEdge_coeff_cast (N : Network S) (hsep : N.ReactantProductSeparated)
    (r : N.R) (hr) (s : S) (hs) :
    ((N.bcEdge r hr s hs).coeff : ℝ) = |N.reactionVector r s| := by
  unfold TrueSREdge.coeff
  rw [bcEdge_endpoint, bcEdge_species]
  unfold bcEndpoint
  rw [reactionVector_apply]
  split_ifs with h
  · have ht : (N.reaction r).target s = 0 := hsep r s h
    rw [ht]
    simp
  · have h0 : (N.reaction r).source s = 0 := by simpa using h
    rw [h0]
    simp

/-- Under separation a nonzero coefficient is negative exactly at reactants. -/
theorem reactionVector_neg_iff (N : Network S) (hsep : N.ReactantProductSeparated)
    (r : N.R) (s : S) (hs : N.reactionVector r s ≠ 0) :
    N.reactionVector r s < 0 ↔ (N.reaction r).source s ≠ 0 := by
  rw [reactionVector_apply]
  constructor
  · intro hlt h0
    rw [h0] at hlt
    have : (0 : ℝ) ≤ ((N.reaction r).target s : ℝ) := Nat.cast_nonneg _
    simp at hlt
    linarith
  · intro h
    have ht : (N.reaction r).target s = 0 := hsep r s h
    rw [ht]
    have : (0 : ℝ) < ((N.reaction r).source s : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero h
    simp only [Nat.cast_zero, zero_sub, neg_neg_iff_pos]
    exact this

/-- Under separation two species of one channel carry the same endpoint label exactly when their
coefficients have the same sign. -/
theorem bcEndpoint_eq_iff (N : Network S) (hsep : N.ReactantProductSeparated)
    (r : N.R) (s t : S) (hs : N.reactionVector r s ≠ 0) (ht : N.reactionVector r t ≠ 0) :
    N.bcEndpoint r s = N.bcEndpoint r t ↔
      (N.reactionVector r s < 0 ↔ N.reactionVector r t < 0) := by
  rw [N.reactionVector_neg_iff hsep r s hs, N.reactionVector_neg_iff hsep r t ht]
  unfold bcEndpoint
  by_cases h1 : (N.reaction r).source s ≠ 0 <;> by_cases h2 : (N.reaction r).source t ≠ 0
  · rw [if_pos h1, if_pos h2]; tauto
  · rw [if_pos h1, if_neg h2]
    constructor
    · intro heq
      exfalso
      have h0 := hsep r s h1
      rw [heq] at h1
      exact h1 h0
    · intro hiff
      exact absurd (hiff.mp h1) h2
  · rw [if_neg h1, if_pos h2]
    constructor
    · intro heq
      exfalso
      have h0 := hsep r t h2
      rw [← heq] at h2
      exact h2 h0
    · intro hiff
      exact absurd (hiff.mpr h2) h1
  · rw [if_neg h1, if_neg h2]; tauto

/-- A ratio of two nonzero reals as a sign times a ratio of absolute values. -/
theorem div_eq_sign_mul_abs_div {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    x / y = (if (y < 0 ↔ x < 0) then 1 else -1) * (|x| / |y|) := by
  rcases lt_or_gt_of_ne hx with hx' | hx' <;> rcases lt_or_gt_of_ne hy with hy' | hy'
  · rw [if_pos (by tauto), abs_of_neg hx', abs_of_neg hy']; field_simp
  · rw [if_neg (by intro h; have := h.mpr hx'; linarith), abs_of_neg hx', abs_of_pos hy']
    field_simp
  · rw [if_neg (by intro h; have := h.mp hy'; linarith), abs_of_pos hx', abs_of_neg hy']
    field_simp
  · rw [if_pos (by constructor <;> intro h <;> linarith), abs_of_pos hx', abs_of_pos hy']
    ring

/-! ## Enumerating the support of a cycle -/

section CycleEnum

variable {c : Perm S}

theorem cycle_pow_mod (hc : c.IsCycle) (x : S) (k : ℕ) :
    (c ^ (k % #c.support)) x = (c ^ k) x := by
  rw [← hc.orderOf, pow_mod_orderOf]

theorem cycle_pow_inj (hc : c.IsCycle) {x : S} (hx : x ∈ c.support) {a b : ℕ}
    (ha : a < #c.support) (hb : b < #c.support) (h : (c ^ a) x = (c ^ b) x) : a = b := by
  have hpow : c ^ a = c ^ b := hc.pow_eq_pow_iff.mpr ⟨x, Perm.mem_support.mp hx, h⟩
  have hmod := pow_inj_mod.mp hpow
  rw [hc.orderOf, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hmod
  exact hmod

theorem cycle_exists_pow_lt (hc : c.IsCycle) {x y : S} (hx : x ∈ c.support)
    (hy : y ∈ c.support) : ∃ k < #c.support, (c ^ k) x = y := by
  obtain ⟨i, hi⟩ := hc.exists_pow_eq (Perm.mem_support.mp hx) (Perm.mem_support.mp hy)
  refine ⟨i % #c.support, Nat.mod_lt _ (by have := hc.two_le_card_support; omega), ?_⟩
  rw [cycle_pow_mod hc, hi]

theorem cycle_pow_card (hc : c.IsCycle) (x : S) : (c ^ #c.support) x = x := by
  rw [← hc.orderOf, pow_orderOf_eq_one]
  rfl

end CycleEnum

/-! ## The true-SR cycle of a permutation cycle -/

/-- Hypotheses making the channel assignment `ch` admissible along the support of `c`. -/
structure CycleChannels (N : Network S) (c : Perm S) (ch : S → N.R) : Prop where
  isCycle : c.IsCycle
  nonflow : ∀ y ∈ c.support, ¬ N.IsFlowChannel (ch y)
  coeff_self : ∀ y ∈ c.support, N.reactionVector (ch y) y ≠ 0
  coeff_next : ∀ y ∈ c.support, N.reactionVector (ch y) (c y) ≠ 0
  class_inj : ∀ y ∈ c.support, ∀ y' ∈ c.support,
    N.trueReaction (ch y) = N.trueReaction (ch y') → y = y'

namespace CycleChannels

variable {N : Network S} {c : Perm S} {ch : S → N.R}

/-- Species `j` of the enumeration from `x₀`. -/
def sp (_h : N.CycleChannels c ch) (x₀ : S) (j : Fin #c.support) : S := (c ^ (j : ℕ)) x₀

theorem sp_mem (h : N.CycleChannels c ch) {x₀ : S} (hx₀ : x₀ ∈ c.support)
    (j : Fin #c.support) : h.sp x₀ j ∈ c.support :=
  Perm.pow_apply_mem_support.mpr hx₀

theorem sp_succ (h : N.CycleChannels c ch) (x₀ : S) (j : Fin #c.support) :
    h.sp x₀ ⟨(j.1 + 1) % #c.support, Nat.mod_lt _ (by
      have := h.isCycle.two_le_card_support; omega)⟩ = c (h.sp x₀ j) := by
  unfold sp
  simp only
  rw [cycle_pow_mod h.isCycle, pow_succ', Perm.mul_apply]

theorem sp_injective (h : N.CycleChannels c ch) {x₀ : S} (hx₀ : x₀ ∈ c.support) :
    Function.Injective (h.sp x₀) := by
  intro a b hab
  exact Fin.ext (cycle_pow_inj h.isCycle hx₀ a.2 b.2 hab)

theorem sp_surj (h : N.CycleChannels c ch) {x₀ : S} (hx₀ : x₀ ∈ c.support)
    {y : S} (hy : y ∈ c.support) : ∃ j, h.sp x₀ j = y := by
  obtain ⟨k, hk, hky⟩ := cycle_exists_pow_lt h.isCycle hx₀ hy
  exact ⟨⟨k, hk⟩, hky⟩

/-- The left edge at species `y`: its incidence with its own channel class. -/
def leftAt (h : N.CycleChannels c ch) (y : S) (hy : y ∈ c.support) : N.TrueSREdge :=
  N.bcEdge (ch y) (h.nonflow y hy) y (h.coeff_self y hy)

/-- The right edge at species `y`: the incidence of `c y` with the channel class of `y`. -/
def rightAt (h : N.CycleChannels c ch) (y : S) (hy : y ∈ c.support) : N.TrueSREdge :=
  N.bcEdge (ch y) (h.nonflow y hy) (c y) (h.coeff_next y hy)

/-- **The true-SR cycle of a permutation cycle.** -/
def toCycle (h : N.CycleChannels c ch) (x₀ : S) (hx₀ : x₀ ∈ c.support) :
    N.TrueSRCycle #c.support where
  nontrivial := h.isCycle.two_le_card_support
  species := h.sp x₀
  reaction := fun j => N.trueReaction (ch (h.sp x₀ j))
  leftEdge := fun j => h.leftAt (h.sp x₀ j) (h.sp_mem hx₀ j)
  rightEdge := fun j => h.rightAt (h.sp x₀ j) (h.sp_mem hx₀ j)
  left_species := fun _ => rfl
  left_reaction := fun _ => rfl
  right_species := fun j => (h.sp_succ x₀ j).symm
  right_reaction := fun _ => rfl
  species_injective := h.sp_injective hx₀
  reaction_injective := by
    intro a b hab
    exact h.sp_injective hx₀ (h.class_inj _ (h.sp_mem hx₀ a) _ (h.sp_mem hx₀ b) hab)

theorem toCycle_species (h : N.CycleChannels c ch) (x₀ : S) (hx₀ : x₀ ∈ c.support) (j) :
    (h.toCycle x₀ hx₀).species j = (c ^ (j : ℕ)) x₀ := rfl

/-- The product over the support equals the product over the enumeration. -/
theorem prod_support_eq (h : N.CycleChannels c ch) {x₀ : S} (hx₀ : x₀ ∈ c.support)
    (F : S → ℝ) :
    ∏ y ∈ c.support, F y = ∏ j : Fin #c.support, F (h.sp x₀ j) := by
  symm
  refine Finset.prod_nbij (h.sp x₀) (fun j _ => h.sp_mem hx₀ j) ?_ ?_ (fun _ _ => rfl)
  · intro a _ b _ hab
    exact h.sp_injective hx₀ hab
  · intro y hy
    obtain ⟨j, hj⟩ := h.sp_surj hx₀ hy
    exact ⟨j, Finset.mem_coe.mpr (Finset.mem_univ _), hj⟩

theorem isCPair_iff (h : N.CycleChannels c ch) (hsep : N.ReactantProductSeparated)
    {x₀ : S} (hx₀ : x₀ ∈ c.support) (j : Fin #c.support) :
    (h.toCycle x₀ hx₀).isCPair j ↔
      (N.reactionVector (ch (h.sp x₀ j)) (h.sp x₀ j) < 0 ↔
        N.reactionVector (ch (h.sp x₀ j)) (c (h.sp x₀ j)) < 0) :=
  N.bcEndpoint_eq_iff hsep _ _ _ (h.coeff_self _ (h.sp_mem hx₀ j))
    (h.coeff_next _ (h.sp_mem hx₀ j))

theorem right_coeff (h : N.CycleChannels c ch) (hsep : N.ReactantProductSeparated)
    {x₀ : S} (hx₀ : x₀ ∈ c.support) (j : Fin #c.support) :
    (((h.toCycle x₀ hx₀).rightEdge j).coeff : ℝ) =
      |N.reactionVector (ch (h.sp x₀ j)) (c (h.sp x₀ j))| :=
  N.bcEdge_coeff_cast hsep (ch (h.sp x₀ j)) (h.nonflow _ (h.sp_mem hx₀ j)) (c (h.sp x₀ j))
    (h.coeff_next _ (h.sp_mem hx₀ j))

theorem left_coeff (h : N.CycleChannels c ch) (hsep : N.ReactantProductSeparated)
    {x₀ : S} (hx₀ : x₀ ∈ c.support) (j : Fin #c.support) :
    (((h.toCycle x₀ hx₀).leftEdge j).coeff : ℝ) =
      |N.reactionVector (ch (h.sp x₀ j)) (h.sp x₀ j)| :=
  N.bcEdge_coeff_cast hsep (ch (h.sp x₀ j)) (h.nonflow _ (h.sp_mem hx₀ j)) (h.sp x₀ j)
    (h.coeff_self _ (h.sp_mem hx₀ j))

theorem numCPairs_le (h : N.CycleChannels c ch) {x₀ : S} (hx₀ : x₀ ∈ c.support) :
    (h.toCycle x₀ hx₀).numCPairs ≤ #c.support := by
  classical
  unfold TrueSRCycle.numCPairs
  exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, Fintype.card_fin])

theorem card_not_cpair (h : N.CycleChannels c ch) {x₀ : S} (hx₀ : x₀ ∈ c.support)
    [DecidablePred fun j => ¬ (h.toCycle x₀ hx₀).isCPair j] :
    (Finset.univ.filter (fun j => ¬ (h.toCycle x₀ hx₀).isCPair j)).card =
      #c.support - (h.toCycle x₀ hx₀).numCPairs := by
  classical
  have h1 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin #c.support))) (fun j => (h.toCycle x₀ hx₀).isCPair j)
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have key : (Finset.univ.filter (fun j => ¬ (h.toCycle x₀ hx₀).isCPair j)).card +
      (h.toCycle x₀ hx₀).numCPairs = #c.support := by
    unfold TrueSRCycle.numCPairs
    rw [add_comm]
    convert h1 using 3
  omega

end CycleChannels

theorem neg_one_pow_mul_neg_one_pow_sub {n k : ℕ} (hk : k ≤ n) :
    ((-1 : ℝ) ^ n) * (-1) ^ (n - k) = (-1) ^ k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = k + m := ⟨n - k, by omega⟩
  rw [Nat.add_sub_cancel_left, pow_add, mul_assoc, ← pow_add, ← two_mul, pow_mul]
  norm_num

namespace CycleChannels

variable {N : Network S} {c : Perm S} {ch : S → N.R}

/-- **The signed weight of a permutation cycle in true-SR terms.** -/
theorem signed_weight_eq (h : N.CycleChannels c ch) (hsep : N.ReactantProductSeparated)
    {x₀ : S} (hx₀ : x₀ ∈ c.support) :
    ((Perm.sign c : ℤ) : ℝ) *
        ∏ y ∈ c.support, (N.reactionVector (ch y) (c y) / N.reactionVector (ch y) y) =
      -(-1) ^ (h.toCycle x₀ hx₀).numCPairs *
        ((∏ j, (((h.toCycle x₀ hx₀).rightEdge j).coeff : ℝ)) /
          ∏ j, (((h.toCycle x₀ hx₀).leftEdge j).coeff : ℝ)) := by
  classical
  rw [h.prod_support_eq hx₀]
  have hfac : ∀ j : Fin #c.support,
      N.reactionVector (ch (h.sp x₀ j)) (c (h.sp x₀ j)) /
          N.reactionVector (ch (h.sp x₀ j)) (h.sp x₀ j) =
        (if (h.toCycle x₀ hx₀).isCPair j then 1 else -1) *
          ((((h.toCycle x₀ hx₀).rightEdge j).coeff : ℝ) /
            (((h.toCycle x₀ hx₀).leftEdge j).coeff : ℝ)) := by
    intro j
    have hy := h.sp_mem hx₀ j
    have hs := h.coeff_self _ hy
    have ht := h.coeff_next _ hy
    rw [div_eq_sign_mul_abs_div ht hs, h.right_coeff hsep hx₀ j, h.left_coeff hsep hx₀ j]
    have hcp := h.isCPair_iff hsep hx₀ j
    by_cases hc : (h.toCycle x₀ hx₀).isCPair j
    · rw [if_pos hc, if_pos (hcp.mp hc)]
    · rw [if_neg hc, if_neg (fun h' => hc (hcp.mpr h'))]
  simp_rw [hfac]
  rw [Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const_one, one_mul,
    Finset.prod_const, Finset.prod_div_distrib, h.card_not_cpair hx₀, h.isCycle.sign]
  have hpow := neg_one_pow_mul_neg_one_pow_sub (h.numCPairs_le hx₀)
  have hsign : (((-(-1) ^ #c.support : ℤˣ) : ℤ) : ℝ) = -(-1 : ℝ) ^ #c.support := by
    push_cast
    ring
  rw [hsign, ← hpow]
  ring

/-- The left labels have positive product. -/
theorem prod_left_pos (h : N.CycleChannels c ch) {x₀ : S} (hx₀ : x₀ ∈ c.support) :
    0 < ∏ j, (((h.toCycle x₀ hx₀).leftEdge j).coeff : ℝ) :=
  Finset.prod_pos fun j _ => by exact_mod_cast TrueSREdge.coeff_pos _

theorem prod_right_pos (h : N.CycleChannels c ch) {x₀ : S} (hx₀ : x₀ ∈ c.support) :
    0 < ∏ j, (((h.toCycle x₀ hx₀).rightEdge j).coeff : ℝ) :=
  Finset.prod_pos fun j _ => by exact_mod_cast TrueSREdge.coeff_pos _

/-- **A negative signed weight forces an even cycle.** -/
theorem even_of_weight_neg (h : N.CycleChannels c ch) (hsep : N.ReactantProductSeparated)
    {x₀ : S} (hx₀ : x₀ ∈ c.support)
    (hneg : ((Perm.sign c : ℤ) : ℝ) *
        ∏ y ∈ c.support, (N.reactionVector (ch y) (c y) / N.reactionVector (ch y) y) < 0) :
    (h.toCycle x₀ hx₀).Even := by
  rw [h.signed_weight_eq hsep hx₀] at hneg
  by_contra hodd
  have hodd' : Odd (h.toCycle x₀ hx₀).numCPairs := Nat.not_even_iff_odd.mp hodd
  rw [hodd'.neg_one_pow] at hneg
  have := div_pos (h.prod_right_pos hx₀) (h.prod_left_pos hx₀)
  simp only [neg_neg, one_mul] at hneg
  linarith

/-- **For an even s-cycle the signed weight is `-1`.** -/
theorem weight_eq_neg_one_of_sCycle (h : N.CycleChannels c ch)
    (hsep : N.ReactantProductSeparated) {x₀ : S} (hx₀ : x₀ ∈ c.support)
    (heven : (h.toCycle x₀ hx₀).Even) (hs : (h.toCycle x₀ hx₀).SCycle) :
    ((Perm.sign c : ℤ) : ℝ) *
        ∏ y ∈ c.support, (N.reactionVector (ch y) (c y) / N.reactionVector (ch y) y) = -1 := by
  rw [h.signed_weight_eq hsep hx₀, heven.neg_one_pow]
  have hs' : (∏ j, (((h.toCycle x₀ hx₀).leftEdge j).coeff : ℝ)) =
      ∏ j, (((h.toCycle x₀ hx₀).rightEdge j).coeff : ℝ) := by
    have := congrArg (fun k : ℕ => (k : ℝ)) hs
    simpa [Nat.cast_prod] using this
  rw [hs', div_self (ne_of_gt (h.prod_right_pos hx₀))]
  ring

end CycleChannels

end Network
end CRNT
