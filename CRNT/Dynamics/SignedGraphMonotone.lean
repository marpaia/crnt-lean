import CRNT.Dynamics.OrthantMonotone

/-!
# A signed-graph criterion for orthant monotonicity (Harary balance)

The **interaction graph** of a network has an edge between species `j` and `i ≠ j` for every
reaction `r` with `j` among its reactants and `i` changed by it, signed by the sign of the
change `(y'_r − y_r)_i`. The graph is **balanced** if no closed walk has an odd number of
negative edges; we formalize this through signed reachability on `S × {±1}`: a walk from `(i, 1)`
never ends at `(i, −1)`.

`exists_orthantCooperative_of_balanced` (Harary's switching theorem, in this setting): a balanced
interaction graph admits a sign vector `σ` with `σ_i σ_j (y'_r − y_r)_i ≥ 0` on every edge, so the
network is orthant-cooperative for `σ` and its mass-action flow preserves `≤_σ`
(`massAction_orthant_preserving`).
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The sign `±1` of a real number (`1` for nonnegative). -/
noncomputable def sgnU (v : ℝ) : ℤˣ := if 0 ≤ v then 1 else -1

theorem sgnU_mul_self_nonneg (v : ℝ) : 0 ≤ ((sgnU v : ℤ) : ℝ) * v := by
  unfold sgnU; split_ifs with h
  · simpa using h
  · push Not at h; simp; linarith

/-- An edge of the interaction graph: `j` is a reactant of `r`, `i ≠ j` is changed by `r`. -/
def InteractionEdge (N : Network S) (r : N.R) (j i : S) : Prop :=
  j ≠ i ∧ (N.reaction r).source j ≠ 0 ∧ N.reactionVector r i ≠ 0

/-- One signed step of the undirected interaction graph. -/
def SignedStep (N : Network S) (p q : S × ℤˣ) : Prop :=
  ∃ r : N.R, (N.InteractionEdge r p.1 q.1 ∧ q.2 = p.2 * sgnU (N.reactionVector r q.1)) ∨
    (N.InteractionEdge r q.1 p.1 ∧ q.2 = p.2 * sgnU (N.reactionVector r p.1))

/-- **Balance**: no walk returns to a species with the opposite sign. -/
def InteractionBalanced (N : Network S) : Prop :=
  ∀ i : S, ¬ Relation.ReflTransGen N.SignedStep (i, 1) (i, -1)

theorem units_sq (u : ℤˣ) : u * u = 1 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

theorem SignedStep.symm {N : Network S} {p q : S × ℤˣ} (h : N.SignedStep p q) :
    N.SignedStep q p := by
  obtain ⟨r, h | h⟩ := h
  · refine ⟨r, Or.inr ⟨h.1, ?_⟩⟩
    rw [h.2, mul_assoc, units_sq, mul_one]
  · refine ⟨r, Or.inl ⟨h.1, ?_⟩⟩
    rw [h.2, mul_assoc, units_sq, mul_one]

theorem SignedStep.scale {N : Network S} {p q : S × ℤˣ} (h : N.SignedStep p q) (c : ℤˣ) :
    N.SignedStep (p.1, c * p.2) (q.1, c * q.2) := by
  obtain ⟨r, h | h⟩ := h
  · exact ⟨r, Or.inl ⟨h.1, by rw [h.2, mul_assoc]⟩⟩
  · exact ⟨r, Or.inr ⟨h.1, by rw [h.2, mul_assoc]⟩⟩

theorem reach_symm {N : Network S} {p q : S × ℤˣ}
    (h : Relation.ReflTransGen N.SignedStep p q) : Relation.ReflTransGen N.SignedStep q p := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hst ih => exact Relation.ReflTransGen.head hst.symm ih

theorem reach_scale {N : Network S} {p q : S × ℤˣ}
    (h : Relation.ReflTransGen N.SignedStep p q) (c : ℤˣ) :
    Relation.ReflTransGen N.SignedStep (p.1, c * p.2) (q.1, c * q.2) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hst ih => exact ih.tail (hst.scale c)

/-- Species in the same component. -/
def SameComp (N : Network S) (i j : S) : Prop :=
  ∃ a : ℤˣ, Relation.ReflTransGen N.SignedStep (i, 1) (j, a)

theorem SameComp.refl' (N : Network S) (i : S) : N.SameComp i i :=
  ⟨1, Relation.ReflTransGen.refl⟩

theorem SameComp.symm' {N : Network S} {i j : S} (h : N.SameComp i j) : N.SameComp j i := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a⁻¹, ?_⟩
  have := reach_scale (reach_symm ha) a⁻¹
  simpa using this

theorem SameComp.trans' {N : Network S} {i j k : S} (h₁ : N.SameComp i j) (h₂ : N.SameComp j k) :
    N.SameComp i k := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  refine ⟨a * b, ha.trans ?_⟩
  have := reach_scale hb a
  simpa using this

/-- Uniqueness of the sign reached from `(i, 1)` at `j`, under balance. -/
theorem sign_unique {N : Network S} (hbal : N.InteractionBalanced) {i j : S} {a b : ℤˣ}
    (ha : Relation.ReflTransGen N.SignedStep (i, 1) (j, a))
    (hb : Relation.ReflTransGen N.SignedStep (i, 1) (j, b)) : a = b := by
  by_contra hne
  have hab : b = -a := by
    rcases Int.units_eq_one_or a with h | h <;> rcases Int.units_eq_one_or b with h' | h' <;>
      simp_all
  -- `(i,1) → (j,b) = (j,−a) → (i,−1)`
  have hback := reach_scale (reach_symm ha) (-1)
  simp only [mul_one, neg_mul, one_mul] at hback
  apply hbal i
  refine hb.trans ?_
  rw [hab]
  convert hback using 2

/-- **Harary's switching theorem for the interaction graph.** -/
theorem exists_orthantCooperative_of_balanced {N : Network S} (hbal : N.InteractionBalanced) :
    ∃ σ : S → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) ∧ N.IsOrthantCooperative σ := by
  classical
  -- a canonical root in each component: the least element under an enumeration
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  have hcomp_ne : ∀ i, (Finset.univ.filter fun j => N.SameComp i j).Nonempty := fun i =>
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, SameComp.refl' N i⟩⟩
  let root : S → S := fun i =>
    e.symm ((Finset.univ.filter fun j => N.SameComp i j).image e |>.min' ((hcomp_ne i).image e))
  have hroot_mem : ∀ i, N.SameComp i (root i) := by
    intro i
    have h := Finset.min'_mem ((Finset.univ.filter fun j => N.SameComp i j).image e)
      ((hcomp_ne i).image e)
    obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp h
    have : root i = j := by simp only [root]; rw [← hje, Equiv.symm_apply_apply]
    rw [this]; exact (Finset.mem_filter.mp hj).2
  have hroot_eq : ∀ i j, N.SameComp i j → root i = root j := by
    intro i j hij
    have hset : (Finset.univ.filter fun k => N.SameComp i k) =
        (Finset.univ.filter fun k => N.SameComp j k) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => hij.symm'.trans' h, fun h => hij.trans' h⟩
    simp only [root, hset]
  -- the sign of `i` relative to its root
  have hsign : ∀ i, ∃ a : ℤˣ, Relation.ReflTransGen N.SignedStep (root i, 1) (i, a) :=
    fun i => (hroot_mem i).symm'
  choose σU hσU using hsign
  refine ⟨fun i => ((σU i : ℤ) : ℝ), fun i => ?_, ?_⟩
  · rcases Int.units_eq_one_or (σU i) with h | h <;> simp [h]
  · intro r i j hji hj
    by_cases hv : N.reactionVector r i = 0
    · show 0 ≤ ((σU i : ℤ) : ℝ) * ((σU j : ℤ) : ℝ) * N.reactionVector r i
      rw [hv, mul_zero]
    · have hedge : N.InteractionEdge r j i := ⟨hji, hj, hv⟩
      have hstep : N.SignedStep (j, σU j) (i, σU j * sgnU (N.reactionVector r i)) :=
        ⟨r, Or.inl ⟨hedge, rfl⟩⟩
      have hsame : N.SameComp j i :=
        ⟨1 * sgnU (N.reactionVector r i), Relation.ReflTransGen.single ⟨r, Or.inl ⟨hedge, rfl⟩⟩⟩
      have hri : root j = root i := hroot_eq j i hsame
      have h1 : Relation.ReflTransGen N.SignedStep (root i, 1)
          (i, σU j * sgnU (N.reactionVector r i)) := by
        rw [← hri]; exact (hσU j).tail hstep
      have hσi : σU i = σU j * sgnU (N.reactionVector r i) := sign_unique hbal (hσU i) h1
      show 0 ≤ ((σU i : ℤ) : ℝ) * ((σU j : ℤ) : ℝ) * N.reactionVector r i
      rw [hσi]
      have hsq : ((σU j : ℤ) : ℝ) * ((σU j : ℤ) : ℝ) = 1 := by
        rcases Int.units_eq_one_or (σU j) with h | h <;> simp [h]
      have : ((((σU j * sgnU (N.reactionVector r i)) : ℤˣ) : ℤ) : ℝ) * ((σU j : ℤ) : ℝ) *
          N.reactionVector r i = (((sgnU (N.reactionVector r i) : ℤˣ) : ℤ) : ℝ) *
            N.reactionVector r i := by
        push_cast
        rw [show ((σU j : ℤ) : ℝ) * ((sgnU (N.reactionVector r i) : ℤ) : ℝ) * ((σU j : ℤ) : ℝ) *
          N.reactionVector r i = (((σU j : ℤ) : ℝ) * ((σU j : ℤ) : ℝ)) *
            (((sgnU (N.reactionVector r i) : ℤ) : ℝ) * N.reactionVector r i) by ring, hsq, one_mul]
      rw [this]
      exact sgnU_mul_self_nonneg _

/-- **Balanced interaction graphs give orthant-monotone mass-action flows.** -/
theorem massAction_orthant_preserving_of_balanced {N : Network S} (hbal : N.InteractionBalanced)
    (κ : N.RateConstants) :
    ∃ σ : S → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) ∧ ∀ (M T : ℝ) {x y : ℝ → Concentration S},
      (∀ t ∈ Set.Icc 0 T, HasDerivWithinAt x (N.massActionVectorField κ (x t)) (Set.Icc 0 T) t) →
      (∀ t ∈ Set.Icc 0 T, HasDerivWithinAt y (N.massActionVectorField κ (y t)) (Set.Icc 0 T) t) →
      (∀ t ∈ Set.Icc 0 T, x t ∈ Set.Icc (0 : S → ℝ) (fun _ => M)) →
      (∀ t ∈ Set.Icc 0 T, y t ∈ Set.Icc (0 : S → ℝ) (fun _ => M)) →
      Monotone.OrthantLE σ (x 0) (y 0) → ∀ t ∈ Set.Icc 0 T, Monotone.OrthantLE σ (x t) (y t) := by
  obtain ⟨σ, hσ, hcoop⟩ := exists_orthantCooperative_of_balanced hbal
  exact ⟨σ, hσ, fun M T x y hx hy hxK hyK h0 =>
    N.massAction_orthant_preserving κ hσ hcoop M hx hy hxK hyK h0⟩

/-- If every edge of the interaction graph is positive, the graph is balanced. -/
theorem interactionBalanced_of_edges_pos {N : Network S}
    (hpos : ∀ r i j, N.InteractionEdge r j i → 0 < N.reactionVector r i) :
    N.InteractionBalanced := by
  intro i h
  have key : ∀ q : S × ℤˣ, Relation.ReflTransGen N.SignedStep (i, 1) q → q.2 = 1 := by
    intro q hq
    induction hq with
    | refl => rfl
    | @tail b c _ hbc ih =>
        obtain ⟨r, h | h⟩ := hbc
        · rw [h.2, ih, one_mul]; unfold sgnU; rw [if_pos (hpos r _ _ h.1).le]
        · rw [h.2, ih, one_mul]; unfold sgnU; rw [if_pos (hpos r _ _ h.1).le]
  have h1 : ((-1 : ℤˣ)) = 1 := key _ h
  exact absurd h1 (by decide)

end Network
end CRNT
