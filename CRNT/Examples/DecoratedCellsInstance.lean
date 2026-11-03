import CRNT.Multistationarity.DecoratedSimplices

/-!
# Non-vacuity of `multistationary_of_two_decoratedCells`

The one-species network `0 ⇌ X`, `2X ⇌ 3X` with unit rates and heights `h(n) = n(n−1)/2` on the
complexes `nX` (a strictly convex lifting `0, 0, 1, 3`) has the lower cells `{0, X}` (normal
`w = 0`, `c = 0`) and `{X, 2X}` (`w = −1`, `c = −1`). Both are positively decorated: the
combined reaction vectors are `+1, −1` and `−1, +1`. The theorem gives multistationarity.
-/

namespace CRNT

namespace Examples

namespace DecoratedCells

open Network

/-- The complex `nX`. -/
def cx (n : ℕ) : Complex Unit := fun _ => n

/-- `0 ⇌ X`, `2X ⇌ 3X`. -/
def net : Network Unit :=
  ⟨Fin 4, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨cx 0, cx 1⟩ else if r = 1 then ⟨cx 1, cx 0⟩
    else if r = 2 then ⟨cx 2, cx 3⟩ else ⟨cx 3, cx 2⟩⟩

/-- Unit rate constants. -/
def κ : RateConstants net := ⟨fun _ => 1, fun _ => one_pos⟩

/-- Heights `h(nX) = n(n−1)/2`. -/
def h (a : Complex Unit) : ℕ := a () * (a () - 1) / 2

theorem cx_inj {m n : ℕ} (h : cx m = cx n) : m = n := congrFun h ()

@[simp] theorem cx_eq_cx {m n : ℕ} : cx m = cx n ↔ m = n := ⟨cx_inj, congrArg cx⟩

theorem source_eq (r : Fin 4) : (net.reaction r).source =
    cx (if r = 0 then 0 else if r = 1 then 1 else if r = 2 then 2 else 3) := by
  fin_cases r <;> rfl

theorem reactionVector_eq (r : Fin 4) : net.reactionVector r =
    fun _ => (if r = 0 then 1 else if r = 1 then -1 else if r = 2 then 1 else -1 : ℝ) := by
  fin_cases r <;> (funext u; simp [Network.reactionVector, net, cx]) <;> norm_num

theorem combined_cx (n : ℕ) : combinedVector net κ (cx n) =
    fun _ => (if n = 0 then 1 else if n = 1 then -1 else if n = 2 then 1 else if n = 3 then -1
      else 0 : ℝ) := by
  classical
  funext u
  simp only [combinedVector, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change ∑ r ∈ Finset.univ.filter (fun r : Fin 4 => (net.reaction r).source = cx n),
    κ.k r * net.reactionVector r u = _
  simp only [source_eq, reactionVector_eq]
  rw [Finset.sum_filter, Fin.sum_univ_four]
  have hk : ∀ r : Fin 4, κ.k r = 1 := fun _ => rfl
  simp only [hk, one_mul]
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n <;> simp
  · have h0 : ¬ (0 = n) := by omega
    have h1 : ¬ (1 = n) := by omega
    have h2 : ¬ (2 = n) := by omega
    have h3 : ¬ (3 = n) := by omega
    have h0' : ¬ (n = 0) := by omega
    have h1' : ¬ (n = 1) := by omega
    have h2' : ¬ (n = 2) := by omega
    have h3' : ¬ (n = 3) := by omega
    simp [h0, h1, h2, h3, h0', h1', h2', h3']

/-- Linear independence of the affine rows of two distinct one-species complexes. -/
theorem affInd_pair (m n : ℕ) (hmn : m ≠ n) :
    LinearIndependent ℝ (fun a : ({cx m, cx n} : Finset (Complex Unit)) => affineRow a.1) := by
  classical
  have hne : cx m ≠ cx n := fun e => hmn (cx_inj e)
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hsum : ∀ j : Option Unit,
      ∑ a : ({cx m, cx n} : Finset (Complex Unit)), g a * affineRow a.1 j = 0 := by
    intro j; have := congrFun hg j; simpa [Finset.sum_apply] using this
  set A : ({cx m, cx n} : Finset (Complex Unit)) := ⟨cx m, by simp⟩
  set B : ({cx m, cx n} : Finset (Complex Unit)) := ⟨cx n, by simp⟩
  have hAB : A ≠ B := fun e => hne (congrArg Subtype.val e)
  have huniv : (Finset.univ : Finset ({cx m, cx n} : Finset (Complex Unit))) = {A, B} := by
    ext a
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases Finset.mem_insert.mp a.2 with h | h
    · left; exact Subtype.ext h
    · right; exact Subtype.ext (Finset.mem_singleton.mp h)
  have e0 := hsum none
  have e1 := hsum (some ())
  rw [huniv, Finset.sum_pair hAB] at e0 e1
  simp only [affineRow, Option.elim, A, B, cx, mul_one] at e0 e1
  have hmn' : (m : ℝ) ≠ n := by exact_mod_cast hmn
  have hgB : g B = 0 := by
    have : g A * m + g B * n = 0 := e1
    have h2 : g A = -g B := by linarith
    rw [h2] at this
    have : g B * ((n : ℝ) - m) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h).symm hmn'
  have hgA : g A = 0 := by linarith
  intro a
  rcases Finset.mem_insert.mp a.2 with h | h
  · have : a = A := Subtype.ext h
    rw [this]; exact hgA
  · have : a = B := Subtype.ext (Finset.mem_singleton.mp h)
    rw [this]; exact hgB

/-- Spanning: a nonzero vector spans `ℝ^Unit`. -/
theorem span_top_of_ne {ι : Type*} (W : ι → (Unit → ℝ)) (i : ι) (hi : W i () ≠ 0) :
    Submodule.span ℝ (Set.range W) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have : v = (v () / W i ()) • W i := by
    funext u; cases u; simp only [Pi.smul_apply, smul_eq_mul]; field_simp
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem pairing_cx (w : Unit → ℤ) (n : ℕ) : pairing w (cx n) = w () * n := by
  simp [pairing, cx]

theorem h_cx (n : ℕ) : h (cx n) = n * (n - 1) / 2 := rfl

/-- The lower cell `{0, X}`. -/
noncomputable def cell₁ : DecoratedCell net κ h where
  Δ := {cx 0, cx 1}
  w := fun _ => 0
  c := 0
  card := by
    rw [Fintype.card_coe, Finset.card_pair (fun e => absurd (cx_inj e) (by norm_num))]; rfl
  affInd := affInd_pair 0 1 (by norm_num)
  onCell := by
    intro a ha
    rcases Finset.mem_insert.mp ha with h' | h' <;>
      [rw [h']; rw [Finset.mem_singleton.mp h']] <;> simp [pairing_cx, h_cx]
  offCell := by
    intro r hr
    fin_cases r <;> simp_all [net, pairing_cx, h_cx]
  span := span_top_of_ne _ ⟨cx 0, by simp⟩ (by simp [combined_cx])
  lam := fun _ => 1
  lam_pos := fun _ => one_pos
  lam_ker := by
    classical
    have hne : cx 0 ≠ cx 1 := fun e => absurd (cx_inj e) (by norm_num)
    rw [Finset.sum_coe_sort {cx 0, cx 1} (fun a => (1 : ℝ) • combinedVector net κ a),
      Finset.sum_pair hne]
    funext u
    simp [combined_cx]

/-- The lower cell `{X, 2X}`. -/
noncomputable def cell₂ : DecoratedCell net κ h where
  Δ := {cx 1, cx 2}
  w := fun _ => -1
  c := -1
  card := by
    rw [Fintype.card_coe, Finset.card_pair (fun e => absurd (cx_inj e) (by norm_num))]; rfl
  affInd := affInd_pair 1 2 (by norm_num)
  onCell := by
    intro a ha
    rcases Finset.mem_insert.mp ha with h' | h' <;>
      [rw [h']; rw [Finset.mem_singleton.mp h']] <;> simp [pairing_cx, h_cx]
  offCell := by
    intro r hr
    fin_cases r <;> simp_all [net, pairing_cx, h_cx]
  span := span_top_of_ne _ ⟨cx 1, by simp⟩ (by simp [combined_cx])
  lam := fun _ => 1
  lam_pos := fun _ => one_pos
  lam_ker := by
    classical
    have hne : cx 1 ≠ cx 2 := fun e => absurd (cx_inj e) (by norm_num)
    rw [Finset.sum_coe_sort {cx 1, cx 2} (fun a => (1 : ℝ) • combinedVector net κ a),
      Finset.sum_pair hne]
    funext u
    simp [combined_cx]

/-- **Non-vacuity.** `0 ⇌ X`, `2X ⇌ 3X` is multistationary, by two decorated cells. -/
theorem multistationary : net.HasMultistationarityCapacity :=
  multistationary_of_two_decoratedCells cell₁ cell₂ (fun e => by
    have := congrFun e (); simp [cell₁, cell₂] at this)

end DecoratedCells

end Examples

end CRNT
