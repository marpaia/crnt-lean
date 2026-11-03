import CRNT.Multistationarity.DecoratedSimplicesConservation
import CRNT.Multistationarity.MultistationarityRegionOpen

/-!
# Non-vacuity of `steadyStates_of_augmentedCells`

The network `X → Y`, `Y → X`, `2X + Y → 3X`, `X + 2Y → 3Y` conserves `X + Y`. With `Z v = v_X`,
`L v = v_X + v_Y`, unit rates and total `1`, the augmented system has support
`{0, X, Y, 2X + Y, X + 2Y}` and coefficient vectors `(0, −1)`, `(−1, 1)`, `(1, 1)`, `(1, 0)`,
`(−1, 0)`. For the heights `h(2X + Y) = h(X + 2Y) = −1` (zero elsewhere) the triangles
`{0, X, 2X + Y}` (normal `(0, 1)`) and `{0, Y, X + 2Y}` (normal `(1, 0)`) are positively decorated
lower cells. The theorem gives two distinct nondegenerate positive steady states in one class.
-/

namespace CRNT

namespace Examples

namespace AugmentedCells

open Network

/-- The complex `iX + jY`. -/
def cpx (i j : ℕ) : Complex (Fin 2) := ![i, j]

@[simp] theorem cpx_eq_cpx {i j k l : ℕ} : cpx i j = cpx k l ↔ i = k ∧ j = l := by
  constructor
  · intro h; exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨rfl, rfl⟩; rfl

@[simp] theorem cpx_apply_zero (i j : ℕ) : cpx i j 0 = i := rfl
@[simp] theorem cpx_apply_one (i j : ℕ) : cpx i j 1 = j := rfl

theorem zero_eq_cpx : (0 : Complex (Fin 2)) = cpx 0 0 := by
  funext s; fin_cases s <;> rfl

/-- `X → Y`, `Y → X`, `2X + Y → 3X`, `X + 2Y → 3Y`. -/
def net : Network (Fin 2) :=
  ⟨Fin 4, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨cpx 1 0, cpx 0 1⟩ else if r = 1 then ⟨cpx 0 1, cpx 1 0⟩
    else if r = 2 then ⟨cpx 2 1, cpx 3 0⟩ else ⟨cpx 1 2, cpx 0 3⟩⟩

def κ : RateConstants net := ⟨fun _ => 1, fun _ => one_pos⟩

/-- `Z v = v_X`. -/
def Z : (Fin 2 → ℝ) →ₗ[ℝ] (Unit → ℝ) :=
  { toFun := fun v _ => v 0, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

/-- `L v = v_X + v_Y`. -/
def L : (Fin 2 → ℝ) →ₗ[ℝ] (Unit → ℝ) :=
  { toFun := fun v _ => v 0 + v 1
    map_add' := fun u v => by funext; simp; ring
    map_smul' := fun c v => by funext; simp; ring }

def T : Unit → ℝ := fun _ => 1

/-- Heights `−1` on `2X + Y` and `X + 2Y`, zero elsewhere. -/
def h (a : Complex (Fin 2)) : ℤ := if a = cpx 2 1 ∨ a = cpx 1 2 then -1 else 0

theorem source_eq (r : Fin 4) : (net.reaction r).source =
    if r = 0 then cpx 1 0 else if r = 1 then cpx 0 1 else if r = 2 then cpx 2 1 else cpx 1 2 := by
  fin_cases r <;> rfl

theorem reactionVector_eq (r : Fin 4) : net.reactionVector r =
    fun s => (if r = 0 ∨ r = 3 then (if s = 0 then -1 else 1)
      else (if s = 0 then 1 else -1) : ℝ) := by
  fin_cases r <;> (funext s; fin_cases s <;> simp [Network.reactionVector, net, cpx]) <;> norm_num

theorem unitComplex_zero : unitComplex (0 : Fin 2) = cpx 1 0 := by
  funext s; fin_cases s <;> rfl
theorem unitComplex_one : unitComplex (1 : Fin 2) = cpx 0 1 := by
  funext s; fin_cases s <;> rfl

theorem hh : ∀ i, h (unitComplex i) = 0 := by
  intro i; fin_cases i
  · show h (unitComplex 0) = 0; rw [unitComplex_zero]; simp [h]
  · show h (unitComplex 1) = 0; rw [unitComplex_one]; simp [h]

/-- The stoichiometric subspace is the line `v_X + v_Y = 0`. -/
theorem mem_stoich_iff (v : Fin 2 → ℝ) : v ∈ net.stoichSubspace ↔ v 0 + v 1 = 0 := by
  constructor
  · intro hv
    have hsub : net.stoichSubspace ≤ LinearMap.ker L := by
      apply Submodule.span_le.2
      rintro _ ⟨r, rfl⟩
      show L (net.reactionVector r) = 0
      funext u
      fin_cases r <;> simp [L, Network.reactionVector, net, cpx] <;> norm_num
    have := hsub hv
    exact congrFun this ()
  · intro hv
    have : v = v 0 • net.reactionVector (1 : Fin 4) := by
      funext s
      rw [reactionVector_eq]
      fin_cases s <;> simp <;> linarith
    rw [this]
    exact Submodule.smul_mem _ _ (net.reactionVector_mem_stoichSubspace _)

theorem hZ : ∀ v ∈ net.stoichSubspace, Z v = 0 → v = 0 := by
  intro v hv hz
  have h0 : v 0 = 0 := congrFun hz ()
  have h1 := (mem_stoich_iff v).mp hv
  funext s; fin_cases s
  · exact h0
  · show v 1 = 0; linarith

theorem hL : ∀ v, L v = 0 ↔ v ∈ net.stoichSubspace := by
  intro v
  rw [mem_stoich_iff]
  constructor
  · intro h; exact congrFun h ()
  · intro h; funext u; exact h

theorem combined_eq (a : Complex (Fin 2)) : combinedVector net κ a =
    fun s => (if a = cpx 1 0 ∨ a = cpx 1 2 then (if s = 0 then -1 else 1)
      else if a = cpx 0 1 ∨ a = cpx 2 1 then (if s = 0 then 1 else -1) else 0 : ℝ) := by
  classical
  funext s
  simp only [combinedVector, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change ∑ r ∈ Finset.univ.filter (fun r : Fin 4 => (net.reaction r).source = a),
    κ.k r * net.reactionVector r s = _
  simp only [source_eq, reactionVector_eq]
  rw [Finset.sum_filter, Fin.sum_univ_four]
  have hk : ∀ r : Fin 4, κ.k r = 1 := fun _ => rfl
  simp only [hk, one_mul]
  by_cases h1 : a = cpx 1 0
  · subst h1; fin_cases s <;> simp
  by_cases h2 : a = cpx 0 1
  · subst h2; fin_cases s <;> simp
  by_cases h3 : a = cpx 2 1
  · subst h3; fin_cases s <;> simp
  by_cases h4 : a = cpx 1 2
  · subst h4; fin_cases s <;> simp
  simp [Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, h1, h2, h3, h4]

theorem support_eq : augSupport net = {cpx 1 0, cpx 0 1, cpx 2 1, cpx 1 2, cpx 0 0} := by
  classical
  ext a
  simp only [augSupport, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_singleton, Finset.mem_insert]
  constructor
  · rintro ((⟨r, rfl⟩ | ⟨i, rfl⟩) | rfl)
    · fin_cases r <;> simp [net]
    · fin_cases i
      · left; exact unitComplex_zero
      · right; left; exact unitComplex_one
    · right; right; right; right; exact zero_eq_cpx
  · rintro (rfl | rfl | rfl | rfl | rfl)
    · left; left; exact ⟨(0 : Fin 4), rfl⟩
    · left; left; exact ⟨(1 : Fin 4), rfl⟩
    · left; left; exact ⟨(2 : Fin 4), rfl⟩
    · left; left; exact ⟨(3 : Fin 4), rfl⟩
    · right; exact zero_eq_cpx.symm

/-- The coefficient vectors, entry by entry. -/
theorem coeff_eq (a : Complex (Fin 2)) (e : Unit ⊕ Unit) :
    augCoeff net κ Z L T a e =
      Sum.elim (fun _ => if a = cpx 1 0 ∨ a = cpx 1 2 then (-1 : ℝ)
          else if a = cpx 0 1 ∨ a = cpx 2 1 then 1 else 0)
        (fun _ => (if a = cpx 1 0 then (1 : ℝ) else 0) + (if a = cpx 0 1 then 1 else 0) -
          (if a = cpx 0 0 then 1 else 0)) e := by
  classical
  cases e with
  | inl u =>
    simp only [augCoeff, Sum.elim_inl]
    show combinedVector net κ a 0 = _
    rw [combined_eq]; simp
  | inr u =>
    simp only [augCoeff, Sum.elim_inr, Pi.sub_apply, Finset.sum_apply, Fin.sum_univ_two,
      unitComplex_zero, unitComplex_one, zero_eq_cpx, T]
    by_cases h1 : a = cpx 1 0
    · subst h1; simp [L]
    by_cases h2 : a = cpx 0 1
    · subst h2; simp [L]
    by_cases h3 : a = cpx 0 0
    · subst h3; simp [T]
    simp [h1, h2, h3]

/-- Affine independence of three points of `ℕ²` with a nonzero determinant. -/
theorem affInd_triple (p q r : ℕ × ℕ)
    (hdet : ((q.1 : ℝ) - p.1) * ((r.2 : ℝ) - p.2) - ((r.1 : ℝ) - p.1) * ((q.2 : ℝ) - p.2) ≠ 0)
    (hpq : cpx p.1 p.2 ≠ cpx q.1 q.2) (hpr : cpx p.1 p.2 ≠ cpx r.1 r.2)
    (hqr : cpx q.1 q.2 ≠ cpx r.1 r.2) :
    LinearIndependent ℝ (fun a : ({cpx p.1 p.2, cpx q.1 q.2, cpx r.1 r.2} :
      Finset (Complex (Fin 2))) => affineRow a.1) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  set P : ({cpx p.1 p.2, cpx q.1 q.2, cpx r.1 r.2} : Finset (Complex (Fin 2))) :=
    ⟨cpx p.1 p.2, by simp⟩
  set Q : ({cpx p.1 p.2, cpx q.1 q.2, cpx r.1 r.2} : Finset (Complex (Fin 2))) :=
    ⟨cpx q.1 q.2, by simp⟩
  set R : ({cpx p.1 p.2, cpx q.1 q.2, cpx r.1 r.2} : Finset (Complex (Fin 2))) :=
    ⟨cpx r.1 r.2, by simp⟩
  have hPQ : P ≠ Q := fun e => hpq (congrArg Subtype.val e)
  have hPR : P ≠ R := fun e => hpr (congrArg Subtype.val e)
  have hQR : Q ≠ R := fun e => hqr (congrArg Subtype.val e)
  have huniv : (Finset.univ : Finset ({cpx p.1 p.2, cpx q.1 q.2, cpx r.1 r.2} :
      Finset (Complex (Fin 2)))) = {P, Q, R} := by
    ext a
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases Finset.mem_insert.mp a.2 with h | h
    · left; exact Subtype.ext h
    rcases Finset.mem_insert.mp h with h | h
    · right; left; exact Subtype.ext h
    · right; right; exact Subtype.ext (Finset.mem_singleton.mp h)
  have e := fun j => congrFun hg j
  have e0 := e none
  have e1 := e (some 0)
  have e2 := e (some 1)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, huniv, Pi.zero_apply] at e0 e1 e2
  rw [Finset.sum_insert (by simp [hPQ, hPR]), Finset.sum_insert (by simp [hQR]),
    Finset.sum_singleton] at e0 e1 e2
  simp only [affineRow, Option.elim, P, Q, R, cpx_apply_zero, cpx_apply_one, mul_one] at e0 e1 e2
  have hgP : g P = -(g Q) - g R := by linarith
  rw [hgP] at e1 e2
  have hq : g Q * ((q.1 : ℝ) - p.1) + g R * ((r.1 : ℝ) - p.1) = 0 := by linear_combination e1
  have hr : g Q * ((q.2 : ℝ) - p.2) + g R * ((r.2 : ℝ) - p.2) = 0 := by linear_combination e2
  have hgQ : g Q = 0 := by
    have : g Q * (((q.1 : ℝ) - p.1) * ((r.2 : ℝ) - p.2) - ((r.1 : ℝ) - p.1) * ((q.2 : ℝ) - p.2))
      = 0 := by linear_combination ((r.2 : ℝ) - p.2) * hq - ((r.1 : ℝ) - p.1) * hr
    exact (mul_eq_zero.mp this).resolve_right hdet
  have hgR : g R = 0 := by
    have : g R * (((q.1 : ℝ) - p.1) * ((r.2 : ℝ) - p.2) - ((r.1 : ℝ) - p.1) * ((q.2 : ℝ) - p.2))
      = 0 := by linear_combination ((q.1 : ℝ) - p.1) * hr - ((q.2 : ℝ) - p.2) * hq
    exact (mul_eq_zero.mp this).resolve_right hdet
  have hgP' : g P = 0 := by rw [hgP, hgQ, hgR]; ring
  intro a
  have ha : a ∈ ({P, Q, R} : Finset _) := huniv ▸ Finset.mem_univ a
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl
  · exact hgP'
  · exact hgQ
  · exact hgR

/-- Two coefficient vectors with a nonzero determinant span `ℝ^{Unit ⊕ Unit}`. -/
theorem span_top_of_two {ι : Type*} (W : ι → (Unit ⊕ Unit → ℝ)) (i j : ι)
    (hdet : W i (Sum.inl ()) * W j (Sum.inr ()) - W j (Sum.inl ()) * W i (Sum.inr ()) ≠ 0) :
    Submodule.span ℝ (Set.range W) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  set D := W i (Sum.inl ()) * W j (Sum.inr ()) - W j (Sum.inl ()) * W i (Sum.inr ())
  have : v = ((v (Sum.inl ()) * W j (Sum.inr ()) - W j (Sum.inl ()) * v (Sum.inr ())) / D) • W i +
      ((W i (Sum.inl ()) * v (Sum.inr ()) - v (Sum.inl ()) * W i (Sum.inr ())) / D) • W j := by
    funext e
    cases e with
    | inl u => cases u; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; field_simp; ring
    | inr u => cases u; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; field_simp; ring
  rw [this]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))

theorem pairing_cpx (w : Fin 2 → ℤ) (i j : ℕ) : pairing w (cpx i j) = w 0 * i + w 1 * j := by
  simp [pairing, Fin.sum_univ_two]

/-- The cell `{0, X, 2X + Y}` with normal `(0, 1)`. -/
noncomputable def cell₁ : Patchworking.SysCell (augSupport net) (augCoeff net κ Z L T) h where
  Δ := {cpx 0 0, cpx 1 0, cpx 2 1}
  sub := by rw [support_eq]; intro a ha; simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢; tauto
  w := ![0, 1]
  c₀ := 0
  card := by
    rw [Fintype.card_coe]
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_pair (by simp)]; rfl
  affInd := affInd_triple (0, 0) (1, 0) (2, 1) (by norm_num) (by simp) (by simp) (by simp)
  onCell := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> simp [pairing_cpx, h]
  offCell := by
    intro a ha hΔ
    rw [support_eq] at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hΔ
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp_all [pairing_cpx, h]
  span := span_top_of_two _ (⟨cpx 1 0, by simp⟩ : ({cpx 0 0, cpx 1 0, cpx 2 1} : Finset _))
    ⟨cpx 2 1, by simp⟩ (by simp only [coeff_eq]; simp)
  lam := fun _ => 1
  lam_pos := fun _ => one_pos
  lam_ker := by
    classical
    rw [Finset.sum_coe_sort {cpx 0 0, cpx 1 0, cpx 2 1}
      (fun a => (1 : ℝ) • augCoeff net κ Z L T a)]
    rw [Finset.sum_insert (by simp), Finset.sum_pair (by simp)]
    funext e
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, Pi.zero_apply, coeff_eq]
    cases e <;> simp

/-- The cell `{0, Y, X + 2Y}` with normal `(1, 0)`. -/
noncomputable def cell₂ : Patchworking.SysCell (augSupport net) (augCoeff net κ Z L T) h where
  Δ := {cpx 0 0, cpx 0 1, cpx 1 2}
  sub := by rw [support_eq]; intro a ha; simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢; tauto
  w := ![1, 0]
  c₀ := 0
  card := by
    rw [Fintype.card_coe]
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_pair (by simp)]; rfl
  affInd := affInd_triple (0, 0) (0, 1) (1, 2) (by norm_num) (by simp) (by simp) (by simp)
  onCell := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> simp [pairing_cpx, h]
  offCell := by
    intro a ha hΔ
    rw [support_eq] at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hΔ
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp_all [pairing_cpx, h]
  span := span_top_of_two _ (⟨cpx 0 1, by simp⟩ : ({cpx 0 0, cpx 0 1, cpx 1 2} : Finset _))
    ⟨cpx 1 2, by simp⟩ (by simp only [coeff_eq]; simp)
  lam := fun _ => 1
  lam_pos := fun _ => one_pos
  lam_ker := by
    classical
    rw [Finset.sum_coe_sort {cpx 0 0, cpx 0 1, cpx 1 2}
      (fun a => (1 : ℝ) • augCoeff net κ Z L T a)]
    rw [Finset.sum_insert (by simp), Finset.sum_pair (by simp)]
    funext e
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, Pi.zero_apply, coeff_eq]
    cases e <;> simp

/-- **Non-vacuity.** Two distinct nondegenerate positive steady states in one class. -/
theorem two_nondegenerate_steadyStates :
    ∃ (κ' : RateConstants net) (x₀ : Concentration (Fin 2)) (X : Fin 2 → Concentration (Fin 2)),
      (∀ j, X j ∈ net.positiveCompatibilityClass x₀ ∧ net.IsMassActionSteadyState κ' (X j) ∧
        net.IsNondegenerateSteadyState κ' (X j)) ∧ Function.Injective X :=
  steadyStates_of_augmentedCells net Z L hZ hL (by simp) κ T h hh (by norm_num)
    ![cell₁, cell₂] (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [cell₁, cell₂] <;>
        (have := congrFun hij 0; simp at this))

theorem multistationary : net.HasMultistationarityCapacity := by
  obtain ⟨κ', x₀, X, hX, hinj⟩ := two_nondegenerate_steadyStates
  exact ⟨κ', x₀, X 0, X 1, (hX 0).1, (hX 1).1, (hX 0).2.1, (hX 1).2.1,
    fun h => absurd (hinj h) (by decide)⟩

/-- **Non-vacuity of the open region.** The parameters `(κ, T)` with two nondegenerate positive
steady states in the class `{x_X + x_Y = T}` form a nonempty open set. -/
theorem region_open_nonempty :
    IsOpen (NondegRegion net Z L 2) ∧ (NondegRegion net Z L 2).Nonempty :=
  nondegRegion_open_nonempty_of_augmentedCells net Z L hZ hL (by simp) κ T h hh (by norm_num)
    ![cell₁, cell₂] (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [cell₁, cell₂] <;>
        (have := congrFun hij 0; simp at this))

end AugmentedCells

end Examples

end CRNT
