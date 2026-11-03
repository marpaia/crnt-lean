import CRNT.Computation.PiecewiseNatAffine
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# Maximum closure and natural-affine chemical examples

Closure and construction results for `PiecewiseNatAffine`. The predicate uses
natural affine coefficients and is narrower than classical semilinearity.
-/
namespace CRNT
namespace Computation

namespace PiecewiseNatAffine

/-- **PiecewiseNatAffine functions are closed under `max`.**  On the intersection of the regions of
`f` and `g` the function `max (f x) (g x)` is affine on each of the two subregions
`f x ≤ g x` and `g x ≤ f x`, both of which are linear conditions. -/
theorem max {d : ℕ} {f g : (Fin d → ℕ) → ℕ} (hf : PiecewiseNatAffine f) (hg : PiecewiseNatAffine g) :
    PiecewiseNatAffine (fun x => Nat.max (f x) (g x)) := by
  obtain ⟨pf, hpf⟩ := hf
  obtain ⟨pg, hpg⟩ := hg
  refine ⟨pf.flatMap fun p => pg.flatMap fun q =>
    [(p.1.and (q.1.and (.le (fun i => (p.2.coeff i : ℤ) - q.2.coeff i)
      ((q.2.const : ℤ) - p.2.const))), q.2),
     (p.1.and (q.1.and (.le (fun i => (q.2.coeff i : ℤ) - p.2.coeff i)
      ((p.2.const : ℤ) - q.2.const))), p.2)], ?_⟩
  intro x
  obtain ⟨p, hp, hpx, hpv⟩ := hpf x
  obtain ⟨q, hq, hqx, hqv⟩ := hpg x
  by_cases h : p.2.eval x ≤ q.2.eval x
  · refine ⟨(p.1.and (q.1.and (.le (fun i => (p.2.coeff i : ℤ) - q.2.coeff i)
      ((q.2.const : ℤ) - p.2.const))), q.2), ?_, ?_, ?_⟩
    · exact List.mem_flatMap.mpr ⟨p, hp, List.mem_flatMap.mpr ⟨q, hq, by simp⟩⟩
    · refine ⟨hpx, hqx, ?_⟩
      simp only [LinFormula.Satisfied]
      exact Affine.eval_diff_iff.mp h
    · show Nat.max (f x) (g x) = _
      rw [hpv, hqv]
      exact Nat.max_eq_right h
  · refine ⟨(p.1.and (q.1.and (.le (fun i => (q.2.coeff i : ℤ) - p.2.coeff i)
      ((p.2.const : ℤ) - q.2.const))), p.2), ?_, ?_, ?_⟩
    · exact List.mem_flatMap.mpr ⟨p, hp, List.mem_flatMap.mpr ⟨q, hq, by simp⟩⟩
    · refine ⟨hpx, hqx, ?_⟩
      simp only [LinFormula.Satisfied]
      exact Affine.eval_diff_iff.mp (by omega)
    · show Nat.max (f x) (g x) = _
      rw [hpv, hqv]
      exact Nat.max_eq_left (by omega)

end PiecewiseNatAffine

/-! ## The region-splitting lemma -/

/-- The linear formula that expresses the comparison of two affine maps: it is
satisfied at `x` exactly when `A x ≤ B x`. -/
def Affine.diffFormula (A B : Affine d) : LinFormula d :=
  .le (fun i => (A.coeff i : ℤ) - (B.coeff i : ℤ)) ((B.const : ℤ) - A.const)

/-- The comparison of two affine maps is exactly the corresponding linear condition. -/
theorem Affine.diffFormula_satisfied {A B : Affine d} {x : Fin d → ℕ} :
    (Affine.diffFormula A B).Satisfied x ↔ A.eval x ≤ B.eval x := by
  simp only [Affine.diffFormula, LinFormula.Satisfied]
  exact (Affine.eval_diff_iff).symm

/-- **The region-splitting lemma.**  If `A` and `B` are affine maps and `φ` is a linear
formula, then the region `φ` is the union of the two regions `φ ∧ {A ≤ B}` and
`φ ∧ {B ≤ A}`; on the first the maximum is the affine map `B`, on the second it is the
affine map `A` (`max_eq_of_diff`, `max_eq_of_diff'`). -/
theorem region_split {d : ℕ} (φ : LinFormula d) (A B : Affine d) (x : Fin d → ℕ)
    (hφ : φ.Satisfied x) :
    (φ.and (Affine.diffFormula A B)).Satisfied x
      ∨ (φ.and (Affine.diffFormula B A)).Satisfied x := by
  by_cases h : A.eval x ≤ B.eval x
  · refine Or.inl ⟨hφ, (Affine.diffFormula_satisfied).mpr h⟩
  · refine Or.inr ⟨hφ, (Affine.diffFormula_satisfied).mpr (by omega)⟩

/-- On the region `{A ≤ B}` the maximum of the two affine maps is the affine map `B`. -/
theorem max_eq_of_diff {d : ℕ} {A B : Affine d} {x : Fin d → ℕ}
    (h : (Affine.diffFormula A B).Satisfied x) :
    Nat.max (A.eval x) (B.eval x) = B.eval x :=
  Nat.max_eq_right ((Affine.diffFormula_satisfied).mp h)

/-- On the region `{B ≤ A}` the maximum of the two affine maps is the affine map `A`. -/
theorem max_eq_of_diff' {d : ℕ} {A B : Affine d} {x : Fin d → ℕ}
    (h : (Affine.diffFormula B A).Satisfied x) :
    Nat.max (A.eval x) (B.eval x) = A.eval x :=
  Nat.max_eq_left ((Affine.diffFormula_satisfied).mp h)

/-- **The region-splitting lemma, in the language of regions.**  The region described by
`φ` is the union of the two regions described by `φ ∧ {A ≤ B}` and `φ ∧ {B ≤ A}`. -/
theorem region_split_union {d : ℕ} (φ : LinFormula d) (A B : Affine d) :
    (LinFormula.Region (φ.and (Affine.diffFormula A B))) ∪
      (LinFormula.Region (φ.and (Affine.diffFormula B A)))
      = LinFormula.Region φ := by
  ext x
  simp only [LinFormula.Region, Set.mem_union]
  constructor
  · rintro (h | h)
    · exact h.1
    · exact h.1
  · intro h
    rcases region_split φ A B x h with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'

/-- **The maximum of two affine maps is piecewiseNatAffine.** -/
theorem max_of_affine_piecewiseNatAffine {d : ℕ} (c₁ c₂ : ℕ) (e₁ e₂ : Fin d → ℕ) :
    PiecewiseNatAffine (fun x => Nat.max (c₁ + ∑ i, e₁ i * x i) (c₂ + ∑ i, e₂ i * x i)) :=
  PiecewiseNatAffine.max (piecewiseNatAffine_of_affine c₁ e₁) (piecewiseNatAffine_of_affine c₂ e₂)


/-- **The piecewiseNatAffine class is a semiring with `max`.**  It is closed under `+`, `min`,
`max`, `k ·` and contains the affine maps. -/
theorem piecewiseNatAffine_max_add {d : ℕ} {f g h : (Fin d → ℕ) → ℕ}
    (hf : PiecewiseNatAffine f) (hg : PiecewiseNatAffine g) (hh : PiecewiseNatAffine h) (k : ℕ) :
    PiecewiseNatAffine (fun x => k * Nat.max (f x + h x) (Nat.min (g x) (h x))) := by
  have h1 : PiecewiseNatAffine (fun x => f x + h x) := PiecewiseNatAffine.add hf hh
  have h2 : PiecewiseNatAffine (fun x => Nat.min (g x) (h x)) := PiecewiseNatAffine.min hg hh
  have h3 : PiecewiseNatAffine (fun x => Nat.max (f x + h x) (Nat.min (g x) (h x))) :=
    PiecewiseNatAffine.max h1 h2
  exact PiecewiseNatAffine.smul h3 k


namespace MaxAffine

variable {d : ℕ}

/-- The species of the network computing the maximum of two affine maps. -/
abbrev Species (d : ℕ) := Fin d ⊕ Fin 6

/-- The input species `X_i`. -/
abbrev xSpec (i : Fin d) : Species d := Sum.inl i
/-- The first piece stream `P₁`. -/
abbrev p1Spec : Species d := Sum.inr 0
/-- The second piece stream `P₂`. -/
abbrev p2Spec : Species d := Sum.inr 1
/-- The output species `Y`. -/
abbrev ySpec : Species d := Sum.inr 2
/-- The accumulator `Z₁`. -/
abbrev z1Spec : Species d := Sum.inr 3
/-- The accumulator `Z₂`. -/
abbrev z2Spec : Species d := Sum.inr 4
/-- The auxiliary species `K`. -/
abbrev kSpec : Species d := Sum.inr 5

/-- The source complex of the conversion reaction for the input `i`. -/
def convSource (i : Fin d) : Species d → ℕ := fun s => if s = xSpec i then 1 else 0

/-- The target complex of the conversion reaction for the input `i`. -/
def convTarget (A B : Affine d) (i : Fin d) : Species d → ℕ := fun s =>
  if s = p1Spec then A.coeff i else if s = p2Spec then B.coeff i else 0

/-- The source complex of the auxiliary reactions, as a table. -/
def auxSource : Fin 4 → Fin 6 → ℕ
  | 0, 0 => 1
  | 1, 1 => 1
  | 2, 3 => 1
  | 2, 4 => 1
  | 3, 2 => 1
  | 3, 5 => 1
  | _, _ => 0

/-- The target complex of the auxiliary reactions, as a table. -/
def auxTarget : Fin 4 → Fin 6 → ℕ
  | 0, 2 => 1
  | 0, 3 => 1
  | 1, 2 => 1
  | 1, 4 => 1
  | 2, 5 => 1
  | _, _ => 0

/-- The source complex of the auxiliary reaction `r`, on the species. -/
def auxSource' (r : Fin 4) : Species d → ℕ := fun s =>
  match s with
  | Sum.inl _ => 0
  | Sum.inr k => auxSource r k

/-- The target complex of the auxiliary reaction `r`, on the species. -/
def auxTarget' (r : Fin 4) : Species d → ℕ := fun s =>
  match s with
  | Sum.inl _ => 0
  | Sum.inr k => auxTarget r k

/-- The network computing the maximum of the two affine maps `A` and `B`. -/
abbrev maxAffineCRN (A B : Affine d) : Network (Species d) :=
  ⟨Fin d ⊕ Fin 4, inferInstance, inferInstance, fun r => match r with
    | Sum.inl i => ⟨convSource i, convTarget A B i⟩
    | Sum.inr r => ⟨auxSource' r, auxTarget' r⟩⟩

/-- The initial configuration: `x i` molecules of the input species `X_i`, `A.const`
molecules of `P₁` and `B.const` molecules of `P₂`. -/
def maxAffineInit (A B : Affine d) (x : Fin d → ℕ) : Config (Species d) := fun s =>
  if s = p1Spec then A.const
  else if s = p2Spec then B.const
  else match s with
    | Sum.inl i => x i
    | _ => 0

/-! ### The stoichiometric change -/

/-- The stoichiometric change of the conversion reaction at an input species. -/
theorem delta_conv_x (A B : Affine d) (i j : Fin d) :
    delta (maxAffineCRN A B) (Sum.inl i) (xSpec j) = (if j = i then (-1 : ℤ) else 0) := by
  simp [delta, convSource, convTarget, xSpec]
  by_cases h : j = i <;> simp [h]

/-- The stoichiometric change of the conversion reaction at an auxiliary species. -/
theorem delta_conv_aux (A B : Affine d) (i : Fin d) (k : Fin 6) :
    delta (maxAffineCRN A B) (Sum.inl i) (Sum.inr k)
      = (if k = 0 then (A.coeff i : ℤ) else if k = 1 then (B.coeff i : ℤ) else 0) := by
  fin_cases k <;> simp [delta, convSource, convTarget, p1Spec, p2Spec]

/-- The stoichiometric change of an auxiliary reaction at an auxiliary species. -/
theorem delta_aux (A B : Affine d) (r : Fin 4) (k : Fin 6) :
    delta (maxAffineCRN A B) (Sum.inr r) (Sum.inr k)
      = (auxTarget r k : ℤ) - (auxSource r k : ℤ) := by
  simp [delta, auxSource', auxTarget']

/-- The stoichiometric change of an auxiliary reaction at an input species. -/
theorem delta_aux_x (A B : Affine d) (r : Fin 4) (j : Fin d) :
    delta (maxAffineCRN A B) (Sum.inr r) (xSpec j) = 0 := by
  simp [delta, auxSource', auxTarget']

/-! ### The weights -/

/-- A weight on the species, given by its values on the input species and on the
auxiliary species. -/
def splitWeight (waux : Fin 6 → ℤ) (winput : Fin d → ℤ) : Species d → ℤ := fun s =>
  match s with
  | Sum.inl j => winput j
  | Sum.inr k => waux k

/-- The weight of the auxiliary species for the potential. -/
def auxPotWeight : Fin 6 → ℤ
  | 0 => 2
  | 1 => 2
  | 2 => 0
  | 3 => 1
  | 4 => 1
  | 5 => 1

/-- The weight of the auxiliary species for the first invariant. -/
def auxW1 : Fin 6 → ℤ
  | 0 => 1
  | 1 => -1
  | 2 => 0
  | 3 => 1
  | 4 => -1
  | 5 => 0

/-- The weight of the auxiliary species for the second invariant. -/
def auxW2 : Fin 6 → ℤ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => -1
  | 4 => -1
  | 5 => -2

/-- The weight of a species for the potential of the network. -/
def potentialWeight (A B : Affine d) : Species d → ℤ :=
  splitWeight auxPotWeight (fun i => ((1 + 2 * (A.coeff i + B.coeff i) : ℕ) : ℤ))

/-- The weight of a species for the first invariant. -/
def weight1 (A B : Affine d) : Species d → ℤ :=
  splitWeight auxW1 (fun i => ((A.coeff i : ℤ) - (B.coeff i : ℤ)))

/-- The weight of a species for the second invariant. -/
def weight2 (A B : Affine d) : Species d → ℤ :=
  splitWeight auxW2 (fun i => ((A.coeff i : ℤ) + (B.coeff i : ℤ)))

/-! ### The change of the weighted sums -/

/-- The change of a weighted sum under the conversion reaction. -/
theorem wsum_delta_conv {waux : Fin 6 → ℤ} {winput : Fin d → ℤ} (A B : Affine d) (i : Fin d) :
    wsum (splitWeight waux winput) (delta (maxAffineCRN A B) (Sum.inl i))
      = winput i * (-1) + waux 0 * (A.coeff i : ℤ) + waux 1 * (B.coeff i : ℤ) := by
  rw [wsum, Fintype.sum_sum_type]
  have key : ∀ j : Fin d,
      splitWeight waux winput (xSpec j) * delta (maxAffineCRN A B) (Sum.inl i) (xSpec j)
        = winput j * ((if j = i then (-1 : ℤ) else 0)) := by
    intro j
    rw [delta_conv_x]
    simp [splitWeight]
  rw [Finset.sum_congr rfl (fun j _ => key j)]
  have h := sum_ite_mul_eq (fun j => winput j) i (-1 : ℤ)
  rw [h]
  have key2 : ∀ k : Fin 6,
      splitWeight waux winput (Sum.inr k)
          * delta (maxAffineCRN A B) (Sum.inl i) (Sum.inr k)
        = waux k * ((if k = 0 then (A.coeff i : ℤ) else 0))
          + waux k * ((if k = 1 then (B.coeff i : ℤ) else 0)) := by
    intro k
    rw [delta_conv_aux]
    by_cases h0 : k = 0 <;> by_cases h1 : k = 1 <;> simp [h0, h1, splitWeight]
  rw [Finset.sum_congr rfl (fun k _ => key2 k), Finset.sum_add_distrib]
  have h0 := sum_ite_mul_eq (fun k => waux k) 0 (A.coeff i : ℤ)
  have h1 := sum_ite_mul_eq (fun k => waux k) 1 (B.coeff i : ℤ)
  rw [h0, h1]
  ring

/-- The change of a weighted sum under an auxiliary reaction. -/
theorem wsum_delta_aux {waux : Fin 6 → ℤ} {winput : Fin d → ℤ} (A B : Affine d) (r : Fin 4) :
    wsum (splitWeight waux winput) (delta (maxAffineCRN A B) (Sum.inr r))
      = (∑ k : Fin 6, waux k * ((auxTarget r k : ℤ) - (auxSource r k : ℤ))) := by
  rw [wsum, Fintype.sum_sum_type]
  have key : ∀ j : Fin d,
      splitWeight waux winput (xSpec j) * delta (maxAffineCRN A B) (Sum.inr r) (xSpec j)
        = 0 := by
    intro j
    rw [delta_aux_x]
    simp [splitWeight]
  rw [Finset.sum_congr rfl (fun j _ => key j)]
  simp
  have key2 : ∀ k : Fin 6,
      splitWeight waux winput (Sum.inr k) * delta (maxAffineCRN A B) (Sum.inr r) (Sum.inr k)
        = waux k * ((auxTarget r k : ℤ) - (auxSource r k : ℤ)) := by
    intro k
    rw [delta_aux]
    simp [splitWeight]
  rw [Finset.sum_congr rfl (fun k _ => key2 k)]

/-- The potential decreases by one at the conversion reaction. -/
theorem wsum_delta_pot_conv (A B : Affine d) (i : Fin d) :
    wsum (potentialWeight A B) (delta (maxAffineCRN A B) (Sum.inl i)) = -1 := by
  have h : wsum (potentialWeight A B) (delta (maxAffineCRN A B) (Sum.inl i))
      = ((1 + 2 * (A.coeff i + B.coeff i) : ℕ) : ℤ) * (-1)
        + auxPotWeight 0 * (A.coeff i : ℤ) + auxPotWeight 1 * (B.coeff i : ℤ) := by
    exact wsum_delta_conv (A := A) (B := B) (i := i) (waux := auxPotWeight)
      (winput := fun j => ((1 + 2 * (A.coeff j + B.coeff j) : ℕ) : ℤ))
  rw [h]
  simp [auxPotWeight]
  ring

/-- The potential decreases by one at an auxiliary reaction. -/
theorem wsum_delta_pot_aux (A B : Affine d) (r : Fin 4) :
    wsum (potentialWeight A B) (delta (maxAffineCRN A B) (Sum.inr r)) = -1 := by
  have h : wsum (potentialWeight A B) (delta (maxAffineCRN A B) (Sum.inr r))
      = (∑ k : Fin 6, auxPotWeight k * ((auxTarget r k : ℤ) - (auxSource r k : ℤ))) := by
    exact wsum_delta_aux (A := A) (B := B) (r := r) (waux := auxPotWeight)
      (winput := fun j => ((1 + 2 * (A.coeff j + B.coeff j) : ℕ) : ℤ))
  rw [h]
  fin_cases r <;> simp [Fin.sum_univ_succ, auxPotWeight, auxTarget, auxSource]

/-- The potential decreases by one at every reaction. -/
theorem wsum_delta_pot (A B : Affine d) (r : Fin d ⊕ Fin 4) :
    wsum (potentialWeight A B) (delta (maxAffineCRN A B) r) = -1 := by
  cases r with
  | inl i => exact wsum_delta_pot_conv A B i
  | inr r => exact wsum_delta_pot_aux A B r

/-- The first invariant is preserved by the conversion reaction. -/
theorem wsum_delta_w1_conv (A B : Affine d) (i : Fin d) :
    wsum (weight1 A B) (delta (maxAffineCRN A B) (Sum.inl i)) = 0 := by
  have h : wsum (weight1 A B) (delta (maxAffineCRN A B) (Sum.inl i))
      = ((A.coeff i : ℤ) - (B.coeff i : ℤ)) * (-1)
        + auxW1 0 * (A.coeff i : ℤ) + auxW1 1 * (B.coeff i : ℤ) := by
    exact wsum_delta_conv (A := A) (B := B) (i := i) (waux := auxW1)
      (winput := fun j => ((A.coeff j : ℤ) - (B.coeff j : ℤ)))
  rw [h]
  simp [auxW1]

/-- The first invariant is preserved by an auxiliary reaction. -/
theorem wsum_delta_w1_aux (A B : Affine d) (r : Fin 4) :
    wsum (weight1 A B) (delta (maxAffineCRN A B) (Sum.inr r)) = 0 := by
  have h : wsum (weight1 A B) (delta (maxAffineCRN A B) (Sum.inr r))
      = (∑ k : Fin 6, auxW1 k * ((auxTarget r k : ℤ) - (auxSource r k : ℤ))) := by
    exact wsum_delta_aux (A := A) (B := B) (r := r) (waux := auxW1)
      (winput := fun j => ((A.coeff j : ℤ) - (B.coeff j : ℤ)))
  rw [h]
  fin_cases r <;> simp [Fin.sum_univ_succ, auxW1, auxTarget, auxSource]

/-- The second invariant is preserved by the conversion reaction. -/
theorem wsum_delta_w2_conv (A B : Affine d) (i : Fin d) :
    wsum (weight2 A B) (delta (maxAffineCRN A B) (Sum.inl i)) = 0 := by
  have h : wsum (weight2 A B) (delta (maxAffineCRN A B) (Sum.inl i))
      = ((A.coeff i : ℤ) + (B.coeff i : ℤ)) * (-1)
        + auxW2 0 * (A.coeff i : ℤ) + auxW2 1 * (B.coeff i : ℤ) := by
    exact wsum_delta_conv (A := A) (B := B) (i := i) (waux := auxW2)
      (winput := fun j => ((A.coeff j : ℤ) + (B.coeff j : ℤ)))
  rw [h]
  simp [auxW2]

/-- The second invariant is preserved by an auxiliary reaction. -/
theorem wsum_delta_w2_aux (A B : Affine d) (r : Fin 4) :
    wsum (weight2 A B) (delta (maxAffineCRN A B) (Sum.inr r)) = 0 := by
  have h : wsum (weight2 A B) (delta (maxAffineCRN A B) (Sum.inr r))
      = (∑ k : Fin 6, auxW2 k * ((auxTarget r k : ℤ) - (auxSource r k : ℤ))) := by
    exact wsum_delta_aux (A := A) (B := B) (r := r) (waux := auxW2)
      (winput := fun j => ((A.coeff j : ℤ) + (B.coeff j : ℤ)))
  rw [h]
  fin_cases r <;> simp [Fin.sum_univ_succ, auxW2, auxTarget, auxSource]

/-- The potential of the network, as a natural number. -/
def maxAffinePotential (A B : Affine d) (c : Config (Species d)) : ℕ :=
  ∑ i, (1 + 2 * (A.coeff i + B.coeff i)) * c (xSpec i)
    + 2 * c (p1Spec) + 2 * c (p2Spec) + c (z1Spec) + c (z2Spec) + c (kSpec)

/-- The potential is the weighted sum of the configuration. -/
theorem configSum_potential_eq (A B : Affine d) (c : Config (Species d)) :
    configSum (potentialWeight A B) c = (maxAffinePotential A B c : ℤ) := by
  have hX : (∑ j : Fin d, potentialWeight A B (xSpec j) * ((c (xSpec j) : ℤ)))
      = ((∑ j, (1 + 2 * (A.coeff j + B.coeff j)) * c (xSpec j) : ℕ) : ℤ) := by
    have key : ∀ j : Fin d, potentialWeight A B (xSpec j) * ((c (xSpec j) : ℤ))
        = (((1 + 2 * (A.coeff j + B.coeff j)) * c (xSpec j) : ℕ) : ℤ) := by
      intro j
      simp only [potentialWeight, splitWeight]
      exact (Nat.cast_mul _ _).symm
    rw [Finset.sum_congr rfl (fun j _ => key j)]
    rw [← Nat.cast_sum]
  have hAux : (∑ k : Fin 6, potentialWeight A B (Sum.inr k) * ((c (Sum.inr k) : ℤ)))
      = (2 * (c (p1Spec) : ℤ) + 2 * (c (p2Spec) : ℤ) + (c (z1Spec) : ℤ)
        + (c (z2Spec) : ℤ) + (c (kSpec) : ℤ)) := by
    simp [potentialWeight, splitWeight, Fin.sum_univ_succ, auxPotWeight]
    ring
  simp only [configSum, wsum, Fintype.sum_sum_type, Fintype.sum_sum_type]
  rw [hX, hAux]
  simp [maxAffinePotential, Nat.cast_add]
  ring

/-! ### The applicability of the reactions -/

/-- The conversion reaction is applicable exactly when the input species `X_i` holds a
molecule. -/
theorem conv_applicable (A B : Affine d) (i : Fin d) (c : Config (Species d)) :
    Applicable (maxAffineCRN A B) (Sum.inl i) c ↔ 1 ≤ c (xSpec i) := by
  constructor
  · intro h
    have hh := h (xSpec i)
    simp [convSource, xSpec] at hh ⊢
    omega
  · intro h s
    simp only [xSpec] at h
    cases s with
    | inl j =>
      by_cases hj : j = i
      · subst hj
        simp [convSource, xSpec]
        exact h
      · simp [hj, convSource, xSpec]
    | inr k => simp [convSource]

/-- The reaction `P₁ → Z₁ + Y` is applicable exactly when `P₁` holds a molecule. -/
theorem p1_applicable (A B : Affine d) (c : Config (Species d)) :
    Applicable (maxAffineCRN A B) (Sum.inr 0) c ↔ 1 ≤ c (p1Spec) := by
  constructor
  · intro h
    have hh := h (p1Spec)
    simp [auxSource', auxSource, p1Spec] at hh ⊢
    omega
  · intro h s
    simp only [p1Spec] at h
    cases s with
    | inl j => simp [auxSource']
    | inr k =>
      fin_cases k
      all_goals simp [auxSource', auxSource]
      all_goals omega

/-- The reaction `P₂ → Z₂ + Y` is applicable exactly when `P₂` holds a molecule. -/
theorem p2_applicable (A B : Affine d) (c : Config (Species d)) :
    Applicable (maxAffineCRN A B) (Sum.inr 1) c ↔ 1 ≤ c (p2Spec) := by
  constructor
  · intro h
    have hh := h (p2Spec)
    simp [auxSource', auxSource, p2Spec] at hh ⊢
    omega
  · intro h s
    simp only [p2Spec] at h
    cases s with
    | inl j => simp [auxSource']
    | inr k =>
      fin_cases k
      all_goals simp [auxSource', auxSource]
      all_goals omega

/-- The reaction `Z₁ + Z₂ → K` is applicable exactly when both accumulators are
non-empty. -/
theorem pair_applicable (A B : Affine d) (c : Config (Species d)) :
    Applicable (maxAffineCRN A B) (Sum.inr 2) c ↔ 1 ≤ c (z1Spec) ∧ 1 ≤ c (z2Spec) := by
  constructor
  · intro h
    have h1 := h (z1Spec)
    have h2 := h (z2Spec)
    simp [auxSource', auxSource, z1Spec, z2Spec] at h1 h2 ⊢
    omega
  · intro h s
    simp only [z1Spec, z2Spec] at h
    cases s with
    | inl j => simp [auxSource']
    | inr k =>
      fin_cases k
      all_goals simp [auxSource', auxSource]
      all_goals omega

/-- The reaction `K + Y → ∅` is applicable exactly when `K` and `Y` are both non-empty. -/
theorem cancel_applicable (A B : Affine d) (c : Config (Species d)) :
    Applicable (maxAffineCRN A B) (Sum.inr 3) c ↔ 1 ≤ c (kSpec) ∧ 1 ≤ c (ySpec) := by
  constructor
  · intro h
    have h1 := h (kSpec)
    have h2 := h (ySpec)
    simp [auxSource', auxSource, kSpec, ySpec] at h1 h2 ⊢
    omega
  · intro h s
    simp only [kSpec, ySpec] at h
    cases s with
    | inl j => simp [auxSource']
    | inr k =>
      fin_cases k
      all_goals simp [auxSource', auxSource]
      all_goals omega

/-! ### The invariants -/

/-- The value of the first invariant in terms of the counts of the species. -/
theorem configSum_weight1 (A B : Affine d) (c : Config (Species d)) :
    configSum (weight1 A B) c
      = (∑ j, (((A.coeff j : ℤ) - (B.coeff j : ℤ)) * (c (xSpec j) : ℤ)))
        + (c (p1Spec) : ℤ) + (c (z1Spec) : ℤ) - (c (p2Spec) : ℤ) - (c (z2Spec) : ℤ) := by
  have hX : (∑ j : Fin d, weight1 A B (xSpec j) * ((c (xSpec j) : ℤ)))
      = ∑ j, (((A.coeff j : ℤ) - (B.coeff j : ℤ)) * (c (xSpec j) : ℤ)) := by
    have key : ∀ j : Fin d, weight1 A B (xSpec j) * ((c (xSpec j) : ℤ))
        = ((A.coeff j : ℤ) - (B.coeff j : ℤ)) * (c (xSpec j) : ℤ) := by
      intro j
      simp [weight1, splitWeight]
    rw [Finset.sum_congr rfl (fun j _ => key j)]
  have hAux : (∑ k : Fin 6, weight1 A B (Sum.inr k) * ((c (Sum.inr k) : ℤ)))
      = (c (p1Spec) : ℤ) + (c (z1Spec) : ℤ) - (c (p2Spec) : ℤ) - (c (z2Spec) : ℤ) := by
    simp [weight1, splitWeight, Fin.sum_univ_succ, auxW1]
    ring
  simp only [configSum, wsum, Fintype.sum_sum_type, Fintype.sum_sum_type]
  rw [hX, hAux]
  ring

/-- The value of the first invariant on the initial configuration. -/
theorem configSum_weight1_init (A B : Affine d) (x : Fin d → ℕ) :
    configSum (weight1 A B) (maxAffineInit A B x) = (A.eval x : ℤ) - (B.eval x : ℤ) := by
  have hX : (∑ j : Fin d, weight1 A B (xSpec j) * ((maxAffineInit A B x (xSpec j) : ℤ)))
      = ∑ j, (((A.coeff j : ℤ) - (B.coeff j : ℤ)) * (x j : ℤ)) := by
    have key : ∀ j : Fin d,
        weight1 A B (xSpec j) * ((maxAffineInit A B x (xSpec j) : ℤ))
          = ((A.coeff j : ℤ) - (B.coeff j : ℤ)) * (x j : ℤ) := by
      intro j
      simp [weight1, splitWeight, maxAffineInit, xSpec]
    rw [Finset.sum_congr rfl (fun j _ => key j)]
  have hAux : (∑ k : Fin 6, weight1 A B (Sum.inr k) * ((maxAffineInit A B x (Sum.inr k) : ℤ)))
      = (A.const : ℤ) - (B.const : ℤ) := by
    simp [weight1, splitWeight, Fin.sum_univ_succ, auxW1, maxAffineInit, p1Spec, p2Spec]
    ring
  simp only [configSum, wsum, Fintype.sum_sum_type, Fintype.sum_sum_type]
  rw [hX, hAux]
  have key2 : ∀ j : Fin d, (((A.coeff j : ℤ) - (B.coeff j : ℤ)) * (x j : ℤ))
      = ((A.coeff j : ℤ) * (x j : ℤ)) - ((B.coeff j : ℤ) * (x j : ℤ)) := by
    intro j
    ring
  rw [Finset.sum_congr rfl (fun j _ => key2 j), Finset.sum_sub_distrib]
  rw [show (A.eval x : ℤ) = (A.const : ℤ) + ∑ j, ((A.coeff j : ℤ) * (x j : ℤ)) by
        rw [Affine.eval]; simp only [Nat.cast_add, Nat.cast_sum, Nat.cast_mul]]
  rw [show (B.eval x : ℤ) = (B.const : ℤ) + ∑ j, ((B.coeff j : ℤ) * (x j : ℤ)) by
        rw [Affine.eval]; simp only [Nat.cast_add, Nat.cast_sum, Nat.cast_mul]]
  ring

/-- The value of the second invariant in terms of the counts of the species. -/
theorem configSum_weight2 (A B : Affine d) (c : Config (Species d)) :
    configSum (weight2 A B) c
      = (∑ j, (((A.coeff j : ℤ) + (B.coeff j : ℤ)) * (c (xSpec j) : ℤ)))
        + (c (p1Spec) : ℤ) + (c (p2Spec) : ℤ) + 2 * (c (ySpec) : ℤ)
        - (c (z1Spec) : ℤ) - (c (z2Spec) : ℤ) - 2 * (c (kSpec) : ℤ) := by
  have hX : (∑ j : Fin d, weight2 A B (xSpec j) * ((c (xSpec j) : ℤ)))
      = ∑ j, (((A.coeff j : ℤ) + (B.coeff j : ℤ)) * (c (xSpec j) : ℤ)) := by
    have key : ∀ j : Fin d, weight2 A B (xSpec j) * ((c (xSpec j) : ℤ))
        = ((A.coeff j : ℤ) + (B.coeff j : ℤ)) * (c (xSpec j) : ℤ) := by
      intro j
      simp [weight2, splitWeight]
    rw [Finset.sum_congr rfl (fun j _ => key j)]
  have hAux : (∑ k : Fin 6, weight2 A B (Sum.inr k) * ((c (Sum.inr k) : ℤ)))
      = (c (p1Spec) : ℤ) + (c (p2Spec) : ℤ) + 2 * (c (ySpec) : ℤ)
        - (c (z1Spec) : ℤ) - (c (z2Spec) : ℤ) - 2 * (c (kSpec) : ℤ) := by
    simp [weight2, splitWeight, Fin.sum_univ_succ, auxW2]
    ring
  simp only [configSum, wsum, Fintype.sum_sum_type, Fintype.sum_sum_type]
  rw [hX, hAux]
  ring

/-- The value of the second invariant on the initial configuration. -/
theorem configSum_weight2_init (A B : Affine d) (x : Fin d → ℕ) :
    configSum (weight2 A B) (maxAffineInit A B x) = (A.eval x : ℤ) + (B.eval x : ℤ) := by
  have hX : (∑ j : Fin d, weight2 A B (xSpec j) * ((maxAffineInit A B x (xSpec j) : ℤ)))
      = ∑ j, (((A.coeff j : ℤ) + (B.coeff j : ℤ)) * (x j : ℤ)) := by
    have key : ∀ j : Fin d,
        weight2 A B (xSpec j) * ((maxAffineInit A B x (xSpec j) : ℤ))
          = ((A.coeff j : ℤ) + (B.coeff j : ℤ)) * (x j : ℤ) := by
      intro j
      simp [weight2, splitWeight, maxAffineInit, xSpec]
    rw [Finset.sum_congr rfl (fun j _ => key j)]
  have hAux : (∑ k : Fin 6, weight2 A B (Sum.inr k) * ((maxAffineInit A B x (Sum.inr k) : ℤ)))
      = (A.const : ℤ) + (B.const : ℤ) := by
    simp [weight2, splitWeight, Fin.sum_univ_succ, auxW2, maxAffineInit, p1Spec, p2Spec]
  simp only [configSum, wsum, Fintype.sum_sum_type, Fintype.sum_sum_type]
  rw [hX, hAux]
  have key2 : ∀ j : Fin d, (((A.coeff j : ℤ) + (B.coeff j : ℤ)) * (x j : ℤ))
      = ((A.coeff j : ℤ) * (x j : ℤ)) + ((B.coeff j : ℤ) * (x j : ℤ)) := by
    intro j
    ring
  rw [Finset.sum_congr rfl (fun j _ => key2 j), Finset.sum_add_distrib]
  rw [show (A.eval x : ℤ) = (A.const : ℤ) + ∑ j, ((A.coeff j : ℤ) * (x j : ℤ)) by
        rw [Affine.eval]; simp only [Nat.cast_add, Nat.cast_sum, Nat.cast_mul]]
  rw [show (B.eval x : ℤ) = (B.const : ℤ) + ∑ j, ((B.coeff j : ℤ) * (x j : ℤ)) by
        rw [Affine.eval]; simp only [Nat.cast_add, Nat.cast_sum, Nat.cast_mul]]
  ring

/-! ### The main theorem -/

/-- **The maximum of two affine maps is stably computed.**

The network `maxAffineCRN A B` stably computes `fun x => max (A x) (B x)`: the conversion
reaction reads every molecule of the input once and produces the molecules of the two
pieces, the reaction `P₁ → Z₁ + Y` and `P₂ → Z₂ + Y` turn the two piece totals into
molecules of the output, the reaction `Z₁ + Z₂ → K` pairs them up and the reaction
`K + Y → ∅` discards the surplus, leaving exactly `max (A x) (B x)` molecules of `Y`. -/
theorem maxAffineCRN_stablyComputes {d : ℕ} (A B : Affine d) :
    StablyComputes (maxAffineCRN A B) (maxAffineInit A B) ySpec
      (fun x => Nat.max (A.eval x) (B.eval x)) := by
  refine stablyComputes_of_terminating _ _ _ _ (maxAffinePotential A B) ?_ ?_
  · intro c c' hstep
    obtain ⟨r, hr, rfl⟩ := hstep
    have hdec := configSum_fire (maxAffineCRN A B) (potentialWeight A B) r c hr
    rw [configSum_potential_eq, configSum_potential_eq] at hdec
    rw [wsum_delta_pot] at hdec
    have hlt : ((maxAffinePotential A B (fire (maxAffineCRN A B) r c) : ℤ))
        < ((maxAffinePotential A B c : ℤ)) := by
      omega
    exact Int.ofNat_lt.mp hlt
  · intro x c hc hterm
    -- (1) the terminal conditions
    have hX : ∀ i : Fin d, c (xSpec i) = 0 := by
      intro i
      have hne : ¬ (1 ≤ c (xSpec i)) := by
        intro h
        exact hterm (Sum.inl i) ((conv_applicable A B i c).mpr h)
      omega
    have hp1 : c (p1Spec) = 0 := by
      have hne : ¬ (1 ≤ c (p1Spec)) := by
        intro h
        exact hterm (Sum.inr 0) ((p1_applicable A B c).mpr h)
      omega
    have hp2 : c (p2Spec) = 0 := by
      have hne : ¬ (1 ≤ c (p2Spec)) := by
        intro h
        exact hterm (Sum.inr 1) ((p2_applicable A B c).mpr h)
      omega
    have hz : c (z1Spec) = 0 ∨ c (z2Spec) = 0 := by
      have hne : ¬ (1 ≤ c (z1Spec) ∧ 1 ≤ c (z2Spec)) := by
        intro h
        exact hterm (Sum.inr 2) ((pair_applicable A B c).mpr h)
      omega
    have hk : c (kSpec) = 0 ∨ c (ySpec) = 0 := by
      have hne : ¬ (1 ≤ c (kSpec) ∧ 1 ≤ c (ySpec)) := by
        intro h
        exact hterm (Sum.inr 3) ((cancel_applicable A B c).mpr h)
      omega
    -- (2) the invariants
    have hInv1 : configSum (weight1 A B) c = configSum (weight1 A B) (maxAffineInit A B x) := by
      exact configSum_invariant (maxAffineCRN A B) (weight1 A B)
        (fun r => by cases r with
          | inl i => exact wsum_delta_w1_conv A B i
          | inr r => exact wsum_delta_w1_aux A B r) hc
    have hInv2 : configSum (weight2 A B) c = configSum (weight2 A B) (maxAffineInit A B x) := by
      exact configSum_invariant (maxAffineCRN A B) (weight2 A B)
        (fun r => by cases r with
          | inl i => exact wsum_delta_w2_conv A B i
          | inr r => exact wsum_delta_w2_aux A B r) hc
    -- (3) the two invariants in explicit form
    have h1 : (c (z1Spec) : ℤ) - (c (z2Spec) : ℤ) = (A.eval x : ℤ) - (B.eval x : ℤ) := by
      have hval := configSum_weight1 A B c
      rw [hInv1, configSum_weight1_init A B x] at hval
      have hsum0 : (∑ j, (((A.coeff j : ℤ) - (B.coeff j : ℤ)) * (c (xSpec j) : ℤ))) = 0 := by
        simp [hX]
      rw [hsum0, hp1, hp2] at hval
      omega
    have h2 : 2 * ((c (ySpec) : ℤ) - (c (kSpec) : ℤ))
        = (A.eval x : ℤ) + (B.eval x : ℤ) + (c (z1Spec) : ℤ) + (c (z2Spec) : ℤ) := by
      have hval := configSum_weight2 A B c
      rw [hInv2, configSum_weight2_init A B x] at hval
      have hsum0 : (∑ j, (((A.coeff j : ℤ) + (B.coeff j : ℤ)) * (c (xSpec j) : ℤ))) = 0 := by
        simp [hX]
      rw [hsum0, hp1, hp2] at hval
      omega
    -- (4) the output is the maximum of the two pieces
    have hY : c (ySpec) = Nat.max (A.eval x) (B.eval x) := by
      have hT1 : (0 : ℤ) ≤ (A.eval x : ℤ) := Int.natCast_nonneg _
      have hT2 : (0 : ℤ) ≤ (B.eval x : ℤ) := Int.natCast_nonneg _
      have hZ1 : (0 : ℤ) ≤ (c (z1Spec) : ℤ) := Int.natCast_nonneg _
      have hZ2 : (0 : ℤ) ≤ (c (z2Spec) : ℤ) := Int.natCast_nonneg _
      have hK : (0 : ℤ) ≤ (c (kSpec) : ℤ) := Int.natCast_nonneg _
      have hY0 : (0 : ℤ) ≤ (c (ySpec) : ℤ) := Int.natCast_nonneg _
      rcases hz with hz1 | hz2
      · -- the accumulator `Z₁` is empty, so the second piece is the larger one
        have hle : A.eval x ≤ B.eval x := by omega
        have hyk : (c (ySpec) : ℤ) - (c (kSpec) : ℤ) = (B.eval x : ℤ) := by omega
        rcases hk with hk1 | hk2
        · -- the auxiliary species `K` is empty
          have hy : c (ySpec) = B.eval x := by omega
          rw [hy]
          exact (Nat.max_eq_right hle).symm
        · -- the output species `Y` is empty, so both pieces are empty
          have hB0 : B.eval x = 0 := by omega
          have hA0 : A.eval x = 0 := by omega
          have hy0 : c (ySpec) = 0 := by omega
          rw [hy0]
          simp [hA0, hB0]
      · -- the accumulator `Z₂` is empty, so the first piece is the larger one
        have hle : B.eval x ≤ A.eval x := by omega
        have hyk : (c (ySpec) : ℤ) - (c (kSpec) : ℤ) = (A.eval x : ℤ) := by omega
        rcases hk with hk1 | hk2
        · -- the auxiliary species `K` is empty
          have hy : c (ySpec) = A.eval x := by omega
          rw [hy]
          exact (Nat.max_eq_left hle).symm
        · -- the output species `Y` is empty, so both pieces are empty
          have hA0 : A.eval x = 0 := by omega
          have hB0 : B.eval x = 0 := by omega
          have hy0 : c (ySpec) = 0 := by omega
          rw [hy0]
          simp [hA0, hB0]
    exact hY


/-- **The maximum of two affine maps is piecewiseNatAffine.**  The two regions on which the
maximum is one of the two affine maps are described by `Affine.diffFormula`. -/
theorem max_of_affine_piecewiseNatAffine {d : ℕ} (c₁ c₂ : ℕ) (e₁ e₂ : Fin d → ℕ) :
    PiecewiseNatAffine (fun x => Nat.max (c₁ + ∑ i, e₁ i * x i) (c₂ + ∑ i, e₂ i * x i)) :=
  PiecewiseNatAffine.max (piecewiseNatAffine_of_affine c₁ e₁) (piecewiseNatAffine_of_affine c₂ e₂)

/-- **The function `max (x 0) (x 1)` is piecewiseNatAffine.** -/
theorem max_piecewiseNatAffine : PiecewiseNatAffine (fun x : Fin 2 → ℕ => Nat.max (x 0) (x 1)) := by
  have h := max_of_affine_piecewiseNatAffine 0 0 (fun i : Fin 2 => if i = 0 then 1 else 0)
    (fun i : Fin 2 => if i = 1 then 1 else 0)
  convert h using 1
  funext x
  simp

/-! ### The maximum of two affine maps is piecewiseNatAffine and stably computed -/

/-- **The maximum of two affine maps is piecewiseNatAffine.**  This is the instance of
`PiecewiseNatAffine.max` for affine maps; the two regions are the ones of
`Affine.diffFormula`. -/
theorem maxAffine_piecewiseNatAffine {d : ℕ} (A B : Affine d) :
    PiecewiseNatAffine (fun x => Nat.max (A.eval x) (B.eval x)) := by
  have h := PiecewiseNatAffine.max (piecewiseNatAffine_of_affine A.const A.coeff)
    (piecewiseNatAffine_of_affine B.const B.coeff)
  convert h using 1
  funext x
  simp [Affine.eval]

/-- **A concrete instance.**  The network `maxAffineCRN` computes the maximum of the two
affine maps `x ↦ 2 * x 0` and `x ↦ x 0 + 3` of `ℕ → ℕ`: the output species holds
`max (2 * x 0) (x 0 + 3)` molecules. -/
theorem max_two_affines_example :
    StablyComputes (maxAffineCRN (d := 1) ⟨0, fun _ => 2⟩ ⟨3, fun _ => 1⟩)
      (maxAffineInit (d := 1) ⟨0, fun _ => 2⟩ ⟨3, fun _ => 1⟩)
      ySpec
      (fun x => Nat.max ((⟨0, fun _ => 2⟩ : Affine 1).eval x)
        ((⟨3, fun _ => 1⟩ : Affine 1).eval x)) :=
  maxAffineCRN_stablyComputes (d := 1) ⟨0, fun _ => 2⟩ ⟨3, fun _ => 1⟩

end MaxAffine

/-! ### The principal declarations -/

#print axioms CRNT.Computation.PiecewiseNatAffine.max
#print axioms CRNT.Computation.Affine.diffFormula_satisfied
#print axioms CRNT.Computation.region_split
#print axioms CRNT.Computation.region_split_union
#print axioms CRNT.Computation.max_of_affine_piecewiseNatAffine
#print axioms CRNT.Computation.piecewiseNatAffine_max_add
#print axioms CRNT.Computation.MaxAffine.maxAffineCRN_stablyComputes
#print axioms CRNT.Computation.MaxAffine.maxAffine_piecewiseNatAffine
#print axioms CRNT.Computation.MaxAffine.max_two_affines_example

end Computation

end CRNT
