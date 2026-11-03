import CRNT.Decision.ConservationConeStrict
import CRNT.Stoich.RationalVector
import CRNT.Decision.RationalFarkasDecide

/-!
# Deciding the critical-siphon verdict

`Network.IsCriticalSiphon P` is critical when `P` is a nonempty siphon carrying no positive
conservation law supported exactly on `P`. The strict-support alternative
(`isCriticalSiphon_iff_exists_pointwise`) reduces the conservation obstruction to a finite
conjunction over the species of `P`: for each `s ∈ P`, whether some `SupportedConservationVector P`
is strictly positive at `s`. This module turns each such single-coordinate existence into a finite
rational linear-feasibility problem and decides it.

Each single-coordinate problem `∃ w : S → ℝ, SupportedConservationVector P w ∧ 0 < w s₀` is a
homogeneous cone-membership question with rational data — the reaction vectors have integer entries
`target − source`. Scaling a witness so that `w s₀ = 1` turns it into the existence of a vector that
is nonnegative, vanishes off `P`, is orthogonal to every reaction, and equals `1` at `s₀`: a finite
rational system of linear inequalities (each equality split into a `≤`/`≥` pair).

* `Network.supportedFeasSystem` — the encoded rational system `List (Ineq (Fintype.card S))` whose
  feasibility is the scaled single-coordinate existence. Its variables are indexed through an
  explicit species enumeration `e : S ≃ Fin (Fintype.card S)` taken as data, keeping the encoding
  computable; a concrete `e` is drawn from the `Fintype` and the resulting decision lifted through
  the subsingleton of `Decidable`.
* `feasibleℝ_iff_feasible` — **the rational–real feasibility bridge**: a rational `Ineq` system has a
  real solution iff it has a rational one. The rational solution casts to a real one; conversely a
  real solution projects through Fourier–Motzkin elimination (the division-free combination rows are
  arithmetic identities valid over `ℝ`) down to a `Fin 0` system whose bounds are then nonnegative
  rationals, certifying rational feasibility via `feasible_zero_iff`.
* `feasible_supportedFeasSystem_iff` — **the encoding equivalence**: `supportedFeasSystem` is feasible
  iff some supported conservation vector is strictly positive at `s₀`.
* `decidableIsCriticalSiphon`, `decidableHasNoCriticalSiphon`, and the `HasCriticalSiphon` existence
  with `decidableHasCriticalSiphon` — the decidable critical-siphon verdict.

The conservation-law feasibility framing of (non)critical siphons is from Angeli, De Leenheer, and
Sontag, *A Petri net approach to the study of persistence in chemical reaction networks*; the
feasibility reduction is the constructive content of Farkas' lemma by Fourier–Motzkin elimination.

Depends on: `CRNT.Decision.ConservationConeStrict`,
`CRNT.Decision.RationalFarkasDecide`.
-/

open scoped BigOperators

namespace CRNT

namespace RationalFarkas

/-! ## The rational–real feasibility bridge

A rational `Ineq` system is *real-feasible* when some real point satisfies every row read over `ℝ`.
The bridge equates this with rational feasibility. The reverse implication replays the forward half
of Fourier–Motzkin elimination over `ℝ`: a real solution projects to a real solution of the
eliminated system, and recursion lands in a `Fin 0` system whose nonnegative-bound certificate is
rational. -/

/-- The left-hand value of an inequality read over `ℝ`: `∑ⱼ (coeff j : ℝ) * x j`. -/
def Ineq.lhsℝ {n : ℕ} (I : Ineq n) (x : Fin n → ℝ) : ℝ :=
  ∑ j, (I.coeff j : ℝ) * x j

/-- A real point satisfies an inequality when its real left-hand value is at most the bound. -/
def Ineq.holdsℝ {n : ℕ} (I : Ineq n) (x : Fin n → ℝ) : Prop :=
  I.lhsℝ x ≤ (I.bound : ℝ)

/-- A real point satisfies a system when it satisfies every row over `ℝ`. -/
def Satℝ {n : ℕ} (sys : List (Ineq n)) (x : Fin n → ℝ) : Prop :=
  ∀ I ∈ sys, I.holdsℝ x

/-- A system is *real-feasible* when some real point satisfies it. -/
def Feasibleℝ {n : ℕ} (sys : List (Ineq n)) : Prop :=
  ∃ x, Satℝ sys x

/-- Splitting the real left-hand sum off the last coordinate. -/
theorem Ineq.lhsℝ_eq_dropLast_add {n : ℕ} (I : Ineq (n + 1)) (x : Fin (n + 1) → ℝ) :
    I.lhsℝ x = I.dropLast.lhsℝ (Fin.init x) + (I.lastCoeff : ℝ) * x (Fin.last n) := by
  unfold Ineq.lhsℝ Ineq.dropLast Ineq.lastCoeff Fin.init
  rw [Fin.sum_univ_castSucc]

/-- The real left-hand value of a combination row expands as the corresponding real combination. -/
theorem combine_lhsℝ {n : ℕ} (lo hi : Ineq (n + 1)) (x : Fin n → ℝ) :
    (combine lo hi).lhsℝ x
      = (hi.lastCoeff : ℝ) * lo.dropLast.lhsℝ x - (lo.lastCoeff : ℝ) * hi.dropLast.lhsℝ x := by
  simp only [combine, Ineq.lhsℝ, Ineq.dropLast, Fin.init, Rat.cast_sub, Rat.cast_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **Forward half of elimination, over `ℝ`.** A real solution of the original system projects to a
real solution of the eliminated system: zero rows lose only a vanishing last term, and combination
rows are a positive combination of two satisfied rows. -/
theorem satℝ_eliminateLast_of_satℝ {n : ℕ} {sys : List (Ineq (n + 1))} {x : Fin (n + 1) → ℝ}
    (hx : Satℝ sys x) : Satℝ (eliminateLast sys) (Fin.init x) := by
  intro J hJ
  rw [eliminateLast, List.mem_append] at hJ
  rcases hJ with hJ | hJ
  · rw [zeroRows, List.mem_map] at hJ
    obtain ⟨I, hI, rfl⟩ := hJ
    rw [List.mem_filter] at hI
    obtain ⟨hImem, hzero⟩ := hI
    have hI := hx I hImem
    have hsplit := I.lhsℝ_eq_dropLast_add x
    simp only [decide_eq_true_eq] at hzero
    rw [hzero, Rat.cast_zero, zero_mul, add_zero] at hsplit
    rw [Ineq.holdsℝ, ← hsplit]
    exact hI
  · rw [comboRows, List.mem_flatMap] at hJ
    obtain ⟨lo, hlo, hJ⟩ := hJ
    rw [List.mem_map] at hJ
    obtain ⟨hi, hhi, rfl⟩ := hJ
    rw [loRows, List.mem_filter] at hlo
    obtain ⟨hlomem, hloneg⟩ := hlo
    rw [hiRows, List.mem_filter] at hhi
    obtain ⟨himem, hhipos⟩ := hhi
    simp only [decide_eq_true_eq] at hloneg hhipos
    have hloneg' : (lo.lastCoeff : ℝ) < 0 := by exact_mod_cast hloneg
    have hhipos' : (0 : ℝ) < (hi.lastCoeff : ℝ) := by exact_mod_cast hhipos
    have hLo := hx lo hlomem
    have hHi := hx hi himem
    rw [Ineq.holdsℝ, lo.lhsℝ_eq_dropLast_add x] at hLo
    rw [Ineq.holdsℝ, hi.lhsℝ_eq_dropLast_add x] at hHi
    rw [Ineq.holdsℝ, combine_lhsℝ]
    have hbound : ((combine lo hi).bound : ℝ)
        = (hi.lastCoeff : ℝ) * (lo.bound : ℝ) - (lo.lastCoeff : ℝ) * (hi.bound : ℝ) := by
      simp only [combine, Rat.cast_sub, Rat.cast_mul]
    rw [hbound]
    have e1 : (hi.lastCoeff : ℝ) * (lo.dropLast.lhsℝ (Fin.init x) + (lo.lastCoeff : ℝ) * x (Fin.last n))
        ≤ (hi.lastCoeff : ℝ) * (lo.bound : ℝ) :=
      mul_le_mul_of_nonneg_left hLo (le_of_lt hhipos')
    have e2 : (-(lo.lastCoeff : ℝ)) * (hi.dropLast.lhsℝ (Fin.init x) + (hi.lastCoeff : ℝ) * x (Fin.last n))
        ≤ (-(lo.lastCoeff : ℝ)) * (hi.bound : ℝ) :=
      mul_le_mul_of_nonneg_left hHi (by linarith)
    nlinarith [e1, e2]

/-- A `Fin 0` system is real-feasible iff every bound is nonnegative — and then iff it is rationally
feasible, since the bounds are rationals. -/
theorem feasibleℝ_zero_iff (sys : List (Ineq 0)) :
    Feasibleℝ sys ↔ ∀ row ∈ sys, 0 ≤ row.bound := by
  constructor
  · rintro ⟨x, hx⟩ row hrow
    have := hx row hrow
    rw [Ineq.holdsℝ, Ineq.lhsℝ, Fin.sum_univ_zero] at this
    exact_mod_cast this
  · intro h
    refine ⟨0, fun I hI => ?_⟩
    rw [Ineq.holdsℝ, Ineq.lhsℝ, Fin.sum_univ_zero]
    exact_mod_cast h I hI

/-- **The rational–real feasibility bridge.** A rational `Ineq` system has a real solution iff it has
a rational one. The forward implication coerces a rational witness; the reverse replays Fourier–Motzkin
elimination over `ℝ` (the combination rows are arithmetic identities valid over `ℝ`) down to a `Fin 0`
system whose nonnegative-bound certificate is rational, then reuses the rational elimination
equivalence `feasible_eliminateLast_iff`. -/
theorem feasibleℝ_iff_feasible : ∀ {n : ℕ} (sys : List (Ineq n)), Feasibleℝ sys ↔ Feasible sys
  | 0, sys => by
      rw [feasibleℝ_zero_iff, feasible_zero_iff]
  | n + 1, sys => by
      constructor
      · rintro ⟨x, hx⟩
        have hproj : Feasibleℝ (eliminateLast sys) := ⟨Fin.init x, satℝ_eliminateLast_of_satℝ hx⟩
        have hQ : Feasible (eliminateLast sys) := (feasibleℝ_iff_feasible (eliminateLast sys)).mp hproj
        exact (feasible_eliminateLast_iff sys).mp hQ
      · rintro ⟨x, hx⟩
        refine ⟨fun i => ((x i : ℝ)), fun I hI => ?_⟩
        have := hx I hI
        rw [Ineq.holds, Ineq.lhs] at this
        rw [Ineq.holdsℝ, Ineq.lhsℝ]
        have hcast : ∑ j, (I.coeff j : ℝ) * ((x j : ℝ)) = (((∑ j, I.coeff j * x j) : ℚ) : ℝ) := by
          push_cast; ring
        rw [hcast]
        exact_mod_cast this

end RationalFarkas

/-- A computable enumeration of a finite type from an explicit equivalence with `Fin (card α)`: the
images of `List.finRange (card α)` under `e.symm`. Every element appears (`mem_enumOfEquiv`). -/
def enumOfEquiv {α : Type*} [Fintype α] (e : α ≃ Fin (Fintype.card α)) : List α :=
  (List.finRange (Fintype.card α)).map e.symm

/-- Every element of a finite type appears in its `enumOfEquiv` enumeration. -/
theorem mem_enumOfEquiv {α : Type*} [Fintype α] (e : α ≃ Fin (Fintype.card α)) (a : α) :
    a ∈ enumOfEquiv e :=
  List.mem_map.2 ⟨e a, List.mem_finRange _, by rw [Equiv.symm_apply_apply]⟩

namespace Network

open RationalFarkas

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A row of the encoded system from a rational coefficient function on species and a bound, indexing
the variables through an explicit species enumeration `e : S ≃ Fin (Fintype.card S)`. The variable
indexed by `i : Fin (Fintype.card S)` is the value at species `e.symm i`. Taking `e` as data keeps
the encoding computable. -/
def encodeRow (e : S ≃ Fin (Fintype.card S)) (c : S → ℚ) (b : ℚ) : Ineq (Fintype.card S) where
  coeff := fun i => c (e.symm i)
  bound := b

omit [DecidableEq S] in
@[simp] theorem encodeRow_bound (e : S ≃ Fin (Fintype.card S)) (c : S → ℚ) (b : ℚ) :
    (encodeRow (S := S) e c b).bound = b := rfl

omit [DecidableEq S] in
/-- The real left-hand value of an encoded row reindexes to a sum over species of the corresponding
real point `w s = x (e s)`. -/
theorem lhsℝ_encodeRow (e : S ≃ Fin (Fintype.card S)) (c : S → ℚ) (b : ℚ)
    (x : Fin (Fintype.card S) → ℝ) :
    (encodeRow e c b).lhsℝ x = ∑ s, (c s : ℝ) * x (e s) := by
  rw [Ineq.lhsℝ, encodeRow]
  rw [← Equiv.sum_comp e (fun i => ((c (e.symm i) : ℝ)) * x i)]
  apply Finset.sum_congr rfl
  intro s _
  rw [Equiv.symm_apply_apply]

/-- The **encoded rational feasibility system** for the single-coordinate problem at `s₀` over siphon
`P`. Its rows are: nonnegativity `w s ≥ 0` at every species; `w s ≤ 0` off `P` (forcing the support
into `P`); the reaction-orthogonality equalities `∑ₛ w s · (reaction r)ₛ = 0` as `≤`/`≥` pairs; and
the normalization `w s₀ = 1` as a `≤`/`≥` pair. -/
def supportedFeasSystem (N : Network S) (e : S ≃ Fin (Fintype.card S))
    (eR : N.R ≃ Fin (Fintype.card N.R)) (P : Finset S) (s₀ : S) :
    List (Ineq (Fintype.card S)) :=
  ((enumOfEquiv e).map fun s => encodeRow e (fun t => if t = s then -1 else 0) 0) ++
  ((enumOfEquiv e).filter (fun s => s ∉ P)).map
      (fun s => encodeRow e (fun t => if t = s then 1 else 0) 0) ++
  ((enumOfEquiv eR).flatMap fun r : N.R =>
      [encodeRow e (fun s => N.reactionCoeffQ r s) 0,
       encodeRow e (fun s => -(N.reactionCoeffQ r s)) 0]) ++
  [encodeRow e (fun t => if t = s₀ then 1 else 0) 1,
   encodeRow e (fun t => if t = s₀ then -1 else 0) (-1)]

/-- The scaled single-coordinate conditions packaged on a real species vector: nonnegative, vanishing
off `P`, orthogonal to every reaction, and normalized to `1` at `s₀`. -/
def NormalizedSupportedVector (N : Network S) (P : Finset S) (s₀ : S) (w : S → ℝ) : Prop :=
  (∀ s, 0 ≤ w s) ∧ (∀ s ∉ P, w s = 0) ∧
    (∀ r : N.R, ∑ s, w s * N.reactionVector r s = 0) ∧ w s₀ = 1

/-- **Real satisfaction of the encoded system equals the normalized conditions.** A real point
satisfies `supportedFeasSystem` iff the species vector it represents is normalized-supported. -/
theorem satℝ_supportedFeasSystem_iff (N : Network S) (e : S ≃ Fin (Fintype.card S))
    (eR : N.R ≃ Fin (Fintype.card N.R)) (P : Finset S) (s₀ : S) (x : Fin (Fintype.card S) → ℝ) :
    Satℝ (N.supportedFeasSystem e eR P s₀) x ↔
      N.NormalizedSupportedVector P s₀ (fun s => x (e s)) := by
  set w : S → ℝ := fun s => x (e s) with hw
  constructor
  · intro hx
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- nonnegativity from the `-w s ≤ 0` rows
      intro s
      have hmem : encodeRow e (fun t => if t = s then (-1 : ℚ) else 0) 0
          ∈ N.supportedFeasSystem e eR P s₀ := by
        rw [supportedFeasSystem]
        refine List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl ?_)))))
        exact List.mem_map.2 ⟨s, mem_enumOfEquiv e s, rfl⟩
      have := hx _ hmem
      rw [Ineq.holdsℝ, lhsℝ_encodeRow] at this
      have hsum : ∑ t, ((if t = s then (-1 : ℚ) else 0 : ℚ) : ℝ) * w t = - w s := by
        rw [Finset.sum_eq_single s]
        · simp
        · intro t _ ht; simp [ht]
        · intro h; exact absurd (Finset.mem_univ s) h
      rw [hsum] at this
      simp only [encodeRow_bound, Rat.cast_zero] at this
      linarith
    · -- vanishing off `P`: combine the `w s ≤ 0` row with nonnegativity
      intro s hs
      have hnn : 0 ≤ w s := by
        have hmem : encodeRow e (fun t => if t = s then (-1 : ℚ) else 0) 0
            ∈ N.supportedFeasSystem e eR P s₀ := by
          rw [supportedFeasSystem]
          refine List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl ?_)))))
          exact List.mem_map.2 ⟨s, mem_enumOfEquiv e s, rfl⟩
        have := hx _ hmem
        rw [Ineq.holdsℝ, lhsℝ_encodeRow] at this
        have hsum : ∑ t, ((if t = s then (-1 : ℚ) else 0 : ℚ) : ℝ) * w t = - w s := by
          rw [Finset.sum_eq_single s]
          · simp
          · intro t _ ht; simp [ht]
          · intro h; exact absurd (Finset.mem_univ s) h
        rw [hsum] at this; simp only [encodeRow_bound, Rat.cast_zero] at this; linarith
      have hle : w s ≤ 0 := by
        have hmem : encodeRow e (fun t => if t = s then (1 : ℚ) else 0) 0
            ∈ N.supportedFeasSystem e eR P s₀ := by
          rw [supportedFeasSystem]
          refine List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr ?_)))))
          refine List.mem_map.2 ⟨s, ?_, rfl⟩
          rw [List.mem_filter]
          exact ⟨mem_enumOfEquiv e s, by simpa using hs⟩
        have := hx _ hmem
        rw [Ineq.holdsℝ, lhsℝ_encodeRow] at this
        have hsum : ∑ t, ((if t = s then (1 : ℚ) else 0 : ℚ) : ℝ) * w t = w s := by
          rw [Finset.sum_eq_single s]
          · simp
          · intro t _ ht; simp [ht]
          · intro h; exact absurd (Finset.mem_univ s) h
        rw [hsum] at this; simp only [encodeRow_bound, Rat.cast_zero] at this; linarith
      linarith
    · -- orthogonality from the `≤`/`≥` pair on each reaction
      intro r
      have hle : ∑ s, w s * N.reactionVector r s ≤ 0 := by
        have hmem : encodeRow e (fun s => N.reactionCoeffQ r s) 0
            ∈ N.supportedFeasSystem e eR P s₀ := by
          rw [supportedFeasSystem]
          refine List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr ?_)))
          rw [List.mem_flatMap]
          exact ⟨r, mem_enumOfEquiv eR r, by simp⟩
        have := hx _ hmem
        rw [Ineq.holdsℝ, lhsℝ_encodeRow] at this
        simp only [encodeRow_bound, Rat.cast_zero] at this
        have heq : ∑ s, w s * N.reactionVector r s
            = ∑ s, ((N.reactionCoeffQ r s : ℝ)) * w s := by
          apply Finset.sum_congr rfl; intro s _; rw [cast_reactionCoeffQ]; ring
        rw [heq]; exact this
      have hge : 0 ≤ ∑ s, w s * N.reactionVector r s := by
        have hmem : encodeRow e (fun s => -(N.reactionCoeffQ r s)) 0
            ∈ N.supportedFeasSystem e eR P s₀ := by
          rw [supportedFeasSystem]
          refine List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr ?_)))
          rw [List.mem_flatMap]
          exact ⟨r, mem_enumOfEquiv eR r, by simp⟩
        have := hx _ hmem
        rw [Ineq.holdsℝ, lhsℝ_encodeRow] at this
        simp only [encodeRow_bound, Rat.cast_zero, Rat.cast_neg] at this
        have hneg : ∑ s, -((N.reactionCoeffQ r s : ℝ)) * w s
            = - ∑ s, w s * N.reactionVector r s := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro s _
          rw [cast_reactionCoeffQ]; ring
        rw [hneg] at this; linarith
      linarith
    · -- normalization at `s₀`
      have hle : w s₀ ≤ 1 := by
        have hmem : encodeRow e (fun t => if t = s₀ then (1 : ℚ) else 0) 1
            ∈ N.supportedFeasSystem e eR P s₀ := by
          rw [supportedFeasSystem]
          refine List.mem_append.2 (Or.inr ?_)
          simp
        have := hx _ hmem
        rw [Ineq.holdsℝ, lhsℝ_encodeRow] at this
        have hsum : ∑ t, ((if t = s₀ then (1 : ℚ) else 0 : ℚ) : ℝ) * w t = w s₀ := by
          rw [Finset.sum_eq_single s₀]
          · simp
          · intro t _ ht; simp [ht]
          · intro h; exact absurd (Finset.mem_univ s₀) h
        rw [hsum] at this; simpa using this
      have hge : 1 ≤ w s₀ := by
        have hmem : encodeRow e (fun t => if t = s₀ then (-1 : ℚ) else 0) (-1)
            ∈ N.supportedFeasSystem e eR P s₀ := by
          rw [supportedFeasSystem]
          refine List.mem_append.2 (Or.inr ?_)
          simp
        have := hx _ hmem
        rw [Ineq.holdsℝ, lhsℝ_encodeRow] at this
        have hsum : ∑ t, ((if t = s₀ then (-1 : ℚ) else 0 : ℚ) : ℝ) * w t = - w s₀ := by
          rw [Finset.sum_eq_single s₀]
          · simp
          · intro t _ ht; simp [ht]
          · intro h; exact absurd (Finset.mem_univ s₀) h
        rw [hsum] at this; simp only [encodeRow_bound, Rat.cast_neg, Rat.cast_one] at this; linarith
      linarith
  · rintro ⟨hnn, hoff, hcons, hnorm⟩ I hI
    rw [supportedFeasSystem] at hI
    -- dispatch by which block `I` belongs to
    rw [List.mem_append, List.mem_append, List.mem_append] at hI
    rcases hI with ((hI | hI) | hI) | hI
    · -- nonnegativity row
      rw [List.mem_map] at hI
      obtain ⟨s, _, rfl⟩ := hI
      rw [Ineq.holdsℝ, lhsℝ_encodeRow]
      have hsum : ∑ t, ((if t = s then (-1 : ℚ) else 0 : ℚ) : ℝ) * w t = - w s := by
        rw [Finset.sum_eq_single s]
        · simp
        · intro t _ ht; simp [ht]
        · intro h; exact absurd (Finset.mem_univ s) h
      rw [hsum]; simp only [encodeRow_bound, Rat.cast_zero]; linarith [hnn s]
    · -- vanish-off-`P` row
      rw [List.mem_map] at hI
      obtain ⟨s, hsf, rfl⟩ := hI
      rw [List.mem_filter] at hsf
      have hsP : s ∉ P := by simpa using hsf.2
      rw [Ineq.holdsℝ, lhsℝ_encodeRow]
      have hsum : ∑ t, ((if t = s then (1 : ℚ) else 0 : ℚ) : ℝ) * w t = w s := by
        rw [Finset.sum_eq_single s]
        · simp
        · intro t _ ht; simp [ht]
        · intro h; exact absurd (Finset.mem_univ s) h
      rw [hsum]; simp only [encodeRow_bound, Rat.cast_zero, hoff s hsP]; linarith
    · -- orthogonality rows
      rw [List.mem_flatMap] at hI
      obtain ⟨r, _, hI⟩ := hI
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
      rcases hI with rfl | rfl
      · rw [Ineq.holdsℝ, lhsℝ_encodeRow]
        have : ∑ s, ((N.reactionCoeffQ r s : ℝ)) * w s = ∑ s, w s * N.reactionVector r s := by
          apply Finset.sum_congr rfl; intro s _; rw [cast_reactionCoeffQ]; ring
        rw [this, hcons r]; simp
      · rw [Ineq.holdsℝ, lhsℝ_encodeRow]
        have : ∑ s, ((-(N.reactionCoeffQ r s) : ℚ) : ℝ) * w s
            = - ∑ s, w s * N.reactionVector r s := by
          rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl
          intro s _; rw [Rat.cast_neg, cast_reactionCoeffQ]; ring
        rw [this, hcons r]; simp
    · -- normalization rows
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
      rcases hI with rfl | rfl
      · rw [Ineq.holdsℝ, lhsℝ_encodeRow]
        have hsum : ∑ t, ((if t = s₀ then (1 : ℚ) else 0 : ℚ) : ℝ) * w t = w s₀ := by
          rw [Finset.sum_eq_single s₀]
          · simp
          · intro t _ ht; simp [ht]
          · intro h; exact absurd (Finset.mem_univ s₀) h
        rw [hsum, hnorm]; simp
      · rw [Ineq.holdsℝ, lhsℝ_encodeRow]
        have hsum : ∑ t, ((if t = s₀ then (-1 : ℚ) else 0 : ℚ) : ℝ) * w t = - w s₀ := by
          rw [Finset.sum_eq_single s₀]
          · simp
          · intro t _ ht; simp [ht]
          · intro h; exact absurd (Finset.mem_univ s₀) h
        rw [hsum, hnorm]; simp

/-- **Scaling equivalence.** A normalized supported vector (positive scale fixed by `w s₀ = 1`)
exists iff some supported conservation vector is strictly positive at `s₀`. The forward direction
reads `w s₀ = 1 > 0`; the reverse rescales a positive-at-`s₀` witness by `1 / w s₀`. -/
theorem exists_normalized_iff_exists_pos (N : Network S) (P : Finset S) (s₀ : S) :
    (∃ w : S → ℝ, N.NormalizedSupportedVector P s₀ w) ↔
      (∃ w : S → ℝ, N.SupportedConservationVector P w ∧ 0 < w s₀) := by
  constructor
  · rintro ⟨w, hnn, hoff, hcons, hnorm⟩
    exact ⟨w, ⟨hnn, hoff, hcons⟩, by rw [hnorm]; norm_num⟩
  · rintro ⟨w, ⟨hnn, hoff, hcons⟩, hpos⟩
    refine ⟨fun s => w s / w s₀, ?_, ?_, ?_, ?_⟩
    · intro s; exact div_nonneg (hnn s) (le_of_lt hpos)
    · intro s hs; show w s / w s₀ = 0; rw [hoff s hs, zero_div]
    · intro r
      have : ∀ s, w s / w s₀ * N.reactionVector r s
          = (w s * N.reactionVector r s) / w s₀ := fun s => by ring
      simp only [this, ← Finset.sum_div, hcons r, zero_div]
    · exact div_self (ne_of_gt hpos)

/-- **The encoding equivalence.** The encoded rational system is feasible iff some supported
conservation vector is strictly positive at `s₀` — the single-coordinate obstruction of the
critical-siphon strict-support alternative. Feasibility passes through the rational–real bridge to
real satisfaction, which the row-by-row characterization equates with the normalized conditions, and
the scaling equivalence removes the normalization. -/
theorem feasible_supportedFeasSystem_iff (N : Network S) (e : S ≃ Fin (Fintype.card S))
    (eR : N.R ≃ Fin (Fintype.card N.R)) (P : Finset S) (s₀ : S) :
    Feasible (N.supportedFeasSystem e eR P s₀) ↔
      (∃ w : S → ℝ, N.SupportedConservationVector P w ∧ 0 < w s₀) := by
  rw [← exists_normalized_iff_exists_pos]
  rw [← feasibleℝ_iff_feasible]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨_, (N.satℝ_supportedFeasSystem_iff e eR P s₀ x).mp hx⟩
  · rintro ⟨w, hw⟩
    refine ⟨fun i => w (e.symm i), ?_⟩
    rw [N.satℝ_supportedFeasSystem_iff e eR P s₀]
    have hfun : (fun s => w (e.symm (e s))) = w := by
      funext s; rw [Equiv.symm_apply_apply]
    rw [hfun]; exact hw

/-- The single-coordinate supported-positivity test at `s₀`, decided through an explicit species
enumeration `e`: it is the feasibility of the encoded rational system, evaluated by Fourier–Motzkin
elimination. Taking `e` as data makes this instance computable. -/
def decidableExistsSupportedPosOfEquiv (N : Network S) (e : S ≃ Fin (Fintype.card S))
    (eR : N.R ≃ Fin (Fintype.card N.R)) (P : Finset S) (s₀ : S) :
    Decidable (∃ w : S → ℝ, N.SupportedConservationVector P w ∧ 0 < w s₀) :=
  decidable_of_iff _ (N.feasible_supportedFeasSystem_iff e eR P s₀)

/-- The single-coordinate supported-positivity test at `s₀` is decidable. The decision is the
feasibility of the encoded rational system; species and reaction enumerations are drawn computably
from the `Fintype` instances and lifted through the subsingleton of `Decidable`, so the instance is
computable and independent of the chosen enumerations. -/
instance decidableExistsSupportedPos (N : Network S) (P : Finset S) (s₀ : S) :
    Decidable (∃ w : S → ℝ, N.SupportedConservationVector P w ∧ 0 < w s₀) :=
  Trunc.recOnSubsingleton (Fintype.truncEquivFin S) fun e =>
    Trunc.recOnSubsingleton (Fintype.truncEquivFin N.R) fun eR =>
      N.decidableExistsSupportedPosOfEquiv e eR P s₀

/-- **Decidability of the critical-siphon verdict.** Via the strict-support alternative, `P` is a
critical siphon iff it is a nonempty siphon and some species of `P` fails its single-coordinate
supported-positivity test — each test being feasibility of the encoded rational system, decided by
Fourier–Motzkin elimination. -/
instance decidableIsCriticalSiphon (N : Network S) (P : Finset S) :
    Decidable (N.IsCriticalSiphon P) :=
  decidable_of_iff _ (N.isCriticalSiphon_iff_exists_pointwise P).symm

/-- A network **has a critical siphon** when some species subset is a critical siphon. This is the
kill-switch verdict for persistence: its negation is `HasNoCriticalSiphon`. -/
def HasCriticalSiphon (N : Network S) : Prop :=
  ∃ P : Finset S, N.IsCriticalSiphon P

/-- The critical-siphon verdict is decidable: it ranges over the finitely many species subsets, each
test decidable by `decidableIsCriticalSiphon`. -/
instance decidableHasCriticalSiphon (N : Network S) :
    Decidable (N.HasCriticalSiphon) :=
  inferInstanceAs (Decidable (∃ P : Finset S, N.IsCriticalSiphon P))

/-- Absence of a critical siphon is decidable, the negation of the critical-siphon verdict over the
finitely many species subsets. -/
instance decidableHasNoCriticalSiphon (N : Network S) :
    Decidable (N.HasNoCriticalSiphon) :=
  inferInstanceAs (Decidable (∀ P : Finset S, ¬ N.IsCriticalSiphon P))

/-- `HasNoCriticalSiphon` is exactly the negation of `HasCriticalSiphon`. -/
theorem hasNoCriticalSiphon_iff_not_hasCriticalSiphon (N : Network S) :
    N.HasNoCriticalSiphon ↔ ¬ N.HasCriticalSiphon := by
  rw [HasNoCriticalSiphon, HasCriticalSiphon, not_exists]

end Network

end CRNT
