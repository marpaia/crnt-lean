import CRNT.Dynamics.TierPersistence
import CRNT.Decision.CriticalSiphonDecide

/-!
# Finite linear feasibility for tier-direction witnesses

The difficult direction in the strongly-endotactic/tier characterization asks for one linear
functional `w` that realizes all asymptotic tier comparisons of a transversal tier sequence.
Because a network has only finitely many occurring complexes, existence of such a `w` is a finite
rational linear-feasibility problem.

For every ordered pair of occurring complexes `(y,y')` we encode:

* `y ~ y'` by the two rows `w·(y-y') ≤ 0` and `w·(y'-y) ≤ 0`;
* `y ≺ y'` by the normalized strict-separation row `w·(y-y') ≤ -1`.

The normalization loses nothing: a finite collection of strict negative inequalities can always be
scaled simultaneously once a direction exists.  This module proves the direction needed by the
CRNT theorem: **any real feasible point of the encoded system is an exact `TierRealizesDirection`
witness**.  Thus the remaining subsequence theorem can be stated as a concrete finite-feasibility
claim rather than an opaque existence of a function `S → ℝ`.

No feasibility theorem is assumed here.
-/

open Filter
open scoped BigOperators Topology

namespace CRNT
namespace Network

open RationalFarkas

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A strict-lower tier comparison cannot simultaneously be a same-tier comparison. -/
theorem TierStrictBelow.not_tierSame {xs : ℕ → Concentration S} {y y' : Complex S}
    (hbelow : TierStrictBelow xs y y') : ¬ TierSame xs y y' := by
  rintro ⟨c, hcpos, hsame⟩
  have hc0 : c = 0 := tendsto_nhds_unique hsame hbelow
  linarith

/-- Rational coefficient vector representing the complex difference `y - y'`. -/
def tierDiffCoeff (y y' : Complex S) : S → ℚ :=
  fun s => (y s : ℚ) - (y' s : ℚ)

/-- Rows contributed by one ordered pair of occurring complexes. -/
noncomputable def tierComparisonRows (e : S ≃ Fin (Fintype.card S))
    (xs : ℕ → Concentration S) (y y' : Complex S) : List (Ineq (Fintype.card S)) := by
  classical
  exact if hsame : TierSame xs y y' then
      [encodeRow e (tierDiffCoeff y y') 0,
       encodeRow e (tierDiffCoeff y' y) 0]
    else if hbelow : TierStrictBelow xs y y' then
      [encodeRow e (tierDiffCoeff y y') (-1)]
    else []

/-- Finite rational linear system whose feasible points realize all tier comparisons of `xs` on
`N.complexes`. -/
noncomputable def tierDirectionSystem (N : Network S) (e : S ≃ Fin (Fintype.card S))
    (xs : ℕ → Concentration S) : List (Ineq (Fintype.card S)) := by
  classical
  exact (N.complexes ×ˢ N.complexes).toList.flatMap
    (fun p => tierComparisonRows e xs p.1 p.2)

/-- The left-hand side of an encoded tier-difference row is exactly the difference of complex
potentials for the reindexed real vector. -/
theorem lhsℝ_tierDiffRow (e : S ≃ Fin (Fintype.card S))
    (x : Fin (Fintype.card S) → ℝ) (y y' : Complex S) (b : ℚ) :
    (encodeRow e (tierDiffCoeff y y') b).lhsℝ x =
      complexWValue (fun s => x (e s)) y - complexWValue (fun s => x (e s)) y' := by
  rw [lhsℝ_encodeRow]
  simp only [tierDiffCoeff, Rat.cast_sub, Rat.cast_natCast, complexWValue, dotProduct,
    exponentVector, Finset.sum_sub_distrib]
  -- the simp set split the right-hand side into two sums; recombine before comparing termwise
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Same-tier comparisons contribute both zero-bound rows to the system. -/
theorem same_rows_mem_tierDirectionSystem (N : Network S)
    (e : S ≃ Fin (Fintype.card S)) (xs : ℕ → Concentration S)
    {y y' : Complex S} (hy : y ∈ N.complexes) (hy' : y' ∈ N.complexes)
    (hsame : TierSame xs y y') :
    encodeRow e (tierDiffCoeff y y') 0 ∈ N.tierDirectionSystem e xs ∧
      encodeRow e (tierDiffCoeff y' y) 0 ∈ N.tierDirectionSystem e xs := by
  classical
  -- both rows come from the *same* pair `(y, y')`, so the same witnesses serve twice;
  -- `simp` reduces membership to an existential over the complex pair but cannot guess them.
  have hmem : ∀ I ∈ tierComparisonRows e xs y y', I ∈ N.tierDirectionSystem e xs := by
    intro I hI
    simp only [tierDirectionSystem, List.mem_flatMap, Finset.mem_toList,
      Finset.mem_product, Prod.exists]
    exact ⟨y, y', ⟨hy, hy'⟩, hI⟩
  refine ⟨hmem _ ?_, hmem _ ?_⟩ <;>
    simp [tierComparisonRows, hsame]

/-- Strict tier comparisons contribute the normalized `≤ -1` row. -/
theorem below_row_mem_tierDirectionSystem (N : Network S)
    (e : S ≃ Fin (Fintype.card S)) (xs : ℕ → Concentration S)
    {y y' : Complex S} (hy : y ∈ N.complexes) (hy' : y' ∈ N.complexes)
    (hbelow : TierStrictBelow xs y y') :
    encodeRow e (tierDiffCoeff y y') (-1) ∈ N.tierDirectionSystem e xs := by
  classical
  have hnsame : ¬ TierSame xs y y' := hbelow.not_tierSame
  simp only [tierDirectionSystem, List.mem_flatMap, Finset.mem_toList,
    Finset.mem_product, Prod.exists]
  exact ⟨y, y', ⟨hy, hy'⟩, by simp [tierComparisonRows, hbelow, hnsame]⟩

/-- A real solution of the tier system assigns equal potential to same-tier complexes. -/
theorem Satℝ.tierSame_potential_eq (N : Network S)
    (e : S ≃ Fin (Fintype.card S)) {xs : ℕ → Concentration S}
    {x : Fin (Fintype.card S) → ℝ} (hx : Satℝ (N.tierDirectionSystem e xs) x)
    {y y' : Complex S} (hy : y ∈ N.complexes) (hy' : y' ∈ N.complexes)
    (hsame : TierSame xs y y') :
    complexWValue (fun s => x (e s)) y = complexWValue (fun s => x (e s)) y' := by
  obtain ⟨hrow1, hrow2⟩ := N.same_rows_mem_tierDirectionSystem e xs hy hy' hsame
  have h1 := hx _ hrow1
  have h2 := hx _ hrow2
  rw [Ineq.holdsℝ, lhsℝ_tierDiffRow] at h1 h2
  norm_num at h1 h2
  linarith

/-- A real solution of the tier system strictly orders strict-lower complexes. -/
theorem Satℝ.tierBelow_potential_lt (N : Network S)
    (e : S ≃ Fin (Fintype.card S)) {xs : ℕ → Concentration S}
    {x : Fin (Fintype.card S) → ℝ} (hx : Satℝ (N.tierDirectionSystem e xs) x)
    {y y' : Complex S} (hy : y ∈ N.complexes) (hy' : y' ∈ N.complexes)
    (hbelow : TierStrictBelow xs y y') :
    complexWValue (fun s => x (e s)) y < complexWValue (fun s => x (e s)) y' := by
  have hrow := N.below_row_mem_tierDirectionSystem e xs hy hy' hbelow
  have h := hx _ hrow
  rw [Ineq.holdsℝ, lhsℝ_tierDiffRow] at h
  norm_num at h
  linarith

/-- **Finite feasibility ⇒ exact tier-direction witness.**  On a genuine tier sequence, a real
solution of the encoded finite comparison system realizes *all and only* the same-tier and
strict-lower comparisons. -/
theorem tierRealizesDirection_of_satℝ (N : Network S)
    (e : S ≃ Fin (Fintype.card S)) {xs : ℕ → Concentration S}
    (htier : N.IsTierSequence xs) {x : Fin (Fintype.card S) → ℝ}
    (hx : Satℝ (N.tierDirectionSystem e xs) x) :
    N.TierRealizesDirection xs (fun s => x (e s)) := by
  constructor
  · intro y hy y' hy'
    constructor
    · exact Satℝ.tierSame_potential_eq N e hx hy hy'
    · intro heq
      rcases htier.2.2 y hy y' hy' with hle | hrev
      · rcases hle with hbelow | hsame
        · have hlt := Satℝ.tierBelow_potential_lt N e hx hy hy' hbelow
          linarith
        · exact hsame
      · have hlt := Satℝ.tierBelow_potential_lt N e hx hy' hy hrev
        linarith
  · intro y hy y' hy'
    constructor
    · exact Satℝ.tierBelow_potential_lt N e hx hy hy'
    · intro hlt
      rcases htier.2.2 y hy y' hy' with hle | hrev
      · rcases hle with hbelow | hsame
        · exact hbelow
        · have heq := Satℝ.tierSame_potential_eq N e hx hy hy' hsame
          linarith
      · have hrevlt := Satℝ.tierBelow_potential_lt N e hx hy' hy hrev
        linarith

/-- Real feasibility of the finite tier-direction system. -/
def TierDirectionSystemFeasible (N : Network S) (xs : ℕ → Concentration S) : Prop :=
  Feasibleℝ (N.tierDirectionSystem (Fintype.equivFin S) xs)

/-- A feasible finite tier-direction system produces the witness required by the strong-endotactic
CRNT proof. -/
theorem hasTierDirectionWitness_of_systemFeasible (N : Network S)
    {xs : ℕ → Concentration S} (htier : N.IsTierSequence xs)
    (hfeas : N.TierDirectionSystemFeasible xs) : N.HasTierDirectionWitness xs := by
  obtain ⟨x, hx⟩ := hfeas
  exact ⟨fun s => x (Fintype.equivFin S s),
    N.tierRealizesDirection_of_satℝ (Fintype.equivFin S) htier hx⟩

/-- Exact finite-dimensional obligation replacing the previous opaque direction-witness premise. -/
def EveryTransversalTierDirectionSystemFeasible (N : Network S) : Prop :=
  ∀ xs : ℕ → Concentration S,
    N.IsTransversalTierSequence xs → N.TierDirectionSystemFeasible xs

/-- Finite feasibility of every transversal tier system discharges the old direction-witness
premise. -/
theorem everyDirectionWitness_of_everySystemFeasible (N : Network S)
    (h : N.EveryTransversalTierDirectionSystemFeasible) :
    N.EveryTransversalTierSequenceHasDirectionWitness := by
  intro xs htrans
  exact N.hasTierDirectionWitness_of_systemFeasible htrans.1 (h xs htrans)

/-- Consequently, standard strong endotacticity implies tier descent once the explicit finite
systems are known feasible. -/
theorem StronglyEndotacticStd.tierDescending_of_systemFeasibility {N : Network S}
    (hse : N.StronglyEndotacticStd)
    (h : N.EveryTransversalTierDirectionSystemFeasible) : N.TierDescending :=
  hse.tierDescending_of_directionWitnesses (N.everyDirectionWitness_of_everySystemFeasible h)

end Network
end CRNT
