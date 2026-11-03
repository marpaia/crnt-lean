import CRNT.Dynamics.GlobalPersistence
import CRNT.Stochastic.JumpReachabilityLift
import CRNT.Deficiency.Consistent
import CRNT.Deficiency.ConsistentWR

/-!
# Drainable and self-replicable species sets

This file formalizes the pathway definitions of Deshpande--Gopalkrishnan for chemical (integer)
reaction networks.

Their `G`-reaction pathway is a chain of *dilutions*: a reaction `a -> b` may be applied to a larger
population `a + w`, producing `b + w`.  For natural-number complexes this is exactly an enabled
count-level firing.  Accordingly `ReactionPathway n rs` threads the current population through a
finite list of enabled reactions using `jumpNextCount`.

A set `P` is self-replicable if some such pathway strictly increases every coordinate of `P`, and
it is drainable if some pathway strictly decreases every coordinate of `P`.  These are the notions
used by the minimal-critical-siphon dichotomy and the no-drainable-siphon persistence theorem.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A `G`-reaction pathway from an integer population: every reaction is enabled when it fires.
Each step is the paper's dilution of the underlying reaction by the unused population. -/
def ReactionPathway (N : Network S) : (S → ℕ) → List N.R → Prop
  | _, [] => True
  | n, r :: rs => N.Enabled n r ∧ N.ReactionPathway (N.jumpNextCount n r) rs

/-- The empty reaction list is always a pathway. -/
@[simp] theorem reactionPathway_nil (N : Network S) (n : S → ℕ) :
    N.ReactionPathway n [] :=
  trivial

/-- Unfolding a nonempty pathway. -/
@[simp] theorem reactionPathway_cons (N : Network S) (n : S → ℕ) (r : N.R)
    (rs : List N.R) :
    N.ReactionPathway n (r :: rs) ↔
      N.Enabled n r ∧ N.ReactionPathway (N.jumpNextCount n r) rs :=
  Iff.rfl

/-- A species set is self-replicable when some finite `G`-reaction pathway strictly increases all
of its coordinates. -/
def IsSelfReplicable (N : Network S) (P : Finset S) : Prop :=
  ∃ (n : S → ℕ) (rs : List N.R), N.ReactionPathway n rs ∧
    ∀ s ∈ P, n s < N.fireListTarget n rs s

/-- A species set is drainable when some finite `G`-reaction pathway strictly decreases all of its
coordinates. -/
def IsDrainable (N : Network S) (P : Finset S) : Prop :=
  ∃ (n : S → ℕ) (rs : List N.R), N.ReactionPathway n rs ∧
    ∀ s ∈ P, N.fireListTarget n rs s < n s

/-- Self-replicability is downward closed under taking subsets. -/
theorem IsSelfReplicable.mono {N : Network S} {P Q : Finset S}
    (h : N.IsSelfReplicable P) (hQP : Q ⊆ P) : N.IsSelfReplicable Q := by
  obtain ⟨n, rs, hpath, hinc⟩ := h
  exact ⟨n, rs, hpath, fun s hs => hinc s (hQP hs)⟩

/-- Drainability is downward closed under taking subsets. -/
theorem IsDrainable.mono {N : Network S} {P Q : Finset S}
    (h : N.IsDrainable P) (hQP : Q ⊆ P) : N.IsDrainable Q := by
  obtain ⟨n, rs, hpath, hdec⟩ := h
  exact ⟨n, rs, hpath, fun s hs => hdec s (hQP hs)⟩

/-! ## Pathways as finite stoichiometric sums -/

/-- A conservative count buffer that contains every source complex in a reaction list, added
coordinatewise.  Starting above this budget is enough to execute the whole list: products can only
add additional nonnegative counts. -/
def pathwaySourceBudget (N : Network S) : List N.R → S → ℕ
  | [], _ => 0
  | r :: rs, s => (N.reaction r).source s + N.pathwaySourceBudget rs s

/-- Real stoichiometric displacement of a reaction list. -/
def pathwayNetChange (N : Network S) : List N.R → S → ℝ
  | [], _ => 0
  | r :: rs, s => N.reactionVector r s + N.pathwayNetChange rs s

/-- Any reaction list can be executed from a sufficiently large integer population.  The explicit
source budget is intentionally crude but makes the dilution semantics constructive. -/
theorem reactionPathway_of_sourceBudget_le (N : Network S) :
    ∀ (rs : List N.R) (n : S → ℕ),
      (∀ s, N.pathwaySourceBudget rs s ≤ n s) → N.ReactionPathway n rs
  | [], n, _ => by simp
  | r :: rs, n, hbudget => by
      rw [reactionPathway_cons]
      have hen : N.Enabled n r := by
        intro s
        have h := hbudget s
        simp only [pathwaySourceBudget] at h
        omega
      refine ⟨hen, ?_⟩
      apply N.reactionPathway_of_sourceBudget_le rs (N.jumpNextCount n r)
      intro s
      have h := hbudget s
      have hs := hen s
      simp only [pathwaySourceBudget] at h
      simp only [jumpNextCount]
      omega

/-- In particular, the source budget itself executes the list. -/
theorem reactionPathway_sourceBudget (N : Network S) (rs : List N.R) :
    N.ReactionPathway (N.pathwaySourceBudget rs) rs :=
  N.reactionPathway_of_sourceBudget_le rs (N.pathwaySourceBudget rs) (fun _ => le_rfl)

/-- One enabled firing changes the real-valued count by exactly the reaction vector. -/
theorem jumpNextCount_sub_eq_reactionVector (N : Network S) {n : S → ℕ} {r : N.R}
    (hen : N.Enabled n r) (s : S) :
    ((N.jumpNextCount n r s : ℕ) : ℝ) - (n s : ℝ) = N.reactionVector r s := by
  simp only [jumpNextCount, reactionVector_apply]
  rw [Nat.cast_add, Nat.cast_sub (hen s)]
  push_cast
  ring

/-- Along an enabled reaction pathway, the final-minus-initial population is exactly the sum of
reaction vectors of the fired list.  This is the formal version of the paper's observation that a
reaction-pathway displacement lies in the positive stoichiometric cone. -/
theorem fireListTarget_sub_eq_pathwayNetChange (N : Network S) :
    ∀ {n : S → ℕ} {rs : List N.R}, N.ReactionPathway n rs → ∀ s : S,
      ((N.fireListTarget n rs s : ℕ) : ℝ) - (n s : ℝ) = N.pathwayNetChange rs s
  | n, [], _ => by
      intro s
      simp [fireListTarget, pathwayNetChange]
  | n, r :: rs, hpath => by
      intro s
      obtain ⟨hen, htail⟩ := hpath
      simp only [fireListTarget, pathwayNetChange]
      have hhead := N.jumpNextCount_sub_eq_reactionVector hen s
      have hrest := N.fireListTarget_sub_eq_pathwayNetChange htail s
      linarith

/-- A self-replicability witness therefore supplies a finite nonnegative stoichiometric sum that is
strictly positive on every species of `P`. -/
theorem IsSelfReplicable.exists_pathwayNetChange_pos {N : Network S} {P : Finset S}
    (h : N.IsSelfReplicable P) :
    ∃ rs : List N.R, ∀ s ∈ P, 0 < N.pathwayNetChange rs s := by
  obtain ⟨n, rs, hpath, hinc⟩ := h
  refine ⟨rs, ?_⟩
  intro s hs
  have hnet := N.fireListTarget_sub_eq_pathwayNetChange hpath s
  have hlt := hinc s hs
  have hltR : (n s : ℝ) < (N.fireListTarget n rs s : ℝ) := by exact_mod_cast hlt
  linarith

/-- A drainability witness supplies a finite stoichiometric sum that is strictly negative on every
species of `P`. -/
theorem IsDrainable.exists_pathwayNetChange_neg {N : Network S} {P : Finset S}
    (h : N.IsDrainable P) :
    ∃ rs : List N.R, ∀ s ∈ P, N.pathwayNetChange rs s < 0 := by
  obtain ⟨n, rs, hpath, hdec⟩ := h
  refine ⟨rs, ?_⟩
  intro s hs
  have hnet := N.fireListTarget_sub_eq_pathwayNetChange hpath s
  have hlt := hdec s hs
  have hltR : (N.fireListTarget n rs s : ℝ) < (n s : ℝ) := by exact_mod_cast hlt
  linarith

/-- Conversely, a reaction list whose net stoichiometric displacement is positive on `P` is an
explicit self-replication pathway once started from its source budget. -/
theorem isSelfReplicable_of_pathwayNetChange_pos (N : Network S) {P : Finset S} {rs : List N.R}
    (hpos : ∀ s ∈ P, 0 < N.pathwayNetChange rs s) : N.IsSelfReplicable P := by
  let n := N.pathwaySourceBudget rs
  have hpath : N.ReactionPathway n rs := N.reactionPathway_sourceBudget rs
  refine ⟨n, rs, hpath, ?_⟩
  intro s hs
  have hnet := N.fireListTarget_sub_eq_pathwayNetChange hpath s
  have hp := hpos s hs
  norm_cast
  by_contra hnot
  have hle : N.fireListTarget n rs s ≤ n s := Nat.le_of_not_gt hnot
  have hleR : (N.fireListTarget n rs s : ℝ) ≤ (n s : ℝ) := by exact_mod_cast hle
  linarith

/-- Conversely, a reaction list whose net displacement is negative on `P` witnesses drainability. -/
theorem isDrainable_of_pathwayNetChange_neg (N : Network S) {P : Finset S} {rs : List N.R}
    (hneg : ∀ s ∈ P, N.pathwayNetChange rs s < 0) : N.IsDrainable P := by
  let n := N.pathwaySourceBudget rs
  have hpath : N.ReactionPathway n rs := N.reactionPathway_sourceBudget rs
  refine ⟨n, rs, hpath, ?_⟩
  intro s hs
  have hnet := N.fireListTarget_sub_eq_pathwayNetChange hpath s
  have hn := hneg s hs
  norm_cast
  by_contra hnot
  have hle : (n s) ≤ N.fireListTarget n rs s := Nat.le_of_not_gt hnot
  have hleR : (n s : ℝ) ≤ (N.fireListTarget n rs s : ℝ) := by exact_mod_cast hle
  linarith

/-- Exact finite-list characterization of self-replicability. -/
theorem isSelfReplicable_iff_exists_pathwayNetChange_pos (N : Network S) (P : Finset S) :
    N.IsSelfReplicable P ↔ ∃ rs : List N.R, ∀ s ∈ P, 0 < N.pathwayNetChange rs s :=
  ⟨IsSelfReplicable.exists_pathwayNetChange_pos,
    fun h => by obtain ⟨rs, hrs⟩ := h; exact N.isSelfReplicable_of_pathwayNetChange_pos hrs⟩

/-- Exact finite-list characterization of drainability. -/
theorem isDrainable_iff_exists_pathwayNetChange_neg (N : Network S) (P : Finset S) :
    N.IsDrainable P ↔ ∃ rs : List N.R, ∀ s ∈ P, N.pathwayNetChange rs s < 0 :=
  ⟨IsDrainable.exists_pathwayNetChange_neg,
    fun h => by obtain ⟨rs, hrs⟩ := h; exact N.isDrainable_of_pathwayNetChange_neg hrs⟩

/-! ## Continuous flux cone and pathway realization

The paper alternates between finite diluted reaction paths and nonnegative stoichiometric fluxes.
The former are combinatorial/integer witnesses; the latter are the natural linear-algebraic form of
the minimal-critical-siphon theorem.  Keeping both forms explicit avoids conflating the finite
rational-realization step with the convex-algebra argument.
-/


/-! ### Canonical integer-flux realization

A finite reaction list carries no information beyond the multiplicity with which each reaction is
used as far as net stoichiometric displacement is concerned.  We therefore make the integer cone
explicit.  This removes list ordering from the algebraic part of drainability/self-replication and
isolates the only genuinely analytic bridge later: strict real cone feasibility implies strict
integer cone feasibility for an integer matrix.
-/

/-- Net displacement of a natural-number reaction multiplicity vector. -/
def naturalFluxNetChange (N : Network S) (m : N.R → ℕ) (s : S) : ℝ :=
  ∑ r : N.R, (m r : ℝ) * N.reactionVector r s

/-- Canonical reaction list realizing a natural multiplicity vector. -/
noncomputable def naturalFluxPath (N : Network S) (m : N.R → ℕ) : List N.R :=
  (Finset.univ.toList).flatMap fun r => List.replicate (m r) r

/-- Net change is additive under concatenation of reaction lists. -/
theorem pathwayNetChange_append (N : Network S) (xs ys : List N.R) (s : S) :
    N.pathwayNetChange (xs ++ ys) s =
      N.pathwayNetChange xs s + N.pathwayNetChange ys s := by
  induction xs with
  | nil => simp [pathwayNetChange]
  | cons r rs ih =>
      simp [pathwayNetChange, ih, add_assoc]

/-- Repeating one reaction `k` times contributes `k` times its reaction vector. -/
theorem pathwayNetChange_replicate (N : Network S) (k : ℕ) (r : N.R) (s : S) :
    N.pathwayNetChange (List.replicate k r) s = (k : ℝ) * N.reactionVector r s := by
  induction k with
  | zero => simp [pathwayNetChange]
  | succ k ih =>
      rw [List.replicate_succ]
      simp only [pathwayNetChange, ih, reactionVector_apply, Nat.cast_succ]
      ring

/-- Flattening repeated reactions over a list sums their multiplicity-weighted reaction vectors. -/
theorem pathwayNetChange_flatMap_replicate (N : Network S) (m : N.R → ℕ)
    (L : List N.R) (s : S) :
    N.pathwayNetChange (L.flatMap (fun r => List.replicate (m r) r)) s =
      (L.map (fun r => (m r : ℝ) * N.reactionVector r s)).sum := by
  induction L with
  | nil => simp [pathwayNetChange]
  | cons r rs ih =>
      rw [List.flatMap_cons, N.pathwayNetChange_append,
        N.pathwayNetChange_replicate, ih]
      simp

/-- The canonical multiplicity path has exactly the natural-flux displacement. -/
theorem pathwayNetChange_naturalFluxPath (N : Network S) (m : N.R → ℕ) (s : S) :
    N.pathwayNetChange (N.naturalFluxPath m) s = N.naturalFluxNetChange m s := by
  rw [naturalFluxPath, N.pathwayNetChange_flatMap_replicate]
  simp [naturalFluxNetChange]


/-- A reaction list's net change is the reaction-vector sum weighted by list multiplicities. -/
theorem pathwayNetChange_eq_sum_count (N : Network S) (rs : List N.R) (s : S) :
    N.pathwayNetChange rs s =
      ∑ r : N.R, (rs.count r : ℝ) * N.reactionVector r s := by
  induction rs with
  | nil => simp [pathwayNetChange]
  | cons q rs ih =>
      rw [pathwayNetChange, ih]
      have hindicator :
          (∑ r : N.R, (if q = r then (1 : ℝ) else 0) * N.reactionVector r s) =
            N.reactionVector q s := by
        simp
      calc
        N.reactionVector q s +
              ∑ r : N.R, (rs.count r : ℝ) * N.reactionVector r s
            = (∑ r : N.R, (if q = r then (1 : ℝ) else 0) * N.reactionVector r s) +
                ∑ r : N.R, (rs.count r : ℝ) * N.reactionVector r s := by rw [hindicator]
        _ = ∑ r : N.R,
              ((if q = r then (1 : ℝ) else 0) + (rs.count r : ℝ)) *
                N.reactionVector r s := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro r _
              ring
        _ = ∑ r : N.R, ((q :: rs).count r : ℝ) * N.reactionVector r s := by
              apply Finset.sum_congr rfl
              intro r _
              by_cases hqr : q = r
              · subst r
                simp [List.count_cons, add_comm]
              · simp [hqr]

/-- Integer-cone witness for self-replication. -/
def IsNaturalFluxSelfReplicable (N : Network S) (P : Finset S) : Prop :=
  ∃ m : N.R → ℕ, ∀ s ∈ P, 0 < N.naturalFluxNetChange m s

/-- Integer-cone witness for drainability. -/
def IsNaturalFluxDrainable (N : Network S) (P : Finset S) : Prop :=
  ∃ m : N.R → ℕ, ∀ s ∈ P, N.naturalFluxNetChange m s < 0

/-- Natural-flux positivity is exactly combinatorial self-replicability. -/
theorem isSelfReplicable_iff_naturalFlux (N : Network S) (P : Finset S) :
    N.IsSelfReplicable P ↔ N.IsNaturalFluxSelfReplicable P := by
  rw [N.isSelfReplicable_iff_exists_pathwayNetChange_pos]
  constructor
  · rintro ⟨rs, hrs⟩
    let m : N.R → ℕ := fun r => rs.count r
    refine ⟨m, ?_⟩
    intro s hs
    have hcount : N.naturalFluxNetChange m s = N.pathwayNetChange rs s := by
      rw [N.pathwayNetChange_eq_sum_count]
      rfl
    rw [hcount]
    exact hrs s hs
  · rintro ⟨m, hm⟩
    refine ⟨N.naturalFluxPath m, ?_⟩
    intro s hs
    rw [N.pathwayNetChange_naturalFluxPath]
    exact hm s hs

/-- Natural-flux negativity is exactly combinatorial drainability. -/
theorem isDrainable_iff_naturalFlux (N : Network S) (P : Finset S) :
    N.IsDrainable P ↔ N.IsNaturalFluxDrainable P := by
  rw [N.isDrainable_iff_exists_pathwayNetChange_neg]
  constructor
  · rintro ⟨rs, hrs⟩
    let m : N.R → ℕ := fun r => rs.count r
    refine ⟨m, ?_⟩
    intro s hs
    have hcount : N.naturalFluxNetChange m s = N.pathwayNetChange rs s := by
      rw [N.pathwayNetChange_eq_sum_count]
      rfl
    rw [hcount]
    exact hrs s hs
  · rintro ⟨m, hm⟩
    refine ⟨N.naturalFluxPath m, ?_⟩
    intro s hs
    rw [N.pathwayNetChange_naturalFluxPath]
    exact hm s hs

/-- Net stoichiometric displacement generated by a real reaction flux. -/
def fluxNetChange (N : Network S) (v : N.R → ℝ) (s : S) : ℝ :=
  ∑ r, v r * N.reactionVector r s

/-- A nonnegative real reaction flux. -/
def IsNonnegativeFlux (N : Network S) (v : N.R → ℝ) : Prop :=
  ∀ r, 0 ≤ v r

/-- Flux-cone form of self-replicability on `P`. -/
def IsFluxSelfReplicable (N : Network S) (P : Finset S) : Prop :=
  ∃ v : N.R → ℝ, N.IsNonnegativeFlux v ∧
    ∀ s ∈ P, 0 < N.fluxNetChange v s

/-- Flux-cone form of drainability on `P`. -/
def IsFluxDrainable (N : Network S) (P : Finset S) : Prop :=
  ∃ v : N.R → ℝ, N.IsNonnegativeFlux v ∧
    ∀ s ∈ P, N.fluxNetChange v s < 0

/-- Reaction multiplicities of a finite path, represented as a real nonnegative flux.  This
recursive definition avoids quotienting lists by permutation and makes the path-to-flux theorem
purely structural. -/
def pathwayFlux (N : Network S) : List N.R → N.R → ℝ
  | [], _ => 0
  | r :: rs, q => (if q = r then 1 else 0) + N.pathwayFlux rs q

@[simp] theorem pathwayFlux_nil (N : Network S) (q : N.R) :
    N.pathwayFlux [] q = 0 := rfl

@[simp] theorem pathwayFlux_cons (N : Network S) (r : N.R) (rs : List N.R) (q : N.R) :
    N.pathwayFlux (r :: rs) q = (if q = r then 1 else 0) + N.pathwayFlux rs q := rfl

/-- A finite path gives a nonnegative real reaction flux. -/
theorem pathwayFlux_nonnegative (N : Network S) (rs : List N.R) :
    N.IsNonnegativeFlux (N.pathwayFlux rs) := by
  intro q
  induction rs with
  | nil => simp [pathwayFlux]
  | cons r rs ih =>
      simp only [pathwayFlux]
      positivity

/-- The flux generated by a reaction list has exactly the list's stoichiometric net change. -/
theorem fluxNetChange_pathwayFlux (N : Network S) (rs : List N.R) (s : S) :
    N.fluxNetChange (N.pathwayFlux rs) s = N.pathwayNetChange rs s := by
  induction rs with
  | nil => simp [fluxNetChange, pathwayFlux, pathwayNetChange]
  | cons r rs ih =>
      simp only [fluxNetChange, pathwayFlux, pathwayNetChange, add_mul]
      rw [Finset.sum_add_distrib]
      have hindicator :
          (∑ q : N.R, (if q = r then (1 : ℝ) else 0) * N.reactionVector q s) =
            N.reactionVector r s := by
        simp
      rw [hindicator]
      have htail :
          (∑ q : N.R, N.pathwayFlux rs q * N.reactionVector q s) =
            N.pathwayNetChange rs s := ih
      rw [htail]

/-- Every combinatorial self-replication pathway yields a nonnegative flux-cone witness. -/
theorem IsSelfReplicable.toFlux {N : Network S} {P : Finset S}
    (h : N.IsSelfReplicable P) : N.IsFluxSelfReplicable P := by
  obtain ⟨rs, hpos⟩ := h.exists_pathwayNetChange_pos
  refine ⟨N.pathwayFlux rs, N.pathwayFlux_nonnegative rs, ?_⟩
  intro s hs
  simpa [N.fluxNetChange_pathwayFlux rs s] using hpos s hs

/-- Every combinatorial drainability pathway yields a nonnegative flux-cone witness. -/
theorem IsDrainable.toFlux {N : Network S} {P : Finset S}
    (h : N.IsDrainable P) : N.IsFluxDrainable P := by
  obtain ⟨rs, hneg⟩ := h.exists_pathwayNetChange_neg
  refine ⟨N.pathwayFlux rs, N.pathwayFlux_nonnegative rs, ?_⟩
  intro s hs
  simpa [N.fluxNetChange_pathwayFlux rs s] using hneg s hs

/-- Strict sign realization principle for the stoichiometric cone.  Mathematically this is the
finite-dimensional rational-density step: because the inequalities are strict and the reaction
vectors have integer coefficients, a nonnegative real flux with a strict sign pattern can be
approximated by a nonnegative rational flux, cleared to integer multiplicities, and then executed
from `pathwaySourceBudget`.  It is isolated as a reusable property because the density/denominator
bookkeeping is independent of CRNT. -/
def FluxSignRealizable (N : Network S) : Prop :=
  (∀ P : Finset S, N.IsFluxSelfReplicable P → N.IsSelfReplicable P) ∧
  (∀ P : Finset S, N.IsFluxDrainable P → N.IsDrainable P)

/-- With the rational-realization lemma available, the pathway and flux definitions of
self-replicability coincide. -/
theorem isSelfReplicable_iff_flux_of_realizable (N : Network S) (hreal : N.FluxSignRealizable)
    (P : Finset S) : N.IsSelfReplicable P ↔ N.IsFluxSelfReplicable P :=
  ⟨IsSelfReplicable.toFlux, hreal.1 P⟩

/-- With the rational-realization lemma available, the pathway and flux definitions of drainability
coincide. -/
theorem isDrainable_iff_flux_of_realizable (N : Network S) (hreal : N.FluxSignRealizable)
    (P : Finset S) : N.IsDrainable P ↔ N.IsFluxDrainable P :=
  ⟨IsDrainable.toFlux, hreal.2 P⟩

/-- **Consistency reverses a strict positive flux direction.**  If the reaction vectors admit a
strictly positive cancelling flux `α` and a nonnegative flux `v` moves all species in `P` strictly
up, then a sufficiently large multiple of `α` minus `v` is still nonnegative and moves all species
in `P` strictly down.  This is the continuous-flux algebra behind the non-autocatalytic
weakly-reversible corollary. -/
theorem IsFluxSelfReplicable.toFluxDrainable_of_consistent {N : Network S} {P : Finset S}
    (hcons : N.IsConsistent) (h : N.IsFluxSelfReplicable P) : N.IsFluxDrainable P := by
  obtain ⟨α, hαpos, hαzero⟩ := hcons
  obtain ⟨v, hvnn, hvpos⟩ := h
  let C : ℝ := (∑ r : N.R, v r / α r) + 1
  have hratio_nonneg : ∀ r : N.R, 0 ≤ v r / α r :=
    fun r => div_nonneg (hvnn r) (hαpos r).le
  have hCdom : ∀ r : N.R, v r ≤ C * α r := by
    intro r
    have hsingle : v r / α r ≤ ∑ q : N.R, v q / α q := by
      exact Finset.single_le_sum (fun q _ => hratio_nonneg q) (Finset.mem_univ r)
    have hltC : v r / α r < C := by
      dsimp [C]
      linarith
    exact (div_lt_iff₀ (hαpos r)).mp hltC |>.le
  let u : N.R → ℝ := fun r => C * α r - v r
  refine ⟨u, ?_, ?_⟩
  · intro r
    dsimp [u]
    exact sub_nonneg.mpr (hCdom r)
  · intro s hs
    have hαs : ∑ r : N.R, α r * N.reactionVector r s = 0 := by
      have hz := congrFun hαzero s
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hz
    have hu : N.fluxNetChange u s = -(N.fluxNetChange v s) := by
      simp only [fluxNetChange, u]
      calc
        (∑ r : N.R, (C * α r - v r) * N.reactionVector r s)
            = C * (∑ r : N.R, α r * N.reactionVector r s) -
                (∑ r : N.R, v r * N.reactionVector r s) := by
                  simp only [sub_mul, mul_assoc]
                  rw [Finset.sum_sub_distrib, Finset.mul_sum]
        _ = -(N.fluxNetChange v s) := by rw [hαs, mul_zero, zero_sub]; rfl
    rw [hu]
    exact neg_lt_zero.mpr (hvpos s hs)

/-- Consistency also reverses a strict negative flux direction to a strict positive one. -/
theorem IsFluxDrainable.toFluxSelfReplicable_of_consistent {N : Network S} {P : Finset S}
    (hcons : N.IsConsistent) (h : N.IsFluxDrainable P) : N.IsFluxSelfReplicable P := by
  obtain ⟨α, hαpos, hαzero⟩ := hcons
  obtain ⟨v, hvnn, hvneg⟩ := h
  let C : ℝ := (∑ r : N.R, v r / α r) + 1
  have hratio_nonneg : ∀ r : N.R, 0 ≤ v r / α r :=
    fun r => div_nonneg (hvnn r) (hαpos r).le
  have hCdom : ∀ r : N.R, v r ≤ C * α r := by
    intro r
    have hsingle : v r / α r ≤ ∑ q : N.R, v q / α q := by
      exact Finset.single_le_sum (fun q _ => hratio_nonneg q) (Finset.mem_univ r)
    have hltC : v r / α r < C := by
      dsimp [C]
      linarith
    exact ((div_lt_iff₀ (hαpos r)).mp hltC).le
  let u : N.R → ℝ := fun r => C * α r - v r
  refine ⟨u, ?_, ?_⟩
  · intro r
    exact sub_nonneg.mpr (hCdom r)
  · intro s hs
    have hαs : ∑ r : N.R, α r * N.reactionVector r s = 0 := by
      have hz := congrFun hαzero s
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hz
    have hu : N.fluxNetChange u s = -(N.fluxNetChange v s) := by
      simp only [fluxNetChange, u]
      calc
        (∑ r : N.R, (C * α r - v r) * N.reactionVector r s)
            = C * (∑ r : N.R, α r * N.reactionVector r s) -
                (∑ r : N.R, v r * N.reactionVector r s) := by
                  simp only [sub_mul, mul_assoc]
                  rw [Finset.sum_sub_distrib, Finset.mul_sum]
        _ = -(N.fluxNetChange v s) := by rw [hαs, mul_zero, zero_sub]; rfl
    rw [hu]
    exact neg_pos.mpr (hvneg s hs)

/-- On a consistent network the two strict-sign flux notions are equivalent. -/
theorem fluxSelfReplicable_iff_fluxDrainable_of_consistent (N : Network S)
    (hcons : N.IsConsistent) (P : Finset S) :
    N.IsFluxSelfReplicable P ↔ N.IsFluxDrainable P :=
  ⟨fun h => h.toFluxDrainable_of_consistent hcons,
    fun h => h.toFluxSelfReplicable_of_consistent hcons⟩

/-- The same reversal specialized to weakly reversible networks, whose consistency is already
proved elsewhere in the library. -/
theorem IsFluxSelfReplicable.toFluxDrainable_of_weaklyReversible {N : Network S} {P : Finset S}
    (hwr : N.WeaklyReversible) (h : N.IsFluxSelfReplicable P) : N.IsFluxDrainable P :=
  h.toFluxDrainable_of_consistent (N.isConsistent_of_weaklyReversible hwr)

/-- Once strict real fluxes are rationally/integrally realizable, a self-replicable set in a
consistent network is drainable in the original pathway sense. -/
theorem IsSelfReplicable.toDrainable_of_consistent {N : Network S} {P : Finset S}
    (hreal : N.FluxSignRealizable) (hcons : N.IsConsistent) (h : N.IsSelfReplicable P) :
    N.IsDrainable P :=
  hreal.2 P (h.toFlux.toFluxDrainable_of_consistent hcons)

/-- Weakly reversible specialization of the preceding pathway theorem. -/
theorem IsSelfReplicable.toDrainable_of_weaklyReversible {N : Network S} {P : Finset S}
    (hreal : N.FluxSignRealizable) (hwr : N.WeaklyReversible) (h : N.IsSelfReplicable P) :
    N.IsDrainable P :=
  h.toDrainable_of_consistent hreal (N.isConsistent_of_weaklyReversible hwr)

/-- With strict-sign realization, drainability and self-replicability coincide on a
consistent network. -/
theorem selfReplicable_iff_drainable_of_consistent (N : Network S)
    (hreal : N.FluxSignRealizable) (hcons : N.IsConsistent) (P : Finset S) :
    N.IsSelfReplicable P ↔ N.IsDrainable P := by
  rw [N.isSelfReplicable_iff_flux_of_realizable hreal P,
    N.isDrainable_iff_flux_of_realizable hreal P]
  exact N.fluxSelfReplicable_iff_fluxDrainable_of_consistent hcons P

/-- Weakly reversible specialization: after the finite strict-flux realization lemma, drainable and
self-replicable sets coincide. -/
theorem selfReplicable_iff_drainable_of_weaklyReversible (N : Network S)
    (hreal : N.FluxSignRealizable) (hwr : N.WeaklyReversible) (P : Finset S) :
    N.IsSelfReplicable P ↔ N.IsDrainable P :=
  N.selfReplicable_iff_drainable_of_consistent hreal (N.isConsistent_of_weaklyReversible hwr) P

/-- A self-replicable siphon. -/
def IsSelfReplicableSiphon (N : Network S) (P : Finset S) : Prop :=
  P.Nonempty ∧ N.IsSiphon P ∧ N.IsSelfReplicable P

/-- A drainable siphon. -/
def IsDrainableSiphon (N : Network S) (P : Finset S) : Prop :=
  P.Nonempty ∧ N.IsSiphon P ∧ N.IsDrainable P

/-- The network contains no drainable siphon. -/
def HasNoDrainableSiphon (N : Network S) : Prop :=
  ∀ P : Finset S, ¬ N.IsDrainableSiphon P

/-- The network contains no self-replicable siphon (the non-autocatalytic siphon condition). -/
def HasNoSelfReplicableSiphon (N : Network S) : Prop :=
  ∀ P : Finset S, ¬ N.IsSelfReplicableSiphon P

/-- In a weakly reversible network, non-autocatalytic siphons imply no drainable siphons
once the strict flux-to-path realization lemma is available. -/
theorem hasNoDrainableSiphon_of_weaklyReversible_hasNoSelfReplicableSiphon
    (N : Network S) (hreal : N.FluxSignRealizable) (hwr : N.WeaklyReversible)
    (hnosr : N.HasNoSelfReplicableSiphon) : N.HasNoDrainableSiphon := by
  intro P hdr
  apply hnosr P
  refine ⟨hdr.1, hdr.2.1, ?_⟩
  exact (N.selfReplicable_iff_drainable_of_weaklyReversible hreal hwr P).mpr hdr.2.2

/-- A minimal critical siphon, minimal among nonempty critical siphons by inclusion. -/
def IsMinimalCriticalSiphon (N : Network S) (P : Finset S) : Prop :=
  N.IsCriticalSiphon P ∧
    ∀ Q : Finset S, Q ⊆ P → Q ≠ P → Q.Nonempty → ¬ N.IsCriticalSiphon Q

/-- Every critical siphon contains an inclusion-minimal critical siphon.  This is purely finite:
choose a critical subset of least cardinality inside `P`; any proper nonempty critical subset would
have smaller cardinality. -/
theorem exists_minimalCriticalSiphon_subset (N : Network S) {P : Finset S}
    (hP : N.IsCriticalSiphon P) :
    ∃ Q : Finset S, Q ⊆ P ∧ N.IsMinimalCriticalSiphon Q := by
  classical
  let C : Finset (Finset S) := P.powerset.filter (fun Q => N.IsCriticalSiphon Q)
  have hPC : P ∈ C := by
    simp [C, hP]
  have hCne : C.Nonempty := ⟨P, hPC⟩
  let cards : Finset ℕ := C.image Finset.card
  have hcardsne : cards.Nonempty := hCne.image Finset.card
  let m : ℕ := cards.min' hcardsne
  have hm : m ∈ cards := by
    dsimp [m]
    exact Finset.min'_mem cards hcardsne
  obtain ⟨Q, hQC, hQcard⟩ := Finset.mem_image.mp hm
  have hQpow : Q ∈ P.powerset := (Finset.mem_filter.mp hQC).1
  have hQcrit : N.IsCriticalSiphon Q := (Finset.mem_filter.mp hQC).2
  refine ⟨Q, Finset.mem_powerset.mp hQpow, hQcrit, ?_⟩
  intro R hRQ hRneQ _hRne hRcrit
  have hRP : R ⊆ P := hRQ.trans (Finset.mem_powerset.mp hQpow)
  have hRC : R ∈ C := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_powerset.mpr hRP, hRcrit⟩
  have hRcardmem : R.card ∈ cards := Finset.mem_image.mpr ⟨R, hRC, rfl⟩
  have hmle : m ≤ R.card := by
    dsimp [m]
    exact Finset.min'_le cards R.card hRcardmem
  have hlt : R.card < Q.card := Finset.card_lt_card (lt_of_le_of_ne hRQ hRneQ)
  rw [hQcard] at hlt
  omega


/-! ## From the minimal-critical dichotomy to exclusion of critical siphons -/

/-- **No drainable siphon + the minimal-critical dichotomy excludes all critical siphons in a
consistent network.**  Any critical siphon contains a minimal critical siphon.  The dichotomy makes
that minimal siphon drainable or self-replicable; consistency plus strict flux realization reverses
the self-replicable case to a drainable one.  Either branch contradicts `HasNoDrainableSiphon`.

This theorem is intentionally parameterized by the finite-pathway dichotomy rather than importing
the research-frontier module. -/
theorem hasNoCriticalSiphon_of_noDrainable_of_minimalCriticalDichotomy
    (N : Network S) (hreal : N.FluxSignRealizable) (hcons : N.IsConsistent)
    (hdich : ∀ P : Finset S, N.IsMinimalCriticalSiphon P →
      N.IsDrainable P ∨ N.IsSelfReplicable P)
    (hnd : N.HasNoDrainableSiphon) : N.HasNoCriticalSiphon := by
  intro P hcrit
  obtain ⟨Q, _hQP, hQmin⟩ := N.exists_minimalCriticalSiphon_subset hcrit
  have hQcrit : N.IsCriticalSiphon Q := hQmin.1
  have hQsiph : N.IsSiphon Q := hQcrit.2.1
  have hQne : Q.Nonempty := hQcrit.1
  rcases hdich Q hQmin with hd | hs
  · exact hnd Q ⟨hQne, hQsiph, hd⟩
  · have hd : N.IsDrainable Q := hs.toDrainable_of_consistent hreal hcons
    exact hnd Q ⟨hQne, hQsiph, hd⟩

/-- Weakly reversible specialization, using the library's proved
`WeaklyReversible → IsConsistent` theorem. -/
theorem hasNoCriticalSiphon_of_weaklyReversible_noDrainable_of_minimalCriticalDichotomy
    (N : Network S) (hreal : N.FluxSignRealizable) (hwr : N.WeaklyReversible)
    (hdich : ∀ P : Finset S, N.IsMinimalCriticalSiphon P →
      N.IsDrainable P ∨ N.IsSelfReplicable P)
    (hnd : N.HasNoDrainableSiphon) : N.HasNoCriticalSiphon :=
  N.hasNoCriticalSiphon_of_noDrainable_of_minimalCriticalDichotomy hreal
    (N.isConsistent_of_weaklyReversible hwr) hdich hnd


/-! ## Critical-siphon elimination from the dichotomy

The published minimal-critical-siphon dichotomy becomes particularly strong on weakly reversible
networks.  Weak reversibility supplies consistency; consistency reverses every strict-sign flux;
and `FluxSignRealizable` turns that reversed flux back into a finite pathway.  Consequently a
minimal critical siphon is drainable iff it is self-replicable.  If either type is globally
forbidden, no critical siphon can exist at all.

This section is intentionally phrased with the dichotomy as an explicit hypothesis.  The remaining
matrix/sign theorem proving that dichotomy belongs to the research frontier; all CRNT consequences
of it are discharged here.
-/

/-- Raw proposition form of the Deshpande--Gopalkrishnan minimal-critical-siphon dichotomy. -/
def MinimalCriticalSiphonDichotomy (N : Network S) : Prop :=
  ∀ P : Finset S, N.IsMinimalCriticalSiphon P →
    N.IsDrainable P ∨ N.IsSelfReplicable P

/-- Flux-cone form of the same dichotomy, before rational/integer pathway realization. -/
def MinimalCriticalSiphonFluxDichotomy (N : Network S) : Prop :=
  ∀ P : Finset S, N.IsMinimalCriticalSiphon P →
    N.IsFluxDrainable P ∨ N.IsFluxSelfReplicable P

/-- Flux-level dichotomy plus strict-sign realization gives the original finite-pathway theorem. -/
theorem minimalCriticalSiphonDichotomy_of_flux (N : Network S)
    (hflux : N.MinimalCriticalSiphonFluxDichotomy)
    (hreal : N.FluxSignRealizable) : N.MinimalCriticalSiphonDichotomy := by
  intro P hmin
  rcases hflux P hmin with hd | hs
  · exact Or.inl (hreal.2 P hd)
  · exact Or.inr (hreal.1 P hs)

/-- On a weakly reversible network, a minimal critical siphon satisfying the dichotomy is actually
both drainable and self-replicable (once strict real flux signs are pathway-realizable). -/
theorem IsMinimalCriticalSiphon.drainable_and_selfReplicable_of_weaklyReversible
    {N : Network S} {P : Finset S} (hmin : N.IsMinimalCriticalSiphon P)
    (hreal : N.FluxSignRealizable) (hwr : N.WeaklyReversible)
    (hdich : N.MinimalCriticalSiphonDichotomy) :
    N.IsDrainable P ∧ N.IsSelfReplicable P := by
  have heq := N.selfReplicable_iff_drainable_of_weaklyReversible hreal hwr P
  rcases hdich P hmin with hd | hs
  · exact ⟨hd, heq.mpr hd⟩
  · exact ⟨heq.mp hs, hs⟩

/-- **Non-autocatalytic weakly reversible networks have no critical siphons**, modulo exactly the
finite sign theorem (`MinimalCriticalSiphonDichotomy`) and strict flux realization.  Any hypothetical
critical siphon contains a minimal critical one; the preceding theorem makes that minimal siphon
self-replicable, contradicting `HasNoSelfReplicableSiphon`. -/
theorem hasNoCriticalSiphon_of_weaklyReversible_hasNoSelfReplicableSiphon
    (N : Network S) (hreal : N.FluxSignRealizable) (hdich : N.MinimalCriticalSiphonDichotomy)
    (hwr : N.WeaklyReversible) (hnosr : N.HasNoSelfReplicableSiphon) :
    N.HasNoCriticalSiphon := by
  intro P hPcrit
  obtain ⟨Q, hQP, hQmin⟩ := N.exists_minimalCriticalSiphon_subset hPcrit
  have hQboth := hQmin.drainable_and_selfReplicable_of_weaklyReversible hreal hwr hdich
  exact hnosr Q ⟨hQmin.1.1, hQmin.1.2.1, hQboth.2⟩

/-- The dual statement: on a weakly reversible network, forbidding drainable siphons also excludes
all critical siphons once the minimal-critical dichotomy and flux realization are available. -/
theorem hasNoCriticalSiphon_of_weaklyReversible_hasNoDrainableSiphon
    (N : Network S) (hreal : N.FluxSignRealizable) (hdich : N.MinimalCriticalSiphonDichotomy)
    (hwr : N.WeaklyReversible) (hnd : N.HasNoDrainableSiphon) :
    N.HasNoCriticalSiphon := by
  intro P hPcrit
  obtain ⟨Q, hQP, hQmin⟩ := N.exists_minimalCriticalSiphon_subset hPcrit
  have hQboth := hQmin.drainable_and_selfReplicable_of_weaklyReversible hreal hwr hdich
  exact hnd Q ⟨hQmin.1.1, hQmin.1.2.1, hQboth.1⟩

/-- Under the same two finite structural inputs, a non-autocatalytic weakly reversible network
inherits the repository's fully proved global omega-limit boundary-exclusion theorem. -/
theorem structurallyBoundaryOmegaExcluded_of_weaklyReversible_hasNoSelfReplicableSiphon
    (N : Network S) (hreal : N.FluxSignRealizable) (hdich : N.MinimalCriticalSiphonDichotomy)
    (hwr : N.WeaklyReversible) (hnosr : N.HasNoSelfReplicableSiphon) :
    N.StructurallyBoundaryOmegaExcluded :=
  N.structurallyBoundaryOmegaExcluded_of_hasNoCriticalSiphon
    (N.hasNoCriticalSiphon_of_weaklyReversible_hasNoSelfReplicableSiphon
      hreal hdich hwr hnosr)

/-- Weakly reversible networks with no drainable siphon satisfy the same global omega-limit
boundary-exclusion conclusion, modulo the finite dichotomy/realization inputs. -/
theorem structurallyBoundaryOmegaExcluded_of_weaklyReversible_hasNoDrainableSiphon
    (N : Network S) (hreal : N.FluxSignRealizable) (hdich : N.MinimalCriticalSiphonDichotomy)
    (hwr : N.WeaklyReversible) (hnd : N.HasNoDrainableSiphon) :
    N.StructurallyBoundaryOmegaExcluded :=
  N.structurallyBoundaryOmegaExcluded_of_hasNoCriticalSiphon
    (N.hasNoCriticalSiphon_of_weaklyReversible_hasNoDrainableSiphon
      hreal hdich hwr hnd)

end Network
end CRNT
