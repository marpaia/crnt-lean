import CRNT.Multistationarity.TrueChemistrySRCriterion

/-!
# The net-coefficient counterexample to the unseparated true-SR criterion

`stronglyConcordant_fullyOpen_of_trueSRCriterion` is **false** without
`ReactantProductSeparated`.  The witness is the two-species network

  `r₀ :  B → A`,   `r₁ : 2B → 2A + B`

over `S = Fin 2` (species `0 = A`, `1 = B`).  No reaction touches the zero complex, so
`ZeroComplexReactionsAreFlows` holds vacuously, and both reaction channels are internal
true-reaction vertices.

Species `B` occurs on **both** sides of `r₁`, with reactant coefficient `2` and product
coefficient `1`.  Hence the true-SR edge `B --ρ₁` carrying the reactant complex has label `2`
while `B`'s net coefficient in `r₁` is only `|1 - 2| = 1`.  The even cycle
`A --ρ₀-- B --ρ₁-- A` therefore satisfies the published `SCycle` identity in labels
(`1 * 2 = 1 * 2`) and *fails* it in net coefficients (`1 * 1 ≠ 1 * 2`).  The net-coefficient
identity is the one the cyclic gain from `InKerL α` actually constrains, which is precisely
the gap recorded at `abs_reactionVector_le_trueSREdge_coeff`.

The fully open extension carries the strong-concordance witness
`α = (3, -2)` on the internal channels, `0` on the synthesis channels, `(-1, -1)` on the
degradation channels, with `σ = (-1, -1)`.
-/

namespace CRNT.Network

open scoped BigOperators

/-- `r₀ : B → A`, `r₁ : 2B → 2A + B`. -/
private abbrev netN : Network (Fin 2) where
  R := Fin 2
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun r =>
    if r = 0 then
      { source := fun s => if s = 0 then 0 else 1
        target := fun s => if s = 0 then 1 else 0 }
    else
      { source := fun s => if s = 0 then 0 else 2
        target := fun s => if s = 0 then 2 else 1 }

/-! ### Coefficient evaluation -/

@[simp] private theorem netN_s0_A : (netN.reaction (0 : Fin 2)).source 0 = 0 := by rfl
@[simp] private theorem netN_s0_B : (netN.reaction (0 : Fin 2)).source 1 = 1 := by rfl
@[simp] private theorem netN_t0_A : (netN.reaction (0 : Fin 2)).target 0 = 1 := by rfl
@[simp] private theorem netN_t0_B : (netN.reaction (0 : Fin 2)).target 1 = 0 := by rfl
@[simp] private theorem netN_s1_A : (netN.reaction (1 : Fin 2)).source 0 = 0 := by rfl
@[simp] private theorem netN_s1_B : (netN.reaction (1 : Fin 2)).source 1 = 2 := by rfl
@[simp] private theorem netN_t1_A : (netN.reaction (1 : Fin 2)).target 0 = 2 := by rfl
@[simp] private theorem netN_t1_B : (netN.reaction (1 : Fin 2)).target 1 = 1 := by rfl

/-! ### Coefficient evaluation in the fully open extension -/

private abbrev FOR := Fin 2 ⊕ (Fin 2 ⊕ Fin 2)

@[simp] private theorem fo_inl0_sA : (netN.fullyOpen.reaction (Sum.inl 0 : FOR)).source 0 = 0 := rfl
@[simp] private theorem fo_inl0_sB : (netN.fullyOpen.reaction (Sum.inl 0 : FOR)).source 1 = 1 := rfl
@[simp] private theorem fo_inl0_tA : (netN.fullyOpen.reaction (Sum.inl 0 : FOR)).target 0 = 1 := rfl
@[simp] private theorem fo_inl0_tB : (netN.fullyOpen.reaction (Sum.inl 0 : FOR)).target 1 = 0 := rfl
@[simp] private theorem fo_inl1_sA : (netN.fullyOpen.reaction (Sum.inl 1 : FOR)).source 0 = 0 := rfl
@[simp] private theorem fo_inl1_sB : (netN.fullyOpen.reaction (Sum.inl 1 : FOR)).source 1 = 2 := rfl
@[simp] private theorem fo_inl1_tA : (netN.fullyOpen.reaction (Sum.inl 1 : FOR)).target 0 = 2 := rfl
@[simp] private theorem fo_inl1_tB : (netN.fullyOpen.reaction (Sum.inl 1 : FOR)).target 1 = 1 := rfl

@[simp] private theorem fo_in_source (s t : Fin 2) :
    (netN.fullyOpen.reaction (Sum.inr (Sum.inl s) : FOR)).source t = 0 := rfl

@[simp] private theorem fo_out_target (s t : Fin 2) :
    (netN.fullyOpen.reaction (Sum.inr (Sum.inr s) : FOR)).target t = 0 := rfl

@[simp] private theorem fo_out0_sA :
    (netN.fullyOpen.reaction (Sum.inr (Sum.inr 0) : FOR)).source 0 = 1 := rfl
@[simp] private theorem fo_out0_sB :
    (netN.fullyOpen.reaction (Sum.inr (Sum.inr 0) : FOR)).source 1 = 0 := rfl
@[simp] private theorem fo_out1_sA :
    (netN.fullyOpen.reaction (Sum.inr (Sum.inr 1) : FOR)).source 0 = 0 := rfl
@[simp] private theorem fo_out1_sB :
    (netN.fullyOpen.reaction (Sum.inr (Sum.inr 1) : FOR)).source 1 = 1 := rfl

/-! ### Non-separation -/

/-- `B` occurs on both sides of `r₁`, so the network is not reactant/product separated. -/
theorem netN_not_reactantProductSeparated : ¬ netN.ReactantProductSeparated := by
  intro h
  have := h (1 : Fin 2) (1 : Fin 2) (by simp)
  simp at this

/-! ### No flow channels -/

private theorem netN_not_flow (r : netN.R) : ¬ netN.IsFlowChannel r := by
  intro h
  fin_cases r
  · rcases h with h | h
    · have := congrFun h (1 : Fin 2); simp [Complex.zero] at this
    · have := congrFun h (0 : Fin 2); simp [Complex.zero] at this
  · rcases h with h | h
    · have := congrFun h (1 : Fin 2); simp [Complex.zero] at this
    · have := congrFun h (0 : Fin 2); simp [Complex.zero] at this

/-- Vacuously true: no channel of `netN` is incident to the zero complex. -/
theorem netN_zeroComplexReactionsAreFlows : netN.ZeroComplexReactionsAreFlows := by
  intro r hr
  exact absurd hr (netN_not_flow r)

/-! ### The fully open extension is strongly discordant

`α = (3, -2)` on the internal channels, `0` on synthesis, `g = (-1,-1)` on degradation,
and `σ = g`. -/

private def sig : Fin 2 → ℝ := fun _ => -1

private def wa : netN.fullyOpen.R → ℝ
  | Sum.inl r => if r = 0 then 3 else -2
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr _) => -1

private theorem netN_kerL : netN.fullyOpen.InKerL wa := by
  apply netN.fullyOpen.inKerL_of_apply
  intro s
  change (∑ q : Fin 2 ⊕ (Fin 2 ⊕ Fin 2), wa q * netN.fullyOpen.reactionVector q s) = 0
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Fin.sum_univ_two]
  fin_cases s <;>
    norm_num [wa, Network.reactionVector, inflowReaction, outflowReaction,
      singletonComplex_apply, Complex.zero_apply]

private theorem netN_witness : netN.fullyOpen.StrongConcordanceWitness wa sig := by
  refine ⟨netN_kerL, ?_, ?_, ?_, ?_, ?_⟩
  · rw [netN.stoichSubspace_fullyOpen_eq_top]; exact Submodule.mem_top
  · intro h
    have h0 := congrFun h 0
    norm_num [sig] at h0
  · -- positive channels: only the internal `r₀`, promoted by species `A`
    intro q hq
    rcases q with r | q
    · fin_cases r
      · exact ⟨0, by
          norm_num [Promotes, reactionDirectionSign, sig]⟩
      · norm_num [wa] at hq
    · rcases q with s | s
      · norm_num [wa] at hq
      · norm_num [wa] at hq
  · -- negative channels: internal `r₁` opposed by `B`, and each degradation opposed by its species
    intro q hq
    rcases q with r | q
    · fin_cases r
      · norm_num [wa] at hq
      · exact ⟨1, by
          norm_num [Promotes, Opposes, reactionDirectionSign, sig]⟩
    · rcases q with s | s
      · norm_num [wa] at hq
      · exact ⟨s, by
          norm_num [Opposes, reactionDirectionSign, sig, outflowReaction,
            singletonComplex_apply, Complex.zero_apply]⟩
  · -- zero channels: only the synthesis channels, whose source support is empty
    intro q hq
    rcases q with r | q
    · fin_cases r <;> norm_num [wa] at hq
    · rcases q with s | s
      · left
        intro t hsrc
        simp at hsrc
      · norm_num [wa] at hq

/-- The fully open extension of `netN` is **not** strongly concordant. -/
theorem netN_fullyOpen_not_stronglyConcordant :
    ¬ netN.fullyOpen.StronglyConcordant := by
  intro h
  exact h ⟨wa, sig, netN_witness⟩

/-! ### The two true-reaction classes -/

private abbrev rho0 : netN.TrueReaction := netN.trueReaction 0
private abbrev rho1 : netN.TrueReaction := netN.trueReaction 1

private theorem netN_trueReaction_injective : Function.Injective netN.trueReaction := by
  intro r q h
  have hs : netN.SameTrueReaction r q := Quotient.exact h
  fin_cases r <;> fin_cases q
  · rfl
  · rcases hs with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact absurd (congrFun h1 1) (by simp)
    · exact absurd (congrFun h1 0) (by simp)
  · rcases hs with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact absurd (congrFun h1 1) (by simp)
    · exact absurd (congrFun h1 0) (by simp)
  · rfl

private theorem rho_ne : rho0 ≠ rho1 := by
  intro h
  exact absurd (netN_trueReaction_injective h) (by decide)

/-- Every true-reaction vertex of `netN` is one of the two channels' classes. -/
private theorem rho_all (p : netN.TrueReaction) : p = rho0 ∨ p = rho1 := by
  induction p using Quotient.inductionOn with
  | _ r => fin_cases r
           · exact Or.inl rfl
           · exact Or.inr rfl

private theorem rep_of_rho0 {r : netN.R} (h : netN.trueReaction r = rho0) : r = 0 :=
  netN_trueReaction_injective h

private theorem rep_of_rho1 {r : netN.R} (h : netN.trueReaction r = rho1) : r = 1 :=
  netN_trueReaction_injective h

private theorem rho0_internal : TrueReaction.Internal netN rho0 := netN_not_flow 0
private theorem rho1_internal : TrueReaction.Internal netN rho1 := netN_not_flow 1

/-! ### Edge classification

Every true-SR edge of `netN` is one of five, determined by its species, its reaction class,
and (only at `ρ₁` on species `B`) its endpoint complex. -/

/-- An edge at `ρ₀` has stoichiometric label `1`, whatever its species and endpoint. -/
private theorem fin2_cases : ∀ s : Fin 2, s = 0 ∨ s = 1 := by decide

private theorem coeff_rho0 (e : netN.TrueSREdge) (h : e.reaction = rho0) :
    e.coeff = 1 := by
  have hrep : e.representative = 0 := rep_of_rho0 (e.representative_class.trans h)
  have hocc := e.occurs
  rw [TrueSREdge.coeff]
  rcases e.endpoint_is_source_or_target with hep | hep
  · rw [hep, hrep] at hocc ⊢
    rcases fin2_cases e.species with hsp | hsp
    · rw [hsp] at hocc; simp at hocc
    · rw [hsp]; rfl
  · rw [hep, hrep] at hocc ⊢
    rcases fin2_cases e.species with hsp | hsp
    · rw [hsp]; rfl
    · rw [hsp] at hocc; simp at hocc

/-- An edge at `ρ₁` on species `A` carries the product complex `2A + B` and has label `2`. -/
private theorem rho1_A_endpoint (e : netN.TrueSREdge) (h : e.reaction = rho1)
    (hs : e.species = 0) : e.endpoint = (netN.reaction 1).target := by
  have hrep : e.representative = 1 := rep_of_rho1 (e.representative_class.trans h)
  have hocc := e.occurs
  rcases e.endpoint_is_source_or_target with hep | hep
  · rw [hep, hrep, hs] at hocc; simp at hocc
  · rw [hep, hrep]

/-- An edge at `ρ₁` on species `B` carries either endpoint; its label is `2` on the reactant
complex `2B` and `1` on the product complex `2A + B`. -/
private theorem rho1_B_cases (e : netN.TrueSREdge) (h : e.reaction = rho1) :
    e.endpoint = (netN.reaction 1).source ∨ e.endpoint = (netN.reaction 1).target := by
  have hrep : e.representative = 1 := rep_of_rho1 (e.representative_class.trans h)
  rcases e.endpoint_is_source_or_target with hep | hep
  · exact Or.inl (by rw [hep, hrep])
  · exact Or.inr (by rw [hep, hrep])

private theorem coeff_rho1_A (e : netN.TrueSREdge) (h : e.reaction = rho1)
    (hs : e.species = 0) : e.coeff = 2 := by
  rw [TrueSREdge.coeff, rho1_A_endpoint e h hs, hs]; rfl

private theorem coeff_rho1_B_source (e : netN.TrueSREdge) (hs : e.species = 1)
    (hep : e.endpoint = (netN.reaction 1).source) : e.coeff = 2 := by
  rw [TrueSREdge.coeff, hep, hs]; rfl

/-- At `ρ₀` the endpoint complex is determined by the species: `A` only occurs in the
product `A`, and `B` only in the reactant `B`. -/
private theorem rho0_A_endpoint (e : netN.TrueSREdge) (h : e.reaction = rho0)
    (hs : e.species = 0) : e.endpoint = (netN.reaction 0).target := by
  have hrep : e.representative = 0 := rep_of_rho0 (e.representative_class.trans h)
  have hocc := e.occurs
  rcases e.endpoint_is_source_or_target with hep | hep
  · rw [hep, hrep, hs] at hocc; simp at hocc
  · rw [hep, hrep]

private theorem rho0_B_endpoint (e : netN.TrueSREdge) (h : e.reaction = rho0)
    (hs : e.species = 1) : e.endpoint = (netN.reaction 0).source := by
  have hrep : e.representative = 0 := rep_of_rho0 (e.representative_class.trans h)
  have hocc := e.occurs
  rcases e.endpoint_is_source_or_target with hep | hep
  · rw [hep, hrep]
  · rw [hep, hrep, hs] at hocc; simp at hocc

private theorem r0_source_ne_target :
    (netN.reaction 0).source ≠ (netN.reaction 0).target := by
  intro h; exact absurd (congrFun h 0) (by simp)

private theorem r1_source_ne_target :
    (netN.reaction 1).source ≠ (netN.reaction 1).target := by
  intro h; exact absurd (congrFun h 0) (by simp)

/-! ### Cycle structure -/

private theorem idx_ne {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    (⟨(i.1 + 1) % n, Nat.mod_lt _ (by omega)⟩ : Fin n) ≠ i := by
  intro h
  have hv : (i.1 + 1) % n = i.1 := congrArg Fin.val h
  have hlt := i.isLt
  rcases Nat.lt_or_ge (i.1 + 1) n with hc | hc
  · rw [Nat.mod_eq_of_lt hc] at hv; omega
  · have he : i.1 + 1 = n := by omega
    rw [he, Nat.mod_self] at hv; omega

/-- Consecutive cycle species are distinct. -/
private theorem cycle_species_ne {n : ℕ} (C : netN.TrueSRCycle n) (i : Fin n) :
    (C.leftEdge i).species ≠ (C.rightEdge i).species := by
  rw [C.left_species, C.right_species]
  intro h
  exact idx_ne C.nontrivial i (C.species_injective h.symm)

/-- A c-pair can only sit at the `ρ₁` vertex: at `ρ₀` the two cycle edges carry opposite
endpoint complexes because they carry different species. -/
private theorem cpair_forces_rho1 {n : ℕ} (C : netN.TrueSRCycle n) (i : Fin n)
    (hcp : C.isCPair i) : C.reaction i = rho1 := by
  rcases rho_all (C.reaction i) with h0 | h1
  · exfalso
    have hl : (C.leftEdge i).reaction = rho0 := (C.left_reaction i).trans h0
    have hr : (C.rightEdge i).reaction = rho0 := (C.right_reaction i).trans h0
    have hne := cycle_species_ne C i
    rcases fin2_cases (C.leftEdge i).species with hls | hls <;>
      rcases fin2_cases (C.rightEdge i).species with hrs | hrs
    · exact hne (hls.trans hrs.symm)
    · rw [TrueSRCycle.isCPair, rho0_A_endpoint _ hl hls,
        rho0_B_endpoint _ hr hrs] at hcp
      exact r0_source_ne_target hcp.symm
    · rw [TrueSRCycle.isCPair, rho0_B_endpoint _ hl hls,
        rho0_A_endpoint _ hr hrs] at hcp
      exact r0_source_ne_target hcp
    · exact hne (hls.trans hrs.symm)
  · exact h1

/-- Hence at most one cycle position is a c-pair. -/
private theorem card_cpairs_le_one {n : ℕ} (C : netN.TrueSRCycle n)
    [DecidablePred C.isCPair] :
    (Finset.univ.filter C.isCPair).card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_
  intro a ha b hb
  simp only [Finset.mem_filter] at ha hb
  exact C.reaction_injective ((cpair_forces_rho1 C a ha.2).trans
    (cpair_forces_rho1 C b hb.2).symm)

/-- An even cycle therefore has **no** c-pair at all. -/
private theorem even_no_cpair {n : ℕ} (C : netN.TrueSRCycle n) (hE : C.Even) (i : Fin n) :
    ¬ C.isCPair i := by
  classical
  have hcard : C.numCPairs ≤ 1 := by
    rw [TrueSRCycle.numCPairs]
    exact card_cpairs_le_one C
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with h0 | h1
  · rw [TrueSRCycle.numCPairs, Finset.card_eq_zero] at h0
    intro hcp
    have : i ∈ Finset.univ.filter C.isCPair := by
      simp only [Finset.mem_filter]; exact ⟨Finset.mem_univ i, hcp⟩
    rw [h0] at this
    exact absurd this (Finset.notMem_empty i)
  · have hE' : _root_.Even C.numCPairs := hE
    rw [h1] at hE'
    exact absurd hE' (by decide)

/-! ### Every even cycle is an s-cycle (in labels) -/

/-- At each position of an even cycle the two edge labels agree: both are `1` at `ρ₀` and
both are `2` at `ρ₁`.  This is what makes the published `SCycle` identity hold. -/
private theorem even_coeff_eq {n : ℕ} (C : netN.TrueSRCycle n) (hE : C.Even) (i : Fin n) :
    (C.leftEdge i).coeff = (C.rightEdge i).coeff := by
  have hne := cycle_species_ne C i
  rcases rho_all (C.reaction i) with h0 | h1
  · rw [coeff_rho0 _ ((C.left_reaction i).trans h0),
      coeff_rho0 _ ((C.right_reaction i).trans h0)]
  · have hl : (C.leftEdge i).reaction = rho1 := (C.left_reaction i).trans h1
    have hr : (C.rightEdge i).reaction = rho1 := (C.right_reaction i).trans h1
    have hcp := even_no_cpair C hE i
    rw [TrueSRCycle.isCPair] at hcp
    rcases fin2_cases (C.leftEdge i).species with hls | hls <;>
      rcases fin2_cases (C.rightEdge i).species with hrs | hrs
    · exact absurd (hls.trans hrs.symm) hne
    · -- left is `A` (label 2), right is `B` forced onto the reactant complex (label 2)
      have hlep := rho1_A_endpoint _ hl hls
      have := rho1_B_cases _ hr
      rcases this with hrep | hrep
      · rw [coeff_rho1_A _ hl hls, coeff_rho1_B_source _ hrs hrep]
      · exact absurd (hlep.trans hrep.symm) hcp
    · -- left is `B`, right is `A`
      have hrep := rho1_A_endpoint _ hr hrs
      rcases rho1_B_cases _ hl with hlep | hlep
      · rw [coeff_rho1_A _ hr hrs, coeff_rho1_B_source _ hls hlep]
      · exact absurd (hlep.trans hrep.symm) hcp
    · exact absurd (hls.trans hrs.symm) hne

private theorem even_sCycle {n : ℕ} (C : netN.TrueSRCycle n) (hE : C.Even) : C.SCycle :=
  Finset.prod_congr rfl (fun i _ => even_coeff_eq C hE i)

/-! ### The four edges of the even cycle

Every even cycle of `netN` is, up to edge identity, the four-cycle
`A --ρ₀-- B --ρ₁-- A`, whose edges are these. -/

private def eA0 : netN.TrueSREdge where
  species := 0
  reaction := rho0
  internal := rho0_internal
  endpoint := (netN.reaction 0).target
  representative := 0
  representative_class := rfl
  endpoint_is_source_or_target := Or.inr rfl
  occurs := by simp

private def eB0 : netN.TrueSREdge where
  species := 1
  reaction := rho0
  internal := rho0_internal
  endpoint := (netN.reaction 0).source
  representative := 0
  representative_class := rfl
  endpoint_is_source_or_target := Or.inl rfl
  occurs := by simp

private def eA1 : netN.TrueSREdge where
  species := 0
  reaction := rho1
  internal := rho1_internal
  endpoint := (netN.reaction 1).target
  representative := 1
  representative_class := rfl
  endpoint_is_source_or_target := Or.inr rfl
  occurs := by simp

private def eB1 : netN.TrueSREdge where
  species := 1
  reaction := rho1
  internal := rho1_internal
  endpoint := (netN.reaction 1).source
  representative := 1
  representative_class := rfl
  endpoint_is_source_or_target := Or.inl rfl
  occurs := by simp

/-- Both reaction classes occur along any cycle, since the two classes are the only ones
and the cycle's reaction map is injective on at least two positions. -/
private theorem exists_rho_positions {n : ℕ} (C : netN.TrueSRCycle n) :
    (∃ i, C.reaction i = rho0) ∧ (∃ j, C.reaction j = rho1) := by
  have hn := C.nontrivial
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have hne : i0 ≠ i1 := by
    intro h; exact absurd (congrArg Fin.val h) (by simp [i0, i1])
  have hrne : C.reaction i0 ≠ C.reaction i1 := fun h => hne (C.reaction_injective h)
  rcases rho_all (C.reaction i0) with h0 | h0 <;> rcases rho_all (C.reaction i1) with h1 | h1
  · exact absurd (h0.trans h1.symm) hrne
  · exact ⟨⟨i0, h0⟩, ⟨i1, h1⟩⟩
  · exact ⟨⟨i1, h1⟩, ⟨i0, h0⟩⟩
  · exact absurd (h0.trans h1.symm) hrne

/-- An even cycle contains all four edges of the four-cycle. -/
private theorem even_contains_edges {n : ℕ} (C : netN.TrueSRCycle n) (hE : C.Even) :
    C.ContainsEdge eA0 ∧ C.ContainsEdge eB0 ∧ C.ContainsEdge eA1 ∧ C.ContainsEdge eB1 := by
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := exists_rho_positions C
  have hli : (C.leftEdge i).reaction = rho0 := (C.left_reaction i).trans hi
  have hri : (C.rightEdge i).reaction = rho0 := (C.right_reaction i).trans hi
  have hlj : (C.leftEdge j).reaction = rho1 := (C.left_reaction j).trans hj
  have hrj : (C.rightEdge j).reaction = rho1 := (C.right_reaction j).trans hj
  have hnei := cycle_species_ne C i
  have hnej := cycle_species_ne C j
  have hcpj := even_no_cpair C hE j
  rw [TrueSRCycle.isCPair] at hcpj
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases fin2_cases (C.leftEdge i).species with hls | hls
    · exact Or.inl ⟨i, ⟨hls.symm, hli.symm, (rho0_A_endpoint _ hli hls).symm⟩⟩
    · rcases fin2_cases (C.rightEdge i).species with hrs | hrs
      · exact Or.inr ⟨i, ⟨hrs.symm, hri.symm, (rho0_A_endpoint _ hri hrs).symm⟩⟩
      · exact absurd (hls.trans hrs.symm) hnei
  · rcases fin2_cases (C.leftEdge i).species with hls | hls
    · rcases fin2_cases (C.rightEdge i).species with hrs | hrs
      · exact absurd (hls.trans hrs.symm) hnei
      · exact Or.inr ⟨i, ⟨hrs.symm, hri.symm, (rho0_B_endpoint _ hri hrs).symm⟩⟩
    · exact Or.inl ⟨i, ⟨hls.symm, hli.symm, (rho0_B_endpoint _ hli hls).symm⟩⟩
  · rcases fin2_cases (C.leftEdge j).species with hls | hls
    · exact Or.inl ⟨j, ⟨hls.symm, hlj.symm, (rho1_A_endpoint _ hlj hls).symm⟩⟩
    · rcases fin2_cases (C.rightEdge j).species with hrs | hrs
      · exact Or.inr ⟨j, ⟨hrs.symm, hrj.symm, (rho1_A_endpoint _ hrj hrs).symm⟩⟩
      · exact absurd (hls.trans hrs.symm) hnej
  · rcases fin2_cases (C.leftEdge j).species with hls | hls
    · -- left is `A`, so right is `B` and its endpoint is forced off the product complex
      rcases fin2_cases (C.rightEdge j).species with hrs | hrs
      · exact absurd (hls.trans hrs.symm) hnej
      · rcases rho1_B_cases _ hrj with hrep | hrep
        · exact Or.inr ⟨j, ⟨hrs.symm, hrj.symm, hrep.symm⟩⟩
        · exact absurd ((rho1_A_endpoint _ hlj hls).trans hrep.symm) hcpj
    · rcases rho1_B_cases _ hlj with hlep | hlep
      · exact Or.inl ⟨j, ⟨hls.symm, hlj.symm, hlep.symm⟩⟩
      · rcases fin2_cases (C.rightEdge j).species with hrs | hrs
        · exact absurd (hlep.trans (rho1_A_endpoint _ hrj hrs).symm) hcpj
        · exact absurd (hls.trans hrs.symm) hnej

/-! ### No S-to-R intersection

The four common edges form a four-cycle on the four vertices `A`, `B`, `ρ₀`, `ρ₁`.
`components_separated` forces them all into one listed component, so that component is a
vertex-injective path with at least four edges; but a path alternates species and reaction
vertices, so its positions `0`, `2`, `4` would carry three distinct species, and `netN`
has only two. -/

@[simp] private theorem eA0_species : eA0.species = 0 := rfl
@[simp] private theorem eA0_reaction : eA0.reaction = rho0 := rfl
@[simp] private theorem eB0_species : eB0.species = 1 := rfl
@[simp] private theorem eB0_reaction : eB0.reaction = rho0 := rfl
@[simp] private theorem eA1_species : eA1.species = 0 := rfl
@[simp] private theorem eA1_reaction : eA1.reaction = rho1 := rfl
@[simp] private theorem eB1_species : eB1.species = 1 := rfl
@[simp] private theorem eB1_reaction : eB1.reaction = rho1 := rfl

/-- A vertex-injective alternating path with four or more edges is impossible here. -/
private theorem no_long_component {m n : ℕ} {C : netN.TrueSRCycle m} {D : netN.TrueSRCycle n}
    (I : C.SToRIntersection D) (c : Fin I.componentCount)
    (h4 : 4 ≤ I.componentLength c) : False := by
  have hq : ∀ x y : Fin (I.componentLength c + 1), x.val ≠ y.val →
      I.vertex c x ≠ I.vertex c y :=
    fun x y hxy h => hxy (congrArg Fin.val (I.vertex_simple c h))
  -- edge positions
  let p0 : Fin (I.componentLength c) := ⟨0, by omega⟩
  let p1 : Fin (I.componentLength c) := ⟨1, by omega⟩
  let p2 : Fin (I.componentLength c) := ⟨2, by omega⟩
  let p3 : Fin (I.componentLength c) := ⟨3, by omega⟩
  -- vertex positions
  let q0 : Fin (I.componentLength c + 1) := ⟨0, by omega⟩
  let q1 : Fin (I.componentLength c + 1) := ⟨1, by omega⟩
  let q2 : Fin (I.componentLength c + 1) := ⟨2, by omega⟩
  let q3 : Fin (I.componentLength c + 1) := ⟨3, by omega⟩
  let q4 : Fin (I.componentLength c + 1) := ⟨4, by omega⟩
  have k0 : Fin.castSucc p0 = q0 := by apply Fin.ext; simp [p0, q0]
  have k0' : p0.succ = q1 := by apply Fin.ext; simp [p0, q1]
  have k1 : Fin.castSucc p1 = q1 := by apply Fin.ext; simp [p1, q1]
  have k1' : p1.succ = q2 := by apply Fin.ext; simp [p1, q2]
  have k2 : Fin.castSucc p2 = q2 := by apply Fin.ext; simp [p2, q2]
  have k2' : p2.succ = q3 := by apply Fin.ext; simp [p2, q3]
  have k3 : Fin.castSucc p3 = q3 := by apply Fin.ext; simp [p3, q3]
  have k3' : p3.succ = q4 := by apply Fin.ext; simp [p3, q4]
  obtain ⟨s0, hs0⟩ := I.starts_at_species c
  have hz : (0 : Fin (I.componentLength c + 1)) = q0 := by apply Fin.ext; simp [q0]
  rw [hz] at hs0
  -- walk along the path, alternating species and reaction vertices
  have step0 : ∃ r, I.vertex c q1 = Sum.inr r := by
    rcases I.connects c p0 with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact ⟨_, by rw [← k0', hv]⟩
    · rw [k0, hs0] at hu; exact absurd hu (by simp)
  obtain ⟨r1, hr1⟩ := step0
  have step1 : ∃ a, I.vertex c q2 = Sum.inl a := by
    rcases I.connects c p1 with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · rw [k1, hr1] at hu; exact absurd hu (by simp)
    · exact ⟨_, by rw [← k1', hv]⟩
  obtain ⟨a2, ha2⟩ := step1
  have step2 : ∃ r, I.vertex c q3 = Sum.inr r := by
    rcases I.connects c p2 with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact ⟨_, by rw [← k2', hv]⟩
    · rw [k2, ha2] at hu; exact absurd hu (by simp)
  obtain ⟨r3, hr3⟩ := step2
  have step3 : ∃ a, I.vertex c q4 = Sum.inl a := by
    rcases I.connects c p3 with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · rw [k3, hr3] at hu; exact absurd hu (by simp)
    · exact ⟨_, by rw [← k3', hv]⟩
  obtain ⟨a4, ha4⟩ := step3
  -- three distinct species in `Fin 2`
  have d02 : s0 ≠ a2 := by
    intro h; exact hq q0 q2 (by simp [q0, q2]) (by rw [hs0, ha2, h])
  have d04 : s0 ≠ a4 := by
    intro h; exact hq q0 q4 (by simp [q0, q4]) (by rw [hs0, ha4, h])
  have d24 : a2 ≠ a4 := by
    intro h; exact hq q2 q4 (by simp [q2, q4]) (by rw [ha2, ha4, h])
  rcases fin2_cases s0 with h1 | h1 <;> rcases fin2_cases a2 with h2 | h2 <;>
    rcases fin2_cases a4 with h3 | h3 <;> simp_all

/-- **No two even cycles of `netN` have a species-to-reaction intersection.** -/
private theorem netN_no_sToR {m n : ℕ} (C : netN.TrueSRCycle m) (D : netN.TrueSRCycle n)
    (hC : C.Even) (hD : D.Even) : ¬ Nonempty (C.SToRIntersection D) := by
  rintro ⟨I⟩
  obtain ⟨hCA0, hCB0, hCA1, hCB1⟩ := even_contains_edges C hC
  obtain ⟨hDA0, hDB0, hDA1, hDB1⟩ := even_contains_edges D hD
  obtain ⟨cA0, iA0, hmA0⟩ := I.covers_common eA0 hCA0 hDA0
  obtain ⟨cB0, iB0, hmB0⟩ := I.covers_common eB0 hCB0 hDB0
  obtain ⟨cA1, iA1, hmA1⟩ := I.covers_common eA1 hCA1 hDA1
  obtain ⟨cB1, iB1, hmB1⟩ := I.covers_common eB1 hCB1 hDB1
  -- all four common edges lie in one listed component
  have h1 : cA0 = cB0 := by
    by_contra hne
    exact I.components_separated hne iA0 iB0 (Or.inr (by rw [← hmA0.2.1, ← hmB0.2.1]; rfl))
  subst h1
  have h2 : cA0 = cB1 := by
    by_contra hne
    exact I.components_separated hne iB0 iB1 (Or.inl (by rw [← hmB0.1, ← hmB1.1]; rfl))
  subst h2
  have h3 : cA0 = cA1 := by
    by_contra hne
    exact I.components_separated hne iB1 iA1 (Or.inr (by rw [← hmB1.2.1, ← hmA1.2.1]; rfl))
  subst h3
  -- the four matching positions inside that component are pairwise distinct
  have nAB0 : iA0 ≠ iB0 := by
    intro h
    have hb : eB0.SameIncidence (I.edge cA0 iA0) := by rw [h]; exact hmB0
    have hs : eA0.species = eB0.species := hmA0.1.trans hb.1.symm
    simp at hs
  have nAB1 : iA0 ≠ iB1 := by
    intro h
    have hb : eB1.SameIncidence (I.edge cA0 iA0) := by rw [h]; exact hmB1
    have hs : eA0.species = eB1.species := hmA0.1.trans hb.1.symm
    simp at hs
  have nAA1 : iA0 ≠ iA1 := by
    intro h
    have hb : eA1.SameIncidence (I.edge cA0 iA0) := by rw [h]; exact hmA1
    exact rho_ne (hmA0.2.1.trans hb.2.1.symm)
  have nB0B1 : iB0 ≠ iB1 := by
    intro h
    have hb : eB1.SameIncidence (I.edge cA0 iB0) := by rw [h]; exact hmB1
    exact rho_ne (hmB0.2.1.trans hb.2.1.symm)
  have nB0A1 : iB0 ≠ iA1 := by
    intro h
    have hb : eA1.SameIncidence (I.edge cA0 iB0) := by rw [h]; exact hmA1
    have hs : eB0.species = eA1.species := hmB0.1.trans hb.1.symm
    simp at hs
  have nB1A1 : iB1 ≠ iA1 := by
    intro h
    have hb : eA1.SameIncidence (I.edge cA0 iB1) := by rw [h]; exact hmA1
    have hs : eB1.species = eA1.species := hmB1.1.trans hb.1.symm
    simp at hs
  -- so the component has at least four edges
  have h4 : 4 ≤ I.componentLength cA0 := by
    have b1 := iA0.isLt; have b2 := iB0.isLt; have b3 := iB1.isLt; have b4 := iA1.isLt
    have v1 : iA0.val ≠ iB0.val := fun h => nAB0 (Fin.ext h)
    have v2 : iA0.val ≠ iB1.val := fun h => nAB1 (Fin.ext h)
    have v3 : iA0.val ≠ iA1.val := fun h => nAA1 (Fin.ext h)
    have v4 : iB0.val ≠ iB1.val := fun h => nB0B1 (Fin.ext h)
    have v5 : iB0.val ≠ iA1.val := fun h => nB0A1 (Fin.ext h)
    have v6 : iB1.val ≠ iA1.val := fun h => nB1A1 (Fin.ext h)
    omega
  exact no_long_component I cA0 h4

/-! ### The counterexample -/

/-- **The unseparated true-SR criterion does not imply strong concordance of the fully open
extension.**  `netN` satisfies `ZeroComplexReactionsAreFlows` and `TrueSRStrongCriterion`,
its fully open extension is strongly discordant, and it is not reactant/product separated. -/
theorem netN_trueSRStrongCriterion : netN.TrueSRStrongCriterion :=
  ⟨fun C hE => even_sCycle C hE, fun C D hC hD => netN_no_sToR C D hC hD⟩

/-- The exact statement of `stronglyConcordant_fullyOpen_of_trueSRCriterion` **without**
`ReactantProductSeparated` is false. -/
theorem trueSRCriterion_netCoeff_counterexample :
    netN.ZeroComplexReactionsAreFlows ∧ netN.TrueSRStrongCriterion ∧
      ¬ netN.fullyOpen.StronglyConcordant ∧ ¬ netN.ReactantProductSeparated :=
  ⟨netN_zeroComplexReactionsAreFlows, netN_trueSRStrongCriterion,
    netN_fullyOpen_not_stronglyConcordant, netN_not_reactantProductSeparated⟩

/-! ### Non-vacuity

Unlike `CRNT/Examples/TrueSRCounterexample.lean`, where every channel was a flow channel so
the true-SR graph had no edges at all and the criterion held vacuously, here the criterion has
real content: the four-cycle `A --ρ₀-- B --ρ₁-- A` is an honest even cycle of the true-SR
graph, and it *is* an `SCycle`.  What it is not is an `SCycleNet`. -/

@[simp] private theorem eA0_endpoint : eA0.endpoint = (netN.reaction 0).target := rfl
@[simp] private theorem eB0_endpoint : eB0.endpoint = (netN.reaction 0).source := rfl
@[simp] private theorem eA1_endpoint : eA1.endpoint = (netN.reaction 1).target := rfl
@[simp] private theorem eB1_endpoint : eB1.endpoint = (netN.reaction 1).source := rfl

@[simp] private theorem eA0_rep : eA0.representative = 0 := rfl
@[simp] private theorem eB0_rep : eB0.representative = 0 := rfl
@[simp] private theorem eA1_rep : eA1.representative = 1 := rfl
@[simp] private theorem eB1_rep : eB1.representative = 1 := rfl

/-- The four-cycle `A --ρ₀-- B --ρ₁-- A`. -/
private def cyc : netN.TrueSRCycle 2 where
  nontrivial := le_refl 2
  species := id
  reaction := fun i => if i = 0 then rho0 else rho1
  leftEdge := fun i => if i = 0 then eA0 else eB1
  rightEdge := fun i => if i = 0 then eB0 else eA1
  left_species := by intro i; fin_cases i <;> rfl
  left_reaction := by intro i; fin_cases i <;> rfl
  right_species := by intro i; fin_cases i <;> rfl
  right_reaction := by intro i; fin_cases i <;> rfl
  species_injective := fun _ _ h => h
  reaction_injective := by
    intro a b h
    fin_cases a <;> fin_cases b
    · rfl
    · simp at h; exact absurd h rho_ne
    · simp at h; exact absurd h.symm rho_ne
    · rfl

private theorem cyc_no_cpair : ∀ i : Fin 2, ¬ cyc.isCPair i := by
  intro i
  fin_cases i
  · exact fun h => r0_source_ne_target h.symm
  · exact fun h => r1_source_ne_target h

/-- The four-cycle is an even cycle: neither of its reaction vertices is a c-pair. -/
private theorem cyc_even : cyc.Even := by
  have h0 : cyc.numCPairs = 0 := by
    rw [TrueSRCycle.numCPairs, Finset.card_eq_zero]
    apply Finset.eq_empty_of_forall_notMem
    intro i hi
    simp only [Finset.mem_filter] at hi
    exact cyc_no_cpair i hi.2
  have : _root_.Even cyc.numCPairs := by rw [h0]; exact ⟨0, rfl⟩
  exact this

/-- **The true-SR graph of `netN` really does have an even cycle**, so
`netN_trueSRStrongCriterion` is not a vacuous statement. -/
theorem netN_has_even_cycle : ∃ (C : netN.TrueSRCycle 2), C.Even := ⟨cyc, cyc_even⟩

/-- That even cycle is an `SCycle` in stoichiometric labels: `1 * 2 = 1 * 2`. -/
theorem netN_cycle_sCycle : cyc.SCycle := even_sCycle cyc cyc_even

/-- **…and it fails the net-coefficient identity**: `1 * 1 ≠ 1 * 2`.  This is the exact
mismatch that breaks the unseparated criterion — the cyclic gain derived from `InKerL α`
constrains `SCycleNet`, not `SCycle`. -/
theorem netN_cycle_not_sCycleNet : ¬ cyc.SCycleNet := by
  have hl0 : cyc.leftEdge 0 = eA0 := rfl
  have hl1 : cyc.leftEdge 1 = eB1 := rfl
  have hr0 : cyc.rightEdge 0 = eB0 := rfl
  have hr1 : cyc.rightEdge 1 = eA1 := rfl
  rw [TrueSRCycle.SCycleNet, Fin.prod_univ_two, Fin.prod_univ_two, hl0, hl1, hr0, hr1]
  norm_num [TrueSREdge.netCoeff]

/-! ### The refutation -/

/-- **The exact statement of `stronglyConcordant_fullyOpen_of_trueSRCriterion` without
`ReactantProductSeparated` is false.**  Refuted at `S = Fin 2`. -/
theorem unseparated_trueSRCriterion_false :
    ¬ ∀ (N : Network (Fin 2)), N.ZeroComplexReactionsAreFlows → N.TrueSRStrongCriterion →
        N.fullyOpen.StronglyConcordant := by
  intro h
  exact netN_fullyOpen_not_stronglyConcordant
    (h netN netN_zeroComplexReactionsAreFlows netN_trueSRStrongCriterion)

end CRNT.Network
