import CRNT.Reduction.Intermediates
import CRNT.Reduction.SingleIntermediateElimination
import CRNT.Reduction.IntermediateSchurComplement
import CRNT.Dynamics.MassActionAlgebra

/-!
# The toric reduction: the reduced network has the same complex-balanced equilibria

Eliminating intermediate species is one of the few operations on chemical reaction networks
that is *exactly* behaviour-preserving: the reduced network has the same steady states, and
in particular the same complex-balanced equilibria, as the original.  Two classical
references are

* M. Feliu and C. Wiuf, *A reduction theorem for steady state sets of chemical reaction
  networks*, J. Math. Chem. **51** (2012), 227–251 — the steady-state-set version of the
  reduction;
* G. Craciun, *Toric differential inclusions and a proof of the global attractor
  conjecture*, arXiv:1501.02860 v3 (2015), §7 — the toric reduction: the reduced network
  has the same complex-balanced equilibria.

They matter because the reduction produces a *smaller* network with the same behaviour: one
may study the reduced network — fewer species, fewer complexes, often a smaller
deficiency — and transport the conclusions back.

## The algebraic kernel already in the repository

* `CRNT.Reduction.Intermediates`: the structural notion of an intermediate species
  (`Network.IsIntermediateSet`), the core complexes (`Network.IsCoreComplex`) and the
  contraction of directed paths through intermediate complexes;
* `CRNT.Reduction.SingleIntermediateElimination`: the rates of the one-intermediate
  elimination — the steady-state concentration `k₁ /(Σ_l k_l) · x^y` and the effective core
  rates `k₁ k_j /(Σ_l k_l)`;
* `CRNT.Reduction.IntermediateSchurComplement`: the multi-intermediate elimination
  `h = −A_H⁻¹ b` and the reduced field `f_red = f_core − C A_H⁻¹ b`.

## What this module adds

This module attaches the *kinetic* content of the reduction to that kernel, for the
one-intermediate case:

* `Network.OneIntermediate`: the structural data of a network with a single intermediate
  species (the intermediate complex is the singleton `{h}`, it is fed by exactly one
  reaction and drained by finitely many);
* `Network.OneIntermediate.reducedNetwork`: the reduced network — the intermediate complex
  disappears, the draining reactions are contracted onto the feeding complex with the
  effective rates `k₁ k_j /(Σ_l k_l)`, and the feeding reaction becomes inert;
* `Network.OneIntermediate.eliminatedConcentration`: the eliminated concentration
  `k₁ /(Σ_l k_l) · x^y`, which is the repository's `SingleIntermediateKineticData`
  formula;
* `Network.OneIntermediate.singleIntermediate_reduction_preserves_complexBalance`: **the
  toric reduction preserves the complex-balanced equilibria**;
* `Network.OneIntermediate.steadyState_intermediate_eliminated`: the Feliu–Wiuf
  steady-state ingredient — at a mass-action steady state the intermediate species sits at
  its eliminated steady-state value, so the intermediate coordinate of a steady state is
  determined by the core concentrations alone (the *full* steady-state-set equivalence
  `IsMassActionSteadyState N κ x ↔ (IsMassActionSteadyState N_red κ_red x ∧ x h = elim)`
  is not proved here — see the module's outstanding obligation);
* `Network.ToricReductionPreservesComplexBalance`: the general contract, of which the two
  theorems above are the one-intermediate instance.

## What this module does *not* do

The *general* reduction — an arbitrary set of intermediate species, an arbitrary reduced
network — is not stated here.  It requires a network-construction API: the ability to build
the reduced network together with its complexes and its rate constants, and to transport
complex-balanced equilibria through it.  This repository deliberately avoids that API, and
the theorems are therefore stated for the one-intermediate case, which is exactly the case
for which the repository's algebraic kernel (`CRNT.Reduction.SingleIntermediateElimination`)
supplies the elimination formulas.

Depends on: `CRNT.Reduction.Intermediates`, `CRNT.Reduction.SingleIntermediateElimination`,
`CRNT.Reduction.IntermediateSchurComplement`, `CRNT.Dynamics.MassActionAlgebra`.
-/


namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

structure OneIntermediate (N : Network S) (κ : N.RateConstants) where
  intermediate : S
  input : N.R
  exits : Finset N.R
  inputSource : Complex S
  structural : N.IsIntermediateSet {intermediate}
  input_target : (N.reaction input).target = singletonComplex intermediate
  input_source : (N.reaction input).source = inputSource
  inputSource_ne : inputSource ≠ singletonComplex intermediate
  exits_source : ∀ r ∈ exits, (N.reaction r).source = singletonComplex intermediate
  exits_target_ne : ∀ r ∈ exits, (N.reaction r).target ≠ singletonComplex intermediate
  exhaustive : ∀ r : N.R, r = input ∨ r ∈ exits ∨
    ((N.reaction r).source ≠ singletonComplex intermediate ∧
      (N.reaction r).target ≠ singletonComplex intermediate)
  exits_ne : exits.Nonempty

namespace OneIntermediate

variable {N : Network S} {κ : N.RateConstants}

/-- Every complex of the network other than the intermediate complex is free of the
intermediate species. -/
theorem core_of_ne {D : OneIntermediate N κ} {c : Complex S} (hc : c ∈ N.complexes)
    (hne : c ≠ singletonComplex D.intermediate) : c D.intermediate = 0 := by
  by_contra h
  have := D.structural.2 c hc D.intermediate (by simp) h
  exact hne this

/-- The source of the feeding reaction is a core complex. -/
theorem inputSource_core (D : OneIntermediate N κ) : D.inputSource D.intermediate = 0 :=
  D.core_of_ne (by rw [← D.input_source]; exact N.source_mem_complexes D.input)
    (by simpa [D.input_source] using D.inputSource_ne)

/-- The feeding reaction is not a draining reaction. -/
theorem input_not_exit (D : OneIntermediate N κ) : D.input ∉ D.exits := by
  intro h
  have h1 := D.exits_source D.input h
  rw [D.input_source] at h1
  exact D.inputSource_ne h1

/-- Total rate constant of the draining reactions. -/
noncomputable def totalExitRate (D : OneIntermediate N κ) : ℝ := ∑ r ∈ D.exits, κ.k r

/-- The total exit rate is positive. -/
theorem totalExitRate_pos (D : OneIntermediate N κ) : 0 < D.totalExitRate := by
  unfold totalExitRate
  obtain ⟨r, hr⟩ := D.exits_ne
  exact Finset.sum_pos' (fun r _ => (κ.positive r).le) ⟨r, hr, κ.positive r⟩

/-- The eliminated concentration of the intermediate species. -/
noncomputable def eliminatedConcentration (D : OneIntermediate N κ) (x : Concentration S) : ℝ :=
  κ.k D.input / D.totalExitRate * D.inputSource.massActionMonomial x

theorem eliminatedConcentration_eq (D : OneIntermediate N κ) (x : Concentration S) :
    D.eliminatedConcentration x * D.totalExitRate
      = κ.k D.input * D.inputSource.massActionMonomial x := by
  unfold eliminatedConcentration
  field_simp [D.totalExitRate_pos.ne']

/-- The source complex of the reduced reaction `r`. -/
def reducedSource (D : OneIntermediate N κ) (r : N.R) : Complex S :=
  if r = D.input ∨ r ∈ D.exits then D.inputSource else (N.reaction r).source

/-- The target complex of the reduced reaction `r`. -/
def reducedTarget (D : OneIntermediate N κ) (r : N.R) : Complex S :=
  if r = D.input then D.inputSource else (N.reaction r).target

/-- The reduced rate constant of `r`. -/
noncomputable def reducedRate (D : OneIntermediate N κ) (r : N.R) : ℝ :=
  if r ∈ D.exits then κ.k D.input * κ.k r / D.totalExitRate else κ.k r

theorem reducedSource_input (D : OneIntermediate N κ) :
    D.reducedSource D.input = D.inputSource := by
  rw [reducedSource, ite_eq_left (Or.inl rfl)]

theorem reducedSource_exit (D : OneIntermediate N κ) {r : N.R} (h : r ∈ D.exits) :
    D.reducedSource r = D.inputSource := by
  have hne : r ≠ D.input := by
    intro hcon; subst hcon; exact D.input_not_exit h
  rw [reducedSource, ite_eq_left (Or.inr h)]

theorem reducedTarget_input (D : OneIntermediate N κ) :
    D.reducedTarget D.input = D.inputSource := by
  rw [reducedTarget, ite_eq_left rfl]

theorem reducedTarget_exit (D : OneIntermediate N κ) {r : N.R} (h : r ∈ D.exits) :
    D.reducedTarget r = (N.reaction r).target := by
  have hne : r ≠ D.input := by
    intro hcon; subst hcon; exact D.input_not_exit h
  rw [reducedTarget, ite_eq_right hne]

theorem reducedRate_input (D : OneIntermediate N κ) :
    D.reducedRate D.input = κ.k D.input := by
  rw [reducedRate, ite_eq_right D.input_not_exit]

theorem reducedRate_exit (D : OneIntermediate N κ) {r : N.R} (h : r ∈ D.exits) :
    D.reducedRate r = κ.k D.input * κ.k r / D.totalExitRate := by
  rw [reducedRate, ite_eq_left h]

theorem reducedSource_core (D : OneIntermediate N κ) {r : N.R} (hne : r ≠ D.input)
    (hexne : r ∉ D.exits) : D.reducedSource r = (N.reaction r).source := by
  rw [reducedSource,
    ite_eq_right (fun h => h.elim (fun h' => hne h') (fun h' => hexne h'))]

theorem reducedTarget_core (D : OneIntermediate N κ) {r : N.R} (hne : r ≠ D.input) :
    D.reducedTarget r = (N.reaction r).target := by
  rw [reducedTarget, ite_eq_right hne]

theorem reducedRate_core (D : OneIntermediate N κ) {r : N.R} (hexne : r ∉ D.exits) :
    D.reducedRate r = κ.k r := by
  rw [reducedRate, ite_eq_right hexne]

/-- The reduced network obtained by eliminating the intermediate species. -/
def reducedNetwork (D : OneIntermediate N κ) : Network S where
  R := N.R
  decEqR := N.decEqR
  fintypeR := N.fintypeR
  reaction := fun r => ⟨D.reducedSource r, D.reducedTarget r⟩

/-- The reduced rate constants are positive. -/
theorem reducedRate_pos (D : OneIntermediate N κ) (r : N.R) : 0 < D.reducedRate r := by
  by_cases h2 : r ∈ D.exits
  · rw [D.reducedRate_exit h2]
    exact div_pos (mul_pos (κ.positive D.input) (κ.positive r)) D.totalExitRate_pos
  · rw [reducedRate, ite_eq_right h2]; exact κ.positive r

/-- The reduced rate constants. -/
noncomputable def reducedRateConstants (D : OneIntermediate N κ) :
    (D.reducedNetwork).RateConstants where
  k := D.reducedRate
  positive := by
    intro r
    exact D.reducedRate_pos (r := r)

/-- The monomial of the singleton complex of a species is the species concentration. -/
theorem massActionMonomial_singleton (h : S) (x : Concentration S) :
    (singletonComplex h).massActionMonomial x = x h := by
  simp [singletonComplex, Complex.massActionMonomial]

/-- Total rate constant of the draining reactions into the core complex `c`. -/
noncomputable def exitRateInto (D : OneIntermediate N κ) (c : Complex S) : ℝ :=
  ∑ r ∈ D.exits, if (N.reaction r).target = c then κ.k r else 0

/-- The net flux into `c` contributed by reaction `r` in the original network. -/
def origNet (κ : N.RateConstants) (x : Concentration S) (c : Complex S) (r : N.R) : ℝ :=
  (if (N.reaction r).target = c then κ.k r * (N.reaction r).source.massActionMonomial x else 0)
    - (if (N.reaction r).source = c then κ.k r * (N.reaction r).source.massActionMonomial x else 0)

/-- The net flux into `c` contributed by reaction `r` in the reduced network. -/
noncomputable def reducedNet (D : OneIntermediate N κ) (x : Concentration S) (c : Complex S)
    (r : N.R) : ℝ :=
  (if D.reducedTarget r = c then D.reducedRate r * (D.reducedSource r).massActionMonomial x else 0)
    - (if D.reducedSource r = c then D.reducedRate r * (D.reducedSource r).massActionMonomial x else 0)

/-- The uniform formula for the difference of the per-reaction net fluxes. -/
noncomputable def netDiffFormula (D : OneIntermediate N κ) (x : Concentration S) (c : Complex S)
    (r : N.R) : ℝ :=
  (if r ∈ D.exits then
      κ.k r * ((if (N.reaction r).target = c then D.eliminatedConcentration x else 0)
        - (if (N.reaction r).target = c then x D.intermediate else 0))
      - (if D.inputSource = c then κ.k r * D.eliminatedConcentration x else 0)
    else 0)
    + (if r = D.input then
        (if D.inputSource = c then κ.k D.input * D.inputSource.massActionMonomial x else 0)
      else 0)

/-- **The per-reaction flux identity.**  For a complex `c` different from the intermediate
complex, the net flux of a single reaction into `c` in the reduced network differs from the
one in the original network by the uniform formula `netDiffFormula`. -/
theorem netDiff_summand (D : OneIntermediate N κ) (x : Concentration S) (c : Complex S)
    (hcne : c ≠ singletonComplex D.intermediate) (r : N.R) :
    D.reducedNet x c r - origNet κ x c r = D.netDiffFormula x c r := by
  rcases D.exhaustive r with hcon | hex | hcore
  · -- the feeding reaction
    subst hcon
    rw [reducedNet, D.reducedSource_input, D.reducedTarget_input, D.reducedRate_input,
      origNet, D.input_target, D.input_source, netDiffFormula,
      ite_eq_right D.input_not_exit, ite_eq_left rfl, ite_eq_right hcne.symm]
    split_ifs <;> ring
  · -- a draining reaction
    have hne : r ≠ D.input := by
      intro hcon2; subst hcon2; exact D.input_not_exit hex
    rw [reducedNet, D.reducedSource_exit hex, D.reducedTarget_exit hex, D.reducedRate_exit hex,
      origNet, D.exits_source r hex, netDiffFormula, ite_eq_left hex, ite_eq_right hne,
      ite_eq_right hcne.symm, massActionMonomial_singleton]
    simp only [eliminatedConcentration]
    split_ifs <;> ring
  · -- a core reaction
    have hsrc : (N.reaction r).source ≠ singletonComplex D.intermediate := hcore.1
    have htgt : (N.reaction r).target ≠ singletonComplex D.intermediate := hcore.2
    have hne : r ≠ D.input := by
      intro hcon2; subst hcon2
      exact htgt (by rw [D.input_target])
    have hexne : r ∉ D.exits := by
      intro hmem
      exact hsrc (D.exits_source r hmem)
    rw [reducedNet, D.reducedSource_core hne hexne, D.reducedTarget_core hne,
      D.reducedRate_core hexne, origNet, netDiffFormula, ite_eq_right hexne, ite_eq_right hne]
    split_ifs <;> ring

/-- Sum of an indicator over a finite set of indices. -/
theorem sum_ite_mem {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Finset ι) (g : ι → ℝ) :
    (∑ r : ι, (if r ∈ s then g r else 0)) = ∑ r ∈ s, g r := by
  classical
  calc (∑ r : ι, (if r ∈ s then g r else 0))
      = ∑ r ∈ (Finset.univ.filter (fun r => r ∈ s)), g r := by
          symm
          rw [Finset.sum_filter]
    _ = ∑ r ∈ s, g r := by
          rw [show (Finset.univ.filter (fun r => r ∈ s)) = s from by
            ext r; simp]

/-- **The summed flux identity.**  Summing the per-reaction identity over all reactions
gives the difference between the reduced and the original complex-flux balance at a core
complex. -/
theorem netDiffFormula_sum (D : OneIntermediate N κ) (x : Concentration S) (c : Complex S) :
    ∑ r : N.R, D.netDiffFormula x c r
      = (D.eliminatedConcentration x - x D.intermediate) * D.exitRateInto c := by
  set P : N.R → ℝ := fun r =>
      κ.k r * ((if (N.reaction r).target = c then D.eliminatedConcentration x else 0)
        - (if (N.reaction r).target = c then x D.intermediate else 0))
      - (if D.inputSource = c then κ.k r * D.eliminatedConcentration x else 0) with hPdef
  set Q : ℝ :=
      (if D.inputSource = c then κ.k D.input * D.inputSource.massActionMonomial x else 0) with hQdef
  have hform : ∀ r : N.R, D.netDiffFormula x c r
      = (if r ∈ D.exits then P r else 0) + (if r = D.input then Q else 0) := by
    intro r
    rw [netDiffFormula, hPdef, hQdef]
  have hP : (∑ r : N.R, (if r ∈ D.exits then P r else 0)) = ∑ r ∈ D.exits, P r := by
    rw [sum_ite_mem]
  have hQ : (∑ r : N.R, (if r = D.input then Q else 0)) = Q := by
    have h : (∑ r : N.R, (if r = D.input then Q else 0))
        = ∑ r : N.R, (if r = D.input then (fun _ => Q) r else 0) := by
      congr 1
    rw [h, Fintype.sum_ite_eq']
  have hP1 : ∑ r ∈ D.exits,
        κ.k r * ((if (N.reaction r).target = c then D.eliminatedConcentration x else 0)
          - (if (N.reaction r).target = c then x D.intermediate else 0))
      = (D.eliminatedConcentration x - x D.intermediate) * D.exitRateInto c := by
    simp only [exitRateInto]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    split_ifs <;> ring
  have hP2 : ∑ r ∈ D.exits,
        (if D.inputSource = c then κ.k r * D.eliminatedConcentration x else 0)
      = D.eliminatedConcentration x * D.totalExitRate
          * (if D.inputSource = c then 1 else 0) := by
    by_cases h : D.inputSource = c
    · simp only [h, ite_true, mul_one, totalExitRate]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
    · simp [h]
  have hQ2 : Q = D.eliminatedConcentration x * D.totalExitRate
          * (if D.inputSource = c then 1 else 0) := by
    rw [hQdef]
    by_cases h : D.inputSource = c
    · rw [ite_eq_left h, ite_eq_left h, mul_one]
      exact (D.eliminatedConcentration_eq x).symm
    · rw [ite_eq_right h, ite_eq_right h]
      simp
  calc (∑ r : N.R, D.netDiffFormula x c r)
      = ∑ r : N.R, ((if r ∈ D.exits then P r else 0) + (if r = D.input then Q else 0)) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [hform r]
    _ = (∑ r : N.R, (if r ∈ D.exits then P r else 0))
        + (∑ r : N.R, (if r = D.input then Q else 0)) := by rw [Finset.sum_add_distrib]
    _ = ∑ r ∈ D.exits, P r + Q := by rw [hP, hQ]
    _ = (∑ r ∈ D.exits, κ.k r * ((if (N.reaction r).target = c then
            D.eliminatedConcentration x else 0)
          - (if (N.reaction r).target = c then x D.intermediate else 0)))
        - ∑ r ∈ D.exits, (if D.inputSource = c then κ.k r * D.eliminatedConcentration x else 0)
        + Q := by
          rw [hPdef, Finset.sum_sub_distrib]
    _ = (D.eliminatedConcentration x - x D.intermediate) * D.exitRateInto c := by
      rw [hP1, hP2, hQ2]
      ring


/-- The original network's complex-flux balance at `c` is the sum of the per-reaction net
fluxes. -/
theorem origNet_sum (κ : N.RateConstants) (x : Concentration S) (c : Complex S) :
    N.inflow κ x c - N.outflow κ x c = ∑ r : N.R, origNet κ x c r := by
  unfold Network.inflow Network.outflow origNet
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Network.massActionRate]

/-- The reduced network's complex-flux balance at `c` is the sum of the per-reaction net
fluxes. -/
theorem reducedNet_sum (D : OneIntermediate N κ) (x : Concentration S) (c : Complex S) :
    D.reducedNetwork.inflow D.reducedRateConstants x c
      - D.reducedNetwork.outflow D.reducedRateConstants x c
      = ∑ r : N.R, D.reducedNet x c r := by
  unfold Network.inflow Network.outflow
  simp only [reducedNetwork, Network.massActionRate, reducedRateConstants, reducedNet]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rfl

/-- **The flux comparison.**  At a core complex `c`, the reduced network's complex-flux
balance differs from the original one exactly by the misbalance of the intermediate
species, weighted by the total rate constant of the draining reactions into `c`. -/
theorem flux_difference (D : OneIntermediate N κ) (x : Concentration S) (c : Complex S)
    (hcne : c ≠ singletonComplex D.intermediate) :
    D.reducedNetwork.inflow D.reducedRateConstants x c
      - D.reducedNetwork.outflow D.reducedRateConstants x c
      = (N.inflow κ x c - N.outflow κ x c)
        + (D.eliminatedConcentration x - x D.intermediate) * D.exitRateInto c := by
  have h1 : (∑ r : N.R, D.reducedNet x c r) - (∑ r : N.R, origNet κ x c r)
      = (D.eliminatedConcentration x - x D.intermediate) * D.exitRateInto c := by
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl (fun r _ => D.netDiff_summand x c hcne r)]
    exact D.netDiffFormula_sum x c
  rw [reducedNet_sum, origNet_sum]
  linarith


/-- Sum of a predicate indicator over a finite set of indices. -/
theorem sum_ite_pred {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → Prop) [DecidablePred p]
    (g : ι → ℝ) :
    (∑ r : ι, (if p r then g r else 0)) = ∑ r ∈ (Finset.univ.filter p), g r := by
  classical
  rw [show (∑ r : ι, (if p r then g r else 0))
      = ∑ r : ι, (if r ∈ (Finset.univ.filter p) then g r else 0) by
        apply Finset.sum_congr rfl
        intro r _
        by_cases hp : p r <;> simp [hp]]
  rw [sum_ite_mem]

/-- The only reaction of `N` whose target is the intermediate complex is the feeding
reaction. -/
theorem filter_target_eq (D : OneIntermediate N κ) :
    Finset.univ.filter (fun r : N.R =>
        (N.reaction r).target = singletonComplex D.intermediate) = {D.input} := by
  ext r
  constructor
  · intro h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    rcases D.exhaustive r with hcon | hex | hcore
    · subst hcon
      exact Finset.mem_singleton_self D.input
    · exact (D.exits_target_ne r hex h).elim
    · exact (hcore.2 h).elim
  · intro h
    simp only [Finset.mem_singleton] at h
    subst h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact D.input_target

/-- The reactions of `N` whose source is the intermediate complex are exactly the draining
reactions. -/
theorem filter_source_eq (D : OneIntermediate N κ) :
    Finset.univ.filter (fun r : N.R =>
        (N.reaction r).source = singletonComplex D.intermediate) = D.exits := by
  ext r
  constructor
  · intro h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    rcases D.exhaustive r with hcon | hex | hcore
    · subst hcon
      exact (D.inputSource_ne (by rw [← D.input_source]; exact h)).elim
    · exact hex
    · exact (hcore.1 h).elim
  · intro h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact D.exits_source r h

/-- **The complex-flux balance at the intermediate complex.**  The intermediate complex
receives the feeding flux and loses the draining flux. -/
theorem fluxBalance_intermediate (D : OneIntermediate N κ) (x : Concentration S) :
    N.inflow κ x (singletonComplex D.intermediate)
      - N.outflow κ x (singletonComplex D.intermediate)
      = κ.k D.input * D.inputSource.massActionMonomial x
        - D.totalExitRate * x D.intermediate := by
  have h1 : (∑ r : N.R, (if (N.reaction r).target = singletonComplex D.intermediate then
        κ.k r * (N.reaction r).source.massActionMonomial x else 0))
      = κ.k D.input * D.inputSource.massActionMonomial x := by
    rw [sum_ite_pred (p := fun r => (N.reaction r).target = singletonComplex D.intermediate),
      D.filter_target_eq, Finset.sum_singleton, D.input_source]
  have h2 : (∑ r : N.R, (if (N.reaction r).source = singletonComplex D.intermediate then
        κ.k r * (N.reaction r).source.massActionMonomial x else 0))
      = D.totalExitRate * x D.intermediate := by
    rw [sum_ite_pred (p := fun r => (N.reaction r).source = singletonComplex D.intermediate),
      D.filter_source_eq]
    have hkey : ∀ r ∈ D.exits,
        κ.k r * (N.reaction r).source.massActionMonomial x = κ.k r * x D.intermediate := by
      intro r hr
      rw [D.exits_source r hr, massActionMonomial_singleton]
    rw [Finset.sum_congr rfl hkey, ← Finset.sum_mul,
      Finset.sum_congr rfl (fun r _ => by ring), totalExitRate]
  unfold Network.inflow Network.outflow
  simp only [Network.massActionRate]
  rw [h1, h2]


/-- The reaction of the reduced network at `r`. -/
theorem reducedNetwork_reaction (D : OneIntermediate N κ) (r : N.R) :
    D.reducedNetwork.reaction r = ⟨D.reducedSource r, D.reducedTarget r⟩ := rfl

/-- Every core complex of the original network is a complex of the reduced network. -/
theorem mem_reducedComplexes (D : OneIntermediate N κ) {c : Complex S}
    (hc : c ∈ N.complexes) (hcne : c ≠ singletonComplex D.intermediate) :
    c ∈ D.reducedNetwork.complexes := by
  have hc' : c ∈ (Finset.univ.image (fun r : N.R => (N.reaction r).source))
      ∪ (Finset.univ.image (fun r : N.R => (N.reaction r).target)) := by
    simpa [Network.complexes] using hc
  simp only [reducedNetwork, Network.complexes]
  rcases Finset.mem_union.mp hc' with h | h
  · rcases Finset.mem_image.mp h with ⟨r, _, rfl⟩
    rcases D.exhaustive r with hcon | hex | hcore
    · subst hcon
      rw [D.input_source]
      have hmem : D.inputSource = D.reducedSource D.input := by rw [D.reducedSource_input]
      rw [hmem]
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    · exact (hcne (D.exits_source r hex)).elim
    · rw [← D.reducedSource_core
        (fun hcon2 => (hcore.2 (by rw [hcon2, D.input_target])).elim)
        (fun hmem => (hcore.1 (D.exits_source r hmem)).elim)]
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  · rcases Finset.mem_image.mp h with ⟨r, _, rfl⟩
    rcases D.exhaustive r with hcon | hex | hcore
    · subst hcon
      exact (hcne (by rw [D.input_target])).elim
    · rw [← D.reducedTarget_exit hex]
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    · rw [← D.reducedTarget_core
        (fun hcon2 => (hcore.2 (by rw [hcon2, D.input_target])).elim)]
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))

/-- Every complex of the reduced network is a core complex of the original network. -/
theorem mem_core_of_mem_reducedComplexes (D : OneIntermediate N κ) {c : Complex S}
    (hc : c ∈ D.reducedNetwork.complexes) :
    c ∈ N.complexes ∧ c ≠ singletonComplex D.intermediate := by
  simp only [reducedNetwork, Network.complexes] at hc
  rcases Finset.mem_union.mp hc with h | h
  · rcases Finset.mem_image.mp h with ⟨r, _, rfl⟩
    rcases D.exhaustive r with hcon | hex | hcore
    · subst hcon
      rw [D.reducedSource_input]
      exact ⟨by rw [← D.input_source]; exact N.source_mem_complexes D.input, D.inputSource_ne⟩
    · rw [D.reducedSource_exit hex]
      exact ⟨by rw [← D.input_source]; exact N.source_mem_complexes D.input, D.inputSource_ne⟩
    · rw [D.reducedSource_core
        (fun hcon2 => (hcore.2 (by rw [hcon2, D.input_target])).elim)
        (fun hmem => (hcore.1 (D.exits_source r hmem)).elim)]
      exact ⟨N.source_mem_complexes r, hcore.1⟩
  · rcases Finset.mem_image.mp h with ⟨r, _, rfl⟩
    rcases D.exhaustive r with hcon | hex | hcore
    · subst hcon
      rw [D.reducedTarget_input]
      exact ⟨by rw [← D.input_source]; exact N.source_mem_complexes D.input, D.inputSource_ne⟩
    · rw [D.reducedTarget_exit hex]
      exact ⟨N.target_mem_complexes r, D.exits_target_ne r hex⟩
    · rw [D.reducedTarget_core
        (fun hcon2 => (hcore.2 (by rw [hcon2, D.input_target])).elim)]
      exact ⟨N.target_mem_complexes r, hcore.2⟩

/-- **The mass-action field in the intermediate coordinate.**  The mass-action vector field
in the coordinate of the intermediate species equals the complex-flux balance at the
intermediate complex: only the feeding and the draining reactions contribute to it. -/
theorem vectorField_intermediate (D : OneIntermediate N κ) (x : Concentration S) :
    N.massActionVectorField κ x D.intermediate
      = N.inflow κ x (singletonComplex D.intermediate)
        - N.outflow κ x (singletonComplex D.intermediate) := by
  rw [N.massActionVectorField_eq κ x, N.complexMap_apply]
  rw [Finset.sum_congr rfl (fun c _ => by rw [N.kineticMap_complexMonomial_apply])]
  have hmem : singletonComplex D.intermediate ∈ N.complexes := D.structural.1 _ (by simp)
  rw [Finset.sum_eq_single ⟨singletonComplex D.intermediate, hmem⟩
    (fun b _ hne => by
      have hb : b.val ≠ singletonComplex D.intermediate := by
        intro hcon
        apply hne
        exact Subtype.ext_iff.mpr hcon
      rw [D.core_of_ne b.property hb]
      ring)
    (by simp)]
  simp only [singletonComplex_self]
  norm_num

/-- **The intermediate coordinate of a steady state (Feliu–Wiuf 2012).**  At any mass-action
steady state of the original network the intermediate species sits at its eliminated
steady-state value — the value `k₁ /(Σ_l k_l) · x^y` at which the intermediate is removed
and the reduced network is obtained.  This is the ingredient that identifies the
steady-state set of the original network with the lift of the steady-state set of the
reduced network. -/
theorem steadyState_intermediate_eliminated (D : OneIntermediate N κ) (x : Concentration S)
    (hss : N.IsMassActionSteadyState κ x) :
    x D.intermediate = D.eliminatedConcentration x := by
  have hfield := hss D.intermediate
  rw [D.vectorField_intermediate x, D.fluxBalance_intermediate x] at hfield
  have h1 : x D.intermediate * D.totalExitRate
      = D.eliminatedConcentration x * D.totalExitRate := by
    have h2 : D.totalExitRate * x D.intermediate
        = κ.k D.input * D.inputSource.massActionMonomial x := by linarith [hfield]
    rw [← D.eliminatedConcentration_eq] at h2
    calc x D.intermediate * D.totalExitRate
        = D.totalExitRate * x D.intermediate := mul_comm _ _
      _ = D.eliminatedConcentration x * D.totalExitRate := h2
  exact mul_right_cancel₀ (D.totalExitRate_pos.ne') h1

/-- **The one-intermediate reduction preserves the complex-balanced equilibria.**  For a
network with a single intermediate species, eliminating the intermediate by the
Schur-complement construction produces a reduced network with exactly the same
complex-balanced equilibria. -/
theorem singleIntermediate_reduction_preserves_complexBalance
    (D : OneIntermediate N κ) (x : Concentration S) :
    N.IsComplexBalanced κ x ↔
      (D.reducedNetwork.IsComplexBalanced D.reducedRateConstants x
        ∧ x D.intermediate = D.eliminatedConcentration x) := by
  constructor
  · intro h
    rw [IsComplexBalanced] at h
    have hinter : N.inflow κ x (singletonComplex D.intermediate)
        - N.outflow κ x (singletonComplex D.intermediate) = 0 := by
      have hbal := h (singletonComplex D.intermediate)
        (D.structural.1 D.intermediate (by simp))
      linarith
    rw [D.fluxBalance_intermediate x] at hinter
    have hkey : x D.intermediate = D.eliminatedConcentration x := by
      have h1 : x D.intermediate * D.totalExitRate
          = D.eliminatedConcentration x * D.totalExitRate := by
        have h2 : D.totalExitRate * x D.intermediate
            = κ.k D.input * D.inputSource.massActionMonomial x := by
          linarith [hinter]
        rw [← D.eliminatedConcentration_eq] at h2
        calc x D.intermediate * D.totalExitRate
            = D.totalExitRate * x D.intermediate := mul_comm _ _
          _ = D.eliminatedConcentration x * D.totalExitRate := h2
      exact mul_right_cancel₀ (D.totalExitRate_pos.ne') h1
    have hred : ∀ c ∈ D.reducedNetwork.complexes,
        D.reducedNetwork.inflow D.reducedRateConstants x c
          = D.reducedNetwork.outflow D.reducedRateConstants x c := by
      intro c hc
      have hc1 := D.mem_core_of_mem_reducedComplexes hc
      have hcore := h c hc1.1
      have hcore' : D.reducedNetwork.inflow D.reducedRateConstants x c
          - D.reducedNetwork.outflow D.reducedRateConstants x c = 0 := by
        rw [D.flux_difference x c hc1.2]
        simp only [hkey, sub_self, zero_mul, add_zero]
        linarith [hcore]
      exact sub_eq_zero.mp hcore'
    rw [IsComplexBalanced]
    exact ⟨hred, hkey⟩
  · rintro ⟨hred, hkey⟩
    rw [IsComplexBalanced] at hred
    rw [IsComplexBalanced]
    intro c hc
    by_cases hcne : c = singletonComplex D.intermediate
    · subst hcne
      have hbal : N.inflow κ x (singletonComplex D.intermediate)
          - N.outflow κ x (singletonComplex D.intermediate) = 0 := by
        rw [D.fluxBalance_intermediate x, hkey, ← D.eliminatedConcentration_eq]
        ring
      linarith
    · have hc' := D.mem_reducedComplexes hc hcne
      have hcore := hred c hc'
      have hcore' : D.reducedNetwork.inflow D.reducedRateConstants x c
          - D.reducedNetwork.outflow D.reducedRateConstants x c = 0 := sub_eq_zero.mpr hcore
      rw [D.flux_difference x c hcne] at hcore'
      simp only [hkey, sub_self, zero_mul, add_zero] at hcore'
      exact sub_eq_zero.mp hcore'

/-- **The toric reduction preserves the complex-balanced equilibria.**  If the intermediate
species of a network are eliminated by the Schur-complement construction, the reduced network
has the same complex-balanced equilibria as the original network: a concentration is
complex-balanced in `N` exactly when it is complex-balanced in the reduced network *and* the
intermediate species sits at its eliminated steady-state value. -/
def ToricReductionPreservesComplexBalance (N : Network S) (H : Finset S) : Prop :=
  ∀ (κ : N.RateConstants) (D : N.OneIntermediate κ), D.intermediate ∈ H →
    ∀ x : Concentration S,
      N.IsComplexBalanced κ x ↔
        (D.reducedNetwork.IsComplexBalanced D.reducedRateConstants x
          ∧ x D.intermediate = D.eliminatedConcentration x)

/-- **The one-intermediate instance of the toric reduction contract.**  Every network with a
single intermediate species satisfies `ToricReductionPreservesComplexBalance`. -/
theorem toricReductionPreservesComplexBalance_of_one (N : Network S) (H : Finset S)
    (κ : N.RateConstants) (_D : N.OneIntermediate κ) :
    ToricReductionPreservesComplexBalance N H := by
  intro κ' D' _ x
  exact OneIntermediate.singleIntermediate_reduction_preserves_complexBalance D' x

end OneIntermediate

end Network
end CRNT

/-!
## A worked instance: the cycle `A → B → C → A`
-/

namespace CRNT.Examples.ToricReductionCycle

set_option backward.isDefEq.respectTransparency false

open CRNT CRNT.Network

/-- The species type of the cycle. -/
abbrev Species := Fin 3

/-- The complex `A`. -/
def cA : Complex Species := ![1, 0, 0]
/-- The complex `B`. -/
def cB : Complex Species := ![0, 1, 0]
/-- The complex `C`. -/
def cC : Complex Species := ![0, 0, 1]

/-- The reaction `A → B`. -/
def rAB : Reaction Species := ⟨cA, cB⟩
/-- The reaction `B → C`. -/
def rBC : Reaction Species := ⟨cB, cC⟩
/-- The reaction `C → A`. -/
def rCA : Reaction Species := ⟨cC, cA⟩

/-- The reaction list of the cycle `A → B → C → A`. -/
def rxn : Fin 3 → Reaction Species
  | 0 => rAB
  | 1 => rBC
  | 2 => rCA

/-- The network `A → B → C → A`. -/
def N : Network Species where
  R := Fin 3
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := rxn

/-- The complexes of the cycle. -/
theorem complexes_eq : N.complexes = {cA, cB, cC} := by decide

/-- The rate constants of the cycle, all equal to `1`. -/
def κ : N.RateConstants where
  k := fun _ => 1
  positive := by intro r; norm_num

/-- The reduction data of the cycle with `B` intermediate: `A → B` feeds the intermediate
and `B → C` drains it. -/
def D : N.OneIntermediate κ where
  intermediate := (1 : Fin 3)
  input := (0 : Fin 3)
  exits := {(1 : Fin 3)}
  inputSource := cA
  structural := ⟨by decide, by decide⟩
  input_target := by decide
  input_source := by decide
  inputSource_ne := by decide
  exits_source := by decide
  exits_target_ne := by decide
  exhaustive := by
    intro r
    fin_cases r
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (Finset.mem_singleton_self (1 : Fin 3)))
    · exact Or.inr (Or.inr ⟨by decide, by decide⟩)
  exits_ne := by decide

/-- **The reduced network of the cycle.**  Eliminating the intermediate `B` turns the
feeding reaction `A → B` into the inert self-loop `A → A`. -/
theorem reduced_reaction_input : (D).reducedNetwork.reaction D.input = ⟨cA, cA⟩ := by
  rw [OneIntermediate.reducedNetwork_reaction, D.reducedSource_input, D.reducedTarget_input]
  rfl

/-- **The draining reaction of the cycle is contracted onto the feeding complex.**  The
reaction `B → C` becomes `A → C`, with the effective rate `k₁ k₂ /(k₂) = k₁`. -/
theorem reduced_reaction_exit (r : N.R) (hr : r ∈ D.exits) :
    (D).reducedNetwork.reaction r = ⟨cA, (N.reaction r).target⟩ := by
  rw [OneIntermediate.reducedNetwork_reaction, D.reducedSource_exit hr, D.reducedTarget_exit hr]
  rfl

/-- Every reaction of the cycle that is neither the feeding nor a draining one — that is,
`C → A` — is left untouched by the reduction. -/
theorem reduced_reaction_core (r : N.R) (hr : r ≠ D.input) (hr2 : r ∉ D.exits) :
    (D).reducedNetwork.reaction r = N.reaction r := by
  rw [OneIntermediate.reducedNetwork_reaction, D.reducedSource_core hr hr2,
    D.reducedTarget_core hr]

/-- **The two networks have the same complex-balanced equilibria.**  This is the toric
reduction applied to the cycle `A → B → C → A`: the reduced network `A ⇄ C` has exactly the
same complex-balanced equilibria as the original three-cycle, with the intermediate `B`
sitting at its eliminated value `k₁ /(k₂) · x^A`. -/
theorem same_complexBalanced (x : Concentration Species) :
    N.IsComplexBalanced κ x ↔
      ((D).reducedNetwork.IsComplexBalanced (D).reducedRateConstants x
        ∧ x 1 = (D).eliminatedConcentration x) :=
  OneIntermediate.singleIntermediate_reduction_preserves_complexBalance D x


/-- The all-ones concentration is complex-balanced for the cycle with all rate constants
equal to `1`: the three complexes `A`, `B`, `C` each have unit inflow and unit outflow. -/
theorem isComplexBalanced : N.IsComplexBalanced κ (fun _ => 1) := by
  rw [IsComplexBalanced, complexes_eq]
  intro c hc
  rcases Finset.mem_insert.mp hc with h | hc
  · subst h
    simp only [N, κ, Network.inflow, Network.outflow, Network.massActionRate,
      Complex.massActionMonomial, rxn, rAB, rBC, rCA, cA, cB, cC]
    simp only [Fin.sum_univ_succ]
    norm_num
  · rcases Finset.mem_insert.mp hc with h | hc
    · subst h
      simp only [N, κ, Network.inflow, Network.outflow, Network.massActionRate,
        Complex.massActionMonomial, rxn, rAB, rBC, rCA, cA, cB, cC]
      simp only [Fin.sum_univ_succ]
      norm_num
    · rw [Finset.mem_singleton] at hc
      subst hc
      simp only [N, κ, Network.inflow, Network.outflow, Network.massActionRate,
        Complex.massActionMonomial, rxn, rAB, rBC, rCA, cA, cB, cC]
      simp only [Fin.sum_univ_succ]
      norm_num

end CRNT.Examples.ToricReductionCycle

/-! The principal results are closed over the three standard axioms. -/

#print axioms CRNT.Network.OneIntermediate.singleIntermediate_reduction_preserves_complexBalance
#print axioms CRNT.Network.OneIntermediate.steadyState_intermediate_eliminated
#print axioms CRNT.Network.OneIntermediate.toricReductionPreservesComplexBalance_of_one
#print axioms CRNT.Network.OneIntermediate.flux_difference
#print axioms CRNT.Network.OneIntermediate.netDiff_summand
