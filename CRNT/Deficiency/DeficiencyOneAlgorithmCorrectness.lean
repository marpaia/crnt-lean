import CRNT.Deficiency.DeficiencyOneAlgorithm
import CRNT.Multistationarity.DeficiencyOneAlgorithm
import CRNT.Deficiency.Confluence
import CRNT.Decision.Reachability
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import CRNT.Decision.ComputableDeficiency

/-!
# Conditional bridges from DOA shelf/run data to semantic feasibility

A supplied run together with shelf-wise positive confluence fluxes and the
displayed placement/equal-pairing conditions yields semantic feasibility and
multistationarity capacity. These auxiliary data are substantial hypotheses.
The file does not compute them from every run, give a finite decision procedure,
or prove full published Deficiency One Algorithm correctness/completeness.
-/

namespace CRNT

namespace Network

open scoped BigOperators
open Finset

section General

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

/-! ### The discrete data of a run of the presented algorithm -/

/-- **The discrete data of a run of the Deficiency One Algorithm**: a nonzero *confluence
vector* `g` on the complexes, a *shelf partition* `sp` of the complexes, and the log-ratio `μ`
of the two candidate steady states.  The log-ratio is nonzero, sign-compatible with the
stoichiometric subspace, and meets the placement rules read against the confluence vector. -/
structure DOARun (N : Network S) where
  /-- The confluence vector of the run. -/
  g : N.ComplexIdx → ℝ
  /-- The confluence vector lies in the cut space. -/
  g_isConfluence : N.IsConfluenceVector g
  /-- The confluence vector is nonzero. -/
  g_ne_zero : g ≠ 0
  /-- The shelf partition of the complexes. -/
  sp : N.ShelfPartition
  /-- The log-ratio `μ = log y − log x` of the two candidate steady states. -/
  μ : S → ℝ
  /-- The log-ratio is nonzero: the two candidate steady states differ. -/
  μ_ne_zero : μ ≠ 0
  /-- The log-ratio is sign-compatible with the stoichiometric subspace. -/
  sign_compatible : N.SignCompatibleWithStoich μ
  /-- The placement rules are met. -/
  imposes : sp.imposes g μ

/-- **The data of a run of the Deficiency One Algorithm**, assembled from its parts. -/
def DOARun.ofData (g : N.ComplexIdx → ℝ) (hg : N.IsConfluenceVector g)
    (hg0 : g ≠ 0) (sp : N.ShelfPartition) (μ : S → ℝ) (hμ : μ ≠ 0)
    (hsc : N.SignCompatibleWithStoich μ) (himp : sp.imposes g μ) : DOARun N :=
  { g := g, g_isConfluence := hg, g_ne_zero := hg0, sp := sp, μ := μ,
    μ_ne_zero := hμ, sign_compatible := hsc, imposes := himp }

/-- **The presented algorithm's verdict is the existence of a run.**  The repository's
`N.DOAAffirmsCapacity` is exactly the existence of the discrete data above. -/
theorem doaAffirmsCapacity_iff_nonempty_run :
    N.DOAAffirmsCapacity ↔ Nonempty (DOARun N) := by
  constructor
  · rintro ⟨g, hg, hg0, sp, μ, hμ0, hsc, himp⟩
    exact ⟨DOARun.ofData g hg hg0 sp μ hμ0 hsc himp⟩
  · rintro ⟨run⟩
    exact ⟨run.g, run.g_isConfluence, run.g_ne_zero, run.sp, run.μ, run.μ_ne_zero,
      run.sign_compatible, run.imposes⟩

/-- **The verdict yields a nonzero log-ratio.** -/
theorem doaAffirmsCapacity_exists_mu (h : N.DOAAffirmsCapacity) :
    ∃ μ : S → ℝ, μ ≠ 0 ∧ N.SignCompatibleWithStoich μ := by
  obtain ⟨run⟩ := (doaAffirmsCapacity_iff_nonempty_run).mp h
  exact ⟨run.μ, run.μ_ne_zero, run.sign_compatible⟩

/-! ### The quantitative content of the placement rules -/

/-- **The middle shelf is a level set of the log-ratio**: two complexes on the middle shelf
pair equally with `μ`. -/
theorem DOARun.pairing_eq_of_middle (run : DOARun N) {y y' : N.ComplexIdx}
    (hy : run.sp.shelf y = Shelf.middle) (hy' : run.sp.shelf y' = Shelf.middle) :
    complexPairing y.val run.μ = complexPairing y'.val run.μ :=
  run.imposes.2.1 y y' hy hy'

/-- **The shelves are ordered by the log-ratio**: a complex on a lower shelf pairs strictly
below a complex on a higher one. -/
theorem DOARun.pairing_lt_of_higher (run : DOARun N) {y y' : N.ComplexIdx}
    (h : (run.sp.shelf y').rank < (run.sp.shelf y).rank) :
    complexPairing y'.val run.μ < complexPairing y.val run.μ :=
  run.imposes.1 y y' h

/-- **The bridge lemma of the shelf enumeration.**  The reactions whose *source* complex lies on
the middle shelf have sources which pair equally with the log-ratio: the placement rules make
the middle shelf a level set of `μ`, and the source pairing is what enters the upper balance
equation of the algorithm. -/
theorem DOARun.source_pairing_eq_of_middle (run : DOARun N) {r r' : N.R}
    (hr : run.sp.shelf (N.sourceIdx r) = Shelf.middle)
    (hr' : run.sp.shelf (N.sourceIdx r') = Shelf.middle) :
    complexPairing (N.reaction r).source run.μ = complexPairing (N.reaction r').source run.μ := by
  have h := run.imposes.2.1 (N.sourceIdx r) (N.sourceIdx r') hr hr'
  exact h

/-- **The bridge lemma, in the form of a whole shelf.**  All the sources of the reactions of a
shelf whose sources lie on the middle shelf pair equally with the log-ratio. -/
theorem DOARun.source_pairing_const_of_middle (run : DOARun N) {sh : Finset N.R}
    (hsh : ∀ r ∈ sh, run.sp.shelf (N.sourceIdx r) = Shelf.middle) :
    ∃ c : ℝ, ∀ r ∈ sh, complexPairing (N.reaction r).source run.μ = c := by
  classical
  by_cases hne : sh.Nonempty
  · obtain ⟨r₀, hr₀⟩ := hne
    refine ⟨complexPairing (N.reaction r₀).source run.μ, ?_⟩
    intro r hr
    exact run.source_pairing_eq_of_middle (hsh r hr) (hsh r₀ hr₀)
  · have hsh : sh = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst hsh
    refine ⟨0, ?_⟩
    intro r hr
    simp at hr

/-- **A candidate solution of the Deficiency One Algorithm**, assembled from its parts. -/
def DOACandidate.ofData (N : Network S) (μ : S → ℝ) (hμ : μ ≠ 0) (α : N.R → ℝ)
    (hα : ∀ r, 0 < α r) (hsc : N.SignCompatibleWithStoich μ)
    (hlb : ∀ s, ∑ r, α r * N.reactionVector r s = 0)
    (hub : ∀ s, ∑ r, α r * Real.exp (complexPairing (N.reaction r).source μ) *
      N.reactionVector r s = 0) : DOACandidate N :=
  { μ := μ, α := α, μ_ne_zero := hμ, α_pos := hα, sign_compatible := hsc,
    lower_balance := hlb, upper_balance := hub }

/-! ### The shelf-wise confluence vectors -/

/-- **The shelf-wise confluence vectors of a Deficiency One Algorithm run.**  A *shelf* here is
a set of reactions; a *shelf decomposition* is a partition of the reaction set into shelves;
the *confluence vector* of a shelf is a flux which is supported on the shelf, strictly positive
on it, and which balances the shelf at the lower state,
`∑_{r ∈ sh} λ_r (y'_r − y_r) = 0`.  This is the datum which the presented algorithm has to
produce: Feinberg's shelves are *dependent* sets of reactions, and their confluence vectors are
the positive dependencies of their reaction vectors. -/
structure DOAShelfFluxes (N : Network S) where
  /-- The shelves: a partition of the reaction set. -/
  shelves : Finset (Finset N.R)
  /-- **Covering**: every reaction of the network lies on some shelf. -/
  cover : ∀ r : N.R, ∃ sh ∈ shelves, r ∈ sh
  /-- **Disjointness**: two distinct shelves are disjoint. -/
  disjoint : ∀ sh ∈ shelves, ∀ sh' ∈ shelves, sh ≠ sh' → sh ∩ sh' = ∅
  /-- The confluence vector of each shelf. -/
  flux : Finset N.R → N.R → ℝ
  /-- **Support**: the confluence vector of a shelf vanishes off the shelf. -/
  support : ∀ sh ∈ shelves, ∀ r, r ∉ sh → flux sh r = 0
  /-- **Positivity**: the confluence vector of a shelf is strictly positive on the shelf. -/
  positive : ∀ sh ∈ shelves, ∀ r ∈ sh, 0 < flux sh r
  /-- **The lower balance on the shelf**: `∑_{r ∈ sh} λ_r (y'_r − y_r) = 0`. -/
  lower_balance : ∀ sh ∈ shelves, ∀ s, ∑ r ∈ sh, flux sh r * N.reactionVector r s = 0

/-- The confluence vector of a shelf is nonnegative on every reaction. -/
theorem DOAShelfFluxes.nonneg {N : Network S} {d : DOAShelfFluxes N}
    (sh : Finset N.R) (hsh : sh ∈ d.shelves) (r : N.R) : 0 ≤ d.flux sh r := by
  by_cases hmem : r ∈ sh
  · exact (d.positive sh hsh r hmem).le
  · exact le_of_eq (d.support sh hsh r hmem).symm

/-- **The global flux of a shelf decomposition**: the sum of the shelf fluxes.  It is the flux
which witnesses the capacity. -/
def DOAShelfFluxes.globalFlux {N : Network S} (d : DOAShelfFluxes N) : N.R → ℝ :=
  fun r => ∑ sh ∈ d.shelves, d.flux sh r

/-- **The global flux is strictly positive**: the shelves cover the reaction set, and every shelf
flux is strictly positive on its shelf. -/
theorem DOAShelfFluxes.globalFlux_pos {N : Network S} {d : DOAShelfFluxes N} (r : N.R) :
    0 < d.globalFlux r := by
  classical
  obtain ⟨sh, hsh, hmem⟩ := d.cover r
  refine Finset.sum_pos' (fun sh' hsh' => d.nonneg sh' hsh' r)
    ⟨sh, hsh, d.positive sh hsh r hmem⟩

/-- **The shelf's lower balance is a global balance**: the flux of a shelf vanishes off the
shelf, so the sum over all reactions equals the sum over the shelf. -/
theorem DOAShelfFluxes.sum_eq_zero {N : Network S} {d : DOAShelfFluxes N}
    {sh : Finset N.R} (hsh : sh ∈ d.shelves) (s : S) :
    ∑ r, d.flux sh r * N.reactionVector r s = 0 := by
  classical
  calc ∑ r, d.flux sh r * N.reactionVector r s
      = ∑ r ∈ (Finset.univ : Finset N.R), d.flux sh r * N.reactionVector r s := rfl
    _ = ∑ r ∈ sh, d.flux sh r * N.reactionVector r s := by
      symm
      refine Finset.sum_subset (Finset.subset_univ sh) ?_
      intro r _ hr
      rw [d.support sh hsh r hr]
      simp
    _ = 0 := d.lower_balance sh hsh s

/-- **The global flux satisfies the lower balance**: it is the sum of the shelf fluxes, and each
shelf balances on its own. -/
theorem DOAShelfFluxes.globalFlux_lower_balance {N : Network S} {d : DOAShelfFluxes N} (s : S) :
    ∑ r, d.globalFlux r * N.reactionVector r s = 0 := by
  classical
  calc ∑ r, d.globalFlux r * N.reactionVector r s
      = ∑ r, (∑ sh ∈ d.shelves, d.flux sh r) * N.reactionVector r s := rfl
    _ = ∑ r ∈ (Finset.univ : Finset N.R), ∑ sh ∈ d.shelves,
        d.flux sh r * N.reactionVector r s := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.sum_mul]
    _ = ∑ sh ∈ d.shelves, ∑ r ∈ (Finset.univ : Finset N.R),
        d.flux sh r * N.reactionVector r s := Finset.sum_comm
    _ = 0 := by
      refine Finset.sum_eq_zero fun sh hsh => ?_
      exact d.sum_eq_zero hsh s

/-- **The upper balance on a shelf whose sources pair equally with the log-ratio.**  If all the
sources of the reactions of the shelf have the same pairing with `μ`, the exponential factor
`e^{⟨y_r, μ⟩}` is constant on the shelf, and the upper balance is the lower balance. -/
theorem DOAShelfFluxes.shelf_upper_balance {N : Network S} {d : DOAShelfFluxes N} (μ : S → ℝ)
    (sh : Finset N.R) (hsh : sh ∈ d.shelves)
    (hp : ∀ r ∈ sh, ∀ r' ∈ sh,
      complexPairing (N.reaction r).source μ = complexPairing (N.reaction r').source μ)
    (s : S) :
    ∑ r ∈ sh, d.flux sh r * Real.exp (complexPairing (N.reaction r).source μ) *
      N.reactionVector r s = 0 := by
  classical
  by_cases hne : sh.Nonempty
  · obtain ⟨r₀, hr₀⟩ := hne
    have hexp : ∀ r ∈ sh, Real.exp (complexPairing (N.reaction r).source μ) =
        Real.exp (complexPairing (N.reaction r₀).source μ) := by
      intro r hr
      rw [hp r hr r₀ hr₀]
    calc ∑ r ∈ sh, d.flux sh r * Real.exp (complexPairing (N.reaction r).source μ) *
          N.reactionVector r s
        = ∑ r ∈ sh, (Real.exp (complexPairing (N.reaction r₀).source μ) *
            (d.flux sh r * N.reactionVector r s)) := by
          refine Finset.sum_congr rfl fun r hr => ?_
          rw [hexp r hr]
          ring
      _ = Real.exp (complexPairing (N.reaction r₀).source μ) *
            ∑ r ∈ sh, d.flux sh r * N.reactionVector r s := by rw [Finset.mul_sum]
      _ = 0 := by rw [d.lower_balance sh hsh s]; simp
  · have hsh : sh = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst hsh
    simp

/-- **The global flux satisfies the upper balance** when the sources of the reactions of each
shelf pair equally with the log-ratio. -/
theorem DOAShelfFluxes.globalFlux_upper_balance {N : Network S} {d : DOAShelfFluxes N}
    (μ : S → ℝ)
    (hp : ∀ sh ∈ d.shelves, ∀ r ∈ sh, ∀ r' ∈ sh,
      complexPairing (N.reaction r).source μ = complexPairing (N.reaction r').source μ)
    (s : S) :
    ∑ r, d.globalFlux r * Real.exp (complexPairing (N.reaction r).source μ) *
      N.reactionVector r s = 0 := by
  classical
  calc ∑ r, d.globalFlux r * Real.exp (complexPairing (N.reaction r).source μ) *
      N.reactionVector r s
      = ∑ r, (∑ sh ∈ d.shelves, d.flux sh r) *
          Real.exp (complexPairing (N.reaction r).source μ) * N.reactionVector r s := rfl
    _ = ∑ r ∈ (Finset.univ : Finset N.R), ∑ sh ∈ d.shelves,
          d.flux sh r * Real.exp (complexPairing (N.reaction r).source μ) *
            N.reactionVector r s := by
      refine Finset.sum_congr rfl fun r _ => ?_
      calc (∑ sh ∈ d.shelves, d.flux sh r) *
          Real.exp (complexPairing (N.reaction r).source μ) * N.reactionVector r s
          = (∑ sh ∈ d.shelves, d.flux sh r) *
            (Real.exp (complexPairing (N.reaction r).source μ) * N.reactionVector r s) := by ring
        _ = ∑ sh ∈ d.shelves, d.flux sh r *
            (Real.exp (complexPairing (N.reaction r).source μ) * N.reactionVector r s) :=
          Finset.sum_mul _ _ _
        _ = ∑ sh ∈ d.shelves, d.flux sh r * Real.exp (complexPairing (N.reaction r).source μ) *
            N.reactionVector r s := by
          refine Finset.sum_congr rfl fun sh _ => ?_
          ring
    _ = ∑ sh ∈ d.shelves, ∑ r ∈ (Finset.univ : Finset N.R),
          d.flux sh r * Real.exp (complexPairing (N.reaction r).source μ) *
            N.reactionVector r s := Finset.sum_comm
    _ = 0 := by
      refine Finset.sum_eq_zero fun sh hsh => ?_
      -- the shelf's upper balance, over all reactions
      have h1 : ∑ r, d.flux sh r * Real.exp (complexPairing (N.reaction r).source μ) *
          N.reactionVector r s
          = ∑ r ∈ sh, d.flux sh r * Real.exp (complexPairing (N.reaction r).source μ) *
            N.reactionVector r s := by
        symm
        refine Finset.sum_subset (Finset.subset_univ sh) ?_
        intro r _ hr
        rw [d.support sh hsh r hr]
        simp
      rw [h1]
      exact d.shelf_upper_balance μ sh hsh (hp sh hsh) s

/-! ### The bridge: the presented algorithm and the feasibility test -/

/-- **The algorithmic direction of the Deficiency One Algorithm, in its presented form.**  A run
of the presented algorithm — a nonzero confluence vector, a shelf partition, and a nonzero
sign-compatible log-ratio meeting the placement rules — together with the shelf-wise confluence
vectors, is a feasible system of the algorithm: the global flux is strictly positive and
satisfies the two flux balances. -/
theorem doaRun_doaFeasible (run : DOARun N) (d : DOAShelfFluxes N)
    (hp : ∀ sh ∈ d.shelves, ∀ r ∈ sh, ∀ r' ∈ sh,
      complexPairing (N.reaction r).source run.μ = complexPairing (N.reaction r').source run.μ) :
    N.DOAFeasible := by
  have hα : ∀ r, 0 < d.globalFlux r := d.globalFlux_pos
  have hlb : ∀ s, ∑ r, d.globalFlux r * N.reactionVector r s = 0 := d.globalFlux_lower_balance
  have hub : ∀ s, ∑ r, d.globalFlux r * Real.exp (complexPairing (N.reaction r).source run.μ) *
      N.reactionVector r s = 0 := d.globalFlux_upper_balance run.μ hp
  exact ⟨DOACandidate.ofData N run.μ run.μ_ne_zero d.globalFlux hα run.sign_compatible
    hlb hub⟩

/-- **The shelf partition supplies the pairing condition.**  If the sources of the reactions of
every shelf lie on the middle shelf of the run's shelf partition, then the placement rules make
the sources of each shelf pair equally with the log-ratio. -/
theorem doaRun_doaFeasible_of_middle (run : DOARun N) (d : DOAShelfFluxes N)
    (hsrc : ∀ sh ∈ d.shelves, ∀ r ∈ sh, run.sp.shelf (N.sourceIdx r) = Shelf.middle) :
    N.DOAFeasible := by
  refine doaRun_doaFeasible run d ?_
  intro sh hsh r hr r' hr'
  exact run.source_pairing_eq_of_middle (hsrc sh hsh r hr) (hsrc sh hsh r' hr')

/-- A supplied run, shelf fluxes, and middle-shelf placement imply capacity.
This is a conditional bridge; it does not compute the auxiliary data or decide capacity. -/
theorem doaRun_hasMultistationarityCapacity (run : DOARun N) (d : DOAShelfFluxes N)
    (hsrc : ∀ sh ∈ d.shelves, ∀ r ∈ sh, run.sp.shelf (N.sourceIdx r) = Shelf.middle) :
    N.HasMultistationarityCapacity :=
  N.doaFeasible_implies_capacity (doaRun_doaFeasible_of_middle run d hsrc)

/-- **The presented verdict implies the repository's verdict.**  The run of the presented
algorithm is exactly the data of `N.DOAAffirmsCapacity`. -/
theorem doaRun_implies_affirmsCapacity (run : DOARun N) : N.DOAAffirmsCapacity :=
  (doaAffirmsCapacity_iff_nonempty_run).mpr ⟨run⟩

/-! ### The converse: the capacity is presented by the shelf-wise confluence vectors -/

/-- **The one-shelf confluence vectors of a network**: the whole reaction set is a single shelf
and its confluence vector is the given flux. -/
def oneShelfFluxes (α : N.R → ℝ) (hα : ∀ r, 0 < α r)
    (hflux : ∀ s, ∑ r, α r * N.reactionVector r s = 0) : DOAShelfFluxes N where
  shelves := {Finset.univ}
  cover := by
    intro r
    exact ⟨Finset.univ, by simp, Finset.mem_univ r⟩
  disjoint := by
    intro sh hsh sh' hsh' hne
    have h1 : sh = Finset.univ := Finset.mem_singleton.mp hsh
    have h2 : sh' = Finset.univ := Finset.mem_singleton.mp hsh'
    rw [h1, h2] at hne
    rw [h1, h2]
    exact (hne rfl).elim
  flux := fun sh r => if r ∈ sh then α r else 0
  support := by
    intro sh hsh r hr
    have h1 : sh = Finset.univ := Finset.mem_singleton.mp hsh
    subst h1
    simp [hr]
  positive := by
    intro sh hsh r hr
    have h1 : sh = Finset.univ := Finset.mem_singleton.mp hsh
    subst h1
    simp only [Finset.mem_univ, ite_eq_left]
    exact hα r
  lower_balance := by
    intro sh hsh s
    have h1 : sh = Finset.univ := Finset.mem_singleton.mp hsh
    subst h1
    simp only [Finset.mem_univ, ite_eq_left]
    exact hflux s

/-- **The global flux of the one-shelf confluence vectors is the flux itself.** -/
theorem oneShelfFluxes_globalFlux (α : N.R → ℝ) (hα : ∀ r, 0 < α r)
    (hflux : ∀ s, ∑ r, α r * N.reactionVector r s = 0) (r : N.R) :
    (oneShelfFluxes α hα hflux).globalFlux r = α r := by
  simp [oneShelfFluxes, DOAShelfFluxes.globalFlux]

/-- **The converse direction of the Deficiency One Algorithm, in its presented form.**  A
feasible system of the algorithm is *presented* by the shelf-wise confluence vectors: the whole
reaction set is a single shelf, and its confluence vector is the flux of the two witnessing
steady states.  This is the one-shelf converse; the *multi-shelf* converse — that a capacity
flux always decomposes into a genuine shelf decomposition whose shelf-wise fluxes satisfy the
two balance conditions — is the hard, genuinely algorithm-specific part of Feinberg's
algorithm and is not proved here. -/
theorem capacity_implies_doaShelfFluxes (h : N.HasMultistationarityCapacity) :
    ∃ (d : DOAShelfFluxes N) (μ : S → ℝ),
      μ ≠ 0 ∧ N.SignCompatibleWithStoich μ ∧
        (∀ s, ∑ r, d.globalFlux r * N.reactionVector r s = 0) ∧
        (∀ s, ∑ r, d.globalFlux r * Real.exp (complexPairing (N.reaction r).source μ) *
          N.reactionVector r s = 0) := by
  obtain ⟨d⟩ := N.capacity_implies_doaFeasible h
  obtain ⟨α, μ, σ, hα, hσS, hσ0, hsign, hflux, hflux'⟩ :=
    (N.hasMultistationarityCapacity_iff_flux_sign).1 h
  have hμ0 : μ ≠ 0 := by
    intro hμ0
    obtain ⟨s, hs⟩ := Function.ne_iff.mp hσ0
    have hs0 : σ s ≠ 0 := by simpa only [Pi.zero_apply] using hs
    have h1 : SignType.sign (μ s) = SignType.sign (σ s) := (hsign s).symm
    have h2 : SignType.sign (μ s) = 0 := by rw [hμ0, Pi.zero_apply, sign_zero]
    rw [h2] at h1
    have h3 : SignType.sign (σ s) = 0 := h1.symm
    rw [sign_eq_zero_iff] at h3
    exact hs0 h3
  have hsc : N.SignCompatibleWithStoich μ := ⟨σ, hσS, sameSign_of_sign_eq hsign⟩
  refine ⟨oneShelfFluxes α hα hflux, μ, hμ0, hsc, ?_, ?_⟩
  · intro s
    calc ∑ r, (oneShelfFluxes α hα hflux).globalFlux r * N.reactionVector r s
        = ∑ r, α r * N.reactionVector r s := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [oneShelfFluxes_globalFlux α hα hflux]
      _ = 0 := hflux s
  · intro s
    calc ∑ r, (oneShelfFluxes α hα hflux).globalFlux r *
        Real.exp (complexPairing (N.reaction r).source μ) * N.reactionVector r s
        = ∑ r, α r * Real.exp (complexPairing (N.reaction r).source μ) *
            N.reactionVector r s := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [oneShelfFluxes_globalFlux α hα hflux]
      _ = 0 := hflux' s

/-- **The converse direction in the feasibility-test form.**  A feasible system of the algorithm
is presented by the shelf-wise confluence vectors. -/
theorem doaFeasible_implies_doaShelfFluxes (h : N.DOAFeasible) :
    ∃ (d : DOAShelfFluxes N) (μ : S → ℝ),
      μ ≠ 0 ∧ N.SignCompatibleWithStoich μ ∧
        (∀ s, ∑ r, d.globalFlux r * N.reactionVector r s = 0) ∧
        (∀ s, ∑ r, d.globalFlux r * Real.exp (complexPairing (N.reaction r).source μ) *
          N.reactionVector r s = 0) := by
  obtain ⟨α, μ, σ, hα, hσS, hσ0, hsign, hflux, hflux'⟩ :=
    (N.hasMultistationarityCapacity_iff_flux_sign).1 (N.doaFeasible_implies_capacity h)
  have hμ0 : μ ≠ 0 := by
    intro hμ0
    obtain ⟨s, hs⟩ := Function.ne_iff.mp hσ0
    have hs0 : σ s ≠ 0 := by simpa only [Pi.zero_apply] using hs
    have h1 : SignType.sign (μ s) = SignType.sign (σ s) := (hsign s).symm
    have h2 : SignType.sign (μ s) = 0 := by rw [hμ0, Pi.zero_apply, sign_zero]
    rw [h2] at h1
    have h3 : SignType.sign (σ s) = 0 := h1.symm
    rw [sign_eq_zero_iff] at h3
    exact hs0 h3
  have hsc : N.SignCompatibleWithStoich μ := ⟨σ, hσS, sameSign_of_sign_eq hsign⟩
  refine ⟨oneShelfFluxes α hα hflux, μ, hμ0, hsc, ?_, ?_⟩
  · intro s
    calc ∑ r, (oneShelfFluxes α hα hflux).globalFlux r * N.reactionVector r s
        = ∑ r, α r * N.reactionVector r s := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [oneShelfFluxes_globalFlux α hα hflux]
      _ = 0 := hflux s
  · intro s
    calc ∑ r, (oneShelfFluxes α hα hflux).globalFlux r *
        Real.exp (complexPairing (N.reaction r).source μ) * N.reactionVector r s
        = ∑ r, α r * Real.exp (complexPairing (N.reaction r).source μ) *
            N.reactionVector r s := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [oneShelfFluxes_globalFlux α hα hflux]
      _ = 0 := hflux' s

/-! ### Reachable sources and targets -/

/-- **A nontrivial path starts at a source.**  If `d` is reachable from `c` and `c ≠ d`, then
some reaction has `c` as its source. -/
theorem reachesWithin_imp_source {N : Network S} {k : ℕ} {c d : Complex S}
    (hk : N.ReachesWithin k c d) (hne : c ≠ d) : ∃ r : N.R, (N.reaction r).source = c := by
  induction k generalizing c d with
  | zero =>
      simp only [N.reachesWithin_zero] at hk
      exact absurd hk hne
  | succ k ih =>
      rcases (N.reachesWithin_succ k c d).mp hk with h | ⟨r, hsrc, hrest⟩
      · exact absurd h hne
      · exact ⟨r, hsrc⟩

/-- **A nontrivial path ends at a target.**  If `d` is reachable from `c` and `c ≠ d`, then some
reaction has `d` as its target. -/
theorem reaches_imp_target {N : Network S} {c d : Complex S} (h : N.Reaches c d) (hne : c ≠ d) :
    ∃ r : N.R, (N.reaction r).target = d := by
  rcases Relation.ReflTransGen.cases_tail h with h' | ⟨w, hw, hstep⟩
  · exact absurd h' hne.symm
  · obtain ⟨r, hsrc, htgt⟩ := hstep
    exact ⟨r, htgt⟩

/-- **A nontrivial path starts at a source**, in the unbounded sense. -/
theorem reaches_imp_source {N : Network S} {c d : Complex S} (h : N.Reaches c d) (hne : c ≠ d) :
    ∃ r : N.R, (N.reaction r).source = c := by
  obtain ⟨k, hk⟩ := (N.reaches_iff_exists_reachesWithin c d).1 h
  exact reachesWithin_imp_source hk hne

/-! ### The leaf complexes -/

/-- **A leaf complex is a cut pair, and its cut component is the singleton.**  The complex `x` is
a *leaf* of the linkage graph when its only neighbour is `y`: the edge `s(x, y)` is a bridge, and
after deleting it `x` is isolated. -/
theorem cutPair_of_leaf {N : Network S} {x y : N.ComplexIdx}
    (hne : x.val ≠ y.val)
    (hedge : N.UndirectedEdge x.val y.val)
    (honly : ∀ v : N.ComplexIdx, N.UndirectedEdge x.val v.val → v.val = y.val) :
    N.CutPair x y ∧ N.cutComponent x y = {x} := by
  have hAdj : N.linkageGraph.Adj x y := ⟨hne, hedge⟩
  have hiso : ∀ v : N.ComplexIdx, ¬ (N.linkageGraph.deleteEdges {s(x, y)}).Adj x v := by
    intro v hv
    rw [SimpleGraph.deleteEdges_adj] at hv
    rcases hv with ⟨hvadj, hnotin⟩
    rcases hvadj with ⟨hne', hedge'⟩
    have hvd : v.val = y.val := honly v hedge'
    have hvd' : v = y := Subtype.ext hvd
    subst hvd'
    exact hnotin (by simp)
  have hreach : ∀ v : N.ComplexIdx,
      (N.linkageGraph.deleteEdges {s(x, y)}).Reachable x v → v.val = x.val := by
    intro v hv
    rw [SimpleGraph.reachable_iff_reflTransGen] at hv
    rcases Relation.ReflTransGen.cases_head hv with h | ⟨w, hstep, _⟩
    · exact congrArg Subtype.val h.symm
    · exact absurd hstep (hiso w)
  constructor
  · refine ⟨hAdj, ?_⟩
    intro hreach'
    have h := hreach y hreach'
    exact absurd h.symm hne
  · ext v
    constructor
    · intro hv
      rw [N.mem_cutComponent] at hv
      have h := hreach v hv
      exact Finset.mem_singleton.mpr (Subtype.ext h)
    · intro hv
      have hvc : v = x := Finset.mem_singleton.mp hv
      subst hvc
      rw [N.mem_cutComponent]



end General

namespace DOAExample

open scoped BigOperators

inductive Species
  | A | B
  deriving DecidableEq, Repr

instance : Fintype Species where
  elems := {Species.A, Species.B}
  complete := by intro s; cases s <;> simp

open Species

def c0 : Complex Species := fun _ => 0
def cA : Complex Species := fun s => match s with | .A => 1 | .B => 0
def cB : Complex Species := fun s => match s with | .A => 0 | .B => 1
def cAB : Complex Species := fun s => match s with | .A => 1 | .B => 1

inductive Rxn
  | r1 | r2 | r3
  deriving DecidableEq, Repr

instance : Fintype Rxn where
  elems := {Rxn.r1, Rxn.r2, Rxn.r3}
  complete := by intro r; cases r <;> simp

def reaction : Rxn → Reaction Species
  | .r1 => { source := c0, target := cA }
  | .r2 => { source := c0, target := cB }
  | .r3 => { source := cAB, target := c0 }

abbrev N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := reaction }

lemma complexes_eq : N.complexes = {c0, cA, cB, cAB} := by decide

lemma mem_complexes (c : Complex Species) (h : c ∈ N.complexes) :
    c = c0 ∨ c = cA ∨ c = cB ∨ c = cAB := by
  rw [complexes_eq] at h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  exact h

def isSource (c : Complex Species) : Prop := ∃ r : Rxn, (N.reaction r).source = c
def isTarget (c : Complex Species) : Prop := ∃ r : Rxn, (N.reaction r).target = c

lemma isSource_iff (c : Complex Species) : isSource c ↔ c = c0 ∨ c = cAB := by
  constructor
  · rintro ⟨r, hsrc⟩
    cases r with
    | r1 => exact Or.inl hsrc.symm
    | r2 => exact Or.inl hsrc.symm
    | r3 => exact Or.inr hsrc.symm
  · rintro (h | h)
    · subst h
      exact ⟨Rxn.r1, rfl⟩
    · subst h
      exact ⟨Rxn.r3, rfl⟩

lemma isTarget_iff (c : Complex Species) : isTarget c ↔ c = cA ∨ c = cB ∨ c = c0 := by
  constructor
  · rintro ⟨r, htgt⟩
    cases r with
    | r1 => exact Or.inl htgt.symm
    | r2 => exact Or.inr (Or.inl htgt.symm)
    | r3 => exact Or.inr (Or.inr htgt.symm)
  · rintro (h | h | h)
    · subst h
      exact ⟨Rxn.r1, rfl⟩
    · subst h
      exact ⟨Rxn.r2, rfl⟩
    · subst h
      exact ⟨Rxn.r3, rfl⟩

lemma not_source_cA : ¬ isSource cA := by
  intro h
  rcases (isSource_iff cA).mp h with h' | h'
  · exact absurd h' (by decide)
  · exact absurd h' (by decide)

lemma not_source_cB : ¬ isSource cB := by
  intro h
  rcases (isSource_iff cB).mp h with h' | h'
  · exact absurd h' (by decide)
  · exact absurd h' (by decide)

lemma not_target_cAB : ¬ isTarget cAB := by
  intro h
  rcases (isTarget_iff cAB).mp h with h' | h' | h'
  · exact absurd h' (by decide)
  · exact absurd h' (by decide)
  · exact absurd h' (by decide)

lemma not_reaches_cA_c0 : ¬ N.Reaches cA c0 := by
  intro h
  obtain ⟨r, hsrc⟩ := N.reaches_imp_source h (by decide)
  exact not_source_cA ⟨r, hsrc⟩

lemma not_reaches_cB_c0 : ¬ N.Reaches cB c0 := by
  intro h
  obtain ⟨r, hsrc⟩ := N.reaches_imp_source h (by decide)
  exact not_source_cB ⟨r, hsrc⟩

lemma not_reaches_cA_cAB : ¬ N.Reaches cA cAB := by
  intro h
  obtain ⟨r, hsrc⟩ := N.reaches_imp_source h (by decide)
  exact not_source_cA ⟨r, hsrc⟩

lemma not_reaches_cB_cAB : ¬ N.Reaches cB cAB := by
  intro h
  obtain ⟨r, hsrc⟩ := N.reaches_imp_source h (by decide)
  exact not_source_cB ⟨r, hsrc⟩

lemma not_reaches_c0_cAB : ¬ N.Reaches c0 cAB := by
  intro h
  obtain ⟨r, htgt⟩ := N.reaches_imp_target h (by decide)
  exact not_target_cAB ⟨r, htgt⟩

lemma source_target_eq_c0 {c : Complex Species} (hs : isSource c) (ht : isTarget c) : c = c0 := by
  rcases (isSource_iff c).mp hs with h1 | h1
  · rcases (isTarget_iff c).mp ht with h2 | h2 | h2
    · exact absurd (h1.symm.trans h2) (by decide)
    · exact absurd (h1.symm.trans h2) (by decide)
    · exact h2
  · rcases (isTarget_iff c).mp ht with h2 | h2 | h2
    · exact absurd (h1.symm.trans h2) (by decide)
    · exact absurd (h1.symm.trans h2) (by decide)
    · exact absurd (h1.symm.trans h2) (by decide)

lemma stronglyLinked_eq {c d : Complex Species} (h : N.StronglyLinked c d) : c = d := by
  by_cases hcd : c = d
  · exact hcd
  · exfalso
    have hcd' : ¬ (d = c) := fun h => hcd h.symm
    obtain ⟨r, hsrc⟩ := N.reaches_imp_source h.1 hcd
    obtain ⟨r', htgt⟩ := N.reaches_imp_target h.2 hcd'
    have hc0 : c = c0 := source_target_eq_c0 ⟨r, hsrc⟩ ⟨r', htgt⟩
    obtain ⟨r'', hsrc'⟩ := N.reaches_imp_source h.2 hcd'
    obtain ⟨r''', htgt'⟩ := N.reaches_imp_target h.1 hcd
    have hd0 : d = c0 := source_target_eq_c0 ⟨r'', hsrc'⟩ ⟨r''', htgt'⟩
    exact hcd (hc0.trans hd0.symm)

lemma isTerminal_cA : N.IsTerminalSLC cA := by
  intro r h
  cases r with
  | r1 => exact absurd h.1 not_reaches_cA_c0
  | r2 => exact absurd h.1 not_reaches_cA_c0
  | r3 => exact absurd h.1 not_reaches_cA_cAB

lemma isTerminal_cB : N.IsTerminalSLC cB := by
  intro r h
  cases r with
  | r1 => exact absurd h.1 not_reaches_cB_c0
  | r2 => exact absurd h.1 not_reaches_cB_c0
  | r3 => exact absurd h.1 not_reaches_cB_cAB

lemma not_isTerminal_c0 : ¬ N.IsTerminalSLC c0 := by
  intro h
  have h' := h Rxn.r1 (StronglyLinked.refl N c0)
  exact absurd h'.2 not_reaches_cA_c0

lemma not_isTerminal_cAB : ¬ N.IsTerminalSLC cAB := by
  intro h
  have h' := h Rxn.r3 (StronglyLinked.refl N cAB)
  exact absurd h'.2 not_reaches_c0_cAB


/-! ### The shelf partition of the enumeration -/

/-- **The shelf rank of a complex**: `A` is on the upper shelf (rank 2), `B` on the lower shelf
(rank 0), and the two nonterminal complexes `0` and `A + B` on the middle shelf (rank 1). -/
def rankOf (c : Complex Species) : ℕ := if c = cA then 2 else if c = cB then 0 else 1

/-- **The shelf of a complex**. -/
def shelfOf (c : Complex Species) : Shelf :=
  match rankOf c with
  | 0 => Shelf.lower
  | 1 => Shelf.middle
  | _ => Shelf.upper

/-- **The pairing of a complex with the log-ratio, as an integer.** -/
def pairOf (c : Complex Species) : ℤ := if c = cA then 1 else if c = cB then -1 else 0

/-- **The log-ratio of the two candidate steady states**: `μ = (1, −1)`. -/
def μ : Species → ℝ := fun s => match s with | .A => 1 | .B => -1

/-- **The shelf of a complex index.** -/
def shelfIdx (c : N.ComplexIdx) : Shelf := shelfOf c.val

/-- **The shelf rank of a complex index.** -/
lemma rankOf_c0 : rankOf c0 = 1 := by decide
lemma rankOf_cA : rankOf cA = 2 := by decide
lemma rankOf_cB : rankOf cB = 0 := by decide
lemma rankOf_cAB : rankOf cAB = 1 := by decide

lemma rank_shelfIdx {c : N.ComplexIdx} (hc : c.val ∈ N.complexes) :
    (shelfIdx c).rank = rankOf c.val := by
  unfold shelfIdx
  rcases mem_complexes c.val hc with h | h | h | h
  · rw [h]
    simp [shelfOf, rankOf_c0, Shelf.rank]
  · rw [h]
    simp [shelfOf, rankOf_cA, Shelf.rank]
  · rw [h]
    simp [shelfOf, rankOf_cB, Shelf.rank]
  · rw [h]
    simp [shelfOf, rankOf_cAB, Shelf.rank]

/-- **A complex on the upper shelf is `A`.** -/
lemma shelfIdx_upper_imp {c : N.ComplexIdx} (hc : c.val ∈ N.complexes) (h : shelfIdx c = Shelf.upper) :
    c.val = cA := by
  rcases mem_complexes c.val hc with h' | h' | h' | h'
  · unfold shelfIdx at h
    rw [h'] at h
    simp [shelfOf, rankOf_c0] at h
  · exact h'
  · unfold shelfIdx at h
    rw [h'] at h
    simp [shelfOf, rankOf_cB] at h
  · unfold shelfIdx at h
    rw [h'] at h
    simp [shelfOf, rankOf_cAB] at h

/-- **A complex on the lower shelf is `B`.** -/
lemma shelfIdx_lower_imp {c : N.ComplexIdx} (hc : c.val ∈ N.complexes) (h : shelfIdx c = Shelf.lower) :
    c.val = cB := by
  rcases mem_complexes c.val hc with h' | h' | h' | h'
  · unfold shelfIdx at h
    rw [h'] at h
    simp [shelfOf, rankOf_c0] at h
  · unfold shelfIdx at h
    rw [h'] at h
    simp [shelfOf, rankOf_cA] at h
  · exact h'
  · unfold shelfIdx at h
    rw [h'] at h
    simp [shelfOf, rankOf_cAB] at h

/-- **A complex on the middle shelf is `0` or `A + B`.** -/
lemma shelfIdx_middle_imp {c : N.ComplexIdx} (hc : c.val ∈ N.complexes)
    (h : shelfIdx c = Shelf.middle) : c.val = c0 ∨ c.val = cAB := by
  rcases mem_complexes c.val hc with h' | h' | h' | h'
  · exact Or.inl h'
  · unfold shelfIdx at h
    rw [h'] at h
    simp [shelfOf, rankOf_cA] at h
  · unfold shelfIdx at h
    rw [h'] at h
    simp [shelfOf, rankOf_cB] at h
  · exact Or.inr h'

/-- **The shelf partition of the example.** -/
def sp : N.ShelfPartition where
  shelf := shelfIdx
  nonterminal_middle := by
    intro c hc
    rcases mem_complexes c.val c.2 with h | h | h | h
    · unfold shelfIdx
      rw [h]
      exact (by decide : shelfOf c0 = Shelf.middle)
    · exact absurd (h ▸ isTerminal_cA) hc
    · exact absurd (h ▸ isTerminal_cB) hc
    · unfold shelfIdx
      rw [h]
      exact (by decide : shelfOf cAB = Shelf.middle)
  sameClass_sameShelf := by
    intro c d h
    have hcd : c.val = d.val := stronglyLinked_eq h
    unfold shelfIdx
    rw [hcd]

/-- **The sum over the two species of the example.** -/
lemma sum_species (f : Species → ℝ) : ∑ s, f s = f .A + f .B := by
  have huniv : (Finset.univ : Finset Species) = {Species.A, Species.B} := by
    ext s
    cases s <;> simp
  show Finset.univ.sum f = _
  rw [huniv]
  simp [Finset.sum_insert, Finset.sum_singleton]

/-- **The pairing of a complex of the network with the log-ratio.** -/
lemma pairing_eq_pairOf (c : Complex Species) (hc : c ∈ N.complexes) :
    CRNT.complexPairing c μ = (pairOf c : ℝ) := by
  rcases mem_complexes c hc with h | h | h | h
  · rw [h]
    have h1 : CRNT.complexPairing c0 μ = 0 := by
      simp [CRNT.complexPairing, c0, μ]
    have h2 : pairOf c0 = 0 := by decide
    rw [h1, h2]
    norm_num
  · rw [h]
    have h1 : CRNT.complexPairing cA μ = 1 := by
      simp [CRNT.complexPairing, sum_species, cA, μ]
    have h2 : pairOf cA = 1 := by decide
    rw [h1, h2]
    norm_num
  · rw [h]
    have h1 : CRNT.complexPairing cB μ = -1 := by
      simp [CRNT.complexPairing, sum_species, cB, μ]
    have h2 : pairOf cB = -1 := by decide
    rw [h1, h2]
    norm_num
  · rw [h]
    have h1 : CRNT.complexPairing cAB μ = 0 := by
      simp [CRNT.complexPairing, sum_species, cAB, μ]
    have h2 : pairOf cAB = 0 := by decide
    rw [h1, h2]
    norm_num

/-- **The shelf order is respected by the pairing order.** -/
lemma rank_pair_lemma : ∀ (c d : N.ComplexIdx), rankOf d.val < rankOf c.val →
    (pairOf d.val : ℤ) < (pairOf c.val : ℤ) := by decide

/-- **The middle shelf is a level set of the pairing.** -/
lemma mid_pair_lemma : ∀ (c d : N.ComplexIdx), rankOf c.val = 1 → rankOf d.val = 1 →
    pairOf c.val = pairOf d.val := by decide


/-! ### The confluence vector of the run -/

/-- **The confluence vector of the run**: the cut-space vector `e_A + e_B − 2 e_0`, the sum of
the incidence vectors of the reactions `0 → A` and `0 → B`. -/
noncomputable def g : N.ComplexIdx → ℝ :=
  N.incidenceMap (fun r => match r with | .r1 => 1 | .r2 => 1 | .r3 => 0)

/-- **The confluence vector of the run is a confluence vector.** -/
lemma g_isConfluence : N.IsConfluenceVector g :=
  ⟨fun r => match r with | .r1 => 1 | .r2 => 1 | .r3 => 0, rfl⟩

/-- **The univ of the reaction index.** -/
lemma univ_Rxn : (Finset.univ : Finset Rxn) = {Rxn.r1, Rxn.r2, Rxn.r3} := by
  ext r
  cases r <;> simp

/-- **The value of the confluence vector at `A`.** -/
lemma g_cA : g (N.targetIdx Rxn.r1) = 1 := by
  rw [g, N.incidenceMap_apply, univ_Rxn]
  simp [Finset.sum_insert, Finset.sum_singleton,
    ite_eq_right (by decide : ¬ (N.targetIdx Rxn.r2 = N.targetIdx Rxn.r1)),
    ite_eq_right (by decide : ¬ (N.targetIdx Rxn.r3 = N.targetIdx Rxn.r1)),
    ite_eq_right (by decide : ¬ (N.sourceIdx Rxn.r1 = N.targetIdx Rxn.r1)),
    ite_eq_right (by decide : ¬ (N.sourceIdx Rxn.r2 = N.targetIdx Rxn.r1)),
    ite_eq_right (by decide : ¬ (N.sourceIdx Rxn.r3 = N.targetIdx Rxn.r1))]

/-- **The value of the confluence vector at `B`.** -/
lemma g_cB : g (N.targetIdx Rxn.r2) = 1 := by
  rw [g, N.incidenceMap_apply, univ_Rxn]
  simp [Finset.sum_insert, Finset.sum_singleton,
    ite_eq_right (by decide : ¬ (N.targetIdx Rxn.r1 = N.targetIdx Rxn.r2)),
    ite_eq_right (by decide : ¬ (N.targetIdx Rxn.r3 = N.targetIdx Rxn.r2)),
    ite_eq_right (by decide : ¬ (N.sourceIdx Rxn.r1 = N.targetIdx Rxn.r2)),
    ite_eq_right (by decide : ¬ (N.sourceIdx Rxn.r2 = N.targetIdx Rxn.r2)),
    ite_eq_right (by decide : ¬ (N.sourceIdx Rxn.r3 = N.targetIdx Rxn.r2))]

/-- **The value of the confluence vector at `A + B`.** -/
lemma g_cAB : g (N.sourceIdx Rxn.r3) = 0 := by
  rw [g, N.incidenceMap_apply, univ_Rxn]
  simp [Finset.sum_insert, Finset.sum_singleton,
    ite_eq_right (by decide : ¬ (N.targetIdx Rxn.r1 = N.sourceIdx Rxn.r3)),
    ite_eq_right (by decide : ¬ (N.targetIdx Rxn.r2 = N.sourceIdx Rxn.r3)),
    ite_eq_right (by decide : ¬ (N.targetIdx Rxn.r3 = N.sourceIdx Rxn.r3)),
    ite_eq_right (by decide : ¬ (N.sourceIdx Rxn.r1 = N.sourceIdx Rxn.r3)),
    ite_eq_right (by decide : ¬ (N.sourceIdx Rxn.r2 = N.sourceIdx Rxn.r3))]

/-- **The confluence vector is nonzero.** -/
lemma g_ne_zero : g ≠ 0 := by
  intro h
  have h' := g_cA
  rw [h] at h'
  simp at h'


/-! ### The cut pairs of the example -/

/-- **The only neighbour of `A` is `0`.** -/
lemma undirectedEdge_cA (d : Complex Species) (h : N.UndirectedEdge cA d) : d = c0 := by
  rcases h with h | h
  · obtain ⟨r, hsrc, _⟩ := h
    exact False.elim (not_source_cA ⟨r, hsrc⟩)
  · obtain ⟨r, hsrc, htgt⟩ := h
    cases r with
    | r1 => exact hsrc.symm
    | r2 => exact False.elim (absurd htgt (by decide))
    | r3 => exact False.elim (absurd htgt (by decide))

/-- **The only neighbour of `B` is `0`.** -/
lemma undirectedEdge_cB (d : Complex Species) (h : N.UndirectedEdge cB d) : d = c0 := by
  rcases h with h | h
  · obtain ⟨r, hsrc, _⟩ := h
    exact False.elim (not_source_cB ⟨r, hsrc⟩)
  · obtain ⟨r, hsrc, htgt⟩ := h
    cases r with
    | r1 => exact False.elim (absurd htgt (by decide))
    | r2 => exact hsrc.symm
    | r3 => exact False.elim (absurd htgt (by decide))

/-- **The only neighbour of `A + B` is `0`.** -/
lemma undirectedEdge_cAB (d : Complex Species) (h : N.UndirectedEdge cAB d) : d = c0 := by
  rcases h with h | h
  · obtain ⟨r, hsrc, htgt⟩ := h
    cases r with
    | r1 => exact False.elim (absurd hsrc (by decide))
    | r2 => exact False.elim (absurd hsrc (by decide))
    | r3 => exact htgt.symm
  · obtain ⟨r, hsrc, htgt⟩ := h
    exact False.elim (not_target_cAB ⟨r, htgt⟩)

/-- **`A` is a cut pair with `0`, and its cut component is the singleton `{A}`.** -/
lemma cutPair_cA_c0 : N.CutPair (N.targetIdx Rxn.r1) (N.sourceIdx Rxn.r1) ∧
    N.cutComponent (N.targetIdx Rxn.r1) (N.sourceIdx Rxn.r1) = {N.targetIdx Rxn.r1} := by
  refine cutPair_of_leaf (N := N) (x := N.targetIdx Rxn.r1) (y := N.sourceIdx Rxn.r1) ?_ ?_ ?_
  · exact (by decide : (N.targetIdx Rxn.r1).val ≠ (N.sourceIdx Rxn.r1).val)
  · exact Or.inr ⟨Rxn.r1, rfl, rfl⟩
  · intro v hv
    exact undirectedEdge_cA v.val hv

/-- **`B` is a cut pair with `0`, and its cut component is the singleton `{B}`.** -/
lemma cutPair_cB_c0 : N.CutPair (N.targetIdx Rxn.r2) (N.sourceIdx Rxn.r2) ∧
    N.cutComponent (N.targetIdx Rxn.r2) (N.sourceIdx Rxn.r2) = {N.targetIdx Rxn.r2} := by
  refine cutPair_of_leaf (N := N) (x := N.targetIdx Rxn.r2) (y := N.sourceIdx Rxn.r2) ?_ ?_ ?_
  · exact (by decide : (N.targetIdx Rxn.r2).val ≠ (N.sourceIdx Rxn.r2).val)
  · exact Or.inr ⟨Rxn.r2, rfl, rfl⟩
  · intro v hv
    exact undirectedEdge_cB v.val hv

/-- **The cut-pair functional on the cut pair `(A, 0)`.** -/
lemma cutSum_cA_c0 : N.cutSum g (N.targetIdx Rxn.r1) (N.sourceIdx Rxn.r1) = 1 := by
  unfold cutSum
  rw [cutPair_cA_c0.2]
  simp [g_cA]

/-- **The cut-pair functional on the cut pair `(0, A)`.** -/
lemma cutSum_c0_cA : N.cutSum g (N.sourceIdx Rxn.r1) (N.targetIdx Rxn.r1) = -1 := by
  have h := N.cutSum_antisymm (g := g) (hg := g_isConfluence) (h := cutPair_cA_c0.1)
  rw [cutSum_cA_c0] at h
  linarith

/-- **The cut-pair functional on the cut pair `(B, 0)`.** -/
lemma cutSum_cB_c0 : N.cutSum g (N.targetIdx Rxn.r2) (N.sourceIdx Rxn.r2) = 1 := by
  unfold cutSum
  rw [cutPair_cB_c0.2]
  simp [g_cB]

/-- **The cut-pair functional on the cut pair `(0, B)`.** -/
lemma cutSum_c0_cB : N.cutSum g (N.sourceIdx Rxn.r2) (N.targetIdx Rxn.r2) = -1 := by
  have h := N.cutSum_antisymm (g := g) (hg := g_isConfluence) (h := cutPair_cB_c0.1)
  rw [cutSum_cB_c0] at h
  linarith


/-! ### The placement rules are met -/

lemma pairOf_c0 : pairOf c0 = 0 := by decide
lemma pairOf_cA : pairOf cA = 1 := by decide
lemma pairOf_cB : pairOf cB = -1 := by decide
lemma pairOf_cAB : pairOf cAB = 0 := by decide

lemma mem_c0 : c0 ∈ N.complexes := by decide
lemma mem_cA : cA ∈ N.complexes := by decide
lemma mem_cB : cB ∈ N.complexes := by decide
lemma mem_cAB : cAB ∈ N.complexes := by decide

/-- **A complex on the middle shelf has rank one.** -/
lemma shelfIdx_middle_rank {c : N.ComplexIdx} (hc : c.val ∈ N.complexes)
    (h : shelfIdx c = Shelf.middle) : rankOf c.val = 1 := by
  unfold shelfIdx at h
  rcases mem_complexes c.val hc with h' | h' | h' | h'
  · rw [h']
    exact rankOf_c0
  · rw [h'] at h
    simp [shelfOf, rankOf_cA] at h
  · rw [h'] at h
    simp [shelfOf, rankOf_cB] at h
  · rw [h']
    exact rankOf_cAB

/-- **The placement rules are met by the run.**  The shelf partition of the example and the
confluence vector `g` satisfy the placement rules for the log-ratio `μ = (1, −1)`. -/
lemma imposes : sp.imposes g μ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the height constraint: a higher shelf pairs strictly above a lower one
    intro y y' h
    have e1 := rank_shelfIdx y'.2
    have e2 := rank_shelfIdx y.2
    have h' : (shelfIdx y').rank < (shelfIdx y).rank := h
    have h1 : rankOf y'.val < rankOf y.val := by
      rw [e1, e2] at h'
      exact h'
    have h2 := rank_pair_lemma y y' h1
    have h3 : (pairOf y'.val : ℝ) < (pairOf y.val : ℝ) := by exact_mod_cast h2
    have hp1 : CRNT.complexPairing y'.val μ = (pairOf y'.val : ℝ) := pairing_eq_pairOf y'.val y'.2
    have hp2 : CRNT.complexPairing y.val μ = (pairOf y.val : ℝ) := pairing_eq_pairOf y.val y.2
    simp only [hp1, hp2]
    exact h3
  · -- the middle shelf is a level set of the log-ratio
    intro y y' hy hy'
    have h1 : rankOf y.val = 1 := shelfIdx_middle_rank y.2 hy
    have h2 : rankOf y'.val = 1 := shelfIdx_middle_rank y'.2 hy'
    have h3 := mid_pair_lemma y y' h1 h2
    have h4 : (pairOf y.val : ℝ) = (pairOf y'.val : ℝ) := by exact_mod_cast h3
    have hp1 : CRNT.complexPairing y.val μ = (pairOf y.val : ℝ) := pairing_eq_pairOf y.val y.2
    have hp2 : CRNT.complexPairing y'.val μ = (pairOf y'.val : ℝ) := pairing_eq_pairOf y'.val y'.2
    simp only [hp1, hp2]
    exact h4
  · -- the cut pairs on the upper shelf
    intro y y' hcut hy
    have hyc : y.val = cA := shelfIdx_upper_imp y.2 hy
    rcases hcut.1 with ⟨hne, hedge⟩
    rcases hedge with ⟨r, hsrc, htgt⟩ | ⟨r, hsrc, htgt⟩
    · rw [hyc] at hsrc
      exact False.elim (not_source_cA ⟨r, hsrc⟩)
    · rw [hyc] at htgt
      cases r with
      | r1 =>
        have hy_eq : y = N.targetIdx Rxn.r1 := Subtype.ext hyc
        have hy'_eq : y' = N.sourceIdx Rxn.r1 := Subtype.ext hsrc.symm
        subst hy_eq
        subst hy'_eq
        refine ⟨?_, ?_, ?_⟩
        · intro h
          have hc := cutSum_cA_c0
          rw [hc] at h
          have hz : (pairOf c0 : ℤ) < (pairOf cA : ℤ) := by
            rw [pairOf_c0, pairOf_cA]
            norm_num
          have hp1 : CRNT.complexPairing c0 μ = (pairOf c0 : ℝ) := pairing_eq_pairOf c0 mem_c0
          have hp2 : CRNT.complexPairing cA μ = (pairOf cA : ℝ) := pairing_eq_pairOf cA mem_cA
          simp only [sourceIdx, targetIdx, reaction]
          rw [hp1, hp2]
          exact_mod_cast hz
        · intro h
          have hc := cutSum_cA_c0
          rw [hc] at h
          norm_num at h
        · intro h
          have hc := cutSum_cA_c0
          rw [hc] at h
          norm_num at h
      | r2 => exact False.elim (absurd htgt (by decide))
      | r3 => exact False.elim (absurd htgt (by decide))
  · -- the cut pairs on the lower shelf
    intro y y' hcut hy
    have hyc : y.val = cB := shelfIdx_lower_imp y.2 hy
    rcases hcut.1 with ⟨hne, hedge⟩
    rcases hedge with ⟨r, hsrc, htgt⟩ | ⟨r, hsrc, htgt⟩
    · rw [hyc] at hsrc
      exact False.elim (not_source_cB ⟨r, hsrc⟩)
    · rw [hyc] at htgt
      cases r with
      | r1 => exact False.elim (absurd htgt (by decide))
      | r2 =>
        have hy_eq : y = N.targetIdx Rxn.r2 := Subtype.ext hyc
        have hy'_eq : y' = N.sourceIdx Rxn.r2 := Subtype.ext hsrc.symm
        subst hy_eq
        subst hy'_eq
        refine ⟨?_, ?_, ?_⟩
        · intro h
          have hc := cutSum_cB_c0
          rw [hc] at h
          have hz : (pairOf cB : ℤ) < (pairOf c0 : ℤ) := by
            rw [pairOf_cB, pairOf_c0]
            norm_num
          have hp1 : CRNT.complexPairing cB μ = (pairOf cB : ℝ) := pairing_eq_pairOf cB mem_cB
          have hp2 : CRNT.complexPairing c0 μ = (pairOf c0 : ℝ) := pairing_eq_pairOf c0 mem_c0
          simp only [sourceIdx, targetIdx, reaction]
          rw [hp1, hp2]
          exact_mod_cast hz
        · intro h
          have hc := cutSum_cB_c0
          rw [hc] at h
          norm_num at h
        · intro h
          have hc := cutSum_cB_c0
          rw [hc] at h
          norm_num at h
      | r3 => exact False.elim (absurd htgt (by decide))


/-! ### The verdict of the algorithm on the example -/

/-- **The stoichiometric vector with the sign pattern of the log-ratio.** -/
lemma stoichVec_eq : N.reactionVector Rxn.r1 - N.reactionVector Rxn.r2 = μ := by
  funext s
  cases s <;> simp [reaction, c0, cA, cB, μ]

/-- **The two pairing functions of the repository agree.** -/
lemma networkComplexPairing_eq (y : Complex Species) (ν : Species → ℝ) :
    CRNT.Network.complexPairing y ν = CRNT.complexPairing y ν := rfl

/-- **The Deficiency One Algorithm affirms the capacity of the example.**  The shelf partition
places `A` on the upper shelf, `B` on the lower shelf and the two nonterminal complexes `0` and
`A + B` on the middle shelf; the confluence vector is the cut-space vector `e_A + e_B − 2e_0`; and
the log-ratio `μ = (1, −1)` meets the placement rules. -/
theorem affirmsCapacity : N.DOAAffirmsCapacity := by
  refine ⟨g, g_isConfluence, g_ne_zero, sp, μ, ?_, ?_, imposes⟩
  · intro h
    have h' := congrFun h Species.A
    simp [μ] at h'
  · refine ⟨N.reactionVector Rxn.r1 - N.reactionVector Rxn.r2, ?_, ?_⟩
    · exact N.stoichSubspace.sub_mem (N.reactionVector_mem_stoichSubspace Rxn.r1)
        (N.reactionVector_mem_stoichSubspace Rxn.r2)
    · rw [stoichVec_eq]
      exact sameSign_refl _

/-- **The algorithm's system is feasible on the example.**  The log-ratio `μ = (1, −1)` and the
unit flux satisfy the two balance equations: every source of the example pairs with `μ` at `0`,
so the exponential factors are all `1`. -/
theorem doaFeasible : N.DOAFeasible := by
  refine ⟨DOACandidate.ofData N μ ?_ (fun _ => (1 : ℝ)) ?_ ?_ ?_ ?_⟩
  · intro h
    have h' := congrFun h Species.A
    simp [μ] at h'
  · intro r
    norm_num
  · refine ⟨N.reactionVector Rxn.r1 - N.reactionVector Rxn.r2, ?_, ?_⟩
    · exact N.stoichSubspace.sub_mem (N.reactionVector_mem_stoichSubspace Rxn.r1)
        (N.reactionVector_mem_stoichSubspace Rxn.r2)
    · rw [stoichVec_eq]
      exact sameSign_refl _
  · intro s
    cases s <;>
      simp [univ_Rxn, Finset.sum_insert, Finset.sum_singleton, reaction, c0, cA, cB, cAB]
  · intro s
    have hexp1 : Real.exp (CRNT.Network.complexPairing c0 μ) = 1 := by
      rw [networkComplexPairing_eq, pairing_eq_pairOf c0 mem_c0, pairOf_c0]
      simp
    have hexp2 : Real.exp (CRNT.Network.complexPairing cAB μ) = 1 := by
      rw [networkComplexPairing_eq, pairing_eq_pairOf cAB mem_cAB, pairOf_cAB]
      simp
    cases s <;>
      simp [univ_Rxn, Finset.sum_insert, Finset.sum_singleton, hexp1, hexp2, reaction,
        c0, cA, cB, cAB]

/-- **The example has the capacity for multiple positive steady states.** -/
theorem hasCapacity : N.HasMultistationarityCapacity :=
  N.doaFeasible_implies_capacity doaFeasible

/-- **The example has a single linkage class**: the zero complex is linked to `A`, `B` and
`A + B`, so `ℓ = 1`.  (The *value* of the deficiency is not reducible under kernel `decide` --
the stoichiometric rank is a determinant permutation-sum -- and is obtained by compiled
evaluation, exactly as `CRNT.Decision.ComputableDeficiency` documents.) -/
theorem numLinkageClasses_eq_one : N.computeNumLinkageClasses = 1 := by decide

/-- **The two verdicts agree on the example.** -/
theorem agreesWithFeasibilityTest : N.DOAAffirmsCapacity ↔ N.DOAFeasible :=
  ⟨fun _ => doaFeasible, fun _ => affirmsCapacity⟩




end DOAExample

end Network

end CRNT
