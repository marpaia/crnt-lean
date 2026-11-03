import CRNT.Dynamics.GraphTransform
import CRNT.Dynamics.FlowConstruction

/-!
# Discrete graph-transform invariance and fixed-point distance bounds

A supplied contracting graph transform has a fixed graph, discrete forward
invariance, and a Banach distance estimate from the reference graph. These are
abstract graph-transform consequences; normal hyperbolicity, a perturbation
family, and an O(ε) defect estimate are not derived here.

For continuous-time invariance `FlowGraphTransformFamily` supplies a separate
operator at each time and a graph-mapping property. A common fixed graph is
invariant at all times. Its time-zero operator is the identity; positive-time
operators can contract. This replaces the former one-operator all-time contract,
which forced that single operator to be the identity. General Fenichel
normally hyperbolic manifold persistence remains incomplete.
-/

open Function Set
open scoped NNReal BoundedContinuousFunction

namespace ODE

variable {Y : Type*} {E : Type*}

section GraphSet

/-- The graph map of a section `σ : Y → E`: the point `y ↦ (y, σ y)` of the product `Y × E`. -/
def graphMap (σ : Y → E) : Y → Y × E := fun y => (y, σ y)

/-- The **graph** of a section `σ : Y → E` as a subset of the product `Y × E`: the set of points
`(y, z)` with `z = σ y`. This is the region the manifold `{(y, σ y)}` occupies. -/
def graphSet (σ : Y → E) : Set (Y × E) := {p | p.2 = σ p.1}

@[simp] theorem mem_graphSet {σ : Y → E} {p : Y × E} : p ∈ graphSet σ ↔ p.2 = σ p.1 := Iff.rfl

theorem graphMap_mem_graphSet (σ : Y → E) (y : Y) : graphMap σ y ∈ graphSet σ := rfl

/-- The graph of a section is the range of its graph map. -/
theorem graphSet_eq_range (σ : Y → E) : graphSet σ = range (graphMap σ) := by
  ext p
  constructor
  · intro hp; exact ⟨p.1, by rw [graphMap, ← hp]⟩
  · rintro ⟨y, rfl⟩; rfl

end GraphSet

section FlowTransform

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A discrete flow graph transform. A forward semiflow `flow : Flow ℝ≥0 (Y × E)` of the
coupled slow–fast field `ẏ = ε·g(y, z)`, `ż = fast y z`, together with the graph-transform operator
`op` it induces and the horizon `τ` at which it acts. The structural hypothesis `flow_mapsTo`
records that `op` *is* the flow-then-regraph map: the time-`τ` flow carries each point `(y, σ y)` of
the graph of `σ` to a point of the graph of `op σ`. Only inclusion in the target graph is required; surjectivity over the base is not asserted. -/
structure CoupledFlowGraphTransform (Y : Type*) (E : Type*)
    [TopologicalSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- The forward semiflow of the coupled slow–fast field on the product `Y × E`. -/
  flow : Flow ℝ≥0 (Y × E)
  /-- The horizon at which the graph transform is taken. -/
  τ : ℝ≥0
  /-- The induced graph-transform / Lyapunov–Perron operator on sections. -/
  op : (Y → E) → (Y → E)
  /-- The time-`τ` flow maps the graph of `σ` into the graph of `op σ`: pushing the graph forward by
  the flow and re-expressing as a graph over `Y` produces `op σ`. -/
  flow_mapsTo : ∀ σ : Y → E, MapsTo (flow.toFun τ) (graphSet σ) (graphSet (op σ))

variable [TopologicalSpace Y]

namespace CoupledFlowGraphTransform

variable (F : CoupledFlowGraphTransform Y E)

/-- **Fixed point ⇒ time-`τ` invariance.** If `σ` is a fixed point of the graph transform
(`op σ = σ`), the time-`τ` flow maps the graph of `σ` into itself: a trajectory on the manifold stays
on it after the horizon `τ`. This is the single-step invariance from which the full forward
invariance follows by the semigroup law. -/
theorem mapsTo_graphSet_of_fixed {σ : Y → E} (hσ : F.op σ = σ) :
    MapsTo (F.flow.toFun F.τ) (graphSet σ) (graphSet σ) := by
  have := F.flow_mapsTo σ
  rwa [hσ] at this

/-- **Fixed point ⇒ invariance at every multiple of the horizon.** Iterating the time-`τ` map by the
semigroup law, the graph of a fixed-point section is mapped into itself by `Φ (n · τ)` for every
`n : ℕ`: sampling a trajectory started on the manifold at multiples of the horizon keeps it on the
manifold. -/
theorem mapsTo_graphSet_iterate_of_fixed {σ : Y → E} (hσ : F.op σ = σ) (n : ℕ) :
    MapsTo (F.flow.toFun (n • F.τ)) (graphSet σ) (graphSet σ) := by
  induction n with
  | zero => simpa using (mapsTo_id _)
  | succ k ih =>
    have hstep := F.mapsTo_graphSet_of_fixed hσ
    intro p hp
    have hsucc : (k + 1) • F.τ = F.τ + k • F.τ := by
      rw [succ_nsmul]; rw [add_comm]
    rw [hsucc, F.flow.map_add]
    exact hstep (ih hp)

/-- Graph invariance and/or a distance estimate for the displayed explicit flow
and supplied contraction data. This does not assert general perturbed NHIM persistence. -/
theorem graphSet_isInvariant_of_fixed {σ : Y → E} (hσ : F.op σ = σ) :
    IsInvariant (fun n : ℕ => F.flow.toFun (n • F.τ)) (graphSet σ) :=
  fun n => F.mapsTo_graphSet_iterate_of_fixed hσ n

/-- **A trajectory started on the manifold stays on it (sampled at the horizon).** If a point lies on
the graph of a fixed-point section, so does its image under `Φ (n · τ)` for every `n`. The concrete
"trajectory stays on the graph" reading of forward invariance. -/
theorem onGraph_iterate_of_fixed {σ : Y → E} (hσ : F.op σ = σ) {p : Y × E}
    (hp : p ∈ graphSet σ) (n : ℕ) : F.flow.toFun (n • F.τ) p ∈ graphSet σ :=
  F.mapsTo_graphSet_iterate_of_fixed hσ n hp

end CoupledFlowGraphTransform

/-- A family of graph transforms indexed by elapsed time. The time-zero operator
is the identity as a consequence of `flow_mapsTo`; positive-time operators can contract. -/
structure FlowGraphTransformFamily (Y : Type*) (E : Type*)
    [TopologicalSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E] where
  flow : Flow ℝ≥0 (Y × E)
  op : ℝ≥0 → (Y → E) → (Y → E)
  flow_mapsTo : ∀ t σ, MapsTo (flow.toFun t) (graphSet σ) (graphSet (op t σ))

namespace FlowGraphTransformFamily

variable (F : FlowGraphTransformFamily Y E)

@[simp] theorem op_zero (σ : Y → E) : F.op 0 σ = σ := by
  funext y
  have hp := F.flow_mapsTo 0 σ (graphMap_mem_graphSet σ y)
  simpa [graphSet, graphMap] using hp.symm

/-- A section fixed by every elapsed-time transform has a continuously invariant graph. -/
theorem graphSet_isInvariant_of_commonFixedPoint {σ : Y → E}
    (hσ : ∀ t, F.op t σ = σ) : IsInvariant F.flow.toFun (graphSet σ) := by
  intro t p hp
  have h := F.flow_mapsTo t σ hp
  rwa [hσ t] at h

end FlowGraphTransformFamily

end FlowTransform

section Persistence

variable [TopologicalSpace Y] [NormedAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E]

omit [CompleteSpace E] [NormedSpace ℝ E] in
/-- Realize the underlying section of a bounded section `σ : Y →ᵇ E` as a plain section `Y → E`. -/
@[simp] theorem graphSet_coe (σ : Y →ᵇ E) :
    graphSet (σ : Y → E) = {p : Y × E | p.2 = σ p.1} := rfl

/-- Discrete graph invariance for the supplied fixed section, together with the
Banach fixed-point distance bound. Any perturbation-size estimate is additional data. -/
theorem graphTransform_discrete_invariant_and_dist_le (G : GraphTransformData Y E)
    (F : CoupledFlowGraphTransform Y E)
    (hfix : F.op (G.manifold : Y → E) = (G.manifold : Y → E)) :
    IsInvariant (fun n : ℕ => F.flow.toFun (n • F.τ)) (graphSet (G.manifold : Y → E)) ∧
      dist G.base G.manifold ≤ G.defect / (1 - G.factor) :=
  ⟨F.graphSet_isInvariant_of_fixed hfix, G.manifold_dist_base_le⟩

/-- Discrete invariance of the fixed graph under the sampled flow. -/
theorem manifold_graphSet_isInvariant (G : GraphTransformData Y E)
    (F : CoupledFlowGraphTransform Y E)
    (hfix : F.op (G.manifold : Y → E) = (G.manifold : Y → E)) :
    IsInvariant (fun n : ℕ => F.flow.toFun (n • F.τ)) (graphSet (G.manifold : Y → E)) :=
  (graphTransform_discrete_invariant_and_dist_le G F hfix).1

end Persistence

end ODE
