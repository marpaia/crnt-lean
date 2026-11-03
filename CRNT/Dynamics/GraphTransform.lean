import CRNT.Dynamics.FenichelC1Manifold
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# The Lyapunov–Perron graph transform and Fenichel `ε`-persistence

This module formalizes the contraction at the heart of Fenichel's `ε`-persistence theorem: the
**graph transform** (Lyapunov–Perron operator) on bounded sections of the fast bundle. For a
singularly-perturbed system `ẏ = ε·g(y, z)`, `ż = fast y z` with a normally attracting fast fibre
contracting at rate `λ > 0`, the perturbed invariant manifold is the graph of a section `σ : Y → E`
that is a fixed point of the operator pushing each candidate graph forward and re-graphing it over
the slow base. The operator contracts in the supremum metric with factor `q = (Lipschitz/drift
terms)/λ < 1` exactly when the spectral gap `λ` dominates those terms, so the perturbed manifold
exists, is unique, and is `O(ε)`-`C⁰`-close to the unperturbed manifold `manifoldMap`. It is CRN-free
and lives in the `ODE` namespace shared with `CRNT.Dynamics.Fenichel` and
`CRNT.Dynamics.FenichelC1Manifold`.

The carrier is the complete metric space `Y →ᵇ E` of bounded continuous sections with the supremum
metric. The contraction core is kept general — parameterized by the contraction factor `q`, the
operator, and a base section — so that the centre-manifold construction (a graph transform on the
centre directions) reuses it verbatim.

Defined by Fenichel, "Geometric singular perturbation theory for ordinary differential equations",
via the Lyapunov–Perron / Hadamard graph-transform method (Carr, "Applications of centre manifold
theory"; Hirsch–Pugh–Shub, "Invariant manifolds"): a uniformly attracting invariant manifold of an
unperturbed system persists as a nearby invariant manifold under small perturbations, constructed as
the fixed point of a contraction on Lipschitz sections.

**Graph-transform data** (`GraphTransformData`). An operator `T : (Y →ᵇ E) → (Y →ᵇ E)` on bounded
sections, a contraction factor `q : ℝ≥0` with `q < 1`, the supremum-metric displacement bound
`dist (T σ) (T τ) ≤ q · dist σ τ`, a distinguished base section `base` (the unperturbed manifold), and
a drift defect bound `dist (T base) base ≤ defect`. The factor `q` is the spectral-gap ratio of the
fibre Lipschitz/drift terms to the rate `λ`; `defect` is the `O(ε)` displacement the slow drift
applies to the base graph.

**Contraction and fixed point** (`GraphTransformData.isContracting`,
`GraphTransformData.manifold`). The displacement bound makes `T` a `ContractingWith q` map on the
complete space `Y →ᵇ E`; Banach's fixed-point theorem (`ContractingWith.fixedPoint`) furnishes the
unique fixed-point section `manifold = M_ε`, with `T manifold = manifold`
(`manifold_isFixedPt`) and uniqueness (`manifold_unique`).

**`O(ε)` `C⁰`-closeness** (`GraphTransformData.manifold_dist_base_le`). The fixed-point distance
estimate `dist x (fixedPoint f) ≤ dist x (f x) / (1 - q)` applied to the base section bounds the
perturbed manifold's supremum distance from the base by `defect / (1 - q)`. With `defect = O(ε)` this
is the `O(ε)` `C⁰`-closeness `‖M_ε - M_0‖_∞ ≤ O(ε)`: the persisted manifold is a small perturbation
of the unperturbed graph.

**Perturbation continuity** (`GraphTransformData.manifold_dist_le_of_op_dist_le`). Two data with the
same factor `q` whose operators stay within `C` in the supremum metric have fixed-point manifolds
within `C / (1 - q)`, the Lipschitz dependence of the persisted manifold on the operator
(`ContractingWith.fixedPoint_lipschitz_in_map`).

**Spectral-gap constructor** (`GraphTransformData.ofSpectralGap`). Packages the contraction from
geometric data: a fibre Lipschitz/drift constant `Lf` strictly below the rate `λ` gives the factor
`q = Lf / λ < 1`, and an `O(ε)` drift defect `defect = ε · C`, so the closeness reads
`‖M_ε - M_0‖_∞ ≤ ε · C / (1 - Lf / λ)`. This is the genuine spectral-gap criterion: the rate `λ`
dominating the perturbation Lipschitz term is exactly what closes the contraction.

**Scope.** This builds the perturbed invariant manifold `M_ε` as the
fixed-point section and proves its existence, uniqueness, and `O(ε)` `C⁰`-closeness to `M_0`. The
remaining piece of the full Fenichel theorem is *local invariance of `M_ε` under the coupled
ε-flow*: that the graph of the fixed-point section is forward-invariant under `ẏ = ε·g`, `ż = fast y z`.
That conclusion needs the time-one (or short-time) flow map of the coupled field realized as the
concrete graph-transform operator `T`, i.e. the ODE plumbing tying `T`'s fixed point to flow
invariance.

Depends on: `CRNT.Dynamics.FenichelC1Manifold`,
`Mathlib.Topology.MetricSpace.Contracting`, `Mathlib.Topology.ContinuousMap.Bounded.Normed`.
-/

open Function
open scoped NNReal BoundedContinuousFunction

namespace ODE

variable {Y : Type*} [TopologicalSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

/-- **Graph-transform data** for a Lyapunov–Perron contraction on bounded sections `Y →ᵇ E`.

`op` is the graph-transform operator induced by a slow–fast field; `factor < 1` is its supremum-metric
contraction factor (the spectral-gap ratio of the fibre Lipschitz/drift terms to the contraction
rate `λ`); `op_dist_le` is the displacement bound the contraction rests on; `base` is the unperturbed
manifold section (`σ ≡ manifoldMap` realized as a bounded section); and `defect_le` bounds the drift
the operator applies to `base` by the `O(ε)` quantity `defect`. -/
structure GraphTransformData (Y : Type*) [TopologicalSpace Y]
    (E : Type*) [NormedAddCommGroup E] [CompleteSpace E] where
  /-- The graph-transform / Lyapunov–Perron operator on bounded sections. -/
  op : (Y →ᵇ E) → (Y →ᵇ E)
  /-- The supremum-metric contraction factor — the spectral-gap ratio `(Lipschitz/drift)/λ`. -/
  factor : ℝ≥0
  /-- The factor is `< 1`: the rate `λ` dominates the perturbation terms. -/
  factor_lt_one : factor < 1
  /-- The displacement bound the contraction rests on, in the supremum metric. -/
  op_dist_le : ∀ σ τ : Y →ᵇ E, dist (op σ) (op τ) ≤ factor * dist σ τ
  /-- The unperturbed manifold section `M_0`, realized as a bounded continuous section. -/
  base : Y →ᵇ E
  /-- The `O(ε)` drift defect: the displacement the operator applies to the base graph. -/
  defect : ℝ
  /-- The defect bound `dist (op base) base ≤ defect`. -/
  defect_le : dist (op base) base ≤ defect

namespace GraphTransformData

variable (G : GraphTransformData Y E)

/-- **The graph transform is a contraction.** The supremum-metric displacement bound makes the
operator `ContractingWith G.factor` on the complete metric space `Y →ᵇ E`. -/
theorem isContracting : ContractingWith G.factor G.op :=
  ⟨G.factor_lt_one, LipschitzWith.of_dist_le_mul G.op_dist_le⟩

/-- **The perturbed invariant manifold `M_ε`.** The unique fixed-point section of the graph transform,
furnished by the Banach fixed-point theorem (`ContractingWith.fixedPoint`) on `Y →ᵇ E`. Its graph is
Fenichel's persisted manifold. -/
noncomputable def manifold : Y →ᵇ E :=
  G.isContracting.fixedPoint G.op

/-- The perturbed manifold section is a fixed point of the graph transform: `op M_ε = M_ε`. -/
theorem manifold_isFixedPt : G.op G.manifold = G.manifold :=
  G.isContracting.fixedPoint_isFixedPt

/-- **Uniqueness of the perturbed manifold.** Any fixed-point section of the graph transform equals
the constructed `manifold`; the persisted manifold is unique. -/
theorem manifold_unique {σ : Y →ᵇ E} (hσ : G.op σ = σ) : σ = G.manifold :=
  G.isContracting.fixedPoint_unique hσ

/-- **`O(ε)` `C⁰`-closeness of `M_ε` to `M_0`.** The supremum distance of the perturbed manifold
from the base section is bounded by `defect / (1 - factor)`. With `defect = O(ε)` and `factor < 1`
this is the `O(ε)` `C⁰`-closeness `‖M_ε - M_0‖_∞ ≤ O(ε)`: the persisted manifold is a small
perturbation of the unperturbed graph. -/
theorem manifold_dist_base_le :
    dist G.base G.manifold ≤ G.defect / (1 - G.factor) := by
  refine le_trans (G.isContracting.dist_fixedPoint_le G.base) ?_
  gcongr
  · exact G.isContracting.one_sub_K_pos.le
  · rw [dist_comm]; exact G.defect_le

/-- **Perturbation continuity of the persisted manifold.** If two graph-transform data share the
contraction factor `factor` and their operators stay within `C` in the supremum metric, their
perturbed manifolds are within `C / (1 - factor)`. This is the Lipschitz dependence of the persisted
manifold on the operator, the stability underlying `O(ε)` comparisons between perturbation levels. -/
theorem manifold_dist_le_of_op_dist_le (H : GraphTransformData Y E) (hfac : H.factor = G.factor)
    {C : ℝ} (hC : ∀ σ, dist (G.op σ) (H.op σ) ≤ C) :
    dist G.manifold H.manifold ≤ C / (1 - G.factor) := by
  have hH : ContractingWith G.factor H.op := hfac ▸ H.isContracting
  have hkey := G.isContracting.fixedPoint_lipschitz_in_map hH hC
  have hfp : ContractingWith.fixedPoint H.op hH = H.manifold :=
    H.isContracting.fixedPoint_unique (ContractingWith.fixedPoint_isFixedPt hH)
  rwa [hfp] at hkey

end GraphTransformData

/-- **Spectral-gap constructor for the graph transform.** Packages a Lyapunov–Perron contraction
from geometric data. The operator `op` has supremum-metric displacement factor `Lf / λ`, where `Lf`
is the combined fibre Lipschitz/drift constant and `λ = rate` the fibre contraction rate; the
spectral gap `Lf < λ` makes the factor `< 1`. The drift defect is the `O(ε)` quantity `ε · C`. The
resulting `GraphTransformData` yields, via `manifold_dist_base_le`, the closeness
`‖M_ε - M_0‖_∞ ≤ ε · C / (1 - Lf / λ)`: the genuine spectral-gap criterion in which the rate `λ`
dominating the perturbation Lipschitz term `Lf` is exactly what closes the contraction. -/
noncomputable def GraphTransformData.ofSpectralGap
    (op : (Y →ᵇ E) → (Y →ᵇ E)) (base : Y →ᵇ E)
    (rate Lf : ℝ) (hrate : 0 < rate) (hLf : 0 ≤ Lf) (hgap : Lf < rate)
    (op_dist_le : ∀ σ τ : Y →ᵇ E, dist (op σ) (op τ) ≤ (Lf / rate) * dist σ τ)
    (ε C : ℝ) (defect_le : dist (op base) base ≤ ε * C) :
    GraphTransformData Y E where
  op := op
  factor := NNReal.mk (Lf / rate) (div_nonneg hLf hrate.le)
  factor_lt_one := by
    change (Lf / rate : ℝ) < 1
    rw [div_lt_one hrate]
    exact hgap
  op_dist_le := fun σ τ => op_dist_le σ τ
  base := base
  defect := ε * C
  defect_le := defect_le

end ODE
