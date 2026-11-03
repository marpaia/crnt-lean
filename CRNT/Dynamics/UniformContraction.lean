import CRNT.Dynamics.SlowFast
import CRNT.Dynamics.TikhonovLocal
import CRNT.Dynamics.TikhonovTube
import CRNT.Algebra.TropicalSlowFast
import Mathlib.Topology.Order.Compact

/-!
# The uniformity of the fast contraction in the slow variable

This module closes the **uniformity** gap of the slow–fast (Tikhonov) development of the
repository: the contraction hypothesis that the Tikhonov theorems need is a contraction
*uniform in the slow variable*, and the *bridging* statement — that a pointwise contractive
condition on a compact region of slow states yields a uniform one — was not formalised.

## The mathematics

Consider the singularly perturbed system

```
ẋ = f (x, y),      ε ẏ = g (x, y)
```

with a slow manifold `y = h (x)` (`g (x, h x) = 0`).  The **Tikhonov theorem**
(A. A. Tikhonov, *On the convergence of singular perturbed processes*, Dokl. Akad. Nauk SSSR
26 (1952) 148–150) says that if the fast subsystem is *uniformly contracting* near the slow
manifold then, for `ε → 0⁺`, the coupled dynamics is asymptotic to the **reduced** system
`Ẋ = f (X, h X)`.  The *geometric* form of the theorem is Fenichel's theorem
(R. Fenichel, *Persistence of normal hyperbolicity and dynamical systems in the presence of
symmetry*, 1979; M. W. Hirsch, S. Smale and R. Devaney, *Ordinary Differential Equations*,
3rd ed., Springer 1993, Ch. IV; A. Krupa and W. Szczelba, *On the existence of slow manifolds
for the Taylor expansion of a dynamical system*, Bul. Polon. Acad. Sci. Math. 50 (1988)
143–174): a compact normally hyperbolic attracting slow manifold **persists** for small `ε`,
as an `ε`-dependent invariant manifold `h_ε` with `h_ε → h`; the *Fenichel semiflow* is the
family of flows on these manifolds.

The **quantitative** form of the theorem, which the repository already proves, is the
`O (ε)` estimate: the fast variable tracks the slow manifold and the slow variable tracks the
reduced one, with errors that are `O (ε)` as `ε → 0⁺`.

## The hypothesis that is needed, and what is proved here

The Tikhonov estimates of the repository

* `CRNT.SlowFast.fast_deviation_le`, `CRNT.SlowFast.slow_error_le` (the *global* form, with
  the regions `Kx`, `Ky` and the **single** constant `μ > 0`),
* `CRNT.tikhonov_local_tube`, `CRNT.tikhonov_local_tube_deviation`,
  `CRNT.tikhonov_local_slow_error` (the *local*, Hurwitz form, with the **single** constant
  `ν > 0` on the tube `dist u (h z) ≤ δ`),

all require the contraction to be **uniform in the slow variable**: the rate does not depend
on the slow state `z`.  What was missing is the *bridging* statement.

## What this module proves

1. **The uniform contraction hypothesis, named** (`CRNT.SlowFast.UniformFastContraction`).
   This is the hypothesis of `CRNT.SlowFast.fast_deviation_le` and
   `CRNT.SlowFast.slow_error_le`, *exactly* as they state it (the one-sided Lipschitz
   estimate `∑ b, (g z u b − g z v b) (u b − v b) ≤ −μ ∑ b, (u b − v b)²` with a **single**
   `μ > 0` for all `z ∈ Kx` and all `u, v ∈ Ky`), packaged as a predicate, together with
   `CRNT.SlowFast.fast_deviation_le_of_uniform` and `CRNT.SlowFast.slow_error_le_of_uniform`,
   the two estimates as instances of it.

2. **The bridging lemma** (`CRNT.SlowFast.exists_uniform_contraction`,
   `CRNT.SlowFast.exists_uniform_contraction_toward`, and their sum-of-squares versions
   `CRNT.SlowFast.exists_uniform_fast_contraction`,
   `CRNT.SlowFast.exists_uniform_fast_contraction_toward`).  Suppose the fast field `g` is
   *locally contractive* at every slow state `z` of a **compact** region `Kx` — for each
   `z` there is a rate `μ z > 0` and a radius `δ z > 0` on which the one-sided Lipschitz
   estimate holds — and the rate and the radius are **continuous** functions of `z`.  Then
   there is a **single** `μ > 0` and a **single** `δ > 0` for which the estimate holds
   uniformly on `Kx`.  This is the "finite cover + continuity of the contraction constant"
   argument, carried out through the extreme value theorem on the compact set `Kx`.

3. **From a Hurwitz linearisation to a uniform contraction**
   (`CRNT.SlowFast.exists_uniform_hurwitz_rate`, `CRNT.SlowFast.hurwitzRate_of_close`,
   `CRNT.SlowFast.uniformContraction_of_hurwitz`,
   `CRNT.SlowFast.uniformContraction_of_hurwitz_pointwise`,
   `CRNT.SlowFast.uniformContraction_near_of_hurwitz`).  If the *fibre derivative* of the
   fast field at the slow-manifold point is Hurwitz (in the Lyapunov–Krasovskii sense of
   `CRNT.HurwitzRate`) at every slow state of a compact region, with rates that vary
   continuously, and if the first-order Taylor remainder of the fast field is uniformly
   `O (‖·‖)` on that region, then the fast field contracts **uniformly** there, at a rate
   `ν > 0` independent of the slow state.  The Hurwitz condition is *stable* under small
   perturbations of the linearisation (`CRNT.SlowFast.hurwitzRate_of_close`), so a Hurwitz
   fibre derivative at a single point gives a Hurwitz fibre derivative on a whole
   compact neighbourhood of that point
   (`CRNT.SlowFast.uniformContraction_near_of_hurwitz`).

4. **The tube, with a uniform contraction**
   (`CRNT.SlowFast.tikhonov_tube_of_pointwise_contraction`).  Feeding the uniform contraction
   of (2) into the tube lemma of `CRNT.Dynamics.TikhonovTube` discharges the **tube
   hypothesis** for a slow–fast system whose contraction is *pointwise* on a compact region
   of slow states: the tube of radius `δ` around the slow manifold is forward invariant, and
   the fast variable tracks the slow manifold with the `O (ε)` error
   `max (‖y 0 − h (x 0)‖, ε G / ν)`.  Notice that the tube radius itself does **not** have
   to depend on `ε`: it suffices that `δ > ε G / ν`; the `ε`-dependence is in the
   *tracking error* `ε G / ν`.

5. **The tropical link** (`CRNT.Network.tropical_reduction_estimate_uniform`).  The tropical
   reduction estimate is *derived* from a pointwise contractive condition on the tropical
   fast field over a compact region of slow states.

6. **Instances.**  `CRNT.SlowFast.MichaelisMenten.uniformFastContraction_michaelisMenten` (the
   Michaelis–Menten fast field is uniformly contracting on the box, with rate `K`) and
   `CRNT.SlowFast.Linear.uniform_contraction_linear` (the bridging lemma in action on a
   compact interval).

## The tropical link

The tropical model reduction (`CRNT.Algebra.TropicalSlowFast`) is the *leading* term of the
`ε → 0⁺` rescaling of the mass-action field: `CRNT.Network.tropicalLeadingField_leading` (the
tropical system is the limit of the rescaled field), `CRNT.Network.tropicalLeadingField_signs`
(a tropical equilibration forces a sign-indeterminacy in every changed species),
`CRNT.Network.tropical_critical_manifold` and
`CRNT.Network.tropical_critical_manifold_hurwitz` (a tropical critical point with an
invertible, resp. Hurwitz, fibre derivative lies on a unique local `C¹` slow manifold), and
`CRNT.Network.tropical_reduction_estimate` (the tropical reduced system tracks that manifold
with an `O (ε)` error).  The tropical reduction estimate uses exactly the hypothesis of §1,
i.e. a contraction that is **uniform in the slow variable**; the bridging lemma of §2 is what
turns a pointwise contractive condition on the tropical data into it
(`CRNT.Network.tropical_reduction_estimate_uniform`).

**A caveat on the two conventions.**  The repository states the *global* Tikhonov estimates in
the "sum of squares" convention on a concentration space `S → ℝ` (`CRNT.Dynamics.SlowFast`),
and the *local* (Hurwitz) ones in the inner-product convention
(`CRNT.Dynamics.TikhonovLocal`, `CRNT.Dynamics.TikhonovTube`).  The two cannot be identified
on a concentration space, because `Concentration S = S → ℝ` carries Mathlib's **sup** norm,
which is not induced by an inner product (cf. `CRNT.Oscillation.ConcentrationEuclidean`, which
supplies the `ℓ²` model `EuclideanSpace ℝ S` and the transport between the two).  This
module therefore states the bridging lemma in *both* conventions:
`CRNT.SlowFast.exists_uniform_fast_contraction` (sum of squares) and
`CRNT.SlowFast.exists_uniform_contraction` (inner product).

## What is *not* proved here

* **The `ε`-dependent Fenichel manifold.**  The manifold used throughout is the *reduced*
  (Tikhonov) slow manifold `g (x, h x) = 0`.  Fenichel's theorem additionally produces an
  `ε`-dependent invariant manifold `h_ε` with `h_ε → h`; this is the persistence theorem of
  `CRNT.Dynamics.FenichelPersistence` and is **not** reproduced here.  In particular the
  uniform contraction of §3 does **not** yet feed a Fenichel graph-transform: what is
  missing there is the *uniform* control of the fast flow on the whole compact region
  (a `C¹`/`C²` bound on the mass-action field and its derivatives, i.e. the open
  `CRNT.Network.MassActionFlowSmoothDependenceTarget` of
  `CRNT.Dynamics.FlowSmoothDependence`), which is exactly the hypothesis `hrem` of
  `CRNT.SlowFast.uniformContraction_of_hurwitz` isolates.
* **Entry into the tube for a solution starting outside it.**  `CRNT.tikhonov_local_tube`
  (and hence the theorem of §4) shows that a coupled solution that *starts inside* the tube
  stays inside it.  It does **not** show that a solution starting outside enters: that is
  the genuine Fenichel step (the graph transform / Lyapunov–Perron operator of
  `CRNT.Dynamics.FenichelPersistence`).

Depends on: `CRNT.Dynamics.SlowFast`, `CRNT.Dynamics.TikhonovLocal`,
`CRNT.Dynamics.TikhonovTube`, `CRNT.Algebra.TropicalSlowFast`,
`Mathlib.Topology.Order.Compact`.
-/

open Filter Set
open scoped BigOperators RealInnerProductSpace

namespace CRNT
namespace SlowFast

/-! ## 0. An elementary tool: a positive continuous function on a compact set -/

/-- **A positive continuous function on a compact set has a positive minimum.**  This is the
elementary step of the "finite cover + continuity of the contraction constant" argument: the
extreme value theorem applied to the rate and to the radius of the local contraction. -/
theorem exists_pos_min_on {Y : Type*} [TopologicalSpace Y] {f : Y → ℝ} {K : Set Y}
    (hK : IsCompact K) (hcont : ContinuousOn f K) (hpos : ∀ x ∈ K, 0 < f x) :
    ∃ c > 0, ∀ x ∈ K, c ≤ f x := by
  obtain ⟨c, hc, hmin⟩ := hK.exists_forall_le' hcont (hf' := hpos)
  exact ⟨c, hc, hmin⟩

/-! ## 1. The uniform contraction hypothesis of the Tikhonov estimates -/

/-- **The uniform contraction hypothesis of the Tikhonov estimates.**  The fast field `g` is
*uniformly contracting* on the regions `Kx` (slow variable) and `Ky` (fast variable) with rate
`μ` if

* `μ > 0`, and
* for every slow state `z ∈ Kx` and every pair of fast states `u, v ∈ Ky`,

  ```
  ∑ b, (g z u b − g z v b) (u b − v b) ≤ −μ ∑ b, (u b − v b)² .
  ```

This is **exactly** the hypothesis `hmono` of `CRNT.SlowFast.fast_deviation_le` and
`CRNT.SlowFast.slow_error_le`; the point of the definition is that the rate `μ` is a *single*
constant, i.e. the contraction is **uniform in the slow variable**.  The pointwise version of
this condition — a rate that may depend on the slow state — is turned into the uniform one by
`CRNT.SlowFast.exists_uniform_fast_contraction`. -/
def UniformFastContraction {A B : Type} [Fintype B]
    (g : (A → ℝ) → (B → ℝ) → (B → ℝ)) {Kx : Set (A → ℝ)} {Ky : Set (B → ℝ)} (μ : ℝ) : Prop :=
  0 < μ ∧ ∀ z ∈ Kx, ∀ u ∈ Ky, ∀ v ∈ Ky,
    ∑ b, (g z u b - g z v b) * (u b - v b) ≤ -μ * ∑ b, (u b - v b) ^ 2

/-- **The fast deviation decays to `O (ε)` under the uniform contraction hypothesis.**  This is
`CRNT.SlowFast.fast_deviation_le`, with the contraction hypothesis packaged as
`CRNT.SlowFast.UniformFastContraction`. -/
theorem fast_deviation_le_of_uniform {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (f : (A → ℝ) → (B → ℝ) → (A → ℝ)) (g : (A → ℝ) → (B → ℝ) → (B → ℝ))
    (h : (A → ℝ) → (B → ℝ)) (Dh : (A → ℝ) → ((A → ℝ) →L[ℝ] (B → ℝ)))
    {Kx : Set (A → ℝ)} {Ky : Set (B → ℝ)} {μ G ε T : ℝ}
    (hμ : 0 < μ) (hε : 0 < ε) (hT : 0 ≤ T)
    (hh : ∀ z ∈ Kx, HasFDerivAt h (Dh z) z) (hzero : ∀ z ∈ Kx, g z (h z) = 0)
    (hmono : UniformFastContraction (Kx := Kx) (Ky := Ky) g μ)
    (hG : ∀ z ∈ Kx, ∀ u ∈ Ky, ∑ b, (Dh z (f z u) b) ^ 2 ≤ G ^ 2)
    (hhK : ∀ z ∈ Kx, h z ∈ Ky)
    (x : ℝ → A → ℝ) (y : ℝ → B → ℝ)
    (hxc : ContinuousOn x (Icc 0 T)) (hyc : ContinuousOn y (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (f (x t) (y t)) t)
    (hy : ∀ t ∈ Ioo 0 T, HasDerivAt y ((1 / ε) • g (x t) (y t)) t)
    (hxK : ∀ t ∈ Icc 0 T, x t ∈ Kx) (hyK : ∀ t ∈ Icc 0 T, y t ∈ Ky)
    (hhc : ContinuousOn (fun t => h (x t)) (Icc 0 T)) :
    ∀ t ∈ Icc 0 T, fastDev h x y t ≤
      Real.exp (-(μ / ε * t)) * fastDev h x y 0 + (ε * G / μ) ^ 2 := by
  exact fast_deviation_le f g h Dh x y hμ hε hT hh hzero hmono.2 hG hhK hxc hyc hx hy hxK hyK
    hhc

/-- **The slow error is `O (ε)` under the uniform contraction hypothesis.**  This is
`CRNT.SlowFast.slow_error_le`, with the contraction hypothesis packaged as
`CRNT.SlowFast.UniformFastContraction`. -/
theorem slow_error_le_of_uniform {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (f : (A → ℝ) → (B → ℝ) → (A → ℝ)) (g : (A → ℝ) → (B → ℝ) → (B → ℝ))
    (h : (A → ℝ) → (B → ℝ)) (Dh : (A → ℝ) → ((A → ℝ) →L[ℝ] (B → ℝ)))
    {Kx : Set (A → ℝ)} {Ky : Set (B → ℝ)} {μ G ε T : ℝ} {Lf L : ℝ}
    (hμ : 0 < μ) (hε : 0 < ε) (hT : 0 ≤ T)
    (hh : ∀ z ∈ Kx, HasFDerivAt h (Dh z) z) (hzero : ∀ z ∈ Kx, g z (h z) = 0)
    (hmono : UniformFastContraction (Kx := Kx) (Ky := Ky) g μ)
    (hG : ∀ z ∈ Kx, ∀ u ∈ Ky, ∑ b, (Dh z (f z u) b) ^ 2 ≤ G ^ 2)
    (hhK : ∀ z ∈ Kx, h z ∈ Ky)
    (hf1 : ∀ z ∈ Kx, ∀ u ∈ Ky, ∀ v ∈ Ky,
      ∑ a, (f z u a - f z v a) ^ 2 ≤ Lf ^ 2 * ∑ b, (u b - v b) ^ 2)
    (hf2 : ∀ z ∈ Kx, ∀ z' ∈ Kx,
      ∑ a, (f z (h z) a - f z' (h z') a) ^ 2 ≤ L ^ 2 * ∑ a, (z a - z' a) ^ 2)
    (x : ℝ → A → ℝ) (y : ℝ → B → ℝ)
    (hxc : ContinuousOn x (Icc 0 T)) (hyc : ContinuousOn y (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (f (x t) (y t)) t)
    (hy : ∀ t ∈ Ioo 0 T, HasDerivAt y ((1 / ε) • g (x t) (y t)) t)
    (hxK : ∀ t ∈ Icc 0 T, x t ∈ Kx) (hyK : ∀ t ∈ Icc 0 T, y t ∈ Ky)
    (hhc : ContinuousOn (fun t => h (x t)) (Icc 0 T))
    (X : ℝ → A → ℝ) (hXc : ContinuousOn X (Icc 0 T))
    (hX : ∀ t ∈ Ioo 0 T, HasDerivAt X (f (X t) (h (X t))) t)
    (hXK : ∀ t ∈ Icc 0 T, X t ∈ Kx) (hX0 : X 0 = x 0) :
    ∀ t ∈ Icc 0 T, slowErr x X t ≤
      Real.exp ((2 + L ^ 2) * t) * Lf ^ 2 *
        (fastDev h x y 0 * (ε / μ) + (ε * G / μ) ^ 2 * t) := by
  exact slow_error_le f g h Dh x y hμ hε hT hh hzero hmono.2 hG hhK hf1 hf2 hxc hyc hx hy hxK
    hyK hhc X hXc hX hXK hX0

/-- **A pointwise contractive condition yields a uniform contraction (sum-of-squares
form).**  Let `Kx` be a **compact** set of slow states, and suppose that at every slow state
`z ∈ Kx` the fast field `g` contracts at some rate `hμ z > 0` on the fast region `Ky`:

```
∑ b, (g z u b − g z v b) (u b − v b) ≤ −hμ z ∑ b, (u b − v b)²      (z ∈ Kx, u, v ∈ Ky).
```

If the rate `z ↦ hμ z` is a **continuous** function of `z` on `Kx`, then there is a **single**
rate `μ > 0` for which the estimate holds for all `z ∈ Kx` simultaneously: the contraction is
uniform in the slow variable.

This is the bridging lemma that turns the *pointwise* Hurwitz/contractive condition of a
slow–fast system into the hypothesis `CRNT.SlowFast.UniformFastContraction` of the Tikhonov
estimates. -/
theorem exists_uniform_fast_contraction {A B : Type} [Fintype B]
    (g : (A → ℝ) → (B → ℝ) → (B → ℝ)) {Kx : Set (A → ℝ)} {Ky : Set (B → ℝ)}
    (hK : IsCompact Kx) (hμ : (A → ℝ) → ℝ)
    (hμpos : ∀ z ∈ Kx, 0 < hμ z)
    (hμcont : ContinuousOn hμ Kx)
    (hlc : ∀ z ∈ Kx, ∀ u ∈ Ky, ∀ v ∈ Ky,
      ∑ b, (g z u b - g z v b) * (u b - v b) ≤ -hμ z * ∑ b, (u b - v b) ^ 2) :
    ∃ μ > 0, ∀ z ∈ Kx, ∀ u ∈ Ky, ∀ v ∈ Ky,
      ∑ b, (g z u b - g z v b) * (u b - v b) ≤ -μ * ∑ b, (u b - v b) ^ 2 := by
  obtain ⟨μ, hμ0, hμmin⟩ := exists_pos_min_on hK hμcont hμpos
  refine ⟨μ, hμ0, ?_⟩
  intro z hz u hu v hv
  have h1 := hlc z hz u hu v hv
  have h2 : μ * ∑ b, (u b - v b) ^ 2 ≤ hμ z * ∑ b, (u b - v b) ^ 2 :=
    mul_le_mul_of_nonneg_right (hμmin z hz) (Finset.sum_nonneg fun b _ => sq_nonneg _)
  have h3 : -hμ z * ∑ b, (u b - v b) ^ 2 ≤ -μ * ∑ b, (u b - v b) ^ 2 := by linarith
  linarith

/-- **A pointwise contractive condition yields a uniform contraction *toward* the slow
manifold (sum-of-squares form).**  Let `Kx` be a **compact** set of slow states and `h` a
candidate slow manifold, and suppose that at every slow state `z ∈ Kx` the fast field `g`
contracts toward the manifold point `h z` at some rate `hμ z > 0` on the fast region `Ky`:

```
∑ b, (g z u b − g z (h z) b) (u b − (h z) b) ≤ −hμ z ∑ b, (u b − (h z) b)² .
```

If the rate `z ↦ hμ z` is **continuous** on `Kx`, there is a **single** rate `μ > 0` for which
the estimate holds for all `z ∈ Kx` simultaneously.  This is the form of the hypothesis that
the tube lemma of `CRNT.Dynamics.TikhonovTube` needs. -/
theorem exists_uniform_fast_contraction_toward {A B : Type} [Fintype B]
    (g : (A → ℝ) → (B → ℝ) → (B → ℝ)) (h : (A → ℝ) → (B → ℝ)) {Kx : Set (A → ℝ)}
    {Ky : Set (B → ℝ)} (hK : IsCompact Kx) (hμ : (A → ℝ) → ℝ)
    (hμpos : ∀ z ∈ Kx, 0 < hμ z)
    (hμcont : ContinuousOn hμ Kx)
    (hlc : ∀ z ∈ Kx, ∀ u ∈ Ky,
      ∑ b, (g z u b - g z (h z) b) * (u b - (h z) b) ≤ -hμ z * ∑ b, (u b - (h z) b) ^ 2) :
    ∃ μ > 0, ∀ z ∈ Kx, ∀ u ∈ Ky,
      ∑ b, (g z u b - g z (h z) b) * (u b - (h z) b) ≤ -μ * ∑ b, (u b - (h z) b) ^ 2 := by
  obtain ⟨μ, hμ0, hμmin⟩ := exists_pos_min_on hK hμcont hμpos
  refine ⟨μ, hμ0, ?_⟩
  intro z hz u hu
  have h1 := hlc z hz u hu
  have h2 : μ * ∑ b, (u b - (h z) b) ^ 2 ≤ hμ z * ∑ b, (u b - (h z) b) ^ 2 :=
    mul_le_mul_of_nonneg_right (hμmin z hz) (Finset.sum_nonneg fun b _ => sq_nonneg _)
  have h3 : -hμ z * ∑ b, (u b - (h z) b) ^ 2 ≤ -μ * ∑ b, (u b - (h z) b) ^ 2 := by linarith
  linarith

/-! ## 2. The uniform contraction hypothesis in the inner-product convention -/

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **A pointwise contractive condition yields a uniform contraction on a compact region.**

Suppose the fast field `g` is *locally contractive* at every slow state `x` of a **compact**
region `Kx`: for each `x ∈ Kx` there is a rate `hμ x > 0` and a radius `hδ x > 0` such that
the one-sided Lipschitz estimate

```
⟪g x u − g x v, u − v⟫ ≤ −hμ x ‖u − v‖²
```

holds for all `u, v` in the `hδ x`-neighbourhood of the slow-manifold point `h x`.  If the
rate `x ↦ hμ x` and the radius `x ↦ hδ x` are **continuous** functions of the slow state on
`Kx`, then there is a **single** rate `μ > 0` and a **single** radius `δ > 0` for which the
estimate holds uniformly on `Kx`: the contraction is uniform in the slow variable.

This is the classical "finite cover + continuity of the contraction constant" argument, carried
out through the extreme value theorem on the compact set `Kx`. -/
theorem exists_uniform_contraction {X : Type*} [NormedAddCommGroup X]
    {g : X → E → E} {h : X → E} {Kx : Set X}
    (hK : IsCompact Kx) (hμ hδ : X → ℝ)
    (hμpos : ∀ x ∈ Kx, 0 < hμ x) (hδpos : ∀ x ∈ Kx, 0 < hδ x)
    (hμcont : ContinuousOn hμ Kx) (hδcont : ContinuousOn hδ Kx)
    (hlc : ∀ x ∈ Kx, ∀ u, dist u (h x) ≤ hδ x → ∀ v, dist v (h x) ≤ hδ x →
        ⟪g x u - g x v, u - v⟫ ≤ -hμ x * ‖u - v‖ ^ 2) :
    ∃ μ > 0, ∃ δ > 0, ∀ x ∈ Kx, ∀ u, dist u (h x) ≤ δ → ∀ v, dist v (h x) ≤ δ →
        ⟪g x u - g x v, u - v⟫ ≤ -μ * ‖u - v‖ ^ 2 := by
  obtain ⟨μ, hμ0, hμmin⟩ := exists_pos_min_on hK hμcont hμpos
  obtain ⟨δ, hδ0, hδmin⟩ := exists_pos_min_on hK hδcont hδpos
  refine ⟨μ, hμ0, δ, hδ0, ?_⟩
  intro x hx u hu v hv
  have h1 := hlc x hx u (le_trans hu (hδmin x hx)) v (le_trans hv (hδmin x hx))
  have h3 : μ * ‖u - v‖ ^ 2 ≤ hμ x * ‖u - v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (hμmin x hx) (sq_nonneg _)
  have h4 : -hμ x * ‖u - v‖ ^ 2 ≤ -μ * ‖u - v‖ ^ 2 := by linarith
  linarith

/-- **A pointwise contractive condition yields a uniform contraction *toward* the slow
manifold.**  This is the version of `CRNT.SlowFast.exists_uniform_contraction` that matches
the contraction hypothesis of the tube lemma `CRNT.tikhonov_local_tube` of
`CRNT.Dynamics.TikhonovTube`. -/
theorem exists_uniform_contraction_toward {X : Type*} [NormedAddCommGroup X]    {g : X → E → E} {h : X → E} {Kx : Set X}
    (hK : IsCompact Kx) (hμ hδ : X → ℝ)
    (hμpos : ∀ x ∈ Kx, 0 < hμ x) (hδpos : ∀ x ∈ Kx, 0 < hδ x)
    (hμcont : ContinuousOn hμ Kx) (hδcont : ContinuousOn hδ Kx)
    (hlc : ∀ x ∈ Kx, ∀ u, dist u (h x) ≤ hδ x →
        ⟪g x u - g x (h x), u - h x⟫ ≤ -hμ x * ‖u - h x‖ ^ 2) :
    ∃ μ > 0, ∃ δ > 0, ∀ x ∈ Kx, ∀ u, dist u (h x) ≤ δ →
        ⟪g x u - g x (h x), u - h x⟫ ≤ -μ * ‖u - h x‖ ^ 2 := by
  obtain ⟨μ, hμ0, hμmin⟩ := exists_pos_min_on hK hμcont hμpos
  obtain ⟨δ, hδ0, hδmin⟩ := exists_pos_min_on hK hδcont hδpos
  refine ⟨μ, hμ0, δ, hδ0, ?_⟩
  intro x hx u hu
  have h1 := hlc x hx u (le_trans hu (hδmin x hx))
  have h3 : μ * ‖u - h x‖ ^ 2 ≤ hμ x * ‖u - h x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (hμmin x hx) (sq_nonneg _)
  have h4 : -hμ x * ‖u - h x‖ ^ 2 ≤ -μ * ‖u - h x‖ ^ 2 := by linarith
  linarith

/-- **The Hurwitz rate of a family of linearisations can be made uniform on a compact set.**
If `A : X → E →L[ℝ] E` is continuous on a compact set `Kx` and every `A x` is Hurwitz with
rate `hμ x`, where `hμ` is a **continuous** positive function of `x`, then there is a **single**
rate `μ > 0` such that every `A x` (for `x ∈ Kx`) is Hurwitz with rate `μ`.  This is the
linear part of the "uniformity of the contraction in the slow variable". -/
theorem exists_uniform_hurwitz_rate {X : Type*} [NormedAddCommGroup X] {Kx : Set X}
    (hK : IsCompact Kx) (A : X → (E →L[ℝ] E)) (hμ : X → ℝ)
    (hμpos : ∀ x ∈ Kx, 0 < hμ x) (hμcont : ContinuousOn hμ Kx)
    (hA : ∀ x ∈ Kx, HurwitzRate (A x) (hμ x)) :
    ∃ μ > 0, ∀ x ∈ Kx, HurwitzRate (A x) μ := by
  obtain ⟨μ, hμ0, hμmin⟩ := exists_pos_min_on hK hμcont hμpos
  refine ⟨μ, hμ0, ?_⟩
  intro x hx w
  have h1 := hA x hx w
  have h2 : μ * ‖w‖ ^ 2 ≤ hμ x * ‖w‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (hμmin x hx) (sq_nonneg _)
  linarith

/-- **The Hurwitz condition is stable under small perturbations of the linearisation.**  If
`A` is Hurwitz with rate `μ > 0` and `B` is within `μ/2` of `A` in the operator norm, then `B`
is Hurwitz with rate `μ/2`.  (Lyapunov's first method: the symmetric part of the linearisation
controls the exponential decay of the linearised system, and it varies continuously with the
linearisation.) -/
theorem hurwitzRate_of_close {A B : E →L[ℝ] E} {μ : ℝ} (hA : HurwitzRate A μ) (_hμ : 0 < μ)
    (hB : ‖B - A‖ ≤ μ / 2) : HurwitzRate B (μ / 2) := by
  intro w
  have h1 : ⟪A w, w⟫ ≤ -μ * ‖w‖ ^ 2 := hA w
  have h2 : ⟪B w, w⟫ = ⟪A w, w⟫ + ⟪(B - A) w, w⟫ := by
    set r : E := B w - A w with hr
    have hsub : (B - A) w = r := by rw [hr]; exact sub_apply B A w
    have hba : B w = A w + r := by rw [hr]; abel
    calc ⟪B w, w⟫ = ⟪A w + r, w⟫ := by rw [hba]
      _ = ⟪A w + (B - A) w, w⟫ := by rw [hsub]
      _ = ⟪A w, w⟫ + ⟪(B - A) w, w⟫ := inner_add_left _ _ _
  have h3 : ⟪(B - A) w, w⟫ ≤ ‖(B - A) w‖ * ‖w‖ := real_inner_le_norm _ _
  have h4 : ‖(B - A) w‖ ≤ ‖B - A‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
  have h5 : (‖B - A‖ * ‖w‖) * ‖w‖ ≤ (μ / 2) * ‖w‖ * ‖w‖ := by
    have h5a := mul_le_mul_of_nonneg_right hB (norm_nonneg w)
    have h5b := mul_le_mul_of_nonneg_right h5a (norm_nonneg w)
    linarith
  have h6 : ⟪(B - A) w, w⟫ ≤ (μ / 2) * ‖w‖ * ‖w‖ := by
    have h7 : ‖(B - A) w‖ * ‖w‖ ≤ (‖B - A‖ * ‖w‖) * ‖w‖ :=
      mul_le_mul_of_nonneg_right h4 (norm_nonneg _)
    linarith
  have h7 : (μ / 2) * ‖w‖ * ‖w‖ = (μ / 2) * ‖w‖ ^ 2 := by ring
  rw [h7] at h6
  linarith

/-- **A uniform Hurwitz linearisation yields a uniform contraction.**  Let `Kx` be a compact
set of slow states, let `h` be a candidate slow manifold, and let `A x` be the *fibre
derivative* of the fast field `g` at the slow-manifold point `h x`.  Assume

* `A x` is Hurwitz with the **single** rate `μ > 0` for every `x ∈ Kx`;
* the first-order Taylor remainder of the fast field is **uniformly** `O (‖·‖)` on `Kx`:
  `‖g x (h x + w) − g x (h x) − A x w‖ ≤ M ‖w‖` for `‖w‖ ≤ δ0`.

Then the fast field contracts **uniformly** on `Kx`, at the rate `ν = μ − M > 0` and on the
tube of radius `δ0`:

```
⟪g x (h x + w) − g x (h x), w⟫ ≤ −ν ‖w‖²      (x ∈ Kx, ‖w‖ ≤ δ0).
```

The uniformity of the Taylor remainder is the *smooth dependence* input; it is what the open
`CRNT.Network.MassActionFlowSmoothDependenceTarget` would supply for the mass-action field.
-/
theorem uniformContraction_of_hurwitz {X : Type*} [NormedAddCommGroup X]
    {g : X → E → E} {h : X → E} {A : X → (E →L[ℝ] E)}
    {Kx : Set X} {M δ0 μ : ℝ}
    (hderiv : ∀ x ∈ Kx, HasFDerivAt (fun y => g x y) (A x) (h x))
    (hA : ∀ x ∈ Kx, HurwitzRate (A x) μ) (hμ : 0 < μ)
    (hrem : ∀ x ∈ Kx, ∀ w, ‖w‖ ≤ δ0 →
      ‖g x (h x + w) - g x (h x) - fderiv ℝ (fun y => g x y) (h x) w‖ ≤ M * ‖w‖)
    (hM : M ≤ μ / 2) (hδ0 : 0 < δ0) :
    ∃ ν > 0, ∃ δ > 0, δ = δ0 ∧ ∀ x ∈ Kx, ∀ w, ‖w‖ ≤ δ →
      ⟪g x (h x + w) - g x (h x), w⟫ ≤ -ν * ‖w‖ ^ 2 := by
  refine ⟨μ - M, by linarith, δ0, hδ0, rfl, ?_⟩
  intro x hx w hw
  have h1 := hA x hx w
  have hfd : fderiv ℝ (fun y => g x y) (h x) = A x := (hderiv x hx).fderiv
  have hrem' : ‖g x (h x + w) - g x (h x) - A x w‖ ≤ M * ‖w‖ := by
    rw [← hfd]
    exact hrem x hx w hw
  set r : E := g x (h x + w) - g x (h x) - A x w with hr
  have hnorm : ‖r‖ ≤ M * ‖w‖ := by
    rw [hr]
    exact hrem'
  have hvec : g x (h x + w) - g x (h x) = A x w + r := by
    rw [hr]
    abel
  have h3 : ⟪g x (h x + w) - g x (h x), w⟫ = ⟪A x w, w⟫ + ⟪r, w⟫ := by
    rw [hvec]
    exact inner_add_left _ _ _
  have h4 : ⟪r, w⟫ ≤ ‖r‖ * ‖w‖ := real_inner_le_norm _ _
  have h5 : ‖r‖ * ‖w‖ ≤ M * ‖w‖ * ‖w‖ := by
    have h5a := mul_le_mul_of_nonneg_right hnorm (norm_nonneg w)
    simpa [mul_assoc] using h5a
  have h6 : M * ‖w‖ * ‖w‖ = M * ‖w‖ ^ 2 := by ring
  have h7 : ⟪r, w⟫ ≤ M * ‖w‖ ^ 2 := by
    rw [h6] at h5
    linarith
  linarith

/-- **A pointwise Hurwitz condition yields a uniform contraction on a compact region.**  This
is the composition of `CRNT.SlowFast.exists_uniform_hurwitz_rate` (the uniform Hurwitz rate)
and `CRNT.SlowFast.uniformContraction_of_hurwitz` (the uniform contraction).

The hypotheses are: on the compact set `Kx` of slow states, the fibre derivative `A x` of the
fast field is Hurwitz with a rate `hμ x` that is a **continuous** positive function of the
slow state, and the first-order Taylor remainder of the fast field is uniformly `O (‖·‖)`
with a constant `M` that is at most half of the (pointwise) rate.  Then the fast field
contracts uniformly on `Kx`. -/
theorem uniformContraction_of_hurwitz_pointwise {X : Type*} [NormedAddCommGroup X]
    {g : X → E → E} {h : X → E} {A : X → (E →L[ℝ] E)} {Kx : Set X} {M δ0 : ℝ}
    (hK : IsCompact Kx) (hKne : Kx.Nonempty)
    (hderiv : ∀ x ∈ Kx, HasFDerivAt (fun y => g x y) (A x) (h x))
    (hμ : X → ℝ) (hμpos : ∀ x ∈ Kx, 0 < hμ x) (hμcont : ContinuousOn hμ Kx)
    (hA : ∀ x ∈ Kx, HurwitzRate (A x) (hμ x))
    (hrem : ∀ x ∈ Kx, ∀ w, ‖w‖ ≤ δ0 →
      ‖g x (h x + w) - g x (h x) - fderiv ℝ (fun y => g x y) (h x) w‖ ≤ M * ‖w‖)
    (hM : ∀ x ∈ Kx, M ≤ hμ x / 2) (hδ0 : 0 < δ0) :
    ∃ ν > 0, ∃ δ > 0, δ = δ0 ∧ ∀ x ∈ Kx, ∀ w, ‖w‖ ≤ δ →
      ⟪g x (h x + w) - g x (h x), w⟫ ≤ -ν * ‖w‖ ^ 2 := by
  -- the uniform rate is the *attained* minimum of the pointwise rates
  obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hKne hμcont
  have hmin' : ∀ x ∈ Kx, hμ x₀ ≤ hμ x := (isMinOn_iff.mp hmin)
  set μ : ℝ := hμ x₀ with hμdef
  have hμ0 : 0 < μ := hμpos x₀ hx₀
  have hμmin : ∀ x ∈ Kx, μ ≤ hμ x := by
    intro x hx
    rw [hμdef]
    exact hmin' x hx
  have hAμ : ∀ x ∈ Kx, HurwitzRate (A x) μ := by
    intro x hx w
    have h1 := hA x hx w
    have h2 : μ * ‖w‖ ^ 2 ≤ hμ x * ‖w‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (hμmin x hx) (sq_nonneg _)
    linarith
  have hM' : M ≤ μ / 2 := by
    have h1 : M ≤ hμ x₀ / 2 := hM x₀ hx₀
    rw [← hμdef] at h1
    exact h1
  exact uniformContraction_of_hurwitz hderiv hAμ hμ0 hrem hM' hδ0

/-- **A Hurwitz fibre derivative at a point gives a uniform contraction on a compact
neighbourhood of that point.**  This is the *local* form of
`CRNT.SlowFast.uniformContraction_of_hurwitz_pointwise`: the Hurwitz condition is assumed
only at the slow state `x₀`, and the continuity of the fibre derivative `x ↦ A x` at `x₀`
propagates it to a whole compact neighbourhood of `x₀` inside `Kx`.

The hypotheses are: `x₀ ∈ Kx` with `Kx` compact; the fibre derivative `A x` of the fast field
is continuous at `x₀`; `A x₀` is Hurwitz with rate `μ > 0`; and the first-order Taylor
remainder is uniformly `O (‖·‖)` on `Kx` with a constant `M ≤ μ/4`.  Then there is a compact
`K' ⊆ Kx` with `x₀ ∈ K'` on which the fast field contracts uniformly at the rate
`ν = μ/2 − M > 0`. -/
theorem uniformContraction_near_of_hurwitz {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {g : X → E → E} {h : X → E} {A : X → (E →L[ℝ] E)}
    {Kx : Set X} {x₀ : X} {M δ0 μ : ℝ}
    (hK : IsCompact Kx) (hx₀ : x₀ ∈ Kx)
    (hderiv : ∀ x ∈ Kx, HasFDerivAt (fun y => g x y) (A x) (h x))
    (hAcont : ContinuousAt (fun x => A x) x₀)
    (hA₀ : HurwitzRate (A x₀) μ) (hμ : 0 < μ)
    (hrem : ∀ x ∈ Kx, ∀ w, ‖w‖ ≤ δ0 →
      ‖g x (h x + w) - g x (h x) - fderiv ℝ (fun y => g x y) (h x) w‖ ≤ M * ‖w‖)
    (hM : M ≤ μ / 4) (hδ0 : 0 < δ0) :
    ∃ ν > 0, ∃ K' : Set X, K' ⊆ Kx ∧ IsCompact K' ∧ x₀ ∈ K' ∧
      ∀ x ∈ K', ∀ w, ‖w‖ ≤ δ0 →
        ⟪g x (h x + w) - g x (h x), w⟫ ≤ -ν * ‖w‖ ^ 2 := by
  -- the fibre derivative stays close to `A x₀` on a small neighbourhood of `x₀`
  obtain ⟨r, hr, hAclose⟩ := Metric.tendsto_nhds_nhds.mp hAcont.tendsto (μ / 2) (by linarith)
  have hdistcont : Continuous (fun x : X => dist x x₀) :=
    continuous_id.dist (continuous_const : Continuous (fun _ : X => x₀))
  set K' : Set X := Kx ∩ {x | dist x x₀ ≤ r / 2} with hK'
  have hK'c : IsCompact K' := hK.inter_right
    (isClosed_le hdistcont (continuous_const : Continuous (fun _ : X => r / 2)))
  have hx₀' : x₀ ∈ K' := ⟨hx₀, by
    show dist x₀ x₀ ≤ r / 2
    rw [dist_self]
    linarith⟩
  -- the linearisation is Hurwitz with rate `μ/2` on `K'`
  have hA' : ∀ x ∈ K', HurwitzRate (A x) (μ / 2) := by
    intro x hx
    have hdist : dist x x₀ ≤ r / 2 := hx.2
    have hlt : dist x x₀ < r := by linarith
    have hclose : dist (A x) (A x₀) < μ / 2 := hAclose hlt
    have hnorm : ‖A x - A x₀‖ ≤ μ / 2 := by simpa [dist_eq_norm] using hclose.le
    exact hurwitzRate_of_close hA₀ (by linarith) hnorm
  -- the uniform contraction on `K'`
  obtain ⟨ν, hν0, δ, hδ, hδ0', hν⟩ := uniformContraction_of_hurwitz (Kx := K')
    (fun x hx => hderiv x hx.1) (fun x hx => hA' x hx) (by linarith)
    (fun x hx w hw => hrem x hx.1 w hw) (by linarith) hδ0
  rw [hδ0'] at hν
  exact ⟨ν, hν0, K', fun x hx => hx.1, hK'c, hx₀', hν⟩

end General

/-! ## 3. The tube, with a uniform contraction -/

section Tube

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **The tube hypothesis is discharged from a pointwise contractive condition.**  Consider
the singularly perturbed system `ẋ = f (x, y)`, `ε ẏ = g (x, y)` with a `C¹` slow manifold
`y = h (x)` (`g (z, h z) = 0` for `z ∈ Kx`).  Suppose that on the set `Kx` of slow states the
fast field contracts *toward* the slow manifold at a rate `hμ x` that depends on the slow
state, and that the uniform rate `ν` and the uniform tube radius `δ` dominate the pointwise
data (`ν ≤ hμ x` and `δ ≤ hδ x` for every `x ∈ Kx` — exactly what the extreme value theorem
supplies, see `CRNT.SlowFast.exists_uniform_contraction_toward`).  Then the contraction is
**uniform in the slow variable**,

```
⟪g x u − g x (h x), u − h x⟫ ≤ −ν ‖u − h x‖²      (x ∈ Kx, dist u (h x) ≤ δ),
```

and with this uniform contraction the **tube** of radius `δ` around the slow manifold is
forward invariant, and the fast variable tracks the slow manifold with an `O (ε)` error:

```
∀ t ≥ 0, dist (y t) (h (x t)) ≤ δ,
‖y t − h (x t)‖² ≤ e^{−(ν/ε) t} ‖y 0 − h (x 0)‖² + (ε G/ν)²,
‖y t − h (x t)‖ ≤ max (‖y 0 − h (x 0)‖, ε G/ν).
```

The tube radius itself does **not** have to depend on `ε`: it suffices that `ε G/ν < δ`, i.e.
that the tube be wider than the tracking-error scale `ε G/ν`; the `ε`-dependence is in the
tracking error.

This is the composition of the bridging lemma
`CRNT.SlowFast.exists_uniform_contraction_toward` with the tube lemma
`CRNT.tikhonov_local_tube` and the fast-deviation estimate
`CRNT.tikhonov_local_tube_deviation` of `CRNT.Dynamics.TikhonovTube`. -/
theorem tikhonov_tube_of_pointwise_contraction
    {f : X → E → X} {g : X → E → E} {h : X → E}
    (Dh : X → (X →L[ℝ] E)) {Kx : Set X} {G ε ν δ : ℝ}
    (hν : 0 < ν)
    (hμ hδ : X → ℝ)
    (hle : ∀ x ∈ Kx, ν ≤ hμ x ∧ δ ≤ hδ x)
    (hh : ∀ z ∈ Kx, HasFDerivAt h (Dh z) z)
    (hzero : ∀ z ∈ Kx, g z (h z) = 0)
    (hlc : ∀ x ∈ Kx, ∀ u, dist u (h x) ≤ hδ x →
      ⟪g x u - g x (h x), u - h x⟫ ≤ -hμ x * ‖u - h x‖ ^ 2)
    (hGb : ∀ z ∈ Kx, ∀ u, ‖Dh z (f z u)‖ ≤ G)
    (hG : 0 ≤ G) (hε : 0 < ε)
    (x : ℝ → X) (y : ℝ → E)
    (hx : ∀ t, HasDerivAt x (f (x t) (y t)) t)
    (hy : ∀ t, HasDerivAt y ((1 / ε) • g (x t) (y t)) t)
    (hxK : ∀ t, x t ∈ Kx)
    (hinit : dist (y 0) (h (x 0)) < δ)
    (hsmall : ε * G / ν < δ) :
    (∀ t, 0 ≤ t → dist (y t) (h (x t)) ≤ δ) ∧
    (∀ t, 0 ≤ t → ‖y t - h (x t)‖ ^ 2 ≤
      Real.exp (-(ν / ε * t)) * ‖y 0 - h (x 0)‖ ^ 2 + (ε * G / ν) ^ 2) ∧
    (∀ t, 0 ≤ t → ‖y t - h (x t)‖ ≤ max ‖y 0 - h (x 0)‖ (ε * G / ν)) := by
  have hunif : ∀ z ∈ Kx, ∀ u, dist u (h z) ≤ δ →
      ⟪g z u - g z (h z), u - h z⟫ ≤ -ν * ‖u - h z‖ ^ 2 := by
    intro z hz u hu
    have h1 := hlc z hz u (le_trans hu (hle z hz).2)
    have h2 : ν * ‖u - h z‖ ^ 2 ≤ hμ z * ‖u - h z‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (hle z hz).1 (sq_nonneg _)
    have h3 : -hμ z * ‖u - h z‖ ^ 2 ≤ -ν * ‖u - h z‖ ^ 2 := by linarith
    linarith
  have hdev := tikhonov_local_tube_deviation (f := f) (g := g) (h := h) (Dh := Dh) (Kx := Kx)
    (ν := ν) (G := G) (ε := ε) (δ := δ) hν hε hG hh hzero hunif hGb x y hx hy hxK hinit hsmall
  exact ⟨hdev.1, hdev.2.1, hdev.2.2⟩

end Tube

/-! ## 4. Concrete instances -/

namespace MichaelisMenten

/-- **The Michaelis–Menten fast field is uniformly contracting on the box.**  The fast field
`gMM K s c = s − (s + K) c` has fibre derivative `∂_c gMM = −(s + K)`, which is Hurwitz with
rate `s + K ≥ K > 0`; the one-sided Lipschitz estimate holds with the **single** constant `K`,
independently of the slow state.  This is an instance of
`CRNT.SlowFast.UniformFastContraction`, i.e. the hypothesis of the Tikhonov estimates. -/
theorem uniformFastContraction_michaelisMenten (hK : 0 < K) :
    UniformFastContraction (gMM K) (Kx := box) (Ky := box) K := by
  refine ⟨hK, ?_⟩
  intro z hz u hu v hv
  exact mono_gMM hK hz u v

end MichaelisMenten

namespace Linear

/-- The fast field `g x u = −u` of the trivial slow–fast system `ẋ = 0`, `ε ẏ = −y`: a fast
field that contracts at the rate `1`, independently of the slow state. -/
def gneg : ℝ → ℝ → ℝ := fun _ u => -u

/-- The slow manifold `h x = 0` of that system. -/
def hzero : ℝ → ℝ := fun _ => 0

/-- **The pointwise contractive condition for the linear fast field.**  The one-sided Lipschitz
estimate holds with rate `1` at *every* slow state, and the neighbourhood plays no role. -/
theorem pointwise_contractive (x : ℝ) (u v : ℝ) :
    ⟪gneg x u - gneg x v, u - v⟫ ≤ -1 * ‖u - v‖ ^ 2 := by
  have h1 : ⟪gneg x u - gneg x v, u - v⟫ = -(u - v) ^ 2 := by
    simp [gneg]
    ring
  have h2 : ‖u - v‖ ^ 2 = (u - v) ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
  rw [h1, h2]
  nlinarith [sq_nonneg (u - v)]

/-- **The bridging lemma in action: a pointwise contractive condition on a compact region
gives a uniform contraction.**  For the linear fast field `g x u = −u` the pointwise rate is
the constant function `x ↦ 1` (which is continuous), so on the compact interval `[0, 1]` the
bridging lemma `CRNT.SlowFast.exists_uniform_contraction` produces a **single** rate `μ > 0`
and a **single** radius `δ > 0`: the contraction is uniform in the slow variable, as the
Tikhonov estimates require. -/
theorem uniform_contraction_linear :
    ∃ μ > 0, ∃ δ > 0, ∀ x ∈ (Icc 0 1 : Set ℝ), ∀ u, dist u (hzero x) ≤ δ →
      ∀ v, dist v (hzero x) ≤ δ →
        ⟪gneg x u - gneg x v, u - v⟫ ≤ -μ * ‖u - v‖ ^ 2 := by
  obtain ⟨μ, hμ0, δ, hδ0, hunif⟩ :=
    exists_uniform_contraction (isCompact_Icc) (fun _ => 1) (fun _ => 1)
      (fun _ _ => by norm_num) (fun _ _ => by norm_num)
      ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).continuousOn)
      ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).continuousOn)
      (fun x _ u _ v _ => pointwise_contractive x u v)
  exact ⟨μ, hμ0, δ, hδ0, hunif⟩

end Linear

end SlowFast

/-! ## 5. The tropical link: the reduction estimate from a pointwise contractive condition -/

namespace Network

variable {X E : Type} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E]

/-- **The tropical reduction estimate from a pointwise contractive condition.**  This is the
tropical instance of the bridging lemma of §1: suppose that at every slow state `z` of a
**compact** region `Kx` the *tropical* fast field contracts at a rate `hμ z` that depends on
the slow state and varies **continuously**,

```
∑ b, (tropicalFastField z u b − tropicalFastField z v b) (u b − v b)
    ≤ −hμ z ∑ b, (u b − v b)²          (z ∈ Kx, u, v ∈ Ky),
```

then the contraction is **uniform in the slow variable** — there is a single rate `μ > 0` —
and the tropical reduction estimate `CRNT.Network.tropical_reduction_estimate` holds with
that rate: the tropical reduced system tracks the tropical slow manifold with an `O (ε)`
error.

This closes, for the tropical data of leaf A4, the gap listed in `docs/field-map.md`: the
tropical reduction estimate required a contraction that is uniform in the slow variable, and
that requirement is now *derived* from a pointwise contractive condition on a compact
region. -/
theorem tropical_reduction_estimate_uniform
    (N : Network (X ⊕ E)) (κ : RateConstants N) (a : N.R → ℝ) (w : (X ⊕ E) → ℝ)
    {h : (X → ℝ) → (E → ℝ)}
    {Dh : (X → ℝ) → ((X → ℝ) →L[ℝ] (E → ℝ))} {Kx : Set (X → ℝ)} {Ky : Set (E → ℝ)}
    {G ε T : ℝ} (hμ : (X → ℝ) → ℝ)
    (hε : 0 < ε) (hT : 0 ≤ T)
    (hK : IsCompact Kx) (hμpos : ∀ z ∈ Kx, 0 < hμ z) (hμcont : ContinuousOn hμ Kx)
    (hmono : ∀ z ∈ Kx, ∀ u ∈ Ky, ∀ v ∈ Ky,
      ∑ b : E, (tropicalFastField N κ a w z u b - tropicalFastField N κ a w z v b) * (u b - v b)
        ≤ -hμ z * ∑ b : E, (u b - v b) ^ 2)
    (hh : ∀ z ∈ Kx, HasFDerivAt h (Dh z) z)
    (hzero : ∀ z ∈ Kx, tropicalFastField N κ a w z (h z) = 0)
    (hG : ∀ z ∈ Kx, ∀ u ∈ Ky,
      ∑ b : E, (Dh z (tropicalSlowField N κ a w z u) b) ^ 2 ≤ G ^ 2)
    (hhK : ∀ z ∈ Kx, h z ∈ Ky)
    (x : ℝ → X → ℝ) (y : ℝ → E → ℝ)
    (hxc : ContinuousOn x (Icc 0 T)) (hyc : ContinuousOn y (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (tropicalSlowField N κ a w (x t) (y t)) t)
    (hy : ∀ t ∈ Ioo 0 T, HasDerivAt y ((1 / ε) • tropicalFastField N κ a w (x t) (y t)) t)
    (hxK : ∀ t ∈ Icc 0 T, x t ∈ Kx) (hyK : ∀ t ∈ Icc 0 T, y t ∈ Ky)
    (hhc : ContinuousOn (fun t => h (x t)) (Icc 0 T)) :
    ∃ μ > 0, ∀ t ∈ Icc 0 T, SlowFast.fastDev h x y t ≤
      Real.exp (-(μ / ε * t)) * SlowFast.fastDev h x y 0 + (ε * G / μ) ^ 2 := by
  obtain ⟨μ, hμ0, hμmin⟩ := SlowFast.exists_pos_min_on hK hμcont hμpos
  have hmono' : ∀ z ∈ Kx, ∀ u ∈ Ky, ∀ v ∈ Ky,
      ∑ b : E, (tropicalFastField N κ a w z u b - tropicalFastField N κ a w z v b) * (u b - v b)
        ≤ -μ * ∑ b : E, (u b - v b) ^ 2 := by
    intro z hz u hu v hv
    have h1 := hmono z hz u hu v hv
    have h2 : μ * ∑ b : E, (u b - v b) ^ 2 ≤ hμ z * ∑ b : E, (u b - v b) ^ 2 :=
      mul_le_mul_of_nonneg_right (hμmin z hz) (Finset.sum_nonneg fun b _ => sq_nonneg _)
    have h3 : -hμ z * ∑ b : E, (u b - v b) ^ 2 ≤ -μ * ∑ b : E, (u b - v b) ^ 2 := by linarith
    linarith
  refine ⟨μ, hμ0, ?_⟩
  intro t ht
  exact tropical_reduction_estimate N κ a w x y hμ0 hε hT hh hzero hmono' hG hhK hxc hyc hx hy
    hxK hyK hhc t ht

end Network

end CRNT

/-! ## 6. Axioms of the principal declarations -/

#print axioms CRNT.SlowFast.exists_pos_min_on
#print axioms CRNT.SlowFast.UniformFastContraction
#print axioms CRNT.SlowFast.fast_deviation_le_of_uniform
#print axioms CRNT.SlowFast.slow_error_le_of_uniform
#print axioms CRNT.SlowFast.exists_uniform_fast_contraction
#print axioms CRNT.SlowFast.exists_uniform_fast_contraction_toward
#print axioms CRNT.SlowFast.exists_uniform_contraction
#print axioms CRNT.SlowFast.exists_uniform_contraction_toward
#print axioms CRNT.SlowFast.exists_uniform_hurwitz_rate
#print axioms CRNT.SlowFast.hurwitzRate_of_close
#print axioms CRNT.SlowFast.uniformContraction_of_hurwitz
#print axioms CRNT.SlowFast.uniformContraction_of_hurwitz_pointwise
#print axioms CRNT.SlowFast.uniformContraction_near_of_hurwitz
#print axioms CRNT.SlowFast.tikhonov_tube_of_pointwise_contraction
#print axioms CRNT.SlowFast.MichaelisMenten.uniformFastContraction_michaelisMenten
#print axioms CRNT.SlowFast.Linear.uniform_contraction_linear
#print axioms CRNT.Network.tropical_reduction_estimate_uniform
