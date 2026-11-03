import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CRNT.Dynamics.MassActionAlgebra
import CRNT.LinearAlgebra.OrthogonalComplement
import CRNT.Stoich.Subspace

/-!
# The log-monomial ratio and the toric characterization

For two positive concentrations `x`, `y` the **log-monomial ratio** of a complex `c` is
`Φ(c) = log Ψ(x)_c − log Ψ(y)_c`, where `Ψ` is the complex monomial map. Because
`Ψ(x)_c = ∏_s x_s^{c_s}`, this expands to `Φ(c) = ∑ s, c_s · (log x_s − log y_s)` — the
pairing of the **log-ratio vector** `μ_s = log x_s − log y_s` with the complex `c`.

The reaction vectors span the stoichiometric subspace `S`, and the pairing of `μ` with a
reaction vector is `Φ(target) − Φ(source)`. Hence the toric condition
`μ ∈ orthSum S` — the orthogonality of the log-ratio to the stoichiometric subspace driving
Birch-style uniqueness — is **exactly** the statement that `Φ` is constant along every
reaction (equivalently, constant on each linkage class). This reduces the log-ratio
characterization of steady states to a constancy statement about `Φ`.

* `logMonomialRatio` — the per-complex log-ratio `Φ`.
* `logMonomialRatio_eq` — `Φ(c) = ∑ s, c_s · (log x_s − log y_s)`.
* `logRatio_mem_orthSum_iff` — `μ ∈ orthSum S ↔ Φ` is constant along every reaction.

Depends on:
`Mathlib.Analysis.SpecialFunctions.Log.Basic`, `CRNT.Dynamics.MassActionAlgebra`,
`CRNT.LinearAlgebra.OrthogonalComplement`, `CRNT.Stoich.Subspace`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The **log-monomial ratio** of a complex: `Φ(c) = log Ψ(x)_c − log Ψ(y)_c`. -/
noncomputable def logMonomialRatio (N : Network S) (x y : Concentration S)
    (c : N.ComplexIdx) : ℝ :=
  Real.log (N.complexMonomialVector x c) - Real.log (N.complexMonomialVector y c)

/-- The log of a complex monomial is the complex-weighted sum of the log concentrations. -/
theorem log_complexMonomialVector (N : Network S) {x : Concentration S} (hx : x.Positive)
    (c : N.ComplexIdx) :
    Real.log (N.complexMonomialVector x c) = ∑ s, (c.val s : ℝ) * Real.log (x s) := by
  rw [complexMonomialVector_apply, Complex.massActionMonomial,
    Real.log_prod (fun s _ => (pow_pos (hx s) _).ne')]
  exact Finset.sum_congr rfl fun s _ => Real.log_pow _ _

/-- The log-monomial ratio pairs the complex with the log-ratio vector
`μ_s = log x_s − log y_s`. -/
theorem logMonomialRatio_eq (N : Network S) {x y : Concentration S}
    (hx : x.Positive) (hy : y.Positive) (c : N.ComplexIdx) :
    N.logMonomialRatio x y c = ∑ s, (c.val s : ℝ) * (Real.log (x s) - Real.log (y s)) := by
  rw [logMonomialRatio, log_complexMonomialVector N hx, log_complexMonomialVector N hy,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- **The toric condition is constancy of `Φ` along reactions.** The log-ratio vector is
orthogonal to the stoichiometric subspace exactly when the log-monomial ratio `Φ` takes
equal values at the source and target of every reaction. Since reaction vectors span `S`
and pair with `μ` to give `Φ(target) − Φ(source)`, orthogonality to `S` is constancy of `Φ`
along reactions. -/
theorem logRatio_mem_orthSum_iff (N : Network S) {x y : Concentration S}
    (hx : x.Positive) (hy : y.Positive) :
    (fun s => Real.log (x s) - Real.log (y s)) ∈ orthSum N.stoichSubspace ↔
      ∀ r, N.logMonomialRatio x y (N.targetIdx r) = N.logMonomialRatio x y (N.sourceIdx r) := by
  set μ : S → ℝ := fun s => Real.log (x s) - Real.log (y s) with hμ
  have hkey : ∀ r, ∑ s, μ s * N.reactionVector r s
      = N.logMonomialRatio x y (N.targetIdx r) - N.logMonomialRatio x y (N.sourceIdx r) := by
    intro r
    rw [logMonomialRatio_eq N hx hy, logMonomialRatio_eq N hx hy, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [reactionVector_apply]
    simp only [targetIdx, sourceIdx, hμ]
    ring
  constructor
  · intro h r
    have h0 : ∑ s, μ s * N.reactionVector r s = 0 :=
      (mem_orthSum.mp h) (N.reactionVector r) (N.reactionVector_mem_stoichSubspace r)
    rw [hkey r] at h0
    exact sub_eq_zero.mp h0
  · intro h
    rw [stoichSubspace]
    refine mem_orthSum_span ?_
    rintro _ ⟨r, rfl⟩
    rw [hkey r, h r, sub_self]

/-- **Single-species reduction of the log-ratio gap.**  If two complexes agree away from `s`,
their log-monomial ratios differ by exactly `(c s - d s) * (log (x s) - log (y s))`.

This is the linearity of `Φ` in the complex vector, specialised to a Shinar--Feinberg pair. -/
theorem logMonomialRatio_sub_of_differOnlyAt (N : Network S) {x y : Concentration S}
    (hx : x.Positive) (hy : y.Positive) {c d : N.ComplexIdx} {s : S}
    (hcd : ∀ t, t ≠ s → c.val t = d.val t) :
    N.logMonomialRatio x y c - N.logMonomialRatio x y d
      = ((c.val s : ℝ) - (d.val s : ℝ)) * (Real.log (x s) - Real.log (y s)) := by
  rw [logMonomialRatio_eq N hx hy, logMonomialRatio_eq N hx hy, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single s]
  · ring
  · intro t _ hts
    rw [hcd t hts]
    ring
  · intro h
    exact absurd (Finset.mem_univ s) h

/-- **The Shinar--Feinberg pair criterion.**  For two complexes differing in exactly one
species `s`, equality of their log-monomial ratios between two positive states is
*equivalent* to those states agreeing at `s`.

This is the precise sense in which the cross-class scalar coupling lemma and absolute
concentration robustness at `s` are the same statement: neither is weaker than the other. -/
theorem logMonomialRatio_eq_iff_of_differOnlyAt (N : Network S) {x y : Concentration S}
    (hx : x.Positive) (hy : y.Positive) {c d : N.ComplexIdx} {s : S}
    (hcd : ∀ t, t ≠ s → c.val t = d.val t) (hne : (c.val s : ℝ) ≠ (d.val s : ℝ)) :
    N.logMonomialRatio x y c = N.logMonomialRatio x y d ↔ x s = y s := by
  have hgap := N.logMonomialRatio_sub_of_differOnlyAt hx hy hcd
  constructor
  · intro h
    have h0 : ((c.val s : ℝ) - (d.val s : ℝ)) * (Real.log (x s) - Real.log (y s)) = 0 := by
      rw [← hgap, h, sub_self]
    have hlog : Real.log (x s) = Real.log (y s) := by
      have := (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hne)
      linarith [this]
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr (hx s)) (Set.mem_Ioi.mpr (hy s)) hlog
  · intro h
    have : Real.log (x s) - Real.log (y s) = 0 := by rw [h, sub_self]
    have : N.logMonomialRatio x y c - N.logMonomialRatio x y d = 0 := by
      rw [hgap, this, mul_zero]
    linarith [this]

end Network

end CRNT
