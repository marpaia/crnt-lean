import CRNT.Dynamics.Persistence
import CRNT.Dynamics.Nagumo
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Monotone

/-!
# Forward-invariance of a siphon face for the mass-action flow

The dynamical companion to `CRNT.Dynamics.Persistence`. That module establishes the
*algebraic* tangency of the mass-action field to a siphon face but explicitly disclaims the
*dynamical* step — turning tangency into genuine forward-invariance — as out of reach
without a Nagumo / subtangential viability theorem. This module supplies exactly that step
for the face, on the same dissipative-coordinate footing the proven orthant-invariance
theorem `Network.massAction_forwardInvariant_nonneg` uses.

* `nagumo_halfspace_scalar_upper`: the *upper* dissipative scalar Nagumo lemma, the mirror
  of `nagumo_halfspace_scalar`. A differentiable `g` with `g 0 ≤ 0` and the one-sided
  inequality `g' ≤ L·g` wherever `g > 0` stays `≤ 0` on `[0, ∞)`. The proof is a
  first-crossing-from-above on `z = g·exp(-L·)`, which is nonincreasing where `g > 0`.
* `Network.faceSum`: the scalar face-distance functional `V(x) = ∑_{s∈P} x s`. On the
  nonnegative orthant `V x = 0` iff `x` vanishes on all of `P` (`faceSum_eq_zero_iff`),
  giving the membership rewrite `mem_siphonFace_iff`.
* `Network.siphonFace_forwardInvariant`: the key theorem. A nonnegative integral curve of
  the mass-action field starting on `SiphonFace P`, along which the face functional
  satisfies the one-sided dissipativity bound `V'(γ t) ≤ L·V(γ t)` (supplied disjunctively,
  mirroring `massAction_forwardInvariant_nonneg`'s `hLip`), stays on `SiphonFace P` for all
  forward time.
* `Network.faceSum_deriv_witness_eq_zero_on_siphonFace`: the tangency tie-in. On the face
  of a siphon, the sum over `P` of the field components — the natural derivative witness for
  `V` — is exactly zero, re-exporting `massActionVectorField_eq_zero_on_siphonFace`.

This delivers face forward-invariance, not persistence. Persistence is the
converse repelling estimate on critical siphons, which needs sign-restricted kernel / LP
feasibility (decidability of `IsCriticalSiphon`, absent in Mathlib v4.31) together with
ω-limit / Birkhoff-center theory. The dissipativity bound is taken here as a
hypothesis: making it unconditional needs a monomial-factoring estimate
`∑_{s∈P} f(x) s ≤ C·∑_{s∈P} x s` on a confining compact box, a separate analytic brick.
The non-circularity is structural: `V` is defined off the face and the scalar lemma only
activates where `V > 0`.

Depends on: `CRNT.Dynamics.Persistence`,
`CRNT.Dynamics.Nagumo`, `Mathlib.Analysis.Calculus.Deriv.MeanValue`,
`Mathlib.Analysis.SpecialFunctions.ExpDeriv`, `Mathlib.Topology.Order.Monotone`.
-/

namespace CRNT

open scoped BigOperators

/-- **Upper scalar dissipative Nagumo invariance for a closed halfspace.** If a
differentiable `g` has `g 0 ≤ 0` and satisfies the one-sided inequality `g' ≤ L·g` wherever
`g > 0`, then `g` stays `≤ 0` on `[0, ∞)`.

This is the reflection of `nagumo_halfspace_scalar` (which keeps a function `≥ 0`): apply
that lemma to `-g`. The dissipativity hypothesis transports because `-g < 0 ↔ g > 0` and
`-L·(-g) ≤ (-g)' ↔ g' ≤ L·g`. -/
theorem nagumo_halfspace_scalar_upper {g : ℝ → ℝ} {L : ℝ}
    (hd : ∀ t, HasDerivAt g (deriv g t) t)
    (hin : ∀ t, 0 < g t → deriv g t ≤ L * g t) (h0 : g 0 ≤ 0) :
    ∀ t, 0 ≤ t → g t ≤ 0 := by
  -- reflect to the lower lemma via `h = -g`
  set h : ℝ → ℝ := fun t => -g t with hh
  have hhd : ∀ t, HasDerivAt h (deriv h t) t := by
    intro t
    have : HasDerivAt h (-(deriv g t)) t := (hd t).neg
    have hderiv : deriv h t = -(deriv g t) := this.deriv
    rw [hderiv]; exact this
  have hhderivval : ∀ t, deriv h t = -(deriv g t) := fun t => ((hd t).neg).deriv
  have hhin : ∀ t, h t < 0 → -(-L) * h t ≤ deriv h t := by
    intro t ht
    have hgpos : 0 < g t := by
      have : -g t < 0 := ht
      linarith
    rw [hhderivval t, hh]
    have := hin t hgpos
    simp only
    linarith
  have hh0 : 0 ≤ h 0 := by rw [hh]; simp only; linarith
  intro t ht
  have := nagumo_halfspace_scalar hhd hhin hh0 t ht
  rw [hh] at this
  simp only at this
  linarith

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The **face-distance functional** of a species set `P`: the sum of the `P`-coordinates of
a concentration, `V(x) = ∑_{s∈P} x s`. It vanishes exactly on the face `SiphonFace P`
(within the nonnegative orthant) and is the natural scalar Lyapunov candidate for proving
the face forward-invariant. -/
def faceSum (P : Finset S) (x : Concentration S) : ℝ := ∑ s ∈ P, x s

omit [DecidableEq S] [Fintype S] in
@[simp] theorem faceSum_apply (P : Finset S) (x : Concentration S) :
    faceSum P x = ∑ s ∈ P, x s := rfl

omit [DecidableEq S] [Fintype S] in
/-- The face functional is nonnegative on the nonnegative orthant. -/
theorem faceSum_nonneg {P : Finset S} {x : Concentration S} (hx : x.Nonnegative) :
    0 ≤ faceSum P x :=
  Finset.sum_nonneg fun s _ => hx s

omit [DecidableEq S] [Fintype S] in
/-- On the nonnegative orthant the face functional vanishes iff every `P`-coordinate
vanishes: `∑_{s∈P} x s = 0 ↔ ∀ s ∈ P, x s = 0`. -/
theorem faceSum_eq_zero_iff {P : Finset S} {x : Concentration S} (hx : x.Nonnegative) :
    faceSum P x = 0 ↔ ∀ s ∈ P, x s = 0 :=
  Finset.sum_eq_zero_iff_of_nonneg fun s _ => hx s

/-- Membership in a siphon face, expressed through the face functional: a concentration lies
on `SiphonFace P` iff it is nonnegative and its face functional vanishes. -/
theorem mem_siphonFace_iff (N : Network S) {P : Finset S} {x : Concentration S} :
    x ∈ N.SiphonFace P ↔ x.Nonnegative ∧ faceSum P x = 0 := by
  unfold SiphonFace
  rw [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hnn, hz⟩
    exact ⟨hnn, (faceSum_eq_zero_iff hnn).mpr hz⟩
  · rintro ⟨hnn, hV⟩
    exact ⟨hnn, (faceSum_eq_zero_iff hnn).mp hV⟩

/-- **Forward-invariance of a siphon face.** A nonnegative integral curve `γ` of the
mass-action field that starts on `SiphonFace P` and along which the face functional
`V = faceSum P` satisfies the one-sided dissipativity bound `V'(γ t) ≤ L·V(γ t)` stays on
`SiphonFace P` for all forward time: every `P`-coordinate remains exactly zero.

The dissipativity hypothesis `hdiss` is phrased disjunctively — at each forward time either
the inward inequality holds or `V` is already `≤ 0` — exactly as the proven orthant-invariance
theorem `massAction_forwardInvariant_nonneg` phrases its `hLip`. The functional is defined
*off* the face and the scalar lemma activates only where `V > 0`, so this is non-circular:
the dissipativity bound is the genuine residual structural certificate, while on the face
itself the field-sum over `P` vanishes unconditionally
(`faceSum_deriv_witness_eq_zero_on_siphonFace`). -/
theorem siphonFace_forwardInvariant_forward (N : Network S) (κ : RateConstants N)
    {P : Finset S} {γ : ℝ → Concentration S} {L : ℝ}
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hnn : ∀ t, 0 ≤ t → (γ t).Nonnegative)
    (hdiss : ∀ t, 0 ≤ t →
      deriv (fun u => faceSum P (γ u)) t ≤ L * faceSum P (γ t) ∨ faceSum P (γ t) ≤ 0)
    (h0 : γ 0 ∈ N.SiphonFace P) :
    ∀ t, 0 ≤ t → γ t ∈ N.SiphonFace P := by
  -- the scalar face functional along the curve
  set g : ℝ → ℝ := fun u => faceSum P (γ u) with hg
  -- per-coordinate derivatives of the Pi-valued curve
  have hcoord : ∀ t, 0 ≤ t → ∀ s,
      HasDerivAt (fun u => γ u s) (N.massActionVectorField κ (γ t) s) t :=
    fun t ht s => (hasDerivAt_pi.mp (hderiv t ht)) s
  -- `g` is differentiable with derivative the sum of the coordinate derivatives
  have hgderiv : ∀ t, 0 ≤ t →
      HasDerivAt g (∑ s ∈ P, N.massActionVectorField κ (γ t) s) t := by
    intro t ht
    have hsum := HasDerivAt.sum (u := P) (A := fun s => fun u => γ u s)
      (fun s (_ : s ∈ P) => hcoord t ht s)
    have hfun : (∑ s ∈ P, fun u => γ u s) = g := by
      funext u; simp [hg, faceSum]
    rw [hfun] at hsum
    exact hsum
  have hgderivval : ∀ t, 0 ≤ t →
      deriv g t = ∑ s ∈ P, N.massActionVectorField κ (γ t) s :=
    fun t ht => (hgderiv t ht).deriv
  have hgd : ∀ t, 0 ≤ t → HasDerivAt g (deriv g t) t := by
    intro t ht; rw [hgderivval t ht]; exact hgderiv t ht
  -- start: `g 0 = 0`
  have hg0 : g 0 = 0 := ((mem_siphonFace_iff N).mp h0).2
  -- the upper Nagumo lemma needs the dissipativity bound on the whole line where `g > 0`;
  -- we run it on the forward-shifted function and use that derivatives match for `t ≥ 0`.
  -- Instead, apply the scalar lemma directly: it only consumes hypotheses at points it
  -- actually visits in `[0, T]`, all of which are `≥ 0`.  We package `hdiss` for `t ≥ 0`.
  -- To feed the lemma (which quantifies over all `t`), define the inward inequality only as
  -- needed via a curve that is honest on `[0,∞)`; the lemma's contradiction lives in
  -- `[0, T] ⊆ [0, ∞)`, so the all-`t` form is established from the forward form by the
  -- argument below.
  -- We prove `g t ≤ 0` for `t ≥ 0` directly, mirroring the lower lemma's crossing argument
  -- on `z = g · exp(-L·)`, using `hdiss` only at forward times.
  have hgle : ∀ t, 0 ≤ t → g t ≤ 0 := by
    have hcont : ContinuousOn g (Set.Ici 0) := by
      intro t ht
      exact (hgd t ht).continuousAt.continuousWithinAt
    intro T hT
    by_contra hgT
    rw [not_le] at hgT
    -- the closed, nonempty, bounded-above set of "good" times in `[0, T]` where `g ≤ 0`
    have hcontIcc : ContinuousOn g (Set.Icc 0 T) :=
      hcont.mono (fun _ ht => Set.mem_Ici.mpr ht.1)
    set A' : Set (Set.Icc 0 T) := {t | g t ≤ 0} with hA'
    have hA'closed : IsClosed A' := by
      change IsClosed ((fun t : Set.Icc 0 T => g t) ⁻¹' Set.Iic 0)
      exact isClosed_Iic.preimage hcontIcc.domRestrict
    have hIccCompact : IsCompact (Set.univ : Set (Set.Icc 0 T)) := by
      letI : CompactSpace (Set.Icc 0 T) :=
        (isCompact_iff_compactSpace).mp (isCompact_Icc : IsCompact (Set.Icc 0 T))
      exact isCompact_univ
    have hA'compact : IsCompact A' :=
      hIccCompact.of_isClosed_subset hA'closed (Set.subset_univ _)
    set A : Set ℝ := (fun t : Set.Icc 0 T => (t : ℝ)) '' A' with hA
    have hAmem : ∀ t, t ∈ A ↔ t ∈ Set.Icc 0 T ∧ g t ≤ 0 := by
      intro t
      simp [hA, hA', and_comm, and_left_comm, and_assoc]
    have hAne : A.Nonempty := by
      refine ⟨0, (hAmem 0).mpr ?_⟩
      exact ⟨⟨le_rfl, hT⟩, hg0.le⟩
    have hAcompact : IsCompact A := by
      rw [hA]
      exact hA'compact.image continuous_subtype_val
    have hAcl : IsClosed A := hAcompact.isClosed
    have hAbdd : BddAbove A := ⟨T, fun t ht => (hAmem t).mp ht |>.1.2⟩
    set t₀ := sSup A with ht₀def
    have ht₀A : t₀ ∈ A := hAcl.csSup_mem hAne hAbdd
    have ht₀mem := (hAmem t₀).mp ht₀A
    have ht₀0 : 0 ≤ t₀ := ht₀mem.1.1
    have ht₀T : t₀ ≤ T := ht₀mem.1.2
    have hgt₀ : g t₀ ≤ 0 := ht₀mem.2
    have ht₀ltT : t₀ < T :=
      lt_of_le_of_ne ht₀T (fun h => absurd (h ▸ hgt₀) (not_le.mpr hgT))
    -- after `t₀` (up to `T`) the function is strictly positive
    have hpos_after : ∀ t, t₀ < t → t ≤ T → 0 < g t := by
      intro t htlt htle
      by_contra hle
      rw [not_lt] at hle
      have htm : t ∈ A := (hAmem t).mpr
        ⟨⟨le_trans ht₀0 htlt.le, htle⟩, hle⟩
      exact absurd (le_csSup hAbdd htm) (not_le.mpr htlt)
    -- `g t₀ = 0` by continuity
    have hgt₀eq : g t₀ = 0 := by
      refine le_antisymm hgt₀ ?_
      have htend : Filter.Tendsto g (nhdsWithin t₀ (Set.Ioi t₀)) (nhds (g t₀)) :=
        (hcont.continuousWithinAt (Set.mem_Ici.mpr ht₀0)).tendsto.mono_left
          (nhdsWithin_mono _ (fun t ht => Set.mem_Ici.mpr (le_trans ht₀0 ht.le)))
      refine ge_of_tendsto htend ?_
      have hlt : ∀ᶠ t in nhdsWithin t₀ (Set.Ioi t₀), t < T :=
        eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds ht₀ltT)
      have hself : ∀ᶠ t in nhdsWithin t₀ (Set.Ioi t₀), t₀ < t :=
        eventually_mem_nhdsWithin.mono fun t ht => ht
      filter_upwards [hlt, hself] with t htT ht₀t
      exact (hpos_after t ht₀t htT.le).le
    -- `z = g · exp(-L·)` is nonincreasing on `[t₀, T]`
    set z : ℝ → ℝ := fun t => g t * Real.exp (-L * t) with hz
    have hzd : ∀ t, 0 ≤ t →
        HasDerivAt z ((deriv g t + (-L) * g t) * Real.exp (-L * t)) t := by
      intro t ht
      have he : HasDerivAt (fun s => Real.exp (-L * s)) (Real.exp (-L * t) * (-L)) t := by
        simpa using (((hasDerivAt_id t).const_mul (-L))).exp
      have hm := (hgd t ht).mul he
      have hval : deriv g t * Real.exp (-L * t) + g t * (Real.exp (-L * t) * (-L))
          = (deriv g t + (-L) * g t) * Real.exp (-L * t) := by ring
      rw [hz, ← hval]; exact hm
    have hzcont : ContinuousOn z (Set.Icc t₀ T) := by
      have hgcont : ContinuousOn g (Set.Icc t₀ T) :=
        hcont.mono (fun _ ht => Set.mem_Ici.mpr (le_trans ht₀0 ht.1))
      have hecont : ContinuousOn (fun t : ℝ => Real.exp (-L * t)) (Set.Icc t₀ T) := by
        fun_prop
      rw [hz]
      exact hgcont.mul hecont
    have hanti : AntitoneOn z (Set.Icc t₀ T) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc t₀ T) hzcont
        (fun t ht => by
          rw [interior_Icc, Set.mem_Ioo] at ht
          have htge : 0 ≤ t := le_trans ht₀0 ht.1.le
          exact (hzd t htge).differentiableAt.differentiableWithinAt)
        (fun t ht => ?_)
      rw [interior_Icc, Set.mem_Ioo] at ht
      have htge : 0 ≤ t := le_trans ht₀0 ht.1.le
      rw [(hzd t htge).deriv]
      have hgt : 0 < g t := hpos_after t ht.1 ht.2.le
      -- activate the dissipativity disjunct: `g t > 0` rules out `g t ≤ 0`
      have hbound : deriv g t ≤ L * g t := by
        rcases hdiss t htge with hb | hc
        · exact hb
        · exact absurd hc (not_le.mpr hgt)
      have : deriv g t + (-L) * g t ≤ 0 := by linarith
      exact mul_nonpos_of_nonpos_of_nonneg this (Real.exp_pos _).le
    have hz01 : z T ≤ z t₀ := hanti ⟨le_refl t₀, ht₀T⟩ ⟨ht₀T, le_refl T⟩ ht₀T
    have hzt₀ : z t₀ = 0 := by rw [hz]; simp [hgt₀eq]
    have hzT : 0 < z T := mul_pos hgT (Real.exp_pos _)
    rw [hzt₀] at hz01
    exact absurd (lt_of_lt_of_le hzT hz01) (lt_irrefl 0)
  -- combine: `g t = 0` (squeezing `≤ 0` against `≥ 0`), hence membership in the face
  intro t ht
  have hge : 0 ≤ g t := faceSum_nonneg (hnn t ht)
  have hgeq : faceSum P (γ t) = 0 := le_antisymm (hgle t ht) hge
  exact (mem_siphonFace_iff N).mpr ⟨hnn t ht, hgeq⟩

/-- Siphon-face invariance for a solution defined at every real time. The forward-time form
`siphonFace_forwardInvariant_forward` only needs the differential equation for `t ≥ 0`. -/
theorem siphonFace_forwardInvariant (N : Network S) (κ : RateConstants N)
    {P : Finset S} {γ : ℝ → Concentration S} {L : ℝ}
    (hderiv : ∀ t, HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hnn : ∀ t, 0 ≤ t → (γ t).Nonnegative)
    (hdiss : ∀ t, 0 ≤ t →
      deriv (fun u => faceSum P (γ u)) t ≤ L * faceSum P (γ t) ∨ faceSum P (γ t) ≤ 0)
    (h0 : γ 0 ∈ N.SiphonFace P) :
    ∀ t, 0 ≤ t → γ t ∈ N.SiphonFace P :=
  N.siphonFace_forwardInvariant_forward κ (fun t _ => hderiv t) hnn hdiss h0

/-- **The derivative witness of the face functional vanishes on a siphon face.** On the
face of a siphon `P`, the sum over `P` of the mass-action field components — the natural
witness for the derivative of `faceSum P` along an integral curve — is exactly zero. This
re-exports `massActionVectorField_eq_zero_on_siphonFace` and shows that the dissipativity
hypothesis of `siphonFace_forwardInvariant` is vacuous *on the face itself*: the residual
content lives strictly off the face, where `faceSum P > 0`. -/
theorem faceSum_deriv_witness_eq_zero_on_siphonFace (N : Network S) (κ : RateConstants N)
    {P : Finset S} (hP : N.IsSiphon P) {x : Concentration S} (hx : x ∈ N.SiphonFace P) :
    ∑ s ∈ P, N.massActionVectorField κ x s = 0 :=
  Finset.sum_eq_zero fun _s hsP =>
    massActionVectorField_eq_zero_on_siphonFace N κ hP hx hsP

end Network

end CRNT
