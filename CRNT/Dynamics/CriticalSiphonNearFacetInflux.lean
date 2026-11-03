import CRNT.Dynamics.Siphon
import CRNT.Dynamics.Persistence

/-!
# Anderson–Shiu near-facet influx estimate (codimension-1 singleton critical siphon)

On the codimension-1 facet `SiphonFace {s*}` cut out by a single critical-siphon species `s*`,
the first-order repulsion of `CRNT.Dynamics.FacetRepulsion` vanishes: the mass-action field is
tangent to the face (`massActionVectorField_eq_zero_on_siphonFace`). Anderson & Shiu,
_The dynamics of weakly reversible population processes near facets_ (2010), close the
critical-siphon facet by a quantitative near-facet estimate on the influx component of the field.

This module proves the dischargeable form of that estimate for a singleton siphon `P = {s*}`.
The siphon condition forces every reaction that *produces* `s*` to also *consume* `s*`: with `s*`
the only species of `P`, a producing reaction must consume some `P`-species, hence `s*` itself.
Consequently every reaction contributing a *negative* `s*`-rate carries at least one factor of the
vanishing coordinate `x s*` in its source monomial. On a region where every concentration is
bounded above by `M`, factoring that coordinate out of each monomial bounds the whole `s*`-component
of the field below by `-(c · x s*)` for an explicit network constant `c ≥ 0`:

`-(c * x s*) ≤ N.massActionVectorField κ x s*`.

The distance from a nonnegative `x` to `SiphonFace {s*}` is governed by the vanishing coordinate
`x s*`, so this is a linear near-facet lower bound: the outflow through `s*` cannot exceed a
multiple of the distance to the face. Along a trajectory it reads `ẋ_{s*} ≥ -c · x_{s*}`, the
Grönwall differential inequality keeping `x_{s*}(t) ≥ x_{s*}(0) · exp(-c t) > 0` — the facet is
non-attracting. This is the Anderson & Shiu influx bound that closes the singleton critical-siphon
facet, supplying the quantitative subtangent estimate that `CRNT.Dynamics.FacetRepulsion` records
as missing.

Depends on: `CRNT.Dynamics.Siphon`,
`CRNT.Dynamics.Persistence`.
-/

open scoped BigOperators

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Monomial factor bound.** On a region bounded above by `B ≥ 1`, with every concentration
nonnegative, if a complex `y` carries a positive power of `s*` (`y s* ≠ 0`) then its monomial is
bounded by the vanishing coordinate times a power of `B`:
`y.massActionMonomial x ≤ x s* * B ^ (∑ s, y s - 1)`. One factor of `x s*` is split off; every
remaining factor `x t ≤ B` and `0 ≤ x t ≤ B`, so the residual product is at most `B` to the
residual total degree. -/
theorem massActionMonomial_le_coord_mul_pow {y : Complex S} {x : Concentration S}
    (hxnn : x.Nonnegative) {B : ℝ} (hB1 : (1 : ℝ) ≤ B) (hxB : ∀ s, x s ≤ B)
    {sstar : S} (hsrc : y sstar ≠ 0) :
    y.massActionMonomial x ≤ x sstar * B ^ ((∑ s, y s) - 1) := by
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  have hsrc1 : 1 ≤ y sstar := Nat.one_le_iff_ne_zero.mpr hsrc
  -- split the universe product at `s*`
  have hmem : sstar ∈ (Finset.univ : Finset S) := Finset.mem_univ _
  rw [Complex.massActionMonomial, ← Finset.prod_erase_mul _ _ hmem]
  -- `x s* ^ (y s*) = x s* * x s* ^ (y s* - 1) ≤ x s* * B ^ (y s* - 1)`
  have hsplit : x sstar ^ (y sstar) = x sstar * x sstar ^ (y sstar - 1) := by
    obtain ⟨n, hn⟩ : ∃ n, y sstar = n + 1 := ⟨y sstar - 1, by omega⟩
    rw [hn, Nat.add_sub_cancel, pow_succ]; ring
  -- residual product over erased universe bounded by `B ^ (sum over erased)`
  have hresid : ∏ s ∈ (Finset.univ.erase sstar), x s ^ (y s)
      ≤ ∏ s ∈ (Finset.univ.erase sstar), B ^ (y s) := by
    refine Finset.prod_le_prod₀ (fun s _ => pow_nonneg (hxnn s) _) (fun s _ => ?_)
    exact pow_le_pow_left₀ (hxnn s) (hxB s) _
  have hxstar0 : 0 ≤ x sstar ^ (y sstar) := pow_nonneg (hxnn sstar) _
  -- combine: bound the residual, then the s*-factor
  calc
    (∏ s ∈ (Finset.univ.erase sstar), x s ^ (y s)) * x sstar ^ (y sstar)
        ≤ (∏ s ∈ (Finset.univ.erase sstar), B ^ (y s)) * x sstar ^ (y sstar) :=
          mul_le_mul_of_nonneg_right hresid hxstar0
    _ = B ^ (∑ s ∈ (Finset.univ.erase sstar), y s) * x sstar ^ (y sstar) := by
          rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ B ^ (∑ s ∈ (Finset.univ.erase sstar), y s) * (x sstar * B ^ (y sstar - 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hB0 _)
          rw [hsplit]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hxnn sstar) (hxB sstar) _) (hxnn sstar)
    _ = x sstar * B ^ ((∑ s ∈ (Finset.univ.erase sstar), y s) + (y sstar - 1)) := by
          rw [pow_add]; ring
    _ = x sstar * B ^ ((∑ s, y s) - 1) := by
          congr 2
          rw [← Finset.sum_erase_add _ _ hmem]
          omega

/-- **Per-reaction near-facet influx bound (singleton siphon).** For the singleton siphon `{s*}`,
on a region where every concentration is bounded above by `M`, a single reaction's contribution to
the `s*`-component of the mass-action field is bounded below by `-(c_r · x s*)`, where the constant
`c_r = κ_r · (source_r s*) · B^(D-1)` with `B = max M 1` and `D` the source degree of `r`. A
reaction not consuming `s*` contributes nonnegatively (it cannot produce `s*` either, by the siphon
condition), so the bound is `0 ≤ rate`. A reaction consuming `s*` carries a factor of `x s*` in its
source monomial; factoring it out and bounding the rest by `B^(D-1)` gives the linear lower bound. -/
theorem massActionRate_mul_reactionVector_singleton_ge (N : Network S) (κ : N.RateConstants)
    {sstar : S} (hsiph : N.IsSiphon ({sstar} : Finset S)) (r : N.R)
    {x : Concentration S} (hxnn : x.Nonnegative) {M : ℝ} (hxM : ∀ s, x s ≤ M) :
    -(κ.k r * ((N.reaction r).source sstar : ℝ)
        * (max M 1) ^ ((∑ s, (N.reaction r).source s) - 1) * x sstar)
      ≤ N.massActionRate κ r x * N.reactionVector r sstar := by
  set B : ℝ := max M 1 with hB
  have hB1 : (1 : ℝ) ≤ B := le_max_right _ _
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  have hxB : ∀ s, x s ≤ B := fun s => le_trans (hxM s) (le_max_left _ _)
  by_cases hsrc : (N.reaction r).source sstar = 0
  · -- `r` does not consume `s*`; by the siphon condition it cannot produce `s*` either,
    -- so its reaction-vector entry at `s*` is `≥ 0` and the contribution is nonnegative.
    have hntz : (N.reaction r).target sstar = 0 := by
      by_contra htz
      have hprod : N.IsProduct r sstar := htz
      obtain ⟨s', hs'P, hs'r⟩ := hsiph r ⟨sstar, Finset.mem_singleton_self sstar, hprod⟩
      rw [Finset.mem_singleton] at hs'P
      subst hs'P
      exact hs'r hsrc
    have hvec : 0 ≤ N.reactionVector r sstar := by
      rw [reactionVector_apply, hsrc, hntz]; simp
    have hnn : 0 ≤ N.massActionRate κ r x * N.reactionVector r sstar :=
      mul_nonneg (N.massActionRate_nonneg κ r hxnn) hvec
    rw [hsrc]; push_cast; simpa using hnn
  · -- `r` consumes `s*`: the source monomial carries a factor `x s*`, bounded by `x s* · B^(D-1)`.
    have hmonle : (N.reaction r).source.massActionMonomial x
        ≤ x sstar * B ^ ((∑ s, (N.reaction r).source s) - 1) :=
      massActionMonomial_le_coord_mul_pow hxnn hB1 hxB hsrc
    -- the reaction-vector entry at `s*` is bounded below by `-(source s*)`
    have hvecge : -((N.reaction r).source sstar : ℝ) ≤ N.reactionVector r sstar := by
      rw [reactionVector_apply]
      have : (0 : ℝ) ≤ ((N.reaction r).target sstar : ℝ) := Nat.cast_nonneg _
      linarith
    -- the monomial and `x s*` are nonnegative
    have hmonnn : 0 ≤ (N.reaction r).source.massActionMonomial x :=
      Complex.massActionMonomial_nonneg hxnn _
    have hxstar : 0 ≤ x sstar := hxnn sstar
    have hpowB : 0 ≤ B ^ ((∑ s, (N.reaction r).source s) - 1) := pow_nonneg hB0 _
    have hsrcnn : 0 ≤ ((N.reaction r).source sstar : ℝ) := Nat.cast_nonneg _
    -- rate is `κ_r * monomial`
    have hrate_eq : N.massActionRate κ r x
        = κ.k r * (N.reaction r).source.massActionMonomial x := rfl
    -- assemble: `rate * vec ≥ rate * (-(source s*)) ≥ -(κ_r * (source s*) * B^(D-1) * x s*)`
    have hrate_nn : 0 ≤ N.massActionRate κ r x := N.massActionRate_nonneg κ r hxnn
    calc
      -(κ.k r * ((N.reaction r).source sstar : ℝ)
          * B ^ ((∑ s, (N.reaction r).source s) - 1) * x sstar)
          ≤ -(κ.k r * ((N.reaction r).source sstar : ℝ)
              * (N.reaction r).source.massActionMonomial x) := by
            rw [neg_le_neg_iff]
            -- `κ_r * (source s*) * monomial ≤ κ_r * (source s*) * (x s* * B^(D-1))`
            have hcoef : 0 ≤ κ.k r * ((N.reaction r).source sstar : ℝ) :=
              mul_nonneg (κ.positive r).le hsrcnn
            calc
              κ.k r * ((N.reaction r).source sstar : ℝ)
                  * (N.reaction r).source.massActionMonomial x
                  ≤ κ.k r * ((N.reaction r).source sstar : ℝ)
                      * (x sstar * B ^ ((∑ s, (N.reaction r).source s) - 1)) :=
                    mul_le_mul_of_nonneg_left hmonle hcoef
              _ = κ.k r * ((N.reaction r).source sstar : ℝ)
                      * B ^ ((∑ s, (N.reaction r).source s) - 1) * x sstar := by ring
      _ = N.massActionRate κ r x * (-((N.reaction r).source sstar : ℝ)) := by
            rw [hrate_eq]; ring
      _ ≤ N.massActionRate κ r x * N.reactionVector r sstar :=
            mul_le_mul_of_nonneg_left hvecge hrate_nn

/-- **Anderson–Shiu near-facet influx bound (singleton critical siphon).** Let `{s*}` be a siphon
of `N`. On a region where every concentration is bounded above by `M`, the `s*`-component of the
mass-action field is bounded below by `-(c · x s*)` for the explicit network constant
`c = ∑_r κ_r · (source_r s*) · (max M 1)^(D_r - 1)` (`D_r` the source degree of `r`):

`-(c * x s*) ≤ N.massActionVectorField κ x s*`.

Since the distance from a nonnegative `x` to the facet `SiphonFace {s*}` is governed by the
vanishing coordinate `x s*`, this is the codimension-1 linear influx lower bound of Anderson & Shiu,
_The dynamics of weakly reversible population processes near facets_: the outflow through `s*` is at
most a multiple of the distance to the face, so trajectories cannot be pinned to the facet. -/
theorem massActionVectorField_singleton_facet_ge (N : Network S) (κ : N.RateConstants)
    {sstar : S} (hsiph : N.IsSiphon ({sstar} : Finset S))
    {x : Concentration S} (hxnn : x.Nonnegative) {M : ℝ} (hxM : ∀ s, x s ≤ M) :
    -((∑ r : N.R, κ.k r * ((N.reaction r).source sstar : ℝ)
          * (max M 1) ^ ((∑ s, (N.reaction r).source s) - 1)) * x sstar)
      ≤ N.massActionVectorField κ x sstar := by
  rw [massActionVectorField_apply, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum (fun r _ => ?_)
  exact N.massActionRate_mul_reactionVector_singleton_ge κ hsiph r hxnn hxM

end Network

end CRNT
