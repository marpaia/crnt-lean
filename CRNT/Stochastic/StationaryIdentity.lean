import CRNT.Design.Antithetic

/-!
# Stationary laws of the master equation annihilate observables

A law `π` on counts is stationary for the chemical master equation when the probability flux into
every count equals the flux out of it (`IsCMEStationary`, `πQ = 0`). Arguments about stationary
means (for example the antithetic-feedback setpoint of Briat–Gupta–Khammash 2016) use the
consequence `∑_n π(n) (A f)(n) = 0` for an observable `f`, where
`A f (n) = ∑_r λ_r(n) (f(n + v_r) − f(n))` is the backward generator. For unbounded `f` this needs
moment bounds. This module proves it under the summability of `π λ_r f` and `π λ_r (f ∘ fire_r)`
for every reaction, and derives the stochastic antithetic setpoint from stationarity and first
moments instead of assuming the identity.

* `predCount`, `cmeInflow`, `IsCMEStationary`: the master equation in global-balance form.
* `tsum_mul_rate_fire_eq`: reindexing the flux sum along the jumps.
* `tsum_mul_observableGenerator_eq_zero`: the identity.
* `tsum_mul_observableGenerator_linear_eq_zero`: the identity for linear observables from
  `Summable (π λ_r)` and `Summable (π λ_r f)`.
* `stochastic_maxRPA_mean_of_cmeStationary`: the maxRPA / antithetic stationary mean from
  stationarity and moment bounds.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The count from which firing `r` lands on `m` (meaningful when `m` contains the target). -/
def predCount (N : Network S) (m : S → ℕ) (r : N.R) : S → ℕ :=
  fun s => m s - (N.reaction r).target s + (N.reaction r).source s

/-- The probability flux into `m` along reaction `r`. -/
noncomputable def cmeInflow (N : Network S) (κ : N.RateConstants) (π : (S → ℕ) → ℝ)
    (m : S → ℕ) (r : N.R) : ℝ := by
  classical
  exact if ∀ s, (N.reaction r).target s ≤ m s then
    π (N.predCount m r) * N.stochasticMassActionRate κ (N.predCount m r) r else 0

/-- **Stationarity for the chemical master equation** (global balance at every count). -/
def IsCMEStationary (N : Network S) (κ : N.RateConstants) (π : (S → ℕ) → ℝ) : Prop :=
  ∀ m, ∑ r, N.cmeInflow κ π m r = π m * ∑ r, N.stochasticMassActionRate κ m r

theorem fireCount_of_enabled (N : Network S) {n : S → ℕ} {r : N.R} (h : N.Enabled n r) :
    N.fireCount n r = fun s => n s - (N.reaction r).source s + (N.reaction r).target s := by
  unfold fireCount; simp only [h, ↓reduceDIte]

theorem target_le_fireCount (N : Network S) {n : S → ℕ} {r : N.R} (h : N.Enabled n r) (s : S) :
    (N.reaction r).target s ≤ N.fireCount n r s := by
  rw [fireCount_of_enabled N h]; dsimp only; omega

theorem predCount_fireCount (N : Network S) {n : S → ℕ} {r : N.R} (h : N.Enabled n r) :
    N.predCount (N.fireCount n r) r = n := by
  funext s
  simp only [predCount, fireCount_of_enabled N h]
  have := h s
  omega

theorem enabled_predCount (N : Network S) (m : S → ℕ) (r : N.R) :
    N.Enabled (N.predCount m r) r := fun s => by simp only [predCount]; omega

theorem fireCount_predCount (N : Network S) {m : S → ℕ} {r : N.R}
    (h : ∀ s, (N.reaction r).target s ≤ m s) : N.fireCount (N.predCount m r) r = m := by
  funext s
  rw [fireCount_of_enabled N (N.enabled_predCount m r)]
  simp only [predCount]
  have := h s
  omega

/-- **Reindexing along the jumps.** `∑_n π(n) λ_r(n) f(fire_r n) = ∑_m f(m) · inflow_r(m)`, and
summability transfers. -/
theorem tsum_mul_rate_fire_eq (N : Network S) (κ : N.RateConstants) (π : (S → ℕ) → ℝ)
    (f : (S → ℕ) → ℝ) (r : N.R)
    (hs : Summable fun n => π n * N.stochasticMassActionRate κ n r * f (N.fireCount n r)) :
    Summable (fun m => f m * N.cmeInflow κ π m r) ∧
      ∑' n, π n * N.stochasticMassActionRate κ n r * f (N.fireCount n r) =
        ∑' m, f m * N.cmeInflow κ π m r := by
  classical
  set g : (S → ℕ) → ℝ := fun n => π n * N.stochasticMassActionRate κ n r * f (N.fireCount n r)
    with hg
  set h : (S → ℕ) → ℝ := fun m => f m * N.cmeInflow κ π m r with hh
  let e : {n : S → ℕ // N.Enabled n r} → (S → ℕ) := fun n => N.fireCount n.1 r
  have he : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    rw [← N.predCount_fireCount a.2, ← N.predCount_fireCount b.2]
    exact congrArg (fun m => N.predCount m r) hab
  have hcomp : ∀ c, h (e c) = g c.1 := by
    intro c
    have ht : ∀ s, (N.reaction r).target s ≤ N.fireCount c.1 r s := N.target_le_fireCount c.2
    simp only [hh, hg, e, cmeInflow, ht, implies_true, ↓reduceIte, N.predCount_fireCount c.2]
    ring
  have hzero : ∀ m ∉ Set.range e, h m = 0 := by
    intro m hm
    simp only [hh, cmeInflow]
    split_ifs with ht
    · exact absurd ⟨⟨_, N.enabled_predCount m r⟩, N.fireCount_predCount ht⟩ hm
    · ring
  have hsupp_g : Function.support g ⊆ {n | N.Enabled n r} := by
    intro n hn
    by_contra hen
    apply hn
    simp only [hg, N.stochasticMassActionRate_eq_zero_of_not_enabled κ n r hen, mul_zero, zero_mul]
  have hsub : Summable (g ∘ (Subtype.val : {n : S → ℕ // N.Enabled n r} → S → ℕ)) :=
    hs.subtype _
  have hhe : (h ∘ e) = g ∘ Subtype.val := funext hcomp
  have hsh : Summable h := (he.summable_iff hzero).mp (hhe ▸ hsub)
  refine ⟨hsh, ?_⟩
  have h1 : ∑' n, g n = ∑' c : {n : S → ℕ // N.Enabled n r}, g c.1 :=
    (tsum_subtype_eq_of_support_subset hsupp_g).symm
  have h2 : ∑' c : {n : S → ℕ // N.Enabled n r}, h (e c) = ∑' m, h m :=
    he.tsum_eq (fun m hm => by
      by_contra hr
      exact hm (hzero m hr))
  rw [h1, ← h2]
  exact tsum_congr fun c => (hcomp c).symm

/-- **The stationarity identity.** For a stationary law `π` and an observable `f` with
`π λ_r f` and `π λ_r (f ∘ fire_r)` summable for every reaction, `∑_n π(n) (A f)(n) = 0`. -/
theorem tsum_mul_observableGenerator_eq_zero (N : Network S) (κ : N.RateConstants)
    {π : (S → ℕ) → ℝ} (hst : N.IsCMEStationary κ π) (f : (S → ℕ) → ℝ)
    (hs1 : ∀ r, Summable fun n => π n * N.stochasticMassActionRate κ n r * f n)
    (hs2 : ∀ r, Summable fun n => π n * N.stochasticMassActionRate κ n r * f (N.fireCount n r)) :
    ∑' n, π n * N.observableGenerator κ f n = 0 := by
  have hexp : ∀ n, π n * N.observableGenerator κ f n =
      ∑ r, (π n * N.stochasticMassActionRate κ n r * f (N.fireCount n r) -
        π n * N.stochasticMassActionRate κ n r * f n) := by
    intro n
    rw [observableGenerator, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  simp_rw [hexp]
  rw [Summable.tsum_finsetSum fun r _ => (hs2 r).sub (hs1 r)]
  simp_rw [fun r => (hs2 r).tsum_sub (hs1 r)]
  rw [Finset.sum_sub_distrib]
  have hre := fun r => N.tsum_mul_rate_fire_eq κ π f r (hs2 r)
  simp_rw [fun r => (hre r).2]
  rw [← Summable.tsum_finsetSum fun r _ => (hre r).1,
    ← Summable.tsum_finsetSum fun r _ => hs1 r, sub_eq_zero]
  refine tsum_congr fun m => ?_
  rw [← Finset.mul_sum, hst m, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => by ring

/-- **Linear observables.** For `f = ⟨w, n⟩`, summability of `π λ_r` and `π λ_r f` suffices. -/
theorem tsum_mul_observableGenerator_linear_eq_zero (N : Network S) (κ : N.RateConstants)
    {π : (S → ℕ) → ℝ} (hst : N.IsCMEStationary κ π) (w : S → ℝ)
    (hs0 : ∀ r, Summable fun n => π n * N.stochasticMassActionRate κ n r)
    (hs1 : ∀ r, Summable fun n => π n * N.stochasticMassActionRate κ n r * linearObservable w n) :
    ∑' n, π n * N.observableGenerator κ (linearObservable w) n = 0 := by
  refine N.tsum_mul_observableGenerator_eq_zero κ hst _ hs1 fun r => ?_
  have hfun : (fun n => π n * N.stochasticMassActionRate κ n r *
      linearObservable w (N.fireCount n r)) = fun n =>
      π n * N.stochasticMassActionRate κ n r * linearObservable w n +
        (∑ s, w s * N.reactionVector r s) * (π n * N.stochasticMassActionRate κ n r) := by
    funext n
    by_cases hen : N.Enabled n r
    · have := linearObservable_fireCount_sub w n r hen
      rw [show linearObservable w (N.fireCount n r) =
        linearObservable w n + ∑ s, w s * N.reactionVector r s by linarith]
      ring
    · rw [N.stochasticMassActionRate_eq_zero_of_not_enabled κ n r hen]
      ring
  rw [hfun]
  exact (hs1 r).add ((hs0 r).mul_left _)

/-- **Stochastic maxRPA setpoint from stationarity and first moments.** Under the hypotheses of
`stochastic_maxRPA_mean`, with its stationarity identity replaced by: `π` is stationary for the
master equation, and `π λ_r` and `π λ_r ⟨charge, n⟩` are summable for every reaction. -/
theorem stochastic_maxRPA_mean_of_cmeStationary (N : Network S) (κ : N.RateConstants)
    {rRef rSense : N.R} {out : S} (C : N.MaxRPAChargeCertificate rRef rSense)
    (hgap : N.UnitOutputGap rRef rSense out) (href : ∀ s, (N.reaction rRef).source s = 0)
    (π : (S → ℕ) → ℝ) (hsum : Summable π) (hmass : ∑' n, π n = 1)
    (hsumOut : Summable (fun n => π n * (n out : ℝ))) (hst : N.IsCMEStationary κ π)
    (hs0 : ∀ r, Summable fun n => π n * N.stochasticMassActionRate κ n r)
    (hs1 : ∀ r, Summable fun n =>
      π n * N.stochasticMassActionRate κ n r * linearObservable C.charge n) :
    ∑' n, π n * (n out : ℝ) = C.gain * κ.k rRef / κ.k rSense :=
  N.stochastic_maxRPA_mean κ C hgap href π hsum hmass hsumOut
    (N.tsum_mul_observableGenerator_linear_eq_zero κ hst C.charge hs0 hs1)

end Network

end CRNT
