import CRNT.Dynamics.PersistenceTheorem

/-!
# Unconditional siphon-face invariance for confined orbits

The companion that discharges the dissipativity hypothesis `hdiss` of
`Network.siphonFace_forwardInvariant`. That theorem keeps an integral curve on the siphon
face `SiphonFace P` provided the face functional `V = faceSum P` obeys the one-sided bound
`V'(γ t) ≤ L·V(γ t)`, but takes that bound as an input. This module proves the bound from
the mass-action structure of a siphon and feeds it back, landing **unconditional** face
forward-invariance for orbits confined to a box.

The analytic brick is the *upper* monomial-factoring estimate `faceSum_field_le`: on the
nonnegative part of the box `[0,B]^S`,

```
∑_{s∈P} (massActionVectorField κ x) s ≤ C · ∑_{s∈P} x s
```

for a uniform `C ≥ 0` depending only on the box and rate constants. The mechanism is the
mirror of `exists_field_lower_bound`. Write the face-sum of the field as
`∑_r rate_r(x) · w_r` with `w_r = ∑_{s∈P} reactionVector r s` the net `P`-mass produced by
reaction `r`. A reaction with `w_r ≤ 0` contributes a nonpositive term. A reaction with
`w_r > 0` *produces* net `P`-mass, hence produces some species of `P`; the siphon property
then forces it to *consume* some species `s'∈P`, so its source monomial carries a factor
`x_{s'} ≤ ∑_{s∈P} x s = faceSum P x`, the remaining factors being bounded by `(max 1 B)^deg`
on the box. Summing against the absolute-value cover `|w_r|` gives the linear face bound.

* `Network.exists_isProduct_of_faceVector_pos`: net `P`-production forces a `P`-producer.
* `Network.faceSum_field_le`: the upper face estimate above, with an explicit nonnegative
  constant.
* `Network.siphonFace_forwardInvariant_confined`: the unconditional theorem. A nonnegative
  integral curve of the mass-action field, starting on `SiphonFace P` of a siphon `P` and
  confined to a box `[0,B]^S` for all forward time, stays on `SiphonFace P` for all forward
  time. No dissipativity hypothesis: it is supplied internally by `faceSum_field_le`.

This delivers unconditional face invariance for *confined* orbits — the
confinement-to-a-box hypothesis `hbox` is the residual input, exactly the certificate that
`exists_field_lower_bound`-style box bounds need (and which `gac_of_genuine_persistence`
supplies via a compact absorbing set). Removing confinement, or upgrading invariance to the
repelling persistence estimate on *critical* siphons, still needs sign-restricted kernel /
LP feasibility (decidability of `IsCriticalSiphon`) and ω-limit theory, absent here.

Depends on: `CRNT.Dynamics.PersistenceTheorem`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **A reaction producing net `P`-mass produces some species of `P`.** If the net
`P`-coordinate change `∑_{s∈P} reactionVector r s` of reaction `r` is strictly positive, then
some species `s ∈ P` has a strictly positive net change, hence a nonzero target coefficient:
`r` is a producer of that species. -/
theorem exists_isProduct_of_faceVector_pos (N : Network S) {P : Finset S} {r : N.R}
    (hw : 0 < ∑ s ∈ P, N.reactionVector r s) : ∃ s ∈ P, N.IsProduct r s := by
  obtain ⟨s, hsP, hpos⟩ := Finset.exists_lt_of_sum_lt
    (s := P) (f := fun _ : S => (0 : ℝ)) (g := N.reactionVector r)
    (by rw [Finset.sum_const_zero]; exact hw)
  refine ⟨s, hsP, ?_⟩
  rw [reactionVector_apply] at hpos
  intro htz
  rw [htz] at hpos
  have hsrc : (0 : ℝ) ≤ ((N.reaction r).source s : ℝ) := Nat.cast_nonneg _
  push_cast at hpos
  linarith

/-- **Linear upper bound on the face-sum of the mass-action field over a box.** On the
nonnegative part of the box `[0,B]^S`, the sum over a siphon `P` of the field components
satisfies `∑_{s∈P} f(x) s ≤ C · ∑_{s∈P} x s` for a uniform `C ≥ 0`. Every reaction producing
net `P`-mass must, by the siphon property, consume a `P`-species, so its monomial carries a
factor of that consumed coordinate, bounded by `∑_{s∈P} x s`; on the box the cofactor is
bounded by `(max 1 B)^{deg}`. -/
theorem faceSum_field_le (N : Network S) (κ : N.RateConstants) {P : Finset S}
    (hP : N.IsSiphon P) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Concentration S, x.Nonnegative → (∀ s, x s ≤ B) →
      (∑ s ∈ P, N.massActionVectorField κ x s) ≤ C * faceSum P x := by
  have hBmnn : (0 : ℝ) ≤ max 1 B := le_trans zero_le_one (le_max_left _ _)
  have hBm1 : (1 : ℝ) ≤ max 1 B := le_max_left _ _
  -- coefficient: rate-constant × box-cofactor bound × |net P-production|, manifestly ≥ 0
  refine ⟨∑ r : N.R,
      κ.k r * (max 1 B) ^ (∑ s'', (N.reaction r).source s'')
        * |∑ s ∈ P, N.reactionVector r s|, ?_, ?_⟩
  · exact Finset.sum_nonneg fun r _ =>
      mul_nonneg (mul_nonneg (κ.positive r).le (pow_nonneg hBmnn _)) (abs_nonneg _)
  · intro x hx hxB
    have hxle : ∀ s', x s' ≤ max 1 B := fun s' => le_trans (hxB s') (le_max_right 1 B)
    have hfacenn : 0 ≤ faceSum P x := faceSum_nonneg hx
    -- rewrite the face-sum of the field as a reaction-indexed sum against `w_r`
    have hswap : (∑ s ∈ P, N.massActionVectorField κ x s)
        = ∑ r : N.R, N.massActionRate κ r x * (∑ s ∈ P, N.reactionVector r s) := by
      simp only [massActionVectorField_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.mul_sum]
    rw [hswap, Finset.sum_mul]
    refine Finset.sum_le_sum fun r _ => ?_
    set w : ℝ := ∑ s ∈ P, N.reactionVector r s with hwdef
    by_cases hwsign : 0 < w
    · -- producing reaction: factor `x_{s'}` out of the monomial via a consumed `P`-species
      obtain ⟨sp, hspP, hprod⟩ := N.exists_isProduct_of_faceVector_pos hwsign
      obtain ⟨s', hs'P, hs'r⟩ := hP r ⟨sp, hspP, hprod⟩
      have hsrc1 : 1 ≤ (N.reaction r).source s' := by
        rcases Nat.eq_zero_or_pos ((N.reaction r).source s') with h0 | h
        · exact absurd h0 hs'r
        · exact h
      -- monomial = x_{s'} · cofactor
      have hmono_eq : (N.reaction r).source.massActionMonomial x
          = x s' * (x s' ^ ((N.reaction r).source s' - 1)
              * ∏ s'' ∈ Finset.univ.erase s', x s'' ^ (N.reaction r).source s'') := by
        have h1 : (N.reaction r).source.massActionMonomial x
            = x s' ^ (N.reaction r).source s'
              * ∏ s'' ∈ Finset.univ.erase s', x s'' ^ (N.reaction r).source s'' := by
          show (∏ s'', x s'' ^ (N.reaction r).source s'') = _
          exact (Finset.mul_prod_erase Finset.univ
            (fun s'' => x s'' ^ (N.reaction r).source s'') (Finset.mem_univ s')).symm
        rw [h1]
        have h2 : x s' ^ (N.reaction r).source s'
            = x s' * x s' ^ ((N.reaction r).source s' - 1) := by
          conv_lhs => rw [show (N.reaction r).source s'
            = ((N.reaction r).source s' - 1) + 1 from by omega]
          rw [pow_succ']
        rw [h2, mul_assoc]
      set Q := x s' ^ ((N.reaction r).source s' - 1)
        * ∏ s'' ∈ Finset.univ.erase s', x s'' ^ (N.reaction r).source s'' with hQ
      have hQnn : 0 ≤ Q :=
        mul_nonneg (pow_nonneg (hx s') _)
          (Finset.prod_nonneg fun s'' _ => pow_nonneg (hx s'') _)
      have hQle : Q ≤ (max 1 B) ^ (∑ s'', (N.reaction r).source s'') := by
        have h1 : x s' ^ ((N.reaction r).source s' - 1)
            ≤ (max 1 B) ^ ((N.reaction r).source s' - 1) :=
          pow_le_pow_left₀ (hx s') (hxle s') _
        have h2 : (∏ s'' ∈ Finset.univ.erase s', x s'' ^ (N.reaction r).source s'')
            ≤ ∏ s'' ∈ Finset.univ.erase s', (max 1 B) ^ (N.reaction r).source s'' :=
          Finset.prod_le_prod₀ (fun s'' _ => pow_nonneg (hx s'') _)
            (fun s'' _ => pow_le_pow_left₀ (hx s'') (hxle s'') _)
        calc Q ≤ (max 1 B) ^ ((N.reaction r).source s' - 1)
                  * ∏ s'' ∈ Finset.univ.erase s', (max 1 B) ^ (N.reaction r).source s'' :=
              mul_le_mul h1 h2 (Finset.prod_nonneg fun s'' _ => pow_nonneg (hx s'') _)
                (pow_nonneg hBmnn _)
          _ = (max 1 B) ^ ((N.reaction r).source s' - 1
                + ∑ s'' ∈ Finset.univ.erase s', (N.reaction r).source s'') := by
              rw [Finset.prod_pow_eq_pow_sum, ← pow_add]
          _ ≤ (max 1 B) ^ (∑ s'', (N.reaction r).source s'') := by
              refine pow_le_pow_right₀ hBm1 ?_
              have hsum_eq : (N.reaction r).source s'
                  + ∑ s'' ∈ Finset.univ.erase s', (N.reaction r).source s''
                  = ∑ s'', (N.reaction r).source s'' :=
                Finset.add_sum_erase Finset.univ
                  (fun s'' => (N.reaction r).source s'') (Finset.mem_univ s')
              omega
      -- `x_{s'} ≤ faceSum P x` since the face-sum has nonnegative summands
      have hxs'face : x s' ≤ faceSum P x :=
        Finset.single_le_sum (f := fun s => x s) (fun s _ => hx s) hs'P
      -- rate = κ · x_{s'} · Q
      have hrate_eq : N.massActionRate κ r x = κ.k r * (x s' * Q) := by
        show κ.k r * (N.reaction r).source.massActionMonomial x = κ.k r * (x s' * Q)
        rw [hmono_eq]
      -- bound: κ·x_{s'}·Q·w ≤ κ·(max1B)^deg·|w|·faceSum
      have habsw : w = |w| := (abs_of_pos hwsign).symm
      calc N.massActionRate κ r x * w
            = κ.k r * Q * x s' * w := by rw [hrate_eq]; ring
        _ ≤ κ.k r * (max 1 B) ^ (∑ s'', (N.reaction r).source s'') * (faceSum P x) * w := by
              apply mul_le_mul_of_nonneg_right _ hwsign.le
              apply mul_le_mul _ hxs'face (hx s')
                (mul_nonneg (κ.positive r).le (pow_nonneg hBmnn _))
              exact mul_le_mul_of_nonneg_left hQle (κ.positive r).le
        _ = κ.k r * (max 1 B) ^ (∑ s'', (N.reaction r).source s'') * |w| * faceSum P x := by
              rw [← habsw]; ring
    · -- non-producing reaction: `w ≤ 0`, rate ≥ 0, so the term is ≤ 0 ≤ RHS
      rw [not_lt] at hwsign
      have hterm_nonpos : N.massActionRate κ r x * w ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (N.massActionRate_nonneg κ r hx) hwsign
      have hrhs_nonneg : 0 ≤ κ.k r * (max 1 B) ^ (∑ s'', (N.reaction r).source s'')
          * |w| * faceSum P x :=
        mul_nonneg (mul_nonneg (mul_nonneg (κ.positive r).le (pow_nonneg hBmnn _))
          (abs_nonneg _)) hfacenn
      exact le_trans hterm_nonpos hrhs_nonneg

/-- **Unconditional forward-invariance of a siphon face for a confined orbit.** A nonnegative
mass-action integral curve `γ` starting on `SiphonFace P` of a siphon `P` and confined to the
box `[0,B]^S` for all forward time stays on `SiphonFace P` for all forward time.

This drops the dissipativity hypothesis of `siphonFace_forwardInvariant`: the one-sided bound
`V'(γ t) ≤ C·V(γ t)` is supplied internally by the monomial-factoring estimate
`faceSum_field_le`, since the derivative of `V = faceSum P` along the curve is the face-sum of
the field. -/
theorem siphonFace_forwardInvariant_confined_forward (N : Network S) (κ : N.RateConstants)
    {P : Finset S} (hP : N.IsSiphon P) {γ : ℝ → Concentration S} {B : ℝ}
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hnn : ∀ t, 0 ≤ t → (γ t).Nonnegative)
    (hbox : ∀ t, 0 ≤ t → ∀ s, γ t s ≤ B)
    (h0 : γ 0 ∈ N.SiphonFace P) :
    ∀ t, 0 ≤ t → γ t ∈ N.SiphonFace P := by
  obtain ⟨C, _hCnn, hC⟩ := N.faceSum_field_le κ hP B
  refine N.siphonFace_forwardInvariant_forward κ (L := C) hderiv hnn ?_ h0
  intro t ht
  left
  -- `deriv (fun u => faceSum P (γ u)) t = ∑ s ∈ P, f(γ t) s`, then apply `faceSum_field_le`
  have hcoord : ∀ s, HasDerivAt (fun u => γ u s) (N.massActionVectorField κ (γ t) s) t :=
    fun s => (hasDerivAt_pi.mp (hderiv t ht)) s
  have hgderiv : HasDerivAt (fun u => faceSum P (γ u))
      (∑ s ∈ P, N.massActionVectorField κ (γ t) s) t := by
    have hsum := HasDerivAt.sum (u := P) (A := fun s => fun u => γ u s)
      (fun s (_ : s ∈ P) => hcoord s)
    have hfun : (∑ s ∈ P, fun u => γ u s) = fun u => faceSum P (γ u) := by
      funext u; simp [faceSum]
    rw [hfun] at hsum
    exact hsum
  rw [hgderiv.deriv]
  exact hC (γ t) (hnn t ht) (hbox t ht)

/-- Confined siphon-face invariance for a solution defined at every real time. -/
theorem siphonFace_forwardInvariant_confined (N : Network S) (κ : N.RateConstants)
    {P : Finset S} (hP : N.IsSiphon P) {γ : ℝ → Concentration S} {B : ℝ}
    (hderiv : ∀ t, HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hnn : ∀ t, 0 ≤ t → (γ t).Nonnegative)
    (hbox : ∀ t, 0 ≤ t → ∀ s, γ t s ≤ B)
    (h0 : γ 0 ∈ N.SiphonFace P) :
    ∀ t, 0 ≤ t → γ t ∈ N.SiphonFace P :=
  N.siphonFace_forwardInvariant_confined_forward κ hP (fun t _ => hderiv t) hnn hbox h0

end Network

end CRNT
