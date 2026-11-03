import CRNT.Multistationarity.DecoratedSimplices

/-!
# Positively decorated simplices for polynomial systems (Bihan–Dickenstein–Giaroli)

A square polynomial system `∑_{a ∈ A} y^a c_a = 0` (`c_a ∈ ℝ^E`, `|E| = |S|`) is deformed by
`t^{h(a)}` on its coefficients. A **decorated cell** is a set `Δ ⊆ A` of `n + 1` affinely
independent exponents with `w ∈ ℤ^S`, `c₀ ∈ ℤ` such that `⟨w, a⟩ + h(a) = c₀` on `Δ` and `> c₀`
on `A \ Δ`, whose coefficient vectors span `ℝ^E` with a positive linear relation. Bihan,
Dickenstein and Giaroli (2020): `d` decorated cells with distinct normals give `d` distinct
nondegenerate positive solutions for small `t > 0`. This is the general form; the network case
with conservation laws is in `CRNT.Multistationarity.DecoratedSimplicesConservation`.

The proof is the toric deformation of `DecoratedSimplices` with the coefficient vectors `c_a` in
place of the combined reaction vectors.

* `Patchworking.sys`, `Patchworking.SysCell`.
* `Patchworking.solutions_of_cells`: the lower bound with nondegeneracy.
-/

namespace CRNT

namespace Patchworking

open Filter Topology Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S] {E : Type} [Fintype E]

/-- The deformed system `∑_{a ∈ A} t^{h(a)} x^a c_a` (with `t^{h} = exp (h log t)`). -/
noncomputable def sys (A : Finset (Complex S)) (c : Complex S → (E → ℝ)) (h : Complex S → ℤ)
    (t : ℝ) (x : S → ℝ) : E → ℝ :=
  ∑ a ∈ A, (Real.exp ((h a : ℝ) * Real.log t) * a.massActionMonomial x) • c a

/-- A positively decorated lower cell of the system `(A, c)` for the heights `h`. -/
structure SysCell (A : Finset (Complex S)) (c : Complex S → (E → ℝ)) (h : Complex S → ℤ) where
  Δ : Finset (Complex S)
  sub : Δ ⊆ A
  w : S → ℤ
  c₀ : ℤ
  card : Fintype.card Δ = Fintype.card (Option S)
  affInd : LinearIndependent ℝ (fun a : Δ => affineRow a.1)
  onCell : ∀ a ∈ Δ, pairing w a + h a = c₀
  offCell : ∀ a ∈ A, a ∉ Δ → c₀ < pairing w a + h a
  span : Submodule.span ℝ (Set.range fun a : Δ => c a.1) = ⊤
  lam : Δ → ℝ
  lam_pos : ∀ a, 0 < lam a
  lam_ker : ∑ a, lam a • c a.1 = 0

namespace SysCell

variable {A : Finset (Complex S)} {c : Complex S → (E → ℝ)} {h : Complex S → ℤ}

/-- The affine matrix with rows `(1, a)`, `a ∈ Δ`. -/
def rows (C : SysCell A c h) : Matrix C.Δ (Option S) ℝ := fun a => affineRow a.1

theorem rows_row (C : SysCell A c h) : C.rows.row = fun a : C.Δ => affineRow a.1 := rfl

theorem rows_mulVec (C : SysCell A c h) (ξ : Option S → ℝ) (a : C.Δ) :
    C.rows.mulVec ξ a = ξ none + ∑ s, (a.1 s : ℝ) * ξ (some s) := by
  simp only [rows, Matrix.mulVec, dotProduct, Fintype.sum_option, affineRow, Option.elim]
  ring

/-- The simplex system has a positive solution `y^a = ρ λ_a`. -/
theorem exists_simplex_solution (C : SysCell A c h) :
    ∃ y : Concentration S, y.Positive ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ a : C.Δ, a.1.massActionMonomial y = ρ * C.lam a := by
  obtain ⟨ξ, hξ⟩ := (rowsMatrix_solve C.rows C.card (by rw [rows_row]; exact C.affInd)).1
    (fun a => Real.log (C.lam a))
  refine ⟨fun s => Real.exp (ξ (some s)), fun s => Real.exp_pos _, Real.exp (-ξ none),
    Real.exp_pos _, fun a => ?_⟩
  have h1 := congrFun hξ a
  rw [rows_mulVec] at h1
  rw [monomial_eq_exp_sum_log _ (fun s => Real.exp_pos _)]
  simp only [Real.log_exp]
  have : ∑ s, (a.1 s : ℝ) * ξ (some s) = Real.log (C.lam a) + (-ξ none) := by linarith
  rw [this, Real.exp_add, Real.exp_log (C.lam_pos a)]
  ring

/-- The kernel of `β ↦ ∑ β_a c_a` is the line `ℝ λ`. -/
theorem ker_eq_smul_lam (C : SysCell A c h) (hE : Fintype.card E = Fintype.card S)
    (β : C.Δ → ℝ) (hβ : ∑ a, β a • c a.1 = 0) : ∃ θ : ℝ, ∀ a, β a = θ * C.lam a := by
  classical
  set L := Fintype.linearCombination ℝ (fun a : C.Δ => c a.1) with hL
  have hrange : LinearMap.range L = ⊤ := by rw [hL, Fintype.range_linearCombination, C.span]
  have hfin : Module.finrank ℝ (LinearMap.ker L) = 1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker L
    rw [hrange, finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      C.card, Fintype.card_option, hE] at h1
    omega
  have hlam : C.lam ∈ LinearMap.ker L := by
    show L C.lam = 0
    rw [hL, Fintype.linearCombination_apply]; exact C.lam_ker
  have hβk : β ∈ LinearMap.ker L := by
    show L β = 0
    rw [hL, Fintype.linearCombination_apply]; exact hβ
  have hne : (⟨C.lam, hlam⟩ : LinearMap.ker L) ≠ 0 := by
    intro h0
    have hc : Fintype.card C.Δ ≠ 0 := by rw [C.card]; simp
    obtain ⟨a⟩ : Nonempty C.Δ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hc)
    have := congrArg (fun v : LinearMap.ker L => (v : C.Δ → ℝ) a) h0
    simp at this
    exact (C.lam_pos a).ne' this
  obtain ⟨θ, hθ⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp hfin ⟨β, hβk⟩
  refine ⟨θ, fun a => ?_⟩
  have := congrArg (fun v : LinearMap.ker L => (v : C.Δ → ℝ) a) hθ
  simpa using this.symm

/-- The cell subsystem `y ↦ ∑_{a ∈ Δ} y^a c_a`. -/
noncomputable def cellSys (C : SysCell A c h) (y : S → ℝ) : E → ℝ :=
  ∑ a ∈ C.Δ, a.massActionMonomial y • c a

/-- Its derivative. -/
noncomputable def cellJac (C : SysCell A c h) (y : S → ℝ) : (S → ℝ) →L[ℝ] (E → ℝ) :=
  ∑ a ∈ C.Δ, (∑ j, massActionMonomialGrad a y j •
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) j).smulRight (c a)

theorem cellSys_hasFDerivAt (C : SysCell A c h) (y : S → ℝ) :
    HasFDerivAt C.cellSys (C.cellJac y) y := by
  have : C.cellSys = fun x => ∑ a ∈ C.Δ, a.massActionMonomial x • c a := rfl
  rw [this, cellJac]
  exact HasFDerivAt.fun_sum fun a _ => (massActionMonomial_hasFDerivAt a y).smul_const (c a)

/-- **The cell Jacobian is injective at the simplex solution.** -/
theorem cellJac_injective (C : SysCell A c h) (hE : Fintype.card E = Fintype.card S)
    {y : Concentration S} (hy : y.Positive) {ρ : ℝ} (hρ : 0 < ρ)
    (hsol : ∀ a : C.Δ, a.1.massActionMonomial y = ρ * C.lam a) (u : S → ℝ)
    (hu : C.cellJac y u = 0) : u = 0 := by
  classical
  have hform : C.cellJac y u =
      ∑ a : C.Δ, (a.1.massActionMonomial y * ∑ j, (a.1 j : ℝ) * (u j / y j)) • c a.1 := by
    have h0 : C.cellJac y u = ∑ a ∈ C.Δ, (∑ j, massActionMonomialGrad a y j * u j) • c a := by
      simp [cellJac, smul_eq_mul]
    rw [h0, ← Finset.sum_coe_sort C.Δ]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [massActionMonomialGrad_eq_of_pos _ hy]
    have := (hy j).ne'
    field_simp
  rw [hform] at hu
  set z : S → ℝ := fun j => u j / y j with hz
  obtain ⟨θ, hθ⟩ := C.ker_eq_smul_lam hE
    (fun a => a.1.massActionMonomial y * ∑ j, (a.1 j : ℝ) * z j) hu
  have hlin : ∀ a : C.Δ, ∑ j, (a.1 j : ℝ) * z j = θ / ρ := by
    intro a
    have h1 := hθ a
    rw [hsol a] at h1
    have hl := C.lam_pos a
    field_simp
    nlinarith [h1]
  have hξ := (rowsMatrix_solve C.rows C.card (by rw [rows_row]; exact C.affInd)).2
    (fun j => Option.elim j (-(θ / ρ)) z) (by
      funext a
      rw [rows_mulVec]
      simp only [Option.elim, Pi.zero_apply]
      rw [hlin a]; ring)
  funext j
  have := congrFun hξ (some j)
  simp only [Option.elim, Pi.zero_apply] at this
  have hyj := (hy j).ne'
  simp only [hz] at this
  rw [Pi.zero_apply]
  rcases div_eq_zero_iff.mp this with h0 | h0
  · exact h0
  · exact absurd h0 hyj

/-- The excess exponent `⟨w, a⟩ + h(a) − c₀ ≥ 0` on `A`. -/
noncomputable def expo (C : SysCell A c h) (a : Complex S) : ℕ :=
  (pairing C.w a + h a - C.c₀).toNat

theorem expo_spec (C : SysCell A c h) {a : Complex S} (ha : a ∈ A) :
    ((C.expo a : ℕ) : ℤ) = pairing C.w a + h a - C.c₀ := by
  unfold expo
  apply Int.toNat_of_nonneg
  by_cases hΔ : a ∈ C.Δ
  · rw [C.onCell _ hΔ]; simp
  · have := C.offCell a ha hΔ; omega

theorem expo_eq_zero_iff (C : SysCell A c h) {a : Complex S} (ha : a ∈ A) :
    C.expo a = 0 ↔ a ∈ C.Δ := by
  constructor
  · intro h0
    by_contra hΔ
    have h1 := C.expo_spec ha
    rw [h0] at h1
    have := C.offCell a ha hΔ
    omega
  · intro hΔ
    have h1 := C.expo_spec ha
    rw [C.onCell _ hΔ, sub_self] at h1
    exact_mod_cast h1

/-- The deformed system in toric coordinates: `G(t, y) = ∑_a t^{e_a} y^a c_a`. -/
noncomputable def G (C : SysCell A c h) (p : ℝ × (S → ℝ)) : E → ℝ :=
  ∑ a ∈ A, (p.1 ^ C.expo a * a.massActionMonomial p.2) • c a

theorem G_contDiff (C : SysCell A c h) : ContDiff ℝ ⊤ C.G := by
  rw [contDiff_pi]
  intro e
  simp only [G, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.massActionMonomial]
  fun_prop

theorem G_zero (C : SysCell A c h) (y : S → ℝ) : C.G (0, y) = C.cellSys y := by
  classical
  simp only [G, cellSys]
  rw [← Finset.sum_sdiff C.sub]
  have hoff : ∑ a ∈ A \ C.Δ, ((0 : ℝ) ^ C.expo a * a.massActionMonomial y) • c a = 0 := by
    refine Finset.sum_eq_zero fun a ha => ?_
    obtain ⟨haA, haΔ⟩ := Finset.mem_sdiff.mp ha
    have hne : C.expo a ≠ 0 := fun h0 => haΔ ((C.expo_eq_zero_iff haA).mp h0)
    rw [zero_pow hne, zero_mul, zero_smul]
  rw [hoff, zero_add]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [(C.expo_eq_zero_iff (C.sub ha)).mpr ha, pow_zero, one_mul]

/-- **The toric deformation.** For `t > 0`: `sys(t, t^w y) = t^{c₀} G(t, y)`. -/
theorem sys_scalePoint (C : SysCell A c h) {t : ℝ} (ht : 0 < t) (y : Concentration S) :
    sys A c h t (DecoratedCell.scalePoint C.w t y) =
      Real.exp ((C.c₀ : ℝ) * Real.log t) • C.G (t, y) := by
  funext e
  simp only [sys, G, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [DecoratedCell.monomial_scalePoint]
  have hexp : Real.exp ((h a : ℝ) * Real.log t) *
      Real.exp ((pairing C.w a : ℝ) * Real.log t) =
      Real.exp ((C.c₀ : ℝ) * Real.log t) * t ^ C.expo a := by
    rw [← Real.exp_add, ← Real.exp_log ht, ← Real.exp_nat_mul, Real.exp_log ht, ← Real.exp_add]
    congr 1
    have h' : ((C.expo a : ℕ) : ℝ) = (pairing C.w a : ℝ) + (h a : ℝ) - (C.c₀ : ℝ) := by
      exact_mod_cast C.expo_spec ha
    rw [h']; ring
  calc Real.exp ((h a : ℝ) * Real.log t) *
        (Real.exp ((pairing C.w a : ℝ) * Real.log t) * a.massActionMonomial y) * c a e
      = (Real.exp ((h a : ℝ) * Real.log t) * Real.exp ((pairing C.w a : ℝ) * Real.log t)) *
          a.massActionMonomial y * c a e := by ring
    _ = _ := by rw [hexp]; ring

theorem sys_hasFDerivAt (t : ℝ) (x : S → ℝ) :
    HasFDerivAt (sys A c h t) (∑ a ∈ A, (Real.exp ((h a : ℝ) * Real.log t) •
      ∑ j, massActionMonomialGrad a x j •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) j).smulRight (c a)) x := by
  have : sys A c h t = fun x => ∑ a ∈ A,
      (Real.exp ((h a : ℝ) * Real.log t) * a.massActionMonomial x) • c a := rfl
  rw [this]
  exact HasFDerivAt.fun_sum fun a _ =>
    ((massActionMonomial_hasFDerivAt a x).const_mul (Real.exp ((h a : ℝ) * Real.log t))).smul_const
      (c a)

/-- **The Jacobian along the deformation**: `D sys(t^w y) ∘ diag(t^w) = t^{c₀} D_y G(t, y)`. -/
theorem jacobian_scale (C : SysCell A c h) {t : ℝ} (ht : 0 < t) (y : S → ℝ) :
    fderiv ℝ (sys A c h t) (DecoratedCell.scalePoint C.w t y) ∘L DecoratedCell.scaleCLM C.w t =
      Real.exp ((C.c₀ : ℝ) * Real.log t) •
        (fderiv ℝ C.G (t, y) ∘L ContinuousLinearMap.inr ℝ ℝ (S → ℝ)) := by
  have hsc : (fun y : S → ℝ => DecoratedCell.scalePoint C.w t y) = DecoratedCell.scaleCLM C.w t :=
    by funext y; exact (DecoratedCell.scaleCLM_apply _ _ _).symm
  have h1 : HasFDerivAt (fun y : S → ℝ => sys A c h t (DecoratedCell.scalePoint C.w t y))
      (fderiv ℝ (sys A c h t) (DecoratedCell.scalePoint C.w t y) ∘L
        DecoratedCell.scaleCLM C.w t) y := by
    have hJ := (sys_hasFDerivAt (A := A) (c := c) (h := h) t
      (DecoratedCell.scalePoint C.w t y)).differentiableAt.hasFDerivAt
    have hL : HasFDerivAt (fun y : S → ℝ => DecoratedCell.scalePoint C.w t y)
        (DecoratedCell.scaleCLM C.w t) y := by
      rw [hsc]; exact (DecoratedCell.scaleCLM C.w t).hasFDerivAt
    exact hJ.comp y hL
  have hdiff : DifferentiableAt ℝ C.G (t, y) := (C.G_contDiff.differentiable (by simp)) _
  have h2 : HasFDerivAt (fun y : S → ℝ => Real.exp ((C.c₀ : ℝ) * Real.log t) • C.G (t, y))
      (Real.exp ((C.c₀ : ℝ) * Real.log t) •
        (fderiv ℝ C.G (t, y) ∘L ContinuousLinearMap.inr ℝ ℝ (S → ℝ))) y :=
    (hdiff.hasFDerivAt.comp y (hasFDerivAt_prodMk_right t y)).const_smul
      (Real.exp ((C.c₀ : ℝ) * Real.log t))
  have heq : (fun y : S → ℝ => sys A c h t (DecoratedCell.scalePoint C.w t y)) =
      fun y => Real.exp ((C.c₀ : ℝ) * Real.log t) • C.G (t, y) := by
    funext y; exact C.sys_scalePoint ht y
  rw [heq] at h1
  exact h1.unique h2

/-- **A nondegenerate branch** of zeros of `G`. -/
theorem exists_branch (C : SysCell A c h) (hE : Fintype.card E = Fintype.card S) :
    ∃ y : Concentration S, y.Positive ∧ ∃ ψ : ℝ → (S → ℝ), ψ 0 = y ∧ ContinuousAt ψ 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), C.G (t, ψ t) = 0) ∧
      ∀ᶠ t in 𝓝 (0 : ℝ),
        (fderiv ℝ C.G (t, ψ t) ∘L ContinuousLinearMap.inr ℝ ℝ (S → ℝ)).IsInvertible := by
  classical
  obtain ⟨y, hy, ρ, hρ, hsol⟩ := C.exists_simplex_solution
  have hG0 : C.G (0, y) = 0 := by
    rw [G_zero, cellSys, ← Finset.sum_coe_sort C.Δ]
    simp only [hsol, mul_smul, ← Finset.smul_sum, C.lam_ker, smul_zero]
  have hcd : ContDiffAt ℝ 1 C.G (0, y) := (C.G_contDiff.of_le (by simp)).contDiffAt
  have hpart : fderiv ℝ C.G (0, y) ∘L ContinuousLinearMap.inr ℝ ℝ (S → ℝ) = C.cellJac y := by
    have hdiff : DifferentiableAt ℝ C.G (0, y) := (C.G_contDiff.differentiable (by simp)) _
    have hcomp : HasFDerivAt (fun x => C.G (0, x))
        (fderiv ℝ C.G (0, y) ∘L ContinuousLinearMap.inr ℝ ℝ (S → ℝ)) y :=
      hdiff.hasFDerivAt.comp y (hasFDerivAt_prodMk_right (0 : ℝ) y)
    have heq : (fun x => C.G (0, x)) = C.cellSys := by funext x; exact C.G_zero x
    rw [heq] at hcomp
    exact hcomp.unique (C.cellSys_hasFDerivAt y)
  have hinj : Function.Injective (C.cellJac y : (S → ℝ) →ₗ[ℝ] (E → ℝ)) := by
    intro u v huv
    have h1 : C.cellJac y (u - v) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr huv
    exact sub_eq_zero.mp (C.cellJac_injective hE hy hρ hsol (u - v) h1)
  have hinv : (fderiv ℝ C.G (0, y) ∘L ContinuousLinearMap.inr ℝ ℝ (S → ℝ)).IsInvertible := by
    rw [hpart]
    have hdim : Module.finrank ℝ (S → ℝ) = Module.finrank ℝ (E → ℝ) := by
      simp [Module.finrank_fintype_fun_eq_card, hE]
    have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
    let e : (S → ℝ) ≃ₗ[ℝ] (E → ℝ) :=
      LinearEquiv.ofBijective (C.cellJac y : (S → ℝ) →ₗ[ℝ] (E → ℝ)) ⟨hinj, hsurj⟩
    refine ⟨e.toContinuousLinearEquiv, ?_⟩
    ext v; rfl
  set ψ := hcd.implicitFunction one_ne_zero hinv with hψdef
  have hψ0 : ψ 0 = y := hcd.implicitFunction_apply_self one_ne_zero hinv
  have hψc : ContinuousAt ψ 0 := (hcd.contDiffAt_implicitFunction one_ne_zero hinv).continuousAt
  refine ⟨y, hy, ψ, hψ0, hψc, ?_, ?_⟩
  · filter_upwards [hcd.eventually_apply_implicitFunction one_ne_zero hinv] with t ht
    rw [← hψdef] at ht
    rw [ht, hG0]
  · have hfc : Continuous (fderiv ℝ C.G) := C.G_contDiff.continuous_fderiv (by simp)
    have hpath : ContinuousAt (fun t => ((t, ψ t) : ℝ × (S → ℝ))) 0 :=
      continuousAt_id.prodMk hψc
    set R := (ContinuousLinearMap.compL ℝ (S → ℝ) (ℝ × (S → ℝ)) (E → ℝ)).flip
      (ContinuousLinearMap.inr ℝ ℝ (S → ℝ)) with hR
    have hD : ContinuousAt (fun t => R (fderiv ℝ C.G (t, ψ t))) 0 :=
      R.continuous.continuousAt.comp (hfc.continuousAt.comp hpath)
    have hD0 : R (fderiv ℝ C.G (0, ψ 0)) =
        fderiv ℝ C.G (0, y) ∘L ContinuousLinearMap.inr ℝ ℝ (S → ℝ) := by
      rw [hψ0]; rfl
    have hev := hD.eventually (hD0 ▸ hinv.eventually_nhds)
    filter_upwards [hev] with t ht
    exact ht

end SysCell

/-- **Bihan–Dickenstein–Giaroli lower bound for square polynomial systems.** If `d` positively
decorated lower cells of `(A, c, h)` have pairwise different normals, then for some `t > 0` the
system `∑_a t^{h(a)} x^a c_a = 0` has `d` distinct positive solutions with injective Jacobian. -/
theorem solutions_of_cells {A : Finset (Complex S)} {c : Complex S → (E → ℝ)}
    {h : Complex S → ℤ} (hE : Fintype.card E = Fintype.card S) {d : ℕ}
    (C : Fin d → SysCell A c h) (hw : Function.Injective fun j => (C j).w) :
    ∃ t : ℝ, 0 < t ∧ ∃ X : Fin d → Concentration S,
      (∀ j, (X j).Positive ∧ sys A c h t (X j) = 0 ∧
        Function.Injective (fderiv ℝ (sys A c h t) (X j))) ∧ Function.Injective X := by
  classical
  choose y hy ψ hψ0 hψc hψ hinvev using fun j => (C j).exists_branch hE
  have hposev : ∀ j, ∀ᶠ t in 𝓝 (0 : ℝ), ∀ s, 0 < ψ j t s := by
    intro j
    rw [eventually_all]
    intro s
    have hcs : ContinuousAt (fun t => ψ j t s) 0 :=
      (continuous_apply s).continuousAt.comp (hψc j)
    have : 0 < ψ j 0 s := by rw [hψ0 j]; exact hy j s
    exact hcs.eventually (lt_mem_nhds this)
  have hne : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ p : Fin d × Fin d, p.1 ≠ p.2 →
      DecoratedCell.scalePoint (C p.1).w t (ψ p.1 t) ≠
        DecoratedCell.scalePoint (C p.2).w t (ψ p.2 t) := by
    rw [eventually_all]
    intro p
    by_cases hp : p.1 = p.2
    · exact Eventually.of_forall fun _ h => absurd hp h
    · exact (eventually_scalePoint_ne (fun e => hp (hw e)) (hy p.1) (hy p.2) (hψ0 p.1)
        (hψ0 p.2) (hψc p.1) (hψc p.2)).mono fun t ht _ => ht
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ j, (C j).G (t, ψ j t) = 0) ∧
      (∀ j, ∀ s, 0 < ψ j t s) ∧ (∀ p : Fin d × Fin d, p.1 ≠ p.2 →
        DecoratedCell.scalePoint (C p.1).w t (ψ p.1 t) ≠
          DecoratedCell.scalePoint (C p.2).w t (ψ p.2 t)) ∧
      (∀ j, (fderiv ℝ (C j).G (t, ψ j t) ∘L
        ContinuousLinearMap.inr ℝ ℝ (S → ℝ)).IsInvertible) ∧ 0 < t := by
    filter_upwards [nhdsWithin_le_nhds (eventually_all.mpr hψ),
      nhdsWithin_le_nhds (eventually_all.mpr hposev), hne,
      nhdsWithin_le_nhds (eventually_all.mpr hinvev), self_mem_nhdsWithin]
      with t a1 a2 a3 a4 a5
    exact ⟨a1, a2, a3, a4, a5⟩
  obtain ⟨t, hG, hp, hX, hinv, ht⟩ := hall.exists
  refine ⟨t, ht, fun j => DecoratedCell.scalePoint (C j).w t (ψ j t), fun j => ⟨fun s =>
      mul_pos (Real.exp_pos _) (hp j s), ?_, ?_⟩, fun j j' heq => ?_⟩
  · rw [(C j).sys_scalePoint ht, hG j, smul_zero]
  · intro u u' huu
    rw [← sub_eq_zero, ← map_sub] at huu
    suffices hz : ∀ v, fderiv ℝ (sys A c h t) (DecoratedCell.scalePoint (C j).w t (ψ j t)) v = 0 →
        v = 0 from sub_eq_zero.mp (hz _ huu)
    intro v hv
    obtain ⟨e, he⟩ := hinv j
    have hscale := (C j).jacobian_scale ht (ψ j t)
    set u₀ : S → ℝ := fun s => Real.exp (-((C j).w s : ℝ) * Real.log t) * v s with hu₀
    have huv : DecoratedCell.scaleCLM (C j).w t u₀ = v := by
      funext s
      simp only [DecoratedCell.scaleCLM_apply, DecoratedCell.scalePoint, hu₀, ← mul_assoc,
        ← Real.exp_add]
      rw [show ((C j).w s : ℝ) * Real.log t + -((C j).w s : ℝ) * Real.log t = 0 by ring,
        Real.exp_zero, one_mul]
    have h1 : (Real.exp (((C j).c₀ : ℝ) * Real.log t) •
        (fderiv ℝ (C j).G (t, ψ j t) ∘L ContinuousLinearMap.inr ℝ ℝ (S → ℝ))) u₀ = 0 := by
      rw [← hscale, ContinuousLinearMap.comp_apply, huv]; exact hv
    rw [smul_apply, ← he] at h1
    have h2 : (e : (S → ℝ) →L[ℝ] (E → ℝ)) u₀ = 0 :=
      (smul_eq_zero.mp h1).resolve_left (Real.exp_pos _).ne'
    have hv0 : u₀ = 0 := by
      have := congrArg e.symm h2
      simpa using this
    rw [← huv, hv0, map_zero]
  · by_contra hjj
    exact hX (j, j') hjj heq

end Patchworking

end CRNT
