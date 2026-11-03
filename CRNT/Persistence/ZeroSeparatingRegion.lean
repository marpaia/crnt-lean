import CRNT.Persistence.RegionIndex

/-!
# The zero-separating region

For a finite set `H ⊆ ℝⁿ` closed under permutations of coordinates, a slack `δ`, a ceiling `M`
and a positive point `x₀`, `exists_zsh` produces finitely many half-spaces `⟨a i, x⟩ ≥ b i` with
nonnegative normals such that

* `x₀` satisfies all of them;
* every point satisfying all of them has every coordinate at least `η > 0`;
* at every positive point below `M` lying on the boundary of the region shifted by any
  `σ ∈ [0, R']`, every active normal `a i` and every `h ∈ H` with `⟨a i, h⟩ < 0` satisfy
  `δ ≤ ∑ h_q log x_q`.

The half-spaces are the level-`m` facets of `level_validity` placed on the `m+1` smallest
coordinates at scales `ε ^ e_m`, with exponents `e_m` chosen so that each level dominates the
coordinates outside its block, and all their permutations.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Persistence

open Finset BTree Real Filter Topology

variable {n : ℕ}

theorem btree_zero_eq_leaf (t : BTree 0) : t = BTree.leaf := by cases t; rfl

/-- `⟨N, x ∘ g⟩ = ⟨N ∘ g⁻¹, x⟩`. -/
theorem fdot_comp_perm (N x : Fin n → ℝ) (g : Equiv.Perm (Fin n)) :
    fdot N (x ∘ g) = fdot (N ∘ g.symm) x := by
  unfold fdot
  rw [← Equiv.sum_comp g (fun q => (N ∘ g.symm) q * x q)]
  simp

/-- A bound on the `ℓ¹` norms of the elements of `H`. -/
noncomputable def hmaxH (H : Finset (Fin n → ℝ)) : ℝ := ∑ h ∈ H, ∑ q, |h q|

theorem hmaxH_nonneg (H : Finset (Fin n → ℝ)) : 0 ≤ hmaxH H :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _

theorem norm1_le_hmaxH {H : Finset (Fin n → ℝ)} {h : Fin n → ℝ} (hh : h ∈ H) :
    ∑ q, |h q| ≤ hmaxH H :=
  single_le_sum (f := fun h : Fin n → ℝ => ∑ q, |h q|)
    (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) hh

/-- The restricted list of level `m`. -/
noncomputable def HkL (H : Finset (Fin n → ℝ)) (m : ℕ) : List (ℕ → ℝ) :=
  H.toList.map (restr n m)

/-- The level ratio. -/
noncomputable def Lam (H : Finset (Fin n → ℝ)) (m : ℕ) (p : ℝ) : ℝ :=
  1 + (2 * hmaxH H + 1) / (thePack m (HkL H m) (p + 1)).κ

/-- Products of the level ratios. -/
noncomputable def Pr (H : Finset (Fin n → ℝ)) : ℕ → ℝ
  | 0 => 1
  | m + 1 => Pr H m * Lam H m (Pr H m)

theorem one_lt_Lam (H : Finset (Fin n → ℝ)) (m : ℕ) (p : ℝ) : 1 < Lam H m p := by
  have := (thePack m (HkL H m) (p + 1)).hκ
  have := hmaxH_nonneg H
  unfold Lam; have : 0 < (2 * hmaxH H + 1) / (thePack m (HkL H m) (p + 1)).κ := by positivity
  linarith

theorem one_le_Pr (H : Finset (Fin n → ℝ)) : ∀ m, 1 ≤ Pr H m
  | 0 => le_rfl
  | m + 1 => by
      have := one_le_Pr H m; have := one_lt_Lam H m (Pr H m)
      simp only [Pr]; nlinarith

/-- The package of level `m`. -/
noncomputable def pk (H : Finset (Fin n → ℝ)) (m : ℕ) :
    LevelPack m (HkL H m) (max (Pr H m + 1) 1) :=
  thePack m (HkL H m) (Pr H m + 1)

theorem max_Pr (H : Finset (Fin n → ℝ)) (m : ℕ) : max (Pr H m + 1) 1 = Pr H m + 1 :=
  max_eq_left (by linarith [one_le_Pr H m])

/-- The scale exponents. -/
noncomputable def eexp (H : Finset (Fin n → ℝ)) (m : ℕ) : ℝ := Pr H (n - 1) / Pr H m

theorem eexp_pos (H : Finset (Fin n → ℝ)) (m : ℕ) : 0 < eexp H m := by
  have := one_le_Pr H (n - 1); have := one_le_Pr H m
  unfold eexp; positivity

theorem eexp_mul_Pr (H : Finset (Fin n → ℝ)) (m : ℕ) : eexp H m * Pr H m = eexp H 0 := by
  have := one_le_Pr H m
  unfold eexp; simp [Pr]; field_simp

theorem eexp_succ (H : Finset (Fin n → ℝ)) (m : ℕ) :
    eexp H m = Lam H m (Pr H m) * eexp H (m + 1) := by
  have := one_le_Pr H m; have := one_lt_Lam H m (Pr H m)
  unfold eexp; simp only [Pr]; field_simp

theorem eexp_le_zero (H : Finset (Fin n → ℝ)) (m : ℕ) : eexp H m ≤ eexp H 0 := by
  have h1 := one_le_Pr H m
  have h2 := eexp_mul_Pr H m
  have h3 := eexp_pos H m
  nlinarith

theorem eexp_succ_lt (H : Finset (Fin n → ℝ)) (m : ℕ) : eexp H (m + 1) < eexp H m := by
  rw [eexp_succ H m]
  have := one_lt_Lam H m (Pr H m); have := eexp_pos H (m + 1)
  nlinarith

theorem eexp_top (H : Finset (Fin n → ℝ)) : eexp H (n - 1) = 1 := by
  have := one_le_Pr H (n - 1); unfold eexp; field_simp

/-- The facet normal of level `m`, path `P`. -/
noncomputable def facetN (H : Finset (Fin n → ℝ)) (m : ℕ) (P : List ℕ) : Fin n → ℝ :=
  levelNormal n m (pk H m).t P

/-- The facet offset of level `m`, path `P`, at scale parameter `ε`. -/
noncomputable def facetB (H : Finset (Fin n → ℝ)) (ε : ℝ) (m : ℕ) (P : List ℕ) : ℝ :=
  ε ^ eexp H m - pathD (ε ^ eexp H m) (pk H m).t P


theorem tailZ_pos {x : Fin n → ℝ} (hx : ∀ q, 0 < x q) (m i : ℕ) : 0 < tailZ n m x i := by
  unfold tailZ; split_ifs <;> [exact hx _; exact one_pos]

theorem facet_val_eq (H : Finset (Fin n → ℝ)) (m : ℕ) (hm : m < n) (s : ℝ) (P : List ℕ)
    (hP : IsPath (pk H m).t P) (x : Fin n → ℝ) :
    tailZ n m x 0 + BTree.val s (pk H m).t P (fun l => tailZ n m x (l + 1)) =
      fdot (facetN H m P) x + pathD s (pk H m).t P := by
  rw [val_eq s (pk H m).t 0 (fun _ => 1) P hP, facetN, fdot_levelNormal m hm _ rfl]
  simp only [Nat.zero_add]; ring

/-- The analysis at a sorted point. -/
theorem sorted_valid (H : Finset (Fin n → ℝ)) {δ M ε : ℝ} (hM : 1 ≤ M) (hε0 : 0 < ε)
    (hε1 : ε < 1)
    (hc1 : ∀ m, m < n → ε ^ eexp H m < (pk H m).s₀)
    (hc2 : ∀ m, m < n → (2:ℝ) ^ (Pr H m + 2) * ε ^ eexp H m ≤ 1)
    (hc3 : ∀ m, m + 1 < n → 8 * ((m:ℝ) + 1) * ε ^ eexp H m ≤ ε ^ eexp H (m + 1))
    (hc4 : ∀ m, m + 1 < n → (δ + (pk H m).κ * log 2 + hmaxH H * (log 4 + log M)) /
      ((hmaxH H + 1) * eexp H (m + 1)) ≤ -log ε)
    (hc4' : log 2 + δ / (pk H (n - 1)).κ ≤ -log ε)
    {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ ≤ ε ^ eexp H 0 / 2)
    (xs : Fin n → ℝ) (hanti : Antitone xs) (hpos : ∀ q, 0 < xs q) (hle : ∀ q, xs q ≤ M)
    (hfac : ∀ m', m' < n → ∀ P', IsPath (pk H m').t P' →
      facetB H ε m' P' - σ ≤ fdot (facetN H m' P') xs)
    (m : ℕ) (hm : m < n) (P : List ℕ) (hP : IsPath (pk H m).t P)
    (hact : fdot (facetN H m P) xs = facetB H ε m P - σ) :
    ∀ h ∈ H, fdot (facetN H m P) h < 0 → δ ≤ ∑ q, h q * log (xs q) := by
  intro h hh hneg
  set s := ε ^ eexp H m with hsdef
  set c := s - σ with hcdef
  set z := tailZ n m xs with hzdef
  set t := (pk H m).t with htdef
  have hs0 : 0 < s := rpow_pos_of_pos hε0 _
  have he0m : ε ^ eexp H 0 ≤ s := rpow_le_rpow_of_exponent_ge hε0 hε1.le (eexp_le_zero H m)
  have hσs : σ ≤ s / 2 := by linarith
  have hz : ∀ i, 0 < z i := tailZ_pos hpos m
  have hdesc : ∀ i, i < m → z (i + 1) ≤ z i := by
    intro i hi
    simp only [hzdef, tailZ, dif_pos (show n - 1 - m + (i + 1) < n by omega),
      dif_pos (show n - 1 - m + i < n by omega)]
    exact hanti (show (⟨n - 1 - m + i, by omega⟩ : Fin n) ≤ ⟨n - 1 - m + (i + 1), by omega⟩ by
      simp [Fin.le_def])
  have hfac' : ∀ P', IsPath t P' → c ≤ z 0 + BTree.val s t P' (fun l => z (l + 1)) := by
    intro P' hP'
    have := hfac m hm P' hP'
    rw [facet_val_eq H m hm s P' hP' xs]
    simp only [facetB, ← hsdef] at this; linarith
  have hact' : z 0 + BTree.val s t P (fun l => z (l + 1)) = c := by
    rw [facet_val_eq H m hm s P hP xs, hact]
    simp only [facetB, ← hsdef]; ring
  -- `z 0 ≤ 2 s`
  have hz0le : z 0 ≤ 2 * s := by
    have hpD := (pk H m).hpD s hs0 (hc1 m hm) P hP
    have hval := val_eq s t 0 (fun _ => 1) P hP (fun l => z (l + 1))
    have hsum : 0 ≤ ∑ l ∈ range m, leafB t 0 (fun _ => 1) P (0 + l) * z (l + 1) := by
      refine sum_nonneg fun l hl => mul_nonneg ?_ (hz _).le
      exact (leafB_mem t _ 0 _ (pk H m).hGP P hP (0 + l) (by omega)
        (by simp at hl; omega)).1
    linarith
  -- the box
  have hlevel0 : ε ^ eexp H 0 / 2 ≤ z m := by
    have ht0 : (pk H 0).t = BTree.leaf := btree_zero_eq_leaf _
    have hP0 : IsPath (pk H 0).t [] := by rw [ht0]; rfl
    have := hfac 0 (by omega) [] hP0
    have hN : fdot (facetN H 0 []) xs = xs ⟨n - 1, by omega⟩ := by
      rw [facetN, fdot_levelNormal 0 (by omega) _ rfl, range_zero, sum_empty, add_zero]
      simp only [tailZ, dif_pos (show n - 1 - 0 + 0 < n by omega)]
      congr 1 <;> (ext; simp)
    have hB0 : facetB H ε 0 [] = ε ^ eexp H 0 := by
      simp only [facetB]; rw [ht0]; simp [pathD]
    rw [hN, hB0] at this
    have hzm : z m = xs ⟨n - 1, by omega⟩ := by
      simp only [hzdef, tailZ, dif_pos (show n - 1 - m + m < n by omega)]
      congr 1 <;> (ext; simp <;> omega)
    rw [hzm]; linarith
  have hbox : z 0 ^ max (Pr H m + 1) 1 ≤ z m := by
    rw [max_Pr]
    have hB0 : 0 ≤ Pr H m + 1 := by linarith [one_le_Pr H m]
    have h1 : z 0 ^ (Pr H m + 1) ≤ (2 * s) ^ (Pr H m + 1) :=
      rpow_le_rpow (hz 0).le hz0le hB0
    have h2 : (2 * s) ^ (Pr H m + 1) = (2:ℝ) ^ (Pr H m + 1) * ε ^ eexp H 0 * s := by
      rw [mul_rpow (by norm_num) hs0.le, hsdef, ← rpow_mul hε0.le, mul_add, mul_one,
        eexp_mul_Pr, rpow_add hε0]; ring
    have h3 : (2:ℝ) ^ (Pr H m + 1) * s ≤ 1 / 2 := by
      have := hc2 m hm
      rw [show Pr H m + 2 = (Pr H m + 1) + 1 by ring, rpow_add (by norm_num), rpow_one] at this
      linarith
    have h4 : 0 ≤ ε ^ eexp H 0 := (rpow_pos_of_pos hε0 _).le
    have : (2:ℝ) ^ (Pr H m + 1) * ε ^ eexp H 0 * s ≤ ε ^ eexp H 0 / 2 := by
      have := mul_le_mul_of_nonneg_left h3 h4
      linarith
    linarith
  obtain ⟨_, hval⟩ := (pk H m).hvalid s hs0 (hc1 m hm) c (by linarith) (by linarith) z hz hdesc
    hbox hfac' P hP hact'
  have hrest : restr n m h ∈ HkL H m := by
    simp only [HkL, List.mem_map, Finset.mem_toList]; exact ⟨h, hh, rfl⟩
  have hnd : normalDot m t P (restr n m h) < 0 := by
    rw [← fdot_levelNormal_h m hm _ rfl]; exact hneg
  have hmain := hval _ hrest hnd
  rw [sum_log_split m hm h xs]
  have htail : ∑ i ∈ range (m + 1), restr n m h i * log (tailZ n m xs i) =
      ∑ i ∈ range (m + 1), restr n m h i * log (z i) := rfl
  rw [htail]
  -- `-log z 0 ≥ e_m (-log ε) - log 2`
  have hlogz0 : eexp H m * -log ε - log 2 ≤ -log (z 0) := by
    have := log_le_log (hz 0) hz0le
    rw [log_mul (by norm_num) hs0.ne', hsdef, log_rpow hε0] at this
    linarith
  have hκ := (pk H m).hκ
  rcases Nat.lt_or_ge (m + 1) n with hmn | hmn
  · -- outside the block
    have hwall := wallPath_facts (ε ^ eexp H (m + 1)) (pk H (m + 1)).t 0 (fun _ => 1) 1
      (pk H (m + 1)).ρ0 (pk H (m + 1)).hWF
    have hPw : IsPath (pk H (m + 1)).t (wallPath (pk H (m + 1)).t) :=
      isPath_wallPath _ _ _ (pk H (m + 1)).hWF
    have hfw := hfac (m + 1) hmn _ hPw
    have hBw : facetB H ε (m + 1) (wallPath (pk H (m + 1)).t) = ε ^ eexp H (m + 1) := by
      simp only [facetB, hwall.1, sub_zero]
    have hNw : fdot (facetN H (m + 1) (wallPath (pk H (m + 1)).t)) xs =
        xs ⟨n - 1 - m - 1, by omega⟩ + ∑ l ∈ range (m + 1), z l := by
      rw [facetN, fdot_levelNormal (m + 1) hmn _ rfl]
      have h0 : tailZ n (m + 1) xs 0 = xs ⟨n - 1 - m - 1, by omega⟩ := by
        simp only [tailZ, dif_pos (show n - 1 - (m + 1) + 0 < n by omega)]
        congr 1 <;> (ext; simp <;> omega)
      rw [h0]; congr 1
      refine sum_congr rfl fun l hl => ?_
      simp at hl
      rw [hwall.2 l (by omega) (by omega), one_mul]
      simp only [hzdef, tailZ, dif_pos (show n - 1 - (m + 1) + (l + 1) < n by omega),
        dif_pos (show n - 1 - m + l < n by omega)]
      congr 1 <;> (ext; simp <;> omega)
    rw [hBw, hNw] at hfw
    have hsumz : ∑ l ∈ range (m + 1), z l ≤ (m + 1) * z 0 := by
      calc ∑ l ∈ range (m + 1), z l ≤ ∑ l ∈ range (m + 1), z 0 := by
            refine sum_le_sum fun l hl => ?_
            simp at hl
            have : ∀ k, k ≤ m → z k ≤ z 0 := by
              intro k hk
              induction k with
              | zero => exact le_rfl
              | succ k ih => exact le_trans (hdesc k (by omega)) (ih (by omega))
            exact this l (by omega)
        _ = (m + 1) * z 0 := by simp
    have hem1 : ε ^ eexp H 0 ≤ ε ^ eexp H (m + 1) :=
      rpow_le_rpow_of_exponent_ge hε0 hε1.le (eexp_le_zero H (m + 1))
    have hc3' := hc3 m hmn
    set s1 := ε ^ eexp H (m + 1) with hs1
    have hs1pos : 0 < s1 := rpow_pos_of_pos hε0 _
    have hout0 : s1 / 4 ≤ xs ⟨n - 1 - m - 1, by omega⟩ := by
      have : ((m:ℝ) + 1) * z 0 ≤ 2 * ((m:ℝ) + 1) * s := by nlinarith
      nlinarith
    -- every coordinate outside the block is in `[s1/4, M]`
    set Lout := -log (s1 / 4) + log M with hLout
    have hlogM : 0 ≤ log M := log_nonneg hM
    have hs14 : s1 / 4 ≤ 1 := by
      have : s1 ≤ 1 := rpow_le_one hε0.le hε1.le (eexp_pos H (m + 1)).le
      linarith
    have hneglog : 0 ≤ -log (s1 / 4) := by
      have := log_nonpos (by positivity) hs14; linarith
    have hcoord : ∀ q ∈ range (n - 1 - m), |extZ (fun q => log (xs q)) q| ≤ Lout := by
      intro q hq
      simp at hq
      simp only [extZ, dif_pos (show q < n by omega)]
      have hq1 : xs ⟨n - 1 - m - 1, by omega⟩ ≤ xs ⟨q, by omega⟩ :=
        hanti (show (⟨q, by omega⟩ : Fin n) ≤ ⟨n - 1 - m - 1, by omega⟩ by simp [Fin.le_def]; omega)
      have hlo := log_le_log (by positivity) (le_trans hout0 hq1)
      have hhi := log_le_log (hpos _) (hle ⟨q, by omega⟩)
      rw [abs_le]; constructor <;> linarith
    have hhead : -(hmaxH H * Lout) ≤
        ∑ q ∈ range (n - 1 - m), extZ (fun q => h q * log (xs q)) q := by
      have habs : ∑ q ∈ range (n - 1 - m), |extZ h q| ≤ hmaxH H := by
        refine le_trans ?_ (norm1_le_hmaxH hh)
        rw [sum_split_tail m hm (fun q => |h q|)]
        have h1 : ∑ q ∈ range (n - 1 - m), |extZ h q| =
            ∑ q ∈ range (n - 1 - m), extZ (fun q => |h q|) q :=
          sum_congr rfl fun q hq => by simp at hq; simp [extZ, show q < n by omega]
        have h2 : 0 ≤ ∑ i ∈ range (m + 1), extZ (fun q => |h q|) (n - 1 - m + i) :=
          sum_nonneg fun i _ => by unfold extZ; split_ifs <;> simp
        linarith
      have hLout0 : 0 ≤ Lout := by linarith
      calc -(hmaxH H * Lout) ≤ -(∑ q ∈ range (n - 1 - m), |extZ h q| * Lout) := by
            rw [← sum_mul]; nlinarith
        _ = ∑ q ∈ range (n - 1 - m), -(|extZ h q| * Lout) := by rw [sum_neg_distrib]
        _ ≤ _ := by
            refine sum_le_sum fun q hq => ?_
            have hc := hcoord q hq
            have he : extZ (fun q => h q * log (xs q)) q =
                extZ h q * extZ (fun q => log (xs q)) q := by
              simp at hq; simp [extZ, show q < n by omega]
            rw [he]
            have := abs_mul (extZ h q) (extZ (fun q => log (xs q)) q)
            have h3 : |extZ h q * extZ (fun q => log (xs q)) q| ≤ |extZ h q| * Lout := by
              rw [this]; exact mul_le_mul_of_nonneg_left hc (abs_nonneg _)
            have := neg_abs_le (extZ h q * extZ (fun q => log (xs q)) q)
            linarith
    -- assemble
    have hLout_eq : Lout = eexp H (m + 1) * -log ε + log 4 + log M := by
      rw [hLout, log_div hs1pos.ne' (by norm_num), hs1, log_rpow hε0]; ring
    have hκLam : (pk H m).κ * eexp H m = ((pk H m).κ + 2 * hmaxH H + 1) * eexp H (m + 1) := by
      rw [eexp_succ H m]
      simp only [Lam]
      have : (thePack m (HkL H m) (Pr H m + 1)).κ = (pk H m).κ := rfl
      rw [this]
      field_simp
      ring
    have hthr := hc4 m hmn
    have hden : 0 < (hmaxH H + 1) * eexp H (m + 1) := by
      have := hmaxH_nonneg H; have := eexp_pos H (m + 1); positivity
    rw [div_le_iff₀ hden] at hthr
    have he1 := eexp_pos H (m + 1)
    have ha : 0 ≤ -log ε := by have := log_neg hε0 hε1; linarith
    have hmainb : (pk H m).κ * (eexp H m * -log ε - log 2) ≤ (pk H m).κ * -log (z 0) :=
      mul_le_mul_of_nonneg_left hlogz0 hκ.le
    have hprod : 0 ≤ (pk H m).κ * (eexp H (m + 1) * -log ε) := by positivity
    have e2 : hmaxH H * Lout = hmaxH H * (eexp H (m + 1) * -log ε) +
        hmaxH H * (log 4 + log M) := by rw [hLout_eq]; ring
    have e3 : (pk H m).κ * (eexp H m * -log ε - log 2) =
        ((pk H m).κ + 2 * hmaxH H + 1) * (eexp H (m + 1) * -log ε) - (pk H m).κ * log 2 := by
      have : (pk H m).κ * (eexp H m * -log ε - log 2) =
          ((pk H m).κ * eexp H m) * -log ε - (pk H m).κ * log 2 := by ring
      rw [this, hκLam]; ring
    have e4 : -log ε * ((hmaxH H + 1) * eexp H (m + 1)) =
        hmaxH H * (eexp H (m + 1) * -log ε) + eexp H (m + 1) * -log ε := by ring
    have e5 : ((pk H m).κ + 2 * hmaxH H + 1) * (eexp H (m + 1) * -log ε) =
        (pk H m).κ * (eexp H (m + 1) * -log ε) + 2 * (hmaxH H * (eexp H (m + 1) * -log ε)) +
          eexp H (m + 1) * -log ε := by ring
    have hthr' : δ + (pk H m).κ * log 2 + hmaxH H * (log 4 + log M) ≤
        -log ε * ((hmaxH H + 1) * eexp H (m + 1)) := by linarith
    linarith
  · -- the top level: no outside coordinates
    have hmtop : m = n - 1 := by omega
    have hoff : n - 1 - m = 0 := by omega
    rw [hoff, range_zero, sum_empty, zero_add]
    have hetop : eexp H m = 1 := by rw [hmtop, eexp_top]
    rw [hetop, one_mul] at hlogz0
    have hκ' : (pk H m).κ = (pk H (n - 1)).κ := by rw [hmtop]
    have : δ / (pk H m).κ ≤ -log (z 0) := by rw [hκ']; linarith
    rw [div_le_iff₀ hκ] at this
    linarith


theorem sum_log_comp_perm (h y : Fin n → ℝ) (τ : Equiv.Perm (Fin n)) :
    ∑ q, h q * log ((y ∘ τ) q) = ∑ q, (h ∘ τ.symm) q * log (y q) := by
  rw [← Equiv.sum_comp τ (fun q => (h ∘ τ.symm) q * log (y q))]
  simp

theorem facetN_monotone (H : Finset (Fin n → ℝ)) (m : ℕ) (P : List ℕ)
    (hP : IsPath (pk H m).t P) : Monotone (facetN H m P) := by
  have hmono := leafB_mono (pk H m).t 0 (fun _ => 1) 1 (pk H m).ρ0 (pk H m).hWF P hP
  have hge1 : ∀ l, l < m → 1 ≤ leafB (pk H m).t 0 (fun _ => 1) P l := by
    intro l hl
    induction l with
    | zero => exact hmono.1 (by omega)
    | succ l ih => exact le_trans (ih (by omega)) (hmono.2 l (by omega) (by omega))
  have hle : ∀ l l', l ≤ l' → l' < m →
      leafB (pk H m).t 0 (fun _ => 1) P l ≤ leafB (pk H m).t 0 (fun _ => 1) P l' := by
    intro l l' hll' hl'
    induction l', hll' using Nat.le_induction with
    | base => exact le_rfl
    | succ l' _ ih => exact le_trans (ih (by omega)) (hmono.2 l' (by omega) (by omega))
  intro q q' hqq'
  have hqq'' : q.val ≤ q'.val := hqq'
  have hq' := q'.isLt
  have hq := q.isLt
  simp only [facetN, levelNormal]
  split_ifs <;> first
    | exact le_rfl
    | (exfalso; omega)
    | (exact zero_le_one)
    | (exact le_trans zero_le_one (hge1 _ (by omega)))
    | (exact hge1 _ (by omega))
    | (exact hle _ _ (by omega) (by omega))

theorem pathD_antitone : ∀ {d : ℕ} (t : BTree d) (βp ρp B : ℝ), WF t βp ρp → GapsPos B t →
    ∀ P, IsPath t P → ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ ≤ s₂ → pathD s₂ t P ≤ pathD s₁ t P
  | _, .leaf, _, _, _, _, _, _, _, _, _, _, _ => by simp [pathD]
  | _, .node n β lo hi sub, βp, ρp, B, hWF, hGP, P, hP, s₁, s₂, h1, h12 => by
    obtain ⟨i, rest, rfl, hin, hrest⟩ := hP
    simp only [pathD]
    have hcol : colD s₂ β hi i ≤ colD s₁ β hi i := by
      simp only [colD, neg_le_neg_iff]
      apply sum_le_sum
      intro i' hi'
      have hi'n : i' + 1 < n := by simp at hi'; omega
      have hgap := hGP.2.1 i' hi'n
      have hh := (hWF.2.2.1 i' hi'n).1
      have hb0 := (hGP.1 i' (by omega)).1
      exact mul_le_mul_of_nonneg_left (rpow_le_rpow h1.le h12 (by linarith)) (by linarith)
    have := pathD_antitone (sub i) (β i) (nodeRad ρp n β hi i) B (hWF.2.2.2.2 i hin)
      (hGP.2.2 i hin) rest hrest s₁ s₂ h1 h12
    linarith

theorem pathD_continuousOn : ∀ {d : ℕ} (t : BTree d) (P : List ℕ),
    ContinuousOn (fun s => pathD s t P) (Set.Ioi 0)
  | _, .leaf, _ => by simp only [pathD]; exact continuousOn_const
  | _, .node _ _ _ _ _, [] => by simp only [pathD]; exact continuousOn_const
  | _, .node n β lo hi sub, i :: rest => by
    simp only [pathD]
    refine ContinuousOn.add ?_ (pathD_continuousOn (sub i) rest)
    simp only [colD]
    refine ContinuousOn.neg (continuousOn_finset_sum _ fun i' _ => ?_)
    exact continuousOn_const.mul
      (ContinuousOn.rpow_const continuousOn_id fun x hx => Or.inl (ne_of_gt hx))

theorem facetB_monotoneOn (H : Finset (Fin n → ℝ)) (m : ℕ) (P : List ℕ)
    (hP : IsPath (pk H m).t P) : MonotoneOn (fun ε => facetB H ε m P) (Set.Ioi 0) := by
  intro ε₁ h1 ε₂ h2 h12
  simp only [facetB]
  have he := eexp_pos H m
  have hle : ε₁ ^ eexp H m ≤ ε₂ ^ eexp H m := rpow_le_rpow (le_of_lt h1) h12 he.le
  have := pathD_antitone (pk H m).t 1 (pk H m).ρ0 _ (pk H m).hWF (pk H m).hGP P hP
    (ε₁ ^ eexp H m) (ε₂ ^ eexp H m) (rpow_pos_of_pos h1 _) hle
  linarith

theorem facetB_continuousOn (H : Finset (Fin n → ℝ)) (m : ℕ) (P : List ℕ) :
    ContinuousOn (fun ε => facetB H ε m P) (Set.Ioi 0) := by
  simp only [facetB]
  have hc : ContinuousOn (fun ε : ℝ => ε ^ eexp H m) (Set.Ioi 0) :=
    ContinuousOn.rpow_const continuousOn_id fun x hx => Or.inl (ne_of_gt hx)
  refine hc.sub ((pathD_continuousOn (pk H m).t P).comp hc ?_)
  intro x hx
  exact rpow_pos_of_pos hx _

/-- **The zero-separating regions as a family in the scale `ε`.** The facet normals `a` depend
only on `H`; the offsets are explicit functions `bf ε` of the scale, monotone and continuous in
`ε > 0`.  For every slack `δ`, box `M` and lower bound `μ` on the start point, every scale `ε` in
an interval `(0, ε₁)` gives a valid region: it contains every point with all coordinates `≥ μ`,
its points have all coordinates `≥ ε ^ e₀`, its enlargements by `σ ≤ ε ^ e₀ / 2` stay positive,
and the validity condition holds on every facet of every such enlargement inside the box. -/
theorem exists_zsh_family (hn : 1 ≤ n) (H : Finset (Fin n → ℝ))
    (hsym : ∀ h ∈ H, ∀ ρ : Equiv.Perm (Fin n), h ∘ ρ ∈ H) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (a : ι → Fin n → ℝ) (bf : ℝ → ι → ℝ),
    (∀ i, MonotoneOn (fun ε => bf ε i) (Set.Ioi 0)) ∧
    (∀ i, ContinuousOn (fun ε => bf ε i) (Set.Ioi 0)) ∧
    (∀ i (x : Fin n → ℝ), (∀ q, 0 < x q) → 0 < fdot (a i) x) ∧
    ∀ (δ M : ℝ), 1 ≤ M → ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε, 0 < ε → ε < ε₁ →
      (∀ μ : ℝ, 0 < μ → (∀ m, m < n → ε ^ eexp H m < μ / 2) →
        ∀ x₀ : Fin n → ℝ, (∀ q, μ ≤ x₀ q) → ∀ i, bf ε i ≤ fdot (a i) x₀) ∧
      (∀ x, (∀ i, bf ε i ≤ fdot (a i) x) → ∀ q, ε ^ eexp H 0 ≤ x q) ∧
      (∀ x, (∀ i, bf ε i - ε ^ eexp H 0 / 2 ≤ fdot (a i) x) → ∀ q, ε ^ eexp H 0 / 2 ≤ x q) ∧
      (∀ σ, 0 ≤ σ → σ ≤ ε ^ eexp H 0 / 2 → ∀ x : Fin n → ℝ, (∀ q, 0 < x q) → (∀ q, x q ≤ M) →
        (∀ i, bf ε i - σ ≤ fdot (a i) x) → ∀ i, fdot (a i) x = bf ε i - σ →
        ∀ h ∈ H, fdot (a i) h < 0 → δ ≤ ∑ q, h q * log (x q)) := by
  -- the facets
  let ι := Σ m : Fin n, Fin (paths (pk H m).t).length × Equiv.Perm (Fin n)
  let Pof : ι → List ℕ := fun i => (paths (pk H i.1).t).get i.2.1
  let a : ι → Fin n → ℝ := fun i => facetN H i.1 (Pof i) ∘ i.2.2
  have hPof : ∀ i : ι, IsPath (pk H i.1).t (Pof i) := fun i =>
    (mem_paths_iff _ _).mp (List.get_mem _ _)
  have hidx : ∀ (m : Fin n) (P : List ℕ), IsPath (pk H m).t P →
      ∃ k : Fin (paths (pk H m).t).length, (paths (pk H m).t).get k = P := fun m P hP =>
    List.mem_iff_get.mp ((mem_paths_iff _ _).mpr hP)
  have hadot : ∀ (i : ι) (x : Fin n → ℝ),
      fdot (a i) x = fdot (facetN H i.1 (Pof i)) (x ∘ i.2.2.symm) := by
    intro i x; rw [fdot_comp_perm]; simp [a]
  have hlevel0 : ∀ t : BTree 0, paths t = [[]] := fun t => by rw [btree_zero_eq_leaf t]; rfl
  have hnon : Nonempty ι := ⟨⟨⟨0, hn⟩, ⟨0, by rw [hlevel0]; simp⟩, 1⟩⟩
  refine ⟨ι, inferInstance, hnon, a, fun ε i => facetB H ε i.1 (Pof i),
    fun i => facetB_monotoneOn H _ _ (hPof i), fun i => facetB_continuousOn H _ _, ?_,
    fun δ M hM => ?_⟩
  · -- the normals are positive on the positive orthant
    intro i x hx
    obtain ⟨m, k, pm⟩ := i
    rw [hadot]
    have hm := m.isLt
    have hP := hPof ⟨m, k, pm⟩
    simp only at hP ⊢
    rw [facetN, fdot_levelNormal m hm _ rfl]
    have hz0 : 0 < tailZ n m (x ∘ pm.symm) 0 := tailZ_pos (fun q => hx _) _ _
    have hsum : 0 ≤ ∑ l ∈ range m, leafB (pk H m).t 0 (fun _ => 1) (Pof ⟨m, k, pm⟩) l *
        tailZ n m (x ∘ pm.symm) (l + 1) := by
      refine sum_nonneg fun l hl => mul_nonneg ?_ (tailZ_pos (fun q => hx _) _ _).le
      exact (leafB_mem _ _ 0 _ (pk H m).hGP _ hP l (by omega) (by simp at hl; omega)).1
    linarith
  -- the scale
  have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ), ε < 1 ∧ log 2 + δ / (pk H (n - 1)).κ ≤ -log ε ∧
      ∀ m ∈ range n, ε ^ eexp H m < (pk H m).s₀ ∧
        ε ^ eexp H m < 1 / (2:ℝ) ^ (Pr H m + 2) ∧
        (m + 1 < n → ε ^ (eexp H m - eexp H (m + 1)) < 1 / (8 * ((m:ℝ) + 1))) ∧
        (δ + (pk H m).κ * log 2 + hmaxH H * (log 4 + log M)) /
          ((hmaxH H + 1) * eexp H (m + 1)) ≤ -log ε := by
    have h1 : ∀ᶠ ε in 𝓝[>] (0:ℝ), ε < 1 := by
      filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with ε hε using hε.2
    refine h1.and ((eventually_neglog_ge _).and ?_)
    rw [Filter.eventually_all_finset]
    intro m _
    refine (eventually_small (eexp_pos H m) (pk H m).hs₀).and ?_
    refine (eventually_small (eexp_pos H m) (by positivity)).and ?_
    refine Filter.Eventually.and ?_ (eventually_neglog_ge _)
    by_cases hm1 : m + 1 < n
    · exact (eventually_small (by linarith [eexp_succ_lt H m]) (by positivity)).mono
        fun ε hε _ => hε
    · exact Filter.Eventually.of_forall fun ε h => absurd h hm1
  obtain ⟨ε₁, hε₁, hε₁P⟩ := (nhdsGT_basis (0:ℝ)).eventually_iff.mp hev
  refine ⟨ε₁, hε₁, fun ε hε0 hεlt => ?_⟩
  obtain ⟨hε1, hc4', hall⟩ := hε₁P ⟨hε0, hεlt⟩
  have hcm := fun m (hm : m < n) => hall m (by simpa using hm)
  -- the conditions of `sorted_valid`
  have hc1 : ∀ m, m < n → ε ^ eexp H m < (pk H m).s₀ := fun m hm => (hcm m hm).1
  have hc2 : ∀ m, m < n → (2:ℝ) ^ (Pr H m + 2) * ε ^ eexp H m ≤ 1 := by
    intro m hm
    have h := (hcm m hm).2.1
    have hp : 0 < (2:ℝ) ^ (Pr H m + 2) := by positivity
    rw [lt_div_iff₀ hp] at h; linarith
  have hc3 : ∀ m, m + 1 < n → 8 * ((m:ℝ) + 1) * ε ^ eexp H m ≤ ε ^ eexp H (m + 1) := by
    intro m hm
    have h := (hcm m (by omega)).2.2.1 hm
    have hsplit : ε ^ eexp H m = ε ^ eexp H (m + 1) * ε ^ (eexp H m - eexp H (m + 1)) := by
      rw [← rpow_add hε0]; ring_nf
    have hp : 0 < 8 * ((m:ℝ) + 1) := by positivity
    rw [lt_div_iff₀ hp] at h
    rw [hsplit]
    have h1 : 0 < ε ^ eexp H (m + 1) := rpow_pos_of_pos hε0 _
    nlinarith
  have hc4 : ∀ m, m + 1 < n → (δ + (pk H m).κ * log 2 + hmaxH H * (log 4 + log M)) /
      ((hmaxH H + 1) * eexp H (m + 1)) ≤ -log ε := fun m hm => (hcm m (by omega)).2.2.2
  let b : ι → ℝ := fun i => facetB H ε i.1 (Pof i)
  show (∀ μ : ℝ, 0 < μ → (∀ m, m < n → ε ^ eexp H m < μ / 2) →
        ∀ x₀ : Fin n → ℝ, (∀ q, μ ≤ x₀ q) → ∀ i, b i ≤ fdot (a i) x₀) ∧
      (∀ x, (∀ i, b i ≤ fdot (a i) x) → ∀ q, ε ^ eexp H 0 ≤ x q) ∧
      (∀ x, (∀ i, b i - ε ^ eexp H 0 / 2 ≤ fdot (a i) x) → ∀ q, ε ^ eexp H 0 / 2 ≤ x q) ∧
      (∀ σ, 0 ≤ σ → σ ≤ ε ^ eexp H 0 / 2 → ∀ x : Fin n → ℝ, (∀ q, 0 < x q) → (∀ q, x q ≤ M) →
        (∀ i, b i - σ ≤ fdot (a i) x) → ∀ i, fdot (a i) x = b i - σ →
        ∀ h ∈ H, fdot (a i) h < 0 → δ ≤ ∑ q, h q * log (x q))
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the start point
    intro μ hμ hsmallμ x₀ hμ' i
    have hx₀ : ∀ q, 0 < x₀ q := fun q => lt_of_lt_of_le hμ (hμ' q)
    obtain ⟨m, k, pm⟩ := i
    rw [hadot]
    have hm := m.isLt
    have hP := hPof ⟨m, k, pm⟩
    simp only at hP ⊢
    rw [facetN, fdot_levelNormal m hm _ rfl]
    have hz0 : μ ≤ tailZ n m (x₀ ∘ pm.symm) 0 := by
      simp only [tailZ, dif_pos (show n - 1 - (m:ℕ) + 0 < n by omega)]; exact hμ' _
    have hsum : 0 ≤ ∑ l ∈ range m, leafB (pk H m).t 0 (fun _ => 1) (Pof ⟨m, k, pm⟩) l *
        tailZ n m (x₀ ∘ pm.symm) (l + 1) := by
      refine sum_nonneg fun l hl => mul_nonneg ?_ (tailZ_pos (fun q => hx₀ _) _ _).le
      exact (leafB_mem _ _ 0 _ (pk H m).hGP _ hP l (by omega) (by simp at hl; omega)).1
    have hpD := (pk H m).hpD _ (rpow_pos_of_pos hε0 _) (hc1 m hm) _ hP
    have hsmall := hsmallμ m hm
    simp only [b, facetB]
    linarith
  · -- the floor
    intro x hx q
    have hnq : n - 1 < n := by omega
    set τ := Equiv.swap q ⟨n - 1, hnq⟩
    have hk : 0 < (paths (pk H 0).t).length := by rw [hlevel0]; simp
    have := hx ⟨⟨0, hn⟩, ⟨0, hk⟩, τ⟩
    rw [hadot] at this
    have hP0 : Pof ⟨⟨0, hn⟩, ⟨0, hk⟩, τ⟩ = [] := by
      simp only [Pof]; simp [hlevel0]
    simp only [b, hP0] at this
    rw [facetN, fdot_levelNormal 0 (by omega) _ rfl, range_zero, sum_empty, add_zero] at this
    have ht0 : (pk H 0).t = BTree.leaf := btree_zero_eq_leaf _
    have hB : facetB H ε 0 [] = ε ^ eexp H 0 := by
      simp only [facetB]; rw [ht0]; simp [pathD]
    rw [hB] at this
    have htz : tailZ n 0 (x ∘ τ.symm) 0 = x q := by
      simp only [tailZ, dif_pos (show n - 1 - 0 + 0 < n by omega), Function.comp_apply]
      have : (⟨n - 1 - 0 + 0, by omega⟩ : Fin n) = ⟨n - 1, hnq⟩ := Fin.ext (by simp)
      rw [this, Equiv.symm_swap, Equiv.swap_apply_right]
    rw [htz] at this; exact this
  · -- the floor in the band
    intro x hx q
    have hnq : n - 1 < n := by omega
    set τ := Equiv.swap q ⟨n - 1, hnq⟩
    have hk : 0 < (paths (pk H 0).t).length := by rw [hlevel0]; simp
    have := hx ⟨⟨0, hn⟩, ⟨0, hk⟩, τ⟩
    rw [hadot] at this
    have hP0 : Pof ⟨⟨0, hn⟩, ⟨0, hk⟩, τ⟩ = [] := by
      simp only [Pof]; simp [hlevel0]
    simp only [b, hP0] at this
    rw [facetN, fdot_levelNormal 0 (by omega) _ rfl, range_zero, sum_empty, add_zero] at this
    have ht0 : (pk H 0).t = BTree.leaf := btree_zero_eq_leaf _
    have hB : facetB H ε 0 [] = ε ^ eexp H 0 := by
      simp only [facetB]; rw [ht0]; simp [pathD]
    rw [hB] at this
    have htz : tailZ n 0 (x ∘ τ.symm) 0 = x q := by
      simp only [tailZ, dif_pos (show n - 1 - 0 + 0 < n by omega), Function.comp_apply]
      have : (⟨n - 1 - 0 + 0, by omega⟩ : Fin n) = ⟨n - 1, hnq⟩ := Fin.ext (by simp)
      rw [this, Equiv.symm_swap, Equiv.swap_apply_right]
    rw [htz] at this; linarith
  · -- validity
    intro σ hσ0 hσ x hxpos hxM hxfac i hact h hh hneg
    obtain ⟨m, k, pm⟩ := i
    have hm := m.isLt
    set P := Pof ⟨m, k, pm⟩ with hPdef
    have hP : IsPath (pk H m).t P := hPof ⟨m, k, pm⟩
    set N := facetN H m P with hNdef
    set y := x ∘ pm.symm with hydef
    have hval : ∀ (g : Equiv.Perm (Fin n)) (m' : Fin n) (P' : List ℕ),
        IsPath (pk H m').t P' → facetB H ε m' P' - σ ≤ fdot (facetN H m' P') (x ∘ g) := by
      intro g m' P' hP'
      obtain ⟨k', hk'⟩ := hidx m' P' hP'
      have := hxfac ⟨m', k', g.symm⟩
      rw [hadot] at this
      simp only [b, Pof, hk', Equiv.symm_symm] at this
      exact this
    have hyval : fdot N y = facetB H ε m P - σ := by
      have := hact; rw [hadot] at this; simpa [b, a] using this
    have hmin : ∀ ρ : Equiv.Perm (Fin n), fdot N y ≤ fdot N (y ∘ ρ) := by
      intro ρ
      rw [hyval]
      have := hval (ρ.trans pm.symm) m P hP
      have hcomp : y ∘ ρ = x ∘ ⇑(ρ.trans pm.symm) := by funext q; simp [hydef]
      rw [hcomp]; exact this
    set V : (Fin n → ℝ) → Prop := fun y' => ∀ h ∈ H, fdot N h < 0 →
      δ ≤ ∑ q, h q * log (y' q) with hVdef
    have hNmono := facetN_monotone H m P hP
    have hVswap : ∀ (y' : Fin n → ℝ) (q r : Fin n), N q = N r →
        (V (y' ∘ Equiv.swap q r) ↔ V y') := by
      intro y' q r hqr
      set τ := Equiv.swap q r
      have hNτ : N ∘ τ = N := by
        funext a
        simp only [Function.comp_apply, τ]
        rcases eq_or_ne a q with rfl | haq
        · rw [Equiv.swap_apply_left]; exact hqr.symm
        · rcases eq_or_ne a r with rfl | har
          · rw [Equiv.swap_apply_right]; exact hqr
          · rw [Equiv.swap_apply_of_ne_of_ne haq har]
      have hdot : ∀ h', fdot N (h' ∘ τ) = fdot N h' := by
        intro h'; rw [fdot_comp_perm, Equiv.symm_swap, hNτ]
      constructor
      · intro hV h' hh' hneg'
        have h1 := hV (h' ∘ τ) (hsym h' hh' τ) (by rw [hdot]; exact hneg')
        rw [sum_log_comp_perm] at h1
        have : (h' ∘ τ) ∘ ⇑τ.symm = h' := by funext a; simp
        rwa [this] at h1
      · intro hV h' hh' hneg'
        rw [sum_log_comp_perm]
        exact hV _ (hsym h' hh' τ.symm) (by
          rw [Equiv.symm_swap]; rw [hdot]; exact hneg')
    have hsorted : ∀ ρ : Equiv.Perm (Fin n), Antitone (y ∘ ρ) → fdot N (y ∘ ρ) = fdot N y →
        V (y ∘ ρ) := by
      intro ρ hanti heq
      have hcomp : y ∘ ρ = x ∘ ⇑(ρ.trans pm.symm) := by funext q; simp [hydef]
      rw [hcomp] at hanti heq ⊢
      exact sorted_valid H hM hε0 hε1 hc1 hc2 hc3 hc4 hc4' hσ0 hσ _ hanti
        (fun q => hxpos _) (fun q => hxM _)
        (fun m' hm' P' hP' => hval _ ⟨m', hm'⟩ P' hP') m hm P hP (by rw [heq, hyval])
    have hVy := sort_reduce N hNmono V hVswap y hmin hsorted 1 (by simp)
    have hVy' : V y := by simpa using hVy
    -- back to `x`
    have hdotπ : fdot (a ⟨m, k, pm⟩) h = fdot N (h ∘ pm.symm) := by
      rw [fdot_comp_perm]; simp [a, hNdef, hPdef]
    rw [hdotπ] at hneg
    have := hVy' (h ∘ pm.symm) (hsym h hh _) hneg
    have hre : ∑ q, (h ∘ pm.symm) q * log (y q) = ∑ q, h q * log (x q) :=
      Equiv.sum_comp pm.symm (fun q => h q * log (x q))
    linarith [hre]



/-- **Zero-separating region with normals independent of the slack.** The finite family of facet
normals `a` depends only on `H` (and the dimension); the slack `δ`, the box size `M` and the start
point `x₀` only move the offsets `b`.  This is the form needed when the field condition requires
the slack to dominate a constant computed from the normals themselves (endotactic networks). -/
theorem exists_zsh_uniform (hn : 1 ≤ n) (H : Finset (Fin n → ℝ))
    (hsym : ∀ h ∈ H, ∀ ρ : Equiv.Perm (Fin n), h ∘ ρ ∈ H) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (a : ι → Fin n → ℝ),
    ∀ (δ M : ℝ), 1 ≤ M → ∀ (x₀ : Fin n → ℝ), (∀ q, 0 < x₀ q) →
    ∃ (b : ι → ℝ) (R' η : ℝ),
      0 < R' ∧ 0 < η ∧
      (∀ i, b i ≤ fdot (a i) x₀) ∧
      (∀ x, (∀ i, b i ≤ fdot (a i) x) → ∀ q, η ≤ x q) ∧
      (∀ x, (∀ i, b i - R' ≤ fdot (a i) x) → ∀ q, R' ≤ x q) ∧
      (∀ σ, 0 ≤ σ → σ ≤ R' → ∀ x : Fin n → ℝ, (∀ q, 0 < x q) → (∀ q, x q ≤ M) →
        (∀ i, b i - σ ≤ fdot (a i) x) → ∀ i, fdot (a i) x = b i - σ →
        ∀ h ∈ H, fdot (a i) h < 0 → δ ≤ ∑ q, h q * log (x q)) := by
  obtain ⟨ι, hF, hN, a, bf, -, -, -, h⟩ := exists_zsh_family hn H hsym
  refine ⟨ι, hF, hN, a, fun δ M hM x₀ hx₀ => ?_⟩
  obtain ⟨μ, hμ, _, hμle⟩ := exists_pos_le_of_forall_pos (List.finRange n) x₀
    (fun q _ => hx₀ q)
  have hμ' : ∀ q, μ ≤ x₀ q := fun q => hμle q (List.mem_finRange q)
  obtain ⟨ε₁, hε₁, hP⟩ := h δ M hM
  have hsm : ∀ᶠ ε in 𝓝[>] (0:ℝ), (0 < ε ∧ ε < ε₁) ∧ ∀ m ∈ range n, ε ^ eexp H m < μ / 2 := by
    have h1 : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < ε ∧ ε < ε₁ := by
      filter_upwards [Ioo_mem_nhdsGT hε₁] with ε hε using hε
    refine h1.and ?_
    rw [Filter.eventually_all_finset]
    exact fun m _ => eventually_small (eexp_pos H m) (by positivity)
  obtain ⟨ε, ⟨hε0, hεlt⟩, hεP⟩ := hsm.exists
  obtain ⟨hs, hfl, hb, hv⟩ := hP ε hε0 hεlt
  have hη := rpow_pos_of_pos hε0 (eexp H 0)
  exact ⟨bf ε, ε ^ eexp H 0 / 2, ε ^ eexp H 0, by positivity, hη,
    hs μ hμ (fun m hm => hεP m (mem_range.mpr hm)) x₀ hμ', hfl, hb, hv⟩

theorem exists_zsh (hn : 1 ≤ n) (H : Finset (Fin n → ℝ))
    (hsym : ∀ h ∈ H, ∀ ρ : Equiv.Perm (Fin n), h ∘ ρ ∈ H)
    (δ M : ℝ) (hM : 1 ≤ M) (x₀ : Fin n → ℝ) (hx₀ : ∀ q, 0 < x₀ q) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (a : ι → Fin n → ℝ) (b : ι → ℝ) (R' η : ℝ),
      0 < R' ∧ 0 < η ∧
      (∀ i, b i ≤ fdot (a i) x₀) ∧
      (∀ x, (∀ i, b i ≤ fdot (a i) x) → ∀ q, η ≤ x q) ∧
      (∀ σ, 0 ≤ σ → σ ≤ R' → ∀ x : Fin n → ℝ, (∀ q, 0 < x q) → (∀ q, x q ≤ M) →
        (∀ i, b i - σ ≤ fdot (a i) x) → ∀ i, fdot (a i) x = b i - σ →
        ∀ h ∈ H, fdot (a i) h < 0 → δ ≤ ∑ q, h q * log (x q)) := by
  obtain ⟨ι, hF, hN, a, h⟩ := exists_zsh_uniform hn H hsym
  obtain ⟨b, R', η, h1, h2, h3, h4, -, h5⟩ := h δ M hM x₀ hx₀
  exact ⟨ι, hF, hN, a, b, R', η, h1, h2, h3, h4, h5⟩

end Persistence
end CRNT
