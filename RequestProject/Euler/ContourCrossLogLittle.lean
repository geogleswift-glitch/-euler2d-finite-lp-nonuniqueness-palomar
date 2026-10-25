module

public import RequestProject.Euler.ContourCrossLogLocus

/-! # Genuine little-space preservation of the separated cross-interaction

Both actual inputs are approximated by genuine smooth contours in their
real Banach norms. Separation is retained quantitatively, and the proved
C¹ Hölder local Lipschitz estimate passes the actual outputs to the closed
little subspace.
-/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) crossLittleC1_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) :=
  Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

local instance (priority := 2000) crossLittleC1_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) :=
  Submodule.normedSpace (contourC1GraphSubmodule γ)

local instance (priority := 2000) crossLittle_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) :=
  Submodule.normedAddCommGroup (LittleContourSpace γ)

theorem LittleContourSpace.exists_smooth_sequence_with_norm_error {γ : ℝ≥0}
    (Z : LittleContourSpace γ) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℕ → LittleContourSpace γ,
      (∀ n, ContDiff ℝ ∞ (LittleContourSpace.lift γ (u n))) ∧
      (∀ n, ‖u n - Z‖ < min ε (1 / ((n : ℝ) + 1))) ∧ Tendsto u atTop (𝓝 Z) := by
  have happrox (n : ℕ) : ∃ g : ContourC1Space γ,
      ContDiff ℝ ∞ (ContourC1Space.lift γ g) ∧ ‖Z.val - g‖ < min ε (1 / ((n : ℝ) + 1)) :=
    LittleContourSpace.exists_smooth_approximation Z (lt_min hε (by positivity))
  choose g hs hg using happrox
  let u : ℕ → LittleContourSpace γ := fun n => LittleContourSpace.ofSmooth γ (g n) (hs n)
  have herr (n : ℕ) : ‖u n - Z‖ < min ε (1 / ((n : ℝ) + 1)) := by
    change ‖g n - Z.val‖ < _
    rw [norm_sub_rev]
    exact hg n
  have hlim : Tendsto u atTop (𝓝 Z) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => (herr n).le.trans (min_le_right _ _))
      tendsto_one_div_add_atTop_nhds_zero_nat
  exact ⟨u, hs, herr, hlim⟩

theorem contourCrossLogC1_mem_little {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : LittleContourSpace γ) {σ : ℝ} (hσ : 0 < σ) (hsep : ContourCrossSeparated Z.val W.val σ) :
    contourCrossLogC1 hγ1 Z.val W.val hσ hsep ∈ (LittleContourSpace γ : Set (ContourC1Space γ)) := by
  obtain ⟨u, hsu, hEu, hlimu⟩ := LittleContourSpace.exists_smooth_sequence_with_norm_error Z
    (show 0 < σ / 8 by positivity)
  obtain ⟨v, hsv, hEv, hlimv⟩ := LittleContourSpace.exists_smooth_sequence_with_norm_error W
    (show 0 < σ / 8 by positivity)
  have hnsep (n : ℕ) : ContourCrossSeparated (u n).val (v n).val (σ / 2) := by
    apply contourCrossSeparated_of_norm_sub_le Z.val W.val (u n).val (v n).val hsep
    have hu : ‖Z.val - (u n).val‖ < σ / 8 := by
      rw [norm_sub_rev]
      exact (hEu n).trans_le (min_le_left _ _)
    have hv : ‖W.val - (v n).val‖ < σ / 8 := by
      rw [norm_sub_rev]
      exact (hEv n).trans_le (min_le_left _ _)
    linarith
  let p : ℕ → PositiveSeparatedContourPair γ := fun n =>
    ⟨((u n).val, (v n).val), ⟨σ / 2, half_pos hσ, hnsep n⟩⟩
  let p₀ : PositiveSeparatedContourPair γ := ⟨(Z.val, W.val), ⟨σ, hσ, hsep⟩⟩
  have huval : Tendsto (fun n => (u n).val) atTop (𝓝 Z.val) :=
    ((LittleContourSpace.inclusion γ).continuous.tendsto Z).comp hlimu
  have hvval : Tendsto (fun n => (v n).val) atTop (𝓝 W.val) :=
    ((LittleContourSpace.inclusion γ).continuous.tendsto W).comp hlimv
  have hp : Tendsto p atTop (𝓝 p₀) := tendsto_subtype_rng.mpr (huval.prodMk_nhds hvval)
  have hF : Tendsto (fun n => contourCrossLogC1OnLocus hγ1 (p n)) atTop
      (𝓝 (contourCrossLogC1OnLocus hγ1 p₀)) :=
    ((locallyLipschitz_contourCrossLogC1OnLocus hγ1).continuous.tendsto p₀).comp hp
  rw [contourCrossLogC1OnLocus_eq hγ1 p₀ hσ hsep] at hF
  apply (isClosed_littleContourSpace γ).mem_of_tendsto hF
  apply Eventually.of_forall
  intro n
  have hs : ContDiff ℝ ∞ (ContourC1Space.lift γ (contourCrossLogC1OnLocus hγ1 (p n))) := by
    rw [lift_contourCrossLogC1OnLocus]
    exact contDiff_contourCrossLogIntegral (hsu n) (hsv n) (contDiff_infty_iff_deriv.mp (hsv n)).2
      (half_pos hσ) (fun θ φ _ => hnsep n (θ : ContourCircle) (φ : ContourCircle))
  exact (LittleContourSpace.ofSmooth γ (contourCrossLogC1OnLocus hγ1 (p n)) hs).property

def contourCrossLogLittle {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : LittleContourSpace γ) {σ : ℝ} (hσ : 0 < σ) (hsep : ContourCrossSeparated Z.val W.val σ) :
    LittleContourSpace γ :=
  ⟨contourCrossLogC1 hγ1 Z.val W.val hσ hsep, contourCrossLogC1_mem_little hγ1 Z W hσ hsep⟩

@[simp] theorem inclusion_contourCrossLogLittle {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : LittleContourSpace γ) {σ : ℝ} (hσ : 0 < σ) (hsep : ContourCrossSeparated Z.val W.val σ) :
    LittleContourSpace.inclusion γ (contourCrossLogLittle hγ1 Z W hσ hsep) =
      contourCrossLogC1 hγ1 Z.val W.val hσ hsep := rfl

@[simp] theorem lift_contourCrossLogLittle {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (Z W : LittleContourSpace γ) {σ : ℝ} (hσ : 0 < σ) (hsep : ContourCrossSeparated Z.val W.val σ) :
    LittleContourSpace.lift γ (contourCrossLogLittle hγ1 Z W hσ hsep) =
      contourC1CrossLogIntegral Z.val W.val := rfl

abbrev PositiveSeparatedLittleContourPair (γ : ℝ≥0) :=
  {p : LittleContourSpace γ × LittleContourSpace γ // ∃ σ > 0, ContourCrossSeparated p.1.val p.2.val σ}

def separatedLittlePairToC1 {γ : ℝ≥0} (p : PositiveSeparatedLittleContourPair γ) :
    PositiveSeparatedContourPair γ := ⟨(p.val.1.val, p.val.2.val), p.property⟩

theorem isometry_separatedLittlePairToC1 (γ : ℝ≥0) :
    Isometry (separatedLittlePairToC1 (γ := γ)) := by
  intro p q
  rfl

def contourCrossLogLittleOnLocus {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (p : PositiveSeparatedLittleContourPair γ) : LittleContourSpace γ :=
  contourCrossLogLittle hγ1 p.val.1 p.val.2 p.property.choose_spec.1 p.property.choose_spec.2

@[simp] theorem inclusion_contourCrossLogLittleOnLocus {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (p : PositiveSeparatedLittleContourPair γ) :
    LittleContourSpace.inclusion γ (contourCrossLogLittleOnLocus hγ1 p) =
      contourCrossLogC1OnLocus hγ1 (separatedLittlePairToC1 p) := rfl

@[simp] theorem lift_contourCrossLogLittleOnLocus {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (p : PositiveSeparatedLittleContourPair γ) :
    LittleContourSpace.lift γ (contourCrossLogLittleOnLocus hγ1 p) =
      contourC1CrossLogIntegral p.val.1.val p.val.2.val := rfl

theorem locallyLipschitz_contourCrossLogLittleOnLocus {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1) :
    LocallyLipschitz (contourCrossLogLittleOnLocus hγ1) := by
  have hc : LocallyLipschitz (fun p : PositiveSeparatedLittleContourPair γ =>
      contourCrossLogC1OnLocus hγ1 (separatedLittlePairToC1 p)) :=
    (locallyLipschitz_contourCrossLogC1OnLocus hγ1).comp
      (isometry_separatedLittlePairToC1 γ).lipschitz.locallyLipschitz
  intro p
  obtain ⟨K, U, hU, hLip⟩ := hc p
  refine ⟨K, U, hU, ?_⟩
  intro q hq r hr
  exact hLip hq hr

end Euler2D

end
