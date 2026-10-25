module

public import RequestProject.Euler.CircularQuadraticGraphAncientSamples
public import RequestProject.Euler.BanachQuadraticGraphFlattening

/-! Both flattened remainders of the original single-period circular
return map satisfy the quantitative bounds used by capture. The graph
is the actual weighted fixed-point graph with its true quadratic
Lipschitz estimate; its C³ regularity is not assumed. -/

@[expose] public section

set_option maxHeartbeats 12000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) flattenedLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) flattenedLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) flattenedFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) flattenedTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
  Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) flattenedTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
  Submodule.normedSpace (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) flattenedTangent_continuousAdd (γ : ℝ≥0) :
    ContinuousAdd (CircularConstrainedTangentSpace γ) where
  continuous_add := by
    have h1 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.1.val) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.2.val) := continuous_subtype_val.comp continuous_snd
    exact (h1.add h2).subtype_mk _
local instance (priority := 2000) flattenedEndo_monoid (γ : ℝ≥0) :
    Monoid (CircularConstrainedTangentSpace γ →L[ℝ] CircularConstrainedTangentSpace γ) :=
  (ContinuousLinearMap.monoidWithZero :
    MonoidWithZero (CircularConstrainedTangentSpace γ →L[ℝ] CircularConstrainedTangentSpace γ)).toMonoid
local instance (priority := 2000) flattenedTangent_complete (γ : ℝ≥0) :
    CompleteSpace (CircularConstrainedTangentSpace γ) := circularConstrainedTangentSpace_complete γ

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedUnstableEmbeddingCLM circularConstrainedUnstableCoordinateCLM
  circularConstrainedChart circularConstraintProjectionToTangentCLM

theorem exists_circularConstrained_flattenedReturn_bounds {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R : ℝ} (hR : 0 < R)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hd : ContDiffAt ℝ 2 (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i))
    {rmax : ℝ} (hrmax : 0 < rmax) :
    ∃ r > 0, r ≤ rmax ∧ ∃ x : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ,
      IsLocalWeightedBackwardGraph
        (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)))
        (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r x ∧
      ∃ C > 0, ∃ s > 0, s ≤ r / 2 ∧ ∀ α w,
        circularConstrainedUnstableProjectionCLM hγ hγ1.le α = α →
        circularConstrainedUnstableProjectionCLM hγ hγ1.le w = 0 → ‖α‖ + ‖w‖ ≤ s →
        let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
        let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
        let L := fderiv ℝ F 0
        let g := fun v => x v 0 - v
        let z := α + g α + w
        ‖P (F z) - (-lamMult : ℝ) • α‖ ≤ C * (‖α‖ + ‖w‖) ^ 2 ∧
        ‖(F z - P (F z)) - g (P (F z)) - L w‖ ≤ C * (‖α‖ + ‖w‖) * ‖w‖ := by
  obtain ⟨r, hr, hrr, x, hg, _, H, hH, hquad, η, hη, hηr, hsingle⟩ :=
    exists_circularConstrained_quadraticBackwardGraph hγ hγ1 hR hX hd hfix harea hrmax
  let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
  let L := fderiv ℝ F 0
  let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  let g := fun v => x v 0 - v
  have hF : ContDiffAt ℝ 2 F 0 := contDiffAt_circularConstrainedReturnMap hγ hγ1 2 hd
  have hF0 : F 0 = 0 := circularConstrainedReturnMap_zero hγ hγ1 _ hfix
  have hfd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1) :=
    hd.differentiableAt (by norm_num)
  have hcomm : L.comp P = P.comp L :=
    circularConstrainedReturnMap_derivative_projection_commute hγ hγ1 hR hX hfd hfix harea
  have hg0 : g 0 = 0 := by
    have hx0 : x 0 0 = 0 := by
      simpa only [Pi.zero_apply] using
        congrArg (fun y : ℕ → CircularConstrainedTangentSpace γ => y 0) (hg.zero hr.le)
    change x 0 0 - 0 = 0
    simpa only [sub_zero] using hx0
  have hgker (α : CircularConstrainedTangentSpace γ) (hα : P α = α) (hαr : ‖α‖ ≤ r / 2) :
      P (g α) = 0 := by
    change P (x α 0 - α) = 0
    rw [P.map_sub, hg.coordinate α hα hαr, hα, sub_self]
  have hinv (α : CircularConstrainedTangentSpace γ) (hα : P α = α) (hαη : ‖α‖ ≤ η) :
      ‖P (F (α + g α))‖ ≤ r / 2 ∧ F (α + g α) - P (F (α + g α)) = g (P (F (α + g α))) := by
    have hga : α + g α = x α 0 := by dsimp only [g]; module
    rw [hga]
    have hh := hsingle α hα hαη
    refine ⟨hh.1, ?_⟩
    have hhead : x (P (F (x α 0))) 0 = F (x α 0) :=
      congrArg (fun y : ℕ → CircularConstrainedTangentSpace γ => y 0) hh.2
    change _ = x (P (F (x α 0))) 0 - P (F (x α 0))
    rw [hhead]
  obtain ⟨C, hC, s, hs, hsr, hbounds⟩ := exists_quadratic_graph_flattened_remainder_bound
    F hF hF0 L P rfl (circularConstrainedUnstableProjectionCLM_idempotent hγ hγ1.le)
    hcomm g hg0 hr hH hη hηr hgker hquad hinv
  refine ⟨r, hr, hrr, x, hg, C, hC, s, hs, hsr, ?_⟩
  intro α w hα hw hsize
  have hLα : L α = (-lamMult : ℝ) • α := by
    have heigen : L (P α) = (-lamMult : ℝ) • P α := by
      have hγle : γ ≤ 1 := by exact_mod_cast hγ1.le
      change L (circularConstrainedUnstableProjectionCLM hγ hγle α) =
        (-lamMult : ℝ) • circularConstrainedUnstableProjectionCLM hγ hγle α
      rw [circularConstrainedUnstableProjection_eq_embedding hγ hγle α]
      exact circularConstrainedReturnMap_derivative_unstable hγ hγ1 hR hX hfd _
    calc
      L α = L (P α) := congrArg L hα.symm
      _ = (-lamMult : ℝ) • P α := heigen
      _ = (-lamMult : ℝ) • α := congrArg (fun v => (-lamMult : ℝ) • v) hα
  simpa only [hLα] using hbounds α w hα hw hsize

theorem exists_actualCircular_flattenedReturn_bounds {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {rmax : ℝ} (hrmax : 0 < rmax) :
    ∃ R > 0, ∃ X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ,
      IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
        (ball (littleCircularReference hγ hγ1) R) period X ∧
      ContDiffAt ℝ 3 (fun W => X W period) (littleCircularReference hγ hγ1) ∧
      X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1 ∧
      (∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
        littleContourArea γ (X W period i) = littleContourArea γ (W i)) ∧
      ∃ r > 0, r ≤ rmax ∧ ∃ x : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ,
        IsLocalWeightedBackwardGraph
          (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)))
          (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r x ∧
        ∃ C > 0, ∃ s > 0, s ≤ r / 2 ∧ ∀ α w,
          circularConstrainedUnstableProjectionCLM hγ hγ1.le α = α →
          circularConstrainedUnstableProjectionCLM hγ hγ1.le w = 0 → ‖α‖ + ‖w‖ ≤ s →
          let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
          let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
          let L := fderiv ℝ F 0
          let g := fun v => x v 0 - v
          let z := α + g α + w
          ‖P (F z) - (-lamMult : ℝ) • α‖ ≤ C * (‖α‖ + ‖w‖) ^ 2 ∧
          ‖(F z - P (F z)) - g (P (F z)) - L w‖ ≤ C * (‖α‖ + ‖w‖) * ‖w‖ := by
  obtain ⟨R, hR, X, hX, hs, hfix, _, harea, _⟩ :=
    exists_circularContour_constrained_period_flow hγ hγ1 3
  have hp : period ∈ Icc (0 : ℝ) period := ⟨by unfold period; positivity, le_rfl⟩
  have hd3 : ContDiffAt ℝ 3 (fun W => X W period) (littleCircularReference hγ hγ1) :=
    (hs period hp).contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hR))
  have ha := fun W hW i => harea W hW period hp i
  exact ⟨R, hR, X, hX, hd3, hfix, ha,
    exists_circularConstrained_flattenedReturn_bounds hγ hγ1 hR hX
      (hd3.of_le (by norm_num)) hfix ha hrmax⟩

end Euler2D

end
