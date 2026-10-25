module

public import RequestProject.Euler.BanachProvisionalContinuation
public import RequestProject.Euler.CircularFinitePhaseTubeContinuation
public import RequestProject.Euler.FinitePhaseForcedUniqueness

/-! Once genuine estimates put every provisional material solution
in the strict circular tube, its actual solution exists throughout the
prescribed horizon. The whole-time path is constructed, not assumed. -/

@[expose] public section

set_option maxHeartbeats 6000000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) circularControlledLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) circularControlledLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) circularControlledC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) circularControlledC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

theorem exists_finiteCircular_trajectory_of_provisional_tube {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R ρ η a H : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hρa : ρ ≤ cellA / 4)
    (hη : 0 ≤ η) (hηa : η ≤ cellA / 16) (hηgap : η ≤ (1 - cellA) / 16)
    (ha : 0 < a) (hsize : R * (‖littleCircularReference hγ hγ1‖ + η) < a / 4)
    (hH : 0 < H) {N : ℕ} (g : FiniteCircularIndex N → ℝ)
    (E : ℝ → (FiniteCircularIndex N → LittleContourSpace γ) →
      FiniteCircularIndex N → LittleContourSpace γ) {K : ℝ≥0}
    (hELip : ∀ t, LipschitzOnWith K (E t) (ball 0 (a / 4)))
    (hEc : ∀ W ∈ ball 0 (a / 4), Continuous (fun t => E t W)) :
    let f := fun t Z =>
      finiteContourPhaseFieldTotal hγ hγ1 (finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceRadius R ρ) (finiteCircularInterfaceRadius_pos hR hρ)
        (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) g Z + E t Z
    let U : Set (FiniteCircularIndex N → LittleContourSpace γ) := {Z |
      IsPhaseAdmissibleLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceRadius R ρ) Z ∧ ‖Z‖ < a / 4 ∧
      IsQuarterPhaseLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceRadius R ρ) Z}
    ∀ Zinit ∈ U,
      (∀ D, 0 < D → D ≤ H → ∀ X : ℝ → FiniteCircularIndex N → LittleContourSpace γ,
        IsBanachTrajectoryOn f U Zinit D X → ∀ t ∈ Icc (0 : ℝ) D,
        ∃ b : FiniteCircularIndex N → ℝ, ∀ p,
          ‖contourParameterShiftC1 (b p) (X t p).val - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤
            η * radScale R ρ p.1) →
      ∃ X : ℝ → FiniteCircularIndex N → LittleContourSpace γ,
        IsBanachTrajectoryOn f U Zinit H X := by
  dsimp only
  intro Zinit hinit hTube
  let f : ℝ → (FiniteCircularIndex N → LittleContourSpace γ) →
      FiniteCircularIndex N → LittleContourSpace γ := fun t Z =>
    finiteContourPhaseFieldTotal hγ hγ1 (finiteCircularReferenceC1 hγ hγ1 R ρ)
      (finiteCircularInterfaceRadius R ρ) (finiteCircularInterfaceRadius_pos hR hρ)
      (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) g Z + E t Z
  let U : Set (FiniteCircularIndex N → LittleContourSpace γ) := {Z |
    IsPhaseAdmissibleLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
      (finiteCircularInterfaceRadius R ρ) Z ∧ ‖Z‖ < a / 4 ∧
    IsQuarterPhaseLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
      (finiteCircularInterfaceRadius R ρ) Z}
  change Zinit ∈ U at hinit
  change ∃ X, IsBanachTrajectoryOn f U Zinit H X
  have hstart : ∃ T > 0, T ≤ H ∧ ∃ X : ℝ → FiniteCircularIndex N → LittleContourSpace γ,
      IsBanachTrajectoryOn f U Zinit T X := by
    let V : Set (FiniteCircularIndex N → LittleContourSpace γ) := ball 0 (a / 4) ∩
      {Z | IsQuarterPhaseLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceRadius R ρ) Z}
    have hV : V ∈ 𝓝 Zinit := inter_mem
      (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hinit.2.1))
      ((isOpen_quarterPhaseLittleContourFamilies _ _).mem_nhds hinit.2.2)
    obtain ⟨r, hr, T, hT, hTH, X, hX, _⟩ :=
      exists_finitePhase_time_restart hγ hγ1 (finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceRadius R ρ) (finiteCircularInterfaceRadius_pos hR hρ)
        (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) g Zinit hinit.1 E hH hV
        (fun t => (hELip t).mono inter_subset_left) (fun W hW => hEc W hW.1) 0
    have hball : Zinit ∈ ball Zinit r := mem_ball_self hr
    refine ⟨T, hT, hTH, X Zinit, hX.initial Zinit hball, hX.continuous Zinit hball, ?_, ?_⟩
    · intro t ht
      simpa only [zero_add] using hX.hasDerivAt Zinit hball t ht
    · intro t ht
      have hm := hX.mem Zinit hball t ht
      exact ⟨hm.1, mem_ball_zero_iff.mp hm.2.1, hm.2.2⟩
  have huniq {A B : ℝ} {X Y : ℝ → FiniteCircularIndex N → LittleContourSpace γ}
      (hX : IsBanachTrajectoryOn f U Zinit A X) (hY : IsBanachTrajectoryOn f U Zinit B Y) :
      EqOn X Y (Icc (0 : ℝ) (min A B)) := by
    have hx := hX.mono (min_le_left A B)
    have hy := hY.mono (min_le_right A B)
    exact eqOn_of_finitePhase_forcedODE hγ hγ1 (finiteCircularReferenceC1 hγ hγ1 R ρ)
      (finiteCircularInterfaceRadius R ρ) (finiteCircularInterfaceRadius_pos hR hρ)
      (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) g E hELip hx.continuous hy.continuous
      (fun t ht => ⟨(hx.mem t ht).1, (hx.mem t ht).2.1⟩)
      (fun t ht => ⟨(hy.mem t ht).1, (hy.mem t ht).2.1⟩)
      (fun t ht => hx.hasDerivAt t ⟨ht.1, ht.2.le⟩)
      (fun t ht => hy.hasDerivAt t ⟨ht.1, ht.2.le⟩) (hx.initial.trans hy.initial.symm)
  apply exists_banachTrajectory_of_no_finite_stopping f U Zinit H hstart huniq
  intro D hD hDH α hα0 hαd hαmem
  have htube (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) D) :
      ∃ b : FiniteCircularIndex N → ℝ, ∀ p,
        ‖contourParameterShiftC1 (b p) (α t p).val - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤
          η * radScale R ρ p.1 := by
    let B := (t + D) / 2
    have hB : 0 < B := by dsimp only [B]; linarith [ht.1]
    have hBD : B < D := by dsimp only [B]; linarith [ht.2]
    have htB : t ≤ B := by dsimp only [B]; linarith [ht.2]
    have hpath : IsBanachTrajectoryOn f U Zinit B α := by
      refine ⟨hα0, ?_, ?_, ?_⟩
      · exact fun s hs => (hαd s ⟨hs.1, hs.2.trans_lt hBD⟩).continuousAt.continuousWithinAt
      · exact fun s hs => hαd s ⟨hs.1, hs.2.trans_lt hBD⟩
      · exact fun s hs => hαmem s ⟨hs.1, hs.2.trans_lt hBD⟩
    exact hTube B hB (hBD.le.trans hDH) α hpath t ⟨ht.1.le, htB⟩
  obtain ⟨δ, hδ, _, Y, hagree, hYc, hYd, hYmem, _⟩ :=
    exists_finiteCircular_phase_tube_continuation hγ hγ1 hR hρ hρa hη hηa hηgap
      ha hsize hD (show (0 : ℝ) < 1 by norm_num) g E hELip hEc α hαd hαmem htube
  exact ⟨δ, hδ, Y, (hagree 0 ⟨le_rfl, hD⟩).trans hα0, hYc, hYd, hYmem⟩

end Euler2D

end
