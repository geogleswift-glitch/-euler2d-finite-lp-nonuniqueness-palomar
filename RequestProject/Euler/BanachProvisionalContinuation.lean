module

public import RequestProject.Euler.BanachDirectedTrajectoryGluing

/-! A genuine continuation principle for provisional trajectories.
Compatibility constructs a path up to the supremum; a proved endpoint
extension rules out a stopping time before the prescribed horizon. -/

@[expose] public section

set_option maxHeartbeats 3500000

noncomputable section

open Set Filter Topology

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure IsBanachTrajectoryOn (f : ℝ → E → E) (U : Set E) (z : E)
    (T : ℝ) (X : ℝ → E) : Prop where
  initial : X 0 = z
  continuous : ContinuousOn X (Icc (0 : ℝ) T)
  hasDerivAt : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt X (f t (X t)) t
  mem : ∀ t ∈ Icc (0 : ℝ) T, X t ∈ U

theorem IsBanachTrajectoryOn.mono {f : ℝ → E → E} {U : Set E} {z : E}
    {A B : ℝ} {X : ℝ → E} (hX : IsBanachTrajectoryOn f U z A X) (hBA : B ≤ A) :
    IsBanachTrajectoryOn f U z B X :=
  ⟨hX.initial, hX.continuous.mono (fun _ ht => ⟨ht.1, ht.2.trans hBA⟩),
    fun t ht => hX.hasDerivAt t ⟨ht.1, ht.2.trans hBA⟩,
    fun t ht => hX.mem t ⟨ht.1, ht.2.trans hBA⟩⟩

theorem exists_banachTrajectory_of_no_finite_stopping
    (f : ℝ → E → E) (U : Set E) (z : E) (H : ℝ)
    (hstart : ∃ T > 0, T ≤ H ∧ ∃ X : ℝ → E, IsBanachTrajectoryOn f U z T X)
    (huniq : ∀ {A B : ℝ} {X Y : ℝ → E},
      IsBanachTrajectoryOn f U z A X → IsBanachTrajectoryOn f U z B Y →
        EqOn X Y (Icc (0 : ℝ) (min A B)))
    (hcontinue : ∀ D, 0 < D → D ≤ H → ∀ α : ℝ → E,
      α 0 = z → (∀ t ∈ Ico (0 : ℝ) D, HasDerivAt α (f t (α t)) t) →
      (∀ t ∈ Ico (0 : ℝ) D, α t ∈ U) →
      ∃ δ > 0, ∃ Y : ℝ → E, IsBanachTrajectoryOn f U z (D + δ) Y) :
    ∃ X : ℝ → E, IsBanachTrajectoryOn f U z H X := by
  classical
  let S : Set ℝ := {T | 0 < T ∧ T ≤ H ∧ ∃ X : ℝ → E, IsBanachTrajectoryOn f U z T X}
  obtain ⟨T₀, hT₀, hT₀H, X₀, hX₀⟩ := hstart
  have hT₀S : T₀ ∈ S := ⟨hT₀, hT₀H, X₀, hX₀⟩
  have hSne : S.Nonempty := ⟨T₀, hT₀S⟩
  have hSbd : BddAbove S := ⟨H, fun _ h => h.2.1⟩
  let D := sSup S
  have hD : 0 < D := hT₀.trans_le (le_csSup hSbd hT₀S)
  have hDH : D ≤ H := csSup_le hSne (fun _ h => h.2.1)
  letI : Nonempty S := ⟨⟨T₀, hT₀S⟩⟩
  let X : S → ℝ → E := fun i => i.property.2.2.choose
  have hX (i : S) : IsBanachTrajectoryOn f U z i.val (X i) := i.property.2.2.choose_spec
  have hcover : ∀ t < D, ∃ i : S, t < i.val := by
    intro t ht
    obtain ⟨u, huS, htu⟩ := exists_lt_of_lt_csSup hSne ht
    exact ⟨⟨u, huS⟩, htu⟩
  obtain ⟨α, hα0, hαd, _, hselect⟩ :=
    exists_glued_trajectory_before_sup hD (fun i : S => i.val) (fun i => i.property.1) X hcover
      (fun i => (hX i).initial) (fun i => (hX i).hasDerivAt)
      (fun i j => huniq (hX i) (hX j))
  have hαU (t : ℝ) (ht : t ∈ Ico (0 : ℝ) D) : α t ∈ U := by
    obtain ⟨i, hti, heq⟩ := hselect t ht
    rw [heq]
    exact (hX i).mem t ⟨ht.1, hti.le⟩
  obtain ⟨δ, hδ, Y, hY⟩ := hcontinue D hD hDH α hα0 hαd hαU
  have hHD : H ≤ D := by
    apply le_of_not_gt
    intro hlt
    let B := min H (D + δ)
    have hDB : D < B := lt_min hlt (by linarith)
    have hBS : B ∈ S :=
      ⟨hD.trans hDB, min_le_left _ _, Y, hY.mono (min_le_right _ _)⟩
    exact (not_lt_of_ge (le_csSup hSbd hBS)) hDB
  exact ⟨Y, hY.mono (hHD.trans (le_add_of_nonneg_right hδ.le))⟩

end Euler2D

end
