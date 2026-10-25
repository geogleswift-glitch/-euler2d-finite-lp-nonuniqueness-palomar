module

public import RequestProject.Euler.BanachProvisionalContinuation

/-! A provisional bootstrap is needed only while its target event has
not occurred. Local existence and uniqueness together with genuine
endpoint continuation on such paths produce either an actual event
or an actual trajectory through the prescribed horizon. -/

@[expose] public section

set_option maxHeartbeats 3500000

noncomputable section

open Set Filter Topology

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_banachTrajectory_or_event
    (f : ℝ → E → E) (U : Set E) (z : E) (H : ℝ) (event : ℝ → E → Prop)
    (hstart : ∃ T > 0, T ≤ H ∧ ∃ X : ℝ → E, IsBanachTrajectoryOn f U z T X)
    (huniq : ∀ {A B : ℝ} {X Y : ℝ → E},
      IsBanachTrajectoryOn f U z A X → IsBanachTrajectoryOn f U z B Y →
        EqOn X Y (Icc (0 : ℝ) (min A B)))
    (hcontinue : ∀ D, 0 < D → D ≤ H → ∀ α : ℝ → E,
      α 0 = z → (∀ t ∈ Ico (0 : ℝ) D, HasDerivAt α (f t (α t)) t) →
      (∀ t ∈ Ico (0 : ℝ) D, α t ∈ U) →
      (∀ t ∈ Ico (0 : ℝ) D, ¬ event t (α t)) →
      ∃ δ > 0, ∃ Y : ℝ → E, IsBanachTrajectoryOn f U z (D + δ) Y) :
    (∃ X : ℝ → E, IsBanachTrajectoryOn f U z H X) ∨
      ∃ t ∈ Icc (0 : ℝ) H, ∃ X : ℝ → E,
        IsBanachTrajectoryOn f U z t X ∧ event t (X t) := by
  classical
  by_cases hevent : ∃ t ∈ Icc (0 : ℝ) H, ∃ X : ℝ → E,
      IsBanachTrajectoryOn f U z t X ∧ event t (X t)
  · exact Or.inr hevent
  left
  apply exists_banachTrajectory_of_no_finite_stopping f U z H hstart huniq
  intro D hD hDH α hα0 hαd hαmem
  apply hcontinue D hD hDH α hα0 hαd hαmem
  intro t ht htEvent
  let B := (t + D) / 2
  have hB : 0 < B := by dsimp only [B]; linarith [ht.1]
  have hBD : B < D := by dsimp only [B]; linarith [ht.2]
  have htB : t ≤ B := by dsimp only [B]; linarith [ht.2]
  have hpath : IsBanachTrajectoryOn f U z B α := by
    refine ⟨hα0, ?_, ?_, ?_⟩
    · exact fun s hs => (hαd s ⟨hs.1, hs.2.trans_lt hBD⟩).continuousAt.continuousWithinAt
    · exact fun s hs => hαd s ⟨hs.1, hs.2.trans_lt hBD⟩
    · exact fun s hs => hαmem s ⟨hs.1, hs.2.trans_lt hBD⟩
  exact hevent ⟨t, ⟨ht.1, htB.trans (hBD.le.trans hDH)⟩, α, hpath.mono htB, htEvent⟩

end Euler2D

end
