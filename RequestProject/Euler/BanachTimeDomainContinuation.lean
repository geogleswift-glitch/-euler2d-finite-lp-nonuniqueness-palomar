module

public import RequestProject.Euler.BanachDirectedTrajectoryGluing

/-! Continuation with a time-dependent validity domain. In particular,
actual support conditions can be retained at every provisional time;
the differential equation outside its physical domain is never used
to infer a material trajectory. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open Set Filter Topology

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure IsBanachTimeDomainTrajectoryOn (f : ℝ → E → E) (U : ℝ → Set E)
    (z : E) (T : ℝ) (X : ℝ → E) : Prop where
  initial : X 0 = z
  continuous : ContinuousOn X (Icc (0 : ℝ) T)
  hasDerivAt : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt X (f t (X t)) t
  mem : ∀ t ∈ Icc (0 : ℝ) T, X t ∈ U t

theorem IsBanachTimeDomainTrajectoryOn.mono {f : ℝ → E → E} {U : ℝ → Set E}
    {z : E} {A B : ℝ} {X : ℝ → E}
    (hX : IsBanachTimeDomainTrajectoryOn f U z A X) (hBA : B ≤ A) :
    IsBanachTimeDomainTrajectoryOn f U z B X :=
  ⟨hX.initial, hX.continuous.mono (fun _ ht => ⟨ht.1, ht.2.trans hBA⟩),
    fun t ht => hX.hasDerivAt t ⟨ht.1, ht.2.trans hBA⟩,
    fun t ht => hX.mem t ⟨ht.1, ht.2.trans hBA⟩⟩

theorem exists_banachTimeDomainTrajectory_of_no_finite_stopping
    (f : ℝ → E → E) (U : ℝ → Set E) (z : E) (H : ℝ)
    (hstart : ∃ T > 0, T ≤ H ∧ ∃ X : ℝ → E, IsBanachTimeDomainTrajectoryOn f U z T X)
    (huniq : ∀ {A B : ℝ} {X Y : ℝ → E},
      IsBanachTimeDomainTrajectoryOn f U z A X → IsBanachTimeDomainTrajectoryOn f U z B Y →
        EqOn X Y (Icc (0 : ℝ) (min A B)))
    (hcontinue : ∀ D, 0 < D → D ≤ H → ∀ α : ℝ → E,
      α 0 = z → (∀ t ∈ Ico (0 : ℝ) D, HasDerivAt α (f t (α t)) t) →
      (∀ t ∈ Ico (0 : ℝ) D, α t ∈ U t) →
      ∃ δ > 0, ∃ Y : ℝ → E, IsBanachTimeDomainTrajectoryOn f U z (D + δ) Y) :
    ∃ X : ℝ → E, IsBanachTimeDomainTrajectoryOn f U z H X := by
  classical
  let S : Set ℝ := {T | 0 < T ∧ T ≤ H ∧ ∃ X : ℝ → E, IsBanachTimeDomainTrajectoryOn f U z T X}
  obtain ⟨T₀, hT₀, hT₀H, X₀, hX₀⟩ := hstart
  have hT₀S : T₀ ∈ S := ⟨hT₀, hT₀H, X₀, hX₀⟩
  have hSne : S.Nonempty := ⟨T₀, hT₀S⟩
  have hSbd : BddAbove S := ⟨H, fun _ h => h.2.1⟩
  let D := sSup S
  have hD : 0 < D := hT₀.trans_le (le_csSup hSbd hT₀S)
  have hDH : D ≤ H := csSup_le hSne (fun _ h => h.2.1)
  letI : Nonempty S := ⟨⟨T₀, hT₀S⟩⟩
  let X : S → ℝ → E := fun i => i.property.2.2.choose
  have hX (i : S) : IsBanachTimeDomainTrajectoryOn f U z i.val (X i) := i.property.2.2.choose_spec
  have hcover : ∀ t < D, ∃ i : S, t < i.val := by
    intro t ht
    obtain ⟨u, huS, htu⟩ := exists_lt_of_lt_csSup hSne ht
    exact ⟨⟨u, huS⟩, htu⟩
  obtain ⟨α, hα0, hαd, _, hselect⟩ :=
    exists_glued_trajectory_before_sup hD (fun i : S => i.val) (fun i => i.property.1) X hcover
      (fun i => (hX i).initial) (fun i => (hX i).hasDerivAt)
      (fun i j => huniq (hX i) (hX j))
  have hαU (t : ℝ) (ht : t ∈ Ico (0 : ℝ) D) : α t ∈ U t := by
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

theorem exists_banachTimeDomainTrajectory_or_event
    (f : ℝ → E → E) (U : ℝ → Set E) (z : E) (H : ℝ) (event : ℝ → E → Prop)
    (hstart : ∃ T > 0, T ≤ H ∧ ∃ X : ℝ → E, IsBanachTimeDomainTrajectoryOn f U z T X)
    (huniq : ∀ {A B : ℝ} {X Y : ℝ → E},
      IsBanachTimeDomainTrajectoryOn f U z A X → IsBanachTimeDomainTrajectoryOn f U z B Y →
        EqOn X Y (Icc (0 : ℝ) (min A B)))
    (hcontinue : ∀ D, 0 < D → D ≤ H → ∀ α : ℝ → E,
      α 0 = z → (∀ t ∈ Ico (0 : ℝ) D, HasDerivAt α (f t (α t)) t) →
      (∀ t ∈ Ico (0 : ℝ) D, α t ∈ U t) →
      (∀ t ∈ Ico (0 : ℝ) D, ¬ event t (α t)) →
      ∃ δ > 0, ∃ Y : ℝ → E, IsBanachTimeDomainTrajectoryOn f U z (D + δ) Y) :
    (∃ X : ℝ → E, IsBanachTimeDomainTrajectoryOn f U z H X) ∨
      ∃ t ∈ Icc (0 : ℝ) H, ∃ X : ℝ → E,
        IsBanachTimeDomainTrajectoryOn f U z t X ∧ event t (X t) := by
  classical
  by_cases hevent : ∃ t ∈ Icc (0 : ℝ) H, ∃ X : ℝ → E,
      IsBanachTimeDomainTrajectoryOn f U z t X ∧ event t (X t)
  · exact Or.inr hevent
  left
  apply exists_banachTimeDomainTrajectory_of_no_finite_stopping f U z H hstart huniq
  intro D hD hDH α hα0 hαd hαmem
  apply hcontinue D hD hDH α hα0 hαd hαmem
  intro t ht htEvent
  let B := (t + D) / 2
  have hB : 0 < B := by dsimp only [B]; linarith [ht.1]
  have hBD : B < D := by dsimp only [B]; linarith [ht.2]
  have htB : t ≤ B := by dsimp only [B]; linarith [ht.2]
  have hpath : IsBanachTimeDomainTrajectoryOn f U z B α := by
    refine ⟨hα0, ?_, ?_, ?_⟩
    · exact fun s hs => (hαd s ⟨hs.1, hs.2.trans_lt hBD⟩).continuousAt.continuousWithinAt
    · exact fun s hs => hαd s ⟨hs.1, hs.2.trans_lt hBD⟩
    · exact fun s hs => hαmem s ⟨hs.1, hs.2.trans_lt hBD⟩
  exact hevent ⟨t, ⟨ht.1, htB.trans (hBD.le.trans hDH)⟩, α, hpath.mono htB, htEvent⟩

end Euler2D

end
