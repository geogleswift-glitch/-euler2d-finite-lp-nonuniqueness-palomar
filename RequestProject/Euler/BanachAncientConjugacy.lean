module

public import RequestProject.Euler.BanachAncientCurve
public import RequestProject.Euler.BanachDoubleFlow
public import RequestProject.Euler.BanachDoubleReturn

/-! A genuine local chart conjugacy lifts an actual doubled return
orbit to an ancient material integral curve of the original vector field. -/

@[expose] public section

set_option maxHeartbeats 1500000

noncomputable section

open Set Filter Topology Metric

namespace Euler2D

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem eventually_doubleReturn_chart_flow
    {F : E → E} (hF0 : F 0 = 0) (hF : ContinuousAt F 0)
    {Φ : E → B} (hΦ : ContinuousAt Φ 0)
    {X : B → ℝ → B} {V : Set B} {T : ℝ} (hV : V ∈ 𝓝 (Φ 0))
    (hconj : ∀ᶠ v : E in 𝓝 0, Φ (F v) = X (Φ v) T) :
    ∀ᶠ v : E in 𝓝 0,
      Φ v ∈ banachDoubleFlowDomain X V T ∧
      Φ (banachDoubleReturn F v) = X (X (Φ v) T) T := by
  have hnear : ∀ᶠ v : E in 𝓝 0, Φ v ∈ V := hΦ hV
  have hnearF : ∀ᶠ v : E in 𝓝 0, Φ (F v) ∈ V := hF (by rw [hF0]; exact hnear)
  have hconjF : ∀ᶠ v : E in 𝓝 0, Φ (F (F v)) = X (Φ (F v)) T :=
    hF (by rw [hF0]; exact hconj)
  filter_upwards [hnear, hnearF, hconj, hconjF] with v hv hvF hc hcF
  refine ⟨⟨hv, ?_⟩, ?_⟩
  · change X (Φ v) T ∈ V
    rw [← hc]
    exact hvF
  · change Φ (F (F v)) = _
    rw [hcF, hc]

theorem exists_ancientCurve_lifting_double_return
    {f : B → B} {U V : Set B} {T : ℝ} (hT : 0 < T) {X : B → ℝ → B}
    (hX : IsBanachFlowOn f U V T X)
    {F : E → E} (hF0 : F 0 = 0) (hF : ContinuousAt F 0)
    {Φ : E → B} (hΦ : ContinuousAt Φ 0) (hV : V ∈ 𝓝 (Φ 0))
    (hconj : ∀ᶠ v : E in 𝓝 0, Φ (F v) = X (Φ v) T) :
    ∃ r > 0, ∀ x : ℕ → E, (∀ n, x n ∈ closedBall 0 r) →
      (∀ n, banachDoubleReturn F (x (n + 1)) = x n) →
      ∃ Y : ℝ → B, Y 0 = Φ (x 0) ∧ ContinuousOn Y (Iic 0) ∧
        (∀ t ≤ 0, Y t ∈ U) ∧
        (∀ t ≤ 0, HasDerivAt Y (f (Y t)) t) ∧
        ∀ n : ℕ, Y (-(n : ℝ) * (T + T)) = Φ (x n) := by
  obtain ⟨s, hs, hb⟩ := Metric.eventually_nhds_iff.mp
    (eventually_doubleReturn_chart_flow hF0 hF hΦ hV hconj)
  have hsub : closedBall (0 : E) (s / 2) ⊆ ball 0 s := closedBall_subset_ball (half_lt_self hs)
  refine ⟨s / 2, half_pos hs, ?_⟩
  intro x hx hrec
  let z : ℕ → B := fun n => Φ (x n)
  have hz (n : ℕ) : z n ∈ banachDoubleFlowDomain X V T := (hb (hsub (hx n))).1
  have hreturn (n : ℕ) : banachDoubleFlow X T (z (n + 1)) (T + T) = z n := by
    rw [banachDoubleFlow_endpoint hT]
    calc
      _ = Φ (banachDoubleReturn F (x (n + 1))) := (hb (hsub (hx (n + 1)))).2.symm
      _ = _ := congrArg Φ (hrec n)
  exact exists_ancientCurve_of_return_sequence (by linarith : 0 < T + T)
    (isBanachFlowOn_banachDoubleFlow hT.le hX) hz hreturn

end Euler2D

end
