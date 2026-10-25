module

public import RequestProject.Euler.ActualTorusContourLittle
public import RequestProject.Euler.LabelInteractions

/-! Source continuity for the actual periodic correction in the original
little contour norm.  All source differences use the genuine kernel integral. -/

@[expose] public section

set_option maxHeartbeats 1500000

noncomputable section

open Complex ComplexConjugate Set Filter Topology MeasureTheory Metric
open scoped NNReal

namespace Euler2D

theorem integrable_actualTorusCorrectionVelocity_integrand
    {w : ℂ → ℝ} (hw : Integrable w) (x : ℂ) :
    Integrable (fun y => w y • actualComplexRemainderKernel (x - y)) := by
  have hi := complexPerpGradientOperator.integrable_comp
    (integrable_actualComplexGreenCorrection_derivative hw x)
  simpa only [map_smul, actualComplexRemainderKernel_eq_operator] using hi

theorem actualTorusCorrectionVelocity_sub {w v : ℂ → ℝ}
    (hw : Integrable w) (hv : Integrable v) (x : ℂ) :
    actualTorusCorrectionVelocity (fun y => w y - v y) x =
      actualTorusCorrectionVelocity w x - actualTorusCorrectionVelocity v x := by
  unfold actualTorusCorrectionVelocity
  simp_rw [sub_smul]
  exact integral_sub (integrable_actualTorusCorrectionVelocity_integrand hw x)
    (integrable_actualTorusCorrectionVelocity_integrand hv x)

theorem littleContour_eq_of_lift_eq {γ : ℝ≥0} {Q P : LittleContourSpace γ}
    (h : ∀ θ, LittleContourSpace.lift γ Q θ = LittleContourSpace.lift γ P θ) : Q = P := by
  apply Subtype.ext
  apply ContourC1Space.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact h θ

theorem exists_actualTorusCorrection_source_lipschitz
    {a : ℝ} (ha : 0 < a) (ha16 : a ≤ 1 / 16) :
    ∃ C : ℝ, 0 < C ∧ ∀ {γ : ℝ≥0}, (γ : ℝ) ≤ 1 →
      ∀ w v : ℂ → ℝ, Integrable w → Integrable v →
      (∀ y, a < ‖y‖ → w y = 0) → (∀ y, a < ‖y‖ → v y = 0) →
      (∫ y, w y) = 0 → (∫ y, v y) = 0 →
      (∀ y, w (I * y) = w y) → (∀ y, v (I * y) = v y) →
      ∀ {R L : ℝ}, 0 < R → 0 ≤ L → (L + 1) * R ≤ a / 2 →
      ∀ Z : LittleContourSpace γ, ‖Z‖ ≤ L * R →
      ∀ Q P : LittleContourSpace γ,
        (∀ θ, LittleContourSpace.lift γ Q θ =
          actualTorusCorrectionVelocity w (LittleContourSpace.lift γ Z θ)) →
        (∀ θ, LittleContourSpace.lift γ P θ =
          actualTorusCorrectionVelocity v (LittleContourSpace.lift γ Z θ)) →
        ‖Q - P‖ ≤ C * torusCorrectionContourBudget (γ : ℝ) L * R ^ 3 * a ^ 4 *
          ∫ y : ℂ, |w y - v y| := by
  obtain ⟨C, hC, hsource⟩ := exists_actualTorusKernelCorrection_contourLittle ha ha16
  refine ⟨C, hC, ?_⟩
  intro γ hγ w v hw hv hws hvs hwm hvm hwy hvy R L hR hL hs Z hZ Q P hQ hP
  have hd : Integrable (fun y => w y - v y) := hw.sub hv
  have hds : ∀ y, a < ‖y‖ → w y - v y = 0 := by
    intro y hy
    rw [hws y hy, hvs y hy, sub_self]
  have hdm : (∫ y, w y - v y) = 0 := by rw [integral_sub hw hv, hwm, hvm, sub_self]
  have hdy : ∀ y, w (I * y) - v (I * y) = w y - v y := fun y => by rw [hwy y, hvy y]
  obtain ⟨D, hD, hn⟩ := hsource hγ _ hd hds hdm hdy hR hL hs Z hZ
  have he : D = Q - P := by
    apply littleContour_eq_of_lift_eq
    intro θ
    have hx := (ContourC1Space.norm_eval_le Z.val (θ : ContourCircle)).trans hZ
    change ‖LittleContourSpace.lift γ Z θ‖ ≤ L * R at hx
    calc
      _ = actualTorusCorrectionVelocity (fun y => w y - v y)
          (LittleContourSpace.lift γ Z θ) :=
        (hD θ).trans (actualTorusKernelDifference_eq_correctionVelocity ha16 hds (by nlinarith))
      _ = actualTorusCorrectionVelocity w (LittleContourSpace.lift γ Z θ) -
          actualTorusCorrectionVelocity v (LittleContourSpace.lift γ Z θ) :=
        actualTorusCorrectionVelocity_sub hw hv _
      _ = LittleContourSpace.lift γ (Q - P) θ := by
        change _ = ContourC1Space.lift γ (Q.val - P.val) θ
        rw [ContourC1Space.lift_sub]
        exact congrArg₂ (· - ·) (hQ θ).symm (hP θ).symm
  rw [he] at hn
  have hm := fourth_le_mass hd hds
  have hb : 0 ≤ torusCorrectionContourBudget (γ : ℝ) L := by
    unfold torusCorrectionContourBudget
    positivity
  have hh := (div_le_iff₀ hR).mp hn
  calc
    ‖Q - P‖ ≤ (C * torusCorrectionContourBudget (γ : ℝ) L * R ^ 2 *
        ∫ y : ℂ, ‖y‖ ^ 4 * |w y - v y|) * R := hh
    _ ≤ (C * torusCorrectionContourBudget (γ : ℝ) L * R ^ 2 *
        (a ^ 4 * ∫ y : ℂ, |w y - v y|)) * R :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by positivity)) hR.le
    _ = _ := by ring

theorem tendsto_actualTorusCorrection_of_L1
    {a : ℝ} (ha : 0 < a) (ha16 : a ≤ 1 / 16)
    {γ : ℝ≥0} (hγ : (γ : ℝ) ≤ 1)
    {α : Type*} {l : Filter α} {w : α → ℂ → ℝ} {v : ℂ → ℝ}
    (hw : ∀ t, Integrable (w t)) (hv : Integrable v)
    (hws : ∀ t y, a < ‖y‖ → w t y = 0) (hvs : ∀ y, a < ‖y‖ → v y = 0)
    (hwm : ∀ t, (∫ y, w t y) = 0) (hvm : (∫ y, v y) = 0)
    (hwy : ∀ t y, w t (I * y) = w t y) (hvy : ∀ y, v (I * y) = v y)
    {R L : ℝ} (hR : 0 < R) (hL : 0 ≤ L) (hs : (L + 1) * R ≤ a / 2)
    (Z : LittleContourSpace γ) (hZ : ‖Z‖ ≤ L * R)
    {Q : α → LittleContourSpace γ} {P : LittleContourSpace γ}
    (hQ : ∀ t θ, LittleContourSpace.lift γ (Q t) θ =
      actualTorusCorrectionVelocity (w t) (LittleContourSpace.lift γ Z θ))
    (hP : ∀ θ, LittleContourSpace.lift γ P θ =
      actualTorusCorrectionVelocity v (LittleContourSpace.lift γ Z θ))
    (hlim : Tendsto (fun t => ∫ y : ℂ, |w t y - v y|) l (𝓝 0)) :
    Tendsto Q l (𝓝 P) := by
  obtain ⟨C, _, hC⟩ := exists_actualTorusCorrection_source_lipschitz ha ha16
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun t => hC hγ (w t) v (hw t) hv (hws t) hvs (hwm t) hvm
      (hwy t) hvy hR hL hs Z hZ (Q t) P (hQ t) hP)
    (by simpa only [mul_zero] using
      hlim.const_mul (C * torusCorrectionContourBudget (γ : ℝ) L * R ^ 3 * a ^ 4))

end Euler2D

end
