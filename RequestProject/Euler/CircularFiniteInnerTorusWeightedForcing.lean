module

public import RequestProject.Euler.CircularFiniteClusterContourForcing
public import RequestProject.Euler.ActualTorusRadialPerturbationBudget
public import RequestProject.Euler.CircularTorusInteractionScale

/-! The genuine deep cluster periodic velocity retains its own mass
and radius. Its current-clock forcing has the original ancestor weight;
the full-source mass is never substituted for the cluster mass. -/

@[expose] public section

set_option maxHeartbeats 5000000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

theorem inner_torus_weighted_scale_le {R ρ C₀ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hC₀ : 1 ≤ C₀)
    {j k : ℕ} (hjk : j ≤ k) :
    radScale R ρ j ^ 2 * radScale R ρ k ^ 6 ≤
      R ^ 8 * (C₀ * ρ ^ 6) ^ (k - j) := by
  have hr : radScale R ρ k = radScale R ρ j * ρ ^ (k - j) := by
    simpa only [mul_comm] using (div_eq_iff (radScale_pos hR hρ j).ne').mp
      (radScale_ratio_eq_pow hR.ne' hρ.ne' hjk)
  have hjR : radScale R ρ j ≤ R :=
    mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1)
  have hj8 : radScale R ρ j ^ 8 ≤ R ^ 8 :=
    pow_le_pow_left₀ (radScale_pos hR hρ j).le hjR 8
  have hρw : (ρ ^ 6) ^ (k - j) ≤ (C₀ * ρ ^ 6) ^ (k - j) := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith only [mul_le_mul_of_nonneg_right hC₀ (by positivity : 0 ≤ ρ ^ 6)]
  calc
    _ = radScale R ρ j ^ 8 * (ρ ^ 6) ^ (k - j) := by
      rw [hr, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm (k - j) 6]
      ring
    _ ≤ _ := mul_le_mul hj8 hρw (by positivity) (by positivity)

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_finiteInnerCluster_torus_weighted_contourLittle :
    ∃ C : ℝ, 0 < C ∧ ∀ {η : ℝ≥0}, (η : ℝ) ≤ 1 →
      ∀ {s A₀ b R ρ a c D C₀ L : ℝ},
      s ≤ 0 → 0 < A₀ → 0 < b → ∀ (hR : 0 < R), R ≤ 1 / 2 →
      ∀ (hρ : 0 < ρ), ρ ≤ 1 → ρ ^ 2 < b →
      0 < a → a ≤ 1 / 16 → 0 ≤ c → 0 ≤ D → 1 ≤ C₀ →
      ∀ (N k j : ℕ), j ≤ k →
      ∀ {f : Lp ℝ 2 μT} {T : ℝ}, ∀ S : BoundedEulerParticleSystem f T,
      IsFourfoldBoundedEulerParticleSystem S → ∀ t ∈ Icc (0 : ℝ) T,
      c * ρ * radScale R ρ k * (1 + D) ≤ a →
      (∀ x ∈ torusBox, c * ρ * radScale R ρ k * (1 + D) < ‖x - torusCenter‖ →
        P.finiteInnerClusterSource s A₀ b R ρ N k S t x = 0) →
      0 ≤ L → (L + 1) * radScale R ρ j ≤ a / 2 →
      ∀ Z : LittleContourSpace η, ‖Z‖ ≤ L * radScale R ρ j →
      ∃ Q : LittleContourSpace η,
        (∀ θ, LittleContourSpace.lift η Q θ =
          actualTorusCorrectionVelocity
            (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t)
            (LittleContourSpace.lift η Z θ)) ∧
        ‖Q‖ / (ampScale A₀ b k * radScale R ρ j) ≤
          (C₀ * ρ ^ 6) ^ (k - j) *
            (C * torusCorrectionContourBudget (η : ℝ) L * finiteLabelMassBound *
              c ^ 4 * R ^ 8 * ρ ^ 6 * (1 + D) ^ 4 / (b * (1 - ρ ^ 2 / b))) := by
  obtain ⟨C, hC, hsource⟩ := exists_uniform_actualTorusCorrection_radialPerturbation_contourLittle
  refine ⟨C, hC, ?_⟩
  intro η hη s A₀ b R ρ a c D C₀ L hs hA hb hR hRmax hρ hρ1 hsmall
    ha ha16 hc hD hC₀ N k j hjk f T S hS t ht hchart hsupp hL hgeom Z hZ
  let w := P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t
  have hi : Integrable w := P.integrable_finiteInnerClusterComplexSource
    hs hA.le hb hR hRmax hρ hρ1 N k S t
  have hws : ∀ y, a < ‖y‖ → w y = 0 := by
    intro y hy
    exact boxedComplexDensity_support hsupp y (hchart.trans_lt hy)
  have hm : (∫ y, w y) = 0 := P.integral_finiteInnerClusterComplexSource_zero
    hs hA.le hb hR hRmax hρ hρ1 N k S t
  have hy : ∀ y, w (I * y) = w y :=
    P.finiteInnerClusterComplexSource_fourfold hs N k S hS ht
      (by linarith : a < 1) (fun x hx hax => hsupp x hx (hchart.trans_lt hax))
  obtain ⟨Q, hQ, hn⟩ := hsource ha ha16 hη w (fun _ => 0) hi (integrable_zero _ _ _)
    hws (fun _ _ => rfl) hm (by simp) hy (fun _ _ => rfl)
    (radScale_pos hR hρ j) hL hgeom Z hZ
  simp only [sub_zero] at hn
  have hM := P.finiteInnerClusterComplexSource_fourthAbsoluteMoment_le hs hA.le hb hR hRmax
    hρ hρ1 hsmall N k S t hsupp
  have hB : 0 ≤ torusCorrectionContourBudget (η : ℝ) L := by
    unfold torusCorrectionContourBudget
    positivity
  have hAk : 0 < ampScale A₀ b k := by unfold ampScale; positivity
  have hden : 0 < b * (1 - ρ ^ 2 / b) :=
    mul_pos hb (sub_pos.mpr ((div_lt_one hb).mpr hsmall))
  let B := C * torusCorrectionContourBudget (η : ℝ) L * finiteLabelMassBound *
    c ^ 4 * ρ ^ 6 * (1 + D) ^ 4 / (b * (1 - ρ ^ 2 / b))
  have hB0 : 0 ≤ B := by unfold B; positivity [finiteLabelMassBound_nonneg]
  have hphysical : ‖Q‖ / (ampScale A₀ b k * radScale R ρ j) ≤
      B * (radScale R ρ j ^ 2 * radScale R ρ k ^ 6) := by
    calc
      _ = (‖Q‖ / radScale R ρ j) / ampScale A₀ b k := by ring
      _ ≤ (C * torusCorrectionContourBudget (η : ℝ) L * radScale R ρ j ^ 2 *
          ∫ y : ℂ, ‖y‖ ^ 4 * |w y|) / ampScale A₀ b k :=
        div_le_div_of_nonneg_right hn hAk.le
      _ ≤ (C * torusCorrectionContourBudget (η : ℝ) L * radScale R ρ j ^ 2 *
          ((c * ρ * radScale R ρ k * (1 + D)) ^ 4 *
            finiteInnerClusterMassBudget A₀ b R ρ k)) / ampScale A₀ b k :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hM (by positivity)) hAk.le
      _ = _ := by
        unfold B finiteInnerClusterMassBudget
        field_simp [hAk.ne', hb.ne']
        <;> ring
  refine ⟨Q, hQ, hphysical.trans ?_⟩
  calc
    _ ≤ B * (R ^ 8 * (C₀ * ρ ^ 6) ^ (k - j)) :=
      mul_le_mul_of_nonneg_left (inner_torus_weighted_scale_le hR hρ hρ1 hC₀ hjk) hB0
    _ = _ := by unfold B; ring

end CircularMaterialTransferProfile
end Euler2D

end
