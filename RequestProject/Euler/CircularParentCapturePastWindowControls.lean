module

public import RequestProject.Euler.CircularCanonicalControlGeometry
public import RequestProject.Euler.CircularCanonicalCrossPrefixReset
public import RequestProject.Euler.CircularFiniteUniformSupport

/-! The same prefix and actual particle flow retain their entire past
when the parent entrance is moved to the end of its warmup window.
The new ancestor entry is not replaced by zero. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set MeasureTheory
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local instance 2000] valueScalarC1_group valueScalarC1_space
attribute [local instance] ContourC1Space.complexScalarNormedSpace ContourC1Space.complexScalarTower

theorem canonicalPrefix_material_tube_of_past_and_window
    {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {A₀ b R ρ entrance D h Kw Kcur δ : ℝ}
    (hA : 0 < A₀) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ)
    (hentrance : 0 ≤ entrance) (hD : 0 ≤ D) (hh : 0 < h) (hh1 : h ≤ 1)
    (hKw : 0 ≤ Kw) (hhδ : h ≤ δ) (hhKw : h * (Kw * h) ≤ δ)
    (hKcur : Kcur * h ≤ δ) (k : ℕ)
    (Y : ℝ → FiniteCircularIndex k → LittleContourSpace γ)
    (hpast : ∀ t ∈ Icc (0 : ℝ) entrance,
      let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y (ampScale A₀ b k * t)
      weightedFamilyNorm h k x ≤ h ∧ ‖x k‖ ≤ h)
    (hweighted : ∀ u ∈ Icc (0 : ℝ) D,
      weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y u) ≤ Kw * h)
    (hcur : ∀ u ∈ Icc (0 : ℝ) D,
      ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y u k‖ ≤ Kcur * h) :
    ∀ t ∈ Icc (0 : ℝ) (entrance + D / ampScale A₀ b k),
      ∃ β : FiniteCircularIndex k → ℝ, ∀ p,
        ‖contourParameterShiftC1 (β p) (Y t p).val - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤
          δ * radScale R ρ p.1 := by
  have hAmp : 0 < ampScale A₀ b k := div_pos hA (pow_pos hb k)
  intro t ht
  have hclockOwn : physicalTimeFromNormalized (ampScale A₀ b k) 0 (ampScale A₀ b k * t) = t := by
    simp only [physicalTimeFromNormalized, zero_add, mul_div_cancel_left₀ t hAmp.ne']
  have build (K : ℝ) (hK : 0 ≤ K) (hbudget : h * K ≤ δ)
      (hweightedOwn : weightedFamilyNorm h k
        (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y (ampScale A₀ b k * t)) ≤ K)
      (hcurOwn : ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y (ampScale A₀ b k * t) k‖ ≤ δ) :
      ∃ β : FiniteCircularIndex k → ℝ, ∀ p,
        ‖contourParameterShiftC1 (β p) (Y t p).val - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤
          δ * radScale R ρ p.1 := by
    have hg := canonicalPrefix_material_tube_of_joint_controls hγ hγ1 A₀ b hR hρ k 0
      (ampScale A₀ b k * t) Y hh hh1 hK hbudget hweightedOwn hcurOwn
    rwa [hclockOwn] at hg
  by_cases hte : t ≤ entrance
  · have hp := hpast t ⟨ht.1, hte⟩
    exact build h hh.le ((mul_le_of_le_one_right hh.le hh1).trans hhδ)
      hp.1 (hp.2.trans hhδ)
  · let u := ampScale A₀ b k * (t - entrance)
    have hu : u ∈ Icc (0 : ℝ) D := by
      refine ⟨mul_nonneg hAmp.le (sub_nonneg.mpr (le_of_not_ge hte)), ?_⟩
      have hdiff : t - entrance ≤ D / ampScale A₀ b k := by linarith only [ht.2]
      exact (mul_le_mul_of_nonneg_left hdiff hAmp.le).trans_eq (by field_simp [hAmp.ne'])
    have hclockWindow : physicalTimeFromNormalized (ampScale A₀ b k) entrance u = t := by
      dsimp only [physicalTimeFromNormalized, u]
      rw [mul_div_cancel_left₀ (t - entrance) hAmp.ne']
      ring
    have hown (j : ℕ) (hj : j ≤ k) :
        canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y (ampScale A₀ b k * t) j =
          canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y u j :=
      canonicalPrefixStageDeviation_crossPrefix_eq hγ hγ1 hA.ne' hb.ne' R ρ le_rfl Y Y
        t entrance u 0 (ampScale A₀ b k * t) hclockWindow hclockOwn (fun _ => rfl) j hj
    have hweightedOwn : weightedFamilyNorm h k
        (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y (ampScale A₀ b k * t)) ≤ Kw * h := by
      rw [weightedFamilyNorm_congr_prefix h k (fun j => hown j j.isLt.le)]
      exact hweighted u hu
    have hcurOwn : ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y
        (ampScale A₀ b k * t) k‖ ≤ δ := by
      rw [hown k le_rfl]
      exact (hcur u hu).trans hKcur
    exact build (Kw * h) (mul_nonneg hKw hh.le) hhKw hweightedOwn hcurOwn

theorem actual_particles_past_and_window_radius
    {f : Lp ℝ 2 μT} {T A₀ b R ρ entrance D Cpre : ℝ}
    (S : BoundedEulerParticleSystem f T) (labels : Set R2)
    (hA : 0 < A₀) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ)
    (hentrance : 0 ≤ entrance) (hD : 0 ≤ D) (hCpre : 0 ≤ Cpre) (k : ℕ)
    (hpast : ∀ t ∈ Icc (0 : ℝ) entrance, ∀ z ∈ labels,
      ‖S.forward t z - torusCenter‖ ≤ 2 * ρ * radScale R ρ k)
    (hwindow : ∀ u ∈ Icc (0 : ℝ) D, ∀ z ∈ labels,
      ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b k) entrance u) z - torusCenter‖ ≤
        Cpre * ρ * radScale R ρ k * (1 + u)) :
    let e := entrance + D / ampScale A₀ b k
    let Cw := Cpre * (1 + D)
    (∀ t ∈ Icc (0 : ℝ) e, ∀ z ∈ labels,
      ‖S.forward t z - torusCenter‖ ≤ (Cw + 2) * ρ * radScale R ρ k) ∧
    ∀ z ∈ labels, ‖S.forward e z - torusCenter‖ ≤ Cw * ρ * radScale R ρ k := by
  let A := ampScale A₀ b k
  let Cw := Cpre * (1 + D)
  have hAmp : 0 < A := div_pos hA (pow_pos hb k)
  have hCw : 0 ≤ Cw := mul_nonneg hCpre (by linarith only [hD])
  have hrad : 0 ≤ ρ * radScale R ρ k := mul_nonneg hρ.le (radScale_pos hR hρ k).le
  have hwindowBound (u : ℝ) (hu : u ∈ Icc (0 : ℝ) D) (z : R2) (hz : z ∈ labels) :
      ‖S.forward (physicalTimeFromNormalized A entrance u) z - torusCenter‖ ≤
        Cw * ρ * radScale R ρ k := by
    have hh := hwindow u hu z hz
    calc
      _ ≤ Cpre * ρ * radScale R ρ k * (1 + u) := hh
      _ ≤ Cpre * ρ * radScale R ρ k * (1 + D) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hu.2)
          (mul_nonneg (mul_nonneg hCpre hρ.le) (radScale_pos hR hρ k).le)
      _ = _ := by dsimp only [Cw]; ring
  dsimp only
  constructor
  · intro t ht z hz
    by_cases hte : t ≤ entrance
    · exact (hpast t ⟨ht.1, hte⟩ z hz).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith only [hCw] : 2 ≤ Cw + 2) hρ.le)
          (radScale_pos hR hρ k).le)
    · let u := A * (t - entrance)
      have hu : u ∈ Icc (0 : ℝ) D := by
        refine ⟨mul_nonneg hAmp.le (sub_nonneg.mpr (le_of_not_ge hte)), ?_⟩
        have hdiff : t - entrance ≤ D / A := by linarith only [ht.2]
        exact (mul_le_mul_of_nonneg_left hdiff hAmp.le).trans_eq (by field_simp [hAmp.ne'])
      have hclock : physicalTimeFromNormalized A entrance u = t := by
        dsimp only [physicalTimeFromNormalized, u]
        rw [mul_div_cancel_left₀ (t - entrance) hAmp.ne']
        ring
      have hh := hwindowBound u hu z hz
      rw [hclock] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2)) hρ.le)
        (radScale_pos hR hρ k).le)
  · intro z hz
    exact hwindowBound D ⟨hD, le_rfl⟩ z hz

end Euler2D

end
