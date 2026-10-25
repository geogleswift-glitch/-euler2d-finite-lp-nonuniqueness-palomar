module

public import RequestProject.Euler.TorusTransportedLabelBounds
public import RequestProject.Euler.CircularFiniteTorusCorrectionBudget

/-! The individual labels of the actual finite datum, including its
actual ancient inner cell. Their genuine mass and amplitude constants
are uniform in the cutoff and in the ancient entry time. -/

@[expose] public section

set_option maxHeartbeats 2400000

noncomputable section

open MeasureTheory Set Filter Topology Metric Real
open scoped NNReal ENNReal

namespace Euler2D

def finiteLabelMassBound : ℝ := max (∫ x : R2, |cellW x|)
  (finiteContourPatchMassBound circularContourStrengths circularContourRadii)

def finiteLabelAmplitudeBound : ℝ := max 4 (finiteContourPatchSupBound circularContourStrengths)

theorem finiteLabelMassBound_nonneg : 0 ≤ finiteLabelMassBound :=
  (integral_nonneg (fun x : R2 => abs_nonneg (cellW x))).trans (le_max_left _ _)

theorem finiteLabelAmplitudeBound_nonneg : 0 ≤ finiteLabelAmplitudeBound := by
  exact (by norm_num : (0 : ℝ) ≤ 4).trans (le_max_left _ _)

theorem integral_abs_circularPhasePatchPlanarVorticity_le {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {Z : Fin 2 → LittleContourSpace γ}
    (hZ : Z ∈ circularQuarterPhaseDomain hγ hγ1) :
    (∫ x : R2, |circularPhasePatchPlanarVorticity Z x|) ≤
      finiteContourPatchMassBound circularContourStrengths circularContourRadii := by
  have he : (∫ x : R2, |circularPhasePatchPlanarVorticity Z x|) =
      ∫ z : ℂ, |circularPhasePatchVorticity Z z| := by
    simpa only [circularPhasePatchPlanarVorticity] using
      measurePreserving_planeComplexEquiv.integral_comp' (fun z => |circularPhasePatchVorticity Z z|)
  rw [he]
  exact integral_abs_circularPhasePatchVorticity_le hγ hγ1 hZ

theorem scaledPlanarSource_zero_of_one_le_norm {w : R2 → ℝ}
    (hw : ∀ x, (5 / 4 : ℝ) < ‖x‖ → w x = 0)
    {r : ℝ} (hr : 0 < r) (hrmax : r ≤ 1 / 2) (A : ℝ) {x : R2} (hx : 1 ≤ ‖x‖) :
    A * w (r⁻¹ • x) = 0 := by
  have hn : 2 ≤ ‖r⁻¹ • x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
    apply (le_inv_mul_iff₀ hr).mpr
    nlinarith
  rw [hw _ (by linarith), mul_zero]

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

def finitePlanarLabel (s A₀ b R ρ : ℝ) (N j : ℕ) : R2 → ℝ :=
  if j = N then P.finiteBaseDensity s A₀ b R ρ N else datumTerm A₀ b R ρ j

def finitePeriodicLabel (s A₀ b R ρ : ℝ) (N j : ℕ) : R2 → ℝ :=
  periodicCenteredSource (P.finitePlanarLabel s A₀ b R ρ N j)

theorem integrable_finitePlanarLabel {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hR : 0 < R) (hρ : 0 < ρ) (N j : ℕ) :
    Integrable (P.finitePlanarLabel s A₀ b R ρ N j) := by
  by_cases hj : j = N
  · simpa only [finitePlanarLabel, if_pos hj] using
      memLp_one_iff_integrable.mp (P.memLp_finiteBaseDensity (A₀ := A₀) (b := b) hs hR hρ 1 N)
  · simpa only [finitePlanarLabel, if_neg hj] using
      memLp_one_iff_integrable.mp (show MemLp (datumTerm A₀ b R ρ j) 1 volume by
        simpa using (datumTerm_memLp (A₀ := A₀) (b := b) (q := 1) hR hρ (by norm_num) j))

theorem finitePlanarLabel_zero_of_one_le_norm {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N j : ℕ) :
    ∀ x, 1 ≤ ‖x‖ → P.finitePlanarLabel s A₀ b R ρ N j x = 0 := by
  have hr (n : ℕ) : 0 < radScale R ρ n := mul_pos hR (pow_pos hρ n)
  have hrmax (n : ℕ) : radScale R ρ n ≤ 1 / 2 :=
    (mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1)).trans hRmax
  intro x hx
  by_cases hj : j = N
  · simp only [finitePlanarLabel, if_pos hj, finiteBaseDensity]
    apply scaledPlanarSource_zero_of_one_le_norm _ (hr N) (hrmax N) _ hx
    intro y hy
    by_contra hn
    exact (not_le.mpr hy) (norm_le_of_circularPhasePatchPlanarVorticity_ne_zero hγ hγ1
      (P.ancient_domain s hs) hn)
  · simp only [finitePlanarLabel, if_neg hj, datumTerm]
    apply scaledPlanarSource_zero_of_one_le_norm _ (hr j) (hrmax j) _ hx
    intro y hy
    exact cellW_eq_zero_of_one_le_norm (by linarith)

theorem norm_finitePlanarLabel_le {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hA : 0 ≤ A₀) (hb : 0 < b) (N j : ℕ) (x : R2) :
    ‖P.finitePlanarLabel s A₀ b R ρ N j x‖ ≤ finiteLabelAmplitudeBound * ampScale A₀ b j := by
  have hAmp (n : ℕ) : 0 ≤ ampScale A₀ b n := div_nonneg hA (pow_pos hb n).le
  by_cases hj : j = N
  · subst j
    simp only [finitePlanarLabel, if_pos rfl, ite_true, finiteBaseDensity, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (hAmp N)]
    have hn := norm_circularPhasePatchPlanarVorticity_le hγ hγ1 (P.ancient_domain s hs)
      ((radScale R ρ N)⁻¹ • x)
    rw [Real.norm_eq_abs] at hn
    calc
      _ ≤ ampScale A₀ b N * finiteContourPatchSupBound circularContourStrengths :=
        mul_le_mul_of_nonneg_left hn (hAmp N)
      _ ≤ ampScale A₀ b N * finiteLabelAmplitudeBound :=
        mul_le_mul_of_nonneg_left (le_max_right 4 (finiteContourPatchSupBound circularContourStrengths)) (hAmp N)
      _ = _ := by ring
  · simp only [finitePlanarLabel, if_neg hj, datumTerm, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (hAmp j)]
    have hn := norm_cellW_le_four ((radScale R ρ j)⁻¹ • x)
    rw [Real.norm_eq_abs] at hn
    calc
      _ ≤ ampScale A₀ b j * 4 := mul_le_mul_of_nonneg_left hn (hAmp j)
      _ ≤ ampScale A₀ b j * finiteLabelAmplitudeBound :=
        mul_le_mul_of_nonneg_left (le_max_left 4 (finiteContourPatchSupBound circularContourStrengths)) (hAmp j)
      _ = _ := by ring

theorem integral_abs_finitePlanarLabel_le {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ) (N j : ℕ) :
    (∫ x, |P.finitePlanarLabel s A₀ b R ρ N j x|) ≤
      finiteLabelMassBound * ampScale A₀ b j * radScale R ρ j ^ 2 := by
  have hAmp (n : ℕ) : 0 ≤ ampScale A₀ b n := div_nonneg hA (pow_pos hb n).le
  have hr (n : ℕ) : 0 < radScale R ρ n := mul_pos hR (pow_pos hρ n)
  by_cases hj : j = N
  · subst j
    simp only [finitePlanarLabel, if_pos rfl, ite_true, finiteBaseDensity]
    rw [integral_abs_planarScaledDensity _ (hr N).le, abs_of_nonneg (hAmp N)]
    have hh : (∫ x : R2, |circularPhasePatchPlanarVorticity (P.ancient s) x|) ≤ finiteLabelMassBound :=
      (integral_abs_circularPhasePatchPlanarVorticity_le hγ hγ1 (P.ancient_domain s hs)).trans
        (le_max_right _ _)
    calc
      _ ≤ ampScale A₀ b N * radScale R ρ N ^ 2 * finiteLabelMassBound :=
        mul_le_mul_of_nonneg_left hh (mul_nonneg (hAmp N) (sq_nonneg _))
      _ = _ := by ring
  · simp only [finitePlanarLabel, if_neg hj, datumTerm]
    rw [integral_abs_planarScaledDensity _ (hr j).le, abs_of_nonneg (hAmp j)]
    calc
      _ ≤ ampScale A₀ b j * radScale R ρ j ^ 2 * finiteLabelMassBound :=
        mul_le_mul_of_nonneg_left (le_max_left (∫ x : R2, |cellW x|)
          (finiteContourPatchMassBound circularContourStrengths circularContourRadii))
            (mul_nonneg (hAmp j) (sq_nonneg _))
      _ = _ := by ring

end CircularMaterialTransferProfile

end Euler2D

end
