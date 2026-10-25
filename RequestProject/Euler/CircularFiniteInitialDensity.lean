module

public import RequestProject.Euler.CircularMaterialFiniteBase
public import RequestProject.Euler.TorusKernelSymmetry

/-! The actual finite initial vorticity consists of circular outer cells
and the same ancient material inner cell. It has a genuine periodic
representative, not a periodicity hypothesis on its planar source. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace Euler2D

theorem norm_cellW_le_four (x : R2) : ‖cellW x‖ ≤ 4 := by
  unfold cellW twoInterface
  by_cases h₁ : x ∈ ball (0 : R2) cellA <;>
    by_cases h₂ : x ∈ ball (0 : R2) 1 <;> norm_num [h₁, h₂]

theorem cellW_perpJ (x : R2) : cellW (perpJ x) = cellW x := by
  have hmem (r : ℝ) : perpJ x ∈ ball (0 : R2) r ↔ x ∈ ball (0 : R2) r := by
    simp only [mem_ball, dist_zero_right, norm_perpJ]
  unfold cellW twoInterface
  by_cases h₁ : x ∈ ball (0 : R2) cellA <;>
    by_cases h₂ : x ∈ ball (0 : R2) 1 <;>
      simp [h₁, h₂, hmem]

theorem cellW_eq_zero_of_one_le_norm {x : R2} (hx : 1 ≤ ‖x‖) : cellW x = 0 := by
  have h₁ : x ∉ ball (0 : R2) cellA := by
    simpa only [mem_ball, dist_zero_right, not_lt] using cellA_lt_one.le.trans hx
  have h₂ : x ∉ ball (0 : R2) 1 := by simpa only [mem_ball, dist_zero_right, not_lt] using hx
  simp [cellW, twoInterface, h₁, h₂]

theorem datumTerm_perpJ (A₀ b R ρ : ℝ) (j : ℕ) (x : R2) :
    datumTerm A₀ b R ρ j (perpJ x) = datumTerm A₀ b R ρ j x := by
  simp only [datumTerm, ← perpJ_smul, cellW_perpJ]

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

def finiteInitialPlanarDensity (s A₀ b R ρ : ℝ) (N : ℕ) (x : R2) : ℝ :=
  (∑ j ∈ Finset.range N, datumTerm A₀ b R ρ j x) + P.finiteBaseDensity s A₀ b R ρ N x

def finiteInitialDensityBound (A₀ b : ℝ) (N : ℕ) : ℝ :=
  (∑ j ∈ Finset.range N, |ampScale A₀ b j| * 4) +
    |ampScale A₀ b N| * finiteContourPatchSupBound circularContourStrengths

theorem finiteInitialDensityBound_nonneg (A₀ b : ℝ) (N : ℕ) :
    0 ≤ finiteInitialDensityBound A₀ b N := by
  exact add_nonneg (Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (by norm_num))
    (mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _))

theorem norm_finiteInitialPlanarDensity_le {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (N : ℕ) (x : R2) :
    ‖P.finiteInitialPlanarDensity s A₀ b R ρ N x‖ ≤ finiteInitialDensityBound A₀ b N := by
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _
    simp only [datumTerm, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_cellW_le_four _) (abs_nonneg _)
  · simp only [finiteBaseDensity, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (norm_circularPhasePatchPlanarVorticity_le hγ hγ1 (P.ancient_domain s hs) _)
      (abs_nonneg _)

theorem finiteInitialPlanarDensity_perpJ {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (N : ℕ) (x : R2) :
    P.finiteInitialPlanarDensity s A₀ b R ρ N (perpJ x) =
      P.finiteInitialPlanarDensity s A₀ b R ρ N x := by
  simp only [finiteInitialPlanarDensity, datumTerm_perpJ, finiteBaseDensity,
    ← perpJ_smul, circularPhasePatchPlanarVorticity_fourfold (P.ancient s) (P.ancient_fourfold s hs)]

theorem finiteInitialPlanarDensity_eq_zero {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N : ℕ) {x : R2} (hx : 1 ≤ ‖x‖) :
    P.finiteInitialPlanarDensity s A₀ b R ρ N x = 0 := by
  have hr (j : ℕ) : 0 < radScale R ρ j := mul_pos hR (pow_pos hρ j)
  have hrmax (j : ℕ) : radScale R ρ j ≤ 1 / 2 := by
    exact (mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1)).trans hRmax
  have hscale (j : ℕ) : 2 ≤ ‖(radScale R ρ j)⁻¹ • x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hr j).le)]
    apply (le_inv_mul_iff₀ (hr j)).mpr
    nlinarith [hrmax j]
  have hterms : ∀ j, datumTerm A₀ b R ρ j x = 0 := by
    intro j
    have hz : cellW ((radScale R ρ j)⁻¹ • x) = 0 :=
      cellW_eq_zero_of_one_le_norm ((by norm_num : (1 : ℝ) ≤ 2).trans (hscale j))
    simp only [datumTerm, hz, mul_zero]
  have hbase : P.finiteBaseDensity s A₀ b R ρ N x = 0 := by
    have hz : circularPhasePatchPlanarVorticity (P.ancient s) ((radScale R ρ N)⁻¹ • x) = 0 := by
      by_contra hn
      have hb := norm_le_of_circularPhasePatchPlanarVorticity_ne_zero hγ hγ1
        (P.ancient_domain s hs) hn
      linarith [hscale N]
    simp only [finiteBaseDensity, hz, mul_zero]
  simp only [finiteInitialPlanarDensity, hterms, Finset.sum_const_zero, hbase, add_zero]

theorem integrable_finiteInitialPlanarDensity {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hR : 0 < R) (hρ : 0 < ρ) (N : ℕ) :
    Integrable (P.finiteInitialPlanarDensity s A₀ b R ρ N) := by
  have hi (j : ℕ) : Integrable (datumTerm A₀ b R ρ j) := by
    apply memLp_one_iff_integrable.mp
    simpa using (datumTerm_memLp (A₀ := A₀) (b := b) hR hρ (q := 1) (by norm_num) j)
  exact (integrable_finset_sum _ fun j _ => hi j).add
    (memLp_one_iff_integrable.mp (P.memLp_finiteBaseDensity hs hR hρ 1 N))

theorem integral_finiteInitialPlanarDensity_zero {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hR : 0 < R) (hρ : 0 < ρ) (N : ℕ) :
    (∫ x, P.finiteInitialPlanarDensity s A₀ b R ρ N x) = 0 := by
  have hi (j : ℕ) : Integrable (datumTerm A₀ b R ρ j) :=
    memLp_one_iff_integrable.mp (by simpa using datumTerm_memLp hR hρ (q := 1) (by norm_num) j)
  have hb : Integrable (P.finiteBaseDensity s A₀ b R ρ N) :=
    memLp_one_iff_integrable.mp (P.memLp_finiteBaseDensity hs hR hρ 1 N)
  unfold finiteInitialPlanarDensity
  rw [integral_add (integrable_finset_sum _ fun j _ => hi j) hb,
    integral_finset_sum _ (fun j _ => hi j)]
  simp only [integral_datumTerm hR hρ, Finset.sum_const_zero,
    P.integral_finiteBaseDensity_zero hs hR hρ, zero_add]

def finiteInitialPeriodicDensity (s A₀ b R ρ : ℝ) (N : ℕ) : R2 → ℝ :=
  torusPeriodize (fun x => P.finiteInitialPlanarDensity s A₀ b R ρ N (x - torusCenter))

theorem isTorusPeriodic_finiteInitialPeriodicDensity (s A₀ b R ρ : ℝ) (N : ℕ) :
    IsTorusPeriodic (P.finiteInitialPeriodicDensity s A₀ b R ρ N) :=
  isTorusPeriodic_torusPeriodize _

theorem finiteInitialPeriodicDensity_quarterTurn {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (N : ℕ) (x : R2) :
    P.finiteInitialPeriodicDensity s A₀ b R ρ N (torusQuarterTurn x) =
      P.finiteInitialPeriodicDensity s A₀ b R ρ N x := by
  change (∑' k, P.finiteInitialPlanarDensity s A₀ b R ρ N
    (torusQuarterTurn x + torusLatticeShift k - torusCenter)) = _
  rw [← torusLatticeQuarterTurn.tsum_eq]
  apply tsum_congr
  intro k
  rw [torusLatticeShift_quarterTurn, ← torusQuarterTurn_add]
  simp only [torusQuarterTurn, add_sub_cancel_left, P.finiteInitialPlanarDensity_perpJ hs]

theorem finiteInitialPeriodicDensity_eq_on_box {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N : ℕ) {x : R2} (hx : x ∈ torusBox) :
    P.finiteInitialPeriodicDensity s A₀ b R ρ N x =
      P.finiteInitialPlanarDensity s A₀ b R ρ N (x - torusCenter) :=
  torusPeriodize_eq_on_box (fun y hy =>
    P.finiteInitialPlanarDensity_eq_zero hs hR hRmax hρ hρ1 N hy) hx

theorem integral_finiteInitialPeriodicDensity_zero {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N : ℕ) :
    (∫ x in torusBox, P.finiteInitialPeriodicDensity s A₀ b R ρ N x) = 0 := by
  calc
    _ = ∫ x in torusBox, P.finiteInitialPlanarDensity s A₀ b R ρ N (x - torusCenter) :=
      setIntegral_congr_fun measurableSet_torusBox (fun x hx =>
        P.finiteInitialPeriodicDensity_eq_on_box hs hR hRmax hρ hρ1 N hx)
    _ = ∫ x, P.finiteInitialPlanarDensity s A₀ b R ρ N (x - torusCenter) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      exact P.finiteInitialPlanarDensity_eq_zero hs hR hRmax hρ hρ1 N
        (le_of_not_gt fun hn => hx (norm_sub_center_lt_one_mem_box hn))
    _ = ∫ x, P.finiteInitialPlanarDensity s A₀ b R ρ N x :=
      integral_sub_right_eq_self _ torusCenter
    _ = 0 := P.integral_finiteInitialPlanarDensity_zero hs hR hρ N

end CircularMaterialTransferProfile

end Euler2D

end
