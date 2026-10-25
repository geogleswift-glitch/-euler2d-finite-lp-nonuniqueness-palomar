module

public import RequestProject.Euler.CircularFiniteEulerFamily
public import RequestProject.Euler.EulerPatchTransport

/-! A nonempty actual small-support window for the finite Euler data.
The source is the same raw initial density and the velocity bound comes
from the genuine particle equation. No confinement interval is assumed. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace Euler2D

namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem exists_short_time_transported_support {w : R2 → ℝ} {B a₀ a : ℝ}
    (hT : 0 < T) (hB0 : 0 ≤ B) (hB : ∀ᵐ x ∂μT, ‖f x‖ ≤ B)
    (ha₀ : 0 ≤ a₀) (haa : a₀ < a) (ha1 : a < 1)
    (hw : ∀ x ∈ torusBox, a₀ < ‖x - torusCenter‖ → w x = 0) :
    ∃ ε > 0, ε ≤ T ∧ ∀ t ∈ Icc (0 : ℝ) ε, ∀ x ∈ torusBox,
      a < ‖x - torusCenter‖ → S.transportedScalar w t x = 0 := by
  generalize hVdef : B * (∫ y in torusBox, ‖torusBiotSavartKernel y‖) = V
  have hV : 0 ≤ V := by
    rw [← hVdef]
    exact mul_nonneg hB0 (integral_nonneg fun _ => norm_nonneg _)
  have hden : 0 < 2 * (V + 1) := mul_pos (by norm_num) (by linarith only [hV])
  let ε := min T ((a - a₀) / (2 * (V + 1)))
  have hε : 0 < ε := lt_min hT (div_pos (sub_pos.mpr haa) hden)
  have hεT : ε ≤ T := min_le_left _ _
  let D : Set R2 := closedBall torusCenter a₀
  have hDbox : D ⊆ torusBox := by
    intro y hy
    have hn : ‖y - torusCenter‖ ≤ a₀ := mem_closedBall_iff_norm.mp hy
    exact norm_sub_center_lt_one_mem_box (hn.trans_lt (haa.trans ha1))
  refine ⟨ε, hε, hεT, ?_⟩
  intro t ht x hx hxa
  have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.trans hεT⟩
  have htime : V * t + a₀ < a := by
    have htε : t ≤ (a - a₀) / (2 * (V + 1)) := ht.2.trans (min_le_right _ _)
    have hm : t * (2 * (V + 1)) ≤ a - a₀ := (le_div_iff₀ hden).mp htε
    nlinarith [mul_nonneg hV ht.1]
  have himage_norm (y : R2) (hy : y ∈ D) : ‖S.forward t y - torusCenter‖ < a := by
    have hn : ‖y - torusCenter‖ ≤ a₀ := mem_closedBall_iff_norm.mp hy
    have hd := S.displacement_le hT.le hB htT y
    rw [hVdef] at hd
    have htri : ‖S.forward t y - torusCenter‖ ≤ ‖S.forward t y - y‖ + ‖y - torusCenter‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (S.forward t y - y) (y - torusCenter)
    exact (htri.trans (add_le_add hd hn)).trans_lt htime
  have himage : S.forward t '' D ⊆ torusBox := by
    rintro y ⟨z, hz, rfl⟩
    exact norm_sub_center_lt_one_mem_box ((himage_norm z hz).trans ha1)
  by_contra hne
  have hpre : torusWrap (S.backward t x) ∈ D := by
    apply mem_closedBall_iff_norm.mpr
    apply le_of_not_gt
    intro hn
    exact hne (hw _ (torusRep_mem _) hn)
  have hximage : x ∈ S.forward t '' D := by
    rw [← S.preimage_patch_inter_box t htT hDbox himage]
    exact ⟨hpre, hx⟩
  obtain ⟨y, hy, he⟩ := hximage
  have hn := himage_norm y hy
  rw [he] at hn
  exact (not_lt_of_ge hn.le) hxa

end BoundedEulerParticleSystem

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem finiteInitialPlanarDensity_eq_zero_of_radius {s A₀ b R ρ : ℝ}
    (hs : s ≤ 0) (hR : 0 < R) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N : ℕ) {x : R2} (hx : (5 / 4) * R < ‖x‖) :
    P.finiteInitialPlanarDensity s A₀ b R ρ N x = 0 := by
  have hr (j : ℕ) : 0 < radScale R ρ j := mul_pos hR (pow_pos hρ j)
  have hrmax (j : ℕ) : radScale R ρ j ≤ R :=
    mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1)
  have hscale (j : ℕ) : 5 / 4 < ‖(radScale R ρ j)⁻¹ • x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hr j).le)]
    apply (lt_inv_mul_iff₀ (hr j)).mpr
    nlinarith [hrmax j]
  have hterms : ∀ j, datumTerm A₀ b R ρ j x = 0 := by
    intro j
    have hz : cellW ((radScale R ρ j)⁻¹ • x) = 0 :=
      cellW_eq_zero_of_one_le_norm (by linarith [hscale j])
    simp only [datumTerm, hz, mul_zero]
  have hbase : P.finiteBaseDensity s A₀ b R ρ N x = 0 := by
    have hz : circularPhasePatchPlanarVorticity (P.ancient s) ((radScale R ρ N)⁻¹ • x) = 0 := by
      by_contra hn
      have hb := norm_le_of_circularPhasePatchPlanarVorticity_ne_zero hγ hγ1 (P.ancient_domain s hs) hn
      linarith [hscale N]
    simp only [finiteBaseDensity, hz, mul_zero]
  simp only [finiteInitialPlanarDensity, hterms, Finset.sum_const_zero, hbase, add_zero]

theorem exists_finiteEuler_short_support {s A₀ b R ρ q T a : ℝ}
    [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hR : 0 < R) (hRmax : R ≤ 1 / 2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
    (hT : 0 < T) (hRa : (5 / 4) * R < a) (ha1 : a < 1) (N : ℕ)
    (S : BoundedEulerParticleSystem
      (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
        (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T) :
    ∃ ε > 0, ε ≤ T ∧ ∀ t ∈ Icc (0 : ℝ) ε, ∀ x ∈ torusBox,
      a < ‖x - torusCenter‖ →
        S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t x = 0 := by
  have hB : ∀ᵐ x ∂μT, ‖finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
      (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N x‖ ≤
        finiteInitialDensityBound A₀ b N := by
    filter_upwards [P.finiteBaseCurlL2_ae_density (A₀ := A₀) (b := b) hs hR hρ hq hqE N] with x hx
    rw [hx]
    exact P.norm_finiteInitialPlanarDensity_le hs N _
  apply S.exists_short_time_transported_support hT (finiteInitialDensityBound_nonneg A₀ b N) hB
    (by positivity : 0 ≤ (5 / 4) * R) hRa ha1
  intro x hx hn
  rw [P.finiteInitialPeriodicDensity_eq_on_box hs hR hRmax hρ hρ1 N hx]
  exact P.finiteInitialPlanarDensity_eq_zero_of_radius hs hR hρ hρ1 N hn

end CircularMaterialTransferProfile

end Euler2D

end
