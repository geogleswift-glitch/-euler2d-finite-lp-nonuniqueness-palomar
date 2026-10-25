module

public import RequestProject.Euler.CircularCanonicalPrefixMaterialBoundary
public import RequestProject.Euler.BanachWeightedTrajectoryReset

/-! A genuine stage reset on the same original Euler solution. The
old and new active prefixes have different dimensions, but their common
material parameters and absolute normalized states agree exactly. -/

@[expose] public section

set_option maxHeartbeats 12000000
set_option maxRecDepth 5500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower

theorem canonicalPrefixStageDeviation_crossPrefix_eq {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {A₀ b : ℝ} (hA : A₀ ≠ 0) (hb : b ≠ 0)
    (R ρ : ℝ) {k l : ℕ} (hlk : l ≤ k)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ)
    (Y : ℝ → FiniteCircularIndex l → LittleContourSpace γ)
    (t e₁ τ₁ e₂ τ₂ : ℝ)
    (ht₁ : physicalTimeFromNormalized (ampScale A₀ b k) e₁ τ₁ = t)
    (ht₂ : physicalTimeFromNormalized (ampScale A₀ b l) e₂ τ₂ = t)
    (hXY : ∀ p : FiniteCircularIndex l, Y t p = X t (finiteCircularPrefixIndex hlk p))
    (j : ℕ) (hj : j ≤ l) :
    canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ l e₂ Y τ₂ j =
      canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k e₁ X τ₁ j := by
  rw [canonicalPrefixStageDeviation_eq_physical hγ hγ1 hA hb R ρ l e₂ τ₂ Y j hj,
    canonicalPrefixStageDeviation_eq_physical hγ hγ1 hA hb R ρ k e₁ τ₁ X j (hj.trans hlk), ht₁, ht₂]
  congr 1
  simp only [canonicalPrefixAbsoluteFamily, dif_pos hj, dif_pos (hj.trans hlk)]
  let jl : Fin (l + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  let jk : Fin (k + 1) := ⟨j, Nat.lt_succ_of_le (hj.trans hlk)⟩
  change canonicalPrefixAbsoluteCell A₀ b R ρ l e₂ Y τ₂ jl =
    canonicalPrefixAbsoluteCell A₀ b R ρ k e₁ X τ₁ jk
  rw [canonicalPrefixAbsoluteCell_eq_physicalState A₀ b R ρ l e₂ τ₂ t Y jl ht₂,
    canonicalPrefixAbsoluteCell_eq_physicalState A₀ b R ρ k e₁ τ₁ t X jk ht₁]
  have hcell : (fun i => Y t (jl, i)) = (fun i => X t (jk, i)) := by
    funext i
    exact hXY (jl, i)
  rw [hcell]

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualCanonical_crossPrefix_weighted_reset :
    ∃ C : ℝ, 0 < C ∧ ∀ {s A₀ b R ρ q T Hglob c : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
        (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
        (hρb : ρ < b) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      Hglob ≤ T → 5 / 4 + (C * A₀ / (1 - ρ / b)) * Hglob < c → c * R ≤ 1 / 4 →
      ∀ (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N),
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      ∀ {a₁ a₂ D₁ D₂ : ℝ}
        {X : ℝ → FiniteCircularIndex k → LittleContourSpace γ}
        {Y : ℝ → FiniteCircularIndex (k - 1) → LittleContourSpace γ},
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a₁ Hglob hR hρ hkN S D₁ X →
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a₂ Hglob hR hρ ((Nat.sub_le k 1).trans hkN) S D₂ Y →
      ∀ t, t ∈ Icc (0 : ℝ) D₁ → t ∈ Icc (0 : ℝ) D₂ →
      ∀ e₁ τ₁ e₂ τ₂ : ℝ,
      physicalTimeFromNormalized (ampScale A₀ b k) e₁ τ₁ = t →
      physicalTimeFromNormalized (ampScale A₀ b (k - 1)) e₂ τ₂ = t →
      ∀ {h K : ℝ}, 0 < h →
      weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k e₁ X τ₁) ≤ K →
      weightedFamilyNorm h (k - 1) (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ (k - 1) e₂ Y τ₂) ≤ K * h ∧
      ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ (k - 1) e₂ Y τ₂ (k - 1)‖ ≤ K * h ∧
      (2 ≤ k → ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ (k - 1) e₂ Y τ₂ (k - 2)‖ ≤ K * h ^ 2) := by
  obtain ⟨C, hC, hagree⟩ := P.exists_uniform_actualCanonical_crossPrefix_agreement
  refine ⟨C, hC, ?_⟩
  intro s A₀ b R ρ q T Hglob c _ hs hA hb hR hRmax hρ hρ1 hρb hq hqE hglobT hc hcR
    N k hk hkN S a₁ a₂ D₁ D₂ X Y hX hY t htX htY e₁ τ₁ e₂ τ₂ htime₁ htime₂ h K hh hbound
  have hXY := hagree hs hA.le hb hR hRmax hρ hρ1 hρb hq hqE hglobT hc hcR N S
    (Nat.sub_le k 1) hkN hX hY t htX htY
  let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k e₁ X τ₁
  let y := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ (k - 1) e₂ Y τ₂
  have heq (j : ℕ) (hj : j ≤ k - 1) : y j = x j :=
    canonicalPrefixStageDeviation_crossPrefix_eq hγ hγ1 hA.ne' hb.ne' R ρ (Nat.sub_le k 1)
      X Y t e₁ τ₁ e₂ τ₂ htime₁ htime₂ hXY j hj
  have hnormeq : weightedFamilyNorm h (k - 1) y = weightedFamilyNorm h (k - 1) x :=
    weightedFamilyNorm_congr_prefix h (k - 1) (fun j => heq j j.isLt.le)
  refine ⟨hnormeq.trans_le (weightedFamilyNorm_reset_bound hh k x hbound), ?_, ?_⟩
  · change ‖y (k - 1)‖ ≤ K * h
    rw [heq (k - 1) le_rfl]
    have hn := norm_le_weightedFamilyNorm hh k x (⟨k - 1, by omega⟩ : Fin k)
    have he : k - (k - 1) = 1 := by omega
    simpa only [Fin.val_mk, he, pow_one, mul_comm] using
      hn.trans (mul_le_mul_of_nonneg_left hbound (pow_pos hh (k - (k - 1))).le)
  · intro hk2
    change ‖y (k - 2)‖ ≤ K * h ^ 2
    rw [heq (k - 2) (by omega)]
    exact norm_parent_after_weighted_reset hh hk2 x hbound

end CircularMaterialTransferProfile
end Euler2D

end
