module

public import RequestProject.Euler.CircularWeightedAncestorDomain
public import RequestProject.Euler.CircularAncestorTimeRescaling
public import RequestProject.Euler.WeightedExistingFixedWindow

/-! Fixed-window weighted control for the original circular field.
The common domain follows from the genuine weighted bootstrap; the
small factor in the initial condition and source is retained. -/

@[expose] public section

set_option maxHeartbeats 12000000
set_option maxRecDepth 6000

noncomputable section

open Set Metric
open scoped NNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower

local instance weightedWindowReal_tower (γ : ℝ≥0) : IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := (smul_smul a b Z).symm

theorem exists_circular_weighted_fixed_window_constants {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ∃ Kself : ℝ≥0, 0 < Kself ∧ ∃ r > 0,
      ∀ b : ℝ≥0, 0 < b → b ≤ 1 →
      ∀ {h H D β Lseed F νbar Kboot : ℝ},
      0 < h → h ≤ 1 → 0 ≤ H → H ≤ D →
      0 ≤ β → 0 ≤ Lseed → 0 ≤ F → 0 ≤ Kboot → h * Kboot ≤ r →
      ((b * Kself : ℝ≥0) : ℝ) + β ≤ νbar →
      ∀ (k : ℕ) (Y : ℕ → ℝ → Fin 2 → LittleContourSpace γ) (u₀ : ℕ → ℝ),
      let c := fun j t => littleCircularMaterialContours hγ hγ1 (u₀ j + (b : ℝ) ^ (k - j) * t)
      (∀ t ∈ Icc (0 : ℝ) H, weightedFamilyNorm h k (fun j => Y j t - c j t) ≤ Kboot) →
      weightedFamilyNorm h k (fun j => Y j 0 - c j 0) ≤ Lseed * h →
      (∀ j : Fin k, ∀ t ∈ Icc (0 : ℝ) H, ∃ p : Fin 2 → LittleContourSpace γ,
        HasDerivAt (Y j) (((b : ℝ) ^ (k - (j : ℕ))) • circularBanachField hγ hγ1 (Y j t) + p) t ∧
        ‖p‖ ≤ h ^ (k - (j : ℕ)) *
          (β * weightedFamilyNorm h k (fun j => Y j t - c j t) + F * h)) →
      ∀ t ∈ Icc (0 : ℝ) H, weightedFamilyNorm h k (fun j => Y j t - c j t) ≤
        (Lseed + F * D) * Real.exp (νbar * D) * h := by
  obtain ⟨U, _hU, _hUD, Kself, hKself, r, hr, _Lnorm, _hLnorm, hLip, _hUnorm, hdomain⟩ :=
    exists_circular_weighted_ancestor_lipschitz_domain hγ hγ1
  refine ⟨Kself, hKself, r, hr, ?_⟩
  intro b _hb hb1 h H D β Lseed F νbar Kboot hh hh1 hH hHD hβ hLseed hF hKboot hhr hνup
    k Y u₀ c hboot hinit hpoint
  classical
  let a : ℕ → ℝ≥0 := fun j => b ^ (k - j)
  let p : ℕ → ℝ → Fin 2 → LittleContourSpace γ := fun j t =>
    if hj : j < k then if ht : t ∈ Icc (0 : ℝ) H then Classical.choose (hpoint ⟨j, hj⟩ t ht) else 0 else 0
  have hp (j : Fin k) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) H) :
      HasDerivAt (Y j) ((a j : ℝ) • circularBanachField hγ hγ1 (Y j t) + p j t) t ∧
      ‖p j t‖ ≤ h ^ (k - (j : ℕ)) *
        (β * weightedFamilyNorm h k (fun j => Y j t - c j t) + F * h) := by
    simpa only [p, dif_pos j.isLt, dif_pos ht, a, NNReal.coe_pow] using
      Classical.choose_spec (hpoint j t ht)
  have ha (j : Fin k) : a j ≤ b := by
    simpa only [a, pow_one] using pow_le_pow_of_le_one (show (0 : ℝ≥0) ≤ b by positivity)
      hb1 (show 1 ≤ k - (j : ℕ) by omega)
  have hcd (j : Fin k) (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) H) :
      HasDerivAt (c j) ((a j : ℝ) • circularBanachField hγ hγ1 (c j t)) t := by
    have hparam : HasDerivAt (fun u : ℝ => u₀ j + (b : ℝ) ^ (k - (j : ℕ)) * u)
        ((b : ℝ) ^ (k - (j : ℕ))) t := by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id t).const_mul ((b : ℝ) ^ (k - (j : ℕ)))).const_add (u₀ j)
    simpa only [c, a, NNReal.coe_pow] using
      (littleCircularMaterialContours_hasDerivAt hγ hγ1 (u₀ j + (b : ℝ) ^ (k - (j : ℕ)) * t)).scomp t hparam
  have hdomains (t : ℝ) (ht : t ∈ Icc (0 : ℝ) H) (j : Fin k) : Y j t ∈ U ∧ c j t ∈ U :=
    hdomain hh hh1 hKboot hhr k (fun j => Y j t)
      (fun j => u₀ j + (b : ℝ) ^ (k - j) * t) (hboot t ht) j
  exact weighted_existing_trajectory_fixed_window_bound hLip hh hH hHD hβ hLseed hF hνup k a ha Y c p
    (fun j t ht => (hp j t ht).1) hcd
    (fun j t ht => (hdomains t ht j).1) (fun j t ht => (hdomains t ht j).2)
    hinit (fun j t ht => (hp j t ht).2)

end Euler2D

end
