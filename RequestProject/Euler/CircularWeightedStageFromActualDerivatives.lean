module

public import RequestProject.Euler.CircularWeightedAncestorDomain
public import RequestProject.Euler.BanachWeightedTrajectoryStageClosure
public import RequestProject.Euler.CircularAncestorTimeRescaling

/-! Whole-stage closure for the original circular field from its
actual pointwise derivatives. The references retain arbitrary fixed
entrance phases; the common Lipschitz domain is supplied internally. -/

@[expose] public section

set_option maxHeartbeats 12000000
set_option maxRecDepth 5000

noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped NNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower

local instance weightedStageReal_tower (γ : ℝ≥0) : IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := (smul_smul a b Z).symm

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

include P

theorem exists_originalCircular_weighted_stage_closure :
    ∃ Kself : ℝ≥0, 0 < Kself ∧ ∃ r > 0, ∃ Lnorm : ℝ, 0 < Lnorm ∧
      ∀ b : ℝ≥0, 0 < b → b ≤ 1 →
      ∀ {ν₀ νbar C₀ Lseed Ccur Cpoly δ D₀ Ktarget Kboot : ℝ},
      0 < ν₀ → νbar < sigma → 1 < C₀ → 0 ≤ Lseed → 0 ≤ Ccur → 0 ≤ Cpoly →
      0 < Ktarget → 0 ≤ Kboot → Ccur * δ / (C₀ * (sigma - νbar)) ≤ Ktarget / 2 →
      ∀ᶠ x : ℝ in atTop, ∀ {β E₀ D : ℝ},
        let ρ := Real.exp (-x)
        let h := C₀ * ρ ^ 6
        let ν := ((b * Kself : ℝ≥0) : ℝ) + β
        h ≤ 1 → h * Kboot ≤ r → C₀ * ρ ^ 8 < 1 → 0 ≤ β → ν₀ ≤ ν → ν ≤ νbar → 0 ≤ E₀ →
        0 ≤ D → D ≤ (6 / sigma) * x + D₀ → E₀ * Real.exp (sigma * D) ≤ δ →
        ∀ (k : ℕ) (Y : ℕ → ℝ → Fin 2 → LittleContourSpace γ) (u₀ : ℕ → ℝ),
        let c := fun j t => littleCircularMaterialContours hγ hγ1 (u₀ j + (b : ℝ) ^ (k - j) * t)
        (∀ t ∈ Icc (0 : ℝ) D, weightedFamilyNorm h k (fun j => Y j t - c j t) ≤ Kboot) →
        weightedFamilyNorm h k (fun j => Y j 0 - c j 0) ≤ Lseed * h →
        (∀ j : Fin k, ∀ t ∈ Icc (0 : ℝ) D, ∃ p : Fin 2 → LittleContourSpace γ,
          HasDerivAt (Y j) (((b : ℝ) ^ (k - (j : ℕ))) • circularBanachField hγ hγ1 (Y j t) + p) t ∧
          ‖p‖ ≤ h ^ (k - (j : ℕ)) *
            (β * weightedFamilyNorm h k (fun j => Y j t - c j t) +
              (Ccur / C₀) * (E₀ * Real.exp (sigma * t)) + Cpoly * ρ ^ 6 * (1 + t) ^ 4)) →
        ∀ t ∈ Icc (0 : ℝ) D, weightedFamilyNorm h k (fun j => Y j t - c j t) ≤ Ktarget := by
  obtain ⟨U, hU, hUD, Kself, hKself, r, hr, Lnorm, hLnorm, hLip, hUnorm, hdomain⟩ :=
    exists_circular_weighted_ancestor_lipschitz_domain hγ hγ1
  refine ⟨Kself, hKself, r, hr, Lnorm, hLnorm, ?_⟩
  intro b hb hb1 ν₀ νbar C₀ Lseed Ccur Cpoly δ D₀ Ktarget Kboot
    hν₀ hgap hC₀ hLseed hCcur hCpoly hKtarget hKboot hcurrent
  have hevent := eventually_weighted_existing_trajectory_stage_closure hLip hb hb1 P.laplace.sigma_pos
    hν₀ hgap (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 0) hC₀
    hLseed hCcur hCpoly hKtarget hcurrent (D₀ := D₀)
  filter_upwards [hevent] with x hx
  intro β E₀ D ρ h ν hh1 hhr hζ hβ hνlo hνup hE₀ hD hclock hEmax k Y u₀ c hboot hinit hpoint
  classical
  let a : ℕ → ℝ≥0 := fun j => b ^ (k - j)
  let p : ℕ → ℝ → Fin 2 → LittleContourSpace γ := fun j t =>
    if hj : j < k then if ht : t ∈ Icc (0 : ℝ) D then Classical.choose (hpoint ⟨j, hj⟩ t ht) else 0 else 0
  have hp (j : Fin k) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) :
      HasDerivAt (Y j) ((a j : ℝ) • circularBanachField hγ hγ1 (Y j t) + p j t) t ∧
      ‖p j t‖ ≤ h ^ (k - (j : ℕ)) *
        (β * weightedFamilyNorm h k (fun j => Y j t - c j t) +
          (Ccur / C₀) * (E₀ * Real.exp (sigma * t)) + Cpoly * ρ ^ 6 * (1 + t) ^ 4) := by
    simpa only [p, dif_pos j.isLt, dif_pos ht, a, NNReal.coe_pow] using
      Classical.choose_spec (hpoint j t ht)
  have ha (j : Fin k) : a j ≤ b := by
    simpa only [a, pow_one] using pow_le_pow_of_le_one (show (0 : ℝ≥0) ≤ b by positivity)
      hb1 (show 1 ≤ k - (j : ℕ) by omega)
  have hcd (j : Fin k) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) :
      HasDerivAt (c j) ((a j : ℝ) • circularBanachField hγ hγ1 (c j t)) t := by
    have hparam : HasDerivAt (fun u : ℝ => u₀ j + (b : ℝ) ^ (k - (j : ℕ)) * u)
        ((b : ℝ) ^ (k - (j : ℕ))) t := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul ((b : ℝ) ^ (k - (j : ℕ)))).const_add (u₀ j)
    simpa only [c, a, NNReal.coe_pow, Function.comp_def, circularBanachField] using
      (littleCircularMaterialContours_hasDerivAt hγ hγ1 (u₀ j + (b : ℝ) ^ (k - (j : ℕ)) * t)).scomp t hparam
  have hdomains (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) (j : Fin k) : Y j t ∈ U ∧ c j t ∈ U :=
    hdomain (by dsimp only [h, ρ]; positivity) hh1 hKboot hhr k (fun j => Y j t)
      (fun j => u₀ j + (b : ℝ) ^ (k - j) * t) (hboot t ht) j
  have hνlo' : ν₀ ≤ ((b * Kself : ℝ≥0) : ℝ) + β + weightedInteractionRowFeedback b 0 0 C₀ ρ := by
    change ν₀ ≤ ν + weightedInteractionRowFeedback b 0 0 C₀ ρ
    simpa [weightedInteractionRowFeedback] using hνlo
  have hνup' : ((b * Kself : ℝ≥0) : ℝ) + β + weightedInteractionRowFeedback b 0 0 C₀ ρ ≤ νbar := by
    change ν + weightedInteractionRowFeedback b 0 0 C₀ ρ ≤ νbar
    simpa [weightedInteractionRowFeedback] using hνup
  exact hx hζ hβ hνlo' hνup' hE₀ hD hclock hEmax k a ha Y c p
    (fun t => Cpoly * ρ ^ 6 * (1 + t) ^ 4) (by fun_prop)
    (fun t ht => by positivity) (fun _ _ => le_rfl) hinit
    (fun j t ht => (hp j t ht).1) hcd
    (fun j t ht => (hdomains t ht j).1) (fun j t ht => (hdomains t ht j).2)
    (fun j t ht => by simpa only [zero_mul, zero_add, add_assoc] using (hp j t ht).2)

end CircularMaterialTransferProfile
end Euler2D

end
