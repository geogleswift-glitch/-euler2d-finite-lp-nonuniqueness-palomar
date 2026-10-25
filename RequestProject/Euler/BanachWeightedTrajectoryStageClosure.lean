module

public import RequestProject.Euler.WeightedTrajectoryStageClosure

/-! Uniform full-stage closure for already existing trajectories with
their true derivatives and interaction-row source budget. It keeps
the original current sigma and is uniform in the finite family size. -/

@[expose] public section

set_option maxHeartbeats 5000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eventually_weighted_existing_trajectory_stage_closure
    {f : E → E} {U : Set E} {Kself b : ℝ≥0} (hLip : LipschitzOnWith Kself f U)
    (hb : 0 < b) (hb1 : b ≤ 1)
    {σ ν₀ νbar Cup Cdown C₀ L Ccur Cpoly δ D₀ K : ℝ}
    (hσ : 0 < σ) (hν₀ : 0 < ν₀) (hgap : νbar < σ)
    (hup : 0 ≤ Cup) (hdown : 0 ≤ Cdown) (hC₀ : 1 < C₀)
    (hL : 0 ≤ L) (hcur : 0 ≤ Ccur) (hpoly : 0 ≤ Cpoly) (hK : 0 < K)
    (hcurrent : Ccur * δ / (C₀ * (σ - νbar)) ≤ K / 2) :
    ∀ᶠ x : ℝ in atTop, ∀ {β₀ E₀ D : ℝ},
      let ρ := Real.exp (-x)
      let ν := ((b * Kself : ℝ≥0) : ℝ) + β₀ + weightedInteractionRowFeedback b Cup Cdown C₀ ρ
      C₀ * ρ ^ 8 < 1 → 0 ≤ β₀ → ν₀ ≤ ν → ν ≤ νbar → 0 ≤ E₀ →
      0 ≤ D → D ≤ (6 / σ) * x + D₀ → E₀ * Real.exp (σ * D) ≤ δ →
      ∀ (k : ℕ) (a : ℕ → ℝ≥0), (∀ j : Fin k, a j ≤ b) →
      ∀ (y c p : ℕ → ℝ → E) (R : ℝ → ℝ),
      ContinuousOn R (Icc (0 : ℝ) D) →
      (∀ t ∈ Icc (0 : ℝ) D, 0 ≤ R t) →
      (∀ t ∈ Icc (0 : ℝ) D, R t ≤ Cpoly * ρ ^ 6 * (1 + t) ^ 4) →
      weightedFamilyNorm (C₀ * ρ ^ 6) k (fun i => y i 0 - c i 0) ≤ L * (C₀ * ρ ^ 6) →
      (∀ j : Fin k, ∀ t ∈ Icc (0 : ℝ) D,
        HasDerivAt (y j) ((a j : ℝ) • f (y j t) + p j t) t) →
      (∀ j : Fin k, ∀ t ∈ Icc (0 : ℝ) D,
        HasDerivAt (c j) ((a j : ℝ) • f (c j t)) t) →
      (∀ j : Fin k, ∀ t ∈ Icc (0 : ℝ) D, y j t ∈ U) →
      (∀ j : Fin k, ∀ t ∈ Icc (0 : ℝ) D, c j t ∈ U) →
      (∀ j : Fin k, ∀ t ∈ Icc (0 : ℝ) D, ‖p j t‖ ≤
        Cup * (∑ l ∈ Finset.univ.filter (fun l : Fin k => j < l),
          (b : ℝ) ^ (k - (l : ℕ)) * ρ ^ (6 * ((l : ℕ) - j)) * ‖y l t - c l t‖) +
        Cdown * (∑ l ∈ Finset.univ.filter (fun l : Fin k => l < j),
          (b : ℝ) ^ (k - (l : ℕ)) * ρ ^ (2 * ((j : ℕ) - l)) * ‖y l t - c l t‖) +
        (C₀ * ρ ^ 6) ^ (k - (j : ℕ)) *
          (β₀ * weightedFamilyNorm (C₀ * ρ ^ 6) k (fun i => y i t - c i t) +
            (Ccur / C₀) * (E₀ * Real.exp (σ * t)) + R t)) →
      ∀ t ∈ Icc (0 : ℝ) D, weightedFamilyNorm (C₀ * ρ ^ 6) k (fun i => y i t - c i t) ≤ K := by
  obtain ⟨Ctail, hCt, hclosure⟩ := exists_uniform_weighted_stage_closure hσ hν₀ hgap
  have hC : 0 < C₀ := by linarith
  filter_upwards [hclosure hC hL hcur hpoly hK hcurrent] with x hx
  intro β₀ E₀ D ρ ν hζ hβ₀ hνlo hνup hE₀ hD hclock hEmax k a ha y c p R hRc hRn hR hZ₀ hyd hcd hym hcm hsource
  let g : ℝ → ℝ := fun t => (Ccur / C₀) * (E₀ * Real.exp (σ * t)) + R t
  have hgc : ContinuousOn g (Icc (0 : ℝ) D) :=
    (by fun_prop : ContinuousOn (fun t : ℝ => (Ccur / C₀) * (E₀ * Real.exp (σ * t))) (Icc 0 D)).add hRc
  have hgn (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) : 0 ≤ g t := by
    have hn := hRn t ht
    dsimp [g]
    positivity
  have hwhole := weighted_existing_trajectory_row_envelope hLip hb hb1 hD hup hdown hC₀
    (Real.exp_pos (-x)) hζ hβ₀ k a ha y c p g hgc hgn hyd hcd hym hcm
    (fun j t ht => by simpa only [g, add_assoc] using hsource j t ht)
  intro t ht
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) D := fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩
  have hA : IntervalIntegrable (fun s : ℝ => (Ccur / C₀) *
      (Real.exp (ν * (t - s)) * (E₀ * Real.exp (σ * s)))) volume 0 t :=
    (by fun_prop : Continuous (fun s : ℝ => (Ccur / C₀) *
      (Real.exp (ν * (t - s)) * (E₀ * Real.exp (σ * s))))).intervalIntegrable 0 t
  have hB : IntervalIntegrable (fun s : ℝ => Real.exp (ν * (t - s)) * R s) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.1]
    exact (by fun_prop : ContinuousOn (fun s : ℝ => Real.exp (ν * (t - s))) (Icc 0 t)).mul (hRc.mono hsub)
  have hsplit : (∫ s in (0)..t, Real.exp (ν * (t - s)) * g s) =
      (Ccur / C₀) * (∫ s in (0)..t, Real.exp (ν * (t - s)) * (E₀ * Real.exp (σ * s))) +
        (∫ s in (0)..t, Real.exp (ν * (t - s)) * R s) := by
    calc
      _ = ∫ s in (0)..t, (Ccur / C₀) *
          (Real.exp (ν * (t - s)) * (E₀ * Real.exp (σ * s))) + Real.exp (ν * (t - s)) * R s := by
        apply intervalIntegral.integral_congr
        intro s _
        dsimp [g]
        ring
      _ = _ := by rw [intervalIntegral.integral_add hA hB, intervalIntegral.integral_const_mul]
  have hZ := hwhole t ht
  change weightedFamilyNorm (C₀ * ρ ^ 6) k (fun i => y i t - c i t) ≤
    weightedFamilyNorm (C₀ * ρ ^ 6) k (fun i => y i 0 - c i 0) * Real.exp (ν * t) +
      ∫ s in (0)..t, Real.exp (ν * (t - s)) * g s at hZ
  rw [hsplit] at hZ
  exact hx hνlo hνup hE₀ ht.1 ht.2 hclock hEmax hZ₀ R (hRc.mono hsub)
    (fun s hs => hR s (hsub hs)) (by simpa only [add_assoc] using hZ)

end Euler2D

end
