module

public import RequestProject.Euler.CircularFinitePlanarVelocityDecomposition
public import RequestProject.Euler.ActualTorusContourSourceContinuity
public import RequestProject.Euler.TorusPhysicalCorrectionIdentity

/-! Exact source and field splits of the same original finite Euler
system at an arbitrary active prefix. In particular its literal torus
correction is the sum of active-label corrections and the actual deep
cluster correction used in the weighted source budgets. -/

@[expose] public section

set_option maxHeartbeats 5000000
set_option maxRecDepth 4000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

theorem actualTorusCorrectionVelocity_add {w v : ℂ → ℝ}
    (hw : Integrable w) (hv : Integrable v) (x : ℂ) :
    actualTorusCorrectionVelocity (fun y => w y + v y) x =
      actualTorusCorrectionVelocity w x + actualTorusCorrectionVelocity v x := by
  unfold actualTorusCorrectionVelocity
  simp_rw [add_smul]
  exact integral_add (integrable_actualTorusCorrectionVelocity_integrand hw x)
    (integrable_actualTorusCorrectionVelocity_integrand hv x)

theorem actualTorusCorrectionVelocity_finset_sum {ι : Type*} (s : Finset ι)
    (w : ι → ℂ → ℝ) (hw : ∀ i ∈ s, Integrable (w i)) (x : ℂ) :
    actualTorusCorrectionVelocity (fun y => ∑ i ∈ s, w i y) x =
      ∑ i ∈ s, actualTorusCorrectionVelocity (w i) x := by
  unfold actualTorusCorrectionVelocity
  simp_rw [Finset.sum_smul]
  exact integral_finset_sum _ (fun i hi => integrable_actualTorusCorrectionVelocity_integrand (hw i hi) x)

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem finiteInnerClusterComplexSource_eq_sum_boxedLabels
    (s A₀ b R ρ : ℝ) (N k : ℕ) {f : Lp ℝ 2 μT} {T : ℝ}
    (S : BoundedEulerParticleSystem f T) (t : ℝ) :
    P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t =
      fun x => ∑ l ∈ Finset.Ico (k + 1) (N + 1), boxedComplexDensity
        (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N l) t) x := by
  funext x
  by_cases hx : complexTorusPoint x ∈ torusBox <;>
    simp [finiteInnerClusterComplexSource, finiteInnerClusterSource, boxedComplexDensity, hx]

theorem finiteInnerClusterComplexSource_eq_middle_add_deep
    (s A₀ b R ρ : ℝ) (N j k : ℕ) (hjk : j ≤ k) (hkN : k ≤ N)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t : ℝ) :
    P.finiteInnerClusterComplexSource s A₀ b R ρ N j S t = fun x =>
      (∑ l ∈ Finset.Ico (j + 1) (k + 1), boxedComplexDensity
        (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N l) t) x) +
      P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t x := by
  rw [P.finiteInnerClusterComplexSource_eq_sum_boxedLabels,
    P.finiteInnerClusterComplexSource_eq_sum_boxedLabels]
  funext x
  exact (Finset.sum_Ico_consecutive _ (Nat.add_le_add_right hjk 1) (Nat.add_le_add_right hkN 1)).symm

theorem physicalComplexSource_finiteDensity_eq_prefix_add_deep
    {s A₀ b R ρ : ℝ} (hs : s ≤ 0) (hR : 0 < R) (hRmax : R ≤ 1 / 2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N k : ℕ) (hkN : k ≤ N)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t : ℝ) :
    S.physicalComplexSource (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t = fun x =>
      (∑ l ∈ Finset.range (k + 1), boxedComplexDensity
        (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N l) t) x) +
      P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t x := by
  rw [P.physicalComplexSource_finiteDensity_eq_sum_labels hs hR hRmax hρ hρ1,
    P.finiteInnerClusterComplexSource_eq_sum_boxedLabels]
  funext x
  exact (Finset.sum_range_add_sum_Ico _ (Nat.add_le_add_right hkN 1)).symm

theorem velocityC_finiteInnerCluster_eq_middle_add_deep
    {s A₀ b R ρ : ℝ} (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N j k : ℕ) (hjk : j ≤ k) (hkN : k ≤ N)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t : ℝ) (x : ℂ) :
    velocityC (P.finiteInnerClusterComplexSource s A₀ b R ρ N j S t) x =
      (∑ l ∈ Finset.Ico (j + 1) (k + 1), velocityC (boxedComplexDensity
        (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N l) t)) x) +
      velocityC (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t) x := by
  rw [P.velocityC_finiteInnerClusterComplexSource_eq_sum hs hA hb hR hRmax hρ hρ1,
    P.velocityC_finiteInnerClusterComplexSource_eq_sum hs hA hb hR hRmax hρ hρ1]
  exact (Finset.sum_Ico_consecutive _ (Nat.add_le_add_right hjk 1) (Nat.add_le_add_right hkN 1)).symm

theorem actualTorusCorrection_finiteDensity_eq_prefix_add_deep
    {s A₀ b R ρ : ℝ} (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N k : ℕ) (hkN : k ≤ N) {f : Lp ℝ 2 μT} {T : ℝ}
    (S : BoundedEulerParticleSystem f T) (t : ℝ) (x : ℂ) :
    actualTorusCorrectionVelocity (S.physicalComplexSource
      (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t) x =
      (∑ l ∈ Finset.range (k + 1), actualTorusCorrectionVelocity (boxedComplexDensity
        (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N l) t)) x) +
      actualTorusCorrectionVelocity (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t) x := by
  have hi (l : ℕ) := (P.boxed_finitePeriodicLabel_bounds hs hA hb hR hRmax hρ hρ1 N l S t).1
  rw [P.physicalComplexSource_finiteDensity_eq_prefix_add_deep hs hR hRmax hρ hρ1 N k hkN S t,
    actualTorusCorrectionVelocity_add (integrable_finset_sum _ (fun l _ => hi l))
      (P.integrable_finiteInnerClusterComplexSource hs hA hb hR hRmax hρ hρ1 N k S t),
    actualTorusCorrectionVelocity_finset_sum _ _ (fun l _ => hi l)]

theorem correctionLabelField_finiteDensity_eq_prefix_add_deep
    {s A₀ b R ρ : ℝ} (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N k : ℕ) (hkN : k ≤ N) {f : Lp ℝ 2 μT} {T : ℝ}
    (S : BoundedEulerParticleSystem f T)
    (hwf : P.finiteInitialPeriodicDensity s A₀ b R ρ N =ᵐ[μT] (f : R2 → ℝ))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x : ℂ) :
    planeComplexEquiv (S.correctionLabelField t (complexTorusPoint x)) =
      (∑ l ∈ Finset.range (k + 1), actualTorusCorrectionVelocity (boxedComplexDensity
        (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N l) t)) x) +
      actualTorusCorrectionVelocity (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t) x := by
  rw [← S.actualTorusCorrectionVelocity_physicalComplexSource hwf ht]
  exact P.actualTorusCorrection_finiteDensity_eq_prefix_add_deep hs hA hb hR hRmax hρ hρ1 N k hkN S t x

end CircularMaterialTransferProfile
end Euler2D

end
