module

public import RequestProject.Euler.Laplace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The original retarded integral is a strong scalar solution when
the original moment is continuous. Its derivative follows from the
actual improper integral, not an extra ODE hypothesis. -/

@[expose] public section

set_option maxHeartbeats 8000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set Filter Topology MeasureTheory

namespace Euler2D

theorem hasDerivAt_retardedSol_of_continuous {σ : ℝ} {N : ℝ → ℂ}
    (hN : ExpWindow σ N) (hNc : Continuous N) {z : ℂ}
    (h0 : 0 < z.re) (h1 : z.re < σ) (c K : ℂ) (t : ℝ) :
    HasDerivAt (retardedSol c z K N)
      (c * retardedSol c z K N t + K * Complex.exp (-(z - c) * (t : ℂ)) * N t) t := by
  let g : ℝ → ℂ := fun s => Complex.exp (-z * (s : ℂ)) * N s
  let F : ℝ → ℂ := fun s => ∫ u in Iic s, g u
  have hg : Integrable g := hN.integrable_exp h0 h1
  have hgc : Continuous g := by dsimp only [g]; fun_prop
  have hFfun : F = fun s => (∫ u in Iic (0 : ℝ), g u) + ∫ u in (0 : ℝ)..s, g u := by
    funext s
    have hh := intervalIntegral.integral_Iic_sub_Iic (f := g) (μ := volume)
      hg.integrableOn hg.integrableOn (a := (0 : ℝ)) (b := s)
    change (∫ u in Iic s, g u) = _
    calc
      _ = ((∫ u in Iic s, g u) - ∫ u in Iic (0 : ℝ), g u) + ∫ u in Iic (0 : ℝ), g u := by ring
      _ = _ := by rw [hh]; ring
  have hFd : HasDerivAt F (g t) t := by
    rw [hFfun]
    exact (intervalIntegral.integral_hasDerivAt_right (hgc.intervalIntegrable 0 t)
      hgc.aestronglyMeasurable.stronglyMeasurableAtFilter hgc.continuousAt).const_add _
  have hEd : HasDerivAt (fun s : ℝ => Complex.exp (c * (s : ℂ)))
      (c * Complex.exp (c * (t : ℂ))) t := by
    have hh := (((hasDerivAt_id t).ofReal_comp).const_mul c).cexp
    simpa only [id_eq, Complex.ofReal_one, mul_one, mul_comm] using hh
  have hd := (hEd.const_mul K).mul hFd
  change HasDerivAt (retardedSol c z K N)
    ((K * (c * Complex.exp (c * (t : ℂ)))) * F t +
      (K * Complex.exp (c * (t : ℂ))) * g t) t at hd
  have hphase : Complex.exp (c * (t : ℂ)) * Complex.exp (-z * (t : ℂ)) =
      Complex.exp (-(z - c) * (t : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  convert hd using 1
  rw [retardedSol, ← hphase]
  dsimp only [F, g]
  ring

theorem continuous_retardedSol_of_continuous {σ : ℝ} {N : ℝ → ℂ}
    (hN : ExpWindow σ N) (hNc : Continuous N) {z : ℂ}
    (h0 : 0 < z.re) (h1 : z.re < σ) (c K : ℂ) : Continuous (retardedSol c z K N) :=
  continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_retardedSol_of_continuous hN hNc h0 h1 c K t).continuousAt

end Euler2D

end
