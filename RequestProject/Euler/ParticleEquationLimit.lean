module

public import RequestProject.Euler.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.ProjIcc

/-!
# Genuine limits and endpoint extensions of particle equations

The first bridge passes the actual fundamental-theorem integral identity
to a trajectory limit.  A clamped integral then extends a jointly
continuous limiting family to all real times, with genuine two-sided
derivatives even at the endpoints of the original closed time interval.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace Euler2D

section TrajectoryLimit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- FTC and dominated convergence retain the actual integral equation.
The derivative fields need only be almost-everywhere measurable and
uniformly bounded on the requested finite time interval. -/
theorem particle_integral_eq_of_tendsto {T M : ℝ} {a : E}
    {Xn : ℕ → ℝ → E} {X : ℝ → E} {gn : ℕ → ℝ → E} {g : ℝ → E}
    (hinit : ∀ n, Xn n 0 = a)
    (hderiv : ∀ n t, t ∈ Icc (0 : ℝ) T → HasDerivAt (Xn n) (gn n t) t)
    (hmeas : ∀ n, AEStronglyMeasurable (gn n) (volume.restrict (Icc (0 : ℝ) T)))
    (hbound : ∀ n, ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) T), ‖gn n s‖ ≤ M)
    (hgn : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) T),
      Tendsto (fun n => gn n s) atTop (𝓝 (g s)))
    (hX : ∀ t ∈ Icc (0 : ℝ) T, Tendsto (fun n => Xn n t) atTop (𝓝 (X t)))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    X t = a + ∫ s in (0 : ℝ)..t, g s := by
  have hsub : Ioc (0 : ℝ) t ⊆ Icc (0 : ℝ) T :=
    fun s hs => ⟨hs.1.le, hs.2.trans ht.2⟩
  have hmon : volume.restrict (Ioc (0 : ℝ) t) ≤ volume.restrict (Icc (0 : ℝ) T) :=
    Measure.restrict_mono hsub le_rfl
  have hgi (n : ℕ) : IntegrableOn (gn n) (Icc (0 : ℝ) T) :=
    Integrable.of_bound (hmeas n) M (hbound n)
  have hInt (n : ℕ) : IntervalIntegrable (gn n) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr ((hgi n).mono_set hsub)
  have hFTC (n : ℕ) : Xn n t = a + ∫ s in (0 : ℝ)..t, gn n s := by
    have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => hderiv n s (by
        have hs' : s ∈ Icc (0 : ℝ) t := by simpa only [uIcc_of_le ht.1] using hs
        exact ⟨hs'.1, hs'.2.trans ht.2⟩)) (hInt n)
    rw [hinit n] at hf
    rw [hf]
    abel
  have hint := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioc (0 : ℝ) t)) (F := gn) (f := g) (fun _ => M)
    (fun n => (hmeas n).mono_measure hmon) (integrable_const _)
    (fun n => (hbound n).filter_mono (ae_mono hmon)) (hgn.filter_mono (ae_mono hmon))
  have hint' : Tendsto (fun n => ∫ s in (0 : ℝ)..t, gn n s) atTop
      (𝓝 (∫ s in (0 : ℝ)..t, g s)) := by
    simpa only [intervalIntegral.integral_of_le ht.1] using hint
  have hleft : Tendsto (fun n => a + ∫ s in (0 : ℝ)..t, gn n s) atTop (𝓝 (X t)) :=
    (hX t ht).congr' (Eventually.of_forall hFTC)
  exact tendsto_nhds_unique hleft (hint'.const_add a)

/-- An integral identity gives the actual interior derivative of the
limiting trajectory, without assuming differentiability of the limit. -/
theorem hasDerivAt_of_particle_integral_eq {T : ℝ} {a : E} {X g : ℝ → E}
    (hg : Continuous g)
    (hInt : ∀ t ∈ Icc (0 : ℝ) T, X t = a + ∫ s in (0 : ℝ)..t, g s)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) : HasDerivAt X (g t) t := by
  have hp := intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 t)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  apply (hp.const_add a).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact hInt s ⟨hs.1.le, hs.2.le⟩

end TrajectoryLimit

section EndpointExtension

variable {T : ℝ}

/-- Continuous extension of the driver from its actual closed time domain. -/
def particleVelocityExtension (hT : 0 ≤ T) (v : Icc (0 : ℝ) T → R2 → R2)
    (t : ℝ) (x : R2) : R2 := v (projIcc 0 T hT t) x

/-- The derivative field along the original trajectory, frozen in time
beyond the endpoints. -/
def clampedParticleDerivative (hT : 0 ≤ T) (v X : Icc (0 : ℝ) T → R2 → R2)
    (s : ℝ) (a : R2) : R2 :=
  v (projIcc 0 T hT s) (X (projIcc 0 T hT s) a)

/-- An actual primitive, rather than a constant extension of a trajectory. -/
def particleIntegralExtension (hT : 0 ≤ T) (v X : Icc (0 : ℝ) T → R2 → R2)
    (t : ℝ) (a : R2) : R2 :=
  a + ∫ s in (0 : ℝ)..t, clampedParticleDerivative hT v X s a

theorem continuous_particleVelocityExtension (hT : 0 ≤ T)
    {v : Icc (0 : ℝ) T → R2 → R2} (hv : Continuous (Function.uncurry v)) :
    Continuous (Function.uncurry (particleVelocityExtension hT v)) :=
  hv.comp (((continuous_projIcc (h := hT)).comp continuous_fst).prodMk continuous_snd)

theorem continuous_clampedParticleDerivative (hT : 0 ≤ T)
    {v X : Icc (0 : ℝ) T → R2 → R2}
    (hv : Continuous (Function.uncurry v)) (hX : Continuous (Function.uncurry X)) :
    Continuous (Function.uncurry (clampedParticleDerivative hT v X)) := by
  have hc : Continuous (fun p : ℝ × R2 => (projIcc 0 T hT p.1, p.2)) :=
    ((continuous_projIcc (h := hT)).comp continuous_fst).prodMk continuous_snd
  exact hv.comp (((continuous_projIcc (h := hT)).comp continuous_fst).prodMk (hX.comp hc))

theorem continuous_particleIntegralExtension (hT : 0 ≤ T)
    {v X : Icc (0 : ℝ) T → R2 → R2}
    (hv : Continuous (Function.uncurry v)) (hX : Continuous (Function.uncurry X)) :
    Continuous (Function.uncurry (particleIntegralExtension hT v X)) := by
  have hc := continuous_clampedParticleDerivative hT hv hX
  have hparam : Continuous (Function.uncurry
      (fun p : ℝ × R2 => fun s : ℝ => clampedParticleDerivative hT v X s p.2)) :=
    hc.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst))
  exact continuous_snd.add
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (a₀ := 0) hparam continuous_fst)

@[simp] theorem particleIntegralExtension_zero (hT : 0 ≤ T)
    (v X : Icc (0 : ℝ) T → R2 → R2) (a : R2) :
    particleIntegralExtension hT v X 0 a = a := by
  simp only [particleIntegralExtension, intervalIntegral.integral_same, add_zero]

theorem particleIntegralExtension_eq (hT : 0 ≤ T)
    {v X : Icc (0 : ℝ) T → R2 → R2}
    (hInt : ∀ (t : Icc (0 : ℝ) T) a,
      X t a = a + ∫ s in (0 : ℝ)..(t : ℝ), clampedParticleDerivative hT v X s a)
    (t : Icc (0 : ℝ) T) (a : R2) :
    particleIntegralExtension hT v X t a = X t a := (hInt t a).symm

/-- The primitive has its genuine derivative at every real time. -/
theorem particleIntegralExtension_hasDerivAt (hT : 0 ≤ T)
    {v X : Icc (0 : ℝ) T → R2 → R2}
    (hv : Continuous (Function.uncurry v)) (hX : Continuous (Function.uncurry X))
    (t : ℝ) (a : R2) :
    HasDerivAt (fun s => particleIntegralExtension hT v X s a)
      (clampedParticleDerivative hT v X t a) t := by
  have hc : Continuous (fun s => clampedParticleDerivative hT v X s a) :=
    (continuous_clampedParticleDerivative hT hv hX).comp
      (continuous_id.prodMk continuous_const)
  have hp := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  exact hp.const_add a

/-- This is the original particle ODE on the entire closed time interval,
including its two endpoints. -/
theorem particleIntegralExtension_hasDerivAt_on_Icc (hT : 0 ≤ T)
    {v X : Icc (0 : ℝ) T → R2 → R2}
    (hv : Continuous (Function.uncurry v)) (hX : Continuous (Function.uncurry X))
    (hInt : ∀ (t : Icc (0 : ℝ) T) a,
      X t a = a + ∫ s in (0 : ℝ)..(t : ℝ), clampedParticleDerivative hT v X s a)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (a : R2) :
    HasDerivAt (fun s => particleIntegralExtension hT v X s a)
      (particleVelocityExtension hT v t (particleIntegralExtension hT v X t a)) t := by
  have hclamp : projIcc 0 T hT t = (⟨t, ht⟩ : Icc (0 : ℝ) T) := by
    exact Subtype.ext (congrArg Subtype.val (projIcc_of_mem hT ht))
  have heq := particleIntegralExtension_eq hT hInt (⟨t, ht⟩ : Icc (0 : ℝ) T) a
  have hd := particleIntegralExtension_hasDerivAt hT hv hX t a
  simpa only [clampedParticleDerivative, particleVelocityExtension, hclamp, heq] using hd

end EndpointExtension

end Euler2D

end
