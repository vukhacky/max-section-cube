import CubeSections.Classical.CubeCharacteristic
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Pointwise Fourier inversion for a genuine density of a cube projection.
The geometric density identity and L1 sinc-product hypothesis are explicit;
the Fourier normalization and value at the central continuity point are proved.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators RealInnerProductSpace FourierTransform

namespace CubeSections

def cubeSincKernel (W : Frame n d) (t : E d) : ℝ :=
  ∏ i : Fin n, Real.sinc (Real.pi*(W t) i)

def cubeAbsSincKernel (W : Frame n d) (t : E d) : ℝ :=
  ∏ i : Fin n, |Real.sinc (Real.pi*(W t) i)|

theorem abs_cubeSincKernel (W : Frame n d) (t : E d) :
    |cubeSincKernel W t| = cubeAbsSincKernel W t := by
  simp only [cubeSincKernel, cubeAbsSincKernel, Finset.abs_prod]

theorem continuous_cubeSincKernel (W : Frame n d) : Continuous (cubeSincKernel W) := by
  unfold cubeSincKernel
  fun_prop

theorem integrable_cubeSincKernel_of_abs (W : Frame n d)
    (habs : Integrable (cubeAbsSincKernel W)) : Integrable (cubeSincKernel W) := by
  apply habs.mono' (continuous_cubeSincKernel W).aestronglyMeasurable
  exact ae_of_all _ (fun t => by rw [Real.norm_eq_abs, abs_cubeSincKernel])

theorem fourier_nonnegative_density_eq_charFun {d : ℕ} (f : E d → ℝ)
    (hmeas : Measurable f) (hpos : ∀ x, 0 ≤ f x) (t : E d) :
    𝓕 (fun x => (f x : ℂ)) t =
      charFun (volume.withDensity (fun x => ENNReal.ofReal (f x))) ((-2*Real.pi) • t) := by
  rw [Real.fourier_eq', charFun_apply,
    integral_withDensity_eq_integral_toReal_smul hmeas.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    dsimp only
    rw [ENNReal.toReal_ofReal (hpos x), inner_smul_right, Complex.real_smul]
    simp only [smul_eq_mul]
    rw [mul_comm (f x : ℂ)])

theorem fourier_cube_density_eq_sinc (W : Frame n d) (f : E d → ℝ)
    (hmeas : Measurable f) (hpos : ∀ x, 0 ≤ f x)
    (hdensity : (cubeUniformMeasure n).map (frameAdjoint W) =
      volume.withDensity (fun x => ENNReal.ofReal (f x))) (t : E d) :
    𝓕 (fun x => (f x : ℂ)) t = (cubeSincKernel W t : ℂ) := by
  rw [fourier_nonnegative_density_eq_charFun f hmeas hpos, ← hdensity,
    charFun_projectedCube_neg_two_pi]
  simp only [cubeSincKernel]
  push_cast
  rfl

/-- A.e. density information is combined with continuity of the specified
representative at zero; no pointwise value is inferred from a.e. equality alone. -/
theorem cube_density_zero_eq_sincIntegral (W : Frame n d) (f : E d → ℝ)
    (hmeas : Measurable f) (hpos : ∀ x, 0 ≤ f x) (hf : Integrable f)
    (hcont : ContinuousAt f 0)
    (hdensity : (cubeUniformMeasure n).map (frameAdjoint W) =
      volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (habs : Integrable (cubeAbsSincKernel W)) :
    f 0 = ∫ t : E d, cubeSincKernel W t := by
  have hker := integrable_cubeSincKernel_of_abs W habs
  have hF : 𝓕 (fun x => (f x : ℂ)) = fun t => (cubeSincKernel W t : ℂ) := by
    funext t
    exact fourier_cube_density_eq_sinc W f hmeas hpos hdensity t
  have hFi : Integrable (𝓕 (fun x => (f x : ℂ))) := by
    rw [hF]
    exact hker.ofReal
  have hfc : Integrable (fun x => (f x : ℂ)) := hf.ofReal
  have hzero : ContinuousAt (fun x => (f x : ℂ)) 0 :=
    Complex.continuous_ofReal.continuousAt.comp hcont
  have hinv := hfc.fourierInv_fourier_eq hFi hzero
  rw [Real.fourierInv_eq', hF] at hinv
  simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_smul] at hinv
  rw [integral_complex_ofReal] at hinv
  exact (Complex.ofReal_injective hinv).symm

theorem cube_density_zero_le_absSincIntegral (W : Frame n d) (f : E d → ℝ)
    (hmeas : Measurable f) (hpos : ∀ x, 0 ≤ f x) (hf : Integrable f)
    (hcont : ContinuousAt f 0)
    (hdensity : (cubeUniformMeasure n).map (frameAdjoint W) =
      volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (habs : Integrable (cubeAbsSincKernel W)) :
    f 0 ≤ ∫ t : E d, cubeAbsSincKernel W t := by
  rw [cube_density_zero_eq_sincIntegral W f hmeas hpos hf hcont hdensity habs]
  apply integral_mono (integrable_cubeSincKernel_of_abs W habs) habs
  intro t
  rw [← abs_cubeSincKernel]
  exact le_abs_self _

#print axioms fourier_cube_density_eq_sinc
#print axioms cube_density_zero_eq_sincIntegral
#print axioms cube_density_zero_le_absSincIntegral
end CubeSections
