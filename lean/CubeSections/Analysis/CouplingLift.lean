import CubeSections.Semantics
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith

/-! Orthogonal lifting of a quadratic transport cost. The existence of the transport
coupling and the entropy decomposition remain separate hypotheses. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace CubeSections

def frameAdjoint {n k : ℕ} (U : Frame n k) : E n →L[ℝ] E k :=
  U.toContinuousLinearMap.adjoint

def frameResidual {n k : ℕ} (U : Frame n k) (b : E n) : E n :=
  b - U (frameAdjoint U b)

theorem frameAdjoint_apply_frame {n k : ℕ} (U : Frame n k) (x : E k) :
    frameAdjoint U (U x) = x := by
  change (U.toContinuousLinearMap.adjoint ∘L U.toContinuousLinearMap) x = x
  rw [U.adjoint_comp_self]
  rfl

theorem frameResidual_inner_frame {n k : ℕ} (U : Frame n k) (b : E n) (x : E k) :
    ⟪frameResidual U b, U x⟫_ℝ = 0 := by
  rw [frameResidual, inner_sub_left, U.inner_map_map]
  exact sub_eq_zero.mpr (ContinuousLinearMap.adjoint_inner_left U.toContinuousLinearMap x b).symm

/-- Pointwise Pythagorean identity underlying the lifted coupling. -/
theorem frame_coupling_lift_identity {n k : ℕ} (U : Frame n k) (b : E n) (g : E k) :
    ‖b - U g‖ ^ 2 = ‖frameResidual U b‖ ^ 2 + ‖frameAdjoint U b - g‖ ^ 2 := by
  have hvec : b - U g = frameResidual U b + U (frameAdjoint U b - g) := by
    rw [frameResidual, U.map_sub]
    abel
  rw [hvec, norm_add_sq_real, frameResidual_inner_frame, U.norm_map]
  ring

theorem frame_residual_norm_sq {n k : ℕ} (U : Frame n k) (b : E n) :
    ‖frameResidual U b‖ ^ 2 = ‖b‖ ^ 2 - ‖frameAdjoint U b‖ ^ 2 := by
  have h := frame_coupling_lift_identity U b 0
  simp only [map_zero, sub_zero] at h
  linarith

/-- Exact integrated lifting, under the two necessary integrability hypotheses. -/
theorem integral_frame_coupling_lift {n k : ℕ} (U : Frame n k)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (b : Ω → E n) (g : Ω → E k)
    (hres : Integrable (fun ω => ‖frameResidual U (b ω)‖ ^ 2) μ)
    (herr : Integrable (fun ω => ‖frameAdjoint U (b ω) - g ω‖ ^ 2) μ) :
    (∫ ω, ‖b ω - U (g ω)‖ ^ 2 ∂μ) =
      (∫ ω, ‖frameResidual U (b ω)‖ ^ 2 ∂μ) +
      (∫ ω, ‖frameAdjoint U (b ω) - g ω‖ ^ 2 ∂μ) := by
  calc
    _ = ∫ ω, (‖frameResidual U (b ω)‖ ^ 2 + ‖frameAdjoint U (b ω) - g ω‖ ^ 2) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => frame_coupling_lift_identity U (b ω) (g ω))
    _ = _ := integral_add hres herr

/-- Once the entropy decomposition and a Talagrand-cost coupling are supplied,
this theorem performs the exact orthogonal lift, retaining the production term. -/
theorem integral_frame_coupling_lift_le {n k : ℕ} (U : Frame n k)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (b : Ω → E n) (g : Ω → E k)
    (hres : Integrable (fun ω => ‖frameResidual U (b ω)‖ ^ 2) μ)
    (herr : Integrable (fun ω => ‖frameAdjoint U (b ω) - g ω‖ ^ 2) μ)
    (D J δ : ℝ)
    (hdecomp : δ = D + J + (1 / 2 : ℝ) * (∫ ω, ‖frameResidual U (b ω)‖ ^ 2 ∂μ))
    (hcost : (∫ ω, ‖frameAdjoint U (b ω) - g ω‖ ^ 2 ∂μ) ≤ 2 * D) :
    (∫ ω, ‖b ω - U (g ω)‖ ^ 2 ∂μ) ≤ 2 * (δ - J) := by
  rw [integral_frame_coupling_lift U μ b g hres herr]
  linarith

end CubeSections
