import CubeSections.Geometry.CentralDomination

/-! Functional Prékopa--Leindler statements used in the Brunn--Minkowski proof.
These definitions separate the one-dimensional and Gaussian-dominated inputs. -/
noncomputable section
open Set MeasureTheory
namespace CubeSections

def GaussianDominated {n : ℕ} (f : E n → ℝ) : Prop :=
  ∃ C a : ℝ, 0 < C ∧ 0 < a ∧ ∀ x, |f x| ≤ C * Real.exp (-a * ‖x‖^2)

def PositiveGaussianPrekopa (n : ℕ) : Prop :=
  ∀ t : ℝ, 0 < t → t < 1 → ∀ f g h : E n → ℝ,
    Continuous f → Continuous g → Continuous h →
    (∀ x, 0 < f x) → (∀ x, 0 < g x) → (∀ x, 0 < h x) →
    GaussianDominated f → GaussianDominated g → GaussianDominated h →
    (∀ x y, (f x)^(1-t) * (g y)^t ≤ h ((1-t) • x + t • y)) →
    (∫ x, f x)^(1-t) * (∫ x, g x)^t ≤ ∫ x, h x

def weightedMinkowski {n : ℕ} (t : ℝ) (A B : Set (E n)) : Set (E n) :=
  (fun p : E n × E n => (1-t) • p.1 + t • p.2) '' (A ×ˢ B)

def CompactMultiplicativeBM (n : ℕ) : Prop :=
  ∀ t : ℝ, 0 < t → t < 1 → ∀ A B : Set (E n),
    IsCompact A → IsCompact B → Convex ℝ A → Convex ℝ B → A.Nonempty → B.Nonempty →
    ((volume A).toReal)^(1-t) * ((volume B).toReal)^t ≤
      (volume (weightedMinkowski t A B)).toReal

theorem weightedMinkowski_compact {n : ℕ} (t : ℝ) {A B : Set (E n)}
    (hA : IsCompact A) (hB : IsCompact B) : IsCompact (weightedMinkowski t A B) :=
  (hA.prod hB).image (by fun_prop)

theorem weightedMinkowski_nonempty {n : ℕ} (t : ℝ) {A B : Set (E n)}
    (hA : A.Nonempty) (hB : B.Nonempty) : (weightedMinkowski t A B).Nonempty :=
  (hA.prod hB).image _

theorem weightedMinkowski_half {n : ℕ} (A B : Set (E n)) :
    weightedMinkowski (1/2 : ℝ) A B = midpointMinkowski A B := by
  unfold weightedMinkowski midpointMinkowski
  congr 1
  funext p
  norm_num [smul_add]

end CubeSections
