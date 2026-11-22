import CubeSections.Certificates.HalfAngle
import CubeSections.Certificates.AngleSoundness

noncomputable section
namespace CubeSections.Certificates

/-- The real direct strip law in terms of its normalized scale `α`. -/
def DirectStripLaw (L R α t C : ℝ) : Prop :=
  L ^ 2 / (2 * R * (1 - α * sineReal t) ^ 2) ≤
    t + C / 8 * sineReal t ^ 3

/-- A source strip law implies the weaker rectangle profile inequality.
All bounds are quantitative; none is the desired angular comparison. -/
theorem directStripLaw_implies_profile_bound
    {L A R B α η t T C D : ℝ}
    (hA₀ : 0 ≤ A) (hAL : A ≤ L) (hR : 0 < R) (hRB : R ≤ B)
    (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1 / 2)
    (hη₀ : 0 ≤ η) (hηα : η ≤ α)
    (ht : 0 ≤ t) (htT : t ≤ T) (hT : T ≤ 1)
    (hD : 0 ≤ D) (hDC : D ≤ C)
    (hlaw : DirectStripLaw L R α t D) :
    A ^ 2 ≤ 2 * B * (1 + C * sineReal T ^ 2 / 4) * stripProfile η t := by
  have hB : 0 < B := hR.trans_le hRB
  have hL : 0 ≤ L := hA₀.trans hAL
  have hC : 0 ≤ C := hD.trans hDC
  have hT₀ : 0 ≤ T := ht.trans htT
  have ht₁ : t ≤ 1 := htT.trans hT
  have hu₀ : 0 ≤ sineReal t := sineReal_nonneg ht
  have hU₀ : 0 ≤ sineReal T := sineReal_nonneg hT₀
  have huU : sineReal t ≤ sineReal T :=
    sineReal_monotoneOn ⟨ht, ht₁⟩ ⟨hT₀, hT⟩ htT
  have hu₂ : sineReal t ≤ 2 * t := sineReal_le_twice ht
  have hu₁ : sineReal t ≤ 1 := sineReal_le_one t
  have hαu : α * sineReal t ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_left hu₁ hα₀
    nlinarith
  have hηu : η * sineReal t ≤ α * sineReal t :=
    mul_le_mul_of_nonneg_right hηα hu₀
  have hfα : 0 < 1 - α * sineReal t := by linarith
  have hfη : 0 < 1 - η * sineReal t := by linarith
  have hsquares : (1 - α * sineReal t) ^ 2 ≤ (1 - η * sineReal t) ^ 2 :=
    (sq_le_sq₀ hfα.le hfη.le).mpr (by linarith)
  have hsq : A ^ 2 ≤ L ^ 2 := (sq_le_sq₀ hA₀ hL).mpr hAL
  have hlower : A ^ 2 / (2 * B) ≤ L ^ 2 / (2 * R) := by
    calc
      A ^ 2 / (2 * B) ≤ L ^ 2 / (2 * B) :=
        div_le_div_of_nonneg_right hsq (by positivity)
      _ ≤ L ^ 2 / (2 * R) := by
        apply div_le_div_of_nonneg_left (sq_nonneg L) (by positivity)
        linarith
  have hlaw' : L ^ 2 / (2 * R) ≤
      (t + D / 8 * sineReal t ^ 3) * (1 - α * sineReal t) ^ 2 := by
    unfold DirectStripLaw at hlaw
    have h := (div_le_iff₀ (by positivity :
      (0 : ℝ) < 2 * R * (1 - α * sineReal t) ^ 2)).mp hlaw
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * R)).mpr
    nlinarith
  have htail : t + D / 8 * sineReal t ^ 3 ≤
      t * (1 + C * sineReal T ^ 2 / 4) := by
    have hp : D * sineReal t ^ 2 ≤ C * sineReal T ^ 2 :=
      mul_le_mul hDC ((sq_le_sq₀ hu₀ hU₀).mpr huU) (sq_nonneg _) hC
    have hp' := mul_le_mul_of_nonneg_right hp hu₀
    have hp'' := mul_le_mul_of_nonneg_left hu₂ (show 0 ≤ C * sineReal T ^ 2 by positivity)
    nlinarith
  have hcomp : (t + D / 8 * sineReal t ^ 3) * (1 - α * sineReal t) ^ 2 ≤
      t * (1 + C * sineReal T ^ 2 / 4) * (1 - η * sineReal t) ^ 2 := by
    exact mul_le_mul htail hsquares (sq_nonneg _) (by positivity)
  have hall := hlower.trans (hlaw'.trans hcomp)
  have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * B)).mp hall
  unfold stripProfile
  nlinarith

/-- A strict rational-style strip test excludes all smaller half angles. -/
theorem strip_test_excludes_le
    {A B η C T t : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hη : 0 ≤ η) (hη₁ : η ≤ 1 / 2)
    (hnecessary : A ^ 2 ≤ 2 * B * (1 + C * sineReal T ^ 2 / 4) * stripProfile η t)
    (htest : 2 * B * T * (1 + C * sineReal T ^ 2 / 4) *
      (1 - η * sineReal T) ^ 2 < A ^ 2) : T < t := by
  by_contra h
  have hle : t ≤ T := le_of_not_gt h
  have hm := stripProfile_monotone hη hη₁ hle
  have hscale : 0 ≤ 2 * B * (1 + C * sineReal T ^ 2 / 4) := by positivity
  have hh := mul_le_mul_of_nonneg_left hm hscale
  unfold stripProfile at hnecessary hh
  nlinarith

/-- Combination of the source strip law with a successful rectangular strip test. -/
theorem directStripLaw_excluded
    {L A R B α η t T C D : ℝ}
    (hA₀ : 0 ≤ A) (hAL : A ≤ L) (hR : 0 < R) (hRB : R ≤ B)
    (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1 / 2)
    (hη₀ : 0 ≤ η) (hηα : η ≤ α)
    (ht : 0 ≤ t) (htT : t ≤ T) (hT : T ≤ 1)
    (hD : 0 ≤ D) (hDC : D ≤ C)
    (hlaw : DirectStripLaw L R α t D)
    (htest : 2 * B * T * (1 + C * sineReal T ^ 2 / 4) *
      (1 - η * sineReal T) ^ 2 < A ^ 2) : False := by
  have hnecessary := directStripLaw_implies_profile_bound
    hA₀ hAL hR hRB hα₀ hα₁ hη₀ hηα ht htT hT hD hDC hlaw
  have hh := strip_test_excludes_le (hR.trans_le hRB).le (hD.trans hDC)
    hη₀ (hηα.trans hα₁) hnecessary htest
  exact (not_lt_of_ge htT) hh

#print axioms directStripLaw_implies_profile_bound
#print axioms directStripLaw_excluded

end CubeSections.Certificates
