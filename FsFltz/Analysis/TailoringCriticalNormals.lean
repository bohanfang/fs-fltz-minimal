import FsFltz.Analysis.TailoringCriticalDifferential

/-!
# Uniform noncancellation of the actual retained tailored normal

Source: `geometric-part-fsf-proof.tex`, `eq:Gchi`, lines 1343–1352.
The retained cutoffs determine the support; the finite-input proper-face
noncancellation theorem then gives a lower bound. The resulting relative
tangent estimate is a direct consumer of this bound and of the exact
cutoff-error differential, rather than an assumed tangent-plane certificate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set
open scoped BigOperators

variable {n : ℕ}

/-- The source's actual complex retained normal `Gχ = ∑ χᵥ mᵥ v`. -/
def tailoringRetainedNormal (I : ToricInput n) (β : ℝ) (y : LGSpace n) : Fin n → ℂ :=
  ∑ v ∈ I.vertices, tailoringRetainedMonomial I β v y • latticeComplex v

/-- Outside a support containing all retained vertices, every actual
retained coefficient vanishes exactly. -/
theorem tailoringRetainedMonomial_eq_zero_of_not_mem_support
    (I : ToricInput n) (β : ℝ) (y : LGSpace n)
    {s : Finset (Lattice n)} (hs : tailoringRetainedVertices I β y.1 ⊆ s)
    {v : Lattice n} (hv : v ∈ I.vertices) (hvs : v ∉ s) :
    tailoringRetainedMonomial I β v y = 0 := by
  have hχ : tailoringCutoff I β v y.1 = 0 := by
    apply le_antisymm _ (tailoringCutoff_nonneg I β v y.1)
    by_contra! hp
    exact hvs (hs ((mem_tailoringRetainedVertices_iff I β y.1 v).mpr ⟨hv, hp⟩))
  simp only [tailoringRetainedMonomial, hχ, Complex.ofReal_zero, zero_mul]

/-- The literal full normal equals the complex vertex sum on every actual
containing face, with exactly the cutoff-weighted coefficients. -/
theorem tailoringRetainedNormal_eq_face_sum (I : ToricInput n) (β : ℝ)
    (y : LGSpace n) {s : Finset (Lattice n)} (hs : s ⊆ I.vertices)
    (hret : tailoringRetainedVertices I β y.1 ⊆ s) :
    tailoringRetainedNormal I β y = complexVertexSum s
      (fun v => tailoringRetainedMonomial I β v.val y) := by
  rw [tailoringRetainedNormal, complexVertexSum,
    Finset.sum_coe_sort s (fun v => tailoringRetainedMonomial I β v y • latticeComplex v)]
  symm
  apply Finset.sum_subset hs
  intro v hv hvs
  rw [tailoringRetainedMonomial_eq_zero_of_not_mem_support I β y hret hv hvs, zero_smul]

/-- A uniform upper bound in the actual coordinate supremum norm. -/
theorem norm_tailoringRetainedNormal_le (I : ToricInput n) (β : ℝ)
    (y : LGSpace n) :
    ‖tailoringRetainedNormal I β y‖ ≤
      (∑ v ∈ I.vertices, ‖latticeComplex v‖) * Real.exp (supportHeight I y.1 - β) := by
  calc
    _ ≤ ∑ v ∈ I.vertices, ‖tailoringRetainedMonomial I β v y • latticeComplex v‖ :=
      norm_sum_le _ _
    _ ≤ ∑ v ∈ I.vertices, ‖latticeComplex v‖ * Real.exp (supportHeight I y.1 - β) := by
      apply Finset.sum_le_sum
      intro v hv
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_right
        (norm_tailoringRetainedMonomial_le_max I β v hv y) (norm_nonneg _)).trans_eq
          (mul_comm _ _)
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- From the finite toric input, one positive constant bounds the exact
retained normal below by the largest monomial on every large endpoint fiber. -/
theorem tailoringEndpoint_exists_uniform_retainedNormal_lower_bound (I : ToricInput n) :
    ∃ c : ℝ, 0 < c ∧ ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      ∀ y : LGSpace n, tailoringFamily I β 1 y = 1 →
      c * Real.exp (supportHeight I y.1 - β) ≤ ‖tailoringRetainedNormal I β y‖ := by
  obtain ⟨c, hc, hnoncancel⟩ := I.uniform_complex_face_lowerBound
  obtain ⟨B, hB, hsupport⟩ := I.exists_tailoringRetainedVertices_face
  let L := Real.log (I.vertices.card : ℝ)
  let β₀ := max B (L ^ 2)
  refine ⟨c, hc, β₀, hB.trans_le (le_max_left _ _), fun β hβ y hy => ?_⟩
  have hBβ : B ≤ β := (le_max_left _ _).trans hβ
  have hβnonneg : 0 ≤ β := (sq_nonneg L).trans ((le_max_right _ _).trans hβ)
  have hLβ : L ≤ Real.sqrt β :=
    (le_abs_self L).trans (by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt ((le_max_right _ _).trans hβ))
  obtain ⟨s, hs, hsne, hsproper, hret⟩ := hsupport β hBβ y.1
  obtain ⟨v, hv⟩ := I.supportHeight_attained y.1
  have hχ := tailoringEndpoint_maximizing_cutoff_eq_one I β y hy hLβ v hv
  have hvret : v.val ∈ tailoringRetainedVertices I β y.1 :=
    (mem_tailoringRetainedVertices_iff I β y.1 v.val).mpr
      ⟨v.property, by rw [hχ]; norm_num⟩
  let γ : {v : Lattice n // v ∈ s} → ℂ :=
    fun w => tailoringRetainedMonomial I β w.val y
  let w : {v : Lattice n // v ∈ s} := ⟨v.val, hret hvret⟩
  have hcoeff : Real.exp (supportHeight I y.1 - β) ≤ ‖γ‖ := by
    have he : ‖γ w‖ = Real.exp (supportHeight I y.1 - β) := by
      dsimp [γ, w, tailoringRetainedMonomial]
      rw [hχ, Complex.ofReal_one, one_mul, norm_tailoring_monomial I β v y,
        tailoringWeight_vertex I β v, hv]
    rw [← he]
    exact norm_le_pi_norm γ w
  have hface := hnoncancel s hs hsne hsproper γ
  rw [← tailoringRetainedNormal_eq_face_sum I β y hs.1 hret] at hface
  exact (mul_le_mul_of_nonneg_left hcoeff hc.le).trans hface

/-- Uniform comparability of the actual retained normal with `M`, with all
constants chosen from the original finite toric input. -/
theorem tailoringEndpoint_exists_uniform_retainedNormal_bounds (I : ToricInput n) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β ≥ β₀, ∀ y : LGSpace n, tailoringFamily I β 1 y = 1 →
        c * Real.exp (supportHeight I y.1 - β) ≤ ‖tailoringRetainedNormal I β y‖ ∧
        ‖tailoringRetainedNormal I β y‖ ≤ C * Real.exp (supportHeight I y.1 - β) := by
  obtain ⟨c, hc, B, hB, hlower⟩ := tailoringEndpoint_exists_uniform_retainedNormal_lower_bound I
  let C := 1 + ∑ v ∈ I.vertices, ‖latticeComplex v‖
  have hsum : 0 ≤ ∑ v ∈ I.vertices, ‖latticeComplex v‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨c, hc, C, by dsimp [C]; linarith, B, hB, fun β hβ y hy => ?_⟩
  refine ⟨hlower β hβ y hy, (norm_tailoringRetainedNormal_le I β y).trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  dsimp [C]
  linarith

/-- The leading complex normal is nonzero everywhere on every sufficiently
large full endpoint fiber. -/
theorem tailoringEndpoint_exists_uniform_retainedNormal_ne_zero (I : ToricInput n) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀, ∀ y : LGSpace n,
      tailoringFamily I β 1 y = 1 → tailoringRetainedNormal I β y ≠ 0 := by
  obtain ⟨c, hc, B, hB, hlower⟩ := tailoringEndpoint_exists_uniform_retainedNormal_lower_bound I
  refine ⟨B, hB, fun β hβ y hy => ?_⟩
  exact norm_pos_iff.mp ((mul_pos hc (Real.exp_pos _)).trans_le (hlower β hβ y hy))

/-- The actual endpoint tangent vectors have exponentially small leading
normal defect relative to the nonvanishing retained normal. -/
theorem tailoringEndpoint_exists_uniform_relative_tangent_error (I : ToricInput n) :
    ∃ C : ℝ, 0 < C ∧ ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      ∀ x : TangentCoordinates n, tailoringFamily I β 1 (lgCover x) = 1 →
      ∀ v : TangentCoordinates n,
      fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x v = 0 →
      ‖tailoringLeadingDifferential I β (lgCover x) v‖ ≤
        C * Real.exp (-Real.sqrt β) * ‖tailoringRetainedNormal I β (lgCover x)‖ * ‖v‖ := by
  obtain ⟨c, hc, B, hB, hlower⟩ := tailoringEndpoint_exists_uniform_retainedNormal_lower_bound I
  obtain ⟨D, hD, herror⟩ := tailoringEndpoint_exists_uniform_tangent_error_bound I
  refine ⟨D / c, div_pos hD hc, B, hB, fun β hβ x hx v hv => ?_⟩
  have hM : Real.exp (supportHeight I x.1 - β) ≤
      ‖tailoringRetainedNormal I β (lgCover x)‖ / c := by
    apply (le_div_iff₀ hc).mpr
    simpa only [mul_comm, lgCover] using hlower β hβ (lgCover x) hx
  calc
    _ ≤ D * Real.exp (-Real.sqrt β) * Real.exp (supportHeight I x.1 - β) * ‖v‖ :=
      herror β x hx v hv
    _ ≤ D * Real.exp (-Real.sqrt β) *
        (‖tailoringRetainedNormal I β (lgCover x)‖ / c) * ‖v‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hM (mul_pos hD (Real.exp_pos _)).le) (norm_nonneg _)
    _ = _ := by ring

end FsFltz
