import FsFltz.Geometry.IntrinsicCollarGluingSmooth

/-!
# Smooth native inclusions in the attached carrier

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. The quotient atlas is the constructed mixed atlas. Smoothness
of the original inclusion across the seam uses the same produced inverse
germ, and is not a hypothesis on a supplied extension manifold.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCollarGluing

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {δ : ℝ} (hδ : 0 < δ)
  (C : ℝ × IntrinsicBoundary.Point k M → M)
  (hemb : IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val))
  (hC : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ C
    (Half δ (IntrinsicBoundary.Point k M)))
  (hboundary : ∀ p : Half δ (IntrinsicBoundary.Point k M),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C p.val) ↔ p.val.1 = 0)
  (hinv : ∀ p ∈ Half δ (IntrinsicBoundary.Point k M),
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C q) = q)
  (hzero : ∀ b : IntrinsicBoundary.Point k M, C (0, b) = b.val)

local instance : ChartedSpace (Model (k + 1)) (Band δ (IntrinsicBoundary.Point k M)) :=
  bandChartedSpace δ

local instance : IsManifold 𝓘(ℝ, Model (k + 1)) ∞ (Band δ (IntrinsicBoundary.Point k M)) :=
  band_isManifold δ

include hC hinv

/-- Smoothness of the literal interior patch in the constructed atlas. -/
theorem contMDiff_interiorIn :
    letI := extensionChartedSpace hδ C hemb hboundary hzero
    ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞
      (interiorIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) :=
  contMDiff_openCover_inclusion _ _ (native_open_cover hδ C hzero)
    (extension_isManifold hδ C hemb hC hboundary hinv hzero)

/-- Smoothness of the full two-sided cylinder patch in that same atlas. -/
theorem contMDiff_cylinder :
    letI := extensionChartedSpace hδ C hemb hboundary hzero
    ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞
      (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) :=
  contMDiff_openCover_inclusion_right _ _ (native_open_cover hδ C hzero)
    (extension_isManifold hδ C hemb hC hboundary hinv hzero)

/-- An actual smooth inverse germ of the cylinder, derived from its pushed chart. -/
theorem cylinder_inverse_germ (p : Band δ (IntrinsicBoundary.Point k M)) :
    letI := extensionChartedSpace hδ C hemb hboundary hzero
    ∃ g : Extension (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) →
      Band δ (IntrinsicBoundary.Point k M),
      ContMDiffAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ g
        (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) p) ∧
        g (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) p) = p ∧
          ∀ᶠ z in 𝓝 (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) p),
            cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) (g z) = z := by
  let := extensionChartedSpace hδ C hemb hboundary hzero
  let := extension_isManifold hδ C hemb hC hboundary hinv hzero
  apply smooth_inverse_germ_of_lifted_chart
    (isOpenEmbedding_cylinder hδ
      (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) hemb) p
  apply IsManifold.subset_maximalAtlas
  exact Or.inr ⟨chartAt (Model (k + 1)) p, chart_mem_atlas _ p, rfl⟩

omit hC hinv in
/-- A total lift of original points into the native interior, near a given interior point. -/
def interiorLift (u : IntrinsicInterior.Point k M) : M → IntrinsicInterior.Point k M := by
  classical
  exact fun x => if hx : (𝓡∂ (k + 1)).IsInteriorPoint x then ⟨x, hx⟩ else u

omit hC hinv in
theorem interiorLift_val_eventually (u : IntrinsicInterior.Point k M) :
    Subtype.val ∘ interiorLift u =ᶠ[𝓝 u.val] id := by
  filter_upwards [IntrinsicInterior.isOpen_interior.mem_nhds u.property] with x hx
  change (𝓡∂ (k + 1)).IsInteriorPoint x at hx
  simp [interiorLift, hx]

omit hC hinv in
theorem contMDiffAt_interiorLift (u : IntrinsicInterior.Point k M) :
    ContMDiffAt (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ (interiorLift u) u.val := by
  apply IntrinsicInterior.contMDiffAt_iff_val.mpr
  exact contMDiffAt_id.congr_of_eventuallyEq (interiorLift_val_eventually u)

/-- The entire original native manifold includes smoothly into the constructed
boundaryless quotient, with the seam proved using the same collar inverse. -/
theorem contMDiff_original :
    letI := extensionChartedSpace hδ C hemb hboundary hzero
    ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞
      (original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) := by
  let := extensionChartedSpace hδ C hemb hboundary hzero
  let := extension_isManifold hδ C hemb hC hboundary hinv hzero
  intro x
  rcases (𝓡∂ (k + 1)).isInteriorPoint_or_isBoundaryPoint x with hx | hx
  · let u : IntrinsicInterior.Point k M := ⟨x, hx⟩
    have hs := (contMDiff_interiorIn hδ C hemb hC hboundary hinv hzero).contMDiffAt.comp x
      (contMDiffAt_interiorLift u)
    apply hs.congr_of_eventuallyEq
    filter_upwards [interiorLift_val_eventually u] with z hz
    exact congrArg (original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) hz.symm
  · let b : IntrinsicBoundary.Point k M := ⟨x, hx⟩
    let p : Half δ (IntrinsicBoundary.Point k M) :=
      ⟨(0, b), ⟨le_rfl, hδ⟩, mem_univ _⟩
    obtain ⟨g, hg, _, heq⟩ := original_cylinder_germ hδ C hemb hinv p
    have hpx : C p.val = x := hzero b
    rw [hpx] at hg heq
    exact ((contMDiff_cylinder hδ C hemb hC hboundary hinv hzero).contMDiffAt.comp x hg)
      |>.congr_of_eventuallyEq heq

end FsFltz.Geometry.IntrinsicCollarGluing
