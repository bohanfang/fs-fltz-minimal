import FsFltz.Geometry.IntrinsicCollarDomain
import FsFltz.Geometry.BoundaryPresentationBridge

/-!
# Return to the native atlas of a constructed collar domain

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. The actual collar construction presents the given compact
native manifold by its literal image in the constructed boundaryless extension.
Both smooth directions below are proved: the inverse uses the pushed interior
charts and the actual cylinder inverse at the seam. No smoothness of an
unconstructed inverse is assumed.

This is the correspondence for this constructed compact domain. Additional
maps, differential forms, and general parameter families remain separate
foundation obligations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCollarGluing

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] [T2Space M] [SecondCountableTopology M]
  [CompactSpace M]
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

local instance presentationBandChartedSpace :
    ChartedSpace (Model (k + 1)) (Band δ (IntrinsicBoundary.Point k M)) :=
  bandChartedSpace δ

local instance presentationBandIsManifold :
    IsManifold 𝓘(ℝ, Model (k + 1)) ∞ (Band δ (IntrinsicBoundary.Point k M)) :=
  band_isManifold δ

/-- The original embedding gives a homeomorphism onto the actual compact
carrier of the produced domain. -/
def originalHomeomorph : M ≃ₜ (compactDomain hδ C hemb hC hboundary hinv hzero).Point :=
  (isClosedEmbedding_original hδ
    (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) hemb).isEmbedding.toHomeomorph

@[simp] theorem originalHomeomorph_val (x : M) :
    (originalHomeomorph hδ C hemb hC hboundary hinv hzero x).val =
      original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) x := rfl

@[simp] theorem original_originalHomeomorph_symm
    (x : (compactDomain hδ C hemb hC hboundary hinv hzero).Point) :
    original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)
      ((originalHomeomorph hδ C hemb hC hboundary hinv hzero).symm x) = x.val := by
  exact congrArg Subtype.val
    ((originalHomeomorph hδ C hemb hC hboundary hinv hzero).apply_symm_apply x)

/-- The literal original inclusion is smooth into the native atlas of the
actual compact carrier, by its proved ambient smoothness. -/
theorem contMDiff_originalHomeomorph :
    ContMDiff (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) ∞
      (originalHomeomorph hδ C hemb hC hboundary hinv hzero) := by
  apply (compactDomain hδ C hemb hC hboundary hinv hzero).contMDiff_iff_subtype_val.mpr
  exact contMDiff_original hδ C hemb hC hboundary hinv hzero

/-- The inverse is smooth in the actual carrier's native boundary atlas.
Interior charts supply inverse germs; on the cylinder patch, its inverse
lands in the nonnegative half and composing with the given collar recovers
the original point. -/
theorem contMDiff_originalHomeomorph_symm :
    ContMDiff (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) ∞
      (originalHomeomorph hδ C hemb hC hboundary hinv hzero).symm := by
  let D := compactDomain hδ C hemb hC hboundary hinv hzero
  let e := originalHomeomorph hδ C hemb hC hboundary hinv hzero
  let C₀ := fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val
  let := extensionChartedSpace hδ C hemb hboundary hzero
  let := extension_isManifold hδ C hemb hC hboundary hinv hzero
  intro x
  have hex (y : D.Point) : original C₀ (e.symm y) = y.val :=
    original_originalHomeomorph_symm hδ C hemb hC hboundary hinv hzero y
  rcases (𝓡∂ (k + 1)).isInteriorPoint_or_isBoundaryPoint (e.symm x) with hx | hx
  · let u : IntrinsicInterior.Point k M := ⟨e.symm x, hx⟩
    have hatlas : (chartAt (Model (k + 1)) u).lift_openEmbedding
        (isOpenEmbedding_interiorIn hδ C₀ hemb hboundary) ∈
        IsManifold.maximalAtlas 𝓘(ℝ, Model (k + 1)) ∞ (Extension C₀) := by
      apply IsManifold.subset_maximalAtlas
      exact Or.inl ⟨chartAt (Model (k + 1)) u, chart_mem_atlas _ u, rfl⟩
    obtain ⟨g, hg, _, heq⟩ := smooth_inverse_germ_of_lifted_chart
      (isOpenEmbedding_interiorIn hδ C₀ hemb hboundary) u hatlas
    have hux : interiorIn C₀ u = x.val := hex x
    rw [hux] at hg heq
    have hs := IntrinsicInterior.contMDiff_val.contMDiffAt.comp x
      (hg.comp x D.contMDiff_subtype_val.contMDiffAt)
    apply hs.congr_of_eventuallyEq
    filter_upwards [continuous_subtype_val.continuousAt.eventually heq] with y hy
    apply (isClosedEmbedding_original hδ C₀ hemb).injective
    exact (hex y).trans hy.symm
  · let b : IntrinsicBoundary.Point k M := ⟨e.symm x, hx⟩
    let p := boundaryIntoBand hδ b
    have hpx : cylinder C₀ p = x.val := by
      have h := boundaryInclusion_map hδ C hemb hC hboundary hinv hzero b
      exact h.trans (hex x)
    let s : Set D.Point := Subtype.val ⁻¹' range (cylinder C₀)
    have hso : IsOpen s :=
      (isOpenEmbedding_cylinder hδ C₀ hemb).isOpen_range.preimage continuous_subtype_val
    have hxs : x ∈ s := ⟨p, hpx⟩
    let f : D.Point → Band δ (IntrinsicBoundary.Point k M) :=
      cylinderInverse hδ C₀ hemb p ∘ Subtype.val
    have hf : ContMDiffOn (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ f s :=
      (contMDiffOn_cylinderInverse hδ C hemb hC hboundary hinv hzero p).comp
        D.contMDiff_subtype_val.contMDiffOn (fun _ hy => hy)
    have hfy (y : D.Point) (hy : y ∈ s) : original C₀ (e.symm y) = cylinder C₀ (f y) :=
      (hex y).trans (cylinder_cylinderInverse hδ C₀ hemb p hy).symm
    have hmaps : MapsTo (Subtype.val ∘ f) s (Half δ (IntrinsicBoundary.Point k M)) := by
      intro y hy
      obtain ⟨ht, _⟩ := (original_eq_cylinder_iff C₀ (e.symm y) (f y)).mp (hfy y hy)
      exact ⟨⟨ht, (f y).property.1.2⟩, mem_univ _⟩
    have hs := hC.comp ((contMDiff_band_val δ).comp_contMDiffOn hf) hmaps
    have heq : EqOn (fun y : D.Point => e.symm y) (C ∘ Subtype.val ∘ f) s := by
      intro y hy
      obtain ⟨_, h⟩ := (original_eq_cylinder_iff C₀ (e.symm y) (f y)).mp (hfy y hy)
      exact h.symm
    exact (hs.congr heq).contMDiffAt (hso.mem_nhds hxs)

/-- The original native compact manifold and its constructed compact-domain
presentation are diffeomorphic, with the literal original inclusion as map. -/
def originalDiffeomorph : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1))
    M (compactDomain hδ C hemb hC hboundary hinv hzero).Point ∞ where
  toEquiv := (originalHomeomorph hδ C hemb hC hboundary hinv hzero).toEquiv
  contMDiff_toFun := contMDiff_originalHomeomorph hδ C hemb hC hboundary hinv hzero
  contMDiff_invFun := contMDiff_originalHomeomorph_symm hδ C hemb hC hboundary hinv hzero

@[simp] theorem originalDiffeomorph_val (x : M) :
    (originalDiffeomorph hδ C hemb hC hboundary hinv hzero x).val = original
      (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) x := rfl

end FsFltz.Geometry.IntrinsicCollarGluing
