import FsFltz.Geometry.IntrinsicCollarDefining
import FsFltz.Geometry.IntrinsicCollarGluingDifferential

/-!
# Compact domains produced by the intrinsic collar extension

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. The carrier, regular defining functions, and smooth embedded
boundary below are all produced by the same collar and its constructed atlas.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Topology

namespace FsFltz.Geometry.IntrinsicCollarGluing

section ZeroSlice

variable {k : ℕ} {B : Type} [TopologicalSpace B] [ChartedSpace (Model k) B]
  [IsManifold 𝓘(ℝ, Model k) ∞ B] {δ : ℝ} (hδ : 0 < δ)

/-- The literal zero-time slice of the actual two-sided collar. -/
def boundaryIntoBand (b : B) : Band δ B :=
  ⟨(0, b), ⟨by linarith, hδ⟩, mem_univ _⟩

local instance domainBandChartedSpace : ChartedSpace (Model (k + 1)) (Band δ B) := bandChartedSpace δ
local instance domainBandIsManifold : IsManifold 𝓘(ℝ, Model (k + 1)) ∞ (Band δ B) := band_isManifold δ

theorem contMDiff_boundaryIntoBand :
    ContMDiff 𝓘(ℝ, Model k) 𝓘(ℝ, Model (k + 1)) ∞ (boundaryIntoBand (B := B) hδ) := by
  intro b
  exact contMDiffAt_band_iff_val.mpr (contMDiffAt_const.prodMk contMDiffAt_id)

theorem isEmbedding_boundaryIntoBand : IsEmbedding (boundaryIntoBand (B := B) hδ) := by
  exact IsEmbedding.of_leftInverse (fun _ => rfl)
    (continuous_snd.comp continuous_subtype_val)
    ((continuous_const.prodMk continuous_id).subtype_mk _)

/-- The zero slice is an immersion: the smooth boundary projection is its
actual left inverse, so the tangent map is injective. -/
theorem injective_mfderiv_boundaryIntoBand (b : B) :
    Function.Injective (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model (k + 1))
      (boundaryIntoBand hδ) b) := by
  let g : Band δ B → B := fun p => p.val.2
  have hg : ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k) ∞ g :=
    contMDiff_snd.comp (contMDiff_band_val δ)
  have hd := mfderiv_comp (f := boundaryIntoBand hδ) (g := g) b
    (hg.mdifferentiableAt (by simp))
    ((contMDiff_boundaryIntoBand hδ).mdifferentiableAt (by simp))
  have heq : g ∘ boundaryIntoBand hδ = id := rfl
  rw [heq, mfderiv_id] at hd
  intro v w hvw
  have heval (a : TangentSpace 𝓘(ℝ, Model k) b) := congrArg (fun A => A a) hd
  exact (heval v).trans ((congrArg
    (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k) g (boundaryIntoBand hδ b)) hvw).trans
      (heval w).symm)

end ZeroSlice

section Native

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] [T2Space M] [SecondCountableTopology M]
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

local instance nativeDomainBandChartedSpace :
    ChartedSpace (Model (k + 1)) (Band δ (IntrinsicBoundary.Point k M)) := bandChartedSpace δ
local instance nativeDomainBandIsManifold :
    IsManifold 𝓘(ℝ, Model (k + 1)) ∞ (Band δ (IntrinsicBoundary.Point k M)) := band_isManifold δ

/-- The literal native boundary is smoothly embedded into the constructed
extension as its zero-time cylinder slice, with injective differential proved. -/
def boundaryInclusion :
    (IntrinsicBoundary.smoothManifold k M).SmoothEmbedding
      (extensionManifold hδ C hemb hC hboundary hinv hzero) := by
  let := extensionChartedSpace hδ C hemb hboundary hzero
  let := extension_isManifold hδ C hemb hC hboundary hinv hzero
  refine
    { map := ⟨cylinder (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val) ∘
        boundaryIntoBand hδ,
        (contMDiff_cylinder hδ C hemb hC hboundary hinv hzero).comp
          (contMDiff_boundaryIntoBand hδ)⟩
      embedding := (isOpenEmbedding_cylinder hδ _ hemb).isEmbedding.comp
        (isEmbedding_boundaryIntoBand hδ)
      immersion := ?_ }
  intro b
  change Function.Injective (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model (k + 1))
    (cylinder (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val) ∘
      boundaryIntoBand hδ) b)
  rw [mfderiv_comp b
    ((contMDiff_cylinder hδ C hemb hC hboundary hinv hzero).mdifferentiableAt (by simp))
    ((contMDiff_boundaryIntoBand hδ).mdifferentiableAt (by simp))]
  exact (injective_mfderiv_cylinder hδ C hemb hC hboundary hinv hzero
    (boundaryIntoBand hδ b)).comp (injective_mfderiv_boundaryIntoBand hδ b)

@[simp] theorem boundaryInclusion_map (b : IntrinsicBoundary.Point k M) :
    (boundaryInclusion hδ C hemb hC hboundary hinv hzero).map b =
      original (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val) b.val := by
  let p : Half δ (IntrinsicBoundary.Point k M) := ⟨(0, b), ⟨le_rfl, hδ⟩, mem_univ _⟩
  have hp : original (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val) b.val =
      cylinder (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val) (halfToBand hδ p) := by
    simpa [p, hzero b] using original_collar_eq_cylinder hδ
      (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val) p
  exact hp.symm

/-- The produced smooth boundary presentation covers exactly the actual
topological frontier of the original carrier. -/
theorem range_boundaryInclusion :
    range (boundaryInclusion hδ C hemb hC hboundary hinv hzero).map =
      frontier (range (original (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val))) := by
  rw [frontier_range_original hδ _ hemb hboundary hzero]
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b.val, b.property, (boundaryInclusion_map hδ C hemb hC hboundary hinv hzero b).symm⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨m, hm⟩, boundaryInclusion_map hδ C hemb hC hboundary hinv hzero ⟨m, hm⟩⟩

/-- An actual compact-domain presentation produced from a compact native
manifold and this collar. The atlas, regularity, and boundary immersion are
outputs of the construction, rather than extra input assumptions. -/
def compactDomain [CompactSpace M] : CompactDomain (k + 1) where
  extension := extensionManifold hδ C hemb hC hboundary hinv hzero
  carrier := range (original (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val))
  compact := isCompact_range_original _
  defining := boundaryDefiningFunction hδ C hemb hC hboundary hinv hzero
  boundary := IntrinsicBoundary.smoothManifold k M
  boundaryInclusion := boundaryInclusion hδ C hemb hC hboundary hinv hzero
  boundary_range := range_boundaryInclusion hδ C hemb hC hboundary hinv hzero
  zero_boundary := by omega

end Native

end FsFltz.Geometry.IntrinsicCollarGluing
