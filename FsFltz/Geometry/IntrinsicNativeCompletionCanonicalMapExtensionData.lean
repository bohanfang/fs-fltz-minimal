import FsFltz.Geometry.IntrinsicNativeCompletionCanonicalExtensionAtlas

/-!
# Local real extensions of arbitrary maps into the original canonical bundle

Source: `geoemtric-part-fsf.tex`, smooth-extension convention (119–122),
`def:maslov` (212–244), and `sec:lean` (766–836). The source and target
charts are the independently constructed original charts. Regularity asks
for the entire coordinate map to extend on a real-open neighborhood, before
any section, coefficient, or desired grading graph is selected.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology Bundle

namespace FsFltz.Geometry.IntrinsicCompletionGluing

variable {k n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] {δ : ℝ}
  (hδ : 0 < δ)
  (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (hemb : ∀ t, IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val))
  (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
  (hzero : ∀ t b, C t (0, b) = b.val)
  (J : ∀ s : Parameter, Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
    Model (k + 1) →L[ℝ] Model (k + 1))
  (N : Model (2 * n) ≃L[ℝ] Model (k + 1))
  (hjoint : IsOpenEmbedding (totalCollar
    (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
  (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ (C t)
    (Half δ (IntrinsicBoundary.Point k M)))
  (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C t q) = q)

/-- Near every actual source point, the full coordinate map in some original
source and target charts has a smooth real-open extension. -/
def HasOriginalTotalLocalMapExtensions
    (f : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) →
      Bundle.TotalSpace ℂ (OriginalTotalCanonicalTensorSquare C J N)) : Prop :=
  ∀ x, ∃ (c d : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (p : c.NativeBase), p ∈ c.nativeDomain ∧ c.inclusion p = x ∧
    (f x).proj ∈ d.totalDomain ∧
    ∃ (U : TopologicalSpace.Opens c.RealBase) (G : c.RealBase → d.RealModel),
      c.baseCoordinate p ∈ U ∧ ContDiffOn ℝ ∞ G U ∧
      (U : Set c.RealBase) ⊆ c.realDomain ∧
      ∀ q : c.NativeBase, q ∈ c.nativeDomain → c.baseCoordinate q ∈ U →
        ∃ hd : (f (c.inclusion q)).proj ∈ d.totalDomain,
          G (c.baseCoordinate q) =
            d.coordinateAt N hjoint hC hinv (f (c.inclusion q)) hd

/-- The corresponding extension condition in every original source and
target chart containing the actual source point and its actual image. -/
def HasOriginalTotalChartMapExtensions
    (f : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) →
      Bundle.TotalSpace ℂ (OriginalTotalCanonicalTensorSquare C J N)) : Prop :=
  ∀ (c d : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (p : c.NativeBase), p ∈ c.nativeDomain → (f (c.inclusion p)).proj ∈ d.totalDomain →
    ∃ (U : TopologicalSpace.Opens c.RealBase) (G : c.RealBase → d.RealModel),
      c.baseCoordinate p ∈ U ∧ ContDiffOn ℝ ∞ G U ∧
      (U : Set c.RealBase) ⊆ c.realDomain ∧
      ∀ q : c.NativeBase, q ∈ c.nativeDomain → c.baseCoordinate q ∈ U →
        ∃ hd : (f (c.inclusion q)).proj ∈ d.totalDomain,
          G (c.baseCoordinate q) =
            d.coordinateAt N hjoint hC hinv (f (c.inclusion q)) hd

end FsFltz.Geometry.IntrinsicCompletionGluing
