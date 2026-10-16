import FsFltz.Geometry.TailoringHittingRibbonFamily
import FsFltz.Geometry.CompletionComparison
import FsFltz.Geometry.DomainCompletionRestriction

/-!
# The full core of the retained hitting ribbon

Source: `geometric-part-fsf-proof.tex`, `subsec:junction`, lines 1918–1924.
The same intrinsic full core is transported through shrinking and hitting.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Manifold ContDiff Topology
namespace FsFltz
open Geometry Geometry.SmoothManifold

/-- The actual hit carries the entire retained shrinking core to the
image of the original full core under the same native hitting map. -/
theorem IntrinsicShrinkingData.hittingEmbedding_core_image {n : ℕ}
    {P : WitnessedPair n} (S : IntrinsicShrinkingData P)
    {R : P.ribbonDomain.domain.extension.SmoothEmbedding (lgManifold n)}
    {f : LGSpace n → ℂ} {value : ℂ} {φ : RealSpace n → ℝ}
    (M : FullFiberRibbonMarking P R f value φ)
    (U : TopologicalSpace.Opens M.manifold.Point)
    (hU : ∀ x : S.extension, (S.fiberEmbedding M parameterOne).map x ∈ U)
    (V : TopologicalSpace.Opens ℝ)
    (e : V → (M.manifold.restrict U).SmoothEmbedding (lgManifold n))
    (k : V) (g : LGSpace n → LGSpace n)
    (he : ∀ x : U, (e k).map x = g (M.embedding.map x.val)) :
    (S.hittingEmbedding M U hU V e k).map '' (S.pair parameterOne).ribbonCompletion.core =
      g '' (R.map '' P.ribbonCompletion.core) := by
  rw [← S.ribbonAmbientEmbedding_core M parameterOne, ← image_comp]
  apply image_congr
  intro x hx
  rw [S.hittingEmbedding_apply M U hU V e k, he,
    S.fiberEmbedding_compact M parameterOne x hx.1]
  rfl

/-- A collar localization retains the full intrinsic core, independently
of the newly constructed cylindrical completion. -/
theorem Geometry.LiouvilleDomain.FlowCollar.originalInclusion_core {d : ℕ}
    {F : LiouvilleDomain d} (B : F.FlowCollar) (C : Completion F) :
    B.originalInclusion.map '' B.cylindricalCompletion.core = C.core := by
  have hc := B.cylindricalCompletion.core_eq_of_same_domain (C.localizeToFlowCollar B)
  have hp : (C.localizeToFlowCollar B).core =
      B.originalInclusion.map ⁻¹' C.core := by
    ext x
    change (x ∈ B.localizedDomain.domain.carrier ∧ ∀ t : ℝ, 0 ≤ t →
      C.ambient.completeFlow.flow t (C.inclusion.map (B.originalInclusion.map x)) ∈
        (C.inclusion.map ∘ B.originalInclusion.map) '' B.localizedDomain.domain.carrier) ↔ _
    rw [image_comp, B.image_originalInclusion_carrier]
    rfl
  rw [hc, hp]
  apply image_preimage_eq_of_subset
  intro x hx
  have hi : x ∈ B.originalInclusion.map '' B.localizedDomain.domain.carrier :=
    B.image_originalInclusion_carrier.symm ▸ hx.1
  obtain ⟨y, _, hy⟩ := hi
  exact ⟨y, hy⟩

/-- Both constructed cylindrical completions retain the entire ribbon
core under the exact original embedding of the localized pair. -/
theorem localizedWitnessedPair_embeddedCore {n : ℕ}
    (D : LiouvilleDomain (2 * n)) (F : LiouvilleDomain (2 * n - 2))
    (A : D.FlowCollar) (B : F.FlowCollar) (C : Completion F)
    (j : F.domain.extension.SmoothEmbedding D.domain.boundary)
    (b : D.domain.boundary.Point → ℝ)
    (hb : ContMDiff 𝓘(ℝ, Model (2 * n - 1)) 𝓘(ℝ, ℝ) ∞ b)
    (hpos : ∀ x, 0 < b x)
    (hp : ∀ x ∈ F.domain.carrier,
      F.domain.extension.pullback D.domain.boundary j.map
        (fun y => b y • D.domain.boundaryForm D.liouville.primitive y) x =
          F.liouville.primitive x) :
    (localizedWitnessedPair D F A B j b hb hpos hp).embeddedCore = j.map '' C.core := by
  change (j.map ∘ B.originalInclusion.map) '' B.cylindricalCompletion.core = _
  rw [image_comp, B.originalInclusion_core C]

/-- The actual completed family retains the full source core at each
parameter under its supplied hitting embedding. -/
theorem CompletedHittingRibbonFamily.embeddedCore {n : ℕ}
    {D : CompactDomain (2 * n)} {F : LiouvilleDomain (2 * n - 2)}
    {L : Parameter → LiouvilleStructure D}
    {j : Parameter → F.domain.extension.SmoothEmbedding D.boundary}
    {b : Parameter → D.boundary.Point → ℝ}
    (H : CompletedHittingRibbonFamily D F L j b) (C : Completion F) (t : Parameter) :
    (H.deformation.pair t).embeddedCore = (j t).map '' C.core :=
  localizedWitnessedPair_embeddedCore ⟨D, L t⟩ F (H.ambient.collars t)
    (H.ribbon.collars t) C (j t) (b t)
    (H.witness_smooth.contMDiff_slice t) (H.positive t) (H.primitive t)

end FsFltz
