import FsFltz.Geometry.OriginalVaryingLevelPair
import FsFltz.Geometry.OriginalInitialChoiceComparison

/-!
# Completed actual ribbon families with unchanged ambient domain

Source: `geoemtric-part-fsf.tex`, `lem:choices`, lines 460–474, and
`geometric-part-fsf-proof.tex`, `lem:choices`, lines 965–973.
The ambient completion is fixed. Ribbon collars and completed presentations
are constructed from the actual primitive family, rather than assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold

/-- The actual collar-localized ribbon with fixed ambient completion and
witness one. -/
def fixedAmbientLocalizedWitnessedPair {n : ℕ} (E : LiouvilleDomain (2 * n))
    (CE : Completion E) (D : CompactDomain (2 * n - 2)) (Λ : LiouvilleStructure D)
    (B : LiouvilleDomain.FlowCollar (⟨D, Λ⟩ : LiouvilleDomain (2 * n - 2)))
    (j : D.extension.SmoothEmbedding E.domain.boundary)
    (hp : D.extension.pullback E.domain.boundary j.map
      (E.domain.boundaryForm E.liouville.primitive) = Λ.primitive) : WitnessedPair n where
  ambientDomain := E
  ambientCompletion := CE
  ribbonDomain := B.localizedDomain
  ribbonCompletion := B.cylindricalCompletion
  ribbonEmbedding := j.comp B.originalInclusion
  witness := fun _ => 1
  smooth_witness := contMDiff_const
  positive_witness := fun _ => zero_lt_one
  ribbon_primitive := by
    intro x _
    change B.localizedDomain.domain.extension.pullback E.domain.boundary
      (j.map ∘ B.originalInclusion.map)
      (fun y => (1 : ℝ) • E.domain.boundaryForm E.liouville.primitive y) x = _
    simp only [one_smul]
    rw [B.localizedDomain.domain.extension.pullback_comp D.extension E.domain.boundary
      (B.originalInclusion.map.contMDiff.mdifferentiable (by simp))
      (j.map.contMDiff.mdifferentiable (by simp)), hp, B.pullback_originalInclusion]
    exact (B.original_primitive x).symm

/-- Assemble the same native compact and completed ribbon family while
the entire ambient tuple and both ambient presentations stay fixed. -/
def fixedAmbientLocalizedPairDeformation {n : ℕ} (E : LiouvilleDomain (2 * n))
    (CE : Completion E) (D : CompactDomain (2 * n - 2))
    (Λ : Parameter → LiouvilleStructure D)
    (j : Parameter → D.extension.SmoothEmbedding E.domain.boundary)
    (hj : D.extension.IsSmoothIntervalMapFamily E.domain.boundary (fun t => (j t).map))
    (ribbon : LocalizedCompletionFamily D Λ)
    (hp : ∀ t, D.extension.pullback E.domain.boundary (j t).map
      (E.domain.boundaryForm E.liouville.primitive) = (Λ t).primitive) : PairDeformation n := by
  let B := ribbon.collars
  let pair := fun t => fixedAmbientLocalizedWitnessedPair E CE D (Λ t) (B t) (j t) (hp t)
  let h := DomainPresentationEquiv.refl E.domain
  let p : CompletionPresentationEquiv CE CE h :=
    { equiv := Diffeomorph.refl _ _ ∞
      compact_square := fun _ _ => rfl
      end_square := fun _ _ _ => rfl }
  have hμ : E.domain.extension.IsSmoothIntervalFormFamily (fun _ : Parameter =>
      E.domain.extension.pullback E.domain.extension h.extensionEquiv E.liouville.primitive) := by
    change E.domain.extension.IsSmoothIntervalFormFamily (fun _ : Parameter =>
      E.domain.extension.pullback E.domain.extension id E.liouville.primitive)
    rw [E.domain.extension.pullback_id]
    exact E.domain.extension.isSmoothIntervalFormFamily_constant _ E.liouville.smooth_primitive
  have hZ : E.domain.extension.IsSmoothIntervalVectorFieldFamily (fun _ : Parameter =>
      E.domain.extension.pullbackVectorField E.domain.extension h.extensionEquiv E.liouville.field) := by
    change E.domain.extension.IsSmoothIntervalVectorFieldFamily (fun _ : Parameter =>
      E.domain.extension.pullbackVectorField E.domain.extension
        (Diffeomorph.refl _ _ ∞) E.liouville.field)
    rw [E.domain.extension.pullbackVectorField_refl]
    exact E.domain.extension.isSmoothIntervalVectorFieldFamily_constant _ E.liouville.smooth_field
  have hcμ : CE.ambient.manifold.IsSmoothIntervalFormFamily (fun _ : Parameter =>
      CE.ambient.manifold.pullback CE.ambient.manifold p.equiv CE.ambient.primitive) := by
    change CE.ambient.manifold.IsSmoothIntervalFormFamily (fun _ : Parameter =>
      CE.ambient.manifold.pullback CE.ambient.manifold id CE.ambient.primitive)
    rw [CE.ambient.manifold.pullback_id]
    exact CE.ambient.manifold.isSmoothIntervalFormFamily_constant _ CE.ambient.smooth_primitive
  have hcZ : CE.ambient.manifold.IsSmoothIntervalVectorFieldFamily (fun _ : Parameter =>
      CE.ambient.manifold.pullbackVectorField CE.ambient.manifold p.equiv CE.ambient.field) := by
    rw [CE.ambient.manifold.pullbackVectorField_refl]
    exact CE.ambient.manifold.isSmoothIntervalVectorFieldFamily_constant _ CE.ambient.smooth_field
  have hpre : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n - 2)))
      𝓘(ℝ, Model (2 * n - 2)) ∞
      (fun q : ℝ × (B parameterZero).localizedDomain.domain.extension.Point =>
        (ribbon.originalPresentation q.1).extensionEquiv
          ((B parameterZero).originalInclusion.map q.2)) :=
    ribbon.smooth_originalPresentation.comp (contMDiff_fst.prodMk
      ((B parameterZero).originalInclusion.map.contMDiff.comp contMDiff_snd))
  have hs := SmoothManifold.isSmoothIntervalMapFamily_comp_of_contMDiff_family
    (B parameterZero).localizedDomain.domain.extension D.extension E.domain.boundary
    (fun t => (j t).map) hj
    (fun t x => (ribbon.originalPresentation t).extensionEquiv
      ((B parameterZero).originalInclusion.map x)) hpre
  have hemb : (pair parameterZero).ribbonDomain.domain.extension.IsSmoothIntervalMapFamily
      E.domain.boundary (fun t x => h.boundaryEquiv.invFun
        ((pair t).ribbonEmbedding.map ((ribbon.compactPresentation t).extensionEquiv x))) := by
    change (B parameterZero).localizedDomain.domain.extension.IsSmoothIntervalMapFamily
      E.domain.boundary (fun t x => h.boundaryEquiv.invFun
        ((pair t).ribbonEmbedding.map ((ribbon.compactPresentation t).extensionEquiv x)))
    have he : (fun t x => h.boundaryEquiv.invFun
        ((pair t).ribbonEmbedding.map ((ribbon.compactPresentation t).extensionEquiv x))) =
        (fun t x => (j t).map ((ribbon.originalPresentation t.val).extensionEquiv
          ((B parameterZero).originalInclusion.map x))) := by
      funext t x
      change (j t).map (((ribbon.compactPresentation t).extensionEquiv x).val.val) = _
      rw [ribbon.original_projection]
      rfl
    rw [he]
    exact hs
  exact
    { pair := pair
      ambientPresentation := fun _ => h
      ambientCompletionPresentation := fun _ => p
      ribbonPresentation := ribbon.compactPresentation
      ribbonCompletionPresentation := ribbon.completionPresentation
      ambientPrimitive_smooth := hμ
      ambientField_smooth := hZ
      ribbonPrimitive_smooth := ribbon.compactPrimitive_smooth
      ribbonField_smooth := ribbon.compactField_smooth
      ribbonEmbedding_smooth := hemb
      witness_smooth := E.domain.boundary.isSmoothIntervalScalarFamily_constant 1
      completedAmbientPrimitive_smooth := hcμ
      completedAmbientField_smooth := hcZ
      completedRibbonPrimitive_smooth := ribbon.completedPrimitive_smooth
      completedRibbonField_smooth := ribbon.completedField_smooth }

section Original
variable {n : ℕ} (I : ToricInput n) {Aamb R Afib level : ℝ}
  (hamb : AmbientEndBound I Aamb)
  (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
  (hfib : FiberEndBound I Aamb R Afib) (hlevel : Afib < level)

local notation "F" => originalFullFiberModel I hamb hR
local notation "η" => (phi0 ∘ SmoothEmbedding.map
  (FullFiberModel.embedding (originalFullFiberModel I hamb hR)))

include hfib hlevel

/-- Every chosen completion of an actual full-fiber sublevel presentation
has the full inclusion/flow marking. No marking or completed comparison is
an input to this theorem. -/
theorem exists_originalSublevelPresentation_fiberMarking
    (S : LiouvilleDomain (2 * n - 2)) (C : Completion S)
    (hS : S.domain.carrier.Nonempty)
    (J : S.domain.extension.SmoothEmbedding (F).ambient.manifold)
    (himage : J.map '' S.domain.carrier = {x | η x ≤ level})
    (hp : ∀ x ∈ S.domain.carrier,
      S.liouville.primitive x = S.domain.extension.pullback (F).ambient.manifold
        J.map (F).ambient.primitive x) :
    Nonempty (InclusionMarking C (F).ambient (fun x => J.map x.val)) := by
  let q : (F).ambient.manifold.Point → ℝ := fun x => η x - level
  have hq : ContMDiff 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, ℝ) ∞ q :=
    (contMDiff_originalFullFiber_phi0 I hamb hR).sub contMDiff_const
  have hc : IsCompact {x | q x ≤ 0} := by
    simpa only [q, sub_nonpos] using
      isCompact_originalFullFiber_phi0_sublevel_all I hamb hR level
  have ho : ∀ x, q x = 0 → 0 < (F).ambient.manifold.scalarDerivative q x
      ((F).ambient.manifold.liouvilleVector (F).ambient.primitive x) := by
    intro x hx
    have he : η x = level := sub_eq_zero.mp hx
    have hd : (F).ambient.manifold.scalarDerivative q x
        ((F).ambient.manifold.liouvilleVector (F).ambient.primitive x) =
        (F).ambient.manifold.scalarDerivative η x
          ((F).ambient.manifold.liouvilleVector (F).ambient.primitive x) := by
      unfold scalarDerivative
      change mfderiv _ _ (η - fun _ => level) x _ = _
      rw [mfderiv_sub ((contMDiff_originalFullFiber_phi0 I hamb hR).mdifferentiable (by simp) x)
        mdifferentiableAt_const, mfderiv_const, sub_zero]
      rfl
    rw [hd]
    exact scalarDerivative_originalFullFiber_phi0_pos I hamb hR hfib x (he.symm ▸ hlevel.le)
  have ha : ∀ x, ∃ T : ℝ, 0 ≤ T ∧ q ((F).ambient.completeFlow.flow (-T) x) ≤ 0 := by
    intro x
    simpa only [q, sub_nonpos] using
      originalFullFiber_absorbs_phi0_sublevel I hamb hR hfib hlevel x
  apply C.exists_inclusionMarking_of_embedded_absorbing_sublevel hS (F).ambient q hq hc ho ha J
  · simpa only [q, sub_nonpos] using himage
  · exact hp

end Original
end FsFltz.Geometry
