import FsFltz.Geometry.IntrinsicRibbonPair

/-!
# Joint native identifications in the actual localized family

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199, and
`sec:lean`, lines 783–814. The collar-adapted compact presentation may move
interior points. Native identifications are therefore transported through
that very presentation. Both directions have jointly smooth extensions in
the real parameter, using the constructed compact atlas's ambient chart
extensions, rather than maps into a half-space beyond its boundary.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry

/-- Joint native smoothness of both directions, with an all-real parameter
extension. This asserts regularity of the actual maps, not just slice forms. -/
def IsJointlySmoothDiffeomorphFamily
    {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (e : ℝ → Diffeomorph I I M M ∞) : Prop :=
  ContMDiff ((𝓘(ℝ, ℝ)).prod I) I ∞ (fun p : ℝ × M => e p.1 p.2) ∧
  ContMDiff ((𝓘(ℝ, ℝ)).prod I) I ∞ (fun p : ℝ × M => (e p.1).symm p.2)

/-- A fixed native diffeomorphism transports both jointly smooth directions
of an all-real family to the original native manifold. -/
theorem IsJointlySmoothDiffeomorphFamily.conjugate
    {E H E' H' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
    {M N : Type} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H' N]
    (f : Diffeomorph I J M N ∞) (e : ℝ → Diffeomorph J J N N ∞)
    (he : IsJointlySmoothDiffeomorphFamily J e) :
    IsJointlySmoothDiffeomorphFamily I (fun t => (f.trans (e t)).trans f.symm) := by
  constructor
  · exact f.symm.contMDiff.comp (he.1.comp
      (contMDiff_fst.prodMk (f.contMDiff.comp contMDiff_snd)))
  · exact f.symm.contMDiff.comp (he.2.comp
      (contMDiff_fst.prodMk (f.contMDiff.comp contMDiff_snd)))

namespace DomainPresentationEquiv

variable {d : ℕ} [NeZero d] {D E : CompactDomain d}

/-- The actual extension presentation restricts to a native compact
diffeomorphism, using the proved ambient-chart smoothness bridge. -/
def nativePointDiffeomorph (h : DomainPresentationEquiv D E) :
    Diffeomorph (𝓡∂ d) (𝓡∂ d) D.Point E.Point ∞ where
  toFun := fun x => ⟨h.extensionEquiv x.val, (h.mem_carrier_iff x.val).mpr x.property⟩
  invFun := fun y => ⟨h.extensionEquiv.symm y.val,
    (h.mem_carrier_iff _).mp (by rw [h.extensionEquiv.apply_symm_apply]; exact y.property)⟩
  left_inv := fun x => Subtype.ext (h.extensionEquiv.symm_apply_apply x.val)
  right_inv := fun y => Subtype.ext (h.extensionEquiv.apply_symm_apply y.val)
  contMDiff_toFun := E.contMDiff_iff_subtype_val.mpr
    (h.extensionEquiv.contMDiff.comp D.contMDiff_subtype_val)
  contMDiff_invFun := D.contMDiff_iff_subtype_val.mpr
    (h.extensionEquiv.symm.contMDiff.comp E.contMDiff_subtype_val)

@[simp] theorem nativePointDiffeomorph_val (h : DomainPresentationEquiv D E) (x : D.Point) :
    (h.nativePointDiffeomorph x).val = h.extensionEquiv x.val := rfl

@[simp] theorem nativePointDiffeomorph_symm_val (h : DomainPresentationEquiv D E) (x : E.Point) :
    (h.nativePointDiffeomorph.symm x).val = h.extensionEquiv.symm x.val := rfl

end DomainPresentationEquiv

namespace LocalizedCompletionFamily

variable {d : ℕ} [NeZero d] {D : CompactDomain d}
  {L : Parameter → LiouvilleStructure D} (F : LocalizedCompletionFamily D L)

/-- Both jointly smooth actual extension maps induce jointly smooth maps
on the fixed native compact manifold, including its boundary charts. -/
theorem jointlySmooth_nativePointDiffeomorph :
    IsJointlySmoothDiffeomorphFamily (𝓡∂ d)
      (fun t => (F.originalPresentation t).nativePointDiffeomorph) := by
  constructor
  · apply D.contMDiff_iff_subtype_val.mpr
    exact F.smooth_originalPresentation.comp
      (contMDiff_fst.prodMk (D.contMDiff_subtype_val.comp contMDiff_snd))
  · apply D.contMDiff_iff_subtype_val.mpr
    exact F.smooth_originalPresentation_symm.comp
      (contMDiff_fst.prodMk (D.contMDiff_subtype_val.comp contMDiff_snd))

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type} [TopologicalSpace M] [ChartedSpace H M]

/-- The native identification after transport back through the actual
family presentation, expressed on the original fixed native manifold. -/
def transportedNativeDiffeomorph
    (e : Diffeomorph I (𝓡∂ d) M D.Point ∞) (t : ℝ) : Diffeomorph I I M M ∞ :=
  (e.trans (F.originalPresentation t).nativePointDiffeomorph.symm).trans e.symm

/-- Both directions of the transported native identifications extend
jointly smoothly across the parameter endpoints. -/
theorem jointlySmooth_transportedNativeDiffeomorph
    (e : Diffeomorph I (𝓡∂ d) M D.Point ∞) :
    IsJointlySmoothDiffeomorphFamily I (F.transportedNativeDiffeomorph I e) := by
  have hs := F.jointlySmooth_nativePointDiffeomorph
  constructor
  · exact e.symm.contMDiff.comp (hs.2.comp
      (contMDiff_fst.prodMk (e.contMDiff.comp contMDiff_snd)))
  · exact e.symm.contMDiff.comp (hs.1.comp
      (contMDiff_fst.prodMk (e.contMDiff.comp contMDiff_snd)))

/-- The transported map is computed from the retained all-real ambient
inverse. This includes every native compact point. -/
theorem transportedNativeDiffeomorph_val
    (e : Diffeomorph I (𝓡∂ d) M D.Point ∞) (t : ℝ) (x : M) :
    (e (F.transportedNativeDiffeomorph I e t x)).val =
      (F.originalPresentation t).extensionEquiv.symm (e x).val := by
  exact congrArg Subtype.val (e.apply_symm_apply _)

/-- The inverse uses the retained all-real ambient forward map. -/
theorem transportedNativeDiffeomorph_symm_val
    (e : Diffeomorph I (𝓡∂ d) M D.Point ∞) (t : ℝ) (x : M) :
    (e ((F.transportedNativeDiffeomorph I e t).symm x)).val =
      (F.originalPresentation t).extensionEquiv (e x).val := by
  exact congrArg Subtype.val (e.apply_symm_apply _)

/-- The same relative native map agrees with the actual constructed
localized compact presentation. It is not an unrelated smooth family. -/
theorem transportedNativeDiffeomorph_square
    (e : Diffeomorph I (𝓡∂ d) M D.Point ∞) (t : Parameter) (x : M) :
    (F.compactPresentation t).extensionEquiv
      (((e.trans (F.collars parameterZero).originalPointDiffeomorph.symm)
        (F.transportedNativeDiffeomorph I e t.val x)).val) =
      ((e.trans (F.collars t).originalPointDiffeomorph.symm) x).val := by
  apply Subtype.ext
  apply Subtype.ext
  rw [F.original_projection]
  change (F.originalPresentation t.val).extensionEquiv
      (e (F.transportedNativeDiffeomorph I e t.val x)).val = (e x).val
  rw [F.transportedNativeDiffeomorph_val]
  exact (F.originalPresentation t.val).extensionEquiv.apply_symm_apply _

end LocalizedCompletionFamily
end FsFltz.Geometry
