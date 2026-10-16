import FsFltz.Geometry.FamilyCompletionAssembly

/-!
# One actual radial weight throughout a localized completed family

Source: `geometric-part-fsf-proof.tex`, `lem:grading`, lines 1994–2030.
The specified cylindrical presentations preserve their actual radius, and
all slices have the same finite collar width. Their completion weights
therefore pull back to the single weight of the zero slice.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry
open SmoothManifold

namespace LiouvilleDomain.FlowCollar
variable {d : ℕ} {D : LiouvilleDomain d} (C : FlowCollar D)

/-- On the actual nonnegative cylindrical end the weight depends only on
its radius and the given collar width. -/
theorem radialWeight_cylindricalEnd (x : C.localizedDomain.domain.boundary.Point)
    (r : ℝ) (hr : 0 ≤ r) :
    C.radialWeight (C.cylindricalCompletion.endMap (x, r)).val =
      Real.exp (r - CollarStretch.inverse C.positive_width r) := by
  have hrr : -C.width < r := lt_of_lt_of_le (neg_lt_zero.mpr C.positive_width) hr
  change C.radialWeight (C.cylindricalFlowEndMap (x, r)).val = _
  rw [C.cylindricalFlowEndMap_eq_endMap (x, r) hrr, C.endMap_val (x, r) hrr]
  let q : C.strip := ⟨(x, CollarStretch.inverse C.positive_width r),
    mem_univ _, CollarStretch.inverse_mem_collar C.positive_width hrr⟩
  change C.radialWeight (C.stripMap q) = _
  rw [C.radialWeight_stripMap q]
  dsimp only [q]
  rw [CollarStretch.stretch_inverse C.positive_width r]

end LiouvilleDomain.FlowCollar

namespace LocalizedCompletionFamily
variable {d : ℕ} {D : CompactDomain d} {L : Parameter → LiouvilleStructure D}

/-- The actual compact presentation preserves the constructed radial
multiplier everywhere, using compact-plus-end coverage and its exact
completion square. No extra collar covariance certificate is an input. -/
theorem radialWeight_compactPresentation (F : LocalizedCompletionFamily D L)
    (t : Parameter) (z : (F.collars parameterZero).localizedDomain.domain.extension.Point) :
    (F.collars t).radialWeight (((F.compactPresentation t).extensionEquiv z).val) =
      (F.collars parameterZero).radialWeight z.val := by
  have hcover : z ∈ (F.collars parameterZero).cylindricalCompletion.inclusion.map ''
        (F.collars parameterZero).localizedDomain.domain.carrier ∪
      (F.collars parameterZero).cylindricalCompletion.endMap '' (univ ×ˢ Ici (0 : ℝ)) := by
    rw [(F.collars parameterZero).cylindricalCompletion.covering]
    exact mem_univ z
  rcases hcover with hcompact | hend
  · obtain ⟨x, hx, he⟩ := hcompact
    change x = z at he
    subst z
    have ht : (F.compactPresentation t).extensionEquiv x ∈
        (F.collars t).localizedDomain.domain.carrier := by
      rw [← (F.compactPresentation t).carrier]
      exact mem_image_of_mem _ hx
    rw [(F.collars t).radialWeight_carrier _ ht,
      (F.collars parameterZero).radialWeight_carrier _ hx]
  · obtain ⟨⟨x, r⟩, hr, rfl⟩ := hend
    have he := (F.completionPresentation t).end_square x r hr.2
    rw [F.completionPresentation_eq t] at he
    refine (congrArg (fun y : (F.collars t).localizedDomain.domain.extension.Point =>
      (F.collars t).radialWeight y.val) he).trans ?_
    rw [(F.collars t).radialWeight_cylindricalEnd _ r hr.2,
      (F.collars parameterZero).radialWeight_cylindricalEnd x r hr.2]
    have hw : (F.collars t).width = (F.collars parameterZero).width :=
      (F.collar_width t).trans (F.collar_width parameterZero).symm
    congr 2
    congr 1

/-- The pulled actual completed primitive is the fixed zero-slice weight
times the pulled actual unstretched primitive throughout the interval. -/
theorem completedPrimitive_eq_radialWeight_smul (F : LocalizedCompletionFamily D L)
    (t : Parameter) :
    (F.collars parameterZero).localizedDomain.domain.extension.pullback
      (F.collars t).localizedDomain.domain.extension (F.completionPresentation t).equiv
        (F.collars t).cylindricalCompletion.ambient.primitive =
      fun z => (F.collars parameterZero).radialWeight z.val •
        ((F.collars parameterZero).localizedDomain.domain.extension.pullback
          (F.collars t).localizedDomain.domain.extension (F.compactPresentation t).extensionEquiv
            (F.collars t).localizedDomain.liouville.primitive) z := by
  rw [F.completionPresentation_eq t]
  funext z
  ext v
  change (F.collars t).radialWeight (((F.compactPresentation t).extensionEquiv z).val) *
    ((F.collars t).localizedDomain.liouville.primitive ((F.compactPresentation t).extensionEquiv z))
      (fun i => mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d)
        (F.compactPresentation t).extensionEquiv z (v i)) = _
  rw [F.radialWeight_compactPresentation t z]
  rfl

/-- The actual compact primitive in the localized presentation is exactly
the restriction of the original family's transported primitive. -/
theorem compactPrimitive_eq_originalPullback (F : LocalizedCompletionFamily D L)
    (t : Parameter) :
    (F.collars parameterZero).localizedDomain.domain.extension.pullback
      (F.collars t).localizedDomain.domain.extension (F.compactPresentation t).extensionEquiv
        (F.collars t).localizedDomain.liouville.primitive =
      (F.collars parameterZero).localizedDomain.domain.extension.pullback D.extension
        (F.collars parameterZero).originalInclusion.map
        (D.extension.pullback D.extension (F.originalPresentation t.val).extensionEquiv (L t).primitive) := by
  rw [(F.collars t).localized_primitive_pullback]
  rw [← (F.collars parameterZero).localizedDomain.domain.extension.pullback_comp
    (F.collars t).localizedDomain.domain.extension D.extension
    ((F.compactPresentation t).extensionEquiv.contMDiff.mdifferentiable (by simp))
    ((F.collars t).originalInclusion.map.contMDiff.mdifferentiable (by simp))]
  have he : (F.collars t).originalInclusion.map ∘ (F.compactPresentation t).extensionEquiv =
      (F.originalPresentation t.val).extensionEquiv ∘ (F.collars parameterZero).originalInclusion.map :=
    funext (F.original_projection t)
  rw [he]
  exact (F.collars parameterZero).localizedDomain.domain.extension.pullback_comp D.extension D.extension
    ((F.collars parameterZero).originalInclusion.map.contMDiff.mdifferentiable (by simp))
    ((F.originalPresentation t.val).extensionEquiv.contMDiff.mdifferentiable (by simp)) (L t).primitive

end LocalizedCompletionFamily
end FsFltz.Geometry
