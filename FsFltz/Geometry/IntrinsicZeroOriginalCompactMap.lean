import FsFltz.Geometry.IntrinsicNativeOriginalCompactMap
import FsFltz.Geometry.IntrinsicNativeFamilyEndpointComparison

/-!
# Native zero-dimensional maps on the original compact presentations

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 159–160;
`def:chain`, lines 171–189; and `sec:lean`, lines 783–814 and 825–830.
The prescribed native finite diffeomorphism is represented on the original
extension types of two fixed compact domains. Completion coverage supplies
fallback carrier points for the values outside the compact carriers.
Discreteness proves smoothness, including for empty carriers; neither
domain nor completion is replaced. Vanishing one-forms proves the full
constant primitive scale. The completed map on the same fixed endpoints
agrees with this original compact map and its inverse.

These are dimension-zero foundations for the compact ribbon map of a
completion identification. No geometric comparison chain is constructed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry.IntrinsicZeroLiouville

variable {M N : Type} [TopologicalSpace M] [ChartedSpace (Model 0) M]
  [TopologicalSpace N] [ChartedSpace (Model 0) N]

private def compactPointOfExtension (D : LiouvilleDomain 0) (C : Completion D)
    (x : D.domain.extension.Point) : D.domain.Point :=
  ⟨(C.carrier_nonempty_of_extension_nonempty ⟨x⟩).choose,
    (C.carrier_nonempty_of_extension_nonempty ⟨x⟩).choose_spec⟩

/-- Represent the original prescribed native map on the original extension
types. Completion coverage supplies irrelevant off-carrier values; the
native compact values and inverse are retained exactly. -/
def originalNativeCompactDiffeomorph
    (D D' : LiouvilleDomain 0) (C : Completion D) (C' : Completion D')
    (eM : letI := D.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M D.domain.Point ∞)
    (eN : letI := D'.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) N D'.domain.Point ∞)
    (h : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M N ∞) :
    CompactDomainDiffeomorph D.domain D'.domain := by
  classical
  let f : D.domain.extension.Point → D'.domain.extension.Point := fun z =>
    if hz : z ∈ D.domain.carrier then (eN (h (eM.symm ⟨z, hz⟩))).val
    else (eN (h (eM.symm (compactPointOfExtension D C z)))).val
  let g : D'.domain.extension.Point → D.domain.extension.Point := fun z =>
    if hz : z ∈ D'.domain.carrier then (eM (h.symm (eN.symm ⟨z, hz⟩))).val
    else (eM (h.symm (eN.symm (compactPointOfExtension D' C' z)))).val
  have hf (x : M) : f (eM x).val = (eN (h x)).val := by
    dsimp [f]
    rw [dite_eq_left (eM x).property]
    simp
  have hg (y : N) : g (eN y).val = (eM (h.symm y)).val := by
    dsimp [g]
    rw [dite_eq_left (eN y).property]
    simp
  letI := D.domain.extension.discreteTopology_of_dimension_zero
  letI := D'.domain.extension.discreteTopology_of_dimension_zero
  exact
    { map := f
      inverse := g
      sourceNeighbourhood := univ
      targetNeighbourhood := univ
      open_source := isOpen_univ
      open_target := isOpen_univ
      contains_source := subset_univ _
      contains_target := subset_univ _
      smooth_map := contMDiff_of_discreteTopology.contMDiffOn
      smooth_inverse := contMDiff_of_discreteTopology.contMDiffOn
      maps_source := by
        intro z hz
        obtain ⟨x, hx⟩ := eM.surjective ⟨z, hz⟩
        have hxv := congrArg Subtype.val hx
        change (eM x).val = z at hxv
        rw [← hxv, hf]
        exact (eN (h x)).property
      maps_target := by
        intro z hz
        obtain ⟨y, hy⟩ := eN.surjective ⟨z, hz⟩
        have hyv := congrArg Subtype.val hy
        change (eN y).val = z at hyv
        rw [← hyv, hg]
        exact (eM (h.symm y)).property
      left_inverse := by
        intro z hz
        obtain ⟨x, hx⟩ := eM.surjective ⟨z, hz⟩
        have hxv := congrArg Subtype.val hx
        change (eM x).val = z at hxv
        rw [← hxv, hf, hg, h.symm_apply_apply]
      right_inverse := by
        intro z hz
        obtain ⟨y, hy⟩ := eN.surjective ⟨z, hz⟩
        have hyv := congrArg Subtype.val hy
        change (eN y).val = z at hyv
        rw [← hyv, hg, hf, h.apply_symm_apply]
      immersion := fun _ _ => fun _ _ _ => PiLp.ext (fun i => Fin.elim0 i) }

@[simp] theorem originalNativeCompactDiffeomorph_map
    (D D' : LiouvilleDomain 0) (C : Completion D) (C' : Completion D')
    (eM : letI := D.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M D.domain.Point ∞)
    (eN : letI := D'.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) N D'.domain.Point ∞)
    (h : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M N ∞) (x : M) :
    (originalNativeCompactDiffeomorph D D' C C' eM eN h).map (eM x).val =
      (eN (h x)).val := by
  classical
  simp [originalNativeCompactDiffeomorph, (eM x).property]

@[simp] theorem originalNativeCompactDiffeomorph_inverse
    (D D' : LiouvilleDomain 0) (C : Completion D) (C' : Completion D')
    (eM : letI := D.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M D.domain.Point ∞)
    (eN : letI := D'.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) N D'.domain.Point ∞)
    (h : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M N ∞) (y : N) :
    (originalNativeCompactDiffeomorph D D' C C' eM eN h).inverse (eN y).val =
      (eM (h.symm y)).val := by
  classical
  simp [originalNativeCompactDiffeomorph, (eN y).property]

/-- Algebraic vanishing proves the complete primitive scaling equation on
the original extension, without an additional map or primitive premise. -/
theorem originalNativeCompactDiffeomorph_primitive_scaled
    (D D' : LiouvilleDomain 0) (C : Completion D) (C' : Completion D')
    (eM : letI := D.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M D.domain.Point ∞)
    (eN : letI := D'.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) N D'.domain.Point ∞)
    (h : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M N ∞) (c : ℝ)
    (z : D.domain.extension.Point) :
    D.domain.extension.pullback D'.domain.extension
      (originalNativeCompactDiffeomorph D D' C C' eM eN h).map D'.liouville.primitive z =
        c • D.liouville.primitive z := by
  rw [D'.domain.extension.oneForm_eq_zero_of_dimension_zero D'.liouville.primitive,
    D.domain.extension.oneForm_eq_zero_of_dimension_zero D.liouville.primitive]
  ext v
  simp [SmoothManifold.pullback]

/-- The original-domain counterpart of the positive-dimensional native
adapter. No nonemptiness assumption is used, so empty carriers are allowed. -/
theorem exists_originalNativeCompactDiffeomorph
    (D D' : LiouvilleDomain 0) (C : Completion D) (C' : Completion D')
    (eM : letI := D.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M D.domain.Point ∞)
    (eN : letI := D'.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) N D'.domain.Point ∞)
    (h : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M N ∞) (c : ℝ) :
    ∃ g : CompactDomainDiffeomorph D.domain D'.domain,
      (∀ x, g.map (eM x).val = (eN (h x)).val) ∧
      (∀ y, g.inverse (eN y).val = (eM (h.symm y)).val) ∧
      ∀ z ∈ D.domain.carrier,
        D.domain.extension.pullback D'.domain.extension g.map D'.liouville.primitive z =
          c • D.liouville.primitive z := by
  exact ⟨originalNativeCompactDiffeomorph D D' C C' eM eN h,
    originalNativeCompactDiffeomorph_map D D' C C' eM eN h,
    originalNativeCompactDiffeomorph_inverse D D' C C' eM eN h,
    fun z _ => originalNativeCompactDiffeomorph_primitive_scaled D D' C C' eM eN h c z⟩

variable [T2Space M] [SecondCountableTopology M] [IsManifold 𝓘(ℝ, Model 0) ∞ M]
  [T2Space N] [SecondCountableTopology N] [IsManifold 𝓘(ℝ, Model 0) ∞ N]

/-- The existing completed endpoint map agrees with the constructed original
compact map in both directions on the whole compact carriers. The native
map is retained, and the same completed map transports the complete flows. -/
theorem exists_scaledCompletionEquiv_of_originalNativeCompactDiffeomorph
    (D D' : LiouvilleDomain 0) (C : Completion D) (C' : Completion D')
    (eM : letI := D.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M D.domain.Point ∞)
    (eN : letI := D'.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) N D'.domain.Point ∞)
    (h : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M N ∞) (c : ℝ) :
    let g := originalNativeCompactDiffeomorph D D' C C' eM eN h
    ∃ e : C.ambient.manifold.SmoothEquiv C'.ambient.manifold,
      C.ambient.manifold.pullback C'.ambient.manifold e C'.ambient.primitive =
        c • C.ambient.primitive ∧
      (∀ x, e (C.inclusion.map (eM x).val) = C'.inclusion.map (eN (h x)).val) ∧
      (∀ y, e.symm (C'.inclusion.map (eN y).val) = C.inclusion.map (eM (h.symm y)).val) ∧
      (∀ z ∈ D.domain.carrier,
        e (C.inclusion.map z) = C'.inclusion.map (g.map z)) ∧
      (∀ z ∈ D'.domain.carrier,
        e.symm (C'.inclusion.map z) = C.inclusion.map (g.inverse z)) ∧
      (∀ z s, e (C.ambient.completeFlow.flow s z) =
        C'.ambient.completeFlow.flow s (e z)) := by
  dsimp only
  obtain ⟨e, hp, hsquare, hinverse, hflow⟩ :=
    exists_scaledEquiv_on_fixed_native_endpoints D D' C C' eM eN h c
  refine ⟨e, hp, hsquare, hinverse, ?_, ?_, hflow⟩
  · intro z hz
    obtain ⟨x, hx⟩ := eM.surjective ⟨z, hz⟩
    have hxv := congrArg Subtype.val hx
    change (eM x).val = z at hxv
    rw [← hxv, originalNativeCompactDiffeomorph_map]
    exact hsquare x
  · intro z hz
    obtain ⟨y, hy⟩ := eN.surjective ⟨z, hz⟩
    have hyv := congrArg Subtype.val hy
    change (eN y).val = z at hyv
    rw [← hyv, originalNativeCompactDiffeomorph_inverse]
    exact hinverse y

end FsFltz.Geometry.IntrinsicZeroLiouville
