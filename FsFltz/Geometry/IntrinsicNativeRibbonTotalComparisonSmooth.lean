import FsFltz.Geometry.IntrinsicNativeRibbonTotalComparison

/-!
# Joint smoothness of the original ribbon total comparison

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199,
and `sec:lean`, lines 788–814. The moving native boundary comparison and
the completed primitive family of the same deformation give one actual
all-real smooth cylinder formula above a negative cutoff. Its spatial
differential is invertible on every nonnegative interval radius, so the
parameter-retaining real map has genuine smooth inverse germs there.
The native interior formula and this strip prove smoothness on the original
total atlas, including the rest of its unaltered inward collar.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.PairDeformation
open IntrinsicLiouville IntrinsicCompletionGluing

variable {k n : ℕ} [NeZero (2 * n - 2)]
  {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {Q : PairDeformation n} {μ : Parameter → Form k M 1}
  {eMs : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M
    (Q.pair t).ribbonDomain.domain.Point ∞}

namespace NativeRibbonCompletionSlices

variable (S : NativeRibbonCompletionSlices Q μ eMs)
  (RM : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
  (hRM : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) RM)
  (hsquare : ∀ t x, (Q.ribbonPresentation t).extensionEquiv
    (eMs parameterZero (RM t.val x)).val = (eMs t x).val)

include RM hRM hsquare

/-- An all-real cylinder extension of the actual retained total map, with
a parameter-retaining real local diffeomorphism at the seam and every
outward radius. The boundary point moves by the actual native relabeling.
Matching covers the original inward cylinder above the negative cutoff. -/
theorem exists_realCylinderExtension :
    ∃ a : ℝ, a < 0 ∧
      ∃ β : ℝ → IntrinsicBoundary.Point k M × ℝ →
          Q.source.ribbonCompletion.ambient.manifold.Point,
        ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)))
          𝓘(ℝ, Model (2 * n - 2)) ∞
          (fun p : ℝ × (IntrinsicBoundary.Point k M × ℝ) => β p.1 p.2) ∧
        (∀ (t : Parameter) (p : Band S.width (IntrinsicBoundary.Point k M)),
          a < -p.val.1 →
          β t.val (p.val.2, -p.val.1) =
            S.totalMap (totalCylinder (fun t p => S.collar t p.val) (t, p))) ∧
        (∀ (t : Parameter) (x : IntrinsicBoundary.Point k M) (r : ℝ), 0 ≤ r →
          β t.val (x, r) = Q.source.ribbonCompletion.endMap
            ((Q.ribbonPresentation t).boundaryEquiv.symm (S.boundary_comparison t x), r)) ∧
        ∀ (t : Parameter) (x : IntrinsicBoundary.Point k M) (r : ℝ), 0 ≤ r →
          IsLocalDiffeomorphAt
            ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)))
            ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n - 2))) ∞
            (fun p : ℝ × (IntrinsicBoundary.Point k M × ℝ) => (p.1, β p.1 p.2))
            (t.val, (x, r)) := by
  obtain ⟨B, hB, _, hb, _, _⟩ := S.exists_jointReferenceBoundaryComparison RM hRM hsquare
  obtain ⟨a, ha, γ, hγ, heγ⟩ :=
    Q.source.ribbonCompletion.exists_prescribedFamily_end_strip_extension
      (fun t => (Q.pair t).ribbonDomain) (fun t => (Q.pair t).ribbonCompletion)
      Q.ribbonPresentation Q.ribbonCompletionPresentation Q.completedRibbonPrimitive_smooth
  let β := fun s (p : IntrinsicBoundary.Point k M × ℝ) => γ s (B s p.1, p.2)
  have hβ : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)))
      𝓘(ℝ, Model (2 * n - 2)) ∞
      (fun p : ℝ × (IntrinsicBoundary.Point k M × ℝ) => β p.1 p.2) :=
    hγ.comp (contMDiff_fst.prodMk
      ((hB.comp (contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd))).prodMk
        (contMDiff_snd.comp contMDiff_snd)))
  have heβ (t : Parameter) (x : IntrinsicBoundary.Point k M) (r : ℝ) (hr : a < r) :
      β t.val (x, r) =
        (Q.ribbonCompletionPresentation t).prescribedEndMap (B t.val x, r) :=
    heγ t (B t.val x) r hr
  refine ⟨a, ha, β, hβ, ?_, ?_, ?_⟩
  · intro t p hr
    rw [S.totalMap_cylinder, S.referenceEquiv_cylinder]
    exact (heβ t p.val.2 (-p.val.1) hr).trans
      (congrArg (fun b => (Q.ribbonCompletionPresentation t).prescribedEndMap (b, -p.val.1))
        (hb t p.val.2))
  · intro t x r hr
    exact (heβ t x r (lt_of_lt_of_le ha hr)).trans
      (((Q.ribbonCompletionPresentation t).prescribedEndMap_nonnegative _ r hr).trans
        (congrArg (fun b => Q.source.ribbonCompletion.endMap (b, r)) (hb t x)))
  · intro t x r hr
    let b := (B t.val).prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)
    have hl₀ : IsLocalDiffeomorphAt
        ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model (2 * n - 2)) ∞
        (fun p : IntrinsicBoundary.Point k M × ℝ =>
          (Q.ribbonCompletionPresentation t).prescribedEndMap (B t.val p.1, p.2))
        (x, r) :=
      (b.isLocalDiffeomorph (x, r)).comp 𝓘(ℝ, Model (2 * n - 2))
        Q.source.ribbonCompletion.ambient.manifold.Point
        ((Q.ribbonCompletionPresentation t).isLocalDiffeomorph_prescribedEndMap (b (x, r)))
    have heq : (fun p : IntrinsicBoundary.Point k M × ℝ => β t.val p) =ᶠ[𝓝 (x, r)]
        (fun p : IntrinsicBoundary.Point k M × ℝ =>
          (Q.ribbonCompletionPresentation t).prescribedEndMap (B t.val p.1, p.2)) := by
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
        (isOpen_Ioi.mem_nhds (show r ∈ Ioi a from lt_of_lt_of_le ha hr))] with p hp
      exact heβ t p.1 p.2 hp
    have hbij : Function.Bijective (mfderiv
        ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model (2 * n - 2))
        (fun p : IntrinsicBoundary.Point k M × ℝ => β t.val p) (x, r)) := by
      rw [heq.mfderiv_eq]
      exact (tangentSpaceCast 𝓘(ℝ, Model (2 * n - 2))
        ((Q.ribbonCompletionPresentation t).prescribedEndMap (B t.val x, r))
        (β t.val (x, r))).bijective.comp
          ((hl₀.mfderivToContinuousLinearEquiv (by simp)).bijective)
    have hM : IsManifold ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)) ∞
        (IntrinsicBoundary.Point k M × ℝ) := inferInstance
    let : ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
      prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ
    rw [← modelWithCornersSelf_prod] at hM hβ hbij ⊢
    exact isLocalDiffeomorphAt_parameterMap_of_bijective_slice
      (fun p : ℝ × (IntrinsicBoundary.Point k M × ℝ) => β p.1 p.2) hβ t.val (x, r) hbij

/-- The compact patch has a genuine all-real smooth formula, including
both parameter endpoints, and names the same original comparison. -/
theorem exists_realInteriorExtension :
    ∃ f : ℝ × IntrinsicInterior.Point k M → Q.source.ribbonCompletion.ambient.manifold.Point,
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1)))
        𝓘(ℝ, Model (2 * n - 2)) ∞ f ∧
      ∀ (t : Parameter) (u : IntrinsicInterior.Point k M),
        f (t.val, u) = S.totalMap (totalInterior (fun t p => S.collar t p.val) (t, u)) := by
  let f₀ : M → Q.source.ribbonCompletion.ambient.manifold.Point :=
    fun x => Q.source.ribbonCompletion.inclusion.map (eMs parameterZero x).val
  have hf₀ : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) ∞ f₀ :=
    Q.source.ribbonCompletion.inclusion.map.contMDiff.comp
      (Q.source.ribbonDomain.domain.contMDiff_subtype_val.comp (eMs parameterZero).contMDiff)
  refine ⟨fun p => f₀ (RM p.1 p.2.val), hf₀.comp
    (hRM.1.comp (contMDiff_fst.prodMk (IntrinsicInterior.contMDiff_val.comp contMDiff_snd))), ?_⟩
  intro t u
  exact (S.referenceEquiv_native_eq_compact RM hsquare t u.val).symm

/-- Smoothness holds on the actual original total atlas. The end-strip
criterion covers the remaining positive inward radii through the original
mixed collar germs, retaining its complete chosen width. -/
theorem contMDiff_totalMap :
    letI := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
    ContMDiff (familyModel (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) ∞ S.totalMap := by
  let c := fun t (p : Half S.width (IntrinsicBoundary.Point k M)) => S.collar t p.val
  let := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) S.width
  let := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
  obtain ⟨f, hf, hef⟩ := S.exists_realInteriorExtension RM hRM hsquare
  have hi : ContMDiff (familyModel (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) ∞
      (S.totalMap ∘ totalInterior c) := by
    convert hf.comp (contMDiff_subtypeVal_Icc.prodMap contMDiff_id) using 1
    funext p
    exact (hef p.1 p.2).symm
  obtain ⟨a, ha, β, hβ, heβ, _, _⟩ := S.exists_realCylinderExtension RM hRM hsquare
  have hinput : ContMDiff (familyModel (k + 1))
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ))) ∞
      (fun p : Parameter × Band S.width (IntrinsicBoundary.Point k M) =>
        (p.1.val, (p.2.val.2, -p.2.val.1))) :=
    (contMDiff_subtypeVal_Icc.comp contMDiff_fst).prodMk
      ((contMDiff_snd.comp ((contMDiff_band_val S.width).comp contMDiff_snd)).prodMk
        (contMDiff_fst.comp ((contMDiff_band_val S.width).comp contMDiff_snd)).neg)
  have hstrip : ContMDiffOn (familyModel (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) ∞
      (S.totalMap ∘ totalCylinder c) {p | p.2.val.1 < -a} := by
    apply (hβ.comp hinput).contMDiffOn.congr
    intro p hp
    exact (heβ p.1 p.2 (by change p.2.val.1 < -a at hp; linarith)).symm
  exact contMDiff_totalFamily_of_end_strip S.width_pos S.collar S.collar_boundary
    S.collar_zero S.collar_joint_embedding S.mixed_germs S.totalMap (neg_pos.mpr ha) hi hstrip

/-- Joint smoothness includes the actual projection to the parameter. -/
theorem contMDiff_totalEquiv :
    letI := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
    ContMDiff (familyModel (k + 1)) (familyModel (2 * n - 2)) ∞ S.totalEquiv := by
  let := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
  exact (contMDiff_parameter S.width_pos S.collar S.collar_boundary
    S.collar_zero S.collar_joint_embedding S.mixed_germs).prodMk
      (S.contMDiff_totalMap RM hRM hsquare)

end NativeRibbonCompletionSlices
end FsFltz.Geometry.PairDeformation
