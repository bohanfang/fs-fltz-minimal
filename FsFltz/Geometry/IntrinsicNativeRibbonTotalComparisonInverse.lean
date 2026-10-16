import FsFltz.Geometry.IntrinsicNativeRibbonTotalComparisonSmooth

/-!
# Smooth inverse of the original ribbon total comparison

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199,
and `sec:lean`, lines 788–814. The fixed native interior inclusion has
actual smooth inverse germs. Composing them with the all-real inverse
native relabeling gives real parameter inverse germs on the interior.
The proved real cylinder local diffeomorphisms give the inverse at every
seam and outward point. These two regions cover the same reference
completion and prove that the original total equivalence is a diffeomorphism.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k d : ℕ} [NeZero d] {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- The actual fixed native interior inclusion has smooth local inverses
in its supplied completion. Its differential uses the native carrier
inclusion and the completion inclusion, with no family regularity input. -/
theorem isLocalDiffeomorph_nativeInteriorInclusion (hdim : k + 1 = d)
    (D : LiouvilleDomain d) (K : Completion D)
    (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ d) M D.domain.Point ∞) :
    IsLocalDiffeomorph 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d) ∞
      (fun u : IntrinsicInterior.Point k M => K.inclusion.map (e u.val).val) := by
  let j : IntrinsicInterior.Point k M → D.domain.Point := fun u => e u.val
  have hj : ContMDiff 𝓘(ℝ, Model (k + 1)) (𝓡∂ d) ∞ j :=
    e.contMDiff.comp IntrinsicInterior.contMDiff_val
  let i : IntrinsicInterior.Point k M → D.domain.extension.Point := fun u => (j u).val
  have hi : ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d) ∞ i :=
    D.domain.contMDiff_subtype_val.comp hj
  have hf : ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d) ∞
      (fun u : IntrinsicInterior.Point k M => K.inclusion.map (e u.val).val) :=
    K.inclusion.map.contMDiff.comp hi
  intro u
  have hjinj : Function.Injective (mfderiv 𝓘(ℝ, Model (k + 1)) (𝓡∂ d) j u) := by
    change Function.Injective (mfderiv 𝓘(ℝ, Model (k + 1)) (𝓡∂ d)
      (e ∘ (Subtype.val : IntrinsicInterior.Point k M → M)) u)
    rw [mfderiv_comp u (e.contMDiff.mdifferentiableAt (by simp))
      (IntrinsicInterior.contMDiff_val.mdifferentiableAt (by simp))]
    exact (e.isInvertible_mfderiv (by simp)).injective.comp
      (IntrinsicInterior.injective_mfderiv_val u)
  have hiinj : Function.Injective (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d) i u) := by
    change Function.Injective (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d)
      ((Subtype.val : D.domain.Point → D.domain.extension.Point) ∘ j) u)
    rw [mfderiv_comp u (D.domain.contMDiff_subtype_val.mdifferentiableAt (by simp))
      (hj.mdifferentiableAt (by simp))]
    exact (D.domain.injective_mfderiv_subtype_val (j u)).comp hjinj
  have hfinj : Function.Injective (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d)
      (fun u : IntrinsicInterior.Point k M => K.inclusion.map (e u.val).val) u) := by
    change Function.Injective (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d)
      (K.inclusion.map ∘ i) u)
    rw [mfderiv_comp u (K.inclusion.map.contMDiff.mdifferentiableAt (by simp))
      (hi.mdifferentiableAt (by simp))]
    exact (K.inclusion.immersion (i u)).comp hiinj
  have hbij : Function.Bijective (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d)
      (fun u : IntrinsicInterior.Point k M => K.inclusion.map (e u.val).val) u) := by
    refine ⟨hfinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hfinj⟩
    change Module.finrank ℝ (Model (k + 1)) = Module.finrank ℝ (Model d)
    rw [hdim]
  exact isLocalDiffeomorphAt_of_bijective_mfderiv_manifold isOpen_univ hf.contMDiffOn
    (mem_univ u) hbij

end FsFltz.Geometry.IntrinsicLiouville

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
  (hdim : k + 1 = 2 * n - 2)
  (RM : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
  (hRM : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) RM)
  (hsquare : ∀ t x, (Q.ribbonPresentation t).extensionEquiv
    (eMs parameterZero (RM t.val x)).val = (eMs t x).val)

include hdim RM hRM hsquare

/-- Real smooth inverse coordinates near every reference native interior
point, also at either parameter endpoint. The restriction agrees with the
actual total inverse in the original native interior patch. -/
theorem exists_realInteriorInverseGerm (t : Parameter) (u : IntrinsicInterior.Point k M) :
    ∃ g : ℝ × Q.source.ribbonCompletion.ambient.manifold.Point →
        ℝ × IntrinsicInterior.Point k M,
      ContMDiffAt ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n - 2)))
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1))) ∞ g
        (t.val, Q.source.ribbonCompletion.inclusion.map (eMs parameterZero u.val).val) ∧
      (∀ p, (g p).1 = p.1) ∧
      ∀ᶠ p in 𝓝 (t, Q.source.ribbonCompletion.inclusion.map (eMs parameterZero u.val).val),
        S.totalEquiv.symm p = totalInterior (fun t p => S.collar t p.val)
          (p.1, (g (p.1.val, p.2)).2) := by
  let c := fun t (p : Half S.width (IntrinsicBoundary.Point k M)) => S.collar t p.val
  let f := fun u : IntrinsicInterior.Point k M =>
    Q.source.ribbonCompletion.inclusion.map (eMs parameterZero u.val).val
  let l := isLocalDiffeomorph_nativeInteriorInclusion hdim
    Q.source.ribbonDomain Q.source.ribbonCompletion (eMs parameterZero) u
  let ri : ℝ × IntrinsicInterior.Point k M → IntrinsicInterior.Point k M :=
    fun p => ⟨(RM p.1).symm p.2.val,
      (IsLocalDiffeomorphAt.isInteriorPoint_iff (by simp)
        ((RM p.1).symm.isLocalDiffeomorph p.2.val)).mp p.2.property⟩
  have hri : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1)))
      𝓘(ℝ, Model (k + 1)) ∞ ri := by
    apply IntrinsicInterior.contMDiff_iff_val.mpr
    exact hRM.2.comp (contMDiff_fst.prodMk
      (IntrinsicInterior.contMDiff_val.comp contMDiff_snd))
  let g : ℝ × Q.source.ribbonCompletion.ambient.manifold.Point → ℝ × IntrinsicInterior.Point k M :=
    fun p => (p.1, ri (p.1, l.localInverse p.2))
  have hg : ContMDiffAt ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n - 2)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1))) ∞ g (t.val, f u) := by
    apply contMDiffAt_fst.prodMk
    apply hri.contMDiffAt.comp
    apply contMDiffAt_fst.prodMk
    exact l.localInverse_contMDiffAt.comp (t.val, f u) contMDiffAt_snd
  refine ⟨g, hg, fun _ => rfl, ?_⟩
  have hn : ∀ᶠ p in 𝓝 (t, f u), p.2 ∈ l.localInverse.source :=
    continuous_snd.continuousAt.eventually
      (l.localInverse.open_source.mem_nhds l.localInverse_mem_source)
  filter_upwards [hn] with p hp
  apply S.totalEquiv.injective
  rw [S.totalEquiv.apply_symm_apply]
  apply Prod.ext
  · rfl
  · change p.2 = S.totalMap (original (totalCollar c) (p.1, (ri (p.1.val, l.localInverse p.2)).val))
    rw [S.totalMap_native, S.referenceEquiv_native_eq_compact RM hsquare]
    change p.2 = Q.source.ribbonCompletion.inclusion.map
      (eMs parameterZero (RM p.1.val ((RM p.1.val).symm (l.localInverse p.2).val))).val
    rw [(RM p.1.val).apply_symm_apply]
    exact (l.localInverse_right_inv hp).symm

/-- Restriction of the real interior inverse coordinates is smooth in
the original total atlas. -/
theorem contMDiffAt_totalEquiv_symm_interior (t : Parameter) (u : IntrinsicInterior.Point k M) :
    letI := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
    ContMDiffAt (familyModel (2 * n - 2)) (familyModel (k + 1)) ∞ S.totalEquiv.symm
      (t, Q.source.ribbonCompletion.inclusion.map (eMs parameterZero u.val).val) := by
  let := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
  obtain ⟨g, hg, _, he⟩ := S.exists_realInteriorInverseGerm hdim RM hRM hsquare t u
  have hrestrict : ContMDiff (familyModel (2 * n - 2))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n - 2))) ∞
      (fun p : Parameter × Q.source.ribbonCompletion.ambient.manifold.Point => (p.1.val, p.2)) :=
    contMDiff_subtypeVal_Icc.prodMap contMDiff_id
  let y := (t, Q.source.ribbonCompletion.inclusion.map (eMs parameterZero u.val).val)
  have hgr : ContMDiffAt (familyModel (2 * n - 2))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1))) ∞
      (fun p : Parameter × Q.source.ribbonCompletion.ambient.manifold.Point => g (p.1.val, p.2)) y :=
    hg.comp y hrestrict.contMDiffAt
  have hr := (contMDiff_totalInterior S.width_pos S.collar S.collar_boundary
    S.collar_zero S.collar_joint_embedding S.mixed_germs).contMDiffAt.comp
      y (contMDiffAt_fst.prodMk (contMDiffAt_snd.comp y hgr))
  exact hr.congr_of_eventuallyEq he

omit hdim in
/-- The real parameter-retaining cylinder inverse restricts to the same
total inverse at the seam and every outward point. -/
theorem contMDiffAt_totalEquiv_symm_end (t : Parameter) (x : IntrinsicBoundary.Point k M)
    (r : ℝ) (hr : 0 ≤ r) :
    letI := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
    ContMDiffAt (familyModel (2 * n - 2)) (familyModel (k + 1)) ∞ S.totalEquiv.symm
      (t, Q.source.ribbonCompletion.endMap
        ((Q.ribbonPresentation t).boundaryEquiv.symm (S.boundary_comparison t x), r)) := by
  obtain ⟨a, ha, β, _, heβ, hβend, hl⟩ := S.exists_realCylinderExtension RM hRM hsquare
  have hs : ∀ (s : Parameter) (p : Band S.width (IntrinsicBoundary.Point k M)),
      a < -p.val.1 →
      S.totalEquiv (totalCylinder (fun t p => S.collar t p.val) (s, p)) =
        (s, β s.val (p.val.2, -p.val.1)) := by
    intro s p hp
    exact Prod.ext rfl (heβ s p hp).symm
  have h := contMDiffAt_inverse_of_real_cylinder S.width_pos S.collar S.collar_boundary
    S.collar_zero S.collar_joint_embedding S.mixed_germs
    Q.source.ribbonCompletion.ambient.manifold S.totalEquiv β a hs t x r
    (lt_of_lt_of_le ha hr) (by linarith [S.width_pos]) (hl t x r hr)
  rwa [hβend t x r hr] at h

/-- The actual reference native interior and nonnegative end cover all
points of the given completion, proving smoothness of the same inverse. -/
theorem contMDiff_totalEquiv_symm :
    letI := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
    ContMDiff (familyModel (2 * n - 2)) (familyModel (k + 1)) ∞ S.totalEquiv.symm := by
  let := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
  let D := Q.source.ribbonDomain.domain
  let K := Q.source.ribbonCompletion
  rintro ⟨t, y⟩
  by_cases hy : y ∈ K.inclusion.map '' interior D.carrier
  · obtain ⟨x, hx, rfl⟩ := hy
    let z : D.Point := ⟨x, interior_subset hx⟩
    have hz : (𝓡∂ (2 * n - 2)).IsInteriorPoint z := by
      change z ∈ (𝓡∂ (2 * n - 2)).interior D.Point
      rw [D.interior_eq_interior]
      exact hx
    let u : IntrinsicInterior.Point k M := ⟨(eMs parameterZero).symm z,
      (IsLocalDiffeomorphAt.isInteriorPoint_iff (by simp)
        ((eMs parameterZero).symm.isLocalDiffeomorph z)).mp hz⟩
    have h := S.contMDiffAt_totalEquiv_symm_interior hdim RM hRM hsquare t u
    simpa only [u, Diffeomorph.apply_symm_apply] using h
  · have hyend : y ∈ range (fun p : D.boundary.Point × Ici (0 : ℝ) => K.endMap (p.1, p.2)) := by
      rw [K.range_nonnegative_endMap]
      exact hy
    obtain ⟨⟨x, ⟨r, hr⟩⟩, rfl⟩ := hyend
    let B := (S.boundary_comparison t).trans (Q.ribbonPresentation t).boundaryEquiv.symm
    have h := S.contMDiffAt_totalEquiv_symm_end RM hRM hsquare t (B.symm x) r hr
    change ContMDiffAt _ _ ∞ S.totalEquiv.symm (t, K.endMap (B (B.symm x), r)) at h
    simpa only [Diffeomorph.apply_symm_apply] using h

/-- The same total equivalence is a diffeomorphism in both original
family atlases, retaining the strict comparison chosen on each slice. -/
def totalDiffeomorph :
    letI := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
    Diffeomorph (familyModel (k + 1)) (familyModel (2 * n - 2))
      (TotalSpace (fun t (p : Half S.width (IntrinsicBoundary.Point k M)) => S.collar t p.val))
      (Parameter × Q.source.ribbonCompletion.ambient.manifold.Point) ∞ := by
  let := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
  exact
    { toEquiv := S.totalEquiv
      contMDiff_toFun := S.contMDiff_totalEquiv RM hRM hsquare
      contMDiff_invFun := S.contMDiff_totalEquiv_symm hdim RM hRM hsquare }

@[simp] theorem totalDiffeomorph_apply
    (z : TotalSpace (fun t (p : Half S.width (IntrinsicBoundary.Point k M)) => S.collar t p.val)) :
    letI := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
    S.totalDiffeomorph hdim RM hRM hsquare z =
      (parameter (fun t p => S.collar t p.val) z, S.totalMap z) := rfl

@[simp] theorem totalDiffeomorph_sliceIn (t : Parameter)
    (x : Space (fun p : Half S.width (IntrinsicBoundary.Point k M) => S.collar t p.val)) :
    letI := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
    S.totalDiffeomorph hdim RM hRM hsquare (sliceIn (fun t p => S.collar t p.val) t x) =
      (t, (Q.ribbonCompletionPresentation t).equiv.symm (S.comparison t x)) :=
  S.totalEquiv_sliceIn t x

@[simp] theorem totalDiffeomorph_symm_apply
    (t : Parameter) (y : Q.source.ribbonCompletion.ambient.manifold.Point) :
    letI := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
    (S.totalDiffeomorph hdim RM hRM hsquare).symm (t, y) =
      sliceIn (fun t p => S.collar t p.val) t
        ((S.comparison t).symm ((Q.ribbonCompletionPresentation t).equiv y)) := rfl

@[simp] theorem parameter_totalDiffeomorph_symm
    (p : Parameter × Q.source.ribbonCompletion.ambient.manifold.Point) :
    letI := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
    parameter (fun t (p : Half S.width (IntrinsicBoundary.Point k M)) => S.collar t p.val)
      ((S.totalDiffeomorph hdim RM hRM hsquare).symm p) = p.1 :=
  S.parameter_totalEquiv_symm p

end NativeRibbonCompletionSlices
end FsFltz.Geometry.PairDeformation
