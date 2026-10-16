import FsFltz.Geometry.TailoringRoundedMarkingFamily
import FsFltz.Geometry.TailoringRoundedMarkingFamilySmooth
import FsFltz.Geometry.SmoothEquivFamilyInverseGerms

/-!
# Joint regularity of the same completed inclusion markings

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 975–1009,
and the actual common marking, lines 1270–1303. The compact formula and
the constructed primitive families prove forward and inverse real germs
for the actual retained completion maps, including the seam and endpoints.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry
open SmoothManifold IntrinsicSmoothBundle

namespace LocalizedCompletionFamily

/-- Actual primitive-preserving slice maps between the constructed native
families are jointly smooth, with jointly smooth inverses, once their full
compact original-inclusion square is the given smooth original map family.
No regularity of the completed maps is an input. -/
theorem markingFamily_realGerms_of_original_square
    {d : ℕ} {E H : CompactDomain d}
    {L : Parameter → LiouvilleStructure E} {μ : Parameter → LiouvilleStructure H}
    (A : LocalizedCompletionFamily E L) (O : LocalizedCompletionFamily H μ)
    (hH : H.carrier.Nonempty)
    (j : Parameter → E.extension.Point → H.extension.Point)
    (hj : E.extension.IsSmoothIntervalMapFamily H.extension j)
    (q : ∀ t, (A.collars t).cylindricalCompletion.ambient.manifold.SmoothEquiv
      (O.collars t).cylindricalCompletion.ambient.manifold)
    (hq : ∀ t, (A.collars t).cylindricalCompletion.ambient.manifold.pullback
      (O.collars t).cylindricalCompletion.ambient.manifold (q t)
        (O.collars t).cylindricalCompletion.ambient.primitive =
          (A.collars t).cylindricalCompletion.ambient.primitive)
    (hsquare : ∀ t x, x ∈ (A.collars t).localizedDomain.domain.carrier →
      (O.collars t).originalInclusion.map (q t x) = j t ((A.collars t).originalInclusion.map x)) :
    let M := (A.collars parameterZero).cylindricalCompletion.ambient.manifold
    let N := (O.collars parameterZero).cylindricalCompletion.ambient.manifold
    let f := fun t => ((A.completionPresentation t).equiv.trans (q t)).trans
      (O.completionPresentation t).equiv.symm
    HasSmoothManifoldTargetFamilyOn M N univ (fun t => f t) ∧
      HasSmoothManifoldTargetFamilyOn N M univ (fun t => (f t).symm) := by
  classical
  dsimp only
  let M := (A.collars parameterZero).cylindricalCompletion.ambient.manifold
  let N := (O.collars parameterZero).cylindricalCompletion.ambient.manifold
  let f : Parameter → M.SmoothEquiv N := fun t =>
    ((A.completionPresentation t).equiv.trans (q t)).trans (O.completionPresentation t).equiv.symm
  let φ : Parameter → ℝ → M.Point → M.Point := fun t r x =>
    (A.completionPresentation t).equiv.symm
      ((A.collars t).cylindricalCompletion.ambient.completeFlow.flow r
        ((A.completionPresentation t).equiv x))
  let ψ : Parameter → ℝ → N.Point → N.Point := fun t r x =>
    (O.completionPresentation t).equiv.symm
      ((O.collars t).cylindricalCompletion.ambient.completeFlow.flow r
        ((O.completionPresentation t).equiv x))
  have hφ : HasRealSmoothFlowGermsOn M univ φ :=
    completeFlowInCoordinates_realGerms_of_smooth_primitive
      (fun t => (A.collars t).cylindricalCompletion.ambient) M
      (fun t => (A.completionPresentation t).equiv.symm) univ A.completedPrimitive_smooth
  have hψ : HasRealSmoothFlowGermsOn N univ ψ :=
    completeFlowInCoordinates_realGerms_of_smooth_primitive
      (fun t => (O.collars t).cylindricalCompletion.ambient) N
      (fun t => (O.completionPresentation t).equiv.symm) univ O.completedPrimitive_smooth
  have hreturn : ∀ t r x, ψ t r (f t (φ t (-r) x)) = f t x := by
    intro t r x
    have hfe (z : M.Point) : f t z = (O.completionPresentation t).equiv.symm
        (q t ((A.completionPresentation t).equiv z)) := rfl
    dsimp only [ψ, φ]
    rw [hfe, hfe]
    rw [(O.completionPresentation t).equiv.apply_symm_apply,
      (A.completionPresentation t).equiv.apply_symm_apply,
      (A.collars t).cylindricalCompletion.ambient.map_flow _ (q t) (hq t),
      ← (O.collars t).cylindricalCompletion.ambient.completeFlow.flow.map_add,
      add_neg_cancel, Flow.map_zero_apply]
  have habsorb : ∀ t x, ∃ T : ℝ, φ t (-T) x ∈
      interior (A.collars parameterZero).localizedDomain.domain.carrier := by
    intro t x
    obtain ⟨T, _, y, hy, he⟩ := (A.collars t).cylindricalCompletion.exists_nonneg_time_mem_interior
      ((A.completionPresentation t).equiv x)
    refine ⟨T, ?_⟩
    have hint := (A.compactPresentation t).extensionEquiv.toHomeomorph.image_interior
      (A.collars parameterZero).localizedDomain.domain.carrier
    change (A.compactPresentation t).extensionEquiv ''
      interior (A.collars parameterZero).localizedDomain.domain.carrier =
      interior ((A.compactPresentation t).extensionEquiv ''
        (A.collars parameterZero).localizedDomain.domain.carrier) at hint
    rw [(A.compactPresentation t).carrier] at hint
    obtain ⟨z, hz, hez⟩ := hint.symm ▸ hy
    have heφ : φ t (-T) x = z := by
      change (A.completionPresentation t).equiv.symm
        ((A.collars t).cylindricalCompletion.ambient.completeFlow.flow (-T)
          ((A.completionPresentation t).equiv x)) = z
      rw [← he]
      change (A.completionPresentation t).equiv.symm y = z
      rw [← hez, ← A.completionPresentation_eq t]
      exact (A.completionPresentation t).equiv.symm_apply_apply z
    exact heφ ▸ hz
  have hcompact : ∀ (t : Parameter) (x : M.Point),
      x ∈ interior (A.collars parameterZero).localizedDomain.domain.carrier →
      ∃ U : TopologicalSpace.Opens (ℝ × M.Point), (t.val, x) ∈ U ∧
        ∃ γ : U → N.Point,
          ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞ γ ∧
          ∀ (s : Parameter) y (hy : (s.val, y) ∈ U), γ ⟨(s.val, y), hy⟩ = f s y := by
    obtain ⟨j', hj', hj'eq⟩ := hj
    obtain ⟨Ω, hΩ, hΩcover, hj'⟩ := hj'
    obtain ⟨z₀, hz₀⟩ := hH
    let : Nonempty (O.collars parameterZero).localizedDomain.domain.extension.Point :=
      ⟨((O.collars parameterZero).cylindricalCompactHomeomorph.symm ⟨z₀, hz₀⟩).val⟩
    let : Nonempty N.Point :=
      ⟨((O.collars parameterZero).cylindricalCompactHomeomorph.symm ⟨z₀, hz₀⟩).val⟩
    let a : ℝ × M.Point → ℝ × E.extension.Point := fun p =>
      (p.1, (A.originalPresentation p.1).extensionEquiv
        ((A.collars parameterZero).originalInclusion.map p.2))
    have ha : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞ a :=
      contMDiff_fst.prodMk (A.smooth_originalPresentation.comp
        (contMDiff_fst.prodMk ((A.collars parameterZero).originalInclusion.map.contMDiff.comp
          contMDiff_snd)))
    let b : ℝ × M.Point → H.extension.Point := fun p =>
      (O.originalPresentation p.1).extensionEquiv.symm (j' p.1 (a p).2)
    let U₀ : Set (ℝ × M.Point) := a ⁻¹' Ω
    have hU₀ : IsOpen U₀ := hΩ.preimage ha.continuous
    have hb : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞ b U₀ :=
      O.smooth_originalPresentation_symm.comp_contMDiffOn
        (contMDiff_fst.contMDiffOn.prodMk (hj'.comp ha.contMDiffOn (fun _ hp => hp)))
    let k := (O.collars parameterZero).originalInclusion
    have hk : IsOpen (range k.map) := k.isLocalDiffeomorph.image.isOpen
    let U₁ : Set (ℝ × M.Point) := U₀ ∩ b ⁻¹' range k.map
    have hU₁ : IsOpen U₁ := hb.continuousOn.isOpen_inter_preimage hU₀ hk
    have hinverse := k.contMDiffOn_invFun
    have hformula (s : Parameter) (y : M.Point)
        (hy : y ∈ (A.collars parameterZero).localizedDomain.domain.carrier) :
        k.map (f s y) = b (s.val, y) := by
      have hym : (A.completionPresentation s).equiv y ∈
          (A.collars s).localizedDomain.domain.carrier := by
        rw [A.completionPresentation_eq s, ← (A.compactPresentation s).carrier]
        exact ⟨y, hy, rfl⟩
      have hproj := O.original_projection s (f s y)
      change (O.collars s).originalInclusion.map
        ((O.compactPresentation s).extensionEquiv (f s y)) =
        (O.originalPresentation s.val).extensionEquiv (k.map (f s y)) at hproj
      rw [← O.completionPresentation_eq s] at hproj
      change (O.collars s).originalInclusion.map
        ((O.completionPresentation s).equiv
          ((O.completionPresentation s).equiv.symm
            (q s ((A.completionPresentation s).equiv y)))) = _ at hproj
      rw [(O.completionPresentation s).equiv.apply_symm_apply, hsquare s _ hym] at hproj
      have hasource : (A.collars s).originalInclusion.map
          ((A.completionPresentation s).equiv y) = (a (s.val, y)).2 := by
        rw [A.completionPresentation_eq s]
        exact A.original_projection s y
      calc
        k.map (f s y) = (O.originalPresentation s.val).extensionEquiv.symm
            (j s ((A.collars s).originalInclusion.map ((A.completionPresentation s).equiv y))) :=
          ((congrArg (O.originalPresentation s.val).extensionEquiv.symm hproj).trans
            ((O.originalPresentation s.val).extensionEquiv.symm_apply_apply _)).symm
        _ = b (s.val, y) := by
          dsimp only [b]
          rw [congrFun (hj'eq s), hasource]
    intro t x hx
    let U : TopologicalSpace.Opens (ℝ × M.Point) :=
      ⟨U₁ ∩ (univ ×ˢ interior (A.collars parameterZero).localizedDomain.domain.carrier),
        hU₁.inter (isOpen_univ.prod isOpen_interior)⟩
    have hcenter : (t.val, x) ∈ U := by
      refine ⟨⟨hΩcover ⟨t.property, mem_univ _⟩, ?_⟩, mem_univ _, hx⟩
      exact ⟨f t x, hformula t x (interior_subset hx)⟩
    let γ : U → N.Point := fun p => Function.invFun k.map (b p.val)
    have hγ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞ γ := by
      have hs : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
          (fun p : ℝ × M.Point => Function.invFun k.map (b p)) U :=
        hinverse.comp (hb.mono (fun _ hp => hp.1.1)) (fun _ hp => hp.1.2)
      intro p
      exact (hs.contMDiffAt (U.isOpen.mem_nhds p.property)).comp p
        contMDiff_subtype_val.contMDiffAt
    refine ⟨U, hcenter, γ, hγ, ?_⟩
    intro s y hy
    change Function.invFun k.map (b (s.val, y)) = f s y
    rw [← hformula s y (interior_subset hy.2.2)]
    exact Function.leftInverse_invFun k.embedding.injective _
  have hf : HasSmoothManifoldTargetFamilyOn M N univ (fun t => f t) :=
    hasSmoothManifoldTargetFamilyOn_of_interior_absorption M N (fun t => f t)
      (interior (A.collars parameterZero).localizedDomain.domain.carrier) φ ψ
      hφ hψ habsorb hreturn hcompact
  exact ⟨hf, hf.inverse M N f⟩

end LocalizedCompletionFamily
end FsFltz.Geometry
