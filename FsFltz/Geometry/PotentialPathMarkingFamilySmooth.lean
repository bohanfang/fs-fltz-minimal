import FsFltz.Geometry.TailoringRoundedMarkingFamilyAssembly
import FsFltz.Geometry.PotentialPathPrimitiveFamily

/-!
# Smooth ambient markings on the retained holomorphic completions

Source: `geometric-part-fsf-proof.tex`, `lem:absorption`, lines 444–468,
`lem:markedfamily`, lines 975–1049, and smooth markings, lines 1270–1303.
The actual compact square and native primitive families prove real smooth
germs of the supplied marking maps and their same inverses. No completed
map regularity is a premise.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry
open SmoothManifold IntrinsicSmoothBundle

namespace LocalizedCompletionFamily

/-- Actual strict slice markings into a common native ambient are jointly
smooth, with jointly smooth inverses, in the retained completion coordinates.
The primitive and original compact map families supply all real germs. -/
theorem markingFamily_realGerms_into_fixed_ambient
    {d : ℕ} {E : CompactDomain d} {L : Parameter → LiouvilleStructure E}
    (A : LocalizedCompletionFamily E L) (N : SmoothManifold d)
    (η : Parameter → N.Form 1) (P : ∀ t, CompletePrimitive N (η t))
    (hη : N.IsSmoothIntervalFormFamily η)
    (j : Parameter → E.extension.Point → N.Point)
    (hj : E.extension.IsSmoothIntervalMapFamily N j)
    (q : ∀ t, (A.collars t).cylindricalCompletion.ambient.manifold.SmoothEquiv N)
    (hq : ∀ t, (A.collars t).cylindricalCompletion.ambient.manifold.pullback
      N (q t) (η t) = (A.collars t).cylindricalCompletion.ambient.primitive)
    (hsquare : ∀ t x, x ∈ (A.collars t).localizedDomain.domain.carrier →
      q t x = j t ((A.collars t).originalInclusion.map x)) :
    let M := (A.collars parameterZero).cylindricalCompletion.ambient.manifold
    let f := fun t => (A.completionPresentation t).equiv.trans (q t)
    HasSmoothManifoldTargetFamilyOn M N univ (fun t => f t) ∧
      HasSmoothManifoldTargetFamilyOn N M univ (fun t => (f t).symm) := by
  classical
  dsimp only
  let M := (A.collars parameterZero).cylindricalCompletion.ambient.manifold
  let f : Parameter → M.SmoothEquiv N := fun t =>
    (A.completionPresentation t).equiv.trans (q t)
  let φ : Parameter → ℝ → M.Point → M.Point := fun t r x =>
    (A.completionPresentation t).equiv.symm
      ((A.collars t).cylindricalCompletion.ambient.completeFlow.flow r
        ((A.completionPresentation t).equiv x))
  let ψ : Parameter → ℝ → N.Point → N.Point := fun t r x => (P t).completeFlow.flow r x
  have hφ : HasRealSmoothFlowGermsOn M univ φ :=
    completeFlowInCoordinates_realGerms_of_smooth_primitive
      (fun t => (A.collars t).cylindricalCompletion.ambient) M
      (fun t => (A.completionPresentation t).equiv.symm) univ A.completedPrimitive_smooth
  have hψ : HasRealSmoothFlowGermsOn N univ ψ := by
    have hη' : N.IsSmoothIntervalFormFamily (fun t =>
        N.pullback N (Diffeomorph.refl 𝓘(ℝ, Model d) N.Point ∞).symm
          (P t).toCompleteLiouvilleManifold.primitive) := by
      change N.IsSmoothIntervalFormFamily (fun t => N.pullback N id (η t))
      simpa only [N.pullback_id] using hη
    have h :=
      completeFlowInCoordinates_realGerms_of_smooth_primitive
        (fun t => (P t).toCompleteLiouvilleManifold) N
        (fun _ => Diffeomorph.refl 𝓘(ℝ, Model d) N.Point ∞) univ hη'
    change HasRealSmoothFlowGermsOn N univ ψ at h
    exact h
  have hreturn : ∀ t r x, ψ t r (f t (φ t (-r) x)) = f t x := by
    intro t r x
    dsimp only [ψ, φ, f]
    change (P t).completeFlow.flow r
      (q t ((A.completionPresentation t).equiv
        ((A.completionPresentation t).equiv.symm _))) = _
    rw [(A.completionPresentation t).equiv.apply_symm_apply]
    have he := (A.collars t).cylindricalCompletion.ambient.map_flow
      (P t).toCompleteLiouvilleManifold (q t) (hq t)
      ((A.completionPresentation t).equiv x) (-r)
    change q t ((A.collars t).cylindricalCompletion.ambient.completeFlow.flow (-r)
      ((A.completionPresentation t).equiv x)) =
      (P t).completeFlow.flow (-r) (q t ((A.completionPresentation t).equiv x)) at he
    rw [he, ← (P t).completeFlow.flow.map_add, add_neg_cancel, Flow.map_zero_apply]
    rfl
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
    let a : ℝ × M.Point → ℝ × E.extension.Point := fun p =>
      (p.1, (A.originalPresentation p.1).extensionEquiv
        ((A.collars parameterZero).originalInclusion.map p.2))
    have ha : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞ a :=
      contMDiff_fst.prodMk (A.smooth_originalPresentation.comp
        (contMDiff_fst.prodMk ((A.collars parameterZero).originalInclusion.map.contMDiff.comp
          contMDiff_snd)))
    let U₀ : Set (ℝ × M.Point) := a ⁻¹' Ω
    have hU₀ : IsOpen U₀ := hΩ.preimage ha.continuous
    let b : ℝ × M.Point → N.Point := fun p => j' p.1 (a p).2
    have hb : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞ b U₀ :=
      hj'.comp ha.contMDiffOn (fun _ hp => hp)
    have hformula (s : Parameter) (y : M.Point)
        (hy : y ∈ (A.collars parameterZero).localizedDomain.domain.carrier) :
        f s y = b (s.val, y) := by
      have hym : (A.completionPresentation s).equiv y ∈
          (A.collars s).localizedDomain.domain.carrier := by
        rw [A.completionPresentation_eq s, ← (A.compactPresentation s).carrier]
        exact ⟨y, hy, rfl⟩
      change q s ((A.completionPresentation s).equiv y) = _
      rw [hsquare s _ hym]
      have he : (A.collars s).originalInclusion.map ((A.completionPresentation s).equiv y) =
          (a (s.val, y)).2 := by
        rw [A.completionPresentation_eq s]
        exact A.original_projection s y
      rw [he]
      dsimp only [b, a]
      rw [congrFun (hj'eq s)]
    intro t x hx
    let U : TopologicalSpace.Opens (ℝ × M.Point) :=
      ⟨U₀ ∩ (univ ×ˢ interior (A.collars parameterZero).localizedDomain.domain.carrier),
        hU₀.inter (isOpen_univ.prod isOpen_interior)⟩
    have hcenter : (t.val, x) ∈ U :=
      ⟨hΩcover ⟨t.property, mem_univ _⟩, mem_univ _, hx⟩
    let γ : U → N.Point := fun p => b p.val
    have hγ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞ γ := by
      intro p
      exact (hb.contMDiffAt (hU₀.mem_nhds p.property.1)).comp p
        contMDiff_subtype_val.contMDiffAt
    exact ⟨U, hcenter, γ, hγ, fun s y hy => (hformula s y (interior_subset hy.2.2)).symm⟩
  have hf : HasSmoothManifoldTargetFamilyOn M N univ (fun t => f t) :=
    hasSmoothManifoldTargetFamilyOn_of_interior_absorption M N (fun t => f t)
      (interior (A.collars parameterZero).localizedDomain.domain.carrier) φ ψ
      hφ hψ habsorb hreturn hcompact
  exact ⟨hf, hf.inverse M N f⟩

end LocalizedCompletionFamily
end FsFltz.Geometry
