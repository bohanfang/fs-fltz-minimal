import FsFltz.Geometry.BoundarySmooth

/-!
# Local smooth inverse from an open smooth domain

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–189, and
`sec:lean`, lines 805–814. A map smooth on a genuine open neighborhood,
whose actual differential is bijective at one point, has a smooth local
inverse. The construction shrinks to the open set of invertible coordinate
differentials and uses the normed inverse function theorem in actual charts.
The open-domain hypothesis retains one common domain for all derivatives;
bare pointwise `C^∞` regularity is not substituted for it.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry

/-- The local finite-dimensional manifold inverse function theorem on an
actual open smooth domain, requiring invertibility at only the chosen point. -/
theorem isLocalDiffeomorphAt_of_bijective_mfderiv_manifold
    {E F M N : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [TopologicalSpace N] [ChartedSpace F N]
    [IsManifold 𝓘(ℝ, F) ∞ N] {f : M → N} {U : Set M} {a : M}
    (hU : IsOpen U) (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f U) (haU : a ∈ U)
    (hd : Function.Bijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f a)) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f a := by
  let c₀ := chartAt E a
  let c := chartAt F (f a)
  let g : E → F := c ∘ f ∘ c₀.symm
  let S : Set E := c₀.target ∩ c₀.symm ⁻¹' (U ∩ f ⁻¹' c.source)
  have hS : IsOpen S := c₀.continuousOn_symm.isOpen_inter_preimage c₀.open_target
    (hf.continuousOn.isOpen_inter_preimage hU c.open_source)
  have hcg (z : E) (hz : z ∈ S) : ContDiffAt ℝ ∞ g z := by
    have h₀ := (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (n := ∞) (x := a)).contMDiffAt
      (c₀.open_target.mem_nhds hz.1)
    have h₁ := (contMDiffOn_chart (I := 𝓘(ℝ, F)) (n := ∞) (x := f a)).contMDiffAt
      (c.open_source.mem_nhds hz.2.2)
    exact ((h₁.comp (c₀.symm z) (hf.contMDiffAt (hU.mem_nhds hz.2.1))).comp z h₀).contDiffAt
  have ha₀ : a ∈ c₀.source := mem_chart_source E a
  have haS : c₀ a ∈ S := by
    refine ⟨c₀.map_source ha₀, ?_⟩
    change c₀.symm (c₀ a) ∈ U ∩ f ⁻¹' c.source
    rw [c₀.left_inv ha₀]
    exact ⟨haU, mem_chart_source F (f a)⟩
  have hgd : Function.Bijective (fderiv ℝ g (c₀ a)) := by
    have h₀ := (mdifferentiable_chart (I := 𝓘(ℝ, E)) a).symm.mdifferentiableAt haS.1
    have h₁ := (mdifferentiable_chart (I := 𝓘(ℝ, F)) (f a)).mdifferentiableAt haS.2.2
    have hfa := (hf.contMDiffAt (hU.mem_nhds haS.2.1)).mdifferentiableAt (by simp)
    have he := mfderiv_comp (f := c₀.symm) (g := c ∘ f) (c₀ a)
      (h₁.comp (c₀.symm (c₀ a)) hfa) h₀
    rw [mfderiv_comp (c₀.symm (c₀ a)) h₁ hfa, mfderiv_eq_fderiv] at he
    change Function.Bijective (fderiv ℝ ((c ∘ f) ∘ c₀.symm) (c₀ a))
    rw [he]
    have hd' : Function.Bijective
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (c₀.symm (c₀ a))) := by
      rwa [c₀.left_inv ha₀]
    exact (((mdifferentiable_chart (I := 𝓘(ℝ, F)) (f a)).mfderiv_bijective haS.2.2).comp hd').comp
      ((mdifferentiable_chart (I := 𝓘(ℝ, E)) a).symm.mfderiv_bijective haS.1)
  let A₀ : E ≃L[ℝ] F :=
    (LinearEquiv.ofBijective (fderiv ℝ g (c₀ a)).toLinearMap hgd).toContinuousLinearEquiv
  have hgS : ContDiffOn ℝ ∞ g S := fun z hz => (hcg z hz).contDiffWithinAt
  let T : Set E := S ∩ (fderiv ℝ g) ⁻¹' {L | L.IsInvertible}
  have hT : IsOpen T := (hgS.continuousOn_fderiv_of_isOpen hS (by simp)).isOpen_inter_preimage
    hS ContinuousLinearMap.isOpen_setOfPred_isInvertible
  have haT : c₀ a ∈ T := ⟨haS, ⟨A₀, rfl⟩⟩
  let A (z : E) (hz : z ∈ T) : E ≃L[ℝ] F := hz.2.choose
  have hder (z : E) (hz : z ∈ T) : HasFDerivAt g (A z hz : E →L[ℝ] F) z := by
    rw [show (A z hz : E →L[ℝ] F) = fderiv ℝ g z from hz.2.choose_spec]
    exact (hcg z hz.1).differentiableAt (by simp) |>.hasFDerivAt
  let e₀ := (hcg (c₀ a) haS).toOpenPartialHomeomorph g (hder (c₀ a) haT) (by simp)
  let e := e₀.restrOpen T hT
  let t := (c₀.trans e).trans c.symm
  have heq : EqOn f t t.source := by
    intro z hz
    have hz₀ : z ∈ c₀.source := hz.1.1
    have hzT : c₀ z ∈ T := hz.1.2.2
    have hz' : f z ∈ c.source := by
      have h := hzT.1.2.2
      rwa [c₀.left_inv hz₀] at h
    change f z = c.symm (g (c₀ z))
    simp only [g, Function.comp_apply, c₀.left_inv hz₀, c.left_inv hz']
  have hsub : t.source ⊆ U := by
    intro z hz
    have h := hz.1.2.2.1.2.1
    change c₀.symm (c₀ z) ∈ U at h
    rwa [c₀.left_inv hz.1.1] at h
  refine ⟨{ t.toPartialEquiv with
      open_source := t.open_source
      open_target := t.open_target
      contMDiffOn_toFun := (hf.mono hsub).congr heq.symm
      contMDiffOn_invFun := ?_ }, ?_, heq⟩
  · intro y hy
    have hcy : c y ∈ e₀.target := hy.2.1.1
    have hzT : e₀.symm (c y) ∈ T := hy.2.1.2
    have hinv : ContDiffAt ℝ ∞ e₀.symm (c y) :=
      e₀.contDiffAt_symm hcy (hder _ hzT) (hcg _ hzT.1)
    have hchart := (contMDiffOn_chart (I := 𝓘(ℝ, F)) (n := ∞) (x := f a)).contMDiffAt
      (c.open_source.mem_nhds hy.1)
    have hsource := (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (n := ∞) (x := a)).contMDiffAt
      (c₀.open_target.mem_nhds hzT.1.1)
    exact (hsource.comp y (hinv.contMDiffAt.comp y hchart)).contMDiffWithinAt
  · refine ⟨⟨ha₀, ?_⟩, ?_⟩
    · exact ⟨(hcg (c₀ a) haS).mem_toOpenPartialHomeomorph_source (hder (c₀ a) haT) (by simp), haT⟩
    · change g (c₀ a) ∈ c.target
      simpa only [g, Function.comp_apply, c₀.left_inv ha₀] using
        c.map_source (mem_chart_source F (f a))

end FsFltz.Geometry
