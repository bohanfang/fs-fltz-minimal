import FsFltz.Geometry.BoundaryMapBridge
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Smooth dependence of induced completion boundary coordinates

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 183–189, and `sec:lean`,
lines 805–814. Local inverses are constructed in the actual manifold charts.
-/

noncomputable section
open scoped Manifold ContDiff
open Topology Set Filter

namespace FsFltz.Geometry
open SmoothManifold

/-- The finite-dimensional inverse function theorem for arbitrary boundaryless
source and target manifolds, expressed using their native smooth atlases. -/
theorem isLocalDiffeomorph_of_bijective_mfderiv_manifold
    {E F M N : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [TopologicalSpace N] [ChartedSpace F N]
    [IsManifold 𝓘(ℝ, F) ∞ N] {f : M → N}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hd : ∀ z, Function.Bijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z)) :
    IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f := by
  intro a
  let c₀ := chartAt E a
  let c := chartAt F (f a)
  let g : E → F := c ∘ f ∘ c₀.symm
  have hcg (z : E) (hz₀ : z ∈ c₀.target) (hz : f (c₀.symm z) ∈ c.source) :
      ContDiffAt ℝ ∞ g z := by
    have h₀ := (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (n := ∞) (x := a)).contMDiffAt
      (c₀.open_target.mem_nhds hz₀)
    have h₁ := (contMDiffOn_chart (I := 𝓘(ℝ, F)) (n := ∞) (x := f a)).contMDiffAt
      (c.open_source.mem_nhds hz)
    exact ((h₁.comp (c₀.symm z) (hf (c₀.symm z))).comp z h₀).contDiffAt
  have hgd (z : E) (hz₀ : z ∈ c₀.target) (hz : f (c₀.symm z) ∈ c.source) :
      Function.Bijective (fderiv ℝ g z) := by
    have h₀ := (mdifferentiable_chart (I := 𝓘(ℝ, E)) a).symm.mdifferentiableAt hz₀
    have h₁ := (mdifferentiable_chart (I := 𝓘(ℝ, F)) (f a)).mdifferentiableAt hz
    change Function.Bijective (fderiv ℝ ((c ∘ f) ∘ c₀.symm) z)
    have he := mfderiv_comp (f := c₀.symm) (g := c ∘ f) z
      (h₁.comp (c₀.symm z) (hf.mdifferentiable (by simp) (c₀.symm z))) h₀
    rw [mfderiv_comp (c₀.symm z) h₁ (hf.mdifferentiable (by simp) (c₀.symm z)),
      mfderiv_eq_fderiv] at he
    rw [he]
    exact (((mdifferentiable_chart (I := 𝓘(ℝ, F)) (f a)).mfderiv_bijective hz).comp
      (hd (c₀.symm z))).comp
      ((mdifferentiable_chart (I := 𝓘(ℝ, E)) a).symm.mfderiv_bijective hz₀)
  let A (z : E) (hz₀ : z ∈ c₀.target) (hz : f (c₀.symm z) ∈ c.source) : E ≃L[ℝ] F :=
    (LinearEquiv.ofBijective (fderiv ℝ g z).toLinearMap (hgd z hz₀ hz)).toContinuousLinearEquiv
  have hder (z : E) (hz₀ : z ∈ c₀.target) (hz : f (c₀.symm z) ∈ c.source) :
      HasFDerivAt g (A z hz₀ hz : E →L[ℝ] F) z :=
    (hcg z hz₀ hz).differentiableAt (by simp) |>.hasFDerivAt
  have ha₀ : a ∈ c₀.source := mem_chart_source E a
  have ha : f (c₀.symm (c₀ a)) ∈ c.source := by
    rw [c₀.left_inv ha₀]
    exact mem_chart_source F (f a)
  let e₀ := (hcg (c₀ a) (c₀.map_source ha₀) ha).toOpenPartialHomeomorph g
    (hder (c₀ a) (c₀.map_source ha₀) ha) (by simp)
  let t₀ := (c₀.trans e₀).trans c.symm
  let t := t₀.restrOpen (f ⁻¹' c.source) (c.open_source.preimage hf.continuous)
  have heq : Set.EqOn f t t.source := by
    intro z hz
    have hz₀ : z ∈ c₀.source := hz.1.1.1
    have hz' : f z ∈ c.source := hz.2
    change f z = c.symm (g (c₀ z))
    simp only [g, Function.comp_apply, c₀.left_inv hz₀, c.left_inv hz']
  refine ⟨{ t.toPartialEquiv with
      open_source := t.open_source
      open_target := t.open_target
      contMDiffOn_toFun := hf.contMDiffOn.congr heq.symm
      contMDiffOn_invFun := ?_ }, ?_, heq⟩
  · intro y hy
    have hcy : c y ∈ e₀.target := hy.1.2.1
    have hz₀ : e₀.symm (c y) ∈ c₀.target := hy.1.2.2
    have hz : f (c₀.symm (e₀.symm (c y))) ∈ c.source := hy.2
    have hinv : ContDiffAt ℝ ∞ e₀.symm (c y) :=
      e₀.contDiffAt_symm hcy (hder _ hz₀ hz) (hcg _ hz₀ hz)
    have hchart := (contMDiffOn_chart (I := 𝓘(ℝ, F)) (n := ∞) (x := f a)).contMDiffAt
      (c.open_source.mem_nhds hy.1.1)
    have hsource := (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (n := ∞) (x := a)).contMDiffAt
      (c₀.open_target.mem_nhds hz₀)
    exact (hsource.comp y (hinv.contMDiffAt.comp y hchart)).contMDiffWithinAt
  · refine ⟨⟨⟨ha₀, ?_⟩, ?_⟩, ?_⟩
    · exact (hcg (c₀ a) (c₀.map_source ha₀) ha).mem_toOpenPartialHomeomorph_source
        (hder (c₀ a) (c₀.map_source ha₀) ha) (by simp)
    · change g (c₀ a) ∈ c.target
      simpa only [g, Function.comp_apply, c₀.left_inv ha₀] using
        c.map_source (mem_chart_source F (f a))
    · exact mem_chart_source F (f a)

namespace Completion

/-- The smooth extension of a compact inclusion is a local diffeomorphism:
its injective tangent map is bijective in the equal ambient dimensions. -/
theorem inclusion_isLocalDiffeomorph {d : ℕ} {D : LiouvilleDomain d}
    (C : Completion D) :
    IsLocalDiffeomorph 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ C.inclusion.map := by
  apply isLocalDiffeomorph_of_bijective_mfderiv_manifold C.inclusion.map.contMDiff
  intro x
  exact ⟨C.inclusion.immersion x,
    LinearMap.injective_iff_surjective.mp (C.inclusion.immersion x)⟩

/-- The all-real-time end parametrization has a native smooth local inverse.
Dimension zero is handled by its empty boundary. -/
theorem endMap_isLocalDiffeomorph {d : ℕ} {D : LiouvilleDomain d} (C : Completion D) :
    IsLocalDiffeomorph ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, Model d)) ∞ C.endMap := by
  by_cases hd₀ : d = 0
  · subst d
    have : IsEmpty D.domain.boundary.Point := D.domain.zero_boundary rfl
    intro p
    exact isEmptyElim p.1
  · have hprod : IsManifold ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))) ∞
        (D.domain.boundary.Point × ℝ) := inferInstance
    rw [← modelWithCornersSelf_prod]
    let : ChartedSpace (Model (d - 1) × ℝ) (D.domain.boundary.Point × ℝ) :=
      prodChartedSpace (Model (d - 1)) D.domain.boundary.Point ℝ ℝ
    have : IsManifold 𝓘(ℝ, Model (d - 1) × ℝ) ∞ (D.domain.boundary.Point × ℝ) := by
      rw [← modelWithCornersSelf_prod] at hprod
      exact hprod
    apply isLocalDiffeomorph_of_bijective_mfderiv_manifold
    · have hs := C.smooth_endMap
      rw [← modelWithCornersSelf_prod] at hs
      exact hs
    · intro p
      have heq : Module.finrank ℝ (Model (d - 1) × ℝ) = Module.finrank ℝ (Model d) := by
        simp only [Module.finrank_prod, Model, finrank_euclideanSpace_fin, Module.finrank_self]
        omega
      have hi : Function.Injective
          (mfderiv 𝓘(ℝ, Model (d - 1) × ℝ) 𝓘(ℝ, Model d) C.endMap p) := by
        have hi := C.end_immersion p
        rw [← modelWithCornersSelf_prod] at hi
        exact hi
      exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mp hi⟩

/-- If a smooth map takes values in the end's all-real-time range, its unique
end coordinates are smooth. No continuity of the coordinate selection is
assumed: injectivity identifies it with the native smooth local inverse. -/
theorem contMDiff_coordinates {d k : ℕ} {D : LiouvilleDomain d} (C : Completion D)
    (M : SmoothManifold k) (u : M.Point → C.ambient.manifold.Point)
    (hu : ContMDiff 𝓘(ℝ, Model k) 𝓘(ℝ, Model d) ∞ u)
    (p : M.Point → D.domain.boundary.Point × ℝ)
    (hp : ∀ x, C.endMap (p x) = u x) :
    ContMDiff 𝓘(ℝ, Model k) ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))) ∞ p := by
  intro x
  have hloc := C.endMap_isLocalDiffeomorph (p x)
  have hinv : ContMDiffAt 𝓘(ℝ, Model d)
      ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))) ∞ hloc.localInverse (u x) := by
    rw [← hp x]
    exact hloc.localInverse_contMDiffAt
  apply (hinv.comp x (hu x)).congr_of_eventuallyEq
  have ht : Tendsto u (𝓝 x) (𝓝 (C.endMap (p x))) := by
    rw [hp x]
    exact (hu x).continuousAt
  filter_upwards [hloc.localInverse_eventuallyEq_right.comp_tendsto ht] with y hy
  apply C.endMap_injective
  exact (hp y).trans hy.symm

/-- The unique boundary representatives and shifts produced by a strict
completion diffeomorphism vary jointly smoothly in the boundary point. -/
theorem exists_smooth_boundary_coordinates {d e : ℕ} {D : LiouvilleDomain d}
    {E : LiouvilleDomain e} (C : Completion D) (C' : Completion E)
    (f : C.ambient.manifold.SmoothEquiv C'.ambient.manifold)
    (hprimitive : C.ambient.manifold.pullback C'.ambient.manifold f
      C'.ambient.primitive = C.ambient.primitive) :
    ∃ p : D.domain.boundary.Point → E.domain.boundary.Point × ℝ,
      ContMDiff 𝓘(ℝ, Model (d - 1))
        ((𝓘(ℝ, Model (e - 1))).prod (𝓘(ℝ, ℝ))) ∞ p ∧
      ∀ (x : D.domain.boundary.Point) (r : ℝ),
        f (C.endMap (x, r)) = C'.endMap ((p x).1, r + (p x).2) := by
  classical
  choose p hp using fun x => (C.existsUnique_boundary_coordinates C' f hprimitive x).exists
  refine ⟨p, ?_, hp⟩
  let u : D.domain.boundary.Point → C'.ambient.manifold.Point :=
    fun x => f (C.endMap (x, 0))
  have hu : ContMDiff 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model e) ∞ u :=
    f.contMDiff.comp (C.smooth_endMap.comp (contMDiff_id.prodMk contMDiff_const))
  exact C'.contMDiff_coordinates D.domain.boundary u hu p
    (fun x => by simpa only [u, zero_add] using (hp x 0).symm)

/-- A strict completion diffeomorphism induces an actual smooth boundary
diffeomorphism and smooth shift. Applying the same proved construction to its
strict inverse supplies the smooth inverse boundary map. The contact pullback
law is not a hypothesis of this construction. -/
theorem exists_boundaryEquiv {d e : ℕ} {D : LiouvilleDomain d}
    {E : LiouvilleDomain e} (C : Completion D) (C' : Completion E)
    (f : C.ambient.manifold.SmoothEquiv C'.ambient.manifold)
    (hprimitive : C.ambient.manifold.pullback C'.ambient.manifold f
      C'.ambient.primitive = C.ambient.primitive) :
    ∃ ψ : D.domain.boundary.SmoothEquiv E.domain.boundary,
      ∃ s : D.domain.boundary.Point → ℝ,
        ContMDiff 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, ℝ) ∞ s ∧
        ∀ (x : D.domain.boundary.Point) (r : ℝ),
          f (C.endMap (x, r)) = C'.endMap (ψ x, r + s x) := by
  obtain ⟨p, hps, hp⟩ := C.exists_smooth_boundary_coordinates C' f hprimitive
  have hprimitive' : C'.ambient.manifold.pullback C.ambient.manifold f.symm
      C.ambient.primitive = C'.ambient.primitive := by
    rw [← hprimitive]
    exact C.ambient.manifold.pullback_symm_pullback C'.ambient.manifold f C'.ambient.primitive
  obtain ⟨q, hqs, hq⟩ := C'.exists_smooth_boundary_coordinates C f.symm hprimitive'
  have hi (x : D.domain.boundary.Point) : (q (p x).1).1 = x := by
    have he := congrArg f.symm (hp x 0)
    simp only [zero_add, f.symm_apply_apply] at he
    rw [hq] at he
    exact (congrArg Prod.fst (C.endMap_injective he)).symm
  have hj (y : E.domain.boundary.Point) : (p (q y).1).1 = y := by
    have he := congrArg f (hq y 0)
    simp only [zero_add, f.apply_symm_apply] at he
    rw [hp] at he
    exact (congrArg Prod.fst (C'.endMap_injective he)).symm
  let ψ : D.domain.boundary.SmoothEquiv E.domain.boundary :=
    { toFun := fun x => (p x).1
      invFun := fun y => (q y).1
      left_inv := hi
      right_inv := hj
      contMDiff_toFun := hps.fst
      contMDiff_invFun := hqs.fst }
  exact ⟨ψ, fun x => (p x).2, hps.snd, hp⟩

end Completion

end FsFltz.Geometry
