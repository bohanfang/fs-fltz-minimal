import FsFltz.Geometry.IntrinsicCollar

/-!
# Common native coefficient neighborhoods from scalar smooth germs

Source: `geoemtric-part-fsf.tex`, differential-geometric conventions,
lines 119–122, `def:pair`, lines 132–160, and `sec:lean`, lines 783–814.
The source requires genuine smooth extensions across boundaries. Here
each scalar coefficient has its own open smooth extension neighborhood;
the common vector coefficient, chart containment, and collar are constructed.
Bare native `ContMDiff` at order infinity is not an extension hypothesis.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicCollar

variable {k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Independently extendible scalar coefficients of the actual chart-pushed
field produce one smooth vector coefficient on an open neighborhood. The
neighborhood's native half-space points are proved to belong to the chart
target, and the vector coefficient agrees there with the original field.
No common coefficient extension or chart containment is supplied. -/
theorem exists_local_coefficients_of_scalar_extensions
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    {Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x} {x : M} (hx : x ∈ e.source)
    (hscalar : ∀ i : Fin (k + 1),
      ∃ (f : Model (k + 1) → ℝ) (V : Set (Model (k + 1))),
        IsOpen V ∧ e.extend (𝓡∂ (k + 1)) x ∈ V ∧ ContDiffOn ℝ ∞ f V ∧
        f =ᶠ[𝓝[(e.extend (𝓡∂ (k + 1))).target] (e.extend (𝓡∂ (k + 1)) x)]
          (fun y => (show Model (k + 1) from
            mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
              (e.extend (𝓡∂ (k + 1))) ((e.extend (𝓡∂ (k + 1))).symm y)
                (Z ((e.extend (𝓡∂ (k + 1))).symm y))) i)) :
    ∃ (f : Model (k + 1) → Model (k + 1)) (U : Set (Model (k + 1))),
      IsOpen U ∧ e.extend (𝓡∂ (k + 1)) x ∈ U ∧ ContDiffOn ℝ ∞ f U ∧
      (∀ y ∈ U, 0 ≤ y 0 → y ∈ (e.extend (𝓡∂ (k + 1))).target) ∧
      ∀ y ∈ U, 0 ≤ y 0 → f y =
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (e.extend (𝓡∂ (k + 1)))
          ((e.extend (𝓡∂ (k + 1))).symm y)
            (Z ((e.extend (𝓡∂ (k + 1))).symm y)) := by
  classical
  let a := e.extend (𝓡∂ (k + 1)) x
  let C : Model (k + 1) → Model (k + 1) := fun y =>
    mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (e.extend (𝓡∂ (k + 1)))
      ((e.extend (𝓡∂ (k + 1))).symm y) (Z ((e.extend (𝓡∂ (k + 1))).symm y))
  choose f V hVo haV hf hagree using hscalar
  obtain ⟨A, hAo, hA⟩ := isOpen_induced_iff.mp e.open_target
  have haA : a ∈ A := by
    have ht := e.map_source hx
    rw [← hA] at ht
    exact ht
  have hV : ∀ᶠ y in 𝓝 a, ∀ i, y ∈ V i :=
    eventually_all.mpr (fun i => (hVo i).mem_nhds (haV i))
  have hEq : ∀ᶠ y in 𝓝 a,
      y ∈ (e.extend (𝓡∂ (k + 1))).target → ∀ i, f i y = C y i := by
    apply eventually_nhdsWithin_iff.mp
    exact eventually_all.mpr hagree
  obtain ⟨U, hUP, hU, haU⟩ := mem_nhds_iff.mp
    (show {y | (∀ i, y ∈ V i) ∧
        (y ∈ (e.extend (𝓡∂ (k + 1))).target → ∀ i, f i y = C y i) ∧ y ∈ A}
      ∈ 𝓝 a from hV.and (hEq.and (hAo.mem_nhds haA)))
  let F : Model (k + 1) → Model (k + 1) :=
    fun y => WithLp.toLp 2 (fun i => f i y)
  have htarget : ∀ y ∈ U, 0 ≤ y 0 → y ∈ (e.extend (𝓡∂ (k + 1))).target := by
    intro y hy hn
    let z : EuclideanHalfSpace (k + 1) := ⟨y, hn⟩
    have hz : (𝓡∂ (k + 1)).symm y = z := (𝓡∂ (k + 1)).left_inv z
    rw [OpenPartialHomeomorph.extend_target]
    refine ⟨?_, ?_⟩
    · change (𝓡∂ (k + 1)).symm y ∈ e.target
      rw [hz, ← hA]
      exact (hUP hy).2.2
    · exact ⟨z, rfl⟩
  refine ⟨F, U, hU, haU, ?_, htarget, ?_⟩
  · apply contDiffOn_euclidean.mpr
    intro i
    exact (hf i).mono (fun y hy => (hUP hy).1 i)
  · intro y hy hn
    apply PiLp.ext
    intro i
    exact (hUP hy).2.1 (htarget y hy hn) i

/-- Scalar source extension germs and strict inwardness construct an actual
native collar on an open subset of the literal intrinsic boundary. The
chart, scalar coefficients, and inward inequality are local input; its
common vector extension, width, map, smoothness and open embedding are
conclusions. The resulting trajectories solve the original native ODE. -/
theorem exists_boundary_local_collar_of_scalar_extensions
    (c : IntrinsicBoundary.Chart k M) {x : IntrinsicBoundary.Point k M}
    (hx : x ∈ c.chart.source)
    (Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x)
    (hscalar : ∀ i : Fin (k + 1),
      ∃ (f : Model (k + 1) → ℝ) (V : Set (Model (k + 1))),
        IsOpen V ∧ c.ambient.extend (𝓡∂ (k + 1)) x.val ∈ V ∧
        ContDiffOn ℝ ∞ f V ∧
        f =ᶠ[𝓝[(c.ambient.extend (𝓡∂ (k + 1))).target]
          (c.ambient.extend (𝓡∂ (k + 1)) x.val)]
          (fun y => (show Model (k + 1) from
            mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
              (c.ambient.extend (𝓡∂ (k + 1)))
              ((c.ambient.extend (𝓡∂ (k + 1))).symm y)
                (Z ((c.ambient.extend (𝓡∂ (k + 1))).symm y))) i))
    (hin : 0 < (show Model (k + 1) from
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
        (c.ambient.extend (𝓡∂ (k + 1))) x.val (Z x.val)) 0) :
    ∃ (γ : ℝ × IntrinsicBoundary.Point k M → M)
      (U : Set (IntrinsicBoundary.Point k M)) (δ : ℝ),
      IsOpen U ∧ x ∈ U ∧ 0 < δ ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞
        γ (Ico 0 δ ×ˢ U) ∧
      Topology.IsOpenEmbedding (fun p : Ico 0 δ ×ˢ U => γ p.val) ∧
      (∀ p ∈ Ico 0 δ ×ˢ U, ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
        ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (γ p) ∧
          ∀ᶠ q in 𝓝[Ico 0 δ ×ˢ U] p, g (γ q) = q) ∧
      (∀ y ∈ U, γ (0, y) = y.val) ∧
      (∀ y ∈ U, IsMIntegralCurveOn (fun t => γ (t, y)) Z (Ico 0 δ)) ∧
      ∀ y ∈ U, ∀ t ∈ Ico 0 δ,
        (𝓡∂ (k + 1)).IsBoundaryPoint (γ (t, y)) ↔ t = 0 := by
  let e := c.ambient
  have hex : x.val ∈ e.source := by
    have h := hx
    rw [c.source_eq] at h
    exact h
  have hcoord : boundaryInsert k (c.chart x) = e.extend (𝓡∂ (k + 1)) x.val := by
    rw [c.toFun_eq x hx]
    apply boundaryInsert_drop
    exact (IntrinsicBoundary.isBoundaryPoint_iff_chart_zero c.mem_atlas hex).mp x.property
  obtain ⟨f, A, hA, hxA, hf, htarget, hcoeff⟩ :=
    exists_local_coefficients_of_scalar_extensions hex hscalar
  have hinf : 0 < f (boundaryInsert k (c.chart x)) 0 := by
    rw [hcoord, hcoeff _ hxA (e x.val).property,
      (e.extend (𝓡∂ (k + 1))).left_inv (by simpa only [e.extend_source] using hex)]
    exact hin
  obtain ⟨a, V, δ, hV, hxV, hδ, ha, haopen, hainv, hzero, hode, hboundary, huniq⟩ :=
    exists_native_local_collar c.mem_atlas Z hA hf (by rwa [hcoord]) htarget hcoeff hinf
  let U : Set (IntrinsicBoundary.Point k M) := c.chart.source ∩ c.chart ⁻¹' V
  let γ : ℝ × IntrinsicBoundary.Point k M → M := fun p => a (p.1, c.chart p.2)
  have hU : IsOpen U := c.chart.continuousOn.isOpen_inter_preimage c.chart.open_source hV
  have hxU : x ∈ U := ⟨hx, hxV⟩
  have hmaps : MapsTo (fun p : ℝ × IntrinsicBoundary.Point k M => (p.1, c.chart p.2))
      (Ico 0 δ ×ˢ U) (Ico 0 δ ×ˢ V) := fun _ hp => ⟨hp.1, hp.2.2⟩
  have hc : ContMDiffOn 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) ∞ c.chart c.chart.source :=
    contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas ⟨c, rfl⟩)
  have hcs : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) 𝓘(ℝ, Model k) ∞
      (fun p : ℝ × IntrinsicBoundary.Point k M => c.chart p.2) (Ico 0 δ ×ˢ U) :=
    hc.comp contMDiff_snd.contMDiffOn (fun _ hp => hp.2.1)
  have hP : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) 𝓘(ℝ, ℝ × Model k) ∞
      (fun p : ℝ × IntrinsicBoundary.Point k M => (p.1, c.chart p.2))
      (Ico 0 δ ×ˢ U) := contMDiff_fst.contMDiffOn.prodMk_space hcs
  refine ⟨γ, U, δ, hU, hxU, hδ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ha.comp hP hmaps
  · let q : U → c.chart.source := fun y => ⟨y.val, y.property.1⟩
    have hq : Topology.IsOpenEmbedding q :=
      c.chart.open_source.isOpenEmbedding_subtypeVal.of_comp q hU.isOpenEmbedding_subtypeVal
    let r : U → V := fun y => ⟨c.chart y.val, y.property.2⟩
    have hr : Topology.IsOpenEmbedding r :=
      hV.isOpenEmbedding_subtypeVal.of_comp r (c.chart.isOpenEmbedding_restrict.comp hq)
    have hp := (Topology.IsOpenEmbedding.id (X := Ico (0 : ℝ) δ)).prodMap hr
    have hprod := (Homeomorph.Set.prod (Ico (0 : ℝ) δ) V).symm.isOpenEmbedding.comp
      (hp.comp (Homeomorph.Set.prod (Ico (0 : ℝ) δ) U).isOpenEmbedding)
    exact haopen.comp hprod
  · intro p hp
    obtain ⟨g₀, hg₀, heq⟩ := hainv (p.1, c.chart p.2) (hmaps hp)
    have heq' : ∀ᶠ q in 𝓝[Ico 0 δ ×ˢ U] p,
        g₀ (γ q) = (q.1, c.chart q.2) :=
      (hP p hp).continuousWithinAt.tendsto_nhdsWithin hmaps |>.eventually heq
    have hcenter : g₀ (γ p) = (p.1, c.chart p.2) :=
      Filter.EventuallyEq.eq_of_nhdsWithin
        (f := fun q => g₀ (γ q)) (g := fun q => (q.1, c.chart q.2)) heq' hp
    let g : M → ℝ × IntrinsicBoundary.Point k M :=
      fun z => ((g₀ z).1, c.chart.symm (g₀ z).2)
    have hg₀fst := (contMDiffAt_prod_module_iff g₀).mp hg₀ |>.1
    have hg₀snd := (contMDiffAt_prod_module_iff g₀).mp hg₀ |>.2
    have hci : ContMDiffAt 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) ∞ c.chart.symm (g₀ (γ p)).2 := by
      rw [hcenter]
      exact contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas ⟨c, rfl⟩) (c.chart.map_source hp.2.1)
    refine ⟨g, hg₀fst.prodMk (hci.comp (γ p) hg₀snd), ?_⟩
    filter_upwards [heq', self_mem_nhdsWithin] with q hq hqmem
    change ((g₀ (γ q)).1, c.chart.symm (g₀ (γ q)).2) = q
    rw [hq, c.chart.left_inv hqmem.2.1]
  · intro y hy
    change a (0, c.chart y) = y.val
    rw [hzero _ hy.2]
    rw [← c.invFun_eq _ (c.chart.map_source hy.1), c.chart.left_inv hy.1]
  · intro y hy
    exact hode (c.chart y) hy.2
  · intro y hy t ht
    exact (hboundary (c.chart y) hy.2 t ht).2

end FsFltz.Geometry.IntrinsicCollar
