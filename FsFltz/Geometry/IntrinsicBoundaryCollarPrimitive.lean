import FsFltz.Geometry.IntrinsicNativeCollarPrimitive
import FsFltz.Geometry.IntrinsicOutwardSign

/-!
# Full primitive scaling on the same native boundary collar

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. Boundary charts reparameterize the same one-sided native
collar. The actual within differential is transported by the chain rule,
including the seam; no extension of the collar or primitive law is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ}

/-- Boundary chart reparameterization recovers every native tangent of the
one-sided collar source, including its arbitrary time component. -/
theorem mfderivWithin_boundary_chart_reparam
    {B : Type*} [TopologicalSpace B] [ChartedSpace (Model k) B]
    [IsManifold 𝓘(ℝ, Model k) ∞ B]
    (y : B) {δ t : ℝ} (ht : t ∈ Ico 0 δ)
    (r : ℝ) (v : TangentSpace 𝓘(ℝ, Model k) y) :
    let e := chartAt (Model k) y
    mfderivWithin 𝓘(ℝ, ℝ × Model k) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k))
      (fun p : ℝ × Model k => (p.1, e.symm p.2)) (Ico 0 δ ×ˢ e.target) (t, e y)
      (r, mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) e y v) = (r, v) := by
  dsimp only
  let e := chartAt (Model k) y
  have hy : y ∈ e.source := mem_chart_source _ y
  have hey : e y ∈ e.target := e.map_source hy
  have hs : UniqueMDiffWithinAt 𝓘(ℝ, ℝ × Model k) (Ico 0 δ ×ˢ e.target) (t, e y) :=
    ((uniqueDiffOn_Ico 0 δ).prod e.open_target.uniqueDiffOn _ ⟨ht, hey⟩).uniqueMDiffWithinAt
  have hi : MDifferentiableAt 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) e.symm (e y) :=
    (mdifferentiable_chart (I := 𝓘(ℝ, Model k)) y).mdifferentiableAt_symm hey
  have hf : HasMFDerivAt 𝓘(ℝ, ℝ × Model k) 𝓘(ℝ, ℝ)
      (Prod.fst : ℝ × Model k → ℝ) (t, e y)
      (ContinuousLinearMap.fst ℝ ℝ (Model k)) :=
    hasMFDerivAt_fst (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, Model k)) (t, e y)
  have hg : HasMFDerivAt 𝓘(ℝ, ℝ × Model k) 𝓘(ℝ, Model k)
      (Prod.snd : ℝ × Model k → Model k) (t, e y)
      (ContinuousLinearMap.snd ℝ ℝ (Model k)) :=
    hasMFDerivAt_snd (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, Model k)) (t, e y)
  have hq : HasMFDerivAt 𝓘(ℝ, ℝ × Model k) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k))
      (fun p : ℝ × Model k => (p.1, e.symm p.2)) (t, e y)
      ((ContinuousLinearMap.fst ℝ ℝ (Model k)).prod
        ((mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) e.symm (e y)).comp
          (ContinuousLinearMap.snd ℝ ℝ (Model k)))) :=
    hf.prodMk (hi.hasMFDerivAt.comp (t, e y) hg)
  rw [hq.hasMFDerivWithinAt.mfderivWithin hs]
  apply Prod.ext
  · rfl
  · exact congrArg (fun A => A v)
      ((mdifferentiable_chart (I := 𝓘(ℝ, Model k)) y).symm_comp_deriv hy)

/-- The inverse boundary chart smoothly reparameterizes the one-sided strip.
The chart target is open; the time strip remains one-sided. -/
theorem contMDiffOn_boundary_chart_reparam
    {B : Type*} [TopologicalSpace B] [ChartedSpace (Model k) B]
    [IsManifold 𝓘(ℝ, Model k) ∞ B] (y : B) (δ : ℝ) :
    let e := chartAt (Model k) y
    ContMDiffOn 𝓘(ℝ, ℝ × Model k) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞
      (fun p : ℝ × Model k => (p.1, e.symm p.2)) (Ico 0 δ ×ˢ e.target) := by
  dsimp only
  let e := chartAt (Model k) y
  have hf : ContMDiffOn 𝓘(ℝ, ℝ × Model k) 𝓘(ℝ, ℝ) ∞
      (Prod.fst : ℝ × Model k → ℝ) (Ico 0 δ ×ˢ e.target) :=
    contDiff_fst.contMDiff.contMDiffOn
  have hg : ContMDiffOn 𝓘(ℝ, ℝ × Model k) 𝓘(ℝ, Model k) ∞
      (Prod.snd : ℝ × Model k → Model k) (Ico 0 δ ×ˢ e.target) :=
    contDiff_snd.contMDiff.contMDiffOn
  have hi : ContMDiffOn 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) ∞ e.symm e.target :=
    contMDiffOn_chart_symm
  exact hf.prodMk (hi.comp hg (fun _ hp => hp.2))

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Reparameterizing a collar by a boundary chart preserves its actual full
within differential after transporting the spatial tangent by that chart. -/
theorem mfderivWithin_collar_boundary_chart
    (C : ℝ × IntrinsicBoundary.Point k M → M) {δ : ℝ}
    (hC : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ C
      (Ico 0 δ ×ˢ univ))
    (y : IntrinsicBoundary.Point k M) {t : ℝ} (ht : t ∈ Ico 0 δ)
    (r : ℝ) (v : TangentSpace 𝓘(ℝ, Model k) y) :
    let e := chartAt (Model k) y
    mfderivWithin 𝓘(ℝ, ℝ × Model k) (𝓡∂ (k + 1))
      (fun p : ℝ × Model k => C (p.1, e.symm p.2)) (Ico 0 δ ×ˢ e.target) (t, e y)
      (r, mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) e y v) =
      mfderivWithin (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) C
        (Ico 0 δ ×ˢ univ) (t, y) (r, v) := by
  dsimp only
  let e := chartAt (Model k) y
  let q : ℝ × Model k → ℝ × IntrinsicBoundary.Point k M := fun p => (p.1, e.symm p.2)
  let T : Set (ℝ × Model k) := Ico 0 δ ×ˢ e.target
  have hy : y ∈ e.source := mem_chart_source _ y
  have hp : (t, e y) ∈ T := ⟨ht, e.map_source hy⟩
  have hq : ContMDiffOn 𝓘(ℝ, ℝ × Model k) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ q T :=
    contMDiffOn_boundary_chart_reparam y δ
  have hmaps : MapsTo q T (Ico 0 δ ×ˢ (univ : Set (IntrinsicBoundary.Point k M))) :=
    fun _ hp => ⟨hp.1, mem_univ _⟩
  have hs : UniqueMDiffWithinAt 𝓘(ℝ, ℝ × Model k) T (t, e y) :=
    ((uniqueDiffOn_Ico 0 δ).prod e.open_target.uniqueDiffOn _ hp).uniqueMDiffWithinAt
  change mfderivWithin 𝓘(ℝ, ℝ × Model k) (𝓡∂ (k + 1)) (C ∘ q) T (t, e y)
    (r, mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) e y v) = _
  rw [mfderivWithin_comp (t, e y) ((hC _ (hmaps hp)).mdifferentiableWithinAt (by simp))
    ((hq _ hp).mdifferentiableWithinAt (by simp)) hmaps hs]
  change mfderivWithin (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) C
    (Ico 0 δ ×ˢ univ) (t, e.symm (e y))
    (mfderivWithin 𝓘(ℝ, ℝ × Model k) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) q T (t, e y)
      (r, mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) e y v)) = _
  rw [mfderivWithin_boundary_chart_reparam y ht r v, e.left_inv hy]

/-- The actual spatial differential of a collar at its seam is the actual
differential of the intrinsic boundary inclusion. Only the seam identity
and one-sided smoothness of the same collar are used. -/
theorem mfderivWithin_collar_seam
    (C : ℝ × IntrinsicBoundary.Point k M → M) {δ : ℝ} (hδ : 0 < δ)
    (hC : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ C
      (Ico 0 δ ×ˢ univ))
    (hzero : ∀ y, C (0, y) = y.val)
    (y : IntrinsicBoundary.Point k M) (v : TangentSpace 𝓘(ℝ, Model k) y) :
    mfderivWithin (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) C
      (Ico 0 δ ×ˢ univ) (0, y) (0, v) =
      mfderiv 𝓘(ℝ, Model k) (𝓡∂ (k + 1))
        (Subtype.val : IntrinsicBoundary.Point k M → M) y v := by
  let s : IntrinsicBoundary.Point k M → ℝ × IntrinsicBoundary.Point k M := fun z => (0, z)
  have hs : HasMFDerivAt 𝓘(ℝ, Model k) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) s y
      ((0 : TangentSpace 𝓘(ℝ, Model k) y →L[ℝ] ℝ).prod
        (ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, Model k) y))) :=
    (hasMFDerivAt_const (0 : ℝ) y).prodMk (hasMFDerivAt_id y)
  have hp : (0, y) ∈ Ico 0 δ ×ˢ (univ : Set (IntrinsicBoundary.Point k M)) :=
    ⟨⟨le_rfl, hδ⟩, mem_univ _⟩
  have hc := ((hC _ hp).mdifferentiableWithinAt (by simp)).hasMFDerivWithinAt.comp y
    (hs.hasMFDerivWithinAt (s := univ))
    (fun z _ => (show s z ∈ Ico 0 δ ×ˢ univ from ⟨⟨le_rfl, hδ⟩, mem_univ _⟩))
  have heq : C ∘ s = (Subtype.val : IntrinsicBoundary.Point k M → M) := funext hzero
  rw [heq] at hc
  have hd := hc.mfderivWithin (uniqueMDiffWithinAt_univ (I := 𝓘(ℝ, Model k)))
  rw [mfderivWithin_univ] at hd
  exact (congrArg (fun A => A v) hd).symm

/-- The full primitive law for the same native collar of the literal
intrinsic boundary. The time component is arbitrary, and the spatial
boundary primitive uses the actual differential of its inclusion. -/
theorem inward_boundary_pullbackWithin_eq_exp_mul_of_liouville
    (α : Form k M 1) (hα : IsLocallyExtendibleForm α)
    (Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x)
    (hZ : Contraction α (exteriorDerivative α) Z)
    (C : ℝ × IntrinsicBoundary.Point k M → M) {δ : ℝ} (hδ : 0 < δ)
    (hC : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ C
      (Ico 0 δ ×ˢ univ))
    (hode : ∀ y, IsMIntegralCurveOn (fun t => C (t, y)) (fun x => -Z x) (Ico 0 δ))
    (hzero : ∀ y, C (0, y) = y.val)
    {t : ℝ} (ht : t ∈ Ico 0 δ) (y : IntrinsicBoundary.Point k M)
    (r : ℝ) (v : TangentSpace 𝓘(ℝ, Model k) y) :
    α (C (t, y)) (fun _ =>
      mfderivWithin (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) C
        (Ico 0 δ ×ˢ univ) (t, y) (r, v)) =
      Real.exp (-t) * α y.val (fun _ =>
        mfderiv 𝓘(ℝ, Model k) (𝓡∂ (k + 1))
          (Subtype.val : IntrinsicBoundary.Point k M → M) y v) := by
  let e := chartAt (Model k) y
  let q : ℝ × Model k → ℝ × IntrinsicBoundary.Point k M := fun p => (p.1, e.symm p.2)
  let D : ℝ × Model k → M := C ∘ q
  have hy : y ∈ e.source := mem_chart_source _ y
  have hey : e y ∈ e.target := e.map_source hy
  have hq : ContMDiffOn 𝓘(ℝ, ℝ × Model k) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ q
      (Ico 0 δ ×ˢ e.target) := contMDiffOn_boundary_chart_reparam y δ
  have hD : ContMDiffOn 𝓘(ℝ, ℝ × Model k) (𝓡∂ (k + 1)) ∞ D
      (Ico 0 δ ×ˢ e.target) := hC.comp hq (fun _ hp => ⟨hp.1, mem_univ _⟩)
  have hodeD : ∀ z ∈ e.target,
      IsMIntegralCurveOn (fun s => D (s, z)) (fun x => -Z x) (Ico 0 δ) :=
    fun z _ => hode (e.symm z)
  have h := inward_pullbackWithin_eq_exp_mul_of_liouville α hα Z hZ D
    e.open_target hδ hD hodeD ht hey r
      (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) e y v)
  change α (C (t, e.symm (e y))) (fun _ =>
      mfderivWithin 𝓘(ℝ, ℝ × Model k) (𝓡∂ (k + 1))
        (fun p : ℝ × Model k => C (p.1, e.symm p.2)) (Ico 0 δ ×ˢ e.target) (t, e y)
        (r, mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) e y v)) =
    Real.exp (-t) * α (C (0, e.symm (e y))) (fun _ =>
      mfderivWithin 𝓘(ℝ, ℝ × Model k) (𝓡∂ (k + 1))
        (fun p : ℝ × Model k => C (p.1, e.symm p.2)) (Ico 0 δ ×ˢ e.target) (0, e y)
        (0, mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) e y v)) at h
  rw [mfderivWithin_collar_boundary_chart C hC y ht r v,
    mfderivWithin_collar_boundary_chart C hC y (show 0 ∈ Ico 0 δ from ⟨le_rfl, hδ⟩) 0 v,
    e.left_inv hy, mfderivWithin_collar_seam C hδ hC hzero y v, hzero y] at h
  exact h

variable [T2Space M] [CompactSpace (IntrinsicBoundary.Point k M)]

/-- Source defining-function outwardness constructs one uniform collar
carrying all the original geometric properties and the full primitive law.
The law concerns precisely that collar and its original positive width. -/
theorem exists_uniform_collar_with_primitive_of_localDefiningFunction_outward
    (α : Form k M 1) (hα : IsLocallyExtendibleForm α)
    (hnd : ∀ x, Nondegenerate (exteriorDerivative α) x)
    (hout : ∀ x : IntrinsicBoundary.Point k M,
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧
        (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector α (exteriorDerivative α) x.val))) :
    ∃ (C : ℝ × IntrinsicBoundary.Point k M → M) (δ : ℝ), 0 < δ ∧
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ C
        (Ico 0 δ ×ˢ univ) ∧
      Topology.IsOpenEmbedding (fun p : Ico 0 δ ×ˢ univ => C p.val) ∧
      (∀ y, C (0, y) = y.val) ∧
      (∀ y, IsMIntegralCurveOn (fun t => C (t, y))
        (fun x => -liouvilleVector α (exteriorDerivative α) x) (Ico 0 δ)) ∧
      (∀ y, ∀ t ∈ Ico 0 δ,
        ((𝓡∂ (k + 1)).IsBoundaryPoint (C (t, y)) ↔ t = 0)) ∧
      (∀ p ∈ Ico 0 δ ×ˢ univ, ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
        ContMDiffAt (𝓡∂ (k + 1)) ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)) ∞ g (C p) ∧
        ∀ᶠ q in 𝓝[Ico 0 δ ×ˢ univ] p, g (C q) = q) ∧
      ∀ t ∈ Ico 0 δ, ∀ y : IntrinsicBoundary.Point k M, ∀ r : ℝ,
        ∀ v : TangentSpace 𝓘(ℝ, Model k) y,
          α (C (t, y)) (fun _ =>
            mfderivWithin (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) C
              (Ico 0 δ ×ˢ univ) (t, y) (r, v)) =
            Real.exp (-t) * α y.val (fun _ =>
              mfderiv 𝓘(ℝ, Model k) (𝓡∂ (k + 1))
                (Subtype.val : IntrinsicBoundary.Point k M → M) y v) := by
  obtain ⟨C, δ, hδ, hC, hemb, hzero, hode, hboundary, hinv⟩ :=
    exists_uniform_collar_of_localDefiningFunction_outward α hα hnd hout
  refine ⟨C, δ, hδ, hC, hemb, hzero, hode, hboundary, hinv, ?_⟩
  intro t ht y r v
  exact inward_boundary_pullbackWithin_eq_exp_mul_of_liouville α hα
    (liouvilleVector α (exteriorDerivative α))
    (contraction_liouvilleVector α (exteriorDerivative α) hnd)
    C hδ hC hode hzero ht y r v

end FsFltz.Geometry.IntrinsicLiouville
