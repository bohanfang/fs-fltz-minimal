import FsFltz.Geometry.IntrinsicCollarPrimitive
import FsFltz.Geometry.IntrinsicLiouvilleCoordinates
import FsFltz.Geometry.IntrinsicExteriorDerivative

/-!
# Native primitive pullback on a one-sided inward collar

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and
`sec:lean`, lines 805–814. Native forms use local smooth extensions of
their coefficients; the collar requires only native one-sided smoothness.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- The actual native pullback is locally the pullback of a smooth chart
extension. The source set may have a boundary; all derivatives are within
that very set. No extension of the map is supplied. -/
theorem pullbackWithin_from_normedSpace_eventually_eq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {r : ℕ}
    (α : Form k M r) (f : E → M) {S : Set E} (hS : UniqueDiffOn ℝ S)
    (hf : ContMDiffOn 𝓘(ℝ, E) (𝓡∂ (k + 1)) ∞ f S)
    {x : E} (hx : x ∈ S)
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M) (hfx : f x ∈ e.source)
    (β : Model (k + 1) → Model (k + 1) [⋀^Fin r]→L[ℝ] ℝ)
    (hag : β =ᶠ[𝓝[(e.extend (𝓡∂ (k + 1))).target]
      (e.extend (𝓡∂ (k + 1)) (f x))] formInChart e α) :
    (fun z => (α (f z)).compContinuousLinearMap
      (mfderivWithin 𝓘(ℝ, E) (𝓡∂ (k + 1)) f S z)) =ᶠ[𝓝[S] x]
    (fun z => (β ((e.extend (𝓡∂ (k + 1))) (f z))).compContinuousLinearMap
      (fderivWithin ℝ (e.extend (𝓡∂ (k + 1)) ∘ f) S z)) := by
  let G := e.extend (𝓡∂ (k + 1)) ∘ f
  have hg : ContMDiffAt (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞
      (e.extend (𝓡∂ (k + 1))) (f x) :=
    e.contMDiffAt_extend (IsManifold.subset_maximalAtlas he) hfx
  have hG : ContDiffWithinAt ℝ ∞ G S x := (hg.comp_contMDiffWithinAt x (hf x hx)).contDiffWithinAt
  have hsource : ∀ᶠ z in 𝓝[S] x, f z ∈ e.source :=
    (hf x hx).continuousWithinAt.preimage_mem_nhdsWithin (e.open_source.mem_nhds hfx)
  have htarg : ∀ᶠ z in 𝓝[S] x, G z ∈ (e.extend (𝓡∂ (k + 1))).target := by
    filter_upwards [hsource] with z hz
    exact (e.extend (𝓡∂ (k + 1))).map_source (by simpa only [e.extend_source] using hz)
  have hGt : Tendsto G (𝓝[S] x) (𝓝[(e.extend (𝓡∂ (k + 1))).target] (G x)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hG.continuousWithinAt, htarg⟩
  have hag' := hGt.eventually hag
  filter_upwards [self_mem_nhdsWithin, hsource, hag'] with z hz hzs hβz
  dsimp only [G, Function.comp_apply] at hβz
  erw [hβz, ← mfderivWithin_eq_fderivWithin]
  have hgz : ContMDiffAt (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞
      (e.extend (𝓡∂ (k + 1))) (f z) :=
    e.contMDiffAt_extend (IsManifold.subset_maximalAtlas he) hzs
  erw [mfderiv_comp_mfderivWithin z (hgz.mdifferentiableAt (by simp))
    ((hf z hz).mdifferentiableWithinAt (by simp)) ((hS z hz).uniqueMDiffWithinAt)]
  erw [← formInChart_comp_chartTangentMap he α hzs]
  ext vs
  rfl

private theorem contDiffWithinAt_one_pullback {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (β : F → F [⋀^Fin 1]→L[ℝ] ℝ) (G : E → F) {S : Set E} (p : E)
    (hS : UniqueDiffOn ℝ S) (hp : p ∈ S)
    (hβ : ContDiffAt ℝ ∞ β (G p)) (hG : ContDiffWithinAt ℝ ∞ G S p) :
    ContDiffWithinAt ℝ ∞
      (fun q => (β (G q)).compContinuousLinearMap (fderivWithin ℝ G S q)) S p := by
  let eF := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := F) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  let eE := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  have h := (eF.symm.contDiff.contDiffAt.comp_contDiffWithinAt p
    (hβ.comp_contDiffWithinAt p hG)).clm_comp (hG.fderivWithin_right hS (by simp) hp)
  have hs := eE.contDiff.contDiffAt.comp_contDiffWithinAt p h
  convert hs using 1
  ext q vs
  change β (G q) (fun i => fderivWithin ℝ G S q (vs i)) =
    β (G q) (fun _ => fderivWithin ℝ G S q (vs 0))
  congr 1
  funext i
  rw [Fin.eq_zero i]

/-- A locally extendible native one-form has smooth actual pullback
coefficients on every unique-differentiation source set, including the
one-sided time strip. -/
theorem contDiffWithinAt_pullback_one_from_normedSpace {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : Form k M 1) (hα : IsLocallyExtendibleForm α)
    (f : E → M) {S : Set E} (hS : UniqueDiffOn ℝ S)
    (hf : ContMDiffOn 𝓘(ℝ, E) (𝓡∂ (k + 1)) ∞ f S) {x : E} (hx : x ∈ S) :
    ContDiffWithinAt ℝ ∞ (F := E [⋀^Fin 1]→L[ℝ] ℝ)
      (fun z => (α (f z)).compContinuousLinearMap
        (mfderivWithin 𝓘(ℝ, E) (𝓡∂ (k + 1)) f S z)) S x := by
  let e := chartAt (EuclideanHalfSpace (k + 1)) (f x)
  have he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M := chart_mem_atlas _ _
  have hfx : f x ∈ e.source := mem_chart_source _ _
  obtain ⟨β, U, hU, hmem, hβ, hag⟩ := hα e he (f x) hfx
  have hg : ContMDiffAt (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞
      (e.extend (𝓡∂ (k + 1))) (f x) :=
    e.contMDiffAt_extend (IsManifold.subset_maximalAtlas he) hfx
  have hG : ContDiffWithinAt ℝ ∞ (e.extend (𝓡∂ (k + 1)) ∘ f) S x :=
    (hg.comp_contMDiffWithinAt x (hf x hx)).contDiffWithinAt
  have hβx := (hβ _ hmem).contDiffAt (hU.mem_nhds hmem)
  exact (contDiffWithinAt_one_pullback β (e.extend (𝓡∂ (k + 1)) ∘ f) x hS hx hβx hG).congr_of_eventuallyEq_of_mem
      (pullbackWithin_from_normedSpace_eventually_eq α f hS hf hx he hfx β hag) hx

/-- Exterior differentiation of the actual native pullback on a source
with boundary. This is proved from local coefficient extensions, the
native derivative's defining chart equation, and within-derivative
naturality; it is not a pullback identity supplied as geometric data. -/
theorem exteriorDerivative_pullbackWithin_from_normedSpace {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {r : ℕ}
    (α : Form k M r) (hα : IsLocallyExtendibleForm α)
    (omega : Form k M (r + 1)) (hd : HasExteriorDerivative α omega)
    (f : E → M) {S : Set E} (hS : UniqueDiffOn ℝ S)
    (hf : ContMDiffOn 𝓘(ℝ, E) (𝓡∂ (k + 1)) ∞ f S)
    {x : E} (hx : x ∈ S) (hxc : x ∈ closure (interior S)) :
    extDerivWithin (fun z => (α (f z)).compContinuousLinearMap
      (mfderivWithin 𝓘(ℝ, E) (𝓡∂ (k + 1)) f S z)) S x =
      (omega (f x)).compContinuousLinearMap
        (mfderivWithin 𝓘(ℝ, E) (𝓡∂ (k + 1)) f S x) := by
  let e := chartAt (EuclideanHalfSpace (k + 1)) (f x)
  have he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M := chart_mem_atlas _ _
  have hfx : f x ∈ e.source := mem_chart_source _ _
  have htarget : e.extend (𝓡∂ (k + 1)) (f x) ∈ (e.extend (𝓡∂ (k + 1))).target :=
    (e.extend (𝓡∂ (k + 1))).map_source (by simpa only [e.extend_source] using hfx)
  obtain ⟨β, U, hU, hmem, hβ, hag⟩ := hα e he (f x) hfx
  have hg : ContMDiffAt (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞
      (e.extend (𝓡∂ (k + 1))) (f x) :=
    e.contMDiffAt_extend (IsManifold.subset_maximalAtlas he) hfx
  have hG : ContDiffWithinAt ℝ ∞ (e.extend (𝓡∂ (k + 1)) ∘ f) S x :=
    (hg.comp_contMDiffWithinAt x (hf x hx)).contDiffWithinAt
  have hβx := (hβ _ hmem).contDiffAt (hU.mem_nhds hmem)
  have heq := pullbackWithin_from_normedSpace_eventually_eq α f hS hf hx he hfx β hag
  erw [heq.extDerivWithin_eq_of_mem hx,
    extDerivWithin_pullback («ω» := β) (f := e.extend (𝓡∂ (k + 1)) ∘ f) (t := univ)
      (hβx.differentiableAt (by simp)).differentiableWithinAt hG
      (by simp) hS hxc hx (mapsTo_univ _ _), extDerivWithin_univ,
    extDeriv_extension_eq he hd htarget (hβx.differentiableAt (by simp)) hag,
    ← mfderivWithin_eq_fderivWithin,
    mfderiv_comp_mfderivWithin x (hg.mdifferentiableAt (by simp))
      ((hf x hx).mdifferentiableWithinAt (by simp)) ((hS x hx).uniqueMDiffWithinAt),
    ← formInChart_comp_chartTangentMap he omega hfx]
  ext vs
  rfl

private theorem extDerivWithin_one_apply {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (eta : E → E [⋀^Fin 1]→L[ℝ] ℝ) (S : Set E) (p u v : E) :
    extDerivWithin eta S p ![u, v] =
      (fderivWithin ℝ eta S p u) (fun _ => v) -
        (fderivWithin ℝ eta S p v) (fun _ => u) := by
  have h0 : (0 : Fin 2).removeNth ![u, v] = fun _ => v := by
    funext i
    fin_cases i
    rfl
  have h1 : (1 : Fin 2).removeNth ![u, v] = fun _ => u := by
    funext i
    fin_cases i
    rfl
  rw [extDerivWithin, ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_two]
  simp only [h0, h1, Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
    Matrix.cons_val_zero, Matrix.cons_val_one, sub_eq_add_neg]

private theorem strip_mem_closure_interior {E : Type*}
    [NormedAddCommGroup E] {V : Set E} {δ : ℝ} (hV : IsOpen V) (hδ : 0 < δ)
    {p : ℝ × E} (hp : p ∈ Ico 0 δ ×ˢ V) : p ∈ closure (interior (Ico 0 δ ×ˢ V)) := by
  rw [interior_prod_eq, interior_Ico, hV.interior_eq, closure_prod_eq,
    closure_Ioo (ne_of_lt hδ)]
  exact ⟨⟨hp.1.1, hp.1.2.le⟩, subset_closure hp.2⟩

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- The native trajectory equation gives the time direction of the
actual within differential of the jointly smooth collar. -/
theorem time_mfderivWithin_of_integralCurveOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x) (C : ℝ × E → M)
    {V : Set E} {δ : ℝ}
    (hC : ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓡∂ (k + 1)) ∞ C (Ico 0 δ ×ˢ V))
    (hode : ∀ y ∈ V, IsMIntegralCurveOn (fun t => C (t, y)) Z (Ico 0 δ))
    {p : ℝ × E} (hp : p ∈ Ico 0 δ ×ˢ V) :
    mfderivWithin 𝓘(ℝ, ℝ × E) (𝓡∂ (k + 1)) C (Ico 0 δ ×ˢ V) p (1, 0) = Z (C p) := by
  have hi : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × E)
      (fun t => (t, p.2)) (Ico 0 δ) p.1 (ContinuousLinearMap.inl ℝ ℝ E) :=
    hasMFDerivWithinAt_iff_hasFDerivWithinAt.mpr
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) p.1 p.2).hasFDerivWithinAt
  have hmaps : MapsTo (fun t : ℝ => (t, p.2)) (Ico 0 δ) (Ico 0 δ ×ˢ V) :=
    fun t ht => ⟨ht, hp.2⟩
  have hc := ((hC p hp).mdifferentiableWithinAt (by simp)).hasMFDerivWithinAt.comp p.1 hi
    hmaps
  have he := congrArg (fun L : ℝ →L[ℝ] TangentSpace (𝓡∂ (k + 1)) (C p) => L (1 : ℝ))
    ((hc.mfderivWithin ((uniqueDiffOn_Ico 0 δ p.1 hp.1).uniqueMDiffWithinAt)).symm.trans
      ((hode p.2 hp.2 p.1 hp.1).mfderivWithin
        ((uniqueDiffOn_Ico 0 δ p.1 hp.1).uniqueMDiffWithinAt)))
  simp only [ContinuousLinearMap.comp_apply] at he
  erw [ContinuousLinearMap.inl_apply, ContinuousLinearMap.smulRight_apply, one_apply_eq_self,
    one_smul] at he
  exact he

/-- The genuine native inward ODE and native exterior derivative derive
the spatial primitive ODE even at the boundary time. Both the primitive
and collar remain intrinsic; no two-sided map extension is used. -/
theorem hasDerivWithinAt_inward_spatial_pullback {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : Form k M 1) (hα : IsLocallyExtendibleForm α)
    (omega : Form k M 2) (hd : HasExteriorDerivative α omega)
    (Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x)
    (hcontr : ∀ x v, omega x ![Z x, v] = -α x (fun _ => v))
    (C : ℝ × E → M) {V : Set E} {δ : ℝ} (hV : IsOpen V) (hδ : 0 < δ)
    (hC : ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓡∂ (k + 1)) ∞ C (Ico 0 δ ×ˢ V))
    (hode : ∀ y ∈ V, IsMIntegralCurveOn (fun t => C (t, y)) Z (Ico 0 δ))
    {t : ℝ} {y : E} (ht : t ∈ Ico 0 δ) (hy : y ∈ V) (v : E) :
    HasDerivWithinAt (fun s => α (C (s, y)) (fun _ =>
      mfderivWithin 𝓘(ℝ, ℝ × E) (𝓡∂ (k + 1)) C (Ico 0 δ ×ˢ V) (s, y) (0, v)))
      (-α (C (t, y)) (fun _ =>
        mfderivWithin 𝓘(ℝ, ℝ × E) (𝓡∂ (k + 1)) C (Ico 0 δ ×ˢ V) (t, y) (0, v)))
      (Ico 0 δ) t := by
  let S := Ico 0 δ ×ˢ V
  let beta : ℝ × E → (ℝ × E) [⋀^Fin 1]→L[ℝ] ℝ := fun p =>
    (α (C p)).compContinuousLinearMap (mfderivWithin 𝓘(ℝ, ℝ × E) (𝓡∂ (k + 1)) C S p)
  have hS : UniqueDiffOn ℝ S := (uniqueDiffOn_Ico 0 δ).prod hV.uniqueDiffOn
  have hp : (t, y) ∈ S := ⟨ht, hy⟩
  have hbeta : DifferentiableWithinAt ℝ beta S (t, y) :=
    (contDiffWithinAt_pullback_one_from_normedSpace α hα C hS hC hp).differentiableWithinAt (by simp)
  have htime (p) (hp : p ∈ S) := time_mfderivWithin_of_integralCurveOn Z C hC hode hp
  have hzero : (fun p => beta p (fun _ => (1, 0))) =ᶠ[𝓝[S] (t, y)] (fun _ => (0 : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with p hpp
    change α (C p) (fun _ => mfderivWithin 𝓘(ℝ, ℝ × E) (𝓡∂ (k + 1)) C S p (1, 0)) = 0
    rw [htime p hpp]
    have hz := (omega (C p)).map_eq_zero_of_eq ![Z (C p), Z (C p)]
      (i := 0) (j := 1) rfl (by decide)
    rw [hcontr] at hz
    exact neg_eq_zero.mp hz
  have hzeroDeriv : (fderivWithin ℝ beta S (t, y) (0, v)) (fun _ => (1, 0)) = 0 := by
    change (fderivWithin ℝ beta S (t, y)).flipAlternating (fun _ => (1, 0)) (0, v) = 0
    rw [← fderivWithin_continuousAlternatingMap_apply_const (hS _ hp) hbeta (fun _ => (1, 0)),
      hzero.fderivWithin_eq_of_mem hp]
    simp
  have hnat := congrArg (fun eta => eta ![(1, 0), (0, v)])
    (exteriorDerivative_pullbackWithin_from_normedSpace α hα omega hd C hS hC hp
      (strip_mem_closure_interior hV hδ hp))
  change extDerivWithin beta S (t, y) ![(1, 0), (0, v)] = omega (C (t, y))
    ((mfderivWithin 𝓘(ℝ, ℝ × E) (𝓡∂ (k + 1)) C S (t, y)) ∘ ![(1, 0), (0, v)]) at hnat
  have hpair : (mfderivWithin 𝓘(ℝ, ℝ × E) (𝓡∂ (k + 1)) C S (t, y)) ∘ ![(1, 0), (0, v)] =
      ![mfderivWithin 𝓘(ℝ, ℝ × E) (𝓡∂ (k + 1)) C S (t, y) (1, 0),
        mfderivWithin 𝓘(ℝ, ℝ × E) (𝓡∂ (k + 1)) C S (t, y) (0, v)] := by
    funext i
    fin_cases i <;> rfl
  rw [hpair, htime _ hp, hcontr, extDerivWithin_one_apply, hzeroDeriv, sub_zero] at hnat
  have hin : HasDerivWithinAt (fun s : ℝ => (s, y)) (1, 0) (Ico 0 δ) t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t y)).hasDerivWithinAt
  have hmaps : MapsTo (fun s : ℝ => (s, y)) (Ico 0 δ) S := fun s hs => ⟨hs, hy⟩
  have hder := (hbeta.hasFDerivWithinAt.continuousAlternatingMap_apply_const
    (fun _ => (0, v))).comp_hasDerivWithinAt t hin hmaps
  exact hder.congr_deriv hnat

/-- Integration of the derived native ODE gives the primitive scaling
on the entire one-sided strip. Its initial time uses the actual within
differential, whose uniqueness was proved for this source set. -/
theorem inward_spatial_pullbackWithin_eq_exp_mul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : Form k M 1) (hα : IsLocallyExtendibleForm α)
    (omega : Form k M 2) (hd : HasExteriorDerivative α omega)
    (Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x)
    (hcontr : ∀ x v, omega x ![Z x, v] = -α x (fun _ => v))
    (C : ℝ × E → M) {V : Set E} {δ : ℝ} (hV : IsOpen V) (hδ : 0 < δ)
    (hC : ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓡∂ (k + 1)) ∞ C (Ico 0 δ ×ˢ V))
    (hode : ∀ y ∈ V, IsMIntegralCurveOn (fun t => C (t, y)) Z (Ico 0 δ))
    {t : ℝ} {y : E} (ht : t ∈ Ico 0 δ) (hy : y ∈ V) (v : E) :
    α (C (t, y)) (fun _ =>
      mfderivWithin 𝓘(ℝ, ℝ × E) (𝓡∂ (k + 1)) C (Ico 0 δ ×ˢ V) (t, y) (0, v)) =
    Real.exp (-t) * α (C (0, y)) (fun _ =>
      mfderivWithin 𝓘(ℝ, ℝ × E) (𝓡∂ (k + 1)) C (Ico 0 δ ×ˢ V) (0, y) (0, v)) := by
  let q : ℝ → ℝ := fun s => α (C (s, y)) (fun _ =>
    mfderivWithin 𝓘(ℝ, ℝ × E) (𝓡∂ (k + 1)) C (Ico 0 δ ×ˢ V) (s, y) (0, v))
  have hq : ∀ s ∈ Ico 0 δ, HasDerivWithinAt q (-q s) (Ico 0 δ) s := fun s hs =>
    hasDerivWithinAt_inward_spatial_pullback α hα omega hd Z hcontr C hV hδ hC hode hs hy v
  have hw : ∀ s ∈ Ico 0 δ, HasDerivWithinAt (fun r => Real.exp r * q r) 0 (Ico 0 δ) s := by
    intro s hs
    exact ((Real.hasDerivAt_exp s).hasDerivWithinAt.mul (hq s hs)).congr_deriv (by ring)
  have hwfd : ∀ s ∈ Ico 0 δ,
      fderivWithin ℝ (fun r => Real.exp r * q r) (Ico 0 δ) s = 0 := by
    intro s hs
    have he := (hw s hs).hasFDerivWithinAt.fderivWithin (uniqueDiffOn_Ico 0 δ s hs)
    simpa using he
  have hcst := (convex_Ico 0 δ).is_const_of_fderivWithin_eq_zero
    (fun s hs => (hw s hs).differentiableWithinAt) hwfd ht (show 0 ∈ Ico 0 δ from ⟨le_rfl, hδ⟩)
  have he := congrArg (fun r => Real.exp (-t) * r) hcst
  simp only [Real.exp_zero, one_mul, ← mul_assoc, ← Real.exp_add,
    neg_add_cancel, Real.exp_zero, one_mul] at he
  exact he

/-- Complete native primitive pullback on a one-sided collar, for every
time and every product tangent including its time component. All terms
use the actual `mfderivWithin` of this same collar map. -/
theorem inward_pullbackWithin_eq_exp_mul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : Form k M 1) (hα : IsLocallyExtendibleForm α)
    (omega : Form k M 2) (hd : HasExteriorDerivative α omega)
    (Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x)
    (hcontr : ∀ x v, omega x ![Z x, v] = -α x (fun _ => v))
    (C : ℝ × E → M) {V : Set E} {δ : ℝ} (hV : IsOpen V) (hδ : 0 < δ)
    (hC : ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓡∂ (k + 1)) ∞ C (Ico 0 δ ×ˢ V))
    (hode : ∀ y ∈ V, IsMIntegralCurveOn (fun t => C (t, y)) Z (Ico 0 δ))
    {t : ℝ} {y : E} (ht : t ∈ Ico 0 δ) (hy : y ∈ V) (r : ℝ) (v : E) :
    α (C (t, y)) (fun _ =>
      mfderivWithin 𝓘(ℝ, ℝ × E) (𝓡∂ (k + 1)) C (Ico 0 δ ×ˢ V) (t, y) (r, v)) =
    Real.exp (-t) * α (C (0, y)) (fun _ =>
      mfderivWithin 𝓘(ℝ, ℝ × E) (𝓡∂ (k + 1)) C (Ico 0 δ ×ˢ V) (0, y) (0, v)) := by
  have htime := time_mfderivWithin_of_integralCurveOn Z C hC hode (show (t, y) ∈ Ico 0 δ ×ˢ V from ⟨ht, hy⟩)
  have hsp := inward_spatial_pullbackWithin_eq_exp_mul α hα omega hd Z hcontr C hV hδ hC hode ht hy v
  have hdecomp : (r, v) = r • (1, (0 : E)) + (0, v) := by simp
  rw [hdecomp, map_add, map_smul, htime]
  have heval : α (C (t, y)) (fun _ => r • Z (C (t, y)) +
      mfderivWithin 𝓘(ℝ, ℝ × E) (𝓡∂ (k + 1)) C (Ico 0 δ ×ˢ V) (t, y) (0, v)) =
      r * α (C (t, y)) (fun _ => Z (C (t, y))) +
        α (C (t, y)) (fun _ =>
          mfderivWithin 𝓘(ℝ, ℝ × E) (𝓡∂ (k + 1)) C (Ico 0 δ ×ˢ V) (t, y) (0, v)) := by
    change ((ContinuousAlternatingMap.ofSubsingleton
      ℝ (TangentSpace (𝓡∂ (k + 1)) (C (t, y))) ℝ (0 : Fin 1)).symm
        (α (C (t, y)))) (r • Z (C (t, y)) +
          mfderivWithin 𝓘(ℝ, ℝ × E) (𝓡∂ (k + 1)) C (Ico 0 δ ×ˢ V) (t, y) (0, v)) = _
    simp only [map_add, map_smul, smul_eq_mul]
    rfl
  have hz : α (C (t, y)) (fun _ => Z (C (t, y))) = 0 := by
    have he := (omega (C (t, y))).map_eq_zero_of_eq ![Z (C (t, y)), Z (C (t, y))]
      (i := 0) (j := 1) rfl (by decide)
    rw [hcontr] at he
    exact neg_eq_zero.mp he
  rw [heval, hz, mul_zero, zero_add]
  exact hsp

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Negating the genuine Liouville field produces the inward contraction
equation, with the sign forced by linearity of the actual two-form. -/
theorem inward_contraction_of_liouville (α : Form k M 1) (omega : Form k M 2)
    (Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x) (hZ : Contraction α omega Z) :
    ∀ x v, omega x ![-Z x, v] = -α x (fun _ => v) := by
  intro x v
  have hn := (omega x).map_update_neg ![Z x, v] (0 : Fin 2) (Z x)
  have hneg : Function.update ![Z x, v] (0 : Fin 2) (-Z x) = ![-Z x, v] := by
    funext i
    fin_cases i <;> simp
  have hpos : Function.update ![Z x, v] (0 : Fin 2) (Z x) = ![Z x, v] := by
    funext i
    fin_cases i <;> simp
  erw [hneg, hpos] at hn
  change omega x ![-Z x, v] = -omega x ![Z x, v] at hn
  rw [hZ] at hn
  convert hn using 1
  apply congrArg Neg.neg
  apply congrArg (α x)
  funext i
  fin_cases i
  rfl

/-- The native primitive law with the canonical, constructed exterior
derivative. Only the local source form extension and actual Liouville
equation are input; the derivative covariance and primitive transport
law are proved producers. -/
theorem inward_pullbackWithin_eq_exp_mul_of_liouville {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : Form k M 1) (hα : IsLocallyExtendibleForm α)
    (Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x)
    (hZ : Contraction α (exteriorDerivative α) Z)
    (C : ℝ × E → M) {V : Set E} {δ : ℝ} (hV : IsOpen V) (hδ : 0 < δ)
    (hC : ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓡∂ (k + 1)) ∞ C (Ico 0 δ ×ˢ V))
    (hode : ∀ y ∈ V, IsMIntegralCurveOn (fun t => C (t, y)) (fun x => -Z x) (Ico 0 δ))
    {t : ℝ} {y : E} (ht : t ∈ Ico 0 δ) (hy : y ∈ V) (r : ℝ) (v : E) :
    α (C (t, y)) (fun _ =>
      mfderivWithin 𝓘(ℝ, ℝ × E) (𝓡∂ (k + 1)) C (Ico 0 δ ×ˢ V) (t, y) (r, v)) =
    Real.exp (-t) * α (C (0, y)) (fun _ =>
      mfderivWithin 𝓘(ℝ, ℝ × E) (𝓡∂ (k + 1)) C (Ico 0 δ ×ˢ V) (0, y) (0, v)) :=
  inward_pullbackWithin_eq_exp_mul α hα (exteriorDerivative α)
    (hasExteriorDerivative_exteriorDerivative α hα) (fun x => -Z x)
    (inward_contraction_of_liouville α (exteriorDerivative α) Z hZ)
    C hV hδ hC hode ht hy r v

end FsFltz.Geometry.IntrinsicLiouville
