import FsFltz.Geometry.IntrinsicBundleTransition
import FsFltz.Geometry.IntrinsicPrimitiveFamilyExtension

/-!
# Joint native one-form transport under bundle changes of coordinates

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–169, and
`sec:lean`, lines 788–814. Actual native pullback uses the full manifold
differential, including at the spatial boundary. Joint open germs are
constructed from the given map and coefficient germs.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- The existing joint coefficient germ condition restricted to actual
parameters in `S`. The extension is defined on a full ambient open set. -/
def HasSmoothFormFamilyOn {r : ℕ} (S : Set Parameter)
    (α : Parameter → Form k M r) : Prop :=
  ∀ e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1)),
    e ∈ atlas (EuclideanHalfSpace (k + 1)) M → ∀ t ∈ S, ∀ x ∈ e.source,
      ∃ (U : Set (ℝ × Model (k + 1)))
        (β : ℝ × Model (k + 1) → Model (k + 1) [⋀^Fin r]→L[ℝ] ℝ),
        IsOpen U ∧ (t.val, e.extend (𝓡∂ (k + 1)) x) ∈ U ∧
        ContDiffOn ℝ ∞ β U ∧
        ∀ s ∈ S, ∀ y ∈ (e.extend (𝓡∂ (k + 1))).target,
          (s.val, y) ∈ U → β (s.val, y) = formInChart e (α s) y

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
theorem IsLocallyExtendibleFormFamily.hasSmoothFormFamilyOn {r : ℕ}
    {α : Parameter → Form k M r} (h : IsLocallyExtendibleFormFamily α)
    (S : Set Parameter) : HasSmoothFormFamilyOn S α := by
  intro e he t _ x hx
  obtain ⟨U, β, hU, hp, hβ, heq⟩ := h e he t x hx
  exact ⟨U, β, hU, hp, hβ, fun s _ y hy hsy => heq s y hy hsy⟩

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
theorem hasSmoothFormFamilyOn_univ_iff {r : ℕ} {α : Parameter → Form k M r} :
    HasSmoothFormFamilyOn univ α ↔ IsLocallyExtendibleFormFamily α := by
  constructor
  · intro h e he t x hx
    obtain ⟨U, β, hU, hp, hβ, heq⟩ := h e he t (mem_univ t) x hx
    exact ⟨U, β, hU, hp, hβ, fun s => heq s (mem_univ s)⟩
  · exact fun h => h.hasSmoothFormFamilyOn univ

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
theorem HasSmoothFormFamilyOn.mono {r : ℕ} {S T : Set Parameter}
    {α : Parameter → Form k M r} (h : HasSmoothFormFamilyOn S α) (hTS : T ⊆ S) :
    HasSmoothFormFamilyOn T α := by
  intro e he t ht x hx
  obtain ⟨U, β, hU, hp, hβ, heq⟩ := h e he t (hTS ht) x hx
  exact ⟨U, β, hU, hp, hβ, fun s hs y hy hsy => heq s (hTS hs) y hy hsy⟩

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
theorem HasSmoothFormFamilyOn.congr {r : ℕ} {S : Set Parameter}
    {α δ : Parameter → Form k M r} (h : HasSmoothFormFamilyOn S α)
    (he : ∀ t ∈ S, α t = δ t) : HasSmoothFormFamilyOn S δ := by
  intro e he' t ht x hx
  obtain ⟨U, β, hU, hp, hβ, heq⟩ := h e he' t ht x hx
  exact ⟨U, β, hU, hp, hβ, fun s hs y hy hsy => by
    rw [← he s hs]
    exact heq s hs y hy hsy⟩

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Locality refers to the actual interval base; extensions still live
in full open real parameter and spatial neighborhoods. -/
theorem HasSmoothFormFamilyOn.of_locally {r : ℕ} {S : Set Parameter}
    {α : Parameter → Form k M r}
    (h : ∀ t ∈ S, ∃ T : Set Parameter, IsOpen T ∧ t ∈ T ∧
      HasSmoothFormFamilyOn (S ∩ T) α) : HasSmoothFormFamilyOn S α := by
  intro e he t ht x hx
  obtain ⟨T, hT, htT, hlocal⟩ := h t ht
  obtain ⟨O, hO, hOT⟩ := isOpen_induced_iff.mp hT
  have htO : t.val ∈ O := by change t ∈ Subtype.val ⁻¹' O; rwa [hOT]
  obtain ⟨U, β, hU, hp, hβ, heq⟩ := hlocal e he t ⟨ht, htT⟩ x hx
  refine ⟨U ∩ Prod.fst ⁻¹' O, β, hU.inter (hO.preimage continuous_fst),
    ⟨hp, htO⟩, hβ.mono inter_subset_left, ?_⟩
  intro s hs y hy hsy
  have hsT : s ∈ T := by rw [← hOT]; exact hsy.2
  exact heq s ⟨hs, hsT⟩ y hy hsy.1

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Smooth reparametrization pulls back the given coefficient germs. -/
theorem HasSmoothFormFamilyOn.reparam {r : ℕ} {S : Set Parameter}
    {α : Parameter → Form k M r} (h : HasSmoothFormFamilyOn S α)
    (σ : ℝ → Parameter) (hσ : ContDiff ℝ ∞ (fun s => (σ s).val))
    (hmem : ∀ s, σ s ∈ S) :
    HasSmoothFormFamilyOn univ (fun t => α (σ t.val)) := by
  intro e he t _ x hx
  obtain ⟨U, β, hU, hp, hβ, heq⟩ := h e he (σ t.val) (hmem t.val) x hx
  let q : ℝ × Model (k + 1) → ℝ × Model (k + 1) := fun z => ((σ z.1).val, z.2)
  have hq : ContDiff ℝ ∞ q := (hσ.comp contDiff_fst).prodMk contDiff_snd
  exact ⟨q ⁻¹' U, β ∘ q, hU.preimage hq.continuous, hp,
    hβ.comp hq.contDiffOn (fun _ hz => hz),
    fun s _ y hy hsy => heq (σ s.val) (hmem s.val) y hy hsy⟩

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
theorem HasSmoothFormFamilyOn.slice {r : ℕ} {S : Set Parameter}
    {α : Parameter → Form k M r} (h : HasSmoothFormFamilyOn S α)
    {t : Parameter} (ht : t ∈ S) : IsLocallyExtendibleForm (α t) := by
  intro e he x hx
  obtain ⟨U, β, hU, hp, hβ, heq⟩ := h e he t ht x hx
  let q : Model (k + 1) → ℝ × Model (k + 1) := fun y => (t.val, y)
  refine ⟨β ∘ q, q ⁻¹' U, hU.preimage (continuous_const.prodMk continuous_id), hp,
    hβ.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hy => hy), ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds
      ((hU.preimage (continuous_const.prodMk continuous_id)).mem_nhds hp)] with y hy hyU
  exact heq t ht y hy hyU

/-- Native pullback on a positive-dimensional manifold with boundary. -/
def nativePullbackForm {r : ℕ} (f : M → M) (α : Form k M r) : Form k M r :=
  fun x => (α (f x)).compContinuousLinearMap (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) f x)

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
@[simp]
theorem nativePullbackForm_id {r : ℕ} (α : Form k M r) :
    nativePullbackForm id α = α := by
  funext x
  unfold nativePullbackForm
  rw [mfderiv_id]
  ext vs
  rfl

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Composition of actual native pullbacks follows the full manifold
differential chain rule; forms require no extra differentiability premise. -/
theorem nativePullbackForm_comp {r : ℕ} {f g : M → M} (α : Form k M r)
    (hf : ContMDiff (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) ∞ f)
    (hg : ContMDiff (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) ∞ g) :
    nativePullbackForm f (nativePullbackForm g α) = nativePullbackForm (g ∘ f) α := by
  funext x
  unfold nativePullbackForm
  rw [mfderiv_comp x (hg.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))]
  ext vs
  rfl

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
private theorem contMDiff_slice_of_joint_germs {S : Set Parameter} (hS : IsOpen S)
    {f : Parameter → M → M}
    (hf : IntrinsicSmoothBundle.HasSmoothFamilyOn (𝓡∂ (k + 1)) S f)
    (hc : ContinuousOn (fun p : Parameter × M => f p.1 p.2) (S ×ˢ univ))
    {t : Parameter} (ht : t ∈ S) : ContMDiff (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) ∞ (f t) := by
  intro x
  let a := chartAt (EuclideanHalfSpace (k + 1)) x
  have hx : x ∈ a.source := mem_chart_source _ _
  obtain ⟨U, β, hU, hp, hβ, heq⟩ := hf a (chart_mem_atlas _ _) t ht x hx
  let q : Model (k + 1) → ℝ × Model (k + 1) := fun z => (t.val, z)
  have hq : ContDiff ℝ ∞ q := contDiff_const.prodMk contDiff_id
  have hβq : ContDiffAt ℝ ∞ (β ∘ q) (a.extend (𝓡∂ (k + 1)) x) :=
    (hβ.contDiffAt (hU.mem_nhds hp)).comp _ hq.contDiffAt
  have hag : β ∘ q =ᶠ[𝓝[(a.extend (𝓡∂ (k + 1))).target]
      (a.extend (𝓡∂ (k + 1)) x)]
      (fun z => extChartAt (𝓡∂ (k + 1)) (f t x)
        (f t ((a.extend (𝓡∂ (k + 1))).symm z))) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds ((hU.preimage hq.continuous).mem_nhds hp)]
      with z hz hzU
    exact heq t ht z hz hzU
  have hxT : a.extend (𝓡∂ (k + 1)) x ∈ (a.extend (𝓡∂ (k + 1))).target :=
    (a.extend (𝓡∂ (k + 1))).map_source (by simpa only [a.extend_source] using hx)
  have hagPoint := hag.eq_of_nhdsWithin hxT
  rw [a.nhdsWithin_extend_target_eq hx] at hag
  apply contMDiffAt_iff.mpr
  refine ⟨?_, hβq.contDiffWithinAt.congr_of_eventuallyEq hag.symm hagPoint.symm⟩
  exact (hc.continuousAt ((hS.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)).comp_of_eq
    (continuous_const.prodMk continuous_id).continuousAt rfl

omit [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] in
private theorem spatial_derivative_extension_eq
    {a b : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    {f : M → M} {U : Set (ℝ × Model (k + 1))} (hU : IsOpen U)
    {β : ℝ × Model (k + 1) → Model (k + 1)} (hβ : ContDiffOn ℝ ∞ β U)
    (s : Parameter) {y : Model (k + 1)}
    (hy : y ∈ (a.extend (𝓡∂ (k + 1))).target) (hp : (s.val, y) ∈ U)
    (heq : ∀ z ∈ (a.extend (𝓡∂ (k + 1))).target, (s.val, z) ∈ U →
      β (s.val, z) = b.extend (𝓡∂ (k + 1)) (f ((a.extend (𝓡∂ (k + 1))).symm z))) :
    (fderiv ℝ β (s.val, y)).comp (ContinuousLinearMap.inr ℝ ℝ (Model (k + 1))) =
      fderivWithin ℝ (b.extend (𝓡∂ (k + 1)) ∘ f ∘
        (a.extend (𝓡∂ (k + 1))).symm) (range (𝓡∂ (k + 1))) y := by
  let q : Model (k + 1) → ℝ × Model (k + 1) := fun z => (s.val, z)
  have hq : HasFDerivAt q (ContinuousLinearMap.inr ℝ ℝ (Model (k + 1))) y := by
    convert (hasFDerivAt_const (s.val) y).prodMk (hasFDerivAt_id y) using 1 <;> rfl
  have hd := ((hβ.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt.comp y hq
  have hag : β ∘ q =ᶠ[𝓝[(a.extend (𝓡∂ (k + 1))).target] y]
      (b.extend (𝓡∂ (k + 1)) ∘ f ∘ (a.extend (𝓡∂ (k + 1))).symm) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds
        ((hU.preimage (continuous_const.prodMk continuous_id)).mem_nhds hp)] with z hz hzU
    exact heq z hz hzU
  have hx : (a.extend (𝓡∂ (k + 1))).symm y ∈ a.source := by
    simpa only [a.extend_source] using (a.extend (𝓡∂ (k + 1))).map_target hy
  have hxy : a.extend (𝓡∂ (k + 1)) ((a.extend (𝓡∂ (k + 1))).symm y) = y :=
    (a.extend (𝓡∂ (k + 1))).right_inv hy
  rw [← hxy, a.nhdsWithin_extend_target_eq hx, hxy] at hag
  have hys := a.extend_target_subset_range (I := 𝓡∂ (k + 1)) hy
  calc
    _ = fderivWithin ℝ (β ∘ q) (range (𝓡∂ (k + 1))) y :=
      (hd.hasFDerivWithinAt.fderivWithin ((𝓡∂ (k + 1)).uniqueDiffOn y hys)).symm
    _ = _ := hag.fderivWithin_eq_of_mem hys

private theorem contDiffOn_oneForm_comp {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {a : G → F [⋀^Fin 1]→L[ℝ] ℝ} {B : G → E →L[ℝ] F} {U : Set G}
    (ha : ContDiffOn ℝ ∞ a U) (hB : ContDiffOn ℝ ∞ B U) :
    ContDiffOn ℝ ∞ (fun y => (a y).compContinuousLinearMap (B y)) U := by
  let eF := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := F) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  let eE := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  have h := (eF.symm.contDiff.contDiffOn.comp ha (fun _ _ => mem_univ _)).clm_comp hB
  have hs := eE.contDiff.contDiffOn.comp h (fun _ _ => mem_univ _)
  convert hs using 1
  ext y vs
  change a y (fun i => B y (vs i)) = a y (fun _ => B y (vs 0))
  congr 1
  funext i
  rw [Fin.eq_zero i]

/-- The full native coordinate chain rule uses differentiation within the
half-space range, even when the source point is on the boundary. -/
theorem formInChart_nativePullbackForm {r : ℕ} {f : M → M} (α : Form k M r)
    {a b : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (ha : a ∈ atlas (EuclideanHalfSpace (k + 1)) M)
    (hb : b ∈ atlas (EuclideanHalfSpace (k + 1)) M)
    {y : Model (k + 1)} (hy : y ∈ (a.extend (𝓡∂ (k + 1))).target)
    (hfx : f ((a.extend (𝓡∂ (k + 1))).symm y) ∈ b.source)
    (hf : MDifferentiableAt (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) f
      ((a.extend (𝓡∂ (k + 1))).symm y)) :
    formInChart a (nativePullbackForm f α) y =
      (formInChart b α (b.extend (𝓡∂ (k + 1))
        (f ((a.extend (𝓡∂ (k + 1))).symm y)))).compContinuousLinearMap
        (fderivWithin ℝ (b.extend (𝓡∂ (k + 1)) ∘ f ∘
          (a.extend (𝓡∂ (k + 1))).symm) (range (𝓡∂ (k + 1))) y) := by
  have hci := mdifferentiableWithinAt_extend_symm
    (IsManifold.subset_maximalAtlas (I := 𝓡∂ (k + 1)) (n := (1 : WithTop ℕ∞)) ha) hy
  have hce := (b.contMDiffAt_extend
    (IsManifold.subset_maximalAtlas (I := 𝓡∂ (k + 1)) (n := ∞) hb) hfx).mdifferentiableAt (by simp)
  have hys : y ∈ range (𝓡∂ (k + 1)) := (a.extend_target_subset_range (I := 𝓡∂ (k + 1))) hy
  have hu : UniqueMDiffWithinAt 𝓘(ℝ, Model (k + 1)) (range (𝓡∂ (k + 1))) y :=
    uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.mpr ((𝓡∂ (k + 1)).uniqueDiffOn y hys)
  rw [← mfderivWithin_eq_fderivWithin,
    mfderiv_comp_mfderivWithin y hce (hf.comp_mdifferentiableWithinAt y hci) hu,
    mfderiv_comp_mfderivWithin y hf hci hu]
  have hrec := formInChart_comp_chartTangentMap hb α hfx
  unfold formInChart nativePullbackForm
  rw [← hrec]
  ext vs
  rfl

/-- Pullback by an actually varying native map preserves joint open
one-form coefficient germs. The extension is built by composing the given
coefficient germ with the map germ and its full spatial derivative. -/
theorem HasSmoothFormFamilyOn.nativePullback {S : Set Parameter}
    {α : Parameter → Form k M 1} (hα : HasSmoothFormFamilyOn S α)
    (hS : IsOpen S) {f : Parameter → M → M}
    (hf : IntrinsicSmoothBundle.HasSmoothFamilyOn (𝓡∂ (k + 1)) S f)
    (hfc : ContinuousOn (fun p : Parameter × M => f p.1 p.2) (S ×ˢ univ)) :
    HasSmoothFormFamilyOn S (fun t => nativePullbackForm (f t) (α t)) := by
  intro a ha t ht x hx
  let b := chartAt (EuclideanHalfSpace (k + 1)) (f t x)
  have hb : b ∈ atlas (EuclideanHalfSpace (k + 1)) M := chart_mem_atlas _ _
  have hfx : f t x ∈ b.source := mem_chart_source _ _
  obtain ⟨U, β, hU, hpU, hβ, heqβ⟩ := hf a ha t ht x hx
  obtain ⟨V, γ, hV, hpV, hγ, heqγ⟩ := hα b hb t ht (f t x) hfx
  let p : ℝ × Model (k + 1) := (t.val, a.extend (𝓡∂ (k + 1)) x)
  let q : ℝ × Model (k + 1) → ℝ × Model (k + 1) := fun z => (z.1, β z)
  have hq : ContDiffOn ℝ ∞ q U := contDiff_fst.contDiffOn.prodMk hβ
  have hxT : a.extend (𝓡∂ (k + 1)) x ∈ (a.extend (𝓡∂ (k + 1))).target :=
    (a.extend (𝓡∂ (k + 1))).map_source (by simpa only [a.extend_source] using hx)
  have hqp : q p = (t.val, b.extend (𝓡∂ (k + 1)) (f t x)) := by
    refine Prod.ext (by rfl) ?_
    change β (t.val, a.extend (𝓡∂ (k + 1)) x) = extChartAt (𝓡∂ (k + 1)) (f t x) (f t x)
    simpa only [(a.extend (𝓡∂ (k + 1))).left_inv
      (by simpa only [a.extend_source] using hx)] using heqβ t ht _ hxT hpU
  let c : ℝ × Model (k + 1) → Parameter × M := fun z =>
    (projIcc 0 1 (by norm_num) z.1, (a.extend (𝓡∂ (k + 1))).symm z.2)
  have hcp : c p = (t, x) := by
    change (projIcc 0 1 (by norm_num) t.val,
      (a.extend (𝓡∂ (k + 1))).symm (a.extend (𝓡∂ (k + 1)) x)) = (t, x)
    rw [projIcc_of_mem (by norm_num) t.property,
      (a.extend (𝓡∂ (k + 1))).left_inv (by simpa only [a.extend_source] using hx)]
  have hcc : ContinuousAt c p :=
    (continuous_projIcc.comp continuous_fst).continuousAt.prodMk
      ((a.continuousAt_extend_symm (I := 𝓡∂ (k + 1)) hx).comp_of_eq
        (continuous_snd.continuousAt (x := p)) rfl)
  have hfcAt : ContinuousAt (fun z : Parameter × M => f z.1 z.2) (t, x) :=
    hfc.continuousAt ((hS.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)
  have hsource : {z | f (c z).1 (c z).2 ∈ b.source} ∈ 𝓝 p :=
    (hfcAt.comp_of_eq hcc hcp).preimage_mem_nhds
      (b.open_source.mem_nhds (by simpa only [Function.comp_apply, hcp] using hfx))
  obtain ⟨N, hNsub, hN, hpN⟩ := mem_nhds_iff.mp hsource
  let W := U ∩ q ⁻¹' V ∩ N
  have hW : IsOpen W :=
    (hq.continuousOn.isOpen_inter_preimage hU hV).inter hN
  let D : ℝ × Model (k + 1) → Model (k + 1) →L[ℝ] Model (k + 1) := fun z =>
    (fderiv ℝ β z).comp (ContinuousLinearMap.inr ℝ ℝ (Model (k + 1)))
  have hD : ContDiffOn ℝ ∞ D U :=
    (hβ.fderiv_of_isOpen hU (by simp)).clm_comp contDiff_const.contDiffOn
  refine ⟨W, (fun z => (γ (q z)).compContinuousLinearMap (D z)), hW,
    ⟨⟨hpU, by change q p ∈ V; rw [hqp]; exact hpV⟩, hpN⟩, ?_, ?_⟩
  · exact contDiffOn_oneForm_comp
      (hγ.comp (hq.mono (inter_subset_left.trans inter_subset_left))
        (fun z hz => hz.1.2))
      (hD.mono (inter_subset_left.trans inter_subset_left))
  · intro s hs y hy hsy
    have hinner : f s ((a.extend (𝓡∂ (k + 1))).symm y) ∈ b.source := by
      have hm := hNsub hsy.2
      change f (projIcc 0 1 (by norm_num) s.val)
        ((a.extend (𝓡∂ (k + 1))).symm y) ∈ b.source at hm
      simpa only [projIcc_of_mem (by norm_num) s.property] using hm
    have hβsy : β (s.val, y) = b.extend (𝓡∂ (k + 1))
        (f s ((a.extend (𝓡∂ (k + 1))).symm y)) := heqβ s hs y hy hsy.1.1
    have hmid : β (s.val, y) ∈ (b.extend (𝓡∂ (k + 1))).target := by
      rw [hβsy]
      exact (b.extend (𝓡∂ (k + 1))).map_source
        (by simpa only [b.extend_source] using hinner)
    change (γ (s.val, β (s.val, y))).compContinuousLinearMap (D (s.val, y)) = _
    rw [heqγ s hs (β (s.val, y)) hmid hsy.1.2, hβsy,
      formInChart_nativePullbackForm (α s) ha hb hy hinner
        ((contMDiff_slice_of_joint_germs hS hf hfc hs).mdifferentiableAt (by simp))]
    congr 1
    exact spatial_derivative_extension_eq hU hβ s hy hsy.1.1
      (fun z hz hsz => heqβ s hs z hz hsz)

end FsFltz.Geometry.IntrinsicLiouville
