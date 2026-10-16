import FsFltz.Geometry.IntrinsicBundleLocalCompletionFamily
import FsFltz.Geometry.IntrinsicNativeCompletionFamilyVertical

/-!
# Vertical primitives on original-chart local completions

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199, and
`sec:lean`, lines 788–814. Smooth local total covectors are assembled on
the actual total atlas. Parameter components are permitted; their full
spatial restrictions retain the native completed primitives.

The total regularity proved here is native `ContMDiff ∞` in the closed
parameter model. Real open coefficient germs for the assembled total
covector, and descent along completed-bundle overlaps, remain separate
foundations. No geometric target theorem is asserted here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter Bundle Topology

namespace FsFltz.Geometry

section NativePartition

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace X]
  {I : ModelWithCorners ℝ E H} [ChartedSpace H X] [IsManifold I ∞ X]

/-- A locally finite weighted sum takes place in the actual native
covector fiber over each point. -/
def partitionNativeCovector {ι : Type*} (ρ : SmoothPartitionOfUnity ι I X univ)
    (g : ι → (x : X) → TangentSpace I x [⋀^Fin 1]→L[ℝ] ℝ) :
    (x : X) → TangentSpace I x [⋀^Fin 1]→L[ℝ] ℝ :=
  fun x => ∑ i ∈ ρ.finsupport x, ρ i x • g i x

/-- Smooth local scalar evaluations give a jointly smooth evaluation of
the global covector on the native tangent bundle. -/
theorem contMDiff_partitionNativeCovector {ι : Type*}
    (ρ : SmoothPartitionOfUnity ι I X univ)
    (g : ι → (x : X) → TangentSpace I x [⋀^Fin 1]→L[ℝ] ℝ)
    (U : ι → Set X) (hρ : ρ.IsSubordinate U) (hU : ∀ i, IsOpen (U i))
    (hg : ∀ i, ContMDiffOn I.tangent 𝓘(ℝ, ℝ) ∞
      (fun v : TangentBundle I X => g i v.proj (fun _ => v.2))
      (Bundle.TotalSpace.proj ⁻¹' U i)) :
    ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞
      (fun v : TangentBundle I X => partitionNativeCovector ρ g v.proj (fun _ => v.2)) := by
  classical
  intro v
  let s := ρ.fintsupport v.proj
  have hp : ContMDiff I.tangent I ∞
      (Bundle.TotalSpace.proj : TangentBundle I X → X) :=
    Bundle.contMDiff_proj (TangentSpace I)
  have hs : ContMDiffAt I.tangent 𝓘(ℝ, ℝ) ∞
      (fun w : TangentBundle I X => ∑ i ∈ s,
        ρ i w.proj * g i w.proj (fun _ => w.2)) v := by
    apply ContMDiffAt.sum
    intro i hi
    have hvi : v.proj ∈ U i := hρ i ((ρ.mem_fintsupport_iff v.proj i).mp hi)
    exact ((ρ i).contMDiff.comp hp).contMDiffAt.mul
      ((hg i).contMDiffAt ((hU i).preimage hp.continuous |>.mem_nhds hvi))
  apply hs.congr_of_eventuallyEq
  filter_upwards [hp.continuous.continuousAt.eventually (ρ.eventually_finsupport_subset v.proj)]
    with w hw
  dsimp only [partitionNativeCovector]
  rw [ContinuousAlternatingMap.sum_apply]
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  exact Finset.sum_subset hw (fun i _ hi => by
    have hz : ρ i w.proj = 0 := by
      simpa only [ρ.mem_finsupport, Function.mem_support, not_not] using hi
    rw [hz, zero_mul])

omit [IsManifold I ∞ X] in
/-- Any linear restriction shared by all active local covectors is
retained by the global sum. In particular this applies to an entire
spatial slice tangent fiber, rather than selected vectors. -/
theorem partitionNativeCovector_comp_eq {ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ρ : SmoothPartitionOfUnity ι I X univ)
    (g : ι → (x : X) → TangentSpace I x [⋀^Fin 1]→L[ℝ] ℝ)
    (U : ι → Set X) (hρ : ρ.IsSubordinate U)
    (x : X) (L : V →L[ℝ] TangentSpace I x) (α : V [⋀^Fin 1]→L[ℝ] ℝ)
    (heq : ∀ i, x ∈ U i → (g i x).compContinuousLinearMap L = α) :
    (partitionNativeCovector ρ g x).compContinuousLinearMap L = α := by
  classical
  ext vs
  change (∑ i ∈ ρ.finsupport x, ρ i x • g i x) (fun j => L (vs j)) = α vs
  rw [ContinuousAlternatingMap.sum_apply]
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  calc
    (∑ i ∈ ρ.finsupport x, ρ i x * g i x (fun j => L (vs j))) =
        ∑ i ∈ ρ.finsupport x, ρ i x * α vs := by
      apply Finset.sum_congr rfl
      intro i hi
      have hx : x ∈ U i := hρ i (subset_closure (by
        simpa only [ρ.mem_finsupport, Function.mem_support] using hi))
      exact congrArg (fun a : ℝ => ρ i x * a) (congrArg (fun a => a vs) (heq i hx))
    _ = (∑ i ∈ ρ.finsupport x, ρ i x) * α vs := (Finset.sum_mul _ _ _).symm
    _ = α vs := by rw [ρ.sum_finsupport x (mem_univ x), one_mul]

end NativePartition

section LocalCovectors

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace X]
  {I : ModelWithCorners ℝ E H} [ChartedSpace H X] [IsManifold I ∞ X]

/-- The local version of native covector evaluation uses the genuine
open patch; values of its spatial map outside that patch are irrelevant. -/
theorem contMDiffOn_nativeTotalCovector_eval {d : ℕ} (N : SmoothManifold d)
    (p : X → Parameter) (q : X → N.Point) (α : Parameter → N.Form 1)
    (hp : ContMDiff I (𝓡∂ 1) ∞ p) {U : Set X} (hU : IsOpen U)
    (hq : ContMDiffOn I 𝓘(ℝ, Model d) ∞ q U)
    (hα : N.IsSmoothIntervalFormFamily α) :
    ContMDiffOn I.tangent 𝓘(ℝ, ℝ) ∞
      (fun v : TangentBundle I X => nativeTotalCovector I N p q α v.proj (fun _ => v.2))
      (Bundle.TotalSpace.proj ⁻¹' U) := by
  have ht := hq.contMDiffOn_tangentMapWithin (m := ∞) (by simp) hU.uniqueMDiffOn
  have ht' : ContMDiffOn I.tangent (𝓘(ℝ, Model d)).tangent ∞
      (tangentMap I 𝓘(ℝ, Model d) q) (Bundle.TotalSpace.proj ⁻¹' U) := by
    apply ht.congr
    intro v hv
    exact (tangentMapWithin_eq_tangentMap (hU.uniqueMDiffOn _ hv)
      ((hq.contMDiffAt (hU.mem_nhds hv)).mdifferentiableAt (by simp))).symm
  have hp' : ContMDiff I.tangent (𝓡∂ 1) ∞
      (fun v : TangentBundle I X => p v.proj) :=
    hp.comp (Bundle.contMDiff_proj (TangentSpace I))
  exact hα.contMDiff_tangentEvaluation.comp_contMDiffOn (hp'.contMDiffOn.prodMk ht')

omit [IsManifold I ∞ X] in
/-- The local inverse of a total patch recovers the whole primitive on
the slice tangent fiber. Its spatial patch differential is onto. -/
theorem nativeTotalCovector_restrict_of_patch {a d : ℕ}
    (A : SmoothManifold a) (N : SmoothManifold d)
    (p : X → Parameter) (q : X → N.Point) (β : Parameter → N.Form 1)
    (s : A.Point → X) (f : N.Point → A.Point)
    (hs : ContMDiff 𝓘(ℝ, Model a) I ∞ s)
    (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model a) ∞ f)
    (t : Parameter) (hparam : ∀ x, p (s x) = t)
    (hqf : ∀ u, q (s (f u)) = u)
    (hq : ∀ u, ContMDiffAt I 𝓘(ℝ, Model d) ∞ q (s (f u)))
    (Λ : A.Form 1) (hΛ : N.pullback A f Λ = β t)
    (u : N.Point) (hbij : Function.Surjective
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model a) f u)) :
    (nativeTotalCovector I N p q β (s (f u))).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, Model a) I s (f u)) = Λ (f u) := by
  apply SmoothManifold.form_eq_of_comp_eq (d := a) (r := 1) (E := Model d) _ _
    (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model a) f u) hbij
  have he : q ∘ (s ∘ f) = id := funext hqf
  have hsf := hs.comp hf
  have hd := mfderiv_comp u ((hq u).mdifferentiableAt (by simp))
    (hsf.mdifferentiableAt (by simp))
  rw [he, mfderiv_id] at hd
  have hds := mfderiv_comp u (hs.mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))
  rw [hds] at hd
  change ContinuousLinearMap.id ℝ (Model d) =
    (mfderiv I 𝓘(ℝ, Model d) q (s (f u))).comp
      ((mfderiv 𝓘(ℝ, Model a) I s (f u)).comp
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model a) f u)) at hd
  have hv := congrFun hΛ u
  ext vs
  rw [nativeTotalCovector, hparam, hqf]
  change β t u (fun j =>
    ((mfderiv I 𝓘(ℝ, Model d) q (s (f u))).comp
      ((mfderiv 𝓘(ℝ, Model a) I s (f u)).comp
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model a) f u))) (vs j)) = _
  rw [← hd]
  exact (congrArg (fun α => α vs) hv).symm

end LocalCovectors

namespace IntrinsicCompletionGluing.RelativeOpenCover

/-- The inverse of an actual open patch is smooth on its range when
its lifted charts belong to the total maximal atlas. -/
theorem contMDiffOn_patchInverse
    {E H Y X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [Nonempty H] [TopologicalSpace Y] [Nonempty Y]
    [TopologicalSpace X] {I : ModelWithCorners ℝ E H}
    [ChartedSpace H Y] [ChartedSpace H X] [IsManifold I ∞ Y]
    (i : Y → X) (hi : IsOpenEmbedding i)
    (hmax : ∀ u, (chartAt H u).lift_openEmbedding hi ∈ IsManifold.maximalAtlas I ∞ X) :
    ContMDiffOn I I ∞ (hi.toOpenPartialHomeomorph i).symm (range i) := by
  rintro z ⟨u, rfl⟩
  obtain ⟨g, hg, _, heq⟩ := inverse_germ hi u (hmax u)
  apply (hg.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [heq] with z hz
  exact (congrArg (hi.toOpenPartialHomeomorph i).symm hz).symm.trans
    (hi.toOpenPartialHomeomorph_left_inv i)

end IntrinsicCompletionGluing.RelativeOpenCover

namespace IntrinsicLiouville

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Joint native coefficient germs pull back through a fixed smooth map
to an actual jointly smooth spatial family. Real endpoint extensions
are glued from the source germs; they are not an extra hypothesis. -/
theorem IsLocallyExtendibleFormFamily.isSmoothInterval_pullback
    {α : Parameter → Form k M 1} (hα : IsLocallyExtendibleFormFamily α)
    {d : ℕ} (N : SmoothManifold d) (f : N.Point → M)
    (hf : ContMDiff 𝓘(ℝ, Model d) (𝓡∂ (k + 1)) ∞ f) :
    N.IsSmoothIntervalFormFamily (fun t => pullbackForm N f (α t)) := by
  classical
  let A : Set (ℝ × N.Point) := parameterInterval ×ˢ univ
  let a : (p : ℝ × N.Point) → N.Tangent p.2 [⋀^Fin 1]→L[ℝ] ℝ := fun p =>
    if ht : p.1 ∈ parameterInterval then pullbackForm N f (α ⟨p.1, ht⟩) p.2 else 0
  have hlocal : ∀ p ∈ A, ∃ U, IsOpen U ∧ p ∈ U ∧ ∃ g : ℝ → N.Form 1,
      N.IsSmoothFormFamilyOn g U ∧ ∀ q ∈ U ∩ A, g q.1 q.2 = a q := by
    rintro ⟨s, x⟩ ⟨hs, _⟩
    let t : Parameter := ⟨s, hs⟩
    let e := chartAt (EuclideanHalfSpace (k + 1)) (f x)
    have hx : f x ∈ e.source := mem_chart_source _ _
    have he := chart_mem_atlas (EuclideanHalfSpace (k + 1)) (f x)
    obtain ⟨V, β, hV, hpV, hβ, hβeq⟩ := hα e he t (f x) hx
    let O := f ⁻¹' e.source
    have hO : IsOpen O := e.open_source.preimage hf.continuous
    let Q := e.extend (𝓡∂ (k + 1)) ∘ f
    have hQ : ContMDiffOn 𝓘(ℝ, Model d) 𝓘(ℝ, Model (k + 1)) ∞ Q O :=
      (e.contMDiffOn_extend (IsManifold.subset_maximalAtlas
        (I := 𝓡∂ (k + 1)) (n := ∞) he)).comp hf.contMDiffOn
          (fun _ hy => by simpa only [e.extend_source] using hy)
    let U := (univ ×ˢ O) ∩ (fun p : ℝ × N.Point => (p.1, Q p.2)) ⁻¹' V
    have hcoord : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
        𝓘(ℝ, ℝ × Model (k + 1)) ∞
        (fun p : ℝ × N.Point => (p.1, Q p.2)) (univ ×ˢ O) :=
      contMDiff_fst.contMDiffOn.prodMk_space
        (hQ.comp contMDiff_snd.contMDiffOn (fun _ hy => hy.2))
    have hU : IsOpen U := hcoord.continuousOn.isOpen_inter_preimage
      (isOpen_univ.prod hO) hV
    let g : ℝ → N.Form 1 := fun s y => (β (s, Q y)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (k + 1)) Q y)
    refine ⟨U, hU, ⟨⟨mem_univ _, hx⟩, hpV⟩, g,
      N.isSmoothFormFamilyOn_modelPullback Q hO hQ β hV hβ, ?_⟩
    rintro ⟨s', y⟩ ⟨hyU, hs', _⟩
    let t' : Parameter := ⟨s', hs'⟩
    have hy : f y ∈ e.source := hyU.1.2
    have htarget : Q y ∈ (e.extend (𝓡∂ (k + 1))).target :=
      (e.extend (𝓡∂ (k + 1))).map_source (by
        simpa only [e.extend_source] using hy)
    have hder := mfderiv_comp y
      ((e.contMDiffAt_extend (IsManifold.subset_maximalAtlas
        (I := 𝓡∂ (k + 1)) (n := ∞) he) hy).mdifferentiableAt (by simp))
      (hf.mdifferentiableAt (by simp))
    have hrec := formInChart_comp_chartTangentMap he (α t') hy
    dsimp only [a]
    rw [dite_eq_left hs']
    change (β (s', Q y)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (k + 1)) Q y) = pullbackForm N f (α t') y
    rw [hβeq t' _ htarget hyU.2, hder]
    ext vs
    exact congrArg (fun c => c (fun j =>
      mfderiv 𝓘(ℝ, Model d) (𝓡∂ (k + 1)) f y (vs j))) hrec
  obtain ⟨lam, hlam, heq⟩ := N.exists_smoothFormFamily_extension_of_closed
    (isClosed_Icc.prod isClosed_univ) hlocal
  refine ⟨lam, hlam, ?_⟩
  intro t
  funext x
  have h := heq (t.val, x) ⟨t.property, mem_univ _⟩
  have ht : t.val ∈ parameterInterval := t.property
  simpa only [a, dite_eq_left ht] using h

end IntrinsicLiouville

namespace IntrinsicCompletionGluing.NativeCompletionFamily
open IntrinsicLiouville

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] [T2Space M] [SecondCountableTopology M]
  {α : Parameter → Form k M 1} (F : NativeCompletionFamily α)

local instance : ChartedSpace
    (ModelProd (EuclideanHalfSpace 1) (Model (k + 1))) F.total := F.totalCharts
local instance : IsManifold (familyModel (k + 1)) ∞ F.total := F.total_isManifold
local instance sliceCharts (t : Parameter) : ChartedSpace (Model (k + 1)) (Space (F.patches t)) :=
  completionChartedSpace F.width_pos (F.collar t) (F.embedding t) (F.boundary t) (F.zero t)

/-- A genuine open spatial patch produces a smooth total covector on
its entire range, with precisely the retained full slice primitive.
Only the original patch equations and its actual atlas are required. -/
theorem exists_patch_covector (N : SmoothManifold (k + 1)) [Nonempty N.Point]
    (j : Parameter × N.Point → F.total) (hj : IsOpenEmbedding j)
    (hmax : ∀ u, (chartAt (ModelProd (EuclideanHalfSpace 1) (Model (k + 1))) u).lift_openEmbedding hj ∈
      IsManifold.maximalAtlas (familyModel (k + 1)) ∞ F.total)
    (f : ∀ t, N.Point → (F.slice t).Point)
    (hf : ∀ t, ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ (f t))
    (hfactor : ∀ t u, j (t, u) = sliceIn F.patches t (f t u))
    (hparam : ∀ u, parameter F.patches (j u) = u.1)
    (β : Parameter → N.Form 1) (hβ : N.IsSmoothIntervalFormFamily β)
    (hprimitive : ∀ t, N.pullback (F.slice t) (f t) (F.primitive t) = β t)
    (hbij : ∀ t u, Function.Surjective
      (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) (f t) u)) :
    ∃ g : (z : F.total) → TangentSpace (familyModel (k + 1)) z [⋀^Fin 1]→L[ℝ] ℝ,
      ContMDiffOn (familyModel (k + 1)).tangent 𝓘(ℝ, ℝ) ∞
        (fun v : TangentBundle (familyModel (k + 1)) F.total => g v.proj (fun _ => v.2))
        (Bundle.TotalSpace.proj ⁻¹' range j) ∧
      ∀ t x, sliceIn F.patches t x ∈ range j →
        (g (sliceIn F.patches t x)).compContinuousLinearMap
          (mfderiv 𝓘(ℝ, Model (k + 1)) (familyModel (k + 1))
            (sliceIn F.patches t) x) = F.primitive t x := by
  let r : F.total → Parameter × N.Point := (hj.toOpenPartialHomeomorph j).symm
  let q : F.total → N.Point := Prod.snd ∘ r
  have hr : ContMDiffOn (familyModel (k + 1)) (familyModel (k + 1)) ∞ r (range j) :=
    RelativeOpenCover.contMDiffOn_patchInverse j hj hmax
  have hq : ContMDiffOn (familyModel (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ q (range j) :=
    contMDiff_snd.comp_contMDiffOn hr
  let g := nativeTotalCovector (familyModel (k + 1)) N (parameter F.patches) q β
  refine ⟨g, contMDiffOn_nativeTotalCovector_eval N (parameter F.patches) q β
    F.smooth_parameter hj.isOpen_range hq hβ, ?_⟩
  intro t x hx
  obtain ⟨⟨s, u⟩, hu⟩ := hx
  have hst : s = t := (hparam (s, u)).symm.trans
    ((congrArg (parameter F.patches) hu).trans (parameter_sliceIn F.patches t x))
  subst s
  have hfu : f t u = x := sliceIn_injective F.patches t ((hfactor t u).symm.trans hu)
  subst x
  have hqu : ∀ v, q (sliceIn F.patches t (f t v)) = v := by
    intro v
    rw [← hfactor t v]
    exact congrArg Prod.snd (hj.toOpenPartialHomeomorph_left_inv j)
  apply nativeTotalCovector_restrict_of_patch (F.slice t) N
    (parameter F.patches) q β (sliceIn F.patches t) (f t)
    (contMDiff_sliceIn F.width_pos F.collar F.embedding F.smooth F.boundary
      F.inverse F.zero F.joint F.mixed t) (hf t) t
    (parameter_sliceIn F.patches t) hqu
    (fun v => hq.contMDiffAt (hj.isOpen_range.mem_nhds
      (show sliceIn F.patches t (f t v) ∈ range j from ⟨(t, v), hfactor t v⟩)))
    (F.primitive t) (hprimitive t) u (hbij t u)

/-- The retained native primitive equation gives the literal interior
pullback on every spatial tangent vector. -/
theorem primitive_interior (t : Parameter) :
    (IntrinsicInterior.smoothManifold k M).pullback (F.slice t)
      (interiorIn (F.patches t)) (F.primitive t) =
        IntrinsicLiouville.pullbackForm (IntrinsicInterior.smoothManifold k M)
          Subtype.val (α t) := by
  let N := IntrinsicInterior.smoothManifold k M
  have hn := F.primitive_native t
  funext u
  have hnu := congrFun hn u.val
  have hd := mfderiv_comp u
    ((contMDiff_original F.width_pos (F.collar t) (F.embedding t) (F.smooth t)
      (F.boundary t) (F.inverse t) (F.zero t)).mdifferentiableAt (by simp))
    (IntrinsicInterior.contMDiff_val.mdifferentiableAt (by simp))
  ext vs
  change F.primitive t (original (F.patches t) u.val) (fun j =>
    mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
      (original (F.patches t) ∘ Subtype.val) u (vs j)) = _
  rw [hd]
  exact congrArg (fun a => a (fun j =>
    mfderiv 𝓘(ℝ, Model (k + 1)) (𝓡∂ (k + 1))
      (Subtype.val : IntrinsicInterior.Point k M → M) u (vs j))) hnu

/-- The original interior patch has a jointly smooth total covector
extension. Source coefficient germs, rather than completed regularity,
produce this extension. -/
theorem exists_interior_covector [Nonempty (IntrinsicInterior.Point k M)]
    (hα : IsLocallyExtendibleFormFamily α) :
    ∃ g : (z : F.total) → TangentSpace (familyModel (k + 1)) z [⋀^Fin 1]→L[ℝ] ℝ,
      ContMDiffOn (familyModel (k + 1)).tangent 𝓘(ℝ, ℝ) ∞
        (fun v : TangentBundle (familyModel (k + 1)) F.total => g v.proj (fun _ => v.2))
        (Bundle.TotalSpace.proj ⁻¹' range (totalInterior F.patches)) ∧
      ∀ t x, sliceIn F.patches t x ∈ range (totalInterior F.patches) →
        (g (sliceIn F.patches t x)).compContinuousLinearMap
          (mfderiv 𝓘(ℝ, Model (k + 1)) (familyModel (k + 1))
            (sliceIn F.patches t) x) = F.primitive t x := by
  let N := IntrinsicInterior.smoothManifold k M
  let β := fun t => IntrinsicLiouville.pullbackForm N Subtype.val (α t)
  apply F.exists_patch_covector N (totalInterior F.patches)
    (isOpenEmbedding_totalInterior F.width_pos F.patches F.zero F.joint)
    (fun u => IsManifold.subset_maximalAtlas (I := familyModel (k + 1)) (n := ∞)
      (Or.inl ⟨chartAt _ u, chart_mem_atlas _ u, rfl⟩))
    (fun t => interiorIn (F.patches t))
    (fun t => contMDiff_completionInterior F.width_pos (F.collar t) (F.embedding t)
      (F.smooth t) (F.boundary t) (F.inverse t) (F.zero t))
    (fun t u => (sliceIn_original F.patches t u.val).symm)
    (fun u => parameter_original F.patches u.1 u.2.val)
    β (hα.isSmoothInterval_pullback N Subtype.val IntrinsicInterior.contMDiff_val)
    F.primitive_interior
    (fun t u => (bijective_mfderiv_completionInterior F.width_pos (F.collar t)
      (F.embedding t) (F.smooth t) (F.boundary t) (F.inverse t) (F.zero t) u).2)

local instance fullBandCharts : ChartedSpace (Model (k + 1))
    (Band F.width (IntrinsicBoundary.Point k M)) := bandChartedSpace F.width
local instance fullBandSmooth : IsManifold 𝓘(ℝ, Model (k + 1)) ∞
    (Band F.width (IntrinsicBoundary.Point k M)) := band_isManifold F.width

/-- The entire actual cylinder, including both sides of the seam and
all end radii, has a jointly smooth total covector extension. -/
theorem exists_cylinder_covector [Nonempty (Band F.width (IntrinsicBoundary.Point k M))] :
    ∃ g : (z : F.total) → TangentSpace (familyModel (k + 1)) z [⋀^Fin 1]→L[ℝ] ℝ,
      ContMDiffOn (familyModel (k + 1)).tangent 𝓘(ℝ, ℝ) ∞
        (fun v : TangentBundle (familyModel (k + 1)) F.total => g v.proj (fun _ => v.2))
        (Bundle.TotalSpace.proj ⁻¹' range (totalCylinder F.patches)) ∧
      ∀ t x, sliceIn F.patches t x ∈ range (totalCylinder F.patches) →
        (g (sliceIn F.patches t x)).compContinuousLinearMap
          (mfderiv 𝓘(ℝ, Model (k + 1)) (familyModel (k + 1))
            (sliceIn F.patches t) x) = F.primitive t x := by
  let N := bandManifold F.width (IntrinsicBoundary.smoothManifold k M)
  let : Nonempty N.Point := inferInstanceAs
    (Nonempty (Band F.width (IntrinsicBoundary.Point k M)))
  have hβ := F.cylinder_family
  have he : (fun t => N.pullback (F.slice t) (cylinder (F.patches t)) (F.primitive t)) =
      (fun t => cylinderPrimitive F.width (α t)) := funext F.primitive_cylinder
  change N.IsSmoothIntervalFormFamily
    (fun t => N.pullback (F.slice t) (cylinder (F.patches t)) (F.primitive t)) at hβ
  rw [he] at hβ
  apply F.exists_patch_covector N (totalCylinder F.patches)
    (isOpenEmbedding_totalCylinder F.patches F.joint)
    (fun u => IsManifold.subset_maximalAtlas (I := familyModel (k + 1)) (n := ∞)
      (Or.inr ⟨chartAt _ u, chart_mem_atlas _ u, rfl⟩))
    (fun t => cylinder (F.patches t))
    (fun t => contMDiff_cylinder F.width_pos (F.collar t) (F.embedding t)
      (F.smooth t) (F.boundary t) (F.inverse t) (F.zero t))
    (fun t u => (sliceIn_cylinder F.patches t u).symm)
    (fun u => parameter_totalCylinder _ _)
    (fun t => cylinderPrimitive F.width (α t)) hβ F.primitive_cylinder
    (fun t u => (bijective_mfderiv_cylinder F.width_pos (F.collar t)
      (F.embedding t) (F.smooth t) (F.boundary t) (F.inverse t) (F.zero t) u).2)

/-- The retained completed primitives are the full spatial restrictions
of one smooth actual total covector on their original quotient atlas.
Local native and cylinder formulas construct the covector. No completed
family comparison or smooth completed primitive is supplied as input. -/
theorem exists_smooth_totalPrimitive (hα : IsLocallyExtendibleFormFamily α) :
    ∃ Ω : (z : F.total) → TangentSpace (familyModel (k + 1)) z [⋀^Fin 1]→L[ℝ] ℝ,
      ContMDiff (familyModel (k + 1)).tangent 𝓘(ℝ, ℝ) ∞
        (fun v : TangentBundle (familyModel (k + 1)) F.total => Ω v.proj (fun _ => v.2)) ∧
      ∀ t x, (Ω (sliceIn F.patches t x)).compContinuousLinearMap
        (mfderiv 𝓘(ℝ, Model (k + 1)) (familyModel (k + 1))
          (sliceIn F.patches t) x) = F.primitive t x := by
  classical
  have hlocal : ∀ z : F.total, ∃ U : Set F.total,
      IsOpen U ∧ z ∈ U ∧
      ∃ g : (z : F.total) → TangentSpace (familyModel (k + 1)) z [⋀^Fin 1]→L[ℝ] ℝ,
        ContMDiffOn (familyModel (k + 1)).tangent 𝓘(ℝ, ℝ) ∞
          (fun v : TangentBundle (familyModel (k + 1)) F.total => g v.proj (fun _ => v.2))
          (Bundle.TotalSpace.proj ⁻¹' U) ∧
        ∀ t x, sliceIn F.patches t x ∈ U →
          (g (sliceIn F.patches t x)).compContinuousLinearMap
            (mfderiv 𝓘(ℝ, Model (k + 1)) (familyModel (k + 1))
              (sliceIn F.patches t) x) = F.primitive t x := by
    intro z
    rcases totalInterior_cylinder_cover F.width_pos F.patches F.zero z with
      ⟨u, rfl⟩ | ⟨v, rfl⟩
    · let : Nonempty (IntrinsicInterior.Point k M) := ⟨u.2⟩
      obtain ⟨g, hg, heq⟩ := F.exists_interior_covector hα
      exact ⟨range (totalInterior F.patches),
        (isOpenEmbedding_totalInterior F.width_pos F.patches F.zero F.joint).isOpen_range,
        mem_range_self u, g, hg, heq⟩
    · let : Nonempty (Band F.width (IntrinsicBoundary.Point k M)) := ⟨v.2⟩
      obtain ⟨g, hg, heq⟩ := F.exists_cylinder_covector
      exact ⟨range (totalCylinder F.patches),
        (isOpenEmbedding_totalCylinder F.patches F.joint).isOpen_range,
        mem_range_self v, g, hg, heq⟩
  choose U hU hzU g hg heq using hlocal
  let : T2Space F.total := F.total_t2Space
  let : SecondCountableTopology F.total := F.total_secondCountable
  let : LocallyCompactSpace (ModelProd (EuclideanHalfSpace 1) (Model (k + 1))) :=
    (familyModel (k + 1)).locallyCompactSpace
  let : LocallyCompactSpace F.total :=
    ChartedSpace.locallyCompactSpace (ModelProd (EuclideanHalfSpace 1) (Model (k + 1))) F.total
  let : SigmaCompactSpace F.total := sigmaCompactSpace_of_locallyCompact_secondCountable
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (familyModel (k + 1)) isClosed_univ U hU
    (fun z _ => mem_iUnion.mpr ⟨z, hzU z⟩)
  refine ⟨partitionNativeCovector ρ g,
    contMDiff_partitionNativeCovector ρ g U hρ hU hg, ?_⟩
  intro t x
  exact partitionNativeCovector_comp_eq (V := Model (k + 1)) ρ g U hρ (sliceIn F.patches t x)
    (mfderiv 𝓘(ℝ, Model (k + 1)) (familyModel (k + 1)) (sliceIn F.patches t) x)
    (F.primitive t x) (fun i hi => heq i t x hi)

end IntrinsicCompletionGluing.NativeCompletionFamily

namespace IntrinsicSmoothBundle.LocalCompletionFamily
open IntrinsicCompletionGluing

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  {E : Parameter → Type*} [∀ t, TopologicalSpace (E t)]
  [TopologicalSpace (Bundle.TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]
  {P : BundlePrimitiveData (k := k) (M := M) E}
  {c : OriginalCompactChart (k := k) (M := M) (E := E)} {t : Parameter}

/-- Original compact-bundle source germs produce a global total covector
on the retained local completion family, restricting to its exact
primitive on every full spatial slice, including endpoint slices. -/
theorem exists_smooth_totalPrimitive (F : LocalCompletionFamily P c t) :
    letI := F.native.totalCharts
    letI := F.native.total_isManifold
    ∃ Ω : (z : F.native.total) → TangentSpace (familyModel (k + 1)) z [⋀^Fin 1]→L[ℝ] ℝ,
      ContMDiff (familyModel (k + 1)).tangent 𝓘(ℝ, ℝ) ∞
        (fun v : TangentBundle (familyModel (k + 1)) F.native.total => Ω v.proj (fun _ => v.2)) ∧
      ∀ s,
        letI := completionChartedSpace F.native.width_pos (F.native.collar s)
          (F.native.embedding s) (F.native.boundary s) (F.native.zero s)
        ∀ x, (Ω (sliceIn F.native.patches s x)).compContinuousLinearMap
          (mfderiv 𝓘(ℝ, Model (k + 1)) (familyModel (k + 1))
            (sliceIn F.native.patches s) x) = F.native.primitive s x :=
  F.native.exists_smooth_totalPrimitive F.source_smooth

end IntrinsicSmoothBundle.LocalCompletionFamily

namespace IntrinsicSmoothBundle.OriginalBundleLiouvilleLaws
open IntrinsicCompletionGluing

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  {E : Parameter → Type*} [∀ t, TopologicalSpace (E t)]
  [TopologicalSpace (Bundle.TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]
  {P : BundlePrimitiveData (k := k) (M := M) E}

/-- The original compact data construct a jointly smooth native total
primitive, whose restriction agrees both with the entire retained
completion slices and with the actual compact-chart primitive on the
produced relative neighborhood. This adds no completion smoothness input. -/
theorem localCompletionFamily_has_smooth_totalPrimitive (L : OriginalBundleLiouvilleLaws P)
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) :
    let F := L.localCompletionFamily c t ht
    letI := F.native.totalCharts
    letI := F.native.total_isManifold
    ∃ Ω : (z : F.native.total) → TangentSpace (familyModel (k + 1)) z [⋀^Fin 1]→L[ℝ] ℝ,
      ContMDiff (familyModel (k + 1)).tangent 𝓘(ℝ, ℝ) ∞
        (fun v : TangentBundle (familyModel (k + 1)) F.native.total => Ω v.proj (fun _ => v.2)) ∧
      (∀ s,
        letI := completionChartedSpace F.native.width_pos (F.native.collar s)
          (F.native.embedding s) (F.native.boundary s) (F.native.zero s)
        ∀ x, (Ω (sliceIn F.native.patches s x)).compContinuousLinearMap
          (mfderiv 𝓘(ℝ, Model (k + 1)) (familyModel (k + 1))
            (sliceIn F.native.patches s) x) = F.native.primitive s x) ∧
      ∀ s ∈ F.base,
        letI := completionChartedSpace F.native.width_pos (F.native.collar s)
          (F.native.embedding s) (F.native.boundary s) (F.native.zero s)
        (fun x => ((Ω (sliceIn F.native.patches s (original (F.native.patches s) x))).compContinuousLinearMap
            (mfderiv 𝓘(ℝ, Model (k + 1)) (familyModel (k + 1))
              (sliceIn F.native.patches s) (original (F.native.patches s) x))).compContinuousLinearMap
            (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
              (original (F.native.patches s)) x)) = P.form c s := by
  let F := L.localCompletionFamily c t ht
  let := F.native.totalCharts
  let := F.native.total_isManifold
  obtain ⟨Ω, hsmooth, hrestriction⟩ := F.exists_smooth_totalPrimitive
  refine ⟨Ω, hsmooth, hrestriction, ?_⟩
  intro s hs
  let := completionChartedSpace F.native.width_pos (F.native.collar s)
    (F.native.embedding s) (F.native.boundary s) (F.native.zero s)
  funext x
  rw [hrestriction s]
  exact congrFun (F.primitive_native_on_base s hs) x

end IntrinsicSmoothBundle.OriginalBundleLiouvilleLaws

end FsFltz.Geometry
