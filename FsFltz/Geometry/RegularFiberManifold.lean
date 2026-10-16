import FsFltz.Geometry.LocalInverse
import FsFltz.Geometry.RegularLevelChart
import Mathlib.Analysis.Calculus.Implicit

/-!
# Smooth normal forms at regular levels

Source: `geoemtric-part-fsf.tex`, `g:initial`, lines 373–379, and `sec:lean`,
lines 783–814; `geometric-part-fsf-proof.tex`, `prop:allinitial`, lines
923–930, and the regular-level foundations at lines 2294–2299.

The normal form is constructed from the actual surjective derivative. Its
first coordinate is the given map, so restriction to a level describes the
literal level subset. No smooth structure on that level is an input.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry

set_option backward.isDefEq.respectTransparency false

/-- A smooth map with surjective differential admits a smooth product normal
form. The second factor is the kernel of its actual differential. -/
theorem exists_regularLevel_kernel_normalForm
    {E F M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → F} {a : M}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hd : Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f a)) :
    let D : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f a
    ∃ e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F × D.ker) M (F × D.ker) ∞,
      a ∈ e.source ∧ ∀ x ∈ e.source, (e x).1 = f x := by
  let D : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f a
  obtain ⟨P, hP⟩ := D.ker_closedComplemented_of_finiteDimensional_range
  let A : E ≃L[ℝ] F × D.ker := D.equivProdOfSurjectiveOfIsCompl P
    (LinearMap.range_eq_top.mpr hd) (LinearMap.range_eq_of_proj hP)
    (LinearMap.isCompl_of_proj hP)
  let c := chartAt E a
  let g : M → F × D.ker := fun x => (f x, P (c x))
  have ha : a ∈ c.source := mem_chart_source E a
  have hc : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c c.source := contMDiffOn_chart
  have hq : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, D.ker) ∞ (P ∘ c) c.source :=
    P.contMDiff.comp_contMDiffOn hc
  have hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F × D.ker) ∞ g c.source :=
    hf.contMDiffOn.prodMk_space hq
  have hca := (hc.contMDiffAt (c.open_source.mem_nhds ha)).mdifferentiableAt (by simp)
  have hqa := (hq.contMDiffAt (c.open_source.mem_nhds ha)).mdifferentiableAt (by simp)
  have hchart : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c a = ContinuousLinearMap.id ℝ E := by
    exact mfderiv_extChartAt_self (I := 𝓘(ℝ, E))
  have hqd : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, D.ker) (P ∘ c) a = P := by
    rw [mfderiv_comp a P.hasMFDerivAt.mdifferentiableAt hca,
      P.hasMFDerivAt.mfderiv, hchart]
    rfl
  have hgd : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F × D.ker) g a = A.toContinuousLinearMap := by
    have hfd := (hf.mdifferentiableAt (by simp)).hasMFDerivAt (x := a)
    have hqd' := hqa.hasMFDerivAt
    have hp : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, F × D.ker) g a
        (D.prod (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, D.ker) (P ∘ c) a)) :=
      ⟨hfd.1.prodMk hqd'.1, hfd.2.prodMk hqd'.2⟩
    rw [hp.mfderiv, hqd]
    rfl
  obtain ⟨e, hae, he⟩ := isLocalDiffeomorphAt_of_bijective_mfderiv_manifold
    c.open_source hg ha (by rw [hgd]; exact A.bijective)
  refine ⟨e, hae, ?_⟩
  intro x hx
  exact congrArg Prod.fst (he hx).symm

/-- The same normal form uses one fixed Euclidean kernel model at every
regular point, including when that model has dimension zero. -/
theorem exists_regularLevel_normalForm
    {E F M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → F} {a : M}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hd : Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f a)) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, E)
        𝓘(ℝ, F × Model (Module.finrank ℝ E - Module.finrank ℝ F))
        M (F × Model (Module.finrank ℝ E - Module.finrank ℝ F)) ∞,
      a ∈ e.source ∧ ∀ x ∈ e.source, (e x).1 = f x := by
  let D : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f a
  have hdim : Module.finrank ℝ D.ker =
      Module.finrank ℝ (Model (Module.finrank ℝ E - Module.finrank ℝ F)) := by
    have hrank := D.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hd, finrank_top] at hrank
    simp only [Model, finrank_euclideanSpace_fin]
    omega
  let B : D.ker ≃L[ℝ] Model (Module.finrank ℝ E - Module.finrank ℝ F) :=
    (LinearEquiv.ofFinrankEq _ _ hdim).toContinuousLinearEquiv
  let Q := (ContinuousLinearEquiv.refl ℝ F).prodCongr B
  obtain ⟨e, ha, hfirst⟩ := exists_regularLevel_kernel_normalForm hf hd
  let q := Q.toDiffeomorph.toPartialDiffeomorph
  refine ⟨e.trans q, ⟨ha, mem_univ _⟩, ?_⟩
  intro x hx
  exact hfirst x hx.1

/-- A chart on a literal level, retained together with its smooth ambient
normal form and the exact restriction equations. -/
structure RegularLevelChart {d k : ℕ} (M : SmoothManifold d)
    (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : M.Point → F) (c : F) where
  ambient : PartialDiffeomorph 𝓘(ℝ, Model d) 𝓘(ℝ, F × Model k)
    M.Point (F × Model k) ∞
  first_eq : ∀ x ∈ ambient.source, (ambient x).1 = f x
  chart : OpenPartialHomeomorph {x : M.Point // f x = c} (Model k)
  source_eq : chart.source = Subtype.val ⁻¹' ambient.source
  target_eq : chart.target = (fun v : Model k => (c, v)) ⁻¹' ambient.target
  toFun_eq : ∀ x ∈ chart.source, chart x = (ambient x.val).2
  invFun_eq : ∀ v ∈ chart.target, (chart.symm v).val = ambient.symm (c, v)

namespace RegularLevelChart

variable {d k : ℕ} {M : SmoothManifold d}
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : M.Point → F} {c : F}

/-- Normal forms supply a chart at every regular point of the literal level. -/
theorem exists_at [FiniteDimensional ℝ F]
    (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, F) ∞ f)
    (x : {x : M.Point // f x = c})
    (hx : Function.Surjective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, F) f x.val)) :
    ∃ q : RegularLevelChart (k := d - Module.finrank ℝ F) M F f c,
      x ∈ q.chart.source := by
  obtain ⟨e, he, hfirst⟩ :
      ∃ e : PartialDiffeomorph 𝓘(ℝ, Model d)
          𝓘(ℝ, F × Model (d - Module.finrank ℝ F))
          M.Point (F × Model (d - Module.finrank ℝ F)) ∞,
        x.val ∈ e.source ∧ ∀ y ∈ e.source, (e y).1 = f y := by
    have h := exists_regularLevel_normalForm hf hx
    have hdim : Module.finrank ℝ (Model d) = d := by simp [Model]
    rwa [hdim] at h
  obtain ⟨r, hs, ht, hfor, hinv⟩ :=
    exists_restricted_level_chart f c e.toOpenPartialHomeomorph hfirst x
  refine ⟨⟨e, hfirst, r, hs, ht, hfor, hinv⟩, ?_⟩
  change x ∈ r.source
  rwa [hs]

/-- Transitions are restrictions of smooth ambient normal-form transitions,
precomposed with insertion into the fixed level and followed by projection. -/
theorem contDiffOn_transition (q q' : RegularLevelChart (k := k) M F f c) :
    ContDiffOn ℝ ∞ (q.chart.symm.trans q'.chart)
      (q.chart.symm.trans q'.chart).source := by
  let S := (q.chart.symm.trans q'.chart).source
  have hsub : MapsTo (fun v : Model k => (c, v)) S
      (q.ambient.symm.trans q'.ambient).source := by
    intro v hv
    change v ∈ q.chart.target ∧ q.chart.symm v ∈ q'.chart.source at hv
    change (c, v) ∈ q.ambient.target ∧ q.ambient.symm (c, v) ∈ q'.ambient.source
    refine ⟨?_, ?_⟩
    · have h := hv.1
      rwa [q.target_eq] at h
    · have h := hv.2
      rw [q'.source_eq] at h
      change (q.chart.symm v).val ∈ q'.ambient.source at h
      rwa [q.invFun_eq v hv.1] at h
  have ht := (q.ambient.symm.trans q'.ambient).contMDiffOn_toFun.contDiffOn
  have hins : ContDiff ℝ ∞ (fun v : Model k => (c, v)) :=
    contDiff_const.prodMk contDiff_id
  apply (contDiff_snd.comp_contDiffOn (ht.comp hins.contDiffOn hsub)).congr
  intro v hv
  change v ∈ q.chart.target ∧ q.chart.symm v ∈ q'.chart.source at hv
  change q'.chart (q.chart.symm v) = (q'.ambient (q.ambient.symm (c, v))).2
  rw [q'.toFun_eq _ hv.2, q.invFun_eq v hv.1]

end RegularLevelChart

/-- A regular level carries a genuine smooth manifold structure of the
expected codimension, with its literal inclusion realized by a smooth
embedding. The inherited topology supplies Hausdorffness and second
countability; no nonemptiness or positive-dimensional hypothesis is needed. -/
theorem exists_regularLevel_embedding
    {d : ℕ} (M : SmoothManifold d)
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (f : M.Point → F) (c : F)
    (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, F) ∞ f)
    (hregular : ∀ x, f x = c →
      Function.Surjective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, F) f x)) :
    ∃ (N : SmoothManifold (d - Module.finrank ℝ F)) (j : N.SmoothEmbedding M),
      Set.range j.map = {x | f x = c} := by
  let k := d - Module.finrank ℝ F
  let X := {x : M.Point // f x = c}
  let q (x : X) : RegularLevelChart (k := k) M F f c :=
    (RegularLevelChart.exists_at hf x (hregular x.val x.property)).choose
  have hq (x : X) : x ∈ (q x).chart.source :=
    (RegularLevelChart.exists_at hf x (hregular x.val x.property)).choose_spec
  let : ChartedSpace (Model k) X := {
    atlas := Set.range (fun q : RegularLevelChart (k := k) M F f c => q.chart)
    chartAt := fun x => (q x).chart
    mem_chart_source := hq
    chart_mem_atlas := fun x => ⟨q x, rfl⟩ }
  let : IsManifold 𝓘(ℝ, Model k) ∞ X := by
    apply isManifold_of_contDiffOn
    rintro e e' ⟨r, rfl⟩ ⟨r', rfl⟩
    simpa using r.contDiffOn_transition r'
  have hval : ContMDiff 𝓘(ℝ, Model k) 𝓘(ℝ, Model d) ∞ (Subtype.val : X → M.Point) := by
    intro x
    apply (contMDiffAt_iff_source_of_mem_source (mem_chart_source (Model k) x)).mpr
    have hc : (q x).chart x ∈ (q x).chart.target := (q x).chart.map_source (hq x)
    have he : (c, (q x).chart x) ∈ (q x).ambient.target := by
      rwa [(q x).target_eq] at hc
    have hs := (q x).ambient.contMDiffOn_invFun.contMDiffAt
      ((q x).ambient.open_target.mem_nhds he)
    have hins : ContMDiff 𝓘(ℝ, Model k) 𝓘(ℝ, F × Model k) ∞
        (fun v : Model k => (c, v)) :=
      (contDiff_const.prodMk contDiff_id).contMDiff
    apply (hs.comp ((q x).chart x) hins.contMDiffAt).contMDiffWithinAt
      |>.congr_of_eventuallyEq_of_mem _ (by simp)
    have ht : ∀ᶠ v in 𝓝 ((q x).chart x), v ∈ (q x).chart.target :=
      (q x).chart.open_target.mem_nhds hc
    filter_upwards [ht.filter_mono nhdsWithin_le_nhds] with v hv
    exact (q x).invFun_eq v hv
  have hinj (x : X) : Function.Injective
      (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model d) (Subtype.val : X → M.Point) x) := by
    have hxs : x.val ∈ (q x).ambient.source := by
      have h := hq x
      rwa [(q x).source_eq] at h
    let g : M.Point → Model k := fun y => ((q x).ambient y).2
    have hg : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model k) ∞ g x.val :=
      (ContinuousLinearMap.snd ℝ F (Model k)).contMDiff.contMDiffAt.comp x.val
        ((q x).ambient.contMDiffOn_toFun.contMDiffAt
          ((q x).ambient.open_source.mem_nhds hxs))
    have heq : (extChartAt 𝓘(ℝ, Model k) x : X → Model k) =ᶠ[𝓝 x]
        g ∘ Subtype.val := by
      filter_upwards [(q x).chart.open_source.mem_nhds (hq x)] with y hy
      exact (q x).toFun_eq y hy
    have hd := mfderiv_comp (f := (Subtype.val : X → M.Point)) (g := g) x
      (hg.mdifferentiableAt (by simp)) (hval.mdifferentiableAt (by simp))
    have hi := mfderiv_extChartAt_self (I := 𝓘(ℝ, Model k)) (x := x)
    rw [heq.mfderiv_eq, hd] at hi
    have hleft (v : TangentSpace 𝓘(ℝ, Model k) x) :
        mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model k) g x.val
          (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model d) Subtype.val x v) = v :=
      congrArg (fun A => A v) hi
    intro v w hvw
    have h := congrArg (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model k) g x.val) hvw
    exact (hleft v).symm.trans (h.trans (hleft w))
  let N : SmoothManifold k := {
    Point := X
    topology := inferInstance
    charts := inferInstance
    hausdorff := inferInstance
    secondCountable := Topology.IsEmbedding.subtypeVal.secondCountableTopology
    smooth := inferInstance }
  let j : N.SmoothEmbedding M := {
    map := ⟨Subtype.val, hval⟩
    embedding := Topology.IsEmbedding.subtypeVal
    immersion := hinj }
  refine ⟨N, j, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx⟩
    change f y = c
    change x.val = y at hx
    rw [← hx]
    exact x.property
  · intro hy
    exact ⟨⟨y, hy⟩, rfl⟩

/-- The tangent image of a regular level embedding is the kernel of the
actual ambient differential. This identifies the tangent spaces required
when restricting forms and intrinsic Liouville fields to the level. -/
theorem regularLevel_embedding_tangent_range
    {d : ℕ} {M : SmoothManifold d}
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : M.Point → F} {c : F}
    (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, F) ∞ f)
    (hregular : ∀ y, f y = c →
      Function.Surjective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, F) f y))
    {N : SmoothManifold (d - Module.finrank ℝ F)} (j : N.SmoothEmbedding M)
    (himage : Set.range j.map = {y | f y = c}) (x : N.Point) :
    (mfderiv 𝓘(ℝ, Model (d - Module.finrank ℝ F)) 𝓘(ℝ, Model d) j.map x).range =
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, F) f (j.map x)).ker := by
  let D : Model d →L[ℝ] F := mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, F) f (j.map x)
  let J : Model (d - Module.finrank ℝ F) →L[ℝ] Model d :=
    mfderiv 𝓘(ℝ, Model (d - Module.finrank ℝ F)) 𝓘(ℝ, Model d) j.map x
  have hj (y : N.Point) : f (j.map y) = c := by
    have h : j.map y ∈ Set.range j.map := ⟨y, rfl⟩
    rwa [himage] at h
  have hconst : f ∘ j.map = fun _ => c := funext hj
  have hcomp : D.comp J = 0 := by
    have h := mfderiv_comp (f := j.map) (g := f) x
      (hf.mdifferentiableAt (by simp)) (j.map.contMDiff.mdifferentiableAt (by simp))
    rw [hconst, mfderiv_const] at h
    exact h.symm
  have hle : J.range ≤ D.ker := by
    rintro v ⟨w, rfl⟩
    change D (J w) = 0
    exact congrArg (fun L : Model (d - Module.finrank ℝ F) →L[ℝ] F => L w) hcomp
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hdimJ : Module.finrank ℝ J.range = d - Module.finrank ℝ F := by
    rw [LinearMap.finrank_range_of_inj (f := J.toLinearMap) (j.immersion x)]
    exact finrank_euclideanSpace_fin
  have hdimD := D.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (hregular (j.map x) (hj x)), finrank_top] at hdimD
  have hdim : Module.finrank ℝ (Model d) = d := finrank_euclideanSpace_fin
  rw [hdim] at hdimD
  change Module.finrank ℝ J.range = Module.finrank ℝ D.ker
  omega

end FsFltz.Geometry
