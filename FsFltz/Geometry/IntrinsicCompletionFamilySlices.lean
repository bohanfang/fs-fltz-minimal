import FsFltz.Geometry.IntrinsicCompletionFamilyAtlas

/-!
# The original completion slice atlas in the shared total family

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 142–158;
`def:chain`, lines 163–169; and `sec:lean`, lines 788–793 and 805–812.
The slice carries its already constructed original completion atlas.
Its native interior and full cylinder have smooth inverse germs in that
atlas. These germs prove the patch criterion used to compare the original
slice with the shared total atlas. No induced-atlas compatibility is input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCompletionGluing

private theorem corner_patch_inverse_germ
    {E H U X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [Nonempty H] [TopologicalSpace U] [TopologicalSpace X]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H U] [ChartedSpace H X]
    [IsManifold I ∞ U] {j : U → X} (hj : IsOpenEmbedding j) (u : U)
    (hf : (chartAt H u).lift_openEmbedding hj ∈ IsManifold.maximalAtlas I ∞ X) :
    ∃ g : X → U, ContMDiffAt I I ∞ g (j u) ∧ g (j u) = u ∧
      ∀ᶠ z in 𝓝 (j u), j (g z) = z := by
  let e := chartAt H u
  let f := e.lift_openEmbedding hj
  have hu : u ∈ e.source := mem_chart_source H u
  have hfu : f (j u) = e u := OpenPartialHomeomorph.lift_openEmbedding_apply e hj
  have hfs : j u ∈ f.source := ⟨u, hu, rfl⟩
  have hes := contMDiffAt_symm_of_mem_maximalAtlas (I := I) (n := ∞)
    (IsManifold.chart_mem_maximalAtlas u) (e.map_source hu)
  have hff := contMDiffAt_of_mem_maximalAtlas hf hfs
  refine ⟨e.symm ∘ f, hes.comp_of_eq hff hfu, ?_, ?_⟩
  · change e.symm (f (j u)) = u
    rw [hfu, e.left_inv hu]
  · filter_upwards [f.open_source.mem_nhds hfs] with z hz
    exact f.left_inv hz

section SingleSlice

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {δ : ℝ} (hδ : 0 < δ)
  (C : ℝ × IntrinsicBoundary.Point k M → M)
  (hemb : IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val))
  (hC : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ C
    (Half δ (IntrinsicBoundary.Point k M)))
  (hboundary : ∀ p : Half δ (IntrinsicBoundary.Point k M),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C p.val) ↔ p.val.1 = 0)
  (hinv : ∀ p ∈ Half δ (IntrinsicBoundary.Point k M),
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C q) = q)
  (hzero : ∀ b : IntrinsicBoundary.Point k M, C (0, b) = b.val)

local instance sliceFullBandCharts : ChartedSpace (Model (k + 1))
    (Band δ (IntrinsicBoundary.Point k M)) := bandChartedSpace δ

local instance sliceFullBandSmooth : IsManifold 𝓘(ℝ, Model (k + 1)) ∞
    (Band δ (IntrinsicBoundary.Point k M)) := band_isManifold δ

include hC hinv

/-- The unchanged native interior is smooth for the established completion
atlas, by composition through the original native inclusion. -/
theorem contMDiff_completionInterior :
    letI := completionChartedSpace hδ C hemb hboundary hzero
    ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞
      (interiorIn (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)) := by
  let := completionChartedSpace hδ C hemb hboundary hzero
  exact (contMDiff_original hδ C hemb hC hboundary hinv hzero).comp
    IntrinsicInterior.contMDiff_val

/-- The actual interior patch differential is invertible, using the native
inclusion differential and the native interior differential. -/
theorem bijective_mfderiv_completionInterior (u : IntrinsicInterior.Point k M) :
    letI := completionChartedSpace hδ C hemb hboundary hzero
    Function.Bijective (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
      (interiorIn (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)) u) := by
  let := completionChartedSpace hδ C hemb hboundary hzero
  change Function.Bijective (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
    (original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) ∘ Subtype.val) u)
  rw [mfderiv_comp u
    ((contMDiff_original hδ C hemb hC hboundary hinv hzero).mdifferentiableAt (by simp))
    (IntrinsicInterior.contMDiff_val.mdifferentiableAt (by simp))]
  exact (bijective_mfderiv_original hδ C hemb hC hboundary hinv hzero u.val).comp
    (IntrinsicInterior.bijective_mfderiv_val u)

/-- The native interior has a smooth inverse germ in the existing original
completion atlas; this is derived from its actual invertible differential. -/
theorem completionInterior_inverse_germ (u : IntrinsicInterior.Point k M) :
    letI := completionChartedSpace hδ C hemb hboundary hzero
    ∃ g : Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) →
      IntrinsicInterior.Point k M,
      ContMDiffAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ g
        (interiorIn (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) u) ∧
      g (interiorIn (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) u) = u ∧
      ∀ᶠ z in 𝓝 (interiorIn (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) u),
        interiorIn (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) (g z) = z := by
  let := completionChartedSpace hδ C hemb hboundary hzero
  let := completion_isManifold hδ C hemb hC hboundary hinv hzero
  let j := interiorIn (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)
  obtain ⟨q, hu, hq⟩ := isLocalDiffeomorphAt_of_bijective_mfderiv_manifold
    isOpen_univ (contMDiff_completionInterior hδ C hemb hC hboundary hinv hzero).contMDiffOn
    (mem_univ u) (bijective_mfderiv_completionInterior hδ C hemb hC hboundary hinv hzero u)
  have hju : j u ∈ q.target := by
    change interiorIn (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) u ∈ q.target
    rw [hq hu]
    exact q.map_source hu
  refine ⟨q.symm, q.contMDiffOn_invFun.contMDiffAt (q.open_target.mem_nhds hju), ?_, ?_⟩
  · rw [hq hu]
    exact q.left_inv hu
  · filter_upwards [q.open_target.mem_nhds hju] with z hz
    exact (hq (q.map_target hz)).trans (q.right_inv hz)

/-- Smoothness in the original slice atlas is detected on the unchanged
native interior and the full cylinder, including all new end radii. -/
theorem contMDiff_completion_iff
    {F H N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace N] {J : ModelWithCorners ℝ F H}
    [ChartedSpace H N]
    (f : Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) → N) :
    letI := completionChartedSpace hδ C hemb hboundary hzero
    ContMDiff 𝓘(ℝ, Model (k + 1)) J ∞ f ↔
      ContMDiff 𝓘(ℝ, Model (k + 1)) J ∞
        (f ∘ interiorIn (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)) ∧
      ContMDiff 𝓘(ℝ, Model (k + 1)) J ∞
        (f ∘ cylinder (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)) := by
  let := completionChartedSpace hδ C hemb hboundary hzero
  constructor
  · intro hf
    exact ⟨hf.comp (contMDiff_completionInterior hδ C hemb hC hboundary hinv hzero),
      hf.comp (contMDiff_cylinder hδ C hemb hC hboundary hinv hzero)⟩
  · rintro ⟨hi, hc⟩ x
    rcases interior_cylinder_cover hδ
        (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) (fun b => hzero b) x with
      ⟨u, rfl⟩ | ⟨p, rfl⟩
    · obtain ⟨g, hg, hgu, heq⟩ :=
        completionInterior_inverse_germ hδ C hemb hC hboundary hinv hzero u
      apply ((hi u).comp_of_eq hg hgu).congr_of_eventuallyEq
      filter_upwards [heq] with z hz
      change f z = f (interiorIn (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) (g z))
      rw [hz]
    · obtain ⟨g, hg, hgp, heq⟩ :=
        cylinder_inverse_germ hδ C hemb hC hboundary hinv hzero p
      apply ((hc p).comp_of_eq hg hgp).congr_of_eventuallyEq
      filter_upwards [heq] with z hz
      change f z = f (cylinder (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) (g z))
      rw [hz]

end SingleSlice

section TotalSlice

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {δ : ℝ} (hδ : 0 < δ)
  (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (hemb : ∀ t, IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val))
  (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ (C t)
    (Half δ (IntrinsicBoundary.Point k M)))
  (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
  (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C t q) = q)
  (hzero : ∀ t (b : IntrinsicBoundary.Point k M), C t (0, b) = b.val)
  (hjoint : IsOpenEmbedding (totalCollar
    (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))

local instance totalSliceFullBandCharts : ChartedSpace (Model (k + 1))
    (Band δ (IntrinsicBoundary.Point k M)) := bandChartedSpace δ

local instance totalSliceFullBandSmooth : IsManifold 𝓘(ℝ, Model (k + 1)) ∞
    (Band δ (IntrinsicBoundary.Point k M)) := band_isManifold δ

include hC hinv

/-- The canonical slice map is smooth from the already constructed original
completion atlas to the original total atlas, including endpoint slices. -/
theorem contMDiff_sliceIn (hmix : HasRealMixedGerms (δ := δ) C) (t : Parameter) :
    letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiff 𝓘(ℝ, Model (k + 1)) (familyModel (k + 1)) ∞
      (sliceIn (fun a (p : Half δ (IntrinsicBoundary.Point k M)) => C a p.val) t) := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  apply (contMDiff_completion_iff hδ (C t) (hemb t) (hC t) (hboundary t) (hinv t) (hzero t) _).mpr
  constructor
  · have h := (contMDiff_totalInterior hδ C hboundary hzero hjoint hmix).comp
      ((contMDiff_const (c := t)).prodMk (contMDiff_id : ContMDiff 𝓘(ℝ, Model (k + 1))
        𝓘(ℝ, Model (k + 1)) ∞ (id : IntrinsicInterior.Point k M → IntrinsicInterior.Point k M)))
    simpa only [Function.comp_def, interiorIn, totalInterior, sliceIn_original, id_eq] using h
  · have h := (contMDiff_totalCylinder hδ C hboundary hzero hjoint hmix).comp
      ((contMDiff_const (c := t)).prodMk (contMDiff_id : ContMDiff 𝓘(ℝ, Model (k + 1))
        𝓘(ℝ, Model (k + 1)) ∞ (id : Band δ (IntrinsicBoundary.Point k M) → Band δ (IntrinsicBoundary.Point k M))))
    simpa only [Function.comp_def, sliceIn_cylinder, id_eq] using h

/-- Near each original slice point there is an actual smooth map from
the total family to the old slice atlas that inverts inclusion on that
parameter fiber. The formula comes from one original open patch. -/
theorem exists_sliceIn_local_retraction (hmix : HasRealMixedGerms (δ := δ) C)
    (t : Parameter)
    (x : Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val)) :
    letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ∃ r : TotalSpace (fun a (p : Half δ (IntrinsicBoundary.Point k M)) => C a p.val) →
      Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val),
      ContMDiffAt (familyModel (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ r
        (sliceIn (fun a p => C a p.val) t x) ∧
      r (sliceIn (fun a p => C a p.val) t x) = x ∧
      ∀ᶠ z in 𝓝 (sliceIn (fun a p => C a p.val) t x),
        parameter (fun a p => C a p.val) z = t →
          sliceIn (fun a p => C a p.val) t (r z) = z := by
  let := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let := totalFamily_isManifold hδ C hboundary hzero hjoint hmix
  let c := fun a (p : Half δ (IntrinsicBoundary.Point k M)) => C a p.val
  rcases interior_cylinder_cover hδ (c t) (fun b => hzero t b) x with
    ⟨u, rfl⟩ | ⟨p, rfl⟩
  · have hj := isOpenEmbedding_totalInterior hδ c (fun a b => hzero a b) hjoint
    obtain ⟨g, hg, hgu, heq⟩ := corner_patch_inverse_germ hj (t, u)
      (IsManifold.subset_maximalAtlas (I := familyModel (k + 1)) (n := ∞)
        (Or.inl ⟨chartAt _ (t, u), chart_mem_atlas _ (t, u), rfl⟩))
    have hanchor : sliceIn c t (interiorIn (c t) u) = totalInterior c (t, u) :=
      sliceIn_original c t u.val
    let r := interiorIn (c t) ∘ Prod.snd ∘ g
    refine ⟨r, ?_, ?_, ?_⟩
    · rw [hanchor]
      exact (contMDiff_completionInterior hδ (C t) (hemb t) (hC t) (hboundary t)
        (hinv t) (hzero t)).contMDiffAt.comp _ (contMDiffAt_snd.comp _ hg)
    · rw [hanchor]
      change interiorIn (c t) (g (totalInterior c (t, u))).2 = interiorIn (c t) u
      rw [hgu]
    · rw [hanchor]
      filter_upwards [heq] with z hz
      intro ht
      have hp : (g z).1 = t := by
        have h := congrArg (parameter c) hz
        change (g z).1 = parameter c z at h
        exact h.trans ht
      have he : (t, (g z).2) = g z := Prod.ext hp.symm rfl
      change sliceIn c t (interiorIn (c t) (g z).2) = z
      rw [interiorIn, sliceIn_original]
      change totalInterior c (t, (g z).2) = z
      rw [he]
      exact hz
  · have hj := isOpenEmbedding_totalCylinder c hjoint
    obtain ⟨g, hg, hgp, heq⟩ := corner_patch_inverse_germ hj (t, p)
      (IsManifold.subset_maximalAtlas (I := familyModel (k + 1)) (n := ∞)
        (Or.inr ⟨chartAt _ (t, p), chart_mem_atlas _ (t, p), rfl⟩))
    have hanchor : sliceIn c t (cylinder (c t) p) = totalCylinder c (t, p) :=
      sliceIn_cylinder c t p
    let r := cylinder (c t) ∘ Prod.snd ∘ g
    refine ⟨r, ?_, ?_, ?_⟩
    · rw [hanchor]
      exact (contMDiff_cylinder hδ (C t) (hemb t) (hC t) (hboundary t)
        (hinv t) (hzero t)).contMDiffAt.comp _ (contMDiffAt_snd.comp _ hg)
    · rw [hanchor]
      change cylinder (c t) (g (totalCylinder c (t, p))).2 = cylinder (c t) p
      rw [hgp]
    · rw [hanchor]
      filter_upwards [heq] with z hz
      intro ht
      have hp : (g z).1 = t := by
        have h := congrArg (parameter c) hz
        rw [parameter_totalCylinder] at h
        exact h.trans ht
      have he : (t, (g z).2) = g z := Prod.ext hp.symm rfl
      change sliceIn c t (cylinder (c t) (g z).2) = z
      rw [sliceIn_cylinder, he]
      exact hz

/-- Local smoothness into the original slice atlas is equivalent to
smoothness after its canonical inclusion in the total family. -/
theorem contMDiffAt_sliceIn_comp_iff (hmix : HasRealMixedGerms (δ := δ) C) (t : Parameter)
    {F H N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace N] {J : ModelWithCorners ℝ F H}
    [ChartedSpace H N]
    (f : N → Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val)) (y : N) :
    letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiffAt J 𝓘(ℝ, Model (k + 1)) ∞ f y ↔
      ContMDiffAt J (familyModel (k + 1)) ∞
        (sliceIn (fun a (p : Half δ (IntrinsicBoundary.Point k M)) => C a p.val) t ∘ f) y := by
  let := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
  let := totalFamilyChartedSpace hδ C hzero hjoint
  constructor
  · intro hf
    exact (contMDiff_sliceIn hδ C hemb hC hboundary hinv hzero hjoint hmix t).contMDiffAt.comp y hf
  · intro hf
    obtain ⟨r, hr, hrx, heq⟩ :=
      exists_sliceIn_local_retraction hδ C hemb hC hboundary hinv hzero hjoint hmix t (f y)
    apply (hr.comp y hf).congr_of_eventuallyEq
    have hn := hf.continuousAt.eventually heq
    filter_upwards [hn] with z hz
    apply sliceIn_injective (fun a (p : Half δ (IntrinsicBoundary.Point k M)) => C a p.val) t
    exact (hz (parameter_sliceIn
      (fun a (p : Half δ (IntrinsicBoundary.Point k M)) => C a p.val) t (f z))).symm

/-- Jointly defined maps into the established slice atlas are smooth
exactly when their canonical total-space inclusion is smooth. -/
theorem contMDiff_sliceIn_comp_iff (hmix : HasRealMixedGerms (δ := δ) C) (t : Parameter)
    {F H N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace N] {J : ModelWithCorners ℝ F H}
    [ChartedSpace H N]
    (f : N → Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val)) :
    letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiff J 𝓘(ℝ, Model (k + 1)) ∞ f ↔
      ContMDiff J (familyModel (k + 1)) ∞
        (sliceIn (fun a (p : Half δ (IntrinsicBoundary.Point k M)) => C a p.val) t ∘ f) := by
  let := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
  let := totalFamilyChartedSpace hδ C hzero hjoint
  constructor
  · intro hf y
    exact (contMDiffAt_sliceIn_comp_iff hδ C hemb hC hboundary hinv hzero hjoint hmix t f y).mp (hf y)
  · intro hf y
    exact (contMDiffAt_sliceIn_comp_iff hδ C hemb hC hboundary hinv hzero hjoint hmix t f y).mpr (hf y)

/-- The canonical slice inclusion has injective actual differential,
including at the two parameter endpoints. Its left inverse is the
derived local smooth retraction to the original slice atlas. -/
theorem injective_mfderiv_sliceIn (hmix : HasRealMixedGerms (δ := δ) C) (t : Parameter)
    (x : Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val)) :
    letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    Function.Injective (mfderiv 𝓘(ℝ, Model (k + 1)) (familyModel (k + 1))
      (sliceIn (fun a (p : Half δ (IntrinsicBoundary.Point k M)) => C a p.val) t) x) := by
  let := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let c := fun a (p : Half δ (IntrinsicBoundary.Point k M)) => C a p.val
  let j := sliceIn c t
  obtain ⟨r, hr, hrx, heq⟩ :=
    exists_sliceIn_local_retraction hδ C hemb hC hboundary hinv hzero hjoint hmix t x
  have hleft : r ∘ j =ᶠ[𝓝 x] id := by
    have hn := (continuous_sliceIn c t).continuousAt.eventually heq
    filter_upwards [hn] with y hy
    apply sliceIn_injective c t
    exact hy (parameter_sliceIn c t y)
  have hd := mfderiv_comp x (hr.mdifferentiableAt (by simp))
    ((contMDiff_sliceIn hδ C hemb hC hboundary hinv hzero hjoint hmix t).mdifferentiableAt (by simp))
  have hid : mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) (r ∘ j) x =
      ContinuousLinearMap.id ℝ _ := by
    exact hleft.mfderiv_eq.trans (by rw [mfderiv_id]; rfl)
  rw [hid] at hd
  intro v w hvw
  have heval (a : TangentSpace 𝓘(ℝ, Model (k + 1)) x) := congrArg (fun A => A a) hd
  exact (heval v).trans ((congrArg
    (mfderiv (familyModel (k + 1)) 𝓘(ℝ, Model (k + 1)) r (j x)) hvw).trans (heval w).symm)

end TotalSlice

end FsFltz.Geometry.IntrinsicCompletionGluing
