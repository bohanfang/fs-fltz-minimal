import FsFltz.Geometry.IntrinsicNativeCompletionWholeCanonicalBundle
import FsFltz.Geometry.OriginalRetainedCanonicalChart

/-!
# The actual canonical-square bundle on a retained parameter base

Source: `geoemtric-part-fsf.tex`, smooth-extension convention, lines 119–122;
`def:maslov`, lines 212–244; and `sec:lean`, lines 788–814.
Only the original parameters in the relative-open retained base carry complex
laws and complex-field germs. Restricting the independently constructed native
coframe atlas gives a smooth complex line bundle on that open part of the
actual completed total family. No section is used to construct this bundle.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Topology Bundle

namespace FsFltz.Geometry

section Restriction

variable {A : Type*} [TopologicalSpace A] {E : A → Type*}
  [∀ x, AddCommMonoid (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, TopologicalSpace (E x)]

/-- Restrict actual fiber coordinates to a subtype of their base. -/
def subtypeCanonicalPretrivialization (U : Set A)
    (e : Pretrivialization ℂ (π ℂ E)) :
    Pretrivialization ℂ (π ℂ (fun x : U => E x.val)) where
  toFun z := (z.proj, (e ⟨z.proj.val, z.snd⟩).2)
  invFun y := ⟨y.1, e.symm y.1.val y.2⟩
  source := (π ℂ (fun x : U => E x.val)) ⁻¹' (Subtype.val ⁻¹' e.baseSet)
  target := (Subtype.val ⁻¹' e.baseSet) ×ˢ univ
  map_source' z hz := ⟨hz, mem_univ _⟩
  map_target' y hy := hy.1
  left_inv' z hz := by
    rcases z with ⟨x, v⟩
    change x.val ∈ e.baseSet at hz
    simp only [e.symm_apply_apply_mk hz]
  right_inv' y hy := by
    have h := congrArg Prod.snd (e.apply_mk_symm hy.1 y.2)
    exact Prod.ext rfl h
  open_target := (e.open_baseSet.preimage continuous_subtype_val).prod isOpen_univ
  baseSet := Subtype.val ⁻¹' e.baseSet
  open_baseSet := e.open_baseSet.preimage continuous_subtype_val
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

omit [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)] in
@[simp] theorem subtypeCanonicalPretrivialization_apply (U : Set A)
    (e : Pretrivialization ℂ (π ℂ E)) (x : U) (v : E x.val) :
    subtypeCanonicalPretrivialization U e ⟨x, v⟩ = (x, (e ⟨x.val, v⟩).2) := rfl

instance subtypeCanonicalPretrivialization_linear (R : Type*) [Semiring R]
    [Module R ℂ] [∀ x, Module R (E x)] (U : Set A)
    (e : Pretrivialization ℂ (π ℂ E)) [e.IsLinear R] :
    (subtypeCanonicalPretrivialization U e).IsLinear R where
  linear _ hx := e.linear R hx

omit [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)] in
theorem subtypeCanonicalPretrivialization_symm (U : Set A)
    (e : Pretrivialization ℂ (π ℂ E)) {x : U}
    (hx : x.val ∈ e.baseSet) (q : ℂ) :
    (subtypeCanonicalPretrivialization U e).symm x q = e.symm x.val q := by
  have h := congrArg Prod.snd
    ((subtypeCanonicalPretrivialization U e).apply_mk_symm hx q)
  change (e ⟨x.val, (subtypeCanonicalPretrivialization U e).symm x q⟩).2 = q at h
  have h' := e.symm_apply_apply_mk hx
    ((subtypeCanonicalPretrivialization U e).symm x q)
  rw [h] at h'
  exact h'.symm

omit [∀ x, Module ℂ (E x)] in
theorem subtypeCanonicalPretrivialization_isInducing (U : Set A)
    (e : Pretrivialization ℂ (π ℂ E)) {x : U} (hx : x.val ∈ e.baseSet)
    (he : IsInducing (e ∘ Bundle.TotalSpace.mk x.val)) :
    IsInducing (subtypeCanonicalPretrivialization U e ∘ Bundle.TotalSpace.mk x) := by
  have hc : Continuous (subtypeCanonicalPretrivialization U e ∘ Bundle.TotalSpace.mk x) :=
    continuous_const.prodMk (continuous_snd.comp he.continuous)
  have hcomp : (Prod.map Subtype.val id) ∘ subtypeCanonicalPretrivialization U e ∘
      Bundle.TotalSpace.mk x = e ∘ Bundle.TotalSpace.mk x.val := by
    funext v
    exact e.mk_proj_snd' (x := ⟨x.val, v⟩) hx
  apply IsInducing.of_comp hc (continuous_subtype_val.prodMap continuous_id)
  rwa [hcomp]

end Restriction

namespace IntrinsicCompletionGluing

variable {k n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] {δ : ℝ}
  (hδ : 0 < δ)
  (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (hemb : ∀ t, IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val))
  (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
  (hzero : ∀ t b, C t (0, b) = b.val)
  (hjoint : IsOpenEmbedding (totalCollar
    (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
  (J : ∀ s : Parameter, Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
    Model (k + 1) →L[ℝ] Model (k + 1))
  (N : Model (2 * n) ≃L[ℝ] Model (k + 1))
  (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ (C t)
    (Half δ (IntrinsicBoundary.Point k M)))
  (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C t q) = q)
  (B : Set Parameter) (hB : IsOpen B)

/-- The retained open part of the actual completion, including its full end. -/
abbrev originalRetainedCanonicalBase : TopologicalSpace.Opens
    (TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) :=
  ⟨parameter (fun t p => C t p.val) ⁻¹' B,
    hB.preimage (continuous_parameter (fun t p => C t p.val))⟩

/-- Literal canonical-square fibers over the retained actual base. -/
abbrev OriginalRetainedCanonicalTensorSquare
    (x : originalRetainedCanonicalBase (δ := δ) C B hB) :=
  OriginalTotalCanonicalTensorSquare C J N x.val

/-- Restriction of an original tensor chart; the tensor coordinate is unchanged. -/
def originalRetainedCanonicalTensorPretrivialization
    (c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    Pretrivialization ℂ (π ℂ (OriginalRetainedCanonicalTensorSquare C J N B hB)) :=
  subtypeCanonicalPretrivialization (originalRetainedCanonicalBase (δ := δ) C B hB : Set _)
    (originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv c)

/-- Restriction preserves the literal promoted native tensor coordinate. -/
theorem originalRetainedCanonicalTensorPretrivialization_apply
    (c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (x : originalRetainedCanonicalBase (δ := δ) C B hB)
    (v : OriginalRetainedCanonicalTensorSquare C J N B hB x) :
    originalRetainedCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv B hB c ⟨x, v⟩ =
      (x, (originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv c ⟨x.val, v⟩).2) := rfl

instance originalRetainedCanonicalTensorPretrivialization_complexLinear
    (c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    (originalRetainedCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv B hB c).IsLinear ℂ := by
  constructor
  intro x hx
  change IsLinearMap ℂ (fun v =>
    (originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv c ⟨x.val, v⟩).2)
  cases c <;> dsimp only [originalTotalCanonicalTensorPretrivialization] at *
  · exact Pretrivialization.linear ℂ _ hx
  · exact Pretrivialization.linear ℂ _ hx

instance originalRetainedCanonicalTensorPretrivialization_realLinear
    (c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    (originalRetainedCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv B hB c).IsLinear ℝ := by
  constructor
  intro x hx
  change IsLinearMap ℝ (fun v =>
    (originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv c ⟨x.val, v⟩).2)
  cases c <;> dsimp only [originalTotalCanonicalTensorPretrivialization] at *
  · exact Pretrivialization.linear ℝ _ hx
  · exact Pretrivialization.linear ℝ _ hx

variable (P : Model (2 * n) ≃L[ℝ] (Model k × ℝ))
  (hJI : HasOriginalInteriorComplexExtensionsOn hδ C hemb hboundary hzero J B)
  (hJE : HasOriginalEndComplexExtensionsOn hδ C hemb hboundary hzero J B)
  (hJsq : ∀ s ∈ B, ∀ x v, J s x (J s x v) = -v)

local instance retainedBundleEndCharts :
    ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ

include N hC hinv P hB hJI hJE hJsq in
/-- The retained cover is produced from the raw complex-field germs only. -/
theorem exists_originalRetainedCanonicalChart
    (x : originalRetainedCanonicalBase (δ := δ) C B hB) :
    ∃ c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n),
      x ∈ (originalRetainedCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv B hB c).baseSet := by
  rcases totalInterior_cylinder_cover hδ (fun t p => C t p.val) hzero x.val with
    ⟨p, hp⟩ | ⟨p, hp⟩
  · have ht : p.1 ∈ B := by
      have h := x.property
      change parameter (fun t p => C t p.val) x.val ∈ B at h
      rw [← hp] at h
      exact h
    have hw := mem_chart_source (Model (k + 1)) p.2
    obtain ⟨U, K, hpU, hK, heK⟩ := hJI p.1 ht p.2 p.2 hw
    obtain ⟨c, _, hpc, _⟩ := exists_originalInteriorCanonicalChart_on hδ C hemb hboundary
      hzero J hC hinv B hB hJsq N p.2 p.1 ht p.2 hw U K hpU hK heK
    exact ⟨.inl c, p, hpc, hp⟩
  · have ht : p.1 ∈ B := by
      have h := x.property
      change parameter (fun t p => C t p.val) x.val ∈ B at h
      rw [← hp] at h
      exact h
    let u := endBandCoordinates p.2
    have hw := mem_chart_source (Model k × ℝ) u
    obtain ⟨U, K, hpU, hK, heK⟩ := hJE p.1 ht u p.2 hw
    obtain ⟨c, _, hpc, _⟩ := exists_originalEndCanonicalChart_on hδ C hemb hboundary
      hzero J hC hinv B hB hJsq P u p.1 ht p.2 hw U K hpU hK heK
    exact ⟨.inr c, p, hpc, hp⟩

/-- The retained atlas chooses a chart using only the retained field germs. -/
def originalRetainedCanonicalChartAt
    (x : originalRetainedCanonicalBase (δ := δ) C B hB) :=
  (exists_originalRetainedCanonicalChart hδ C hemb hboundary hzero hjoint J N hC hinv
    B hB P hJI hJE hJsq x).choose

theorem mem_originalRetainedCanonicalChartAt
    (x : originalRetainedCanonicalBase (δ := δ) C B hB) :
    x ∈ (originalRetainedCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv B hB
      (originalRetainedCanonicalChartAt hδ C hemb hboundary hzero hjoint J N hC hinv B hB P hJI hJE hJsq x)).baseSet :=
  (exists_originalRetainedCanonicalChart hδ C hemb hboundary hzero hjoint J N hC hinv
    B hB P hJI hJE hJsq x).choose_spec

variable (hmix : HasRealMixedGerms (δ := δ) C)

/-- Actual retained changes of tensor coordinates are the same native changes. -/
theorem originalRetainedCanonicalTransitionMap_apply
    (c d : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n))
    {x : originalRetainedCanonicalBase (δ := δ) C B hB}
    (hx : x ∈ (originalRetainedCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv B hB c).baseSet ∩
      (originalRetainedCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv B hB d).baseSet)
    (q : ℂ) :
    originalTotalCanonicalTransitionMap hδ C hemb hboundary hzero J N c d x.val q =
      (originalRetainedCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv B hB d
        ⟨x, (originalRetainedCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv B hB c).symm x q⟩).2 := by
  change _ = (originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv d
    ⟨x.val, (subtypeCanonicalPretrivialization _ _).symm x q⟩).2
  rw [subtypeCanonicalPretrivialization_symm _ _ hx.1]
  exact originalTotalCanonicalTransitionMap_apply hδ C hemb hboundary hzero hjoint J N hC hinv c d hx q

include hmix P in
/-- Restriction preserves the already proved smooth overlap maps. -/
theorem contMDiffOn_originalRetainedCanonicalTransitionMap
    (c d : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiffOn (familyModel (k + 1)) 𝓘(ℝ, ℂ →L[ℝ] ℂ) ∞
      (fun x : originalRetainedCanonicalBase (δ := δ) C B hB =>
        originalTotalCanonicalTransitionMap hδ C hemb hboundary hzero J N c d x.val)
      ((originalRetainedCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv B hB c).baseSet ∩
        (originalRetainedCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv B hB d).baseSet) := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  exact (contMDiffOn_originalTotalCanonicalTransitionMap hδ C hemb hboundary hzero hjoint J N hC hinv hmix P c d).comp
    contMDiff_subtype_val.contMDiffOn (fun _ hx => hx)

/-- An actual canonical-square prebundle on the retained original completion.
Neither chart coverage nor overlap regularity depends on a section. -/
def originalRetainedCanonicalTensorSquareVectorPrebundle :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    VectorPrebundle ℝ ℂ (OriginalRetainedCanonicalTensorSquare C J N B hB) := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  exact {
    pretrivializationAtlas := Set.range (originalRetainedCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv B hB)
    pretrivialization_linear' := by
      rintro _ ⟨c, rfl⟩
      infer_instance
    pretrivializationAt := fun x =>
      originalRetainedCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv B hB
        (originalRetainedCanonicalChartAt hδ C hemb hboundary hzero hjoint J N hC hinv B hB P hJI hJE hJsq x)
    mem_base_pretrivializationAt :=
      mem_originalRetainedCanonicalChartAt hδ C hemb hboundary hzero hjoint J N hC hinv B hB P hJI hJE hJsq
    pretrivialization_mem_atlas := fun _ => ⟨_, rfl⟩
    exists_coordChange := by
      rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
      exact ⟨fun x => originalTotalCanonicalTransitionMap hδ C hemb hboundary hzero J N c d x.val,
        (contMDiffOn_originalRetainedCanonicalTransitionMap hδ C hemb hboundary hzero hjoint J N hC hinv B hB P hmix c d).continuousOn,
        fun _ hx q => originalRetainedCanonicalTransitionMap_apply hδ C hemb hboundary hzero hjoint J N hC hinv B hB c d hx q⟩
    totalSpaceMk_isInducing := by
      intro x
      have hx := mem_originalRetainedCanonicalChartAt hδ C hemb hboundary hzero hjoint J N hC hinv B hB P hJI hJE hJsq x
      apply subtypeCanonicalPretrivialization_isInducing _ _ hx
      cases h : originalRetainedCanonicalChartAt hδ C hemb hboundary hzero hjoint J N hC hinv B hB P hJI hJE hJsq x with
      | inl c =>
        rw [h] at hx
        exact c.totalTensorPretrivialization_isInducing N hjoint hC hinv hx
      | inr c =>
        rw [h] at hx
        exact c.totalTensorPretrivialization_isInducing N hjoint hC hinv hx }

instance originalRetainedCanonicalTensorSquareVectorPrebundle_isContMDiff :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    (originalRetainedCanonicalTensorSquareVectorPrebundle hδ C hemb hboundary hzero hjoint J N hC hinv B hB P hJI hJE hJsq hmix).IsContMDiff
      (familyModel (k + 1)) ∞ := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  exact {
    exists_contMDiffCoordChange := by
      rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
      exact ⟨fun x => originalTotalCanonicalTransitionMap hδ C hemb hboundary hzero J N c d x.val,
        contMDiffOn_originalRetainedCanonicalTransitionMap hδ C hemb hboundary hzero hjoint J N hC hinv B hB P hmix c d,
        fun _ hx q => originalRetainedCanonicalTransitionMap_apply hδ C hemb hboundary hzero hjoint J N hC hinv B hB c d hx q⟩ }

/-- The actual retained canonical tensor square is a smooth real vector bundle. -/
theorem originalRetainedCanonicalTensorSquareVectorBundle_smooth :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    let a := originalRetainedCanonicalTensorSquareVectorPrebundle hδ C hemb hboundary hzero hjoint J N hC hinv B hB P hJI hJE hJsq hmix
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    letI := a.toVectorBundle
    ContMDiffVectorBundle ∞ ℂ (OriginalRetainedCanonicalTensorSquare C J N B hB) (familyModel (k + 1)) := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  exact (originalRetainedCanonicalTensorSquareVectorPrebundle hδ C hemb hboundary hzero hjoint J N hC hinv B hB P hJI hJE hJsq hmix).contMDiffVectorBundle _

include N hjoint hC hinv P hB hJI hJE hJsq in
/-- Each retained fiber is a complex line; no complex law is imposed elsewhere. -/
theorem originalRetainedCanonicalTensorSquare_finrank
    (x : originalRetainedCanonicalBase (δ := δ) C B hB) :
    Module.finrank ℂ (OriginalRetainedCanonicalTensorSquare C J N B hB x) = 1 := by
  obtain ⟨c, hc⟩ := exists_originalRetainedCanonicalChart hδ C hemb hboundary hzero hjoint J N hC hinv B hB P hJI hJE hJsq x
  rw [((originalRetainedCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv B hB c).linearEquivAt ℂ x hc).finrank_eq]
  exact Module.finrank_self ℂ

/-- The same retained smooth atlas is complex linear, so it gives a complex
vector bundle with the literal canonical-square fibers. -/
theorem originalRetainedCanonicalTensorSquareVectorBundle_complex :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    let a := originalRetainedCanonicalTensorSquareVectorPrebundle hδ C hemb hboundary hzero hjoint J N hC hinv B hB P hJI hJE hJsq hmix
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    VectorBundle ℂ ℂ (OriginalRetainedCanonicalTensorSquare C J N B hB) := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let a := originalRetainedCanonicalTensorSquareVectorPrebundle hδ C hemb hboundary hzero hjoint J N hC hinv B hB P hJI hJE hJsq hmix
  let := a.totalSpaceTopology
  let := a.toFiberBundle
  refine ⟨?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    obtain ⟨c, rfl⟩ := he
    have hlin : (originalRetainedCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv B hB c).IsLinear ℂ := inferInstance
    exact ⟨fun _ hx => hlin.linear _ hx⟩
  · rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    obtain ⟨c, rfl⟩ := he
    obtain ⟨d, rfl⟩ := he'
    let L : ℂ →L[ℂ] (ℂ →L[ℂ] ℂ) :=
      ContinuousLinearMap.toSpanSingleton ℂ (ContinuousLinearMap.id ℂ ℂ)
    have hc : ContinuousOn (fun x : originalRetainedCanonicalBase (δ := δ) C B hB =>
        L (originalTotalCanonicalTransition hδ C hemb hboundary hzero J N c d x.val))
        ((originalRetainedCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv B hB c).baseSet ∩
          (originalRetainedCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv B hB d).baseSet) :=
      L.continuous.comp_continuousOn
        ((contMDiffOn_originalTotalCanonicalTransition hδ C hemb hboundary hzero hjoint J N hC hinv hmix P c d).continuousOn.comp
          continuous_subtype_val.continuousOn (fun _ hx => hx))
    apply hc.congr
    intro x hx
    apply ContinuousLinearMap.ext
    intro q
    simp only [ContinuousLinearEquiv.coe_coe]
    rw [Trivialization.coordChangeL_apply]
    · exact (originalRetainedCanonicalTransitionMap_apply hδ C hemb hboundary hzero hjoint J N hC hinv B hB c d hx q).symm
    · exact hx

end IntrinsicCompletionGluing
end FsFltz.Geometry
