import FsFltz.Geometry.IntrinsicNativeCompletionWholeCanonicalCoordinates
import FsFltz.Geometry.IntrinsicNativeCompletionGlobalMixedTransition

/-!
# The canonical-square bundle on the original completed total family

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–232, and
`sec:lean`, lines 788–814. The atlas is the union of the original interior
and full-cylinder canonical coframe charts promoted through the actual
original inclusions. Mixed coordinate changes are proved from the original
real collar germs, before any canonical-square section is selected.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Topology Bundle

namespace FsFltz.Geometry.IntrinsicCompletionGluing

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

variable {hδ C hemb hboundary hzero J}

/-- Actual promoted tensor coordinates have exactly the produced mixed
scalar transition. The proof uses the full natural tensor reconstruction. -/
theorem originalTotalInteriorToEnd_tensorTransition
    (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    {x : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)}
    (hx : x ∈ c.totalBaseDomain ∩ d.totalBaseDomain) (q : ℂ) :
    (d.totalTensorPretrivialization N hjoint hC hinv
      ⟨x, (c.totalTensorPretrivialization N hjoint hC hinv).symm x q⟩).2 =
        originalEndToInteriorCanonicalTransition hδ C hemb hboundary hzero J N c d x * q := by
  rcases hx.1 with ⟨p, hp, rfl⟩
  rcases hx.2 with ⟨r, hr, he⟩
  let τ := (c.totalTensorPretrivialization N hjoint hC hinv).symm
    (totalInterior (fun t p => C t p.val) p) q
  have hq : (c.totalTensorPretrivialization N hjoint hC hinv
      ⟨totalInterior (fun t p => C t p.val) p, τ⟩).2 = q :=
    congrArg Prod.snd ((c.totalTensorPretrivialization N hjoint hC hinv).apply_mk_symm
      (show totalInterior (fun t p => C t p.val) p ∈ c.totalBaseDomain from ⟨p, hp, rfl⟩) q)
  have hτ := c.totalTensorPretrivialization_reconstruction N hjoint hC hinv hp τ
  rw [hq] at hτ
  rw [d.totalTensorPretrivialization_coefficient_at N hjoint hC hinv hr he, hτ,
    originalEndToInteriorCanonicalTransition_apply hδ C hemb hboundary hzero hjoint J N c d p r he.symm]
  change q * squaredCoframeCoefficient (d.nativeCoframe N r)
    (coframeSquaredGenerator (c.nativeCoframe N p)) = _
  exact mul_comm _ _

/-- The reverse mixed tensor change uses the same actual fiber and keeps
the spatial collar derivative already present in the native coframes. -/
theorem originalTotalEndToInterior_tensorTransition
    (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    {x : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)}
    (hx : x ∈ c.totalBaseDomain ∩ d.totalBaseDomain) (q : ℂ) :
    (c.totalTensorPretrivialization N hjoint hC hinv
      ⟨x, (d.totalTensorPretrivialization N hjoint hC hinv).symm x q⟩).2 =
        originalInteriorToEndCanonicalTransition hδ C hemb hboundary hzero J N c d x * q := by
  rcases hx.2 with ⟨r, hr, rfl⟩
  rcases hx.1 with ⟨p, hp, he⟩
  let τ := (d.totalTensorPretrivialization N hjoint hC hinv).symm
    (totalCylinder (fun t p => C t p.val) r) q
  have hq : (d.totalTensorPretrivialization N hjoint hC hinv
      ⟨totalCylinder (fun t p => C t p.val) r, τ⟩).2 = q :=
    congrArg Prod.snd ((d.totalTensorPretrivialization N hjoint hC hinv).apply_mk_symm
      (show totalCylinder (fun t p => C t p.val) r ∈ d.totalBaseDomain from ⟨r, hr, rfl⟩) q)
  have hτ := d.totalTensorPretrivialization_reconstruction N hjoint hC hinv hr τ
  rw [hq] at hτ
  rw [c.totalTensorPretrivialization_coefficient_at N hjoint hC hinv hp he, hτ]
  have hs := originalInteriorToEndCanonicalTransition_apply hδ C hemb hboundary hzero hjoint J N c d p r he
  rw [he] at hs
  rw [hs]
  change q * squaredCoframeCoefficient (c.nativeCoframe N p)
    (coframeSquaredGenerator (d.nativeCoframe N r)) = _
  exact mul_comm _ _

theorem originalTotalInterior_tensorTransition
    (c d : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    {x : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)}
    (hx : x ∈ c.totalBaseDomain ∩ d.totalBaseDomain) (q : ℂ) :
    (d.totalTensorPretrivialization N hjoint hC hinv
      ⟨x, (c.totalTensorPretrivialization N hjoint hC hinv).symm x q⟩).2 =
        originalInteriorCanonicalTransition hδ C hemb hboundary hzero J N c d x * q := by
  rcases hx.1 with ⟨p, hp, rfl⟩
  rcases hx.2 with ⟨r, hr, he⟩
  have hrp := (isOpenEmbedding_totalInterior hδ (fun t p => C t p.val) hzero hjoint).injective he
  subst r
  let τ := (c.totalTensorPretrivialization N hjoint hC hinv).symm
    (totalInterior (fun t p => C t p.val) p) q
  have hq : (c.totalTensorPretrivialization N hjoint hC hinv
      ⟨totalInterior (fun t p => C t p.val) p, τ⟩).2 = q :=
    congrArg Prod.snd ((c.totalTensorPretrivialization N hjoint hC hinv).apply_mk_symm
      (show totalInterior (fun t p => C t p.val) p ∈ c.totalBaseDomain from ⟨p, hp, rfl⟩) q)
  have hτ := c.totalTensorPretrivialization_reconstruction N hjoint hC hinv hp τ
  rw [hq] at hτ
  rw [d.totalTensorPretrivialization_coefficient N hjoint hC hinv hr, hτ,
    originalInteriorCanonicalTransition_apply hδ C hemb hboundary hzero hjoint J N c d p]
  change q * squaredCoframeCoefficient (d.nativeCoframe N p)
    (coframeSquaredGenerator (c.nativeCoframe N p)) = _
  exact mul_comm _ _

theorem originalTotalEnd_tensorTransition
    (c d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    {x : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)}
    (hx : x ∈ c.totalBaseDomain ∩ d.totalBaseDomain) (q : ℂ) :
    (d.totalTensorPretrivialization N hjoint hC hinv
      ⟨x, (c.totalTensorPretrivialization N hjoint hC hinv).symm x q⟩).2 =
        originalEndCanonicalTransition hδ C hemb hboundary hzero J N c d x * q := by
  rcases hx.1 with ⟨p, hp, rfl⟩
  rcases hx.2 with ⟨r, hr, he⟩
  have hrp := (isOpenEmbedding_totalCylinder (fun t p => C t p.val) hjoint).injective he
  subst r
  let τ := (c.totalTensorPretrivialization N hjoint hC hinv).symm
    (totalCylinder (fun t p => C t p.val) p) q
  have hq : (c.totalTensorPretrivialization N hjoint hC hinv
      ⟨totalCylinder (fun t p => C t p.val) p, τ⟩).2 = q :=
    congrArg Prod.snd ((c.totalTensorPretrivialization N hjoint hC hinv).apply_mk_symm
      (show totalCylinder (fun t p => C t p.val) p ∈ c.totalBaseDomain from ⟨p, hp, rfl⟩) q)
  have hτ := c.totalTensorPretrivialization_reconstruction N hjoint hC hinv hp τ
  rw [hq] at hτ
  rw [d.totalTensorPretrivialization_coefficient N hjoint hC hinv hr, hτ,
    originalEndCanonicalTransition_apply hδ C hemb hboundary hzero hjoint J N c d p]
  change q * squaredCoframeCoefficient (d.nativeCoframe N p)
    (coframeSquaredGenerator (c.nativeCoframe N p)) = _
  exact mul_comm _ _

variable (hδ C hemb hboundary hzero J)

/-- All actual native coframe charts on the two original open patches. -/
abbrev OriginalTotalCanonicalChart :=
  Sum (OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))

/-- Both sorts of original chart belong to the same actual total bundle. -/
def originalTotalCanonicalTensorPretrivialization
    (c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    Pretrivialization ℂ (π ℂ (OriginalTotalCanonicalTensorSquare C J N)) :=
  match c with
  | .inl c => c.totalTensorPretrivialization N hjoint hC hinv
  | .inr c => c.totalTensorPretrivialization N hjoint hC hinv

def originalTotalCanonicalTransition
    (c d : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) → ℂ :=
  match c, d with
  | .inl c, .inl d => originalInteriorCanonicalTransition hδ C hemb hboundary hzero J N c d
  | .inl c, .inr d => originalEndToInteriorCanonicalTransition hδ C hemb hboundary hzero J N c d
  | .inr c, .inl d => originalInteriorToEndCanonicalTransition hδ C hemb hboundary hzero J N d c
  | .inr c, .inr d => originalEndCanonicalTransition hδ C hemb hboundary hzero J N c d

def originalTotalCanonicalTransitionMap
    (c d : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (x : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) :
    ℂ →L[ℝ] ℂ :=
  originalTotalCanonicalTransition hδ C hemb hboundary hzero J N c d x •
    ContinuousLinearMap.id ℝ ℂ

theorem originalTotalCanonicalTransitionMap_apply
    (c d : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n))
    {x : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)}
    (hx : x ∈ (originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv c).baseSet ∩
      (originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv d).baseSet)
    (q : ℂ) :
    originalTotalCanonicalTransitionMap hδ C hemb hboundary hzero J N c d x q =
      (originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv d
        ⟨x, (originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv c).symm x q⟩).2 := by
  cases c with
  | inl c =>
    cases d with
    | inl d => exact (originalTotalInterior_tensorTransition hjoint N hC hinv c d hx q).symm
    | inr d => exact (originalTotalInteriorToEnd_tensorTransition hjoint N hC hinv c d hx q).symm
  | inr c =>
    cases d with
    | inl d => exact (originalTotalEndToInterior_tensorTransition hjoint N hC hinv d c ⟨hx.2, hx.1⟩ q).symm
    | inr d => exact (originalTotalEnd_tensorTransition hjoint N hC hinv c d hx q).symm

variable (hmix : HasRealMixedGerms (δ := δ) C)
  (P : Model (2 * n) ≃L[ℝ] (Model k × ℝ))

include hC hinv hjoint hmix P in
theorem contMDiffOn_originalTotalCanonicalTransition
    (c d : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiffOn (familyModel (k + 1)) 𝓘(ℝ, ℂ) ∞
      (originalTotalCanonicalTransition hδ C hemb hboundary hzero J N c d)
      ((originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv c).baseSet ∩
        (originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv d).baseSet) := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  cases c with
  | inl c =>
    cases d with
    | inl d => exact contMDiffOn_originalInteriorCanonicalTransition hδ C hemb hC hboundary hinv hzero hjoint hmix J N c d
    | inr d => exact contMDiffOn_originalEndToInteriorCanonicalTransition hδ C hemb hC hboundary hinv hzero hjoint hmix J N P c d
  | inr c =>
    cases d with
    | inl d =>
      have h := contMDiffOn_originalInteriorToEndCanonicalTransition hδ C hemb hC hboundary hinv hzero hjoint hmix J N d c
      intro x hx
      exact (h x ⟨hx.2, hx.1⟩).mono (fun _ hy => ⟨hy.2, hy.1⟩)
    | inr d => exact contMDiffOn_originalEndCanonicalTransition hδ C hemb hC hboundary hinv hzero hjoint hmix J N P c d

include hC hinv hjoint hmix P in
theorem contMDiffOn_originalTotalCanonicalTransitionMap
    (c d : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiffOn (familyModel (k + 1)) 𝓘(ℝ, ℂ →L[ℝ] ℂ) ∞
      (originalTotalCanonicalTransitionMap hδ C hemb hboundary hzero J N c d)
      ((originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv c).baseSet ∩
        (originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv d).baseSet) := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let L : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) :=
    (ContinuousLinearMap.toSpanSingleton ℂ (ContinuousLinearMap.id ℝ ℂ)).restrictScalars ℝ
  exact L.contMDiff.comp_contMDiffOn
    (contMDiffOn_originalTotalCanonicalTransition hδ C hemb hboundary hzero hjoint J N hC hinv hmix P c d)

include hC hinv P in
theorem exists_originalTotalCanonicalChart
    (hJI : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
    (hJE : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (x : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) :
    ∃ c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n),
      x ∈ (originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv c).baseSet := by
  rcases totalInterior_cylinder_cover hδ (fun t p => C t p.val) hzero x with ⟨p, rfl⟩ | ⟨p, rfl⟩
  · let c := originalInteriorCanonicalChartAt hδ C hemb hboundary hzero J N hC hinv hJI hJsq p
    refine ⟨.inl c, p, ?_, rfl⟩
    exact mem_originalInteriorCanonicalChartAt hδ C hemb hboundary hzero J N hC hinv hJI hJsq p
  · let c := originalEndCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJE hJsq p
    refine ⟨.inr c, p, ?_, rfl⟩
    exact mem_originalEndCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJE hJsq p

/-- The coframe cover chooses coordinates on the actual completed total
space, using complex-field local extension data and no section. -/
def originalTotalCanonicalChartAt
    (hJI : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
    (hJE : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (x : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) :=
  (exists_originalTotalCanonicalChart hδ C hemb hboundary hzero hjoint J N hC hinv P hJI hJE hJsq x).choose

theorem mem_originalTotalCanonicalChartAt
    (hJI : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
    (hJE : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (x : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) :
    x ∈ (originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv
      (originalTotalCanonicalChartAt hδ C hemb hboundary hzero hjoint J N hC hinv P hJI hJE hJsq x)).baseSet :=
  (exists_originalTotalCanonicalChart hδ C hemb hboundary hzero hjoint J N hC hinv P hJI hJE hJsq x).choose_spec

/-- A canonical-square prebundle on the whole original completed total
family. Every overlap is proved smooth from actual coframes and real collar
germs. In particular mixed-overlap regularity is not an input field. -/
def originalTotalCanonicalTensorSquareVectorPrebundle
    (hJI : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
    (hJE : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    VectorPrebundle ℝ ℂ (OriginalTotalCanonicalTensorSquare C J N) := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  exact {
    pretrivializationAtlas := Set.range (originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv)
    pretrivialization_linear' := by
      rintro _ ⟨c, rfl⟩
      cases c <;> dsimp only [originalTotalCanonicalTensorPretrivialization] <;> infer_instance
    pretrivializationAt := fun x =>
      originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv
        (originalTotalCanonicalChartAt hδ C hemb hboundary hzero hjoint J N hC hinv P hJI hJE hJsq x)
    mem_base_pretrivializationAt :=
      mem_originalTotalCanonicalChartAt hδ C hemb hboundary hzero hjoint J N hC hinv P hJI hJE hJsq
    pretrivialization_mem_atlas := fun x => ⟨_, rfl⟩
    exists_coordChange := by
      rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
      exact ⟨originalTotalCanonicalTransitionMap hδ C hemb hboundary hzero J N c d,
        (contMDiffOn_originalTotalCanonicalTransitionMap hδ C hemb hboundary hzero hjoint J N hC hinv hmix P c d).continuousOn,
        fun _ hx q => originalTotalCanonicalTransitionMap_apply hδ C hemb hboundary hzero hjoint J N hC hinv c d hx q⟩
    totalSpaceMk_isInducing := by
      intro x
      have hx := mem_originalTotalCanonicalChartAt hδ C hemb hboundary hzero hjoint J N hC hinv P hJI hJE hJsq x
      cases h : originalTotalCanonicalChartAt hδ C hemb hboundary hzero hjoint J N hC hinv P hJI hJE hJsq x with
      | inl c =>
        rw [h] at hx
        exact c.totalTensorPretrivialization_isInducing N hjoint hC hinv hx
      | inr c =>
        rw [h] at hx
        exact c.totalTensorPretrivialization_isInducing N hjoint hC hinv hx }

instance originalTotalCanonicalTensorSquareVectorPrebundle_isContMDiff
    (hJI : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
    (hJE : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    (originalTotalCanonicalTensorSquareVectorPrebundle hδ C hemb hboundary hzero hjoint J N hC hinv hmix P hJI hJE hJsq).IsContMDiff
      (familyModel (k + 1)) ∞ := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  exact {
    exists_contMDiffCoordChange := by
      rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
      exact ⟨originalTotalCanonicalTransitionMap hδ C hemb hboundary hzero J N c d,
        contMDiffOn_originalTotalCanonicalTransitionMap hδ C hemb hboundary hzero hjoint J N hC hinv hmix P c d,
        fun _ hx q => originalTotalCanonicalTransitionMap_apply hδ C hemb hboundary hzero hjoint J N hC hinv c d hx q⟩ }

/-- The original completed family now carries an actual smooth tensor-square
vector bundle, before selecting a Maslov section. -/
theorem originalTotalCanonicalTensorSquareVectorBundle_smooth
    (hJI : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
    (hJE : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    let a := originalTotalCanonicalTensorSquareVectorPrebundle hδ C hemb hboundary hzero hjoint J N hC hinv hmix P hJI hJE hJsq
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    letI := a.toVectorBundle
    ContMDiffVectorBundle ∞ ℂ (OriginalTotalCanonicalTensorSquare C J N) (familyModel (k + 1)) := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  exact (originalTotalCanonicalTensorSquareVectorPrebundle hδ C hemb hboundary hzero hjoint J N hC hinv hmix P hJI hJE hJsq).contMDiffVectorBundle _

/-- The same independently constructed atlas also defines a complex vector
bundle: its charts and every transition preserve complex scalar multiplication. -/
theorem originalTotalCanonicalTensorSquareVectorBundle_complex
    (hJI : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
    (hJE : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    let a := originalTotalCanonicalTensorSquareVectorPrebundle hδ C hemb hboundary hzero hjoint J N hC hinv hmix P hJI hJE hJsq
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    VectorBundle ℂ ℂ (OriginalTotalCanonicalTensorSquare C J N) := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let a := originalTotalCanonicalTensorSquareVectorPrebundle hδ C hemb hboundary hzero hjoint J N hC hinv hmix P hJI hJE hJsq
  let := a.totalSpaceTopology
  let := a.toFiberBundle
  refine ⟨?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    obtain ⟨c, rfl⟩ := he
    have hlin : (originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv c).IsLinear ℂ := by
      cases c <;> dsimp only [originalTotalCanonicalTensorPretrivialization] <;> infer_instance
    exact ⟨fun x hx => hlin.linear x hx⟩
  · rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    obtain ⟨c, rfl⟩ := he
    obtain ⟨d, rfl⟩ := he'
    let L : ℂ →L[ℂ] (ℂ →L[ℂ] ℂ) :=
      ContinuousLinearMap.toSpanSingleton ℂ (ContinuousLinearMap.id ℂ ℂ)
    have hc : ContinuousOn (fun x => L (originalTotalCanonicalTransition hδ C hemb hboundary hzero J N c d x))
        ((originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv c).baseSet ∩
          (originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv d).baseSet) :=
      L.continuous.comp_continuousOn
        (contMDiffOn_originalTotalCanonicalTransition hδ C hemb hboundary hzero hjoint J N hC hinv hmix P c d).continuousOn
    apply hc.congr
    intro x hx
    apply ContinuousLinearMap.ext
    intro q
    simp only [ContinuousLinearEquiv.coe_coe]
    rw [Trivialization.coordChangeL_apply]
    · exact (originalTotalCanonicalTransitionMap_apply hδ C hemb hboundary hzero hjoint J N hC hinv c d hx q).symm
    · exact hx

include hC hinv P in
/-- Every actual completed-total canonical-square fiber is a complex line. -/
theorem originalTotalCanonicalTensorSquare_finrank
    (hJI : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
    (hJE : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (x : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) :
    Module.finrank ℂ (OriginalTotalCanonicalTensorSquare C J N x) = 1 := by
  rcases totalInterior_cylinder_cover hδ (fun t p => C t p.val) hzero x with ⟨p, rfl⟩ | ⟨p, rfl⟩
  · rw [(originalTotalInteriorFiberEquiv C J N p).toLinearEquiv.finrank_eq]
    exact originalInteriorCanonicalTensorSquare_finrank hδ C hemb hboundary hzero J N hC hinv hJI hJsq p
  · rw [(originalTotalEndFiberEquiv C J N p).toLinearEquiv.finrank_eq]
    exact originalEndCanonicalTensorSquare_finrank hδ C hemb hboundary hzero J N P hC hinv hJE hJsq p

end FsFltz.Geometry.IntrinsicCompletionGluing
