import FsFltz.Geometry.IntrinsicNativeCompletionInteriorSectionExtraction
import FsFltz.Geometry.IntrinsicNativeCompletionEndSectionExtraction
import FsFltz.Geometry.IntrinsicNativeCompletionMixedSectionExtension

/-!
# Local section extensions on the original completed total family

Source: `geoemtric-part-fsf.tex`, lines 119–122 (smooth open extension),
`def:maslov`, lines 212–232, and `sec:lean`, lines 788–814. A single
section of the original native completed fibers has a local coefficient
extension near every point of the actual total family, in either patch
of its native open cover. This condition is formulated on total points,
before either restriction is chosen.

The correspondence uses the original scalar coordinates on the independent
canonical tensor square. It concerns the source's open-extension convention;
it does not assert an extension theorem for bare boundary `ContMDiff`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Topology Bundle

namespace FsFltz.Geometry.IntrinsicCompletionGluing

variable {k n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {δ : ℝ} (hδ : 0 < δ)
  (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (hemb : ∀ t, IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val))
  (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
  (hzero : ∀ t b, C t (0, b) = b.val)
  (J : ∀ s : Parameter, Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
    Model (k + 1) →L[ℝ] Model (k + 1))
  (N : Model (2 * n) ≃L[ℝ] Model (k + 1))

/-- Near each actual total-family point, one native canonical chart has a
smooth open coefficient extension for the same original section. The chart
may belong to either side of the native interior/full-cylinder cover. -/
def HasOriginalTotalLocalSectionExtensions
    (σ : OriginalNativeCanonicalSection C J N) : Prop :=
  ∀ x : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val),
    (∃ (p : Parameter × IntrinsicInterior.Point k M)
      (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n)),
      totalInterior (fun t p => C t p.val) p = x ∧
      p ∈ c.baseDomain ∧ c.HasSectionCoefficientExtension (P := N) σ p) ∨
    (∃ (p : Parameter × Band δ (IntrinsicBoundary.Point k M))
      (c : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n)),
      totalCylinder (fun t p => C t p.val) p = x ∧
      p ∈ c.baseDomain ∧ c.HasSectionCoefficientExtension (N := N) σ p)

/-- The native geometric cover sends local coefficients on both original
patches to a local coefficient near every actual total-family point. -/
theorem originalTotalLocalSectionExtensions_of_branches
    (σ : OriginalNativeCanonicalSection C J N)
    (hσI : HasOriginalInteriorLocalSectionExtensions hδ C hemb hboundary hzero J N σ)
    (hσE : HasOriginalEndLocalSectionExtensions hδ C hemb hboundary hzero J N σ) :
    HasOriginalTotalLocalSectionExtensions hδ C hemb hboundary hzero J N σ := by
  intro x
  rcases totalInterior_cylinder_cover hδ (fun t p => C t p.val)
    (fun t b => hzero t b) x with ⟨p, hp⟩ | ⟨p, hp⟩
  · obtain ⟨c, hpc, hc⟩ := hσI p
    exact Or.inl ⟨p, c, hp, hpc, hc⟩
  · obtain ⟨c, hpc, hc⟩ := hσE p
    exact Or.inr ⟨p, c, hp, hpc, hc⟩

variable
  (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ (C t)
    (Half δ (IntrinsicBoundary.Point k M)))
  (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C t q) = q)
  (PE : Model (2 * n) ≃L[ℝ] (Model k × ℝ))
  (hjoint : IsOpenEmbedding (totalCollar
    (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
  (hmix : HasRealMixedGerms (δ := δ) C)

include hC hinv PE hjoint hmix in
/-- A germ in either native patch at a total point gives a germ in every
full-cylinder canonical chart there. Mixed points use the actual scalar
extension transfer; same-patch points use the derived chart changes. -/
theorem originalEndSectionExtensions_of_totalLocal
    (σ : OriginalNativeCanonicalSection C J N)
    (hσ : HasOriginalTotalLocalSectionExtensions hδ C hemb hboundary hzero J N σ) :
    HasOriginalEndSectionExtensions hδ C hemb hboundary hzero J N σ := by
  intro d p hp
  rcases hσ (totalCylinder (fun t q => C t q.val) p) with
    ⟨q, c, hqp, hqc, hc⟩ | ⟨q, c, hqp, hqc, hc⟩
  · rcases p with ⟨s, p⟩
    rcases q with ⟨t, w⟩
    have ht : t = s := by
      have h := congrArg (parameter (fun t q => C t q.val)) hqp
      simpa only [totalInterior, parameter_original, parameter_totalCylinder] using h
    subst t
    exact originalSectionCoefficientExtension_interiorToEnd hδ C hemb hboundary hzero J N
      hC hinv PE hjoint hmix c d σ s w p hqp hqc hp hc
  · have heq : q = p := (isOpenEmbedding_totalCylinder
      (fun t q => C t q.val) hjoint).injective hqp
    subst q
    exact OriginalEndCanonicalChart.HasSectionCoefficientExtension.changeChart
      N PE hC hinv c hc hqc d hp

include hC hinv hjoint hmix in
/-- A total-point germ also gives a germ in every interior canonical chart.
An end witness transfers through the inverse real mixed transition. -/
theorem originalInteriorSectionExtensions_of_totalLocal
    (σ : OriginalNativeCanonicalSection C J N)
    (hσ : HasOriginalTotalLocalSectionExtensions hδ C hemb hboundary hzero J N σ) :
    HasOriginalInteriorSectionExtensions hδ C hemb hboundary hzero J N σ := by
  intro c p hp
  rcases hσ (totalInterior (fun t q => C t q.val) p) with
    ⟨q, d, hqp, hqd, hd⟩ | ⟨q, d, hqp, hqd, hd⟩
  · have heq : q = p := (isOpenEmbedding_totalInterior hδ
      (fun t q => C t q.val) (fun t b => hzero t b) hjoint).injective hqp
    subst q
    exact OriginalInteriorCanonicalChart.HasSectionCoefficientExtension.changeChart
      N hC hinv d hd hqd c hp
  · rcases p with ⟨s, w⟩
    rcases q with ⟨t, a⟩
    have ht : t = s := by
      have h := congrArg (parameter (fun t q => C t q.val)) hqp
      simpa only [totalInterior, parameter_original, parameter_totalCylinder] using h
    subst t
    exact originalSectionCoefficientExtension_endToInterior hδ C hemb hboundary hzero J N
      hC hinv hjoint hmix c d σ s w a hqp.symm hp hqd hd

include hC hinv PE hjoint hmix in
/-- Under the original complex-field cover, a local coefficient germ in
either chart at every actual total-family point is equivalent to the two
original branch conditions. Both directions of mixed transfer are used in
the total-to-branch implication; this is not a conjunction definition. -/
theorem originalTotalLocalSectionExtensions_iff
    (hJI : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
    (hJE : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (σ : OriginalNativeCanonicalSection C J N) :
    HasOriginalTotalLocalSectionExtensions hδ C hemb hboundary hzero J N σ ↔
      HasOriginalInteriorLocalSectionExtensions hδ C hemb hboundary hzero J N σ ∧
      HasOriginalEndLocalSectionExtensions hδ C hemb hboundary hzero J N σ := by
  constructor
  · intro hσ
    have hI := originalInteriorSectionExtensions_of_totalLocal hδ C hemb hboundary hzero J N
      hC hinv hjoint hmix σ hσ
    have hE := originalEndSectionExtensions_of_totalLocal hδ C hemb hboundary hzero J N
      hC hinv PE hjoint hmix σ hσ
    constructor
    · intro p
      let c := originalInteriorCanonicalChartAt hδ C hemb hboundary hzero J N hC hinv hJI hJsq p
      have hp : p ∈ c.baseDomain :=
        mem_originalInteriorCanonicalChartAt hδ C hemb hboundary hzero J N hC hinv hJI hJsq p
      exact ⟨c, hp, hI c p hp⟩
    · intro p
      let c := originalEndCanonicalChartAt hδ C hemb hboundary hzero J PE hC hinv hJE hJsq p
      have hp : p ∈ c.baseDomain :=
        mem_originalEndCanonicalChartAt hδ C hemb hboundary hzero J PE hC hinv hJE hJsq p
      exact ⟨c, hp, hE c p hp⟩
  · rintro ⟨hσI, hσE⟩
    exact originalTotalLocalSectionExtensions_of_branches hδ C hemb hboundary hzero J N σ hσI hσE

end FsFltz.Geometry.IntrinsicCompletionGluing
