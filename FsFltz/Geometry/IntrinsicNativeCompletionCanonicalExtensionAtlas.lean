import FsFltz.Geometry.IntrinsicNativeCompletionWholeCanonicalBundle
import FsFltz.Geometry.IntrinsicNativeCompletionRealBaseChanges
import FsFltz.Geometry.IntrinsicNativeCompletionWholeSectionRestriction

/-!
# Real-open coordinates of the original whole canonical bundle

Source: `geoemtric-part-fsf.tex`, smooth-extension convention (119–122),
`def:maslov` (212–244), and `sec:lean` (766–836). These coordinates use the
actual original open inclusions and the already constructed tensor bundle.
Real-open changes are local; no off-interval cocycle or complex law is imposed.
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
  (J : ∀ s : Parameter, Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
    Model (k + 1) →L[ℝ] Model (k + 1))

local instance extensionBandCharts :
    ChartedSpace (Model (k + 1)) (Band δ (IntrinsicBoundary.Point k M)) := bandChartedSpace δ
local instance atlasProductCharts :
    ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ
local instance atlasProductSmooth :
    IsManifold 𝓘(ℝ, Model k × ℝ) ∞ (IntrinsicBoundary.Point k M × ℝ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, ℝ))
    (IntrinsicBoundary.Point k M) ℝ

namespace OriginalTotalCanonicalChart

variable {hδ C hemb hboundary hzero J}

/-- The native base of each of the two sorts of actual bundle charts. -/
abbrev NativeBase (c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n)) : Type :=
  match c with
  | .inl _ => Parameter × IntrinsicInterior.Point k M
  | .inr _ => Parameter × Band δ (IntrinsicBoundary.Point k M)

abbrev SpatialModel (c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n)) : Type :=
  match c with
  | .inl _ => Model (k + 1)
  | .inr _ => Model k × ℝ

instance (c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    NormedAddCommGroup c.SpatialModel :=
  match c with
  | .inl _ => inferInstanceAs (NormedAddCommGroup (Model (k + 1)))
  | .inr _ => inferInstanceAs (NormedAddCommGroup (Model k × ℝ))
instance (c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    NormedSpace ℝ c.SpatialModel :=
  match c with
  | .inl _ => inferInstanceAs (NormedSpace ℝ (Model (k + 1)))
  | .inr _ => inferInstanceAs (NormedSpace ℝ (Model k × ℝ))

abbrev RealBase (c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n)) :=
  ℝ × c.SpatialModel
abbrev RealModel (c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n)) :=
  c.RealBase × ℂ

abbrev inclusion (c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    c.NativeBase → TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) :=
  match c with
  | .inl _ => totalInterior (fun t p => C t p.val)
  | .inr _ => totalCylinder (fun t p => C t p.val)

abbrev nativeDomain (c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    Set c.NativeBase := match c with | .inl c => c.baseDomain | .inr c => c.baseDomain

abbrev realDomain (c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    TopologicalSpace.Opens c.RealBase := match c with | .inl c => c.domain | .inr c => c.domain

abbrev baseCoordinate (c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    c.NativeBase → c.RealBase :=
  match c with
  | .inl c => fun p => (p.1.val, chartAt (Model (k + 1)) c.anchor p.2)
  | .inr c => fun p => (p.1.val, chartAt (Model k × ℝ) c.anchor (endBandCoordinates p.2))

def totalDomain (c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    Set (TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) :=
  c.inclusion '' c.nativeDomain

variable (N : Model (2 * n) ≃L[ℝ] Model (k + 1))
  (hjoint : IsOpenEmbedding (totalCollar
    (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
  (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ (C t)
    (Half δ (IntrinsicBoundary.Point k M)))
  (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C t q) = q)

/-- Literal real coordinates of a point of the actual whole tensor bundle.
The last coordinate is its already constructed promoted pretrivialization. -/
def coordinate (c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (p : c.NativeBase) (τ : OriginalTotalCanonicalTensorSquare C J N (c.inclusion p)) : c.RealModel :=
  (c.baseCoordinate p,
    (originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv c
      ⟨c.inclusion p, τ⟩).2)

theorem totalDomain_eq_baseSet
    (c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    c.totalDomain =
      (originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv c).baseSet := by
  cases c <;> rfl

/-- Raw coordinates at an arbitrary point of the actual whole bundle.
Membership supplies its unique original branch preimage. -/
def coordinateAt
    (c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (z : Bundle.TotalSpace ℂ (OriginalTotalCanonicalTensorSquare C J N))
    (hz : z.proj ∈ c.totalDomain) : c.RealModel :=
  (c.baseCoordinate hz.choose,
    (originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv c z).2)

include hδ hzero hjoint in
theorem inclusion_injective
    (c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    Function.Injective c.inclusion := by
  cases c with
  | inl c => exact (isOpenEmbedding_totalInterior hδ (fun t p => C t p.val) hzero hjoint).injective
  | inr c => exact (isOpenEmbedding_totalCylinder (fun t p => C t p.val) hjoint).injective

theorem coordinateAt_inclusion
    (c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (p : c.NativeBase) (hp : p ∈ c.nativeDomain)
    (τ : OriginalTotalCanonicalTensorSquare C J N (c.inclusion p)) :
    c.coordinateAt N hjoint hC hinv ⟨c.inclusion p, τ⟩ ⟨p, hp, rfl⟩ =
      c.coordinate N hjoint hC hinv p τ := by
  have he : (⟨p, hp, rfl⟩ : c.inclusion p ∈ c.totalDomain).choose = p :=
    c.inclusion_injective hjoint (⟨p, hp, rfl⟩ : c.inclusion p ∈ c.totalDomain).choose_spec.2
  exact congrArg (fun q => (c.baseCoordinate q,
    (originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv c
      ⟨c.inclusion p, τ⟩).2)) he

end OriginalTotalCanonicalChart

variable (N : Model (2 * n) ≃L[ℝ] Model (k + 1))
  (hjoint : IsOpenEmbedding (totalCollar
    (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
  (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ (C t)
    (Half δ (IntrinsicBoundary.Point k M)))
  (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C t q) = q)

/-- The proved transition law applies to every tensor in the actual fiber,
not only to a chosen section or generator. -/
theorem originalTotalCanonicalCoefficient_transition
    (c d : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n))
    {x : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)}
    (hx : x ∈ c.totalDomain ∩ d.totalDomain)
    (τ : OriginalTotalCanonicalTensorSquare C J N x) :
    (originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv d ⟨x, τ⟩).2 =
      originalTotalCanonicalTransition hδ C hemb hboundary hzero J N c d x *
        (originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv c ⟨x, τ⟩).2 := by
  let ec := originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv c
  let ed := originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv d
  have hxc : x ∈ ec.baseSet := (c.totalDomain_eq_baseSet N hjoint hC hinv) ▸ hx.1
  have hxd : x ∈ ed.baseSet := (d.totalDomain_eq_baseSet N hjoint hC hinv) ▸ hx.2
  have h := originalTotalCanonicalTransitionMap_apply hδ C hemb hboundary hzero hjoint J N hC hinv
    c d ⟨hxc, hxd⟩ (ec ⟨x, τ⟩).2
  change _ * (ec ⟨x, τ⟩).2 = (ed ⟨x, ec.symm x (ec ⟨x, τ⟩).2⟩).2 at h
  rw [ec.symm_apply_apply_mk hxc τ] at h
  exact h.symm

include hjoint hC hinv in
/-- Actual chart scalars are reciprocal on retained overlaps. This follows
from the actual fiber coordinates, without any off-interval complex law. -/
theorem originalTotalCanonicalTransition_mul_reverse
    (c d : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n))
    {x : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)}
    (hx : x ∈ c.totalDomain ∩ d.totalDomain) :
    originalTotalCanonicalTransition hδ C hemb hboundary hzero J N d c x *
      originalTotalCanonicalTransition hδ C hemb hboundary hzero J N c d x = 1 := by
  let ec := originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint J N hC hinv c
  have hxc : x ∈ ec.baseSet := (c.totalDomain_eq_baseSet N hjoint hC hinv) ▸ hx.1
  let τ := ec.symm x 1
  have hq : (ec ⟨x, τ⟩).2 = 1 := congrArg Prod.snd (ec.apply_mk_symm hxc 1)
  have hcd := originalTotalCanonicalCoefficient_transition hδ C hemb hboundary hzero J N hjoint hC hinv c d hx τ
  have hdc := originalTotalCanonicalCoefficient_transition hδ C hemb hboundary hzero J N hjoint hC hinv d c ⟨hx.2, hx.1⟩ τ
  rw [hcd, hq, mul_one] at hdc
  exact hdc.symm

include hjoint hC hinv in
theorem originalTotalCanonicalTransition_ne_zero
    (c d : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n))
    {x : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)}
    (hx : x ∈ c.totalDomain ∩ d.totalDomain) :
    originalTotalCanonicalTransition hδ C hemb hboundary hzero J N c d x ≠ 0 := by
  intro hz
  have h := originalTotalCanonicalTransition_mul_reverse hδ C hemb hboundary hzero J N hjoint hC hinv c d hx
  rw [hz, mul_zero] at h
  exact zero_ne_one h

end FsFltz.Geometry.IntrinsicCompletionGluing
