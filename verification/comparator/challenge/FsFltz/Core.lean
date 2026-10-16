import Mathlib.Dynamics.Flow
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Separation.Hausdorff

/-!
# The full core of a domain in a complete real flow

This is the flow and compactness component of `def:pair`, lines 148–160,
and `lem:shrinking`, lines 605–629, in `geoemtric-part-fsf.tex`.
The complete flow is Mathlib's continuous action `Flow ℝ X`; its construction
from a smooth Liouville field on a completion remains a separate obligation
(`sec:lean`, lines 805–814). No Liouville or completion existence is asserted.
-/

namespace FsFltz

open Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Points whose entire forward real-time trajectory stays in the domain.
Source: `def:pair`, lines 148–155; `sec:lean`, lines 783–787. -/
def flowCore (φ : Flow ℝ X) (F : Set X) : Set X :=
  {x | ∀ t : ℝ, 0 ≤ t → φ t x ∈ F}

@[simp]
theorem mem_flowCore {φ : Flow ℝ X} {F : Set X} {x : X} :
    x ∈ flowCore φ F ↔ ∀ t : ℝ, 0 ≤ t → φ t x ∈ F := Iff.rfl

theorem flowCore_subset (φ : Flow ℝ X) (F : Set X) : flowCore φ F ⊆ F := by
  intro x hx
  simpa using hx 0 (le_refl 0)

/-- The negative-image formula uses the actual inverse time maps of the same
complete flow, not an independent family of sets. -/
theorem flowCore_eq_iInter_image (φ : Flow ℝ X) (F : Set X) :
    flowCore φ F = ⋂ t : {t : ℝ // 0 ≤ t}, φ (-t.val) '' F := by
  ext x
  simp only [flowCore, mem_ofPred_eq, mem_iInter, φ.image_eq_preimage_symm,
    neg_neg, mem_preimage]
  exact ⟨fun h t => h t.val t.property, fun h t ht => h ⟨t, ht⟩⟩

theorem flowCore_mono (φ : Flow ℝ X) {F G : Set X} (hFG : F ⊆ G) :
    flowCore φ F ⊆ flowCore φ G := by
  intro x hx t ht
  exact hFG (hx t ht)

theorem flowCore_forwardInvariant (φ : Flow ℝ X) (F : Set X) :
    IsForwardInvariant φ (flowCore φ F) := by
  intro t ht x hx s hs
  rw [← φ.map_add]
  exact hx (s + t) (add_nonneg hs ht)

/-- Equivariance under a homeomorphism conjugating the actual flows. Deriving
this conjugacy from primitive preservation is a separate geometric bridge
(`def:chain`, lines 171–189; `sec:lean`, lines 805–809). -/
theorem image_flowCore_of_conjugacy (φ : Flow ℝ X) (ψ : Flow ℝ Y)
    (h : X ≃ₜ Y) (hconj : ∀ t, Function.Semiconj h (φ t) (ψ t)) (F : Set X) :
    h '' flowCore φ F = flowCore ψ (h '' F) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ t ht
    exact ⟨φ t x, hx t ht, hconj t x⟩
  · intro hy
    refine ⟨h.symm y, ?_, h.apply_symm_apply y⟩
    intro t ht
    obtain ⟨x, hx, heq⟩ := hy t ht
    have hflow : h (φ t (h.symm y)) = ψ t y := by
      rw [hconj t, h.apply_symm_apply]
    have : x = φ t (h.symm y) := h.injective (heq.trans hflow.symm)
    simpa [this] using hx

/-- The zero-flow model retains the entire domain, including a finite
zero-dimensional ribbon (`def:pair`, lines 159–160). Identifying the flow of
a zero Liouville field with `Flow.id` remains a smooth-flow bridge. -/
@[simp]
theorem flowCore_id (F : Set X) : flowCore (Flow.id ℝ X) F = F := by
  ext x
  constructor
  · exact fun hx => flowCore_subset _ _ hx
  · intro hx t _
    exact hx

@[simp]
theorem flowCore_id_univ : flowCore (Flow.id ℝ X) Set.univ = Set.univ :=
  flowCore_id _

/-- A finite ribbon in the zero-flow model has a compact full core. -/
theorem isCompact_flowCore_id_of_finite {F : Set X} (hF : F.Finite) :
    IsCompact (flowCore (Flow.id ℝ X) F) := by
  rw [flowCore_id]
  exact hF.isCompact

theorem isClosed_flowCore (φ : Flow ℝ X) {F : Set X} (hF : IsClosed F) :
    IsClosed (flowCore φ F) := by
  rw [flowCore_eq_iInter_image]
  apply isClosed_iInter
  intro t
  rw [φ.image_eq_preimage_symm]
  exact hF.preimage (φ.continuous_toFun _)

theorem isCompact_flowCore [T2Space X] (φ : Flow ℝ X) {F : Set X}
    (hF : IsCompact F) : IsCompact (flowCore φ F) :=
  hF.of_isClosed_subset (isClosed_flowCore φ hF.isClosed) (flowCore_subset φ F)

/-- Negative invariance supplies the nesting used in `lem:shrinking`,
lines 618–620. Deriving negative invariance from strict outwardness is pending. -/
theorem negative_image_antitone (φ : Flow ℝ X) {F : Set X}
    (hneg : IsForwardInvariant φ.reverse F) :
    Antitone (fun t : {t : ℝ // 0 ≤ t} => φ (-t.val) '' F) := by
  intro s t hst y hy
  obtain ⟨x, hx, rfl⟩ := hy
  refine ⟨φ (-(t.val - s.val)) x, hneg (sub_nonneg.mpr hst) hx, ?_⟩
  simp [← φ.map_add, sub_eq_add_neg, ← add_assoc]

/-- The compact nested-set conclusion of `lem:shrinking`, lines 605–623.
Only the topological containment at one finite time is proved here; smooth
deformation and primitive scaling (lines 624–628) require geometric bridges. -/
theorem exists_negative_image_subset [T2Space X] (φ : Flow ℝ X) {F U : Set X}
    (hF : IsCompact F) (hneg : IsForwardInvariant φ.reverse F)
    (hU : IsOpen U) (hcore : flowCore φ F ⊆ U) :
    ∃ T : ℝ, 0 ≤ T ∧ φ (-T) '' F ⊆ U := by
  have hdir : Directed (· ⊇ ·) (fun t : {t : ℝ // 0 ≤ t} => φ (-t.val) '' F) := by
    intro s t
    refine ⟨max s t, ?_, ?_⟩
    · exact negative_image_antitone φ hneg (le_max_left s t)
    · exact negative_image_antitone φ hneg (le_max_right s t)
  have hcpct : ∀ t : {t : ℝ // 0 ≤ t}, IsCompact (φ (-t.val) '' F) :=
    fun t => hF.image (φ.continuous_toFun _)
  have hneighborhood : U ∈ nhdsSet (⋂ t : {t : ℝ // 0 ≤ t}, φ (-t.val) '' F) := by
    rw [← flowCore_eq_iInter_image]
    exact hU.mem_nhdsSet.mpr hcore
  obtain ⟨T, hT⟩ := exists_subset_nhds_of_isCompact hdir hcpct hneighborhood
  exact ⟨T.val, T.property, hT⟩

end FsFltz
