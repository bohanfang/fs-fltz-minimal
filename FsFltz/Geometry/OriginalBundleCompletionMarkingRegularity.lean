import FsFltz.Geometry.OriginalBundleCompletionMarking
import FsFltz.Geometry.IntrinsicBundleInteriorTransport
import FsFltz.Geometry.IntrinsicNativeCompletionEndGradingDerivative

/-!
# Real germs of the independently prescribed original markings

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 143–158;
`def:chain`, lines 163–199; `g:initial`, lines 374–384; and `sec:lean`,
lines 788–814. The actual retained marking is jointly regular whenever its
original compact inclusion and its source complete flow have real local
extensions. Its interior formula and all signed cylinder formulas follow
from the already proved marking equations.

Joint finite-time regularity of the source flow is an explicit upstream
assumption here. It concerns only actual interval parameters and arbitrary
finite real flow times; it asks for no complete off-interval flow. Source
markings, their geometric existence, and the target theorem remain separate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle Topology
open FsFltz.Geometry.IntrinsicLiouville
open FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.IntrinsicSmoothBundle

/-- A smooth map on an open subtype has a raw representative smooth on
that same open set. No regularity outside the set is asserted. -/
theorem exists_rawRepresentative_of_smoothOpenMap
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {d : ℕ} (N : SmoothManifold d) (U : TopologicalSpace.Opens V)
    (x : U) (β : U → N.Point)
    (hβ : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, Model d) ∞ β) :
    ∃ γ : V → N.Point, ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, Model d) ∞ γ U ∧
      ∀ y (hy : y ∈ U), γ y = β ⟨y, hy⟩ := by
  let γ := Subtype.val.extend β (fun _ => β x)
  have he : γ ∘ (Subtype.val : U → V) = β :=
    Function.extend_comp Subtype.val_injective β (fun _ => β x)
  refine ⟨γ, ?_, ?_⟩
  · intro y hy
    apply ContMDiffAt.contMDiffWithinAt
    apply (contMDiffAt_subtype_iff (x := (⟨y, hy⟩ : U))).mp
    simpa only [← Function.comp_def, he] using hβ.contMDiffAt (x := (⟨y, hy⟩ : U))
  · intro y hy
    exact congrFun he ⟨y, hy⟩

variable {k d : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

omit [T2Space M] [SecondCountableTopology M] in
/-- A compact source germ restricts to every original native interior
chart, preserving its actual coordinate map. -/
theorem HasSmoothTargetFamilyOn.rawInteriorGerm
    (N : SmoothManifold d) {S : Set Parameter} {v : Parameter → M → N.Point}
    (h : HasSmoothTargetFamilyOn (𝓡∂ (k + 1)) N S v)
    (s : Parameter) (hs : s ∈ S) (u w : IntrinsicInterior.Point k M)
    (hw : w ∈ (chartAt (Model (k + 1)) u).source) :
    ∃ U : Set (ℝ × Model (k + 1)), IsOpen U ∧
      (s.val, chartAt (Model (k + 1)) u w) ∈ U ∧
      ∃ β : ℝ × Model (k + 1) → N.Point,
        ContMDiffOn 𝓘(ℝ, ℝ × Model (k + 1)) 𝓘(ℝ, Model d) ∞ β U ∧
        ∀ t ∈ S, ∀ z ∈ (chartAt (Model (k + 1)) u).source,
          (t.val, chartAt (Model (k + 1)) u z) ∈ U →
          β (t.val, chartAt (Model (k + 1)) u z) = v t z.val := by
  obtain ⟨a, ha⟩ := chart_mem_atlas (Model (k + 1)) u
  change a.chart = chartAt (Model (k + 1)) u at ha
  have hwa : w.val ∈ a.ambient.source := by rwa [← ha, a.source_eq] at hw
  obtain ⟨U, hpU, β, hβ, heq⟩ := h a.ambient a.mem_atlas s hs w.val hwa
  obtain ⟨γ, hγ, hγeq⟩ := exists_rawRepresentative_of_smoothOpenMap N U ⟨_, hpU⟩ β hβ
  refine ⟨U, U.isOpen, ?_, γ, hγ, ?_⟩
  · rw [← ha, a.toFun_eq w (by simpa only [ha] using hw)]
    exact hpU
  · intro t ht z hz htz
    have hza : z.val ∈ a.ambient.source := by rwa [← ha, a.source_eq] at hz
    have hc := a.toFun_eq z (by simpa only [ha] using hz)
    rw [ha] at hc
    rw [hc] at htz ⊢
    exact (hγeq _ htz).trans (heq t ht z.val hza htz)

omit [T2Space M] [SecondCountableTopology M] in
/-- A compact source germ restricts to every original native boundary
chart by insertion of the zero normal coordinate. -/
theorem HasSmoothTargetFamilyOn.rawBoundaryGerm
    (N : SmoothManifold d) {S : Set Parameter} {v : Parameter → M → N.Point}
    (h : HasSmoothTargetFamilyOn (𝓡∂ (k + 1)) N S v)
    (s : Parameter) (hs : s ∈ S) (u b : IntrinsicBoundary.Point k M)
    (hb : b ∈ (chartAt (Model k) u).source) :
    ∃ U : Set (ℝ × Model k), IsOpen U ∧ (s.val, chartAt (Model k) u b) ∈ U ∧
      ∃ β : ℝ × Model k → N.Point,
        ContMDiffOn 𝓘(ℝ, ℝ × Model k) 𝓘(ℝ, Model d) ∞ β U ∧
        ∀ t ∈ S, ∀ z ∈ (chartAt (Model k) u).source,
          (t.val, chartAt (Model k) u z) ∈ U →
          β (t.val, chartAt (Model k) u z) = v t z.val := by
  obtain ⟨a, ha⟩ := chart_mem_atlas (Model k) u
  change a.chart = chartAt (Model k) u at ha
  have hba : b.val ∈ a.ambient.source := by rwa [← ha, a.source_eq] at hb
  obtain ⟨U, hpU, β, hβ, heq⟩ := h a.ambient a.mem_atlas s hs b.val hba
  obtain ⟨γ, hγ, hγeq⟩ := exists_rawRepresentative_of_smoothOpenMap N U ⟨_, hpU⟩ β hβ
  let p : ℝ × Model k → ℝ × Model (k + 1) := fun z => (z.1, boundaryInsert k z.2)
  have hp : ContMDiff 𝓘(ℝ, ℝ × Model k) 𝓘(ℝ, ℝ × Model (k + 1)) ∞ p :=
    (contDiff_fst.prodMk ((boundaryInsert k).contDiff.comp contDiff_snd)).contMDiff
  refine ⟨p ⁻¹' U, U.isOpen.preimage hp.continuous, ?_, γ ∘ p,
    hγ.comp hp.contMDiffOn (fun _ hz => hz), ?_⟩
  · change p (s.val, chartAt (Model k) u b) ∈ U
    change (s.val, boundaryInsert k (chartAt (Model k) u b)) ∈ U
    rw [← ha, ← a.extend_eq_insert b (by simpa only [ha] using hb)]
    exact hpU
  · intro t ht z hz htz
    have hza : z.val ∈ a.ambient.source := by rwa [← ha, a.source_eq] at hz
    have hc := a.extend_eq_insert z (by simpa only [ha] using hz)
    rw [ha] at hc
    have hpz : p (t.val, chartAt (Model k) u z) =
        (t.val, a.ambient.extend (𝓡∂ (k + 1)) z.val) := Prod.ext rfl hc.symm
    change γ (p (t.val, chartAt (Model k) u z)) = _
    change p (t.val, chartAt (Model k) u z) ∈ U at htz
    rw [hpz] at htz ⊢
    exact (hγeq _ htz).trans (heq t ht z.val hza htz)

/-- Ordinary joint source-flow regularity at finite times and actual
interval parameters. The extension is local in all three variables. -/
def HasRealSmoothFlowGermsOn (N : SmoothManifold d) (S : Set Parameter)
    (φ : Parameter → ℝ → N.Point → N.Point) : Prop :=
  ∀ s ∈ S, ∀ r (x : N.Point),
    ∃ U : Set (ℝ × (ℝ × N.Point)), IsOpen U ∧ (s.val, (r, x)) ∈ U ∧
      ∃ β : ℝ × (ℝ × N.Point) → N.Point,
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)))
          𝓘(ℝ, Model d) ∞ β U ∧
        ∀ t ∈ S, ∀ a (y : N.Point), (t.val, (a, y)) ∈ U →
          β (t.val, (a, y)) = φ t a y

local instance markingProductCharts :
    ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ

omit [T2Space M] [SecondCountableTopology M] in
/-- The compact boundary inclusion and an ordinary source flow compose
to actual real germs in every boundary–radius chart, for all real radii. -/
theorem HasSmoothTargetFamilyOn.rawBoundaryFlowGerm
    (N : SmoothManifold d) {S : Set Parameter} {v : Parameter → M → N.Point}
    (h : HasSmoothTargetFamilyOn (𝓡∂ (k + 1)) N S v)
    (φ : Parameter → ℝ → N.Point → N.Point) (hφ : HasRealSmoothFlowGermsOn N S φ)
    (s : Parameter) (hs : s ∈ S) (u p : IntrinsicBoundary.Point k M × ℝ)
    (hp : p ∈ (chartAt (Model k × ℝ) u).source) :
    ∃ U : Set (ℝ × (Model k × ℝ)), IsOpen U ∧
      (s.val, chartAt (Model k × ℝ) u p) ∈ U ∧
      ∃ β : ℝ × (Model k × ℝ) → N.Point,
        ContMDiffOn 𝓘(ℝ, ℝ × (Model k × ℝ)) 𝓘(ℝ, Model d) ∞ β U ∧
        ∀ t ∈ S, ∀ z ∈ (chartAt (Model k × ℝ) u).source,
          (t.val, chartAt (Model k × ℝ) u z) ∈ U →
          β (t.val, chartAt (Model k × ℝ) u z) = φ t z.2 (v t z.1.val) := by
  have hchart (z : IntrinsicBoundary.Point k M × ℝ) :
      chartAt (Model k × ℝ) u z = (chartAt (Model k) u.1 z.1, z.2) := rfl
  have hpb : p.1 ∈ (chartAt (Model k) u.1).source := hp.1
  obtain ⟨U, hU, hpU, β, hβ, heq⟩ := h.rawBoundaryGerm N s hs u.1 p.1 hpb
  obtain ⟨V, hV, hpV, γ, hγ, hγeq⟩ := hφ s hs p.2 (v s p.1.val)
  let ρ : ℝ × (Model k × ℝ) → ℝ × Model k := fun z => (z.1, z.2.1)
  have hρ : ContMDiff 𝓘(ℝ, ℝ × (Model k × ℝ)) 𝓘(ℝ, ℝ × Model k) ∞ ρ :=
    (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)).contMDiff
  let q : ℝ × (Model k × ℝ) → ℝ × (ℝ × N.Point) :=
    fun z => (z.1, (z.2.2, β (ρ z)))
  have hq : ContMDiffOn 𝓘(ℝ, ℝ × (Model k × ℝ))
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))) ∞ q (ρ ⁻¹' U) := by
    have h₁ : ContMDiffOn 𝓘(ℝ, ℝ × (Model k × ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun z => z.1) (ρ ⁻¹' U) := contDiff_fst.contMDiff.contMDiffOn
    have h₂ : ContMDiffOn 𝓘(ℝ, ℝ × (Model k × ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun z => z.2.2) (ρ ⁻¹' U) :=
      (contDiff_snd.comp contDiff_snd).contMDiff.contMDiffOn
    exact h₁.prodMk (h₂.prodMk (hβ.comp hρ.contMDiffOn (fun _ hz => hz)))
  let W := (ρ ⁻¹' U) ∩ q ⁻¹' V
  have hW : IsOpen W :=
    hq.continuousOn.isOpen_inter_preimage (hU.preimage hρ.continuous) hV
  refine ⟨W, hW, ?_, γ ∘ q,
    hγ.comp (hq.mono inter_subset_left) (fun _ hz => hz.2), ?_⟩
  · rw [hchart]
    refine ⟨hpU, ?_⟩
    change (s.val, (p.2, β (s.val, chartAt (Model k) u.1 p.1))) ∈ V
    rw [heq s hs p.1 hpb hpU]
    exact hpV
  · intro t ht z hz htz
    rw [hchart] at htz ⊢
    have hzb : z.1 ∈ (chartAt (Model k) u.1).source := hz.1
    have hβz : β (t.val, chartAt (Model k) u.1 z.1) = v t z.1.val :=
      heq t ht z.1 hzb htz.1
    change γ (t.val, (z.2, β (t.val, chartAt (Model k) u.1 z.1))) = _
    have hzV : (t.val, (z.2, β (t.val, chartAt (Model k) u.1 z.1))) ∈ V := htz.2
    rw [hβz] at hzV ⊢
    exact hγeq t ht z.2 (v t z.1.val) hzV

variable {E : Parameter → Type*} [∀ s, TopologicalSpace (E s)]
  [TopologicalSpace (Bundle.TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]
  {P : BundlePrimitiveData (k := k) (M := M) E}
  {L : OriginalBundleLiouvilleLaws P} {Z : Parameter → CompleteLiouvilleManifold d}
  {c : OriginalCompactChart (k := k) (M := M) (E := E)} {t : Parameter}

namespace OriginalBundleCompletionMarkingData

omit [T2Space M] [SecondCountableTopology M] in
/-- The actual independent local marking has real germs on every
interior chart and every full signed-cylinder chart. Compact source
regularity and finite-time source-flow regularity are the only joint
regularity assumptions; neither marking-map germs nor pulled tensors
are inputs. The target coordinates may present varying source primitives. -/
theorem localEquiv_realGerms_of_source_inclusion_and_flow
    (O : OriginalBundleCompletionMarkingData L Z) (F : LocalCompletionFamily P c t)
    (N : SmoothManifold d) (R : ∀ s, (Z s).manifold.SmoothEquiv N)
    (hi : HasSmoothTargetFamilyOn (𝓡∂ (k + 1)) N F.base
      (fun s x => R s (chartValue c.val (O.compact s) s x)))
    (hflow : HasRealSmoothFlowGermsOn N F.base
      (fun s r y => R s ((Z s).completeFlow.flow r ((R s).symm y)))) :
    (∀ s (_hs : s ∈ F.base) (u w : IntrinsicInterior.Point k M),
      w ∈ (chartAt (Model (k + 1)) u).source →
      ∃ U : Set (ℝ × Model (k + 1)), IsOpen U ∧
        (s.val, chartAt (Model (k + 1)) u w) ∈ U ∧
        ∃ β : ℝ × Model (k + 1) → N.Point,
          ContMDiffOn 𝓘(ℝ, ℝ × Model (k + 1)) 𝓘(ℝ, Model d) ∞ β U ∧
          ∀ v (hv : v ∈ F.base) z, z ∈ (chartAt (Model (k + 1)) u).source →
            (v.val, chartAt (Model (k + 1)) u z) ∈ U →
            β (v.val, chartAt (Model (k + 1)) u z) =
              ((O.localEquiv F v hv).trans (R v)) (interiorIn (F.native.patches v) z)) ∧
    (∀ s (_hs : s ∈ F.base) (u : IntrinsicBoundary.Point k M × ℝ)
      (p : Band F.native.width (IntrinsicBoundary.Point k M)),
      endBandCoordinates p ∈ (chartAt (Model k × ℝ) u).source →
      ∃ U : Set (ℝ × (Model k × ℝ)), IsOpen U ∧
        (s.val, chartAt (Model k × ℝ) u (endBandCoordinates p)) ∈ U ∧
        ∃ β : ℝ × (Model k × ℝ) → N.Point,
          ContMDiffOn 𝓘(ℝ, ℝ × (Model k × ℝ)) 𝓘(ℝ, Model d) ∞ β U ∧
          ∀ v (hv : v ∈ F.base) (q : Band F.native.width (IntrinsicBoundary.Point k M)),
            endBandCoordinates q ∈ (chartAt (Model k × ℝ) u).source →
            (v.val, chartAt (Model k × ℝ) u (endBandCoordinates q)) ∈ U →
            β (v.val, chartAt (Model k × ℝ) u (endBandCoordinates q)) =
              ((O.localEquiv F v hv).trans (R v)) (cylinder (F.native.patches v) q)) := by
  constructor
  · intro s hs u w hw
    obtain ⟨U, hU, hpU, β, hβ, heq⟩ := hi.rawInteriorGerm N s hs u w hw
    refine ⟨U, hU, hpU, β, hβ, ?_⟩
    intro v hv z hz hzU
    rw [heq v hv z hz hzU]
    change R v (chartValue c.val (O.compact v) v z.val) =
      R v (O.localEquiv F v hv (original (F.native.patches v) z.val))
    rw [O.localEquiv_native]
  · intro s hs u p hp
    obtain ⟨U, hU, hpU, β, hβ, heq⟩ := hi.rawBoundaryFlowGerm N
      (fun v r y => R v ((Z v).completeFlow.flow r ((R v).symm y))) hflow
      s hs u (endBandCoordinates p) hp
    refine ⟨U, hU, hpU, β, hβ, ?_⟩
    intro v hv q hq hqU
    rw [heq v hv (endBandCoordinates q) hq hqU]
    change R v ((Z v).completeFlow.flow (-q.val.1)
      ((R v).symm (R v (chartValue c.val (O.compact v) v q.val.2.val)))) =
      R v (O.localEquiv F v hv (cylinder (F.native.patches v) q))
    rw [(R v).symm_apply_apply]
    have hq' : (F.sliceCompletion L v).endMap (q.val.2, -q.val.1) =
        cylinder (F.native.patches v) q :=
      F.sliceCompletion_end_cylinder L v q.val.2 q.val.1 q.property.1
    rw [← hq', O.localEquiv_end]

end OriginalBundleCompletionMarkingData

end FsFltz.Geometry.IntrinsicSmoothBundle
