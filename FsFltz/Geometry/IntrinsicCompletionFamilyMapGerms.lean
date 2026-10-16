import FsFltz.Geometry.IntrinsicNativeCompletionFamilyCovectorAtlas
import FsFltz.Geometry.IntrinsicBundleNativeData

/-!
# Actual real open map germs in the original completed-family atlas

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199;
`def:maslov`, lines 225–232; and `sec:lean`, lines 788–814.
Target-valued real germs on the original interior and a cylinder strip
containing the seam produce real Euclidean germs of the same total map.
The chart belongs to the retained atlas and the interval restriction
agrees literally with the original map. No extension theorem for arbitrary
native `ContMDiff` maps is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCompletionGluing
open IntrinsicSmoothBundle

/-- Actual target-valued real germs of a map on a specified part of a
manifold with corners, in charts of its original atlas. -/
def HasRealOpenMapGermsOn {E H X : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] [TopologicalSpace X]
    (I : ModelWithCorners ℝ E H) [ChartedSpace H X] {r : ℕ}
    (N : SmoothManifold r) (A : Set X) (f : A → N.Point) : Prop :=
  ∀ x ∈ A,
    ∃ e : OpenPartialHomeomorph X H,
      e ∈ _root_.atlas H X ∧ x ∈ e.source ∧
      ∃ U : TopologicalSpace.Opens E, e.extend I x ∈ U ∧
        ∃ β : U → N.Point, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Model r) ∞ β ∧
          ∀ z (hzA : z ∈ A), ∀ _hz : z ∈ e.source, ∀ h : e.extend I z ∈ U,
            β ⟨e.extend I z, h⟩ = f ⟨z, hzA⟩

variable {d r : ℕ} (M : SmoothManifold d) (N : SmoothManifold r)
  {X : Type} [TopologicalSpace X]
  [ChartedSpace (ModelProd (EuclideanHalfSpace 1) (Model d)) X]

/-- A target-valued real germ on a native interval patch becomes a real
Euclidean germ in the literal lifted patch chart of the total atlas. -/
theorem exists_realOpenMapGermAt_intervalPatch
    (T : Set X) (f : T → N.Point) (S : Set Parameter) (A : Set M.Point)
    (hA : IsOpen A) (j : Parameter × M.Point → X) (hj : IsOpenEmbedding j)
    (hcharts : ∀ p : Parameter × M.Point,
      (chartAt (ModelProd (EuclideanHalfSpace 1) (Model d)) p).lift_openEmbedding hj ∈
        _root_.atlas (ModelProd (EuclideanHalfSpace 1) (Model d)) X)
    (hjS : ∀ p, j p ∈ T → p.1 ∈ S)
    (v : Parameter → M.Point → N.Point)
    (hformula : ∀ t ∈ S, ∀ x ∈ A, ∀ h : j (t, x) ∈ T,
      f ⟨j (t, x), h⟩ = v t x)
    (hf : ∀ t ∈ S, ∀ x ∈ A,
      ∃ V : TopologicalSpace.Opens (ℝ × M.Point), (t.val, x) ∈ V ∧
        ∃ γ : V → N.Point,
          ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model r) ∞ γ ∧
          ∀ s ∈ S, ∀ y ∈ A, ∀ h : (s.val, y) ∈ V,
            γ ⟨(s.val, y), h⟩ = v s y)
    (p : Parameter × M.Point) (hpS : p.1 ∈ S) (hpA : p.2 ∈ A) :
    ∃ e : OpenPartialHomeomorph X (ModelProd (EuclideanHalfSpace 1) (Model d)),
      e ∈ _root_.atlas (ModelProd (EuclideanHalfSpace 1) (Model d)) X ∧ j p ∈ e.source ∧
      ∃ U : TopologicalSpace.Opens (Model 1 × Model d),
        e.extend (familyModel d) (j p) ∈ U ∧
        ∃ β : U → N.Point, ContMDiff 𝓘(ℝ, Model 1 × Model d) 𝓘(ℝ, Model r) ∞ β ∧
          ∀ z (hzT : z ∈ T), ∀ _hz : z ∈ e.source, ∀ h : e.extend (familyModel d) z ∈ U,
            β ⟨e.extend (familyModel d) z, h⟩ = f ⟨z, hzT⟩ := by
  let c := chartAt (Model d) p.2
  let e : OpenPartialHomeomorph (Parameter × M.Point)
      (ModelProd (EuclideanHalfSpace 1) (Model d)) :=
    (chartAt (EuclideanHalfSpace 1) p.1).prod c
  let b := e.lift_openEmbedding hj
  have hp : p ∈ e.source := ⟨mem_chart_source _ _, mem_chart_source _ _⟩
  have hb : j p ∈ b.source := ⟨p, hp, rfl⟩
  have he : (b.extend (familyModel d)) ∘ j = e.extend (familyModel d) := by
    funext q
    exact congrArg (familyModel d) (OpenPartialHomeomorph.lift_openEmbedding_apply e hj)
  let ρ := intervalChartRealInverse (d := d) p.1
  have hρ := contDiff_intervalChartRealInverse (d := d) p.1
  have hρM : ContMDiff 𝓘(ℝ, Model 1 × Model d)
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞ ρ := by
    exact (contDiff_fst.comp hρ).contMDiff.prodMk
      (contDiff_snd.comp hρ).contMDiff
  let W : Set (Model 1 × Model d) := ρ ⁻¹' (univ ×ˢ c.target)
  have hW : IsOpen W := (isOpen_univ.prod c.open_target).preimage hρ.continuous
  let η : Model 1 × Model d → ℝ × M.Point := fun z => ((ρ z).1, c.symm (ρ z).2)
  have hcs : ContMDiffOn 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ c.symm c.target :=
    contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (chart_mem_atlas _ _))
  have hη : ContMDiffOn 𝓘(ℝ, Model 1 × Model d)
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞ η W :=
    ((contMDiff_fst.comp hρM).contMDiffOn).prodMk
      (hcs.comp (contMDiff_snd.comp hρM).contMDiffOn (fun _ hz => hz.2))
  have hηeq (q : Parameter × M.Point) (hq : q ∈ e.source) :
      η (b.extend (familyModel d) (j q)) = (q.1.val, q.2) := by
    have hρeq : ρ (b.extend (familyModel d) (j q)) = (q.1.val, c q.2) := by
      change ρ ((b.extend (familyModel d) ∘ j) q) = _
      rw [he]
      exact intervalChartRealInverse_extend M p.1 p.2 q
    change ((ρ (b.extend (familyModel d) (j q))).1,
      c.symm (ρ (b.extend (familyModel d) (j q))).2) = _
    rw [hρeq, c.left_inv hq.2]
  obtain ⟨V, hpV, γ, hγ, hag⟩ := hf p.1 hpS p.2 hpA
  let U : TopologicalSpace.Opens (Model 1 × Model d) :=
    ⟨W ∩ η ⁻¹' ((V : Set (ℝ × M.Point)) ∩ (univ ×ˢ A)),
      hη.continuousOn.isOpen_inter_preimage hW (V.isOpen.inter (isOpen_univ.prod hA))⟩
  let Q : U → V := fun z => ⟨η z.val, z.property.2.1⟩
  have hQ : ContMDiff 𝓘(ℝ, Model 1 × Model d)
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞ Q := by
    apply (ContMDiff.subtypeVal_comp_iff V Q).mp
    intro z
    exact (hη.contMDiffAt (hW.mem_nhds z.property.1)).comp z contMDiff_subtype_val.contMDiffAt
  refine ⟨b, hcharts p, hb, U, ?_, γ ∘ Q, hγ.comp hQ, ?_⟩
  · refine ⟨?_, ?_⟩
    · change ρ ((b.extend (familyModel d) ∘ j) p) ∈ univ ×ˢ c.target
      rw [he]
      have hρp : ρ (e.extend (familyModel d) p) = (p.1.val, c p.2) :=
        intervalChartRealInverse_extend M p.1 p.2 p
      rw [hρp]
      exact ⟨mem_univ _, c.map_source hp.2⟩
    · change η (b.extend (familyModel d) (j p)) ∈
        (V : Set (ℝ × M.Point)) ∩ (univ ×ˢ A)
      rw [hηeq p hp]
      exact ⟨hpV, mem_univ _, hpA⟩
  · intro z hz hze hzU
    obtain ⟨q, hq, rfl⟩ := hze
    have hmid : (q.1.val, q.2) ∈ V := by
      have h := hzU.2.1
      change η (b.extend (familyModel d) (j q)) ∈ V at h
      rwa [hηeq q hq] at h
    have hqA : q.2 ∈ A := by
      have h := hzU.2.2.2
      change (η (b.extend (familyModel d) (j q))).2 ∈ A at h
      rwa [hηeq q hq] at h
    have harg : Q ⟨b.extend (familyModel d) (j q), hzU⟩ = ⟨(q.1.val, q.2), hmid⟩ :=
      Subtype.ext (hηeq q hq)
    exact (congrArg γ harg).trans ((hag q.1 (hjS q hz) q.2 hqA hmid).trans
      (hformula q.1 (hjS q hz) q.2 hqA hz).symm)

section TotalFamily

variable {k : ℕ} {M₀ : Type} [TopologicalSpace M₀] [T2Space M₀]
  [SecondCountableTopology M₀]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M₀]
  [IsManifold (𝓡∂ (k + 1)) ∞ M₀]

/-- Actual real patch germs cover every point of the retained total
completion on its original parameter set. The cylinder strip contains
the boundary seam and every outward radius; no collar width is changed. -/
theorem hasRealOpenMapGermsOn_totalFamily_of_patches
    {δ : ℝ} (hδ : 0 < δ)
    (C : Parameter → ℝ × IntrinsicBoundary.Point k M₀ → M₀)
    (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M₀)),
      (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
    (hzero : ∀ t b, C t (0, b) = b.val)
    (hjoint : IsOpenEmbedding (totalCollar
      (fun t (p : Half δ (IntrinsicBoundary.Point k M₀)) => C t p.val)))
    (cutoff : ℝ) (hcutoff : cutoff < 0) (S : Set Parameter)
    (f : {z : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M₀)) => C t p.val) //
      parameter (fun t (p : Half δ (IntrinsicBoundary.Point k M₀)) => C t p.val) z ∈ S} → N.Point)
    (vi : Parameter → IntrinsicInterior.Point k M₀ → N.Point)
    (vc : Parameter → Band δ (IntrinsicBoundary.Point k M₀) → N.Point)
    (hfi : ∀ t (ht : t ∈ S) x, f ⟨totalInterior (fun t p => C t p.val) (t, x), ht⟩ = vi t x)
    (hfc : ∀ t (ht : t ∈ S) x, f ⟨totalCylinder (fun t p => C t p.val) (t, x), ht⟩ = vc t x) :
    letI := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M₀) δ
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    let c := fun t (p : Half δ (IntrinsicBoundary.Point k M₀)) => C t p.val
    HasSmoothManifoldTargetFamilyOn (IntrinsicInterior.smoothManifold k M₀) N S
      vi →
    (∀ t ∈ S, ∀ x : Band δ (IntrinsicBoundary.Point k M₀), cutoff < -x.val.1 →
      ∃ V : TopologicalSpace.Opens (ℝ × Band δ (IntrinsicBoundary.Point k M₀)),
        (t.val, x) ∈ V ∧ ∃ γ : V → N.Point,
          ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1))) 𝓘(ℝ, Model r) ∞ γ ∧
          ∀ s ∈ S, ∀ y : Band δ (IntrinsicBoundary.Point k M₀), cutoff < -y.val.1 →
            ∀ h : (s.val, y) ∈ V, γ ⟨(s.val, y), h⟩ = vc s y) →
    HasRealOpenMapGermsOn (familyModel (k + 1)) N (parameter c ⁻¹' S) f := by
  let := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M₀) δ
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let c := fun t (p : Half δ (IntrinsicBoundary.Point k M₀)) => C t p.val
  dsimp only
  intro hi hc z hz
  rcases totalInterior_cylinder_strip_cover hδ C hboundary hzero cutoff hcutoff z with
    ⟨p, rfl⟩ | ⟨p, hp, rfl⟩
  · apply exists_realOpenMapGermAt_intervalPatch
      (IntrinsicInterior.smoothManifold k M₀) N (parameter c ⁻¹' S) f S univ isOpen_univ
      (totalInterior c) (isOpenEmbedding_totalInterior hδ c hzero hjoint)
      (v := vi) (hformula := fun t ht x _ h => hfi t ht x)
      (hf := by
        intro t ht x _
        obtain ⟨U, hpU, β, hβ, heq⟩ := hi t ht x
        exact ⟨U, hpU, β, hβ, fun s hs y _ hy => heq s hs y hy⟩)
      (p := p) (hpS := hz) (hpA := mem_univ _)
    · intro q
      change _ ∈ RelativeOpenCover.atlas _ _
      exact Or.inl ⟨chartAt (ModelProd (EuclideanHalfSpace 1) (Model (k + 1))) q,
        chart_mem_atlas _ q, rfl⟩
    · intro q hq
      exact hq
  · have hA : IsOpen {x : Band δ (IntrinsicBoundary.Point k M₀) | cutoff < -x.val.1} :=
      isOpen_lt continuous_const (continuous_fst.comp continuous_subtype_val).neg
    apply exists_realOpenMapGermAt_intervalPatch
      (bandManifold δ (IntrinsicBoundary.smoothManifold k M₀)) N (parameter c ⁻¹' S) f S
      {x | cutoff < -x.val.1} hA (totalCylinder c) (isOpenEmbedding_totalCylinder c hjoint)
      (v := vc) (hformula := fun t ht x _ h => hfc t ht x)
      (hf := hc) (p := p) (hpS := hz) (hpA := hp)
    · intro q
      change _ ∈ RelativeOpenCover.atlas _ _
      exact Or.inr ⟨chartAt (ModelProd (EuclideanHalfSpace 1) (Model (k + 1))) q,
        chart_mem_atlas _ q, rfl⟩
    · intro q hq
      exact hq

end TotalFamily

end FsFltz.Geometry.IntrinsicCompletionGluing
