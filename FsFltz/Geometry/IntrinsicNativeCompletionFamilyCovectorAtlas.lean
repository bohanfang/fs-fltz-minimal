import FsFltz.Geometry.IntrinsicNativeCompletionFamilyCovectorGerms

/-!
# Real open covector coefficients in the original total atlas

Source: `geoemtric-part-fsf.tex`, smooth extension conventions, lines 119–122;
`def:chain`, lines 163–169; and `sec:lean`, lines 788–814. Every point of the
original total family has an actual chart in its existing smooth structure
with a smooth covector coefficient extension on a real open neighborhood.
The coordinate equality is on the entire native tangent fiber, including
the time direction and both parameter endpoints.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry

section RealOpenCoefficients
variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace X]
  (I : ModelWithCorners ℝ E H) [ChartedSpace H X]

/-- At every native point, an actual smooth chart has full covector
coefficients extending smoothly to a real open neighborhood of its coordinate.
The equality uses the whole native tangent fiber. -/
def HasRealOpenCovectorCoefficients
    (Ω : (x : X) → TangentSpace I x [⋀^Fin 1]→L[ℝ] ℝ) : Prop :=
  ∀ x, ∃ e : OpenPartialHomeomorph X H,
    e ∈ IsManifold.maximalAtlas I ∞ X ∧ x ∈ e.source ∧
    ∃ (U : Set E) (B : E → E [⋀^Fin 1]→L[ℝ] ℝ),
      IsOpen U ∧ e.extend I x ∈ U ∧ ContDiffOn ℝ ∞ B U ∧
      ∀ z ∈ e.source, e.extend I z ∈ U →
        Ω z = (B (e.extend I z)).compContinuousLinearMap
          (mfderiv I 𝓘(ℝ, E) (e.extend I) z)

end RealOpenCoefficients

namespace SmoothManifold

/-- Natural time and spatial coordinates recover the full interval covector,
including native time tangents at both endpoints. -/
theorem intervalCovectorInChart_reconstruct {d : ℕ} (M : SmoothManifold d)
    (Ω : (p : Parameter × M.Point) → TangentSpace ((𝓡∂ 1).prod 𝓘(ℝ, Model d)) p
      [⋀^Fin 1]→L[ℝ] ℝ) (a : M.Point) (p : Parameter × M.Point)
    (hp : p.2 ∈ (chartAt (Model d) a).source) :
    Ω p = (M.intervalCovectorInChart Ω a p.1 ((chartAt (Model d) a) p.2)).compContinuousLinearMap
      (mfderiv ((𝓡∂ 1).prod 𝓘(ℝ, Model d))
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
        (fun q : Parameter × M.Point => (q.1.val, (chartAt (Model d) a) q.2)) p) := by
  let c := chartAt (Model d) a
  have hd := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).symm_comp_deriv hp
  have hdν : mfderiv ((𝓡∂ 1).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      (fun q : Parameter × M.Point => (q.1.val, c q.2)) p =
        (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : Parameter → ℝ) p.1).prodMap
          (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c p.2) := by
    change mfderiv _ _ (Prod.map (Subtype.val : Parameter → ℝ) c) p = _
    exact mfderiv_prodMap
      ((contMDiff_subtypeVal_Icc (n := ∞)).mdifferentiableAt (by simp))
      ((mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).mdifferentiableAt hp)
  ext vs
  dsimp only [intervalCovectorInChart]
  erw [hdν, c.left_inv hp]
  change (Ω p) vs = (Ω p) (fun j =>
    (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : Parameter → ℝ) p.1 (vs j).1 •
      (1 : TangentSpace (𝓡∂ 1) p.1),
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c.symm (c p.2)
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c p.2 (vs j).2)))
  congr 1
  funext j
  apply Prod.ext
  · exact (canonicalTimeTangent_decompose p.1 (vs j).1).symm
  · exact (congrArg (fun L => L (vs j).2) hd).symm

end SmoothManifold

namespace IntrinsicCompletionGluing

/-- Inverse of the parameter chart on the real ambient coordinate line.
The right endpoint chart reverses its time direction. -/
def intervalChartRealInverse {d : ℕ} (t : Parameter) (p : Model 1 × Model d) :
    ℝ × Model d :=
  (if t.val < 1 then p.1 0 else 1 - p.1 0, p.2)

theorem contDiff_intervalChartRealInverse {d : ℕ} (t : Parameter) :
    ContDiff ℝ ∞ (intervalChartRealInverse (d := d) t) := by
  unfold intervalChartRealInverse
  split_ifs <;> fun_prop

/-- The explicit real inverse recovers the natural parameter and spatial
coordinates from the actual interval-product chart. -/
theorem intervalChartRealInverse_extend {d : ℕ} (M : SmoothManifold d)
    (t : Parameter) (a : M.Point) (p : Parameter × M.Point) :
    intervalChartRealInverse t
      (((chartAt (EuclideanHalfSpace 1) t).prod (chartAt (Model d) a)).extend
        (familyModel d) p) = (p.1.val, (chartAt (Model d) a) p.2) := by
  rw [OpenPartialHomeomorph.extend_prod]
  apply Prod.ext
  · rw [Icc_chartedSpaceChartAt]
    unfold intervalChartRealInverse
    split_ifs <;> simp [IccLeftChart, IccRightChart, OpenPartialHomeomorph.extend,
      modelWithCornersEuclideanHalfSpace]
  · rfl

end IntrinsicCompletionGluing

section IntervalPatch
open SmoothManifold IntrinsicCompletionGluing

variable {d : ℕ} (M : SmoothManifold d) {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ModelProd (EuclideanHalfSpace 1) (Model d)) X]
  [IsManifold (familyModel d) ∞ X]

/-- Real smooth coefficients pull back along a real smooth coordinate map
with its entire differential. -/
private theorem contDiffOn_covector_coordinate_pullback
    (B : ℝ × Model d → (ℝ × Model d) [⋀^Fin 1]→L[ℝ] ℝ)
    (U : Set (ℝ × Model d)) (hB : ContDiffOn ℝ ∞ B U)
    (r : Model 1 × Model d → ℝ × Model d) (hr : ContDiff ℝ ∞ r) :
    ContDiffOn ℝ ∞ (fun p => (B (r p)).compContinuousLinearMap (fderiv ℝ r p))
      (r ⁻¹' U) := by
  let eF := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := ℝ × Model d) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  let eE := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := Model 1 × Model d) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  have hc := hB.comp hr.contDiffOn (fun _ hp => hp)
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ r) (r ⁻¹' U) :=
    (hr.fderiv_right (m := ∞) (by simp)).contDiffOn
  have hs := eE.contDiff.comp_contDiffOn
    ((eF.symm.contDiff.comp_contDiffOn hc).clm_comp hd)
  convert hs using 1
  · ext p vs
    change (B (r p)) (fun i => fderiv ℝ r p (vs i)) =
      (B (r p)) (fun _ => fderiv ℝ r p (vs 0))
    congr 1
    funext i
    rw [Fin.eq_zero i]
  · rfl

/-- A real coefficient extension on an actual interval-product patch
produces a real open coefficient germ in a chart of the original smooth
structure. The native patch is used through its full differential. -/
theorem exists_realOpenCovectorCoefficientsAt_intervalPatch
    (Ω : (x : X) → TangentSpace (familyModel d) x [⋀^Fin 1]→L[ℝ] ℝ)
    (j : Parameter × M.Point → X) (hj : IsOpenEmbedding j)
    (hjs : ContMDiff (familyModel d) (familyModel d) ∞ j)
    (hcharts : ∀ p : Parameter × M.Point,
      (chartAt (ModelProd (EuclideanHalfSpace 1) (Model d)) p).lift_openEmbedding hj ∈
        _root_.atlas (ModelProd (EuclideanHalfSpace 1) (Model d)) X)
    (A : Set M.Point)
    (hΩ : M.HasRealIntervalCovectorCoefficientsOn
      (fun p => (Ω (j p)).compContinuousLinearMap
        (mfderiv (familyModel d) (familyModel d) j p)) A)
    (p : Parameter × M.Point) (hp : p.2 ∈ A) :
    ∃ e : OpenPartialHomeomorph X (ModelProd (EuclideanHalfSpace 1) (Model d)),
      e ∈ IsManifold.maximalAtlas (familyModel d) ∞ X ∧ j p ∈ e.source ∧
      ∃ (U : Set (Model 1 × Model d))
        (B : Model 1 × Model d → (Model 1 × Model d) [⋀^Fin 1]→L[ℝ] ℝ),
        IsOpen U ∧ e.extend (familyModel d) (j p) ∈ U ∧ ContDiffOn ℝ ∞ B U ∧
        ∀ z ∈ e.source, e.extend (familyModel d) z ∈ U →
          Ω z = (B (e.extend (familyModel d) z)).compContinuousLinearMap
            (mfderiv (familyModel d) 𝓘(ℝ, Model 1 × Model d)
              (e.extend (familyModel d)) z) := by
  let c := chartAt (Model d) p.2
  let e : OpenPartialHomeomorph (Parameter × M.Point)
      (ModelProd (EuclideanHalfSpace 1) (Model d)) :=
    (chartAt (EuclideanHalfSpace 1) p.1).prod c
  let f : OpenPartialHomeomorph X (ModelProd (EuclideanHalfSpace 1) (Model d)) :=
    e.lift_openEmbedding hj
  have he : e ∈ _root_.atlas (ModelProd (EuclideanHalfSpace 1) (Model d))
      (Parameter × M.Point) := chart_mem_atlas _ p
  have hf : f ∈ _root_.atlas (ModelProd (EuclideanHalfSpace 1) (Model d)) X := hcharts p
  have hfm := IsManifold.subset_maximalAtlas (I := familyModel d) (n := ∞) hf
  have hep : p ∈ e.source := ⟨mem_chart_source (EuclideanHalfSpace 1) p.1,
    mem_chart_source (Model d) p.2⟩
  have hfp : j p ∈ f.source := ⟨p, hep, rfl⟩
  have hfe : (f.extend (familyModel d)) ∘ j = e.extend (familyModel d) := by
    funext q
    exact congrArg (familyModel d) (OpenPartialHomeomorph.lift_openEmbedding_apply e hj)
  rcases hΩ with ⟨hA, hΩ⟩
  obtain ⟨B, hBNear, heq⟩ := hΩ p.2
  obtain ⟨U₀, hU₀, hcover, hB⟩ := hBNear
  let S := U₀ ∩ (univ ×ˢ (c.target ∩ c.symm ⁻¹' A))
  have hS : IsOpen S := hU₀.inter (isOpen_univ.prod
    (c.continuousOn_symm.isOpen_inter_preimage c.open_target hA))
  have hpS : (p.1.val, c p.2) ∈ S := by
    refine ⟨hcover ⟨p.1.property, c.map_source (mem_chart_source _ _)⟩,
      mem_univ _, c.map_source (mem_chart_source _ _), ?_⟩
    change c.symm (c p.2) ∈ A
    rwa [c.left_inv (mem_chart_source _ _)]
  let r := intervalChartRealInverse (d := d) p.1
  have hr := contDiff_intervalChartRealInverse (d := d) p.1
  let U := r ⁻¹' S
  let D := fun y => (B (r y)).compContinuousLinearMap (fderiv ℝ r y)
  have hU : IsOpen U := hS.preimage hr.continuous
  have hpU : f.extend (familyModel d) (j p) ∈ U := by
    change r ((f.extend (familyModel d) ∘ j) p) ∈ S
    rw [hfe]
    have hrp : r (e.extend (familyModel d) p) = (p.1.val, c p.2) :=
      intervalChartRealInverse_extend M p.1 p.2 p
    exact hrp.symm ▸ hpS
  refine ⟨f, hfm, hfp, U, D, hU, hpU,
    contDiffOn_covector_coordinate_pullback B S (hB.mono inter_subset_left) r hr, ?_⟩
  intro z hz hzU
  obtain ⟨q, hqe, rfl⟩ := hz
  have hqf : j q ∈ f.source := ⟨q, hqe, rfl⟩
  have hqc : q.2 ∈ c.source := hqe.2
  have hfr : r (f.extend (familyModel d) (j q)) = (q.1.val, c q.2) := by
    change r ((f.extend (familyModel d) ∘ j) q) = _
    rw [hfe]
    exact intervalChartRealInverse_extend M p.1 p.2 q
  have hqS : (q.1.val, c q.2) ∈ S := hfr ▸ hzU
  have hdE : mfderiv (familyModel d) 𝓘(ℝ, Model 1 × Model d)
      (e.extend (familyModel d)) q =
        (mfderiv (familyModel d) 𝓘(ℝ, Model 1 × Model d)
          (f.extend (familyModel d)) (j q)).comp
            (mfderiv (familyModel d) (familyModel d) j q) := by
    rw [← hfe]
    exact mfderiv_comp q
      ((f.contMDiffAt_extend hfm hqf).mdifferentiableAt (by simp))
      ((hjs q).mdifferentiableAt (by simp))
  have hjSurj : Function.Surjective (mfderiv (familyModel d) (familyModel d) j q) := by
    have hEi := isInvertible_mfderiv_extend (I := familyModel d)
      (IsManifold.subset_maximalAtlas (n := 1) he) hqe
    have hFi := isInvertible_mfderiv_extend (I := familyModel d)
      (IsManifold.subset_maximalAtlas (n := 1) hf) hqf
    intro v
    obtain ⟨w, hw⟩ := hEi.surjective
      (mfderiv (familyModel d) 𝓘(ℝ, Model 1 × Model d)
        (f.extend (familyModel d)) (j q) v)
    refine ⟨w, hFi.bijective.1 ?_⟩
    rw [hdE] at hw
    exact hw
  let ν : Parameter × M.Point → ℝ × Model d := fun w => (w.1.val, c w.2)
  have hrE : r ∘ (e.extend (familyModel d)) = ν := by
    funext w
    exact intervalChartRealInverse_extend M p.1 p.2 w
  have hdν : mfderiv (familyModel d) ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ν q =
      (fderiv ℝ r (e.extend (familyModel d) q)).comp
        (mfderiv (familyModel d) 𝓘(ℝ, Model 1 × Model d)
          (e.extend (familyModel d)) q) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod, ← hrE]
    rw [mfderiv_comp q (hr.contMDiff.mdifferentiableAt (by simp))
      ((e.contMDiffAt_extend (IsManifold.subset_maximalAtlas (n := ∞) he) hqe).mdifferentiableAt (by simp)),
      mfderiv_eq_fderiv]
  have hrec := M.intervalCovectorInChart_reconstruct
    (fun w => (Ω (j w)).compContinuousLinearMap
      (mfderiv (familyModel d) (familyModel d) j w)) p.2 q hqc
  have hcoeff := heq q.1 (c q.2) (c.map_source hqc) hqS.2.2.2
  rw [hcoeff] at hrec
  have hcomp : (Ω (j q)).compContinuousLinearMap
      (mfderiv (familyModel d) (familyModel d) j q) =
        ((D (f.extend (familyModel d) (j q))).compContinuousLinearMap
          (mfderiv (familyModel d) 𝓘(ℝ, Model 1 × Model d)
            (f.extend (familyModel d)) (j q))).compContinuousLinearMap
              (mfderiv (familyModel d) (familyModel d) j q) := by
    rw [hrec]
    ext vs
    dsimp only [D]
    erw [hfr]
    have hvalue := congrFun hfe q
    change f.extend (familyModel d) (j q) = e.extend (familyModel d) q at hvalue
    erw [hvalue, hdν, hdE]
    rfl
  ext vs
  let ws := fun i : Fin 1 => (hjSurj (vs i)).choose
  have hws : ∀ i, mfderiv (familyModel d) (familyModel d) j q (ws i) = vs i :=
    fun i => (hjSurj (vs i)).choose_spec
  have hh := congrArg (fun L => L ws) hcomp
  change (Ω (j q)) (fun i => mfderiv (familyModel d) (familyModel d) j q (ws i)) =
    (D (f.extend (familyModel d) (j q))) (fun i =>
      mfderiv (familyModel d) 𝓘(ℝ, Model 1 × Model d)
        (f.extend (familyModel d)) (j q)
          (mfderiv (familyModel d) (familyModel d) j q (ws i))) at hh
  change (Ω (j q)) vs = (D (f.extend (familyModel d) (j q)))
    (fun i => mfderiv (familyModel d) 𝓘(ℝ, Model 1 × Model d)
      (f.extend (familyModel d)) (j q) (vs i))
  simpa only [hws] using hh

end IntervalPatch

namespace IntrinsicCompletionGluing

variable {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Interior and seam/outward strip coefficients supply actual real open
coefficient germs at every point of the original completed family. The
same covector is retained and its full native tangent fiber is identified. -/
theorem hasRealOpenCovectorCoefficients_totalFamily_of_patches
    {δ : ℝ} (hδ : 0 < δ)
    (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
    (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
      (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
    (hzero : ∀ t x, C t (0, x) = x.val)
    (hjoint : IsOpenEmbedding (totalCollar
      (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
    (hmix : HasRealMixedGerms (δ := δ) C)
    (cutoff : ℝ) (hcutoff : cutoff < 0)
    (Ω : letI := totalFamilyChartedSpace hδ C hzero hjoint
      (z : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) →
        TangentSpace (familyModel (k + 1)) z [⋀^Fin 1]→L[ℝ] ℝ) :
    letI := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) δ
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
    (IntrinsicInterior.smoothManifold k M).HasRealIntervalCovectorCoefficientsOn
      (fun p => (Ω (totalInterior c p)).compContinuousLinearMap
        (mfderiv (familyModel (k + 1)) (familyModel (k + 1)) (totalInterior c) p)) univ →
    (bandManifold δ (IntrinsicBoundary.smoothManifold k M)).HasRealIntervalCovectorCoefficientsOn
      (fun p => (Ω (totalCylinder c p)).compContinuousLinearMap
        (mfderiv (familyModel (k + 1)) (familyModel (k + 1)) (totalCylinder c) p))
      {p | cutoff < -p.val.1} →
    HasRealOpenCovectorCoefficients (familyModel (k + 1)) Ω := by
  let := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) δ
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let := totalFamily_isManifold hδ C hboundary hzero hjoint hmix
  let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
  dsimp only
  intro hInterior hCylinder z
  rcases totalInterior_cylinder_strip_cover hδ C hboundary hzero cutoff hcutoff z with
    ⟨p, rfl⟩ | ⟨p, hp, rfl⟩
  · apply exists_realOpenCovectorCoefficientsAt_intervalPatch
      (IntrinsicInterior.smoothManifold k M) Ω (totalInterior c)
      (isOpenEmbedding_totalInterior hδ c hzero hjoint)
      (contMDiff_totalInterior hδ C hboundary hzero hjoint hmix)
      (A := univ) (hΩ := hInterior) (p := p) (hp := mem_univ _)
    intro q
    change _ ∈ RelativeOpenCover.atlas _ _
    exact Or.inl ⟨chartAt (ModelProd (EuclideanHalfSpace 1) (Model (k + 1))) q,
      chart_mem_atlas _ q, rfl⟩
  · apply exists_realOpenCovectorCoefficientsAt_intervalPatch
      (bandManifold δ (IntrinsicBoundary.smoothManifold k M)) Ω (totalCylinder c)
      (isOpenEmbedding_totalCylinder c hjoint)
      (contMDiff_totalCylinder hδ C hboundary hzero hjoint hmix)
      (A := {p | cutoff < -p.val.1}) (hΩ := hCylinder) (p := p) (hp := hp)
    intro q
    change _ ∈ RelativeOpenCover.atlas _ _
    exact Or.inr ⟨chartAt (ModelProd (EuclideanHalfSpace 1) (Model (k + 1))) q,
      chart_mem_atlas _ q, rfl⟩

end IntrinsicCompletionGluing
end FsFltz.Geometry
