import FsFltz.Analysis.TailoringCriticalToriInertiaGlobal
import FsFltz.Geometry.LocalCovers

/-!
# Native logarithmic charts and the face Hessian

Source: `geometric-part-fsf-proof.tex`, `prop:morsebott`, `eq:hessian`,
lines 1538–1570, and `lem:stable`, lines 1703–1725. The logarithmic
parametrization is constructed from an actual embedded fiber chart.
No local trapping or full-core equality is assumed or asserted here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set Filter Function
open scoped Topology BigOperators ContDiff Manifold

section LocalComposition

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The stationary Hessian chain rule requires only local smoothness. -/
theorem fderiv_fderiv_comp_of_stationary_at {f : E → ℝ} {g : F → E}
    (x V W : F) (hf : ContDiffAt ℝ ∞ f (g x)) (hg : ContDiffAt ℝ ∞ g x)
    (hstationary : fderiv ℝ f (g x) = 0) :
    fderiv ℝ (fderiv ℝ (f ∘ g)) x V W =
      fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x V) (fderiv ℝ g x W) := by
  have hfg : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ f (g z) :=
    hg.continuousAt.tendsto.eventually
      (((hf.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).eventually (by simp)).mono
        fun _ hz => hz.differentiableAt_one)
  have hgg : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ g z :=
    ((hg.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).eventually (by simp)).mono
      fun _ hz => hz.differentiableAt_one
  have he : fderiv ℝ (f ∘ g) =ᶠ[𝓝 x]
      fun z => (fderiv ℝ f (g z)).comp (fderiv ℝ g z) := by
    filter_upwards [hfg, hgg] with z hfz hgz
    exact fderiv_comp z hfz hgz
  have hDf := ((hf.fderiv_right (m := 1) (by simp)).differentiableAt_one.hasFDerivAt.comp x
    (hg.differentiableAt (by simp)).hasFDerivAt)
  have hDg := (hg.fderiv_right (m := 1) (by simp)).differentiableAt_one.hasFDerivAt
  have hd := hDf.clm_comp hDg
  simp only [Function.comp_def] at hd
  rw [he.fderiv_eq, hd.fderiv]
  simp [hstationary]

end LocalComposition

/-- The literal constrained Hessian formula also holds for a parametrization
smooth only at the point under consideration. -/
theorem criticalFace_parametrization_hessian_at {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (s : Finset (Lattice n)) (β lam : ℝ)
    {g : F → TangentCoordinates n} (a V : F) (hg : ContDiffAt ℝ ∞ g a)
    (hlevel : ∀ᶠ z in 𝓝 a, criticalFaceFunction s β (g z) = 1)
    (hreal : ∀ v ∈ s, (monomial (Real.exp (-β) : ℂ) v ((g a).1, angleQuotient (g a).2)).im = 0)
    (hcritical : coordinateGradient φ (g a).1 = lam • ∑ v ∈ s,
      (monomial (Real.exp (-β) : ℂ) v ((g a).1, angleQuotient (g a).2)).re • latticeReal v) :
    fderiv ℝ (fun z => φ (g z).1) a = 0 ∧
      fderiv ℝ (fderiv ℝ (fun z => φ (g z).1)) a V V =
        fderiv ℝ (fderiv ℝ φ) (g a).1 (fderiv ℝ g a V).1 (fderiv ℝ g a V).1 -
          lam * criticalFaceGram s
            (fun v => (monomial (Real.exp (-β) : ℂ) v ((g a).1, angleQuotient (g a).2)).re)
            (fderiv ℝ g a V).1 +
          lam * criticalFaceGram s
            (fun v => (monomial (Real.exp (-β) : ℂ) v ((g a).1, angleQuotient (g a).2)).re)
            (fderiv ℝ g a V).2 := by
  let L := criticalFaceLagrangian φ s β lam
  have hLs : ContDiff ℝ ∞ L := contDiff_criticalFaceLagrangian hφ s β lam
  have hstationary : fderiv ℝ L (g a) = 0 :=
    fderiv_criticalFaceLagrangian_eq_zero s β lam (g a)
      (hφ.differentiable (by simp) _) hreal hcritical
  have hshift : (fun z => φ (g z).1) =ᶠ[𝓝 a] (fun z => L (g z) + lam) := by
    filter_upwards [hlevel] with z hz
    dsimp [L, criticalFaceLagrangian]
    rw [hz, Complex.one_re]
    ring
  have hfirst : fderiv ℝ (fun z => φ (g z).1) =ᶠ[𝓝 a] fderiv ℝ (L ∘ g) := by
    filter_upwards [hshift.fderiv (𝕜 := ℝ)] with z hz
    rw [hz, fderiv_add_const]
    rfl
  constructor
  · rw [hfirst.eq_of_nhds, fderiv_comp a (hLs.differentiable (by simp) _)
      (hg.differentiableAt (by simp)), hstationary, ContinuousLinearMap.zero_comp]
  · rw [hfirst.fderiv_eq,
      fderiv_fderiv_comp_of_stationary_at a V V hLs.contDiffAt hg hstationary]
    exact fderiv_fderiv_criticalFaceLagrangian hφ s β lam (g a) (fderiv ℝ g a V) hreal

/-- Equality with a homogeneous end germ transfers the local-chart Hessian. -/
theorem criticalFace_parametrization_hessian_at_of_potential_germ {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ ψ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (s : Finset (Lattice n)) (β lam : ℝ) (q : s → ℝ)
    {g : F → TangentCoordinates n} (a V : F) (hg : ContDiffAt ℝ ∞ g a)
    (hlevel : ∀ᶠ w in 𝓝 a, criticalFaceFunction s β (g w) = 1)
    (heq : φ =ᶠ[𝓝 (g a).1] ψ)
    (hmon : ∀ v : s,
      monomial (Real.exp (-β) : ℂ) v.val ((g a).1, angleQuotient (g a).2) = (q v : ℂ))
    (hcritical : coordinateGradient ψ (g a).1 = lam • faceNormalMap s q) :
    fderiv ℝ (fun w => φ (g w).1) a = 0 ∧
      fderiv ℝ (fderiv ℝ (fun w => φ (g w).1)) a V V =
        faceConstrainedHessian s (fderiv ℝ (coordinateGradient ψ) (g a).1) q lam
          (fderiv ℝ g a V) := by
  have hreal : ∀ v ∈ s,
      (monomial (Real.exp (-β) : ℂ) v ((g a).1, angleQuotient (g a).2)).im = 0 := by
    intro v hv
    rw [hmon ⟨v, hv⟩]
    rfl
  have hweights : (fun v => (monomial (Real.exp (-β) : ℂ) v
      ((g a).1, angleQuotient (g a).2)).re) =ᶠ[Filter.principal (s : Set (Lattice n))]
      faceCoordinateExtend s q := by
    rw [Filter.eventuallyEq_principal]
    intro v hv
    dsimp only
    rw [hmon ⟨v, hv⟩]
    simpa only [Complex.ofReal_re] using (faceCoordinateExtend_apply s q ⟨v, hv⟩).symm
  have hnormal : coordinateGradient φ (g a).1 = lam • ∑ v ∈ s,
      (monomial (Real.exp (-β) : ℂ) v ((g a).1, angleQuotient (g a).2)).re • latticeReal v := by
    rw [coordinateGradient_eq_of_eventuallyEq heq, hcritical, faceNormalMap_eq_extended_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro v hv
    congr 1
    exact (Filter.eventuallyEq_principal.mp hweights) hv |>.symm
  obtain ⟨hfirst, hsecond⟩ := criticalFace_parametrization_hessian_at hφ s β lam a V hg
    hlevel hreal hnormal
  refine ⟨hfirst, ?_⟩
  rw [hsecond, second_fderiv_eq_coordinate_hessian (hφ.differentiable (by simp)) hφ.contDiffAt,
    coordinateHessian_eq_of_eventuallyEq heq]
  have hgram (X : RealSpace n) : criticalFaceGram s
      (fun v => (monomial (Real.exp (-β) : ℂ) v ((g a).1, angleQuotient (g a).2)).re) X =
        faceWeightSquare q (faceLevelMap s X) := by
    rw [← criticalFaceGram_eq_faceWeightSquare]
    apply Finset.sum_congr rfl
    intro v hv
    rw [(Filter.eventuallyEq_principal.mp hweights) hv]
  rw [hgram, hgram]
  rfl


/-- An actual embedded manifold chart has a smooth logarithmic lift at
each chosen representative. Its germ is fixed by the quotient cover. -/
theorem exists_logarithmic_chart_lift {n d : ℕ} (N : SmoothManifold d)
    (j : N.SmoothEmbedding (lgManifold n)) (a : N.Point)
    (x : TangentCoordinates n) (hpoint : j.map a = lgCover x) :
    ∃ g : Model d → TangentCoordinates n,
      ContDiffAt ℝ ∞ g (chartAt (Model d) a a) ∧
      g (chartAt (Model d) a a) = x ∧
      (∀ᶠ y in 𝓝 (chartAt (Model d) a a),
        lgCover (g y) = j.map ((chartAt (Model d) a).symm y)) := by
  let c := chartAt (Model d) a
  let l := isLocalDiffeomorph_lgCover n x
  let k : Model d → (lgManifold n).Point := j.map ∘ c.symm
  have hc : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ c.symm (c a) :=
    contMDiffOn_chart_symm.contMDiffAt (c.open_target.mem_nhds
      (c.map_source (mem_chart_source (Model d) a)))
  have hca : c.symm (c a) = a := c.left_inv (mem_chart_source (Model d) a)
  have hk : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) ∞ k (c a) :=
    j.map.contMDiff.contMDiffAt.comp (c a) hc
  have hka : k (c a) = lgCover x := by dsimp [k]; rw [hca, hpoint]
  have hl : ContMDiffAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, TangentCoordinates n) ∞
      l.localInverse (k (c a)) := hka.symm ▸ l.localInverse_contMDiffAt
  refine ⟨l.localInverse ∘ k, (hl.comp (c a) hk).contDiffAt, ?_, ?_⟩
  · change l.localInverse (k (c a)) = x
    rw [hka]
    exact l.localInverse_left_inv l.localInverse_mem_target
  · have he := hk.continuousAt.tendsto.eventually
      (hka.symm ▸ l.localInverse_eventuallyEq_right)
    exact he

/-- The differential of the constructed lift is the actual inclusion
differential composed with the actual inverse-chart differential. -/
theorem logarithmic_chart_lift_tangent {n d : ℕ} (N : SmoothManifold d)
    (j : N.SmoothEmbedding (lgManifold n)) (a : N.Point)
    (x : TangentCoordinates n) {g : Model d → TangentCoordinates n}
    (hg : ContDiffAt ℝ ∞ g (chartAt (Model d) a a))
    (hga : g (chartAt (Model d) a a) = x)
    (heq : ∀ᶠ y in 𝓝 (chartAt (Model d) a a),
      lgCover (g y) = j.map ((chartAt (Model d) a).symm y)) :
    (lgCoverTangent x).comp (fderiv ℝ g (chartAt (Model d) a a)) =
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) j.map a).comp
        (N.inverseChartTangentMap a (chartAt (Model d) a a)) := by
  let c := chartAt (Model d) a
  have hc : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ c.symm (c a) :=
    contMDiffOn_chart_symm.contMDiffAt (c.open_target.mem_nhds
      (c.map_source (mem_chart_source (Model d) a)))
  have hca : c.symm (c a) = a := c.left_inv (mem_chart_source (Model d) a)
  have he : (lgCover ∘ g) =ᶠ[𝓝 (c a)] (j.map ∘ c.symm) := heq
  have hd := he.mfderiv_eq (I := 𝓘(ℝ, Model d)) (I' := 𝓘(ℝ, Model (2 * n)))
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) (lgCover ∘ g) (c a) =
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) (j.map ∘ c.symm) (c a) at hd
  rw [mfderiv_comp (c a) ((contMDiff_lgCover n).mdifferentiable (by simp) _)
      (hg.contMDiffAt.mdifferentiableAt (by simp)),
    mfderiv_comp (c a) (j.map.contMDiff.mdifferentiable (by simp) _)
      (hc.mdifferentiableAt (by simp)), mfderiv_eq_fderiv, hga, hca] at hd
  exact hd

/-- The lift of an embedded chart has injective differential, including
zero-dimensional source charts. -/
theorem logarithmic_chart_lift_immersion {n d : ℕ} (N : SmoothManifold d)
    (j : N.SmoothEmbedding (lgManifold n)) (a : N.Point)
    (x : TangentCoordinates n) {g : Model d → TangentCoordinates n}
    (hg : ContDiffAt ℝ ∞ g (chartAt (Model d) a a))
    (hga : g (chartAt (Model d) a a) = x)
    (heq : ∀ᶠ y in 𝓝 (chartAt (Model d) a a),
      lgCover (g y) = j.map ((chartAt (Model d) a).symm y)) :
    Injective (fderiv ℝ g (chartAt (Model d) a a)) := by
  have hchart := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).symm.mfderiv_bijective
    ((chartAt (Model d) a).map_source (mem_chart_source (Model d) a))
  have hd := logarithmic_chart_lift_tangent N j a x hg hga heq
  intro V W hVW
  apply hchart.1
  apply j.immersion a
  have h := congrArg (fun L : Model d →L[ℝ] Model (2 * n) => L V - L W) hd
  change lgCoverTangent x (fderiv ℝ g (chartAt (Model d) a a) V) -
      lgCoverTangent x (fderiv ℝ g (chartAt (Model d) a a) W) = _ at h
  rw [hVW, sub_self] at h
  exact sub_eq_zero.mp h.symm

/-- The actual fiber-chart Hessian is the constrained face Hessian of the
same global potential. The logarithmic parametrization is constructed;
the local face equation and normal equation are the analytic producers. -/
theorem tailoring_fullFiber_exists_native_hessian_chart {n d : ℕ}
    (I : ToricInput n) (β : ℝ) {φ ψ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (s : Finset (Lattice n)) (lam : ℝ) (q : s → ℝ)
    (N : SmoothManifold d) (j : N.SmoothEmbedding (lgManifold n))
    (himage : range j.map = {y | tailoringFamily I β 1 y = 1})
    (a : N.Point) (x : TangentCoordinates n) (hpoint : j.map a = lgCover x)
    (hlocal : ∀ᶠ y in 𝓝 (j.map a),
      tailoringFamily I β 1 y = ∑ v ∈ s, monomial (Real.exp (-β) : ℂ) v y)
    (hpot : φ =ᶠ[𝓝 x.1] ψ)
    (hmon : ∀ v : s, monomial (Real.exp (-β) : ℂ) v.val (lgCover x) = (q v : ℂ))
    (hcritical : coordinateGradient ψ x.1 = lam • faceNormalMap s q) :
    ∃ g : Model d → TangentCoordinates n,
      ContDiffAt ℝ ∞ g (chartAt (Model d) a a) ∧
      g (chartAt (Model d) a a) = x ∧
      (∀ᶠ y in 𝓝 (chartAt (Model d) a a),
        lgCover (g y) = j.map ((chartAt (Model d) a).symm y)) ∧
      Injective (fderiv ℝ g (chartAt (Model d) a a)) ∧
      (lgCoverTangent x).comp (fderiv ℝ g (chartAt (Model d) a a)) =
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) j.map a).comp
          (N.inverseChartTangentMap a (chartAt (Model d) a a)) ∧
      (fderiv ℝ (fun y => φ (j.map ((chartAt (Model d) a).symm y)).1)
        (chartAt (Model d) a a) = 0) ∧
      ∀ V : Model d,
        fderiv ℝ (fderiv ℝ (fun y => φ (j.map ((chartAt (Model d) a).symm y)).1))
            (chartAt (Model d) a a) V V =
          faceConstrainedHessian s (fderiv ℝ (coordinateGradient ψ) x.1) q lam
            (fderiv ℝ g (chartAt (Model d) a a) V) := by
  obtain ⟨g, hg, hga, heq⟩ := exists_logarithmic_chart_lift N j a x hpoint
  let c := chartAt (Model d) a
  change g (c a) = x at hga
  have hc : ContinuousAt (lgCover ∘ g) (c a) :=
    (contMDiff_lgCover n).continuous.continuousAt.comp hg.continuousAt
  have hcenter : lgCover (g (c a)) = j.map a := by rw [hga, hpoint]
  have hlevel : ∀ᶠ y in 𝓝 (c a), criticalFaceFunction s β (g y) = 1 := by
    have hnear := hc.tendsto.eventually (hcenter.symm ▸ hlocal)
    filter_upwards [hnear, heq] with y hy hcover
    change (∑ v ∈ s, monomial (Real.exp (-β) : ℂ) v (lgCover (g y))) = 1
    have hmem : j.map (c.symm y) ∈ range j.map := ⟨c.symm y, rfl⟩
    rw [himage] at hmem
    exact hy.symm.trans ((congrArg (tailoringFamily I β 1) hcover).trans hmem)
  have hφeq : (fun y => φ (g y).1) =ᶠ[𝓝 (c a)]
      (fun y => φ (j.map (c.symm y)).1) := by
    filter_upwards [heq] with y hy
    exact congrArg (fun z : LGSpace n => φ z.1) hy
  have hh (V : Model d) := criticalFace_parametrization_hessian_at_of_potential_germ
    hφ s β lam q (c a) V hg hlevel (hga.symm ▸ hpot)
    (by rw [hga]; exact hmon) (by rw [hga]; exact hcritical)
  refine ⟨g, hg, hga, heq, logarithmic_chart_lift_immersion N j a x hg hga heq,
    logarithmic_chart_lift_tangent N j a x hg hga heq, ?_, ?_⟩
  · rw [← hφeq.fderiv_eq]
    exact (hh 0).1
  · intro V
    rw [← hφeq.fderiv.fderiv_eq]
    simpa only [hga] using (hh V).2

end FsFltz
