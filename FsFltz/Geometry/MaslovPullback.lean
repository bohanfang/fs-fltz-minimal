import FsFltz.Geometry.GradingRepresentatives
import FsFltz.Geometry.LiouvilleNaturality

/-!
# Maslov representatives under actual smooth markings

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244;
`thm:target` / `g:chain`, lines 407–413; `sec:lean`, lines 794–814.
Pullback uses the derivative of the specified diffeomorphism and its actual
inverse. The rank-one canonical-bundle identification and invariance under
changing compatible complex structures remain separate foundations.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry

set_option backward.isDefEq.respectTransparency false in
/-- The actual derivatives of a smooth marking and its inverse are inverse. -/
theorem marking_mfderiv_inverse_left {d : ℕ} (M N : SmoothManifold d)
    (f : M.SmoothEquiv N) (x : M.Point) :
    (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) f.invFun (f x)).comp
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) f x) =
        ContinuousLinearMap.id ℝ (M.Tangent x) := by
  have hcomp : (f.symm ∘ f : M.Point → M.Point) = id := by
    funext y
    exact f.left_inv y
  have h := mfderiv_comp x (f.symm.mdifferentiable (by simp) (f x))
    (f.mdifferentiable (by simp) x)
  rw [hcomp, mfderiv_id] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
theorem marking_mfderiv_inverse_right {d : ℕ} (M N : SmoothManifold d)
    (f : M.SmoothEquiv N) (x : M.Point) :
    (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) f x).comp
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) f.invFun (f x)) =
        ContinuousLinearMap.id ℝ (N.Tangent (f x)) := by
  have hcomp : (f ∘ f.symm : N.Point → N.Point) = id := by
    funext y
    exact f.right_inv y
  have h := mfderiv_comp (f x)
    (f.mdifferentiable (by simp) (f.symm (f x)))
    (f.symm.mdifferentiable (by simp) (f x))
  rw [f.symm_apply_apply x, hcomp, mfderiv_id] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
/-- The pulled-back complex structure intertwines the marking derivative. -/
theorem pullbackAlmostComplex_intertwines {n : ℕ} (M N : SmoothManifold (2 * n))
    (f : M.SmoothEquiv N) (J : AlmostComplexField N) (x : M.Point) (v : M.Tangent x) :
    mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x
      (pullbackAlmostComplex M N f J x v) =
        J (f x) (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x v) := by
  exact congrArg (fun L => L
    (J (f x) (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x v)))
      (marking_mfderiv_inverse_right M N f x)

set_option backward.isDefEq.respectTransparency false in
/-- Separate alternation and complex linearity survive an actual marking. -/
theorem pullbackSquaredTensor_canonical {n : ℕ} (M N : SmoothManifold (2 * n))
    (f : M.SmoothEquiv N) (J : AlmostComplexField N)
    (s : N.Point → SquaredCanonicalTensor n)
    (hs : ∀ x, IsSquaredCanonicalTensor (J x) (s x)) (x : M.Point) :
    IsSquaredCanonicalTensor (pullbackAlmostComplex M N f J x)
      (pullbackSquaredTensor M N f s x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v i j hij hv
    exact (hs (f x)).1 _ i j hij (congrArg
      (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x) hv)
  · intro v i j hij hv
    exact (hs (f x)).2.1 _ i j hij (congrArg
      (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x) hv)
  · intro v i
    classical
    let D := mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x
    have hu : (fun k => D (Function.update v i
        (pullbackAlmostComplex M N f J x (v i)) k)) =
          Function.update (fun k => D (v k)) i (J (f x) (D (v i))) := by
      funext k
      by_cases hk : k = i
      · subst k
        simp only [Function.update_self]
        exact pullbackAlmostComplex_intertwines M N f J x (v i)
      · simp only [Function.update_of_ne hk]
    change s (f x) (fun k => D (Function.update v i
      (pullbackAlmostComplex M N f J x (v i)) k)) =
        Complex.I * s (f x) (fun k => D (v k))
    rw [hu]
    exact (hs (f x)).2.2 _ i

set_option backward.isDefEq.respectTransparency false in
/-- Nonvanishing survives a marking because every tangent frame pulls back. -/
theorem pullbackSquaredTensor_ne_zero {n : ℕ} (M N : SmoothManifold (2 * n))
    (f : M.SmoothEquiv N) (s : N.Point → SquaredCanonicalTensor n)
    (hs : ∀ x, s x ≠ 0) (x : M.Point) :
    pullbackSquaredTensor M N f s x ≠ 0 := by
  intro h
  apply hs (f x)
  ext v
  have hv := congrArg (fun t : SquaredCanonicalTensor n => t
    (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n))
      f.invFun (f x) (v i))) h
  have hi (i : Fin n ⊕ Fin n) :
      mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f.invFun (f x) (v i)) = v i :=
    congrArg (fun L => L (v i)) (marking_mfderiv_inverse_right M N f x)
  change s (f x) (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x
    (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f.invFun (f x) (v i))) = 0 at hv
  have he : (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x
    (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f.invFun (f x) (v i))) = v :=
      funext hi
  exact (congrArg (s (f x)) he).symm.trans hv

set_option backward.isDefEq.respectTransparency false in
/-- The chart expression of the actual tangent pullback. -/
theorem squaredTensorInChart_pullback {n : ℕ} (M N : SmoothManifold (2 * n))
    (f : M.SmoothEquiv N) (s : N.Point → SquaredCanonicalTensor n)
    (a : M.Point) (b : N.Point) (y : Model (2 * n))
    (hy : y ∈ (chartAt (Model (2 * n)) a).target)
    (hb : f ((chartAt (Model (2 * n)) a).symm y) ∈
      (chartAt (Model (2 * n)) b).source) :
    squaredTensorInChart M a (pullbackSquaredTensor M N f s) y =
      (squaredTensorInChart N b s
        (chartAt (Model (2 * n)) b (f ((chartAt (Model (2 * n)) a).symm y)))).compContinuousLinearMap (fun _ =>
            fderiv ℝ (chartAt (Model (2 * n)) b ∘ f ∘
              (chartAt (Model (2 * n)) a).symm) y) := by
  rw [← mfderiv_eq_fderiv]
  have hca := (mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n))) a).mdifferentiableAt_symm hy
  have hcb := (mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n))) b).mdifferentiableAt hb
  have hf := f.mdifferentiable (by simp) ((chartAt (Model (2 * n)) a).symm y)
  rw [mfderiv_comp y hcb (hf.comp y hca), mfderiv_comp y hf hca]
  unfold squaredTensorInChart pullbackSquaredTensor
  rw [(chartAt (Model (2 * n)) b).left_inv hb]
  have hinv := (mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n))) b).symm_comp_deriv hb
  ext v
  apply congrArg (s (f ((chartAt (Model (2 * n)) a).symm y)))
  funext i
  exact (congrArg (fun L => L
    ((mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f
      ((chartAt (Model (2 * n)) a).symm y))
        ((M.inverseChartTangentMap a y) (v i)))) hinv).symm

set_option backward.isDefEq.respectTransparency false in
private theorem contDiffAt_squaredTensor_comp {n : ℕ}
    (a : Model (2 * n) → SquaredCanonicalTensor n)
    (B : Model (2 * n) → Model (2 * n) →L[ℝ] Model (2 * n)) (z : Model (2 * n))
    (ha : ContDiffAt ℝ ∞ a z) (hB : ContDiffAt ℝ ∞ B z) :
    ContDiffAt ℝ ∞ (fun y => (a y).compContinuousLinearMap (fun _ => B y)) z := by
  let C := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
    (fun _ : Fin n ⊕ Fin n => Model (2 * n))
    (fun _ : Fin n ⊕ Fin n => Model (2 * n)) ℂ
  have hC : ContDiff ℝ ∞ (fun L => C L) :=
    ContinuousMultilinearMap.contDiff (𝕜 := ℝ)
      (F := SquaredCanonicalTensor n →L[ℝ] SquaredCanonicalTensor n) C
  have h := hC.contDiffAt.comp z
      (contDiffAt_pi.mpr (fun _ => hB))
  exact h.clm_apply ha

set_option backward.isDefEq.respectTransparency false in
/-- Smoothness of a squared tensor pullback follows from the smooth marking;
no regularity of the resulting section is assumed. -/
theorem isSmoothSquaredTensorSection_pullback {n : ℕ}
    (M N : SmoothManifold (2 * n)) (f : M.SmoothEquiv N)
    (s : N.Point → SquaredCanonicalTensor n) (hs : IsSmoothSquaredTensorSection N s) :
    IsSmoothSquaredTensorSection M (pullbackSquaredTensor M N f s) := by
  intro a y hy
  let c := chartAt (Model (2 * n)) a
  let x := c.symm y
  let b := chartAt (Model (2 * n)) (f x)
  let g := b ∘ f ∘ c.symm
  have hx : f x ∈ b.source := mem_chart_source _ _
  have hA : ContMDiffAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) ∞ c.symm y :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model (2 * n))) (x := a)).contMDiffAt
      (c.open_target.mem_nhds hy)
  have hB : ContMDiffAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) ∞ b (f x) :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model (2 * n))) (x := f x)).contMDiffAt
      (b.open_source.mem_nhds hx)
  have hg : ContDiffAt ℝ ∞ g y :=
    (hB.comp y (f.contMDiff.contMDiffAt.comp y hA)).contDiffAt
  have hcoeff : ContDiffAt ℝ ∞ (squaredTensorInChart N (f x) s) (g y) :=
    (hs (f x)).contDiffAt (b.open_target.mem_nhds (b.map_source hx))
  have hsm := contDiffAt_squaredTensor_comp
    (fun z => squaredTensorInChart N (f x) s (g z)) (fderiv ℝ g) y
    (hcoeff.comp y hg) (hg.fderiv_right (by simp))
  have hnb : ∀ᶠ z in 𝓝 y, f (c.symm z) ∈ b.source :=
    (f.contMDiff.continuous.continuousAt.comp (c.continuousAt_symm hy)).preimage_mem_nhds
      (b.open_source.mem_nhds hx)
  have hlocal : squaredTensorInChart M a (pullbackSquaredTensor M N f s) =ᶠ[𝓝 y]
      fun z => (squaredTensorInChart N (f x) s (g z)).compContinuousLinearMap
        (fun _ => fderiv ℝ g z) := by
    filter_upwards [c.open_target.mem_nhds hy, hnb] with z hz hzb
    exact squaredTensorInChart_pullback M N f s a (f x) z hz hzb
  exact (hsm.congr_of_eventuallyEq hlocal).contDiffWithinAt

set_option backward.isDefEq.respectTransparency false in
/-- Conjugation by the two actual coordinate derivatives computes the
pulled-back complex structure in a chart overlap. -/
theorem almostComplexInChart_pullback {n : ℕ} (M N : SmoothManifold (2 * n))
    (f : M.SmoothEquiv N) (J : AlmostComplexField N)
    (a : M.Point) (b : N.Point) (y : Model (2 * n))
    (hy : y ∈ (chartAt (Model (2 * n)) a).target)
    (hb : f ((chartAt (Model (2 * n)) a).symm y) ∈
      (chartAt (Model (2 * n)) b).source) :
    almostComplexInChart M a (pullbackAlmostComplex M N f J) y =
      (fderiv ℝ (chartAt (Model (2 * n)) a ∘ f.symm ∘
        (chartAt (Model (2 * n)) b).symm)
          (chartAt (Model (2 * n)) b (f ((chartAt (Model (2 * n)) a).symm y)))).comp
        ((almostComplexInChart N b J
          (chartAt (Model (2 * n)) b (f ((chartAt (Model (2 * n)) a).symm y)))).comp
            (fderiv ℝ (chartAt (Model (2 * n)) b ∘ f ∘
              (chartAt (Model (2 * n)) a).symm) y)) := by
  let c := chartAt (Model (2 * n)) a
  let e := chartAt (Model (2 * n)) b
  let x := c.symm y
  have hca := (mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n))) a).mdifferentiableAt_symm hy
  have hcb := (mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n))) b).mdifferentiableAt hb
  have hf := f.mdifferentiable (by simp) x
  have hforward : fderiv ℝ (e ∘ f ∘ c.symm) y =
      (N.chartTangentMap b (f x)).comp
        ((mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x).comp
          (M.inverseChartTangentMap a y)) := by
    rw [← mfderiv_eq_fderiv]
    erw [mfderiv_comp y hcb (hf.comp y hca), mfderiv_comp y hf hca]
    rfl
  have heinv := (mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n))) b).mdifferentiableAt_symm
    (e.map_source hb)
  have hfinv := f.symm.mdifferentiable (by simp) (e.symm (e (f x)))
  have hc : MDifferentiableAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) c
      (f.symm (e.symm (e (f x)))) := by
    rw [e.left_inv hb, f.symm_apply_apply]
    exact (mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n))) a).mdifferentiableAt (c.map_target hy)
  have hbackward : fderiv ℝ (c ∘ f.symm ∘ e.symm) (e (f x)) =
      (M.chartTangentMap a x).comp
        ((mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f.invFun (f x)).comp
          (N.inverseChartTangentMap b (e (f x)))) := by
    rw [← mfderiv_eq_fderiv]
    erw [mfderiv_comp (e (f x)) hc (hfinv.comp _ heinv),
      mfderiv_comp (e (f x)) hfinv heinv]
    simp only [Function.comp_apply]
    erw [e.left_inv hb, f.symm_apply_apply]
    rfl
  change almostComplexInChart M a (pullbackAlmostComplex M N f J) y =
    (fderiv ℝ (c ∘ f.symm ∘ e.symm) (e (f x))).comp
      ((almostComplexInChart N b J (e (f x))).comp (fderiv ℝ (e ∘ f ∘ c.symm) y))
  rw [hforward, hbackward]
  have hinv := (mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n))) b).symm_comp_deriv hb
  apply ContinuousLinearMap.ext
  intro v
  have hi (q : N.Tangent (f x)) : N.inverseChartTangentMap b (e (f x))
      (N.chartTangentMap b (f x) q) = q := congrArg (fun L => L q) hinv
  change (M.chartTangentMap a x)
    ((mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f.invFun (f x))
      (J (f x) ((mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x)
        ((M.inverseChartTangentMap a y) v)))) =
    (M.chartTangentMap a x)
      ((mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f.invFun (f x))
        ((N.inverseChartTangentMap b (e (f x)))
          ((N.chartTangentMap b (e.symm (e (f x))))
            (J (e.symm (e (f x)))
              ((N.inverseChartTangentMap b (e (f x)))
                ((N.chartTangentMap b (f x))
                  ((mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x)
                    ((M.inverseChartTangentMap a y) v))))))))
  rw [e.left_inv hb]
  erw [hi, hi]

set_option backward.isDefEq.respectTransparency false in
/-- Smoothness of the inverse marking and both chart maps proves smoothness
of the pulled-back almost complex field. -/
theorem isSmoothAlmostComplexField_pullback {n : ℕ} (M N : SmoothManifold (2 * n))
    (f : M.SmoothEquiv N) (J : AlmostComplexField N) (hJ : IsSmoothAlmostComplexField N J) :
    IsSmoothAlmostComplexField M (pullbackAlmostComplex M N f J) := by
  intro a y hy
  let c := chartAt (Model (2 * n)) a
  let x := c.symm y
  let b := chartAt (Model (2 * n)) (f x)
  let g := b ∘ f ∘ c.symm
  let h := c ∘ f.symm ∘ b.symm
  have hx : f x ∈ b.source := mem_chart_source _ _
  have hA : ContMDiffAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) ∞ c.symm y :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model (2 * n))) (x := a)).contMDiffAt
      (c.open_target.mem_nhds hy)
  have hB : ContMDiffAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) ∞ b (f x) :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model (2 * n))) (x := f x)).contMDiffAt
      (b.open_source.mem_nhds hx)
  have hg : ContDiffAt ℝ ∞ g y :=
    (hB.comp y (f.contMDiff.contMDiffAt.comp y hA)).contDiffAt
  have hbinv : ContMDiffAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) ∞ b.symm (g y) :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model (2 * n))) (x := f x)).contMDiffAt
      (b.open_target.mem_nhds (b.map_source hx))
  have hc : ContMDiffAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) ∞ c
      (f.symm (b.symm (g y))) := by
    have he : f.symm (b.symm (g y)) = x := by
      change f.symm (b.symm (b (f x))) = x
      rw [b.left_inv hx, f.symm_apply_apply]
    rw [he]
    exact (contMDiffOn_chart (I := 𝓘(ℝ, Model (2 * n))) (x := a)).contMDiffAt
      (c.open_source.mem_nhds (c.map_target hy))
  have hh : ContDiffAt ℝ ∞ h (g y) :=
    (hc.comp (g y) (f.symm.contMDiff.contMDiffAt.comp (g y) hbinv)).contDiffAt
  have hcoeff : ContDiffAt ℝ ∞ (almostComplexInChart N (f x) J) (g y) :=
    (hJ (f x)).contDiffAt (b.open_target.mem_nhds (b.map_source hx))
  have hsm := ((hh.fderiv_right (by simp)).comp y hg).clm_comp
    ((hcoeff.comp y hg).clm_comp (hg.fderiv_right (by simp)))
  have hnb : ∀ᶠ z in 𝓝 y, f (c.symm z) ∈ b.source :=
    (f.contMDiff.continuous.continuousAt.comp (c.continuousAt_symm hy)).preimage_mem_nhds
      (b.open_source.mem_nhds hx)
  have hlocal : almostComplexInChart M a (pullbackAlmostComplex M N f J) =ᶠ[𝓝 y]
      fun z => (fderiv ℝ h (g z)).comp
        ((almostComplexInChart N (f x) J (g z)).comp (fderiv ℝ g z)) := by
    filter_upwards [c.open_target.mem_nhds hy, hnb] with z hz hzb
    exact almostComplexInChart_pullback M N f J a (f x) z hz hzb
  exact (hsm.congr_of_eventuallyEq hlocal).contDiffWithinAt

set_option backward.isDefEq.respectTransparency false in
theorem SmoothManifold.evalTwo_pullback {d : ℕ} (M N : SmoothManifold d)
    (f : M.Point → N.Point) (eta : N.Form 2) (x : M.Point) (v w : M.Tangent x) :
    SmoothManifold.evalTwo (M.pullback N f eta) x v w =
      SmoothManifold.evalTwo eta (f x)
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) f x v)
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) f x w) := by
  apply congrArg (eta (f x))
  funext i
  fin_cases i <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- All compatibility equations follow from tangent conjugation and the
actual two-form pullback. Positivity uses injectivity of the marking derivative. -/
theorem isCompatibleAlmostComplex_pullback {n : ℕ} (M N : SmoothManifold (2 * n))
    (f : M.SmoothEquiv N) (eta : N.Form 2) (J : AlmostComplexField N)
    (hJ : IsCompatibleAlmostComplex N eta J) :
    IsCompatibleAlmostComplex M (M.pullback N f eta) (pullbackAlmostComplex M N f J) := by
  refine ⟨isSmoothAlmostComplexField_pullback M N f J hJ.1, ?_, ?_, ?_⟩
  · intro x v
    apply (f.mfderivToContinuousLinearEquiv (by simp) x).injective
    change mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x
      (pullbackAlmostComplex M N f J x (pullbackAlmostComplex M N f J x v)) =
        mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x (-v)
    rw [pullbackAlmostComplex_intertwines, pullbackAlmostComplex_intertwines,
      hJ.2.1, map_neg]
  · intro x v w
    rw [M.evalTwo_pullback, M.evalTwo_pullback,
      pullbackAlmostComplex_intertwines, pullbackAlmostComplex_intertwines]
    exact hJ.2.2.1 _ _ _
  · intro x v hv
    rw [M.evalTwo_pullback, pullbackAlmostComplex_intertwines]
    apply hJ.2.2.2
    intro hzero
    apply hv
    apply (f.mfderivToContinuousLinearEquiv (by simp) x).injective
    exact hzero.trans (map_zero _).symm

/-- Pullback of any actual representative, with every defining property
proved from the smooth diffeomorphism and the target representative. -/
def MaslovRepresentative.pullback {n : ℕ} {M N : SmoothManifold (2 * n)}
    {eta : N.Form 2} (s : MaslovRepresentative N eta) (f : M.SmoothEquiv N) :
    MaslovRepresentative M (M.pullback N f eta) where
  J := pullbackAlmostComplex M N f s.J
  compatible := isCompatibleAlmostComplex_pullback M N f eta s.J s.compatible
  tensor := pullbackSquaredTensor M N f s.tensor
  canonical := pullbackSquaredTensor_canonical M N f s.J s.tensor s.canonical
  smooth := isSmoothSquaredTensorSection_pullback M N f s.tensor s.smooth
  nowhereZero := pullbackSquaredTensor_ne_zero M N f s.tensor s.nowhereZero

set_option backward.isDefEq.respectTransparency false in
/-- Primitive preservation identifies the pulled-back symplectic form with
the source's actual exterior derivative. No symplectic-naturality certificate
is assumed in addition to the marking's primitive equation. -/
def pullbackPrimitiveMaslovRepresentative {n : ℕ} (M N : SmoothManifold (2 * n))
    (alpha : M.Form 1) (alpha' : N.Form 1) (f : M.SmoothEquiv N)
    (halpha' : N.IsSmoothForm alpha')
    (hprimitive : M.pullback N f alpha' = alpha)
    (s : MaslovRepresentative N (N.exteriorDerivative alpha')) :
    MaslovRepresentative M (M.exteriorDerivative alpha) where
  J := pullbackAlmostComplex M N f s.J
  compatible := by
    have hd : M.exteriorDerivative alpha = M.pullback N f (N.exteriorDerivative alpha') := by
      rw [← hprimitive]
      exact M.exteriorDerivative_pullback N f.toContMDiffMap alpha' halpha'
    rw [hd]
    exact isCompatibleAlmostComplex_pullback M N f (N.exteriorDerivative alpha') s.J s.compatible
  tensor := pullbackSquaredTensor M N f s.tensor
  canonical := pullbackSquaredTensor_canonical M N f s.J s.tensor s.canonical
  smooth := isSmoothSquaredTensorSection_pullback M N f s.tensor s.smooth
  nowhereZero := pullbackSquaredTensor_ne_zero M N f s.tensor s.nowhereZero

/-- The source prescription pulled back by the actual primitive-preserving
ambient marking from `g:initial`; no comparison-chain existence is asserted. -/
def pullbackLogarithmicMaslovRepresentative {n : ℕ} (M : SmoothManifold (2 * n))
    (alpha : M.Form 1) (f : M.SmoothEquiv (lgManifold n)) (I : ToricInput n)
    (K : ℝ) (hK : 0 ≤ K)
    (hprimitive : M.pullback (lgManifold n) f (lambdaKForm I K) = alpha) :
    MaslovRepresentative M (M.exteriorDerivative alpha) :=
  pullbackPrimitiveMaslovRepresentative M (lgManifold n) alpha (lambdaKForm I K) f
    (isSmoothForm_lambdaKForm I K) hprimitive (logarithmicMaslovRepresentative I K hK)

/-- The cotangent vertical-phase-zero prescription under its actual marking. -/
def pullbackCotangentMaslovRepresentative {n : ℕ} (M : SmoothManifold (2 * n))
    (alpha : M.Form 1) (f : M.SmoothEquiv (cotangentManifold n))
    (hprimitive : M.pullback (cotangentManifold n) f (lambdaCanForm n) = alpha) :
    MaslovRepresentative M (M.exteriorDerivative alpha) :=
  pullbackPrimitiveMaslovRepresentative M (cotangentManifold n) alpha (lambdaCanForm n) f
    (isSmoothForm_lambdaCanForm n) hprimitive (cotangentMaslovRepresentative n)

set_option backward.isDefEq.respectTransparency false in
/-- Actual scalar differentials satisfy the manifold chain rule. -/
theorem differentialCovector_comp {d e : ℕ} (M : SmoothManifold d) (N : SmoothManifold e)
    {f : M.Point → N.Point} (hf : MDifferentiable 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f)
    {q : N.Point → ℝ} (hq : MDifferentiable 𝓘(ℝ, Model e) 𝓘(ℝ, ℝ) q)
    (x : M.Point) :
    differentialCovector M (q ∘ f) x = (differentialCovector N q (f x)).comp
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x) :=
  mfderiv_comp x (hq (f x)) (hf x)

set_option backward.isDefEq.respectTransparency false in
/-- The global phase covector also satisfies the actual chain rule,
without a real-valued angular coordinate. -/
theorem phaseCovector_comp {d e : ℕ} (M : SmoothManifold d) (N : SmoothManifold e)
    {f : M.Point → N.Point} (hf : MDifferentiable 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f)
    {q : N.Point → ℂ} (hq : MDifferentiable 𝓘(ℝ, Model e) 𝓘(ℝ, ℂ) q)
    (x : M.Point) :
    phaseCovector M (q ∘ f) x = (phaseCovector N q (f x)).comp
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x) := by
  unfold phaseCovector complexDifferential
  rw [mfderiv_comp x (hq (f x)) (hf x)]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The prescribed marked logarithmic coordinates are exactly the intrinsic
target coframe composed with the marking derivative. -/
theorem logarithmicTangentCoordinates_naturality {n : ℕ} (M : SmoothManifold (2 * n))
    (f : M.SmoothEquiv (lgManifold n)) (x : M.Point) (v : M.Tangent x) :
    logarithmicTangentCoordinates M f x v =
      logarithmicTangentCoordinates (lgManifold n) id (f x)
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x v) := by
  apply Prod.ext <;> funext j
  · change differentialCovector M ((fun y : (lgManifold n).Point => y.1 j) ∘ f) x v =
      (differentialCovector (lgManifold n) (fun y => y.1 j) (f x))
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x v)
    exact congrArg (fun L => L v) (differentialCovector_comp M (lgManifold n)
      (f.mdifferentiable (by simp)) ((contMDiff_lgLogCoordinate j).mdifferentiable (by simp)) x)
  · change phaseCovector M (lgCircleCoordinate j ∘ f) x v =
      (phaseCovector (lgManifold n) (lgCircleCoordinate j) (f x))
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x v)
    exact congrArg (fun L => L v) (phaseCovector_comp M (lgManifold n)
      (f.mdifferentiable (by simp)) ((contMDiff_lg_circleCoordinate j).mdifferentiable (by simp)) x)

set_option backward.isDefEq.respectTransparency false in
theorem cotangentTangentCoordinates_naturality {n : ℕ} (M : SmoothManifold (2 * n))
    (f : M.SmoothEquiv (cotangentManifold n)) (x : M.Point) (v : M.Tangent x) :
    cotangentTangentCoordinates M f x v =
      cotangentTangentCoordinates (cotangentManifold n) id (f x)
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x v) := by
  apply Prod.ext <;> funext j
  · change differentialCovector M ((fun y : (cotangentManifold n).Point => y.2 j) ∘ f) x v =
      (differentialCovector (cotangentManifold n) (fun y => y.2 j) (f x))
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x v)
    exact congrArg (fun L => L v) (differentialCovector_comp M (cotangentManifold n)
      (f.mdifferentiable (by simp))
      ((contMDiff_cotangentMomentumCoordinate j).mdifferentiable (by simp)) x)
  · change phaseCovector M (cotangentCircleCoordinate j ∘ f) x v =
      (phaseCovector (cotangentManifold n) (cotangentCircleCoordinate j) (f x))
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x v)
    exact congrArg (fun L => L v) (phaseCovector_comp M (cotangentManifold n)
      (f.mdifferentiable (by simp))
      ((contMDiff_cotangent_circleCoordinate j).mdifferentiable (by simp)) x)

set_option backward.isDefEq.respectTransparency false in
/-- The representative under a logarithmic marking has the literal
prescribed determinant-square values in every tangent slot. -/
theorem isLogarithmicGrading_pullbackLogarithmicMaslovRepresentative {n : ℕ}
    (M : SmoothManifold (2 * n)) (alpha : M.Form 1) (f : M.SmoothEquiv (lgManifold n))
    (I : ToricInput n) (K : ℝ) (hK : 0 ≤ K)
    (hprimitive : M.pullback (lgManifold n) f (lambdaKForm I K) = alpha) :
    IsLogarithmicGrading f (pullbackLogarithmicMaslovRepresentative M alpha f I K hK hprimitive) := by
  intro x v
  change logarithmicSquaredVolumeTensor n (f x)
    (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x (v i)) = _
  rw [logarithmicSquaredVolumeTensor_apply]
  apply congrArg coordinateSquaredVolumeValue
  funext i
  exact (logarithmicTangentCoordinates_naturality M f x (v i)).symm

set_option backward.isDefEq.respectTransparency false in
theorem isVerticalGrading_pullbackCotangentMaslovRepresentative {n : ℕ}
    (M : SmoothManifold (2 * n)) (alpha : M.Form 1) (f : M.SmoothEquiv (cotangentManifold n))
    (hprimitive : M.pullback (cotangentManifold n) f (lambdaCanForm n) = alpha) :
    IsVerticalGrading f (pullbackCotangentMaslovRepresentative M alpha f hprimitive) := by
  intro x v
  change cotangentSquaredVolumeTensor n (f x)
    (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x (v i)) = _
  rw [cotangentSquaredVolumeTensor_apply]
  apply congrArg coordinateSquaredVolumeValue
  funext i
  exact (cotangentTangentCoordinates_naturality M f x (v i)).symm

end FsFltz.Geometry
