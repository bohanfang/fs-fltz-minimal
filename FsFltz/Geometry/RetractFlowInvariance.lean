import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Local flow invariance from smooth retractions and tangency

Source: `geometric-part-fsf-proof.tex`, `lem:invariance`, lines 1624–1658.
The restricted field is constructed by differentiating a smooth retraction.
Its local integral curves, followed by uniqueness, prove local invariance.
-/

noncomputable section
open scoped Manifold ContDiff
open Set Filter Topology Function

namespace FsFltz.Geometry

section Retract

variable {E F H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

omit [I.Boundaryless] [J.Boundaryless] in
set_option backward.isDefEq.respectTransparency false in
/-- Differentiating a smooth retraction constructs the smooth restricted field. -/
theorem contMDiff_retract_vectorField
    {j : M → N} {r : N → M}
    (hj : ContMDiff I J ∞ j) (hr : ContMDiff J I ∞ r)
    (hleft : LeftInverse r j)
    {Z : (x : N) → TangentSpace J x}
    (hZ : ContMDiff J J.tangent ∞ (fun x => (⟨x, Z x⟩ : TangentBundle J N))) :
    ContMDiff I I.tangent ∞ (fun x =>
      (⟨x, mfderiv J I r (j x) (Z (j x))⟩ : TangentBundle I M)) := by
  have h := (hr.contMDiff_tangentMap (by simp : ∞ + 1 ≤ ∞)).comp (hZ.comp hj)
  convert h using 1
  funext x
  simp only [Function.comp_apply, tangentMap]
  exact Bundle.TotalSpace.ext (hleft x).symm (heq_of_eq rfl)

omit [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ M] [IsManifold J ∞ N] in
set_option backward.isDefEq.respectTransparency false in
/-- Tangency makes the constructed restricted field map to the original one. -/
theorem mfderiv_retract_vectorField
    {j : M → N} {r : N → M}
    (hj : ContMDiff I J ∞ j) (hr : ContMDiff J I ∞ r)
    (hleft : LeftInverse r j)
    {Z : (x : N) → TangentSpace J x}
    (htangent : ∀ x, Z (j x) ∈ (mfderiv I J j x).range) (x : M) :
    mfderiv I J j x (mfderiv J I r (j x) (Z (j x))) = Z (j x) := by
  obtain ⟨v, hv⟩ := htangent x
  have hcomp : r ∘ j = id := funext hleft
  have hd := mfderiv_comp x (hr.mdifferentiableAt (by simp))
    (hj.mdifferentiableAt (by simp))
  rw [hcomp, mfderiv_id] at hd
  have hdv := congrArg (fun L => L v) hd
  change v = mfderiv J I r (j x) (mfderiv I J j x v) at hdv
  calc
    _ = mfderiv I J j x (mfderiv J I r (j x) (mfderiv I J j x v)) :=
      congrArg (fun w : F => mfderiv I J j x (mfderiv J I r (j x) w)) hv.symm
    _ = mfderiv I J j x v := congrArg (fun w : E => mfderiv I J j x w) hdv.symm
    _ = _ := hv

set_option backward.isDefEq.respectTransparency false in
/-- A smooth tangent field has locally invariant retract image, by constructed
local integral curves and ODE uniqueness. -/
theorem integralCurve_eventually_mem_retract_range [CompleteSpace E]
    {j : M → N} {r : N → M}
    (hj : ContMDiff I J ∞ j) (hr : ContMDiff J I ∞ r)
    (hleft : LeftInverse r j)
    {Z : (x : N) → TangentSpace J x}
    (hZ : ContMDiff J J.tangent ∞ (fun x => (⟨x, Z x⟩ : TangentBundle J N)))
    (htangent : ∀ x, Z (j x) ∈ (mfderiv I J j x).range)
    {γ : ℝ → N} {t₀ : ℝ} (hγ : IsMIntegralCurveAt γ Z t₀)
    {x : M} (hx : γ t₀ = j x) :
    ∀ᶠ t in 𝓝 t₀, γ t ∈ range j := by
  let W : (x : M) → TangentSpace I x := fun x => mfderiv J I r (j x) (Z (j x))
  have hW := contMDiff_retract_vectorField hj hr hleft hZ
  obtain ⟨α, hα₀, hα⟩ := exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
    (x₀ := x) t₀ ((hW.of_le (by simp)) x)
  have hjα : IsMIntegralCurveAt (j ∘ α) Z t₀ := by
    filter_upwards [hα] with t ht
    have hd := (hj.mdifferentiableAt (by simp)).hasMFDerivAt.comp t ht
    apply hd.congr_mfderiv
    apply ContinuousLinearMap.ext
    intro b
    change ℝ at b
    change mfderiv I J j (α t) (b • W (α t)) = b • Z (j (α t))
    rw [map_smul]
    exact congrArg (fun w : F => b • w)
      (mfderiv_retract_vectorField hj hr hleft htangent (α t))
  have heq := isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless
    ((hZ.of_le (by simp)) (γ t₀)) hγ hjα (by simpa only [Function.comp_apply, hα₀] using hx)
  filter_upwards [heq] with t ht
  exact ⟨α t, ht.symm⟩

omit [I.Boundaryless] [J.Boundaryless] in
set_option backward.isDefEq.respectTransparency false in
/-- Local twice differentiability gives a once differentiable tangent map. -/
theorem contMDiffAt_tangentMap_of_two
    {j : M → N} {v : TangentBundle I M}
    (hj : ContMDiffAt I J 2 j v.proj) :
    ContMDiffAt I.tangent J.tangent 1 (tangentMap I J j) v := by
  obtain ⟨U, hU, hjU⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).mp hj
  obtain ⟨V, hVU, hV, hvV⟩ := mem_nhds_iff.mp hU
  have hjV := hjU.mono hVU
  have hpre : (fun w : TangentBundle I M => w.proj) ⁻¹' V ∈ 𝓝 v :=
    (FiberBundle.continuous_proj (E := TangentSpace I) (F := E)).continuousAt.preimage_mem_nhds
      (hV.mem_nhds hvV)
  have h := (hjV.contMDiffOn_tangentMapWithin (m := 1) (by norm_num)
    hV.uniqueMDiffOn).contMDiffAt hpre
  apply h.congr_of_eventuallyEq
  filter_upwards [hpre] with w hw
  simp only [tangentMap, tangentMapWithin]
  rw [mfderivWithin_of_mem_nhds (hV.mem_nhds hw)]

omit [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ M] [IsManifold J ∞ N] in
set_option backward.isDefEq.respectTransparency false in
/-- The differential retraction identity only needs an identity of germs. -/
theorem mfderiv_retract_vectorField_of_germ
    {j : M → N} {r : N → M} {x : M}
    (hj : MDifferentiableAt I J j x) (hr : MDifferentiableAt J I r (j x))
    (hleft : r ∘ j =ᶠ[𝓝 x] id) {z : TangentSpace J (j x)}
    (htangent : z ∈ (mfderiv I J j x).range) :
    mfderiv I J j x (mfderiv J I r (j x) z) = z := by
  obtain ⟨v, hv⟩ := htangent
  have hd := mfderiv_comp x hr hj
  rw [hleft.mfderiv_eq, mfderiv_id] at hd
  have hdv := congrArg (fun L => L v) hd
  change v = mfderiv J I r (j x) (mfderiv I J j x v) at hdv
  calc
    _ = mfderiv I J j x (mfderiv J I r (j x) (mfderiv I J j x v)) :=
      congrArg (fun w : F => mfderiv I J j x (mfderiv J I r (j x) w)) hv.symm
    _ = mfderiv I J j x v := congrArg (fun w : E => mfderiv I J j x w) hdv.symm
    _ = _ := hv

set_option backward.isDefEq.respectTransparency false in
/-- Local retraction and tangency germs suffice; all maps may be arbitrary
away from the indicated neighborhoods. The local restricted ODE is constructed. -/
theorem integralCurve_eventually_mem_retract_image_of_germ [CompleteSpace E]
    {j : M → N} {r : N → M} {x : M}
    (hj : ContMDiffAt I J 2 j x) (hr : ContMDiffAt J I 2 r (j x))
    (hleft : r ∘ j =ᶠ[𝓝 x] id)
    {Z : (y : N) → TangentSpace J y}
    (hZ : ContMDiffAt J J.tangent 1 (fun y => (⟨y, Z y⟩ : TangentBundle J N)) (j x))
    (htangent : ∀ᶠ y in 𝓝 x, Z (j y) ∈ (mfderiv I J j y).range)
    {γ : ℝ → N} {t₀ : ℝ} (hγ : IsMIntegralCurveAt γ Z t₀)
    (hx : γ t₀ = j x) {U : Set M} (hU : U ∈ 𝓝 x) :
    ∀ᶠ t in 𝓝 t₀, γ t ∈ j '' U := by
  let W : (y : M) → TangentSpace I y := fun y => mfderiv J I r (j y) (Z (j y))
  have hW : ContMDiffAt I I.tangent 1
      (fun y => (⟨y, W y⟩ : TangentBundle I M)) x := by
    have ht := (contMDiffAt_tangentMap_of_two (v := ⟨j x, Z (j x)⟩) hr).comp x
      (hZ.comp x (hj.of_le (by norm_num)))
    apply ht.congr_of_eventuallyEq
    filter_upwards [hleft] with y hy
    exact Bundle.TotalSpace.ext hy.symm (heq_of_eq rfl)
  obtain ⟨α, hα₀, hα⟩ := exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
    (x₀ := x) t₀ hW
  have hαx : Tendsto α (𝓝 t₀) (𝓝 x) := hα₀ ▸ hα.continuousAt.tendsto
  have hjnear := (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hj
  have hrnear := hj.continuousAt.tendsto.eventually
    ((contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hr)
  have hlnear : ∀ᶠ y in 𝓝 x, r ∘ j =ᶠ[𝓝 y] id :=
    eventually_eventually_nhds.mpr hleft
  have hjα : IsMIntegralCurveAt (j ∘ α) Z t₀ := by
    filter_upwards [hα, hαx.eventually hjnear, hαx.eventually hrnear,
      hαx.eventually hlnear, hαx.eventually htangent] with t ht hjt hrt hlt htan
    have hd := (hjt.mdifferentiableAt (by norm_num)).hasMFDerivAt.comp t ht
    apply hd.congr_mfderiv
    apply ContinuousLinearMap.ext
    intro b
    change ℝ at b
    change mfderiv I J j (α t) (b • W (α t)) = b • Z (j (α t))
    rw [map_smul]
    exact congrArg (fun w : F => b • w)
      (mfderiv_retract_vectorField_of_germ (hjt.mdifferentiableAt (by norm_num))
        (hrt.mdifferentiableAt (by norm_num)) hlt htan)
  have hzγ : ContMDiffAt J J.tangent 1
      (fun y => (⟨y, Z y⟩ : TangentBundle J N)) (γ t₀) := hx ▸ hZ
  have heq := isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless
    hzγ hγ hjα (by simpa only [Function.comp_apply, hα₀] using hx)
  filter_upwards [heq, hαx.eventually hU] with t ht hUt
  exact ⟨α t, hUt, ht.symm⟩

end Retract

end FsFltz.Geometry
