import FsFltz.Geometry.LiouvilleFlowPrimitive
import FsFltz.Geometry.TailoringMarkedHittingEmbedding

/-!
# The actual primitive of a regional outer hitting map

Source: `geometric-part-fsf-proof.tex`, `prop:band`, lines 1778–1817,
and `eq:hittingprimitive`, lines 1847–1853. Regional contraction and the
actual cutoff orbit equation give exponential scaling up to the finite
hit. No pullback law or complete native ambient flow is an input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.LiouvilleFlowPrimitive
open SmoothManifold

/-- The spatial coefficient scales up to a finite endpoint when the
native equation holds on an open region containing every pre-hit point. -/
theorem spatial_pullback_eq_exp_mul_of_regional {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}
    (M : SmoothManifold d) (α : M.Form 1) (hα : M.IsSmoothForm α)
    (Z : (x : M.Point) → M.Tangent x) (F : ℝ × E → M.Point)
    {V : Set E} (hV : IsOpen V)
    (hF : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) ∞ F (univ ×ˢ V))
    {S : Set M.Point} (hS : IsOpen S)
    (hode : ∀ p ∈ univ ×ˢ V, F p ∈ S →
      mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F p (1, 0) = Z (F p))
    (hZ : ∀ p ∈ univ ×ˢ V, F p ∈ S → M.LiouvilleEquation α (F p) (Z (F p)))
    {T : ℝ} (hT : 0 < T) {y : E} (hy : y ∈ V)
    (hstay : ∀ s < T, F (s, y) ∈ S) (v : E) :
    evalOne α (F (T, y))
      (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F (T, y) (0, v)) =
      Real.exp T * evalOne α (F (0, y))
        (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F (0, y) (0, v)) := by
  let q : ℝ → ℝ := fun s => evalOne α (F (s, y))
    (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F (s, y) (0, v))
  let B : ℝ × E → (ℝ × E) [⋀^Fin 1]→L[ℝ] ℝ := fun p =>
    (α (F p)).compContinuousLinearMap (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F p)
  have hq : Differentiable ℝ q := by
    intro s
    have hB := (M.contDiffAt_pullback_one_from_normedSpace F (isOpen_univ.prod hV)
      hF α hα (show (s, y) ∈ univ ×ˢ V from ⟨mem_univ _, hy⟩)).differentiableAt
      (by simp)
    exact ((hB.hasFDerivAt.continuousAlternatingMap_apply_const
      (fun _ => (0, v))).comp_hasDerivAt s
        ((hasDerivAt_id s).prodMk (hasDerivAt_const s y))).differentiableAt
  let O : Set (ℝ × E) := (univ ×ˢ V) ∩ F ⁻¹' S
  have hO : IsOpen O := hF.continuousOn.isOpen_inter_preimage (isOpen_univ.prod hV) hS
  have hqode : ∀ s < T, HasDerivAt q (q s) s := by
    intro s hs
    exact hasDerivAt_spatial_pullback M α hα Z F hO (hF.mono inter_subset_left)
      (fun p hp => hode p hp.1 hp.2) (fun p hp => hZ p hp.1 hp.2)
      ⟨⟨mem_univ _, hy⟩, hstay s hs⟩ v
  let w : ℝ → ℝ := fun s => Real.exp (-s) * q s
  have hw : ∀ s ∈ Iio T, HasDerivAt w 0 s := by
    intro s hs
    exact (((hasDerivAt_id s).neg.exp).mul (hqode s hs)).congr_deriv (by ring)
  have heq : EqOn w (fun _ => w 0) (Iio T) := by
    intro s hs
    exact isOpen_Iio.is_const_of_deriv_eq_zero isPreconnected_Iio
      (fun s hs => (hw s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hw s hs).deriv) hs hT
  have hclosed := heq.closure ((Real.continuous_exp.comp continuous_id.neg).mul hq.continuous)
    continuous_const
  have htclosure : T ∈ closure (Iio T) := by
    rw [closure_Iio T]
    exact mem_Iic.mpr (le_refl T)
  have he := hclosed htclosure
  have hm := congrArg (fun r => Real.exp T * r) he
  simp only [w, neg_zero, Real.exp_zero, one_mul, ← mul_assoc, ← Real.exp_add,
    add_neg_cancel, Real.exp_zero] at hm
  exact hm

/-- The actual manifold spatial pullback scales at a regional finite hit.
The field is only required to satisfy contraction on the open flow region. -/
theorem pullback_slice_at_of_regional_contraction {d e : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold e) (α : M.Form 1)
    (hα : M.IsSmoothForm α) (Z : (x : M.Point) → M.Tangent x)
    (F : ℝ × N.Point → M.Point)
    (hF : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model e)) 𝓘(ℝ, Model d) ∞ F)
    {S : Set M.Point} (hS : IsOpen S)
    (hode : ∀ x t, F (t, x) ∈ S →
      HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) (fun s => F (s, x)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Z (F (t, x)))))
    (hZ : ∀ y ∈ S, M.LiouvilleEquation α y (Z y))
    {T : ℝ} (hT : 0 < T) (x : N.Point) (hstay : ∀ s < T, F (s, x) ∈ S) :
    N.pullback M (fun y => F (T, y)) α x =
      Real.exp T • N.pullback M (fun y => F (0, y)) α x := by
  let c := chartAt (Model e) x
  let H : ℝ × Model e → M.Point := fun p => F (p.1, c.symm p.2)
  have hx : x ∈ c.source := mem_chart_source _ _
  have hxt : c x ∈ c.target := c.map_source hx
  have hH : ContMDiffOn 𝓘(ℝ, ℝ × Model e) 𝓘(ℝ, Model d) ∞ H (univ ×ˢ c.target) := by
    apply hF.comp_contMDiffOn
    apply ContMDiffOn.prodMk (contMDiffOn_iff_contDiffOn.mpr contDiffOn_fst)
    exact (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model e)) (x := x)).comp
      (contMDiffOn_iff_contDiffOn.mpr contDiffOn_snd) (fun p hp => hp.2)
  let O : Set (ℝ × Model e) := (univ ×ˢ c.target) ∩ H ⁻¹' S
  have hO : IsOpen O := hH.continuousOn.isOpen_inter_preimage
    (isOpen_univ.prod c.open_target) hS
  have hHode : ∀ p ∈ univ ×ˢ c.target, H p ∈ S →
      mfderiv 𝓘(ℝ, ℝ × Model e) 𝓘(ℝ, Model d) H p (1, 0) = Z (H p) := by
    intro p hp hs
    exact time_derivative_of_orbit M Z H hO (hH.mono inter_subset_left)
      (fun q hq => hode (c.symm q.2) q.1 hq.2) ⟨hp, hs⟩
  have hspatial (s : ℝ) (v : N.Tangent x) :
      mfderiv 𝓘(ℝ, ℝ × Model e) 𝓘(ℝ, Model d) H (s, c x)
        (0, N.chartTangentMap x x v) =
      mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) (fun y => F (s, y)) x v := by
    have hinc := hasMFDerivAt_iff_hasFDerivAt.mpr
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) s (c x))
    have hleft := mfderiv_comp (c x)
      (((hH (s, c x) ⟨mem_univ _, hxt⟩).contMDiffAt
        ((isOpen_univ.prod c.open_target).mem_nhds ⟨mem_univ _, hxt⟩)).mdifferentiableAt
          (by simp)) hinc.mdifferentiableAt
    rw [hinc.mfderiv] at hleft
    have hright := mfderiv_comp (g := fun y => F (s, y)) (c x)
      ((hF.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt (by simp))
      ((mdifferentiable_chart (I := 𝓘(ℝ, Model e)) x).mdifferentiableAt_symm hxt)
    have he := congrArg (fun L : Model e →L[ℝ] M.Tangent (H (s, c x)) =>
      L (N.chartTangentMap x x v)) (hleft.symm.trans hright)
    simp only [ContinuousLinearMap.comp_apply] at he
    erw [ContinuousLinearMap.inr_apply] at he
    have hinv := congrArg (fun L : N.Tangent x →L[ℝ] N.Tangent x => L v)
      ((mdifferentiable_chart (I := 𝓘(ℝ, Model e)) x).symm_comp_deriv hx)
    change N.inverseChartTangentMap x (c x) (N.chartTangentMap x x v) = v at hinv
    change mfderiv 𝓘(ℝ, ℝ × Model e) 𝓘(ℝ, Model d) H (s, c x)
      (0, N.chartTangentMap x x v) =
      mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) (fun y => F (s, y)) (c.symm (c x))
        (N.inverseChartTangentMap x (c x) (N.chartTangentMap x x v)) at he
    rw [c.left_inv hx] at he
    erw [hinv] at he
    exact he
  ext vs
  have hscale := spatial_pullback_eq_exp_mul_of_regional M α hα Z H c.open_target hH hS
    hHode (fun p _ hp => hZ (H p) hp) hT hxt
    (fun s hs => by simpa only [H, c.left_inv hx] using hstay s hs)
    (N.chartTangentMap x x (vs 0))
  change evalOne α (F (T, c.symm (c x)))
      (mfderiv 𝓘(ℝ, ℝ × Model e) 𝓘(ℝ, Model d) H (T, c x)
        (0, N.chartTangentMap x x (vs 0))) =
    Real.exp T * evalOne α (F (0, c.symm (c x)))
      (mfderiv 𝓘(ℝ, ℝ × Model e) 𝓘(ℝ, Model d) H (0, c x)
        (0, N.chartTangentMap x x (vs 0))) at hscale
  rw [c.left_inv hx, hspatial, hspatial] at hscale
  convert hscale using 1 <;> apply congrArg _ <;> funext i <;> rw [Fin.eq_zero i]

/-- Variable time adds a field-direction derivative, killed by the
primitive at the endpoint. Scaling is proved from the regional orbit. -/
theorem pullback_variableTime_at_of_regional_contraction {d e : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold e) (α : M.Form 1)
    (hα : M.IsSmoothForm α) (Z : (x : M.Point) → M.Tangent x)
    (F : ℝ × N.Point → M.Point)
    (hF : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model e)) 𝓘(ℝ, Model d) ∞ F)
    {S : Set M.Point} (hS : IsOpen S)
    (hode : ∀ x t, F (t, x) ∈ S →
      HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) (fun s => F (s, x)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Z (F (t, x)))))
    (hZ : ∀ y ∈ S, M.LiouvilleEquation α y (Z y))
    (τ : N.Point → ℝ) (x : N.Point)
    (hτ : MDifferentiableAt 𝓘(ℝ, Model e) 𝓘(ℝ, ℝ) τ x) (hT : 0 < τ x)
    (hstay : ∀ s < τ x, F (s, x) ∈ S)
    (hend : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) (fun s => F (s, x)) (τ x)
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Z (F (τ x, x)))))
    (hzero : evalOne α (F (τ x, x)) (Z (F (τ x, x))) = 0) :
    N.pullback M (fun y => F (τ y, y)) α x =
      Real.exp (τ x) • N.pullback M (fun y => F (0, y)) α x := by
  have hscale := pullback_slice_at_of_regional_contraction M N α hα Z F hF hS
    hode hZ hT x hstay
  have hFd := hF.mdifferentiableAt (x := (τ x, x)) (by simp)
  have hid : MDifferentiableAt 𝓘(ℝ, Model e) 𝓘(ℝ, Model e) (fun y : N.Point => y) x :=
    mdifferentiableAt_id
  ext vs
  let v := vs 0
  have hc := mfderiv_comp_apply (f := fun y => (τ y, y)) (g := F) x hFd (hτ.prodMk hid) v
  rw [mfderiv_prodMk hτ hid] at hc
  rw [mfderiv_prod_eq_add_apply hFd, hend.mfderiv] at hc
  have hi : mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model e) (fun y : N.Point => y) x =
      (1 : N.Tangent x →L[ℝ] N.Tangent x) := mfderiv_id
  rw [hi] at hc
  change mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) (fun y => F (τ y, y)) x v =
    (mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, ℝ) τ x v) • Z (F (τ x, x)) +
      mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) (fun y => F (τ x, y)) x v at hc
  have hv : vs = fun _ : Fin 1 => v := by
    funext i
    exact congrArg vs (Subsingleton.elim i 0)
  rw [hv]
  change evalOne α (F (τ x, x))
    (mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) (fun y => F (τ y, y)) x v) = _
  rw [hc, evalOne_add, evalOne_smul, hzero, mul_zero, zero_add]
  exact congrArg (fun η => η (fun _ : Fin 1 => v)) hscale

end FsFltz.Geometry.LiouvilleFlowPrimitive

namespace FsFltz.Geometry
open SmoothManifold

/-- The actual regional action has the hitting primitive law on every
source tangent. Boundary positivity proves that every earlier real time,
including negative times, stays in the native open sublevel. -/
theorem regional_outer_hitting_pullback {d e : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold e) (α : M.Form 1)
    (hα : M.IsSmoothForm α) (ρ : M.Point → ℝ)
    (hρ : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ ρ) (A k : ℝ)
    (hnd : ∀ y, ρ y ≤ A → M.Nondegenerate (M.exteriorDerivative α) y)
    (G : Flow ℝ (ℝ × M.Point))
    (hG : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
      (fun p : ℝ × (ℝ × M.Point) => G p.1 p.2))
    (hnative : ∀ y t, ρ (G t (k, y)).2 ≤ A →
      IsMIntegralCurveAt (fun s => (G s (k, y)).2) (M.liouvilleVector α) t)
    (hboundary : ∀ y, ρ y = A → 0 < M.scalarDerivative ρ y (M.liouvilleVector α y))
    (j : N.Point → M.Point)
    (hj : ContMDiff 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) ∞ j)
    (τ : N.Point → ℝ) (x : N.Point)
    (hτ : MDifferentiableAt 𝓘(ℝ, Model e) 𝓘(ℝ, ℝ) τ x)
    (hT : 0 < τ x) (hhit : ρ (G (τ x) (k, j x)).2 = A) :
    N.pullback M (fun y => (G (τ y) (k, j y)).2) α x =
      Real.exp (τ x) • N.pullback M j α x := by
  let F : ℝ × N.Point → M.Point := fun p => (G p.1 (k, j p.2)).2
  have hF : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model e)) 𝓘(ℝ, Model d) ∞ F :=
    (hG.comp (contMDiff_fst.prodMk
      (contMDiff_const.prodMk (hj.comp contMDiff_snd)))).snd
  let S : Set M.Point := {y | ρ y < A}
  have hS : IsOpen S := isOpen_lt hρ.continuous continuous_const
  have hZ : ∀ y, ρ y ≤ A → M.LiouvilleEquation α y (M.liouvilleVector α y) := by
    intro y hy
    exact M.liouvilleVector_contraction α y (M.liouvilleEquation_exists α y (hnd y hy))
  let f : ℝ → ℝ := fun s => ρ (G s (k, j x)).2
  have hf : Differentiable ℝ f :=
    (hρ.comp (hG.comp (contMDiff_id.prodMk contMDiff_const)).snd).contDiff.differentiable
      (by simp)
  have hpos : ∀ s, f s = A → 0 < deriv f s := by
    intro s hs
    have hd := hasDerivAt_scalar_of_isMIntegralCurveAt M hρ (hnative (j x) s hs.le)
    rw [hd.deriv]
    exact hboundary _ hs
  have hstay : ∀ s < τ x, F (s, x) ∈ S := by
    intro s hs
    change f s < A
    by_contra hn
    have hp := BoundaryOutwardAbsorptionMarking.level_lt_of_boundary_deriv_pos
      (fun s => (hf s).hasDerivAt) hpos (le_of_not_gt hn) hs
    exact (not_lt_of_ge hhit.le) hp
  have hend := (hnative (j x) (τ x) hhit.le).hasMFDerivAt
  have hz : evalOne α (F (τ x, x)) (M.liouvilleVector α (F (τ x, x))) = 0 :=
    M.evalOne_eq_zero_of_liouvilleEquation α _ _ (hZ _ hhit.le)
  have hp := LiouvilleFlowPrimitive.pullback_variableTime_at_of_regional_contraction
    M N α hα (M.liouvilleVector α) F hF hS
      (fun y t ht => (hnative (j y) t ht.le).hasMFDerivAt)
      (fun y hy => hZ y hy.le) τ x hτ hT hstay hend hz
  have he : (fun y => F (0, y)) = j := by
    funext y
    exact congrArg Prod.snd (G.map_zero_apply (k, j y))
  rw [he] at hp
  exact hp

end FsFltz.Geometry

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}
local instance hittingPrimitiveCharts : ChartedSpace (Model (2 * n)) (LGSpace n) :=
  (lgManifold n).charts
local instance hittingPrimitiveSmooth :
    IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth

/-- The literal full fiber annihilates the plane primitive in every
coefficient, by differentiating its actual constant level equation. -/
theorem FullFiberRibbonMarking.pullback_rankTwoPrimitive
    {P : WitnessedPair n}
    {R : P.ribbonDomain.domain.extension.SmoothEmbedding (lgManifold n)}
    {f : LGSpace n → ℂ} {φ : RealSpace n → ℝ}
    (Q : FullFiberRibbonMarking P R f 1 φ)
    (hf : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ) ∞ f) (k : ℝ) :
    Q.manifold.pullback (lgManifold n) Q.embedding.map
      ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) f k) =
        Q.manifold.pullback (lgManifold n) Q.embedding.map (lambdaPotentialForm φ) := by
  have he : (fun x => f (Q.embedding.map x)) = fun _ : Q.manifold.Point => (1 : ℂ) := by
    funext x
    have hx : Q.embedding.map x ∈ {y | f y = 1} := Q.image ▸ mem_range_self x
    exact hx
  funext x
  apply Q.manifold.pullback_rankTwoPrimitive_eq_of_tangent_range_le_kernel
    (lgManifold n) Q.embedding (lambdaPotentialForm φ) f k x
  rintro v ⟨w, rfl⟩
  change complexDifferential (lgManifold n) f (Q.embedding.map x)
    (mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n)) Q.embedding.map x w) = 0
  have hd := mfderiv_comp_apply (f := Q.embedding.map) (g := f) x
    (hf.mdifferentiableAt (by simp)) (Q.embedding.map.contMDiff.mdifferentiableAt (by simp)) w
  change mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, ℂ)
    (fun x => f (Q.embedding.map x)) x w = _ at hd
  rw [he, mfderiv_const, zero_apply] at hd
  exact hd.symm

/-- The actual outer hitting map on the retained full fiber pulls back
the native ambient primitive to the exponential of its same hitting time
times the full-fiber primitive. The geometric and analytic inputs are the
existing regional native-flow and outer-boundary conclusions. -/
theorem FullFiberRibbonMarking.native_hitting_pullback_at
    {P : WitnessedPair n}
    {R : P.ribbonDomain.domain.extension.SmoothEmbedding (lgManifold n)}
    {f : LGSpace n → ℂ} {φ : RealSpace n → ℝ}
    (Q : FullFiberRibbonMarking P R f 1 φ)
    (hf : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ) ∞ f)
    (hφ : ContDiff ℝ ∞ φ) (A k : ℝ)
    (hnd : ∀ y, φ y.1 ≤ A → (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative ((lgManifold n).rankTwoPrimitive
        (lambdaPotentialForm φ) f k)) y)
    (G : Flow ℝ (ℝ × LGSpace n))
    (hG : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
      (fun p : ℝ × (ℝ × LGSpace n) => G p.1 p.2))
    (hnative : ∀ y t, φ (G t (k, y)).2.1 ≤ A →
      IsMIntegralCurveAt (fun s => (G s (k, y)).2)
        ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm φ) f k)) t)
    (hboundary : ∀ y, φ y.1 = A →
      0 < (lgManifold n).scalarDerivative (fun z => φ z.1) y
        ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm φ) f k) y))
    {W : Set (ℝ × LGSpace n)} (hW : IsOpen W)
    {τ : ℝ × LGSpace n → ℝ}
    (hτ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℝ) ∞ τ W)
    (hhit : ∀ p ∈ W, 0 < τ p ∧ φ (G (τ p) p).2.1 = A)
    (x : Q.manifold.Point) (hx : (k, Q.embedding.map x) ∈ W) :
    Q.manifold.pullback (lgManifold n)
      (fun y => (G (τ (k, Q.embedding.map y)) (k, Q.embedding.map y)).2)
      ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) f k) x =
        Real.exp (τ (k, Q.embedding.map x)) •
          Q.manifold.pullback (lgManifold n) Q.embedding.map (lambdaPotentialForm φ) x := by
  have hi : ContMDiff 𝓘(ℝ, Model (2 * n - 2))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
      (fun y => (k, Q.embedding.map y)) :=
    contMDiff_const.prodMk Q.embedding.map.contMDiff
  have hτx := ((hτ _ hx).contMDiffAt (hW.mem_nhds hx)).comp x hi.contMDiffAt
  have hp := regional_outer_hitting_pullback (lgManifold n) Q.manifold
    ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) f k)
    ((lgManifold n).isSmoothForm_rankTwoPrimitive (isSmoothForm_lambdaPotentialForm hφ) hf k)
    (fun z => φ z.1) (contMDiff_potentialValue hφ) A k hnd G hG hnative hboundary
    Q.embedding.map Q.embedding.map.contMDiff
    (fun y => τ (k, Q.embedding.map y)) x (hτx.mdifferentiableAt (by simp))
    (hhit _ hx).1 (hhit _ hx).2
  rw [Q.pullback_rankTwoPrimitive hf] at hp
  exact hp

end FsFltz
