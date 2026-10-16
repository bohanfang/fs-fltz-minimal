import FsFltz.Geometry.SubmersionProductCoordinates
import FsFltz.Geometry.TailoringCriticalTransverseLinearization
import FsFltz.Geometry.SubmersionExpansion
import FsFltz.Geometry.TailoringConormalRate

/-!
# Actual native product coordinates at a face critical point

Source: `geometric-part-fsf-proof.tex`, `lem:trapping`, lines 1672–1696,
and `lem:stable`, lines 1709–1724. The defining map is the native conormal
transverse map already used by the fixed transverse metric. Its proved
normal right inverse constructs the product inverse. No assumed tube or
nonlinear expansion is added to the toric input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set Filter Function
open scoped Topology BigOperators ContDiff Manifold

namespace NativeFaceHessianChart

variable {n d : ℕ} {φ : RealSpace n → ℝ} {s : Finset (Lattice n)}
  {H : RealSpace n →L[ℝ] RealSpace n} {q : s → ℝ} {lam : ℝ}
  {N : SmoothManifold d} {j : N.SmoothEmbedding (lgManifold n)}
  {a : N.Point} {x : TangentCoordinates n}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual defining map in the native fiber chart. -/
def coordinateTransverseMap (_C : NativeFaceHessianChart φ s H q lam N j a x)
    (Φ : RealSpace n → RealSpace n) (Q : RealSpace n →L[ℝ] E) (v₀ : s)
    (y : Model d) : E × (s.erase v₀.val → ℝ) :=
  conormalTransverseCoordinates Φ Q s v₀.val
    (j.map ((chartAt (Model d) a).symm y))

theorem coordinateTransverseMap_smooth
    (C : NativeFaceHessianChart φ s H q lam N j a x)
    {Φ : RealSpace n → RealSpace n} (Q : RealSpace n →L[ℝ] E)
    (v₀ : s) (hΦ : ContDiffAt ℝ ∞ Φ x.1) :
    ContDiffAt ℝ ∞ (C.coordinateTransverseMap Φ Q v₀) (chartAt (Model d) a a) := by
  let δ := conormalTransverseCoordinates Φ Q s v₀.val
  have hs : ContDiffAt ℝ ∞ (δ ∘ lgCover) x := by
    let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
    exact ((contMDiffAt_conormalTransverseCoordinates_native Q s v₀.val
      (lgCover x) hΦ).comp x (contMDiff_lgCover n).contMDiffAt).contDiffAt
  apply ((C.center.symm ▸ hs).comp _ C.smooth).congr_of_eventuallyEq
  filter_upwards [C.cover] with y hy
  exact (congrArg δ hy).symm

theorem coordinateTransverseMap_center
    (C : NativeFaceHessianChart φ s H q lam N j a x)
    (Φ : RealSpace n → RealSpace n) (Q : RealSpace n →L[ℝ] E) (v₀ : s) :
    C.coordinateTransverseMap Φ Q v₀ (chartAt (Model d) a a) =
      conormalTransverseCoordinates Φ Q s v₀.val (lgCover x) := by
  have hcover : (lgCover ∘ C.lift) =ᶠ[𝓝 (chartAt (Model d) a a)]
      (j.map ∘ (chartAt (Model d) a).symm) := C.cover
  have h := hcover.eq_of_nhds
  dsimp only [Function.comp_def] at h
  rw [C.center] at h
  exact (congrArg (conormalTransverseCoordinates Φ Q s v₀.val) h).symm

/-- The actual native defining map and its already proved normal lift
construct the product inverse, without a tubular-chart hypothesis. -/
theorem exists_transverse_product_coordinates
    (C : NativeFaceHessianChart φ s H q lam N j a x)
    {Φ : RealSpace n → RealSpace n} (Q : RealSpace n →L[ℝ] E)
    (v₀ : s) (hΦ : ContDiffAt ℝ ∞ Φ x.1) (hHΦ : H = fderiv ℝ Φ x.1)
    (r : s → ℝ) (hmon : ∀ v : s, monomial 1 v.val (lgCover x) = (r v : ℂ))
    (L : (E × (s.erase v₀.val → ℝ)) →L[ℝ] faceFiberPlane q)
    (hL : (faceFiberTransverseDifferential Q H v₀ q r).comp L =
      ContinuousLinearMap.id ℝ (E × (s.erase v₀.val → ℝ)))
    (hzero : conormalTransverseCoordinates Φ Q s v₀.val (lgCover x) = 0) :
    let ca := chartAt (Model d) a a
    let δ := C.coordinateTransverseMap Φ Q v₀
    let A := fderiv ℝ δ ca
    ∃ e : OpenPartialHomeomorph (Model d) (A.ker × (E × (s.erase v₀.val → ℝ))),
      ca ∈ e.source ∧ (0 : A.ker × (E × (s.erase v₀.val → ℝ))) ∈ e.target ∧
      e ca = 0 ∧ e.symm 0 = ca ∧
      (∀ y, (e y).2 = δ y) ∧
      ContDiffAt ℝ ∞ e.symm 0 ∧
      ((fderiv ℝ e.symm 0).comp
        (ContinuousLinearMap.inr ℝ A.ker (E × (s.erase v₀.val → ℝ))) =
          C.transverseNormalLift v₀ L) ∧
      (∀ p ∈ e.target, δ (e.symm p) = p.2) := by
  let ca := chartAt (Model d) a a
  let δ := C.coordinateTransverseMap Φ Q v₀
  let A := fderiv ℝ δ ca
  have hs := C.coordinateTransverseMap_smooth Q v₀ hΦ
  have hz : δ ca = 0 := (C.coordinateTransverseMap_center Φ Q v₀).trans hzero
  have hright : RightInverse (C.transverseNormalLift v₀ L) A := by
    intro z
    exact congrArg (fun K : (E × (s.erase v₀.val → ℝ)) →L[ℝ] _ => K z)
      (C.transverseNormalLift_rightInverse Q v₀ hΦ hHΦ r hmon L hL)
  obtain ⟨e, ha, ht, he, hmap, hinv, hd, hnormal, hδ⟩ :=
    exists_submersion_product_coordinates δ ca A (C.transverseNormalLift v₀ L)
      hright hs (hs.differentiableAt (by simp)).hasFDerivAt hz
  refine ⟨e, ha, ht, he, ?_, fun y => congrArg Prod.snd (hmap y), hinv, hnormal, hδ⟩
  simpa only [he] using e.left_inv ha

end NativeFaceHessianChart

namespace NativeFaceHessianChart

variable {n : ℕ} {φ : RealSpace n → ℝ} {s : Finset (Lattice n)}
  {H : RealSpace n →L[ℝ] RealSpace n} {q : s → ℝ} {lam : ℝ}
  {N : SmoothManifold (2 * n - 2)} {j : N.SmoothEmbedding (lgManifold n)}
  {a : N.Point} {x : TangentCoordinates n}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Smoothness belongs to the actual transverse rate, rather than to an
assigned normal field. -/
theorem coordinateTransverseRate_smooth
    (C : NativeFaceHessianChart φ s H q lam N j a x) (hφ : ContDiff ℝ ∞ φ)
    (hnd : ∀ b, N.Nondegenerate
      (N.exteriorDerivative (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ))) b)
    {Φ : RealSpace n → RealSpace n} (Q : RealSpace n →L[ℝ] E)
    (v₀ : s) (hΦ : ContDiffAt ℝ ∞ Φ x.1) :
    ContDiffAt ℝ ∞ (C.coordinateTransverseRate Φ Q v₀)
      (chartAt (Model (2 * n - 2)) a a) := by
  exact ((C.coordinateTransverseMap_smooth Q v₀ hΦ).fderiv_right (m := ∞) (by simp)).clm_apply
    (C.coordinateField_smooth hφ hnd)

/-- Chart transport preserves the rate of the original defining map
against the original intrinsic Liouville field. -/
theorem coordinateTransverseRate_eq_native
    (C : NativeFaceHessianChart φ s H q lam N j a x)
    (Φ : RealSpace n → RealSpace n) (Q : RealSpace n →L[ℝ] E) (v₀ : s)
    (y : Model (2 * n - 2)) (hy : y ∈ (chartAt (Model (2 * n - 2)) a).target)
    (hδ : MDifferentiableAt 𝓘(ℝ, Model (2 * n - 2))
      𝓘(ℝ, E × (s.erase v₀.val → ℝ))
      ((conormalTransverseCoordinates Φ Q s v₀.val) ∘ j.map)
        ((chartAt (Model (2 * n - 2)) a).symm y)) :
    C.coordinateTransverseRate Φ Q v₀ y =
      conormalTransverseRate N j
        (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) Φ Q s v₀.val
          ((chartAt (Model (2 * n - 2)) a).symm y) := by
  let c := chartAt (Model (2 * n - 2)) a
  let f := (conormalTransverseCoordinates Φ Q s v₀.val) ∘ j.map
  let Z := N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ))
  have hb : c.symm y ∈ c.source := c.map_target hy
  have hinv := congrArg (fun K : N.Tangent (c.symm y) →L[ℝ] N.Tangent (c.symm y) =>
      K (Z (c.symm y)))
    ((mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n - 2))) a).symm_comp_deriv hb)
  change N.inverseChartTangentMap a (c (c.symm y))
    (N.chartTangentMap a (c.symm y) (Z (c.symm y))) = Z (c.symm y) at hinv
  rw [c.right_inv hy] at hinv
  change fderiv ℝ (f ∘ c.symm) y (N.chartTangentMap a (c.symm y) (Z (c.symm y))) =
    mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, E × (s.erase v₀.val → ℝ)) f
      (c.symm y) (Z (c.symm y))
  have hcomp := mfderiv_comp_apply y hδ
    ((mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n - 2))) a).mdifferentiableAt_symm hy)
    (N.chartTangentMap a (c.symm y) (Z (c.symm y)))
  rw [mfderiv_eq_fderiv] at hcomp
  exact hcomp.trans (congrArg (mfderiv 𝓘(ℝ, Model (2 * n - 2))
    𝓘(ℝ, E × (s.erase v₀.val → ℝ)) f (c.symm y)) hinv)

/-- Actual chart smoothness, actual normal positivity and the proved
zero-section equation yield a nonlinear inequality in the native manifold.
The generic local zero-section hypothesis is discharged by the uniform
branch-rate producer in the critical-torus consumer. -/
theorem exists_local_native_transverse_expansion [FiniteDimensional ℝ E]
    (C : NativeFaceHessianChart φ s H q lam N j a x) (hφ : ContDiff ℝ ∞ φ)
    (hnd : ∀ b, N.Nondegenerate
      (N.exteriorDerivative (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ))) b)
    {Φ : RealSpace n → RealSpace n} (Q : RealSpace n →L[ℝ] E)
    (v₀ : s) (hΦ : ContDiffAt ℝ ∞ Φ x.1) (hHΦ : H = fderiv ℝ Φ x.1)
    (r : s → ℝ) (hmon : ∀ v : s, monomial 1 v.val (lgCover x) = (r v : ℂ))
    (L : (E × (s.erase v₀.val → ℝ)) →L[ℝ] faceFiberPlane q)
    (hL : (faceFiberTransverseDifferential Q H v₀ q r).comp L =
      ContinuousLinearMap.id ℝ (E × (s.erase v₀.val → ℝ)))
    (hzero : conormalTransverseCoordinates Φ Q s v₀.val (lgCover x) = 0)
    (G : (E × (s.erase v₀.val → ℝ)) →L[ℝ] (E × (s.erase v₀.val → ℝ)) →L[ℝ] ℝ)
    (hpos : ∀ z : E × (s.erase v₀.val → ℝ), z ≠ 0 →
      0 < G ((fderiv ℝ (C.coordinateTransverseRate Φ Q v₀)
        (chartAt (Model (2 * n - 2)) a a)) (C.transverseNormalLift v₀ L z)) z)
    (O : Set N.Point) (hO : IsOpen O) (haO : a ∈ O)
    (hδO : ∀ b ∈ O, ContMDiffAt 𝓘(ℝ, Model (2 * n - 2))
      𝓘(ℝ, E × (s.erase v₀.val → ℝ)) ∞
      ((conormalTransverseCoordinates Φ Q s v₀.val) ∘ j.map) b)
    (hRO : ∀ b ∈ O, conormalTransverseCoordinates Φ Q s v₀.val (j.map b) = 0 →
      conormalTransverseRate N j
        (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) Φ Q s v₀.val b = 0) :
    ∃ k : ℝ, 0 < k ∧ ∃ V : Set N.Point, IsOpen V ∧ a ∈ V ∧ V ⊆ O ∧
      ∀ b ∈ V, k * ‖conormalTransverseCoordinates Φ Q s v₀.val (j.map b)‖ ^ 2 ≤
        G (conormalTransverseRate N j
          (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) Φ Q s v₀.val b)
          (conormalTransverseCoordinates Φ Q s v₀.val (j.map b)) := by
  let c := chartAt (Model (2 * n - 2)) a
  let ca := c a
  let δ := C.coordinateTransverseMap Φ Q v₀
  let Rate := C.coordinateTransverseRate Φ Q v₀
  let A := fderiv ℝ δ ca
  have ht : ca ∈ c.target := c.map_source (mem_chart_source _ _)
  have hcenter : c.symm ca = a := c.left_inv (mem_chart_source _ _)
  have hδ := C.coordinateTransverseMap_smooth Q v₀ hΦ
  have hr := C.coordinateTransverseRate_smooth hφ hnd Q v₀ hΦ
  have hright : RightInverse (C.transverseNormalLift v₀ L) A := by
    intro z
    exact congrArg (fun K : (E × (s.erase v₀.val → ℝ)) →L[ℝ] _ => K z)
      (C.transverseNormalLift_rightInverse Q v₀ hΦ hHΦ r hmon L hL)
  have hRateZero : ∀ᶠ y in 𝓝 ca, δ y = 0 → Rate y = 0 := by
    have hnear := (c.continuousAt_symm ht).eventually
      (hO.mem_nhds (hcenter.symm ▸ haO))
    filter_upwards [c.open_target.mem_nhds ht, hnear] with y hy hyO hz
    dsimp only [Rate]
    rw [C.coordinateTransverseRate_eq_native Φ Q v₀ y hy
      ((hδO (c.symm y) hyO).mdifferentiableAt (by simp))]
    exact hRO _ hyO hz
  obtain ⟨k, hk, U, hU, haU, hexpand⟩ :=
    exists_submersion_rate_expansion δ Rate ca A (C.transverseNormalLift v₀ L) G
      hright hδ (hδ.differentiableAt (by simp)).hasFDerivAt
      ((C.coordinateTransverseMap_center Φ Q v₀).trans hzero)
      (hr.of_le (by simp)) hRateZero hpos
  have hn : O ∩ (c.source ∩ c ⁻¹' U) ∈ 𝓝 a :=
    inter_mem (hO.mem_nhds haO) (inter_mem (c.open_source.mem_nhds (mem_chart_source _ _))
      ((c.continuousAt (mem_chart_source _ _)).preimage_mem_nhds (hU.mem_nhds haU)))
  obtain ⟨V, hVsub, hV, haV⟩ := mem_nhds_iff.mp hn
  refine ⟨k, hk, V, hV, haV, fun b hb => (hVsub hb).1, ?_⟩
  intro b hb
  have hbO := (hVsub hb).1
  have hbs := (hVsub hb).2.1
  have hback : (chartAt (Model (2 * n - 2)) a).symm (c b) = b := c.left_inv hbs
  have hrb := C.coordinateTransverseRate_eq_native Φ Q v₀ (c b) (c.map_source hbs)
    (by simpa only [hback] using (hδO b hbO).mdifferentiableAt (by simp))
  have hh := hexpand (c b) (hVsub hb).2.2
  simpa only [δ, Rate, coordinateTransverseMap, hrb, hback] using hh

end NativeFaceHessianChart

namespace CriticalFaceNormalData

variable {n : ℕ} {I : ToricInput n} {φEnd φ : RealSpace n → ℝ} {β : ℝ}
  {s : Finset (Lattice n)} {u : RealSpace n} {q : s → ℝ} {lam : ℝ}
  {B : (s → ℝ) →L[ℝ] RealSpace n} {R : (s → ℝ) →L[ℝ] (s → ℝ)}

/-- The same constructed critical radius and fixed transverse metric give
actual product inverses at every angle. The derivative of the actual rate
in their normal coordinate is positive for that same fixed metric. -/
theorem exists_same_data_native_transverse_products
    (D : CriticalFaceNormalData I φEnd φ β s u q lam B R)
    (hStrong : IsStronglyCompatibleEndPotential I φEnd) (hEnd1 : ContDiff ℝ 1 φEnd)
    (hs : IsPolytopeFace I.vertices s) (hφ : ContDiff ℝ ∞ φ)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hpi : ∀ y, tailoringFamily I β 1 y = 1 →
      0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1) y
        (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n))
    (himage : range j.map = {y | tailoringFamily I β 1 y = 1}) (v₀ : s) :
    let H := fderiv ℝ (coordinateGradient φEnd) u
    let r := criticalFaceTransverseWeights β q
    ∃ W : ConormalTransverseNeighborhoodAt I φEnd β s u v₀,
    ∃ L : (W.projection.ker × (s.erase v₀.val → ℝ)) →L[ℝ] faceFiberPlane q,
      (faceFiberTransverseDifferential W.quotient H v₀ q r).comp L =
        ContinuousLinearMap.id ℝ (W.projection.ker × (s.erase v₀.val → ℝ)) ∧
      (∀ z w, fixedFaceTransverseMetric H q v₀ L z w =
        fixedFaceTransverseMetric H q v₀ L w z) ∧
      (∀ z, z ≠ 0 → 0 < fixedFaceTransverseMetric H q v₀ L z z) ∧
      ∀ θ ∈ coneTorus (positiveCone s),
        ∀ (a : N.Point) (ξ : TangentCoordinates n), j.map a = lgCover ξ →
          lgCover ξ = (u, θ) →
          ∃ C : NativeFaceHessianChart φ s H q lam N j a ξ,
            let ca := chartAt (Model (2 * n - 2)) a a
            let δ := C.coordinateTransverseMap (coordinateGradient φEnd) W.quotient v₀
            let A := fderiv ℝ δ ca
            ∃ e : OpenPartialHomeomorph (Model (2 * n - 2))
                (A.ker × (W.projection.ker × (s.erase v₀.val → ℝ))),
              ca ∈ e.source ∧ (0 : A.ker × (W.projection.ker × (s.erase v₀.val → ℝ))) ∈ e.target ∧
              e ca = 0 ∧ e.symm 0 = ca ∧
              (∀ y, (e y).2 = δ y) ∧ ContDiffAt ℝ ∞ e.symm 0 ∧
              ((fderiv ℝ e.symm 0).comp
                (ContinuousLinearMap.inr ℝ A.ker (W.projection.ker × (s.erase v₀.val → ℝ))) =
                  C.transverseNormalLift v₀ L) ∧
              (∀ p ∈ e.target, δ (e.symm p) = p.2) ∧
              ContDiffAt ℝ ∞ (C.coordinateTransverseRate (coordinateGradient φEnd)
                W.quotient v₀) ca ∧
              (∀ z : W.projection.ker × (s.erase v₀.val → ℝ), z ≠ 0 →
                0 < fixedFaceTransverseMetric H q v₀ L
                (((fderiv ℝ (fun p : A.ker × (W.projection.ker × (s.erase v₀.val → ℝ)) =>
                  C.coordinateTransverseRate (coordinateGradient φEnd)
                  W.quotient v₀ (e.symm p)) 0).comp
                    (ContinuousLinearMap.inr ℝ A.ker
                      (W.projection.ker × (s.erase v₀.val → ℝ)))) z) z) := by
  obtain ⟨W, L, hL, horth, hsym, hpos, hcharts⟩ :=
    D.exists_same_data_fixed_transverse_linearization hStrong hEnd1 hs hφ hc hlower hpi
      N j himage v₀
  refine ⟨W, L, hL, hsym, hpos, ?_⟩
  intro θ hθ a ξ hpoint hξ
  obtain ⟨C, hz, hrzero, hlin, hpair, hself, hlinpos⟩ :=
    (hcharts θ hθ).2 a ξ hpoint hξ
  have hrad : ξ.1 = u := congrArg Prod.fst hξ
  have hΦ : ContDiffAt ℝ ∞ (coordinateGradient φEnd) ξ.1 :=
    hrad.symm ▸ D.gradient_smooth hStrong hEnd1
  have hHΦ : fderiv ℝ (coordinateGradient φEnd) u =
      fderiv ℝ (coordinateGradient φEnd) ξ.1 := by rw [hrad]
  have hmon : ∀ v : s, monomial 1 v.val (lgCover ξ) =
      (criticalFaceTransverseWeights β q v : ℂ) := by
    rw [hξ]
    exact D.transverseWeights_monomial θ hθ
  have hδzero : conormalTransverseCoordinates (coordinateGradient φEnd) W.quotient
      s v₀.val (lgCover ξ) = 0 := by
    rw [hξ]
    exact W.torus_zero θ hθ
  obtain ⟨e, ha, ht, he, hei, hmap, hinv, hnormal, hδ⟩ :=
    C.exists_transverse_product_coordinates W.quotient v₀ hΦ hHΦ
      (criticalFaceTransverseWeights β q) hmon L hL hδzero
  have hrate := C.coordinateTransverseRate_smooth hφ
    (fun b => tailoring_fullFiber_nondegenerate I β hφ hc hlower hpi j himage b)
    W.quotient v₀ hΦ
  refine ⟨C, e, ha, ht, he, hei, hmap, hinv, hnormal, hδ, hrate, ?_⟩
  intro z hz
  have hri : DifferentiableAt ℝ
      (C.coordinateTransverseRate (coordinateGradient φEnd) W.quotient v₀)
        (e.symm 0) := by
    rw [hei]
    exact hrate.differentiableAt (by simp)
  have hd := fderiv_comp 0 hri (hinv.differentiableAt (by simp))
  simp only [Function.comp_def] at hd
  rw [hd, ContinuousLinearMap.comp_assoc, hnormal, hei, ← hlin]
  exact hlinpos z hz

end CriticalFaceNormalData

end FsFltz
