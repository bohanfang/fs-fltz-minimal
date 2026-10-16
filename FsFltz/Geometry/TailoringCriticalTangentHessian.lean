import FsFltz.Geometry.TailoringCriticalCharts

/-!
# Native tangent image and critical Hessian radical

Source: `geometric-part-fsf-proof.tex`, `eq:hessian`, lines 1538–1569,
and `lem:stable`, lines 1713–1724. This identifies the exact image of
actual chart differentials and transports the actual Hessian radical.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set Filter Function
open scoped Topology BigOperators ContDiff Manifold

/-- At a real face point the actual complex differential is the pair of
the same weighted real face constraints. -/
theorem criticalFaceFunction_fderiv_real_weights {n : ℕ}
    (s : Finset (Lattice n)) (β : ℝ) (x : TangentCoordinates n) (q : s → ℝ)
    (hmon : ∀ v : s, monomial (Real.exp (-β) : ℂ) v.val (lgCover x) = (q v : ℂ))
    (V : TangentCoordinates n) :
    fderiv ℝ (criticalFaceFunction s β) x V =
      (faceWeightFunctional q (faceLevelMap s V.1) : ℂ) +
        Complex.I * (faceWeightFunctional q (faceLevelMap s V.2) : ℂ) := by
  classical
  change ∀ v : s, monomial (Real.exp (-β) : ℂ) v.val
    (x.1, angleQuotient x.2) = (q v : ℂ) at hmon
  rw [(hasFDerivAt_criticalFaceFunction s β x).fderiv]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  rw [← Finset.sum_coe_sort s]
  simp only [hmon, exponentLinearMap_eq_pairing,
    mul_add, faceWeightFunctional_apply, faceLevelMap_apply,
    Finset.sum_add_distrib, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- Both components of the literal tangent hyperplane are necessary and
sufficient, even if the ambient or face dimension degenerates. -/
theorem criticalFaceFunction_fderiv_eq_zero_iff {n : ℕ}
    (s : Finset (Lattice n)) (β : ℝ) (x : TangentCoordinates n) (q : s → ℝ)
    (hmon : ∀ v : s, monomial (Real.exp (-β) : ℂ) v.val (lgCover x) = (q v : ℂ))
    (V : TangentCoordinates n) :
    fderiv ℝ (criticalFaceFunction s β) x V = 0 ↔
      V.1 ∈ faceRealTangent q ∧ V.2 ∈ faceRealTangent q := by
  rw [criticalFaceFunction_fderiv_real_weights s β x q hmon]
  simp only [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, mul_zero, sub_zero, add_zero, zero_add,
    Complex.zero_re, Complex.zero_im, mem_faceRealTangent]

/-- The inclusion differential and quotient covering identify exactly the
full face tangent image of every actual lifted chart. -/
theorem logarithmic_chart_lift_range_face_tangent {n d : ℕ}
    (I : ToricInput n) (β : ℝ) (s : Finset (Lattice n)) (q : s → ℝ)
    (N : SmoothManifold d) (j : N.SmoothEmbedding (lgManifold n)) (a : N.Point)
    (x : TangentCoordinates n) (hpoint : j.map a = lgCover x)
    (hkernel : (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) j.map a).range =
      (complexDifferential (lgManifold n) (tailoringFamily I β 1) (j.map a)).ker)
    (hlocal : ∀ᶠ y in 𝓝 (j.map a),
      tailoringFamily I β 1 y = ∑ v ∈ s, monomial (Real.exp (-β) : ℂ) v y)
    (hmon : ∀ v : s, monomial (Real.exp (-β) : ℂ) v.val (lgCover x) = (q v : ℂ))
    {g : Model d → TangentCoordinates n}
    (hg : ContDiffAt ℝ ∞ g (chartAt (Model d) a a))
    (hga : g (chartAt (Model d) a a) = x)
    (heq : ∀ᶠ y in 𝓝 (chartAt (Model d) a a),
      lgCover (g y) = j.map ((chartAt (Model d) a).symm y))
    (V : TangentCoordinates n) :
    V ∈ (fderiv ℝ g (chartAt (Model d) a a)).range ↔
      V.1 ∈ faceRealTangent q ∧ V.2 ∈ faceRealTangent q := by
  have hd := logarithmic_chart_lift_tangent N j a x hg hga heq
  have hchart := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).symm.mfderiv_bijective
    ((chartAt (Model d) a).map_source (mem_chart_source (Model d) a))
  have hcoord : (fun z => tailoringFamily I β 1 (lgCover z)) =ᶠ[𝓝 x]
      criticalFaceFunction s β := by
    have hc : ContinuousAt (lgCover (n := n)) x := (contMDiff_lgCover n).continuous.continuousAt
    have hl : ∀ᶠ y : (lgManifold n).Point in 𝓝 (lgCover x),
        tailoringFamily I β 1 y = ∑ v ∈ s, monomial (Real.exp (-β) : ℂ) v y :=
      hpoint ▸ hlocal
    filter_upwards [hc.tendsto.eventually hl] with y hy
    exact hy
  have hderiv : fderiv ℝ (criticalFaceFunction s β) x =
      (complexDifferential (lgManifold n) (tailoringFamily I β 1) (j.map a)).comp
        (lgCoverTangent x) := by
    rw [← hcoord.fderiv_eq, fderiv_complex_lgCover (contMDiff_tailoringFamily_lgManifold I β 1)]
    rw [hpoint]
  rw [← criticalFaceFunction_fderiv_eq_zero_iff s β x q hmon V]
  rw [hderiv]
  constructor
  · rintro ⟨W, rfl⟩
    have hW := congrArg (fun L : Model d →L[ℝ] Model (2 * n) => L W) hd
    change lgCoverTangent x (fderiv ℝ g (chartAt (Model d) a a) W) = _ at hW
    have hmem : lgCoverTangent x (fderiv ℝ g (chartAt (Model d) a a) W) ∈
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) j.map a).range :=
      ⟨N.inverseChartTangentMap a (chartAt (Model d) a a) W, hW.symm⟩
    rw [hkernel] at hmem
    exact hmem
  · intro hV
    have hmem : lgCoverTangent x V ∈
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) j.map a).range := by
      rw [hkernel]
      exact hV
    obtain ⟨W, hW⟩ := hmem
    obtain ⟨U, hU⟩ := hchart.2 W
    refine ⟨U, (lgCoverTangent_bijective x).1 ?_⟩
    have h := congrArg (fun L : Model d →L[ℝ] Model (2 * n) => L U) hd
    change lgCoverTangent x (fderiv ℝ g (chartAt (Model d) a a) U) =
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) j.map a
        (N.inverseChartTangentMap a (chartAt (Model d) a a) U) at h
    exact h.trans ((congrArg (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) j.map a) hU).trans hW)

/-- The constrained pairing is symmetric when the actual radial Hessian is. -/
theorem faceConstrainedPairing_symm {n : ℕ} (s : Finset (Lattice n))
    (H : RealSpace n →L[ℝ] RealSpace n) (q : s → ℝ) (lam : ℝ)
    (hH : ∀ X Y, (∑ j, H X j * Y j) = ∑ j, H Y j * X j)
    (V W : TangentCoordinates n) :
    faceConstrainedPairing s H q lam V W = faceConstrainedPairing s H q lam W V := by
  have hs (X Y : RealSpace n) :
      (∑ v, q v * faceLevelMap s X v * faceLevelMap s Y v) =
        ∑ v, q v * faceLevelMap s Y v * faceLevelMap s X v :=
    Finset.sum_congr rfl fun _ _ => by ring
  simp only [faceConstrainedPairing, hH V.1 W.1, hs V.1 W.1, hs V.2 W.2]

/-- Polarization of the literal face quadratic form. -/
theorem faceConstrainedHessian_add {n : ℕ} (s : Finset (Lattice n))
    (H : RealSpace n →L[ℝ] RealSpace n) (q : s → ℝ) (lam : ℝ)
    (V W : TangentCoordinates n) :
    faceConstrainedHessian s H q lam (V + W) =
      faceConstrainedHessian s H q lam V + faceConstrainedHessian s H q lam W +
        faceConstrainedPairing s H q lam V W + faceConstrainedPairing s H q lam W V := by
  simp only [faceConstrainedHessian, faceConstrainedPairing, faceWeightSquare,
    Prod.fst_add, Prod.snd_add, map_add, Pi.add_apply, pow_two, add_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  ring

/-- The computed diagonal Hessian determines the entire native chart
Hessian, so its radical is a bilinear kernel rather than a zero cone. -/
theorem second_fderiv_eq_faceConstrainedPairing {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {a : E} (hf : ContDiffAt ℝ ∞ f a)
    (D : E →L[ℝ] TangentCoordinates n) (s : Finset (Lattice n))
    (H : RealSpace n →L[ℝ] RealSpace n) (q : s → ℝ) (lam : ℝ)
    (hH : ∀ X Y, (∑ j, H X j * Y j) = ∑ j, H Y j * X j)
    (hdiag : ∀ V, fderiv ℝ (fderiv ℝ f) a V V = faceConstrainedHessian s H q lam (D V))
    (V W : E) :
    fderiv ℝ (fderiv ℝ f) a V W = faceConstrainedPairing s H q lam (D V) (D W) := by
  have h := hdiag (V + W)
  rw [map_add D, faceConstrainedHessian_add, ← hdiag V, ← hdiag W] at h
  have hsym := hf.isSymmSndFDerivAt (by simp) W V
  have hpair := faceConstrainedPairing_symm s H q lam hH (D W) (D V)
  simp only [map_add, add_apply] at h
  rw [hsym, hpair] at h
  linarith

/-- Transfer of the computed radical through an actual surjective tangent
parametrization. The chart Hessian is identified by its differentiated formula. -/
theorem second_fderiv_face_radical_iff {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {a : E} (hf : ContDiffAt ℝ ∞ f a)
    (D : E →L[ℝ] TangentCoordinates n) {s : Finset (Lattice n)}
    {H : RealSpace n →L[ℝ] RealSpace n} {B : (s → ℝ) →L[ℝ] RealSpace n}
    {R : (s → ℝ) →L[ℝ] (s → ℝ)}
    (hB : (faceLevelMap s).comp B = ContinuousLinearMap.id ℝ (s → ℝ))
    (hnormal : H.comp B = (faceNormalMap s).comp R)
    (hHsym : ∀ X Y, (∑ j, H X j * Y j) = ∑ j, H Y j * X j)
    (hH : ∀ e : RealSpace n, e ≠ 0 → 0 < ∑ j, H e j * e j)
    {q : s → ℝ} (hq : ∀ v, 0 < q v) {lam : ℝ} (hlam : 0 < lam)
    (hnegative : ∀ h : s → ℝ, h ≠ 0 →
      (∑ v, R h v * h v) - lam * faceWeightSquare q h < 0)
    (hrange : ∀ V, V ∈ D.range ↔ V.1 ∈ faceRealTangent q ∧ V.2 ∈ faceRealTangent q)
    (hdiag : ∀ V, fderiv ℝ (fderiv ℝ f) a V V = faceConstrainedHessian s H q lam (D V))
    (V : E) :
    (∀ W : E, fderiv ℝ (fderiv ℝ f) a V W = 0) ↔
      (D V).1 = 0 ∧ faceLevelMap s (D V).2 = 0 := by
  have ht := (hrange (D V)).mp ⟨V, rfl⟩
  rw [← faceConstrainedPairing_radical_iff hB hnormal hH hq hlam hnegative (D V) ht.1 ht.2]
  constructor
  · intro h W hW₁ hW₂
    obtain ⟨w, rfl⟩ := (hrange W).mpr ⟨hW₁, hW₂⟩
    exact (second_fderiv_eq_faceConstrainedPairing hf D s H q lam hHsym hdiag V w).symm.trans (h w)
  · intro h W
    rw [second_fderiv_eq_faceConstrainedPairing hf D s H q lam hHsym hdiag]
    have htW := (hrange (D W)).mp ⟨W, rfl⟩
    exact h (D W) htW.1 htW.2

/-- On the actual regular tailored fiber, the actual chart Hessian has
precisely the angular face-kernel radical. The chart and tangent image are
constructed, while the displayed algebraic hypotheses are the previously
computed actual branch Hessian blocks. -/
theorem tailoring_fullFiber_exists_native_hessian_radical {n : ℕ}
    (I : ToricInput n) (β : ℝ) {φ ψ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hpi : ∀ y, tailoringFamily I β 1 y = 1 →
      0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1) y
        (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    (s : Finset (Lattice n)) (lam : ℝ) (q : s → ℝ)
    (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n))
    (himage : range j.map = {y | tailoringFamily I β 1 y = 1})
    (a : N.Point) (x : TangentCoordinates n) (hpoint : j.map a = lgCover x)
    (hlocal : ∀ᶠ y in 𝓝 (j.map a),
      tailoringFamily I β 1 y = ∑ v ∈ s, monomial (Real.exp (-β) : ℂ) v y)
    (hpot : φ =ᶠ[𝓝 x.1] ψ)
    (hmon : ∀ v : s, monomial (Real.exp (-β) : ℂ) v.val (lgCover x) = (q v : ℂ))
    (hcritical : coordinateGradient ψ x.1 = lam • faceNormalMap s q)
    {B : (s → ℝ) →L[ℝ] RealSpace n} {R : (s → ℝ) →L[ℝ] (s → ℝ)}
    (hB : (faceLevelMap s).comp B = ContinuousLinearMap.id ℝ (s → ℝ))
    (hnormal : (fderiv ℝ (coordinateGradient ψ) x.1).comp B = (faceNormalMap s).comp R)
    (hH : ∀ e : RealSpace n, e ≠ 0 → 0 < ∑ j, fderiv ℝ (coordinateGradient ψ) x.1 e j * e j)
    (hq : ∀ v, 0 < q v) (hlam : 0 < lam)
    (hnegative : ∀ h : s → ℝ, h ≠ 0 →
      (∑ v, R h v * h v) - lam * faceWeightSquare q h < 0) :
    ∃ g : Model (2 * n - 2) → TangentCoordinates n,
      ContDiffAt ℝ ∞ g (chartAt (Model (2 * n - 2)) a a) ∧
      g (chartAt (Model (2 * n - 2)) a a) = x ∧
      (∀ᶠ y in 𝓝 (chartAt (Model (2 * n - 2)) a a),
        lgCover (g y) = j.map ((chartAt (Model (2 * n - 2)) a).symm y)) ∧
      Injective (fderiv ℝ g (chartAt (Model (2 * n - 2)) a a)) ∧
      (∀ V, V ∈ (fderiv ℝ g (chartAt (Model (2 * n - 2)) a a)).range ↔
        V.1 ∈ faceRealTangent q ∧ V.2 ∈ faceRealTangent q) ∧
      ∀ V : Model (2 * n - 2),
        (∀ W : Model (2 * n - 2),
          fderiv ℝ (fderiv ℝ (fun y => φ (j.map ((chartAt (Model (2 * n - 2)) a).symm y)).1))
            (chartAt (Model (2 * n - 2)) a a) V W = 0) ↔
          (fderiv ℝ g (chartAt (Model (2 * n - 2)) a a) V).1 = 0 ∧
            faceLevelMap s (fderiv ℝ g (chartAt (Model (2 * n - 2)) a a) V).2 = 0 := by
  obtain ⟨g, hg, hga, heq, hinj, _, _, hh⟩ :=
    tailoring_fullFiber_exists_native_hessian_chart I β hφ s lam q N j himage a x
      hpoint hlocal hpot hmon hcritical
  have hkernel := tailoringFamily_levelEmbedding_tangent_range I hφ hc hlower β 1 1 hpi j himage a
  have hrange := logarithmic_chart_lift_range_face_tangent I β s q N j a x hpoint
    hkernel hlocal hmon hg hga heq
  have he : (fun y => φ (j.map ((chartAt (Model (2 * n - 2)) a).symm y)).1) =ᶠ[
      𝓝 (chartAt (Model (2 * n - 2)) a a)] (fun y => φ (g y).1) := by
    filter_upwards [heq] with y hy
    exact (congrArg (fun z : LGSpace n => φ z.1) hy).symm
  have hsmooth : ContDiffAt ℝ ∞
      (fun y => φ (j.map ((chartAt (Model (2 * n - 2)) a).symm y)).1)
      (chartAt (Model (2 * n - 2)) a a) :=
    (hφ.contDiffAt.comp _ hg.fst).congr_of_eventuallyEq he
  have hHsym (X Y : RealSpace n) :
      (∑ j, fderiv ℝ (coordinateGradient ψ) x.1 X j * Y j) =
        ∑ j, fderiv ℝ (coordinateGradient ψ) x.1 Y j * X j := by
    rw [← coordinateHessian_eq_of_eventuallyEq hpot]
    exact coordinate_hessian_symmetric_at (hφ.differentiable (by simp)) hφ.contDiffAt X Y
  refine ⟨g, hg, hga, heq, hinj, hrange, ?_⟩
  intro V
  exact second_fderiv_face_radical_iff hsmooth _ hB hnormal hHsym hH hq hlam
    hnegative hrange hh V

end FsFltz
