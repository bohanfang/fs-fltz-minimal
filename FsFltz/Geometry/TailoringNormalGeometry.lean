import FsFltz.Geometry.TailoringConormalBranch
import FsFltz.Geometry.TailoringCriticalTorusTangent
import FsFltz.Geometry.TailoringGradientIdentity
import FsFltz.Analysis.ToricConeNeighborhood

/-!
# The metric normal of the actual conormal branch

Source: `geometric-part-fsf-proof.tex`, `prop:morsebott`, lines 1538–1569,
and `lem:stable`, lines 1709–1724. The full-span radial condition is
identified with the actual Hessian complement. Positivity is transported
to the second derivative of the restricted potential in its native chart.
Construction of normal tubular coordinates and their field equation remains
a separate geometric obligation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Geometry.SmoothManifold Set Filter Function TopologicalSpace
open scoped Topology BigOperators ContDiff Manifold

variable {n : ℕ}

/-- The real face span is exactly the range of the literal face-normal map. -/
theorem faceNormalMap_range_eq_span_positiveCone (s : Finset (Lattice n)) :
    (faceNormalMap s).toLinearMap.range = Submodule.span ℝ (positiveCone s) := by
  classical
  apply le_antisymm
  · rintro p ⟨a, rfl⟩
    let b : s → ℝ := fun v => max (a v) 0
    let c : s → ℝ := fun v => max (-a v) 0
    have he : a = b - c := by
      funext v
      dsimp only [b, c, Pi.sub_apply]
      rcases le_total (a v) 0 with h | h
      · rw [max_eq_right h, max_eq_left (by linarith)]
        ring
      · rw [max_eq_left h, max_eq_right (by linarith)]
        ring
    rw [he, map_sub]
    exact Submodule.sub_mem _
      (Submodule.subset_span (faceNormalMap_mem_positiveCone b (fun v => le_max_right _ _)))
      (Submodule.subset_span (faceNormalMap_mem_positiveCone c (fun v => le_max_right _ _)))
  · apply Submodule.span_le.mpr
    rintro p ⟨a, _, ha⟩
    refine ⟨fun v => a v.val, ?_⟩
    change faceNormalMap s (fun v => a v.val) = p
    rw [faceNormalMap_apply, Finset.sum_coe_sort s (fun v => a v • latticeReal v), ← ha]

/-- The full-span branch condition is exactly the actual Hessian-orthogonal
minimizer lift. -/
theorem face_hessian_mem_span_iff {s : Finset (Lattice n)}
    {H : RealSpace n →L[ℝ] RealSpace n} {B : (s → ℝ) →L[ℝ] RealSpace n}
    {R : (s → ℝ) →L[ℝ] (s → ℝ)}
    (hB : (faceLevelMap s).comp B = ContinuousLinearMap.id ℝ (s → ℝ))
    (hnormal : H.comp B = (faceNormalMap s).comp R)
    (hH : ∀ e : RealSpace n, e ≠ 0 → 0 < ∑ j, H e j * e j)
    (X : RealSpace n) :
    H X ∈ Submodule.span ℝ (positiveCone s) ↔ X = B (faceLevelMap s X) := by
  rw [← faceNormalMap_range_eq_span_positiveCone]
  constructor
  · rintro ⟨a, ha⟩
    apply (face_minimum_lift_eq_orthogonal hB hnormal hH X).mp
    intro e he
    change faceNormalMap s a = H X at ha
    rw [← ha, faceNormalMap_pairing s a e, he]
    simp
  · intro he
    refine ⟨R (faceLevelMap s X), ?_⟩
    have h := congrArg (fun L : (s → ℝ) →L[ℝ] RealSpace n => L (faceLevelMap s X)) hnormal
    change H (B (faceLevelMap s X)) = faceNormalMap s (R (faceLevelMap s X)) at h
    exact h.symm.trans (congrArg H he.symm)

/-- The source's smooth branch tangent in logarithmic coordinates, with
the full real face span rather than the singular union of cones. -/
def faceConormalTangent (s : Finset (Lattice n))
    (H : RealSpace n →L[ℝ] RealSpace n) (q : s → ℝ) :
    Submodule ℝ (TangentCoordinates n) :=
  (faceRealTangent q ⊓
    (Submodule.span ℝ (positiveCone s)).comap H.toLinearMap).prod
      (faceLevelMap s).toLinearMap.ker

@[simp] theorem mem_faceConormalTangent (s : Finset (Lattice n))
    (H : RealSpace n →L[ℝ] RealSpace n) (q : s → ℝ) (V : TangentCoordinates n) :
    V ∈ faceConormalTangent s H q ↔ V.1 ∈ faceRealTangent q ∧
      H V.1 ∈ Submodule.span ℝ (positiveCone s) ∧ faceLevelMap s V.2 = 0 := by
  simp only [faceConormalTangent, Submodule.mem_prod, Submodule.mem_inf,
    Submodule.mem_comap, LinearMap.mem_ker, and_assoc]
  rfl

/-- The actual Hessian metric in radial and angular logarithmic coordinates. -/
def faceHessianMetric (H : RealSpace n →L[ℝ] RealSpace n)
    (V W : TangentCoordinates n) : ℝ :=
  (∑ j, H V.1 j * W.1 j) + ∑ j, H V.2 j * W.2 j

/-- The metric is the actual descended potential form evaluated against the
standard complex rotation, in every pair of quotient-cover tangents. -/
theorem exteriorDerivative_lambdaPotentialForm_metric_eq {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x V W : TangentCoordinates n) :
    evalTwo ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x)
      (lgCoverTangent x V) (lgCoverTangent x (coordinateComplexStructure n W)) =
      faceHessianMetric (fderiv ℝ (coordinateGradient φ) x.1) V W := by
  rw [exteriorDerivative_lambdaPotentialForm_lgCover hφ]
  simp only [coordinateComplexStructure_apply, map_neg, Pi.neg_apply,
    neg_mul, sub_neg_eq_add, Finset.sum_add_distrib, faceHessianMetric]
  congr 1
  exact coordinate_hessian_symmetric_at (hφ.differentiable (by simp)) hφ.contDiffAt W.2 V.2

/-- Positive weights give a positive weighted square on every nonzero vector. -/
theorem faceWeightSquare_pos {s : Finset (Lattice n)} {q h : s → ℝ}
    (hq : ∀ v, 0 < q v) (hh : h ≠ 0) : 0 < faceWeightSquare q h := by
  classical
  have hne : ∃ v, h v ≠ 0 := by contrapose! hh; exact funext hh
  obtain ⟨v, hv⟩ := hne
  exact (mul_pos (hq v) (sq_pos_of_ne_zero hv)).trans_le
    (Finset.single_le_sum (fun w _ => mul_nonneg (hq w).le (sq_nonneg _))
      (Finset.mem_univ v))

/-- The positive source blocks form the metric normal to the actual branch
tangent; no negative-block assumption is needed for this positivity. -/
theorem faceConstrainedHessian_pos_on_conormal_normal {s : Finset (Lattice n)}
    {H : RealSpace n →L[ℝ] RealSpace n} {B : (s → ℝ) →L[ℝ] RealSpace n}
    {R : (s → ℝ) →L[ℝ] (s → ℝ)}
    (hB : (faceLevelMap s).comp B = ContinuousLinearMap.id ℝ (s → ℝ))
    (hnormal : H.comp B = (faceNormalMap s).comp R)
    (hHsym : ∀ X Y, (∑ j, H X j * Y j) = ∑ j, H Y j * X j)
    (hH : ∀ e : RealSpace n, e ≠ 0 → 0 < ∑ j, H e j * e j)
    {q : s → ℝ} (hq : ∀ v, 0 < q v) {lam : ℝ} (hlam : 0 < lam)
    (V : TangentCoordinates n) (hV : V ≠ 0)
    (hX : V.1 ∈ faceRealTangent q)
    (horth : ∀ W ∈ faceConormalTangent s H q, faceHessianMetric H V W = 0) :
    0 < faceConstrainedHessian s H q lam V := by
  have hright (a : s → ℝ) : faceLevelMap s (B a) = a :=
    congrArg (fun L : (s → ℝ) →L[ℝ] (s → ℝ) => L a) hB
  let e := V.1 - B (faceLevelMap s V.1)
  have he : faceLevelMap s e = 0 := by rw [map_sub, hright, sub_self]
  have hBX : (B (faceLevelMap s V.1), 0) ∈ faceConormalTangent s H q := by
    rw [mem_faceConormalTangent]
    refine ⟨?_, (face_hessian_mem_span_iff hB hnormal hH _).mpr ?_, by simp⟩
    · simpa only [mem_faceRealTangent, hright] using hX
    · rw [hright]
  have hzero := horth _ hBX
  simp only [faceHessianMetric, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero] at hzero
  have hcross : (∑ j, H e j * B (faceLevelMap s V.1) j) = 0 :=
    (hHsym _ _).trans (face_minimum_lift_orthogonal hnormal he _)
  have hbzero : (∑ j, H (B (faceLevelMap s V.1)) j * B (faceLevelMap s V.1) j) = 0 := by
    have heq : V.1 = e + B (faceLevelMap s V.1) := (sub_add_cancel _ _).symm
    conv at hzero => lhs; arg 2; ext j; arg 1; rw [heq]
    simp only [map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib] at hzero
    linarith
  have hb : B (faceLevelMap s V.1) = 0 := by
    by_contra hne
    have hp := hH _ hne
    rw [hbzero] at hp
    exact lt_irrefl 0 hp
  have hAX : faceLevelMap s V.1 = 0 := by
    have h := congrArg (faceLevelMap s) hb
    simpa only [hright, map_zero] using h
  have hBY : V.2 = B (faceLevelMap s V.2) := by
    apply (face_minimum_lift_eq_orthogonal hB hnormal hH _).mp
    intro f hf
    have hm : (0, f) ∈ faceConormalTangent s H q := by
      simp only [mem_faceConormalTangent, map_zero]
      exact ⟨by simp, Submodule.zero_mem _, hf⟩
    have h := horth _ hm
    simpa only [faceHessianMetric, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add] using h
  have hrnonneg : 0 ≤ ∑ j, H V.1 j * V.1 j := by
    by_cases hx : V.1 = 0
    · simp [hx]
    · exact (hH _ hx).le
  have hsq : 0 ≤ faceWeightSquare q (faceLevelMap s V.2) :=
    Finset.sum_nonneg fun v _ => mul_nonneg (hq v).le (sq_nonneg _)
  rw [faceConstrainedHessian, hAX]
  simp only [faceWeightSquare, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0),
    mul_zero, Finset.sum_const_zero, sub_zero]
  by_cases hx : V.1 = 0
  · have hy : V.2 ≠ 0 := by
      intro hy
      exact hV (Prod.ext hx hy)
    have hAY : faceLevelMap s V.2 ≠ 0 := by
      intro ha
      rw [ha, map_zero] at hBY
      exact hy hBY
    have hp := mul_pos hlam (faceWeightSquare_pos hq hAY)
    dsimp only [faceWeightSquare] at hp
    linarith
  · exact add_pos_of_pos_of_nonneg (hH _ hx) (mul_nonneg hlam.le hsq)

/-- The second derivative here is the actual restricted potential in its
native fiber chart; the tangent map is constructed and injective. -/
theorem NativeFaceHessianChart.hessian_pos_on_conormal_normal {n d : ℕ}
    {φ : RealSpace n → ℝ} {s : Finset (Lattice n)}
    {H : RealSpace n →L[ℝ] RealSpace n} {q : s → ℝ} {lam : ℝ}
    {N : SmoothManifold d} {j : N.SmoothEmbedding (lgManifold n)}
    {a : N.Point} {x : TangentCoordinates n}
    (C : NativeFaceHessianChart φ s H q lam N j a x)
    {B : (s → ℝ) →L[ℝ] RealSpace n} {R : (s → ℝ) →L[ℝ] (s → ℝ)}
    (hB : (faceLevelMap s).comp B = ContinuousLinearMap.id ℝ (s → ℝ))
    (hnormal : H.comp B = (faceNormalMap s).comp R)
    (hHsym : ∀ X Y, (∑ j, H X j * Y j) = ∑ j, H Y j * X j)
    (hH : ∀ e : RealSpace n, e ≠ 0 → 0 < ∑ j, H e j * e j)
    (hq : ∀ v, 0 < q v) (hlam : 0 < lam)
    (v : Model d) (hv : v ≠ 0)
    (horth : ∀ W ∈ faceConormalTangent s H q,
      faceHessianMetric H (fderiv ℝ C.lift (chartAt (Model d) a a) v) W = 0) :
    0 < fderiv ℝ (fderiv ℝ (fun y => φ (j.map ((chartAt (Model d) a).symm y)).1))
      (chartAt (Model d) a a) v v := by
  rw [C.hessian, faceConstrainedPairing_self]
  have ht := (C.tangent_range _).mp ⟨v, rfl⟩
  apply faceConstrainedHessian_pos_on_conormal_normal hB hnormal hHsym hH hq hlam
    _ _ ht.1 horth
  intro he
  exact hv (C.immersion (he.trans (map_zero _).symm))

section ActualBranchDifferential

variable {K : Type} [NormedAddCommGroup K] [NormedSpace ℝ K] {m : ℕ}

/-- The actual radial-angular branch map, with the same recharted ambient
manifold as the full-fiber native Hessian. -/
def conormalBranchAmbientMap (g : K → RealSpace n) (f : Torus m → Torus n)
    (p : K × Torus m) : (lgManifold n).Point := (g p.1, f p.2)

theorem contMDiffAt_conormalBranchAmbientMap {g : K → RealSpace n}
    {f : Torus m → Torus n} {q : K} {θ : Torus m}
    (hg : ContDiffAt ℝ ∞ g q)
    (hf : ContMDiffAt (torusModel m) (torusModel n) ∞ f θ) :
    ContMDiffAt ((𝓘(ℝ, K)).prod (torusModel m)) 𝓘(ℝ, Model (2 * n)) ∞
      (conormalBranchAmbientMap g f) (q, θ) := by
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  exact (contMDiff_linearRechart_id (M := LGSpace n) (lgEuclideanEquiv n)).contMDiffAt.comp
    (q, θ) (hg.contMDiffAt.prodMap hf)

/-- The radial part of the true branch differential is the cover transport
of the literal radial derivative, with zero angular component. -/
theorem conormalBranchAmbientMap_deriv_radial {g : K → RealSpace n}
    {f : Torus m → Torus n} {q : K} {θ : Torus m}
    (hg : ContDiffAt ℝ ∞ g q)
    (hf : ContMDiffAt (torusModel m) (torusModel n) ∞ f θ)
    (x : TangentCoordinates n) (hpoint : conormalBranchAmbientMap g f (q, θ) = lgCover x)
    (v : K) :
    mfderiv ((𝓘(ℝ, K)).prod (torusModel m)) 𝓘(ℝ, Model (2 * n))
      (conormalBranchAmbientMap g f) (q, θ) (v, 0) =
        lgCoverTangent x (fderiv ℝ g q v, 0) := by
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hrad : g q = x.1 := congrArg Prod.fst hpoint
  have hang : f θ = angleQuotient x.2 := congrArg Prod.snd hpoint
  let ι : K → K × Torus m := fun a => (a, θ)
  have hι : ContMDiff 𝓘(ℝ, K) ((𝓘(ℝ, K)).prod (torusModel m)) ∞ ι :=
    contMDiff_id.prodMk contMDiff_const
  have h := mfderiv_comp_apply q
    ((contMDiffAt_conormalBranchAmbientMap hg hf).mdifferentiableAt (by simp))
    (hι.mdifferentiable (by simp) q) v
  have hdι : mfderiv 𝓘(ℝ, K) ((𝓘(ℝ, K)).prod (torusModel m)) ι q v = (v, 0) := by
    have he := mfderiv_prodMk (I := 𝓘(ℝ, K))
      (I' := 𝓘(ℝ, K)) (I'' := torusModel m) (x := q)
      (f := id) (g := fun _ => θ) mdifferentiableAt_id mdifferentiableAt_const
    exact congrArg (fun L : K →L[ℝ] K × TorusCoordinates m => L v)
      (by simpa only [mfderiv_id, mfderiv_const] using he)
  rw [hdι] at h
  let G : K → TangentCoordinates n := fun a => (g a, x.2)
  have hG : ContDiffAt ℝ ∞ G q := hg.prodMk contDiffAt_const
  have hGq : G q = x := Prod.ext hrad rfl
  have heq : (conormalBranchAmbientMap g f) ∘ ι = lgCover ∘ G := by
    funext a
    exact Prod.ext rfl hang
  have h' := mfderiv_comp_apply q
    (hGq ▸ (contMDiff_lgCover n).mdifferentiable (by simp) x)
    (hG.contMDiffAt.mdifferentiableAt (by simp)) v
  rw [heq] at h
  rw [mfderiv_eq_fderiv, ((hg.differentiableAt (by simp)).hasFDerivAt.prodMk
    (hasFDerivAt_const x.2 q)).fderiv] at h'
  change mfderiv 𝓘(ℝ, K) 𝓘(ℝ, Model (2 * n)) (lgCover ∘ G) q v =
    lgCoverTangent (G q) (fderiv ℝ g q v, 0) at h'
  have hd : (lgCoverTangent (G q) : TangentCoordinates n →L[ℝ] Model (2 * n)) =
      lgCoverTangent x := by
    let Dc (y : TangentCoordinates n) : TangentCoordinates n →L[ℝ] Model (2 * n) :=
      lgCoverTangent y
    exact congrArg Dc hGq
  change (mfderiv 𝓘(ℝ, K) 𝓘(ℝ, Model (2 * n)) (lgCover ∘ G) q v : Model (2 * n)) =
    (lgCoverTangent (G q) : TangentCoordinates n →L[ℝ] Model (2 * n))
      (fderiv ℝ g q v, 0) at h'
  rw [hd] at h'
  exact h.symm.trans h'

/-- The angular part is precisely the differential of the actual
constant-radius face torus. -/
theorem conormalBranchAmbientMap_deriv_angular {g : K → RealSpace n}
    {f : Torus m → Torus n} {q : K} {θ : Torus m}
    (hg : ContDiffAt ℝ ∞ g q)
    (hf : ContMDiffAt (torusModel m) (torusModel n) ∞ f θ)
    (v : TorusCoordinates m) :
    mfderiv ((𝓘(ℝ, K)).prod (torusModel m)) 𝓘(ℝ, Model (2 * n))
      (conormalBranchAmbientMap g f) (q, θ) (0, v) =
        mfderiv (torusModel m) 𝓘(ℝ, Model (2 * n)) (faceTorusAmbientMap (g q) f) θ v := by
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  let ι : Torus m → K × Torus m := fun α => (q, α)
  have hι : ContMDiff (torusModel m) ((𝓘(ℝ, K)).prod (torusModel m)) ∞ ι :=
    contMDiff_const.prodMk contMDiff_id
  have h := mfderiv_comp_apply θ
    ((contMDiffAt_conormalBranchAmbientMap hg hf).mdifferentiableAt (by simp))
    (hι.mdifferentiable (by simp) θ) v
  have hdι : mfderiv (torusModel m) ((𝓘(ℝ, K)).prod (torusModel m)) ι θ v = (0, v) := by
    have he := mfderiv_prodMk (I := torusModel m)
      (I' := 𝓘(ℝ, K)) (I'' := torusModel m) (x := θ)
      (f := fun _ => q) (g := id) mdifferentiableAt_const mdifferentiableAt_id
    exact congrArg (fun L : TorusCoordinates m →L[ℝ] K × TorusCoordinates m => L v)
      (by simpa only [mfderiv_const, mfderiv_id] using he)
  rw [hdι] at h
  exact h.symm

/-- Join both actual branch differential components. The radial image is
the exact derivative range supplied by the constructed conormal branch. -/
theorem conormalBranchAmbientMap_tangent_iff (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hsne : s.Nonempty) (hsproper : s ≠ I.vertices)
    {g : K → RealSpace n} {f : Torus (n - s.card) → Torus n} {q : K}
    (hg : ContDiffAt ℝ ∞ g q)
    (hf : ContMDiff (torusModel (n - s.card)) (torusModel n) ∞ f)
    (hfrange : range f = coneTorus (positiveCone s))
    (θ : Torus (n - s.card)) (x : TangentCoordinates n)
    (hpoint : conormalBranchAmbientMap g f (q, θ) = lgCover x)
    (hfi : Injective (mfderiv (torusModel (n - s.card)) 𝓘(ℝ, Model (2 * n))
      (faceTorusAmbientMap (g q) f) θ))
    (H : RealSpace n →L[ℝ] RealSpace n) (w : s → ℝ)
    (hgrange : range (fderiv ℝ g q) = {X | X ∈ faceRealTangent w ∧
      H X ∈ Submodule.span ℝ (positiveCone s)})
    (V : TangentCoordinates n) :
    lgCoverTangent x V ∈
      (mfderiv ((𝓘(ℝ, K)).prod (torusModel (n - s.card))) 𝓘(ℝ, Model (2 * n))
        (conormalBranchAmbientMap g f) (q, θ)).range ↔
          V ∈ faceConormalTangent s H w := by
  let D : K × TorusCoordinates (n - s.card) →L[ℝ] Model (2 * n) :=
    mfderiv ((𝓘(ℝ, K)).prod (torusModel (n - s.card)))
    𝓘(ℝ, Model (2 * n)) (conormalBranchAmbientMap g f) (q, θ)
  let L : TangentCoordinates n →L[ℝ] Model (2 * n) := lgCoverTangent x
  have hr (a : K) : D (a, 0) = L (fderiv ℝ g q a, 0) :=
    conormalBranchAmbientMap_deriv_radial hg (hf θ) x hpoint a
  have ha (a : TorusCoordinates (n - s.card)) : D (0, a) =
      mfderiv (torusModel (n - s.card)) 𝓘(ℝ, Model (2 * n))
        (faceTorusAmbientMap (g q) f) θ a :=
    conormalBranchAmbientMap_deriv_angular hg (hf θ) a
  have htor (W : TangentCoordinates n) := faceTorusAmbientMap_tangent_iff I hs hsne hsproper
    (g q) hf hfrange θ x hpoint hfi W
  constructor
  · rintro ⟨⟨a, b⟩, hab⟩
    obtain ⟨Y, hY⟩ : ∃ Y, L Y = D (0, b) := (lgCoverTangent_bijective x).2 (D (0, b))
    have htorY := (htor Y).mp ⟨b, (ha b).symm.trans hY.symm⟩
    have hsplit : V = (fderiv ℝ g q a, 0) + Y := by
      apply (show Injective L from lgCoverTangent_injective x)
      rw [map_add, ← hr, hY]
      have he : (a, 0) + (0, b) = (a, b) := by simp
      exact (show L V = D (a, b) from hab.symm).trans
        ((congrArg D he).symm.trans (map_add D _ _))
    have hgrad : fderiv ℝ g q a ∈ {X | X ∈ faceRealTangent w ∧
        H X ∈ Submodule.span ℝ (positiveCone s)} := by
      rw [← hgrange]
      exact ⟨a, rfl⟩
    rw [mem_faceConormalTangent, hsplit]
    simpa only [Prod.fst_add, Prod.snd_add, htorY.1, add_zero, zero_add] using
      ⟨hgrad.1, hgrad.2, htorY.2⟩
  · rw [mem_faceConormalTangent]
    rintro ⟨hV₁, hHV₁, hV₂⟩
    obtain ⟨a, ha'⟩ : V.1 ∈ range (fderiv ℝ g q) := hgrange.symm ▸ ⟨hV₁, hHV₁⟩
    obtain ⟨b, hb⟩ := (htor (0, V.2)).mpr ⟨rfl, hV₂⟩
    change (mfderiv (torusModel (n - s.card)) 𝓘(ℝ, Model (2 * n))
      (faceTorusAmbientMap (g q) f) θ b : Model (2 * n)) = L (0, V.2) at hb
    refine ⟨(a, b), ?_⟩
    have he : (a, b) = (a, 0) + (0, b) := by simp
    change D (a, b) = L V
    rw [he, map_add, hr, ha, hb, ← map_add, ha']
    congr 1
    exact Prod.ext (by simp) (by simp)

end ActualBranchDifferential

/-- The native fiber Hessian is positive on the normal measured against
the actual branch differential by the literal descended potential form. -/
theorem NativeFaceHessianChart.hessian_pos_on_actual_branch_normal {n d : ℕ}
    {K : Type} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (I : ToricInput n) {s : Finset (Lattice n)}
    (hs : IsPolytopeFace I.vertices s) (hsne : s.Nonempty) (hsproper : s ≠ I.vertices)
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {H : RealSpace n →L[ℝ] RealSpace n} {w : s → ℝ} {lam : ℝ}
    {N : SmoothManifold d} {j : N.SmoothEmbedding (lgManifold n)}
    {a : N.Point} {x : TangentCoordinates n}
    (C : NativeFaceHessianChart φ s H w lam N j a x)
    (hHφ : H = fderiv ℝ (coordinateGradient φ) x.1)
    {g : K → RealSpace n} {f : Torus (n - s.card) → Torus n} {q : K}
    (hg : ContDiffAt ℝ ∞ g q)
    (hf : ContMDiff (torusModel (n - s.card)) (torusModel n) ∞ f)
    (hfrange : range f = coneTorus (positiveCone s))
    (θ : Torus (n - s.card))
    (hpoint : conormalBranchAmbientMap g f (q, θ) = lgCover x)
    (hfi : Injective (mfderiv (torusModel (n - s.card)) 𝓘(ℝ, Model (2 * n))
      (faceTorusAmbientMap (g q) f) θ))
    (hgrange : range (fderiv ℝ g q) = {X | X ∈ faceRealTangent w ∧
      H X ∈ Submodule.span ℝ (positiveCone s)})
    {B : (s → ℝ) →L[ℝ] RealSpace n} {R : (s → ℝ) →L[ℝ] (s → ℝ)}
    (hB : (faceLevelMap s).comp B = ContinuousLinearMap.id ℝ (s → ℝ))
    (hnormal : H.comp B = (faceNormalMap s).comp R)
    (hHsym : ∀ X Y, (∑ j, H X j * Y j) = ∑ j, H Y j * X j)
    (hH : ∀ e : RealSpace n, e ≠ 0 → 0 < ∑ j, H e j * e j)
    (hw : ∀ v, 0 < w v) (hlam : 0 < lam)
    (v : Model d) (hv : v ≠ 0)
    (horth : ∀ W : TangentCoordinates n,
      lgCoverTangent x W ∈
        (mfderiv ((𝓘(ℝ, K)).prod (torusModel (n - s.card))) 𝓘(ℝ, Model (2 * n))
          (conormalBranchAmbientMap g f) (q, θ)).range →
      evalTwo ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x)
        (lgCoverTangent x (fderiv ℝ C.lift (chartAt (Model d) a a) v))
        (lgCoverTangent x (coordinateComplexStructure n W)) = 0) :
    0 < fderiv ℝ (fderiv ℝ (fun y => φ (j.map ((chartAt (Model d) a).symm y)).1))
      (chartAt (Model d) a a) v v := by
  apply C.hessian_pos_on_conormal_normal hB hnormal hHsym hH hw hlam v hv
  intro W hW
  have h := horth W
    ((conormalBranchAmbientMap_tangent_iff I hs hsne hsproper hg hf hfrange θ x
      hpoint hfi H w hgrange W).mpr hW)
  rw [exteriorDerivative_lambdaPotentialForm_metric_eq hφ, ← hHφ] at h
  exact h

/-- The ambient conormal germ and the exact holomorphic face germ identify
the scalar radial level derivative with the real face-tangent constraint. -/
theorem tailoringRadialFunction_fderiv_eq_face_constraint
    (I : ToricInput n) (β : ℝ) (s : Finset (Lattice n))
    (x : TangentCoordinates n) (q : s → ℝ)
    (hlocal : ∀ᶠ y in 𝓝 (lgCover x), tailoringFamily I β 1 y =
      ∑ v ∈ s, monomial (Real.exp (-β) : ℂ) v y)
    (hradial : ∀ᶠ u in 𝓝 x.1,
      tailoringFamily I β 1 (u, angleQuotient x.2) = (tailoringRadialFunction I β u : ℝ))
    (hmon : ∀ v : s, monomial (Real.exp (-β) : ℂ) v.val (lgCover x) = (q v : ℂ))
    (X : RealSpace n) :
    fderiv ℝ (tailoringRadialFunction I β) x.1 X =
      faceWeightFunctional q (faceLevelMap s X) := by
  let G : RealSpace n → TangentCoordinates n := fun u => (u, x.2)
  have hG : ContDiff ℝ ∞ G := contDiff_id.prodMk contDiff_const
  have hG₀ : G x.1 = x := rfl
  have hc : ContinuousAt (fun u => lgCover (G u)) x.1 :=
    (contMDiff_lgCover n).continuous.continuousAt.comp hG.continuous.continuousAt
  have he : (fun u => (criticalFaceFunction s β (G u)).re) =ᶠ[𝓝 x.1]
      tailoringRadialFunction I β := by
    filter_upwards [hc.tendsto.eventually hlocal, hradial] with u hu hr
    change tailoringFamily I β 1 (lgCover (G u)) = criticalFaceFunction s β (G u) at hu
    rw [← hu]
    exact congrArg Complex.re hr
  have hgder := (hasFDerivAt_id (𝕜 := ℝ) x.1).prodMk (hasFDerivAt_const x.2 x.1)
  have hder := Complex.reCLM.hasFDerivAt.comp x.1
    ((hasFDerivAt_criticalFaceFunction s β x).comp x.1 hgder)
  change HasFDerivAt (fun u => (criticalFaceFunction s β (G u)).re) _ x.1 at hder
  have h := congrArg (fun L : RealSpace n →L[ℝ] ℝ => L X) (he.fderiv_eq (𝕜 := ℝ))
  rw [hder.fderiv] at h
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, zero_apply] at h
  rw [← (hasFDerivAt_criticalFaceFunction s β x).fderiv,
    criticalFaceFunction_fderiv_real_weights s β x q hmon] at h
  simpa only [Complex.reCLM_apply, map_zero, Complex.ofReal_zero, mul_zero, add_zero,
    Complex.ofReal_re] using h.symm

/-- An angular immersion remains an immersion after adjoining a constant
radial coordinate, in the actual recharted ambient manifold. -/
theorem faceTorusAmbientMap_immersion_of_immersion {m : ℕ} (u : RealSpace n)
    {f : Torus m → Torus n}
    (hf : ContMDiff (torusModel m) (torusModel n) ∞ f)
    (θ : Torus m) (hi : Injective (mfderiv (torusModel m) (torusModel n) f θ)) :
    Injective (mfderiv (torusModel m) 𝓘(ℝ, Model (2 * n))
      (faceTorusAmbientMap u f) θ) := by
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hsnd : ContMDiff 𝓘(ℝ, Model (2 * n)) (torusModel n) ∞
      (fun y : (lgManifold n).Point => y.2) :=
    (contMDiff_snd : ContMDiff (lgModel n) (torusModel n) ∞ (Prod.snd : LGSpace n → _)).comp
      (contMDiff_linearRechart_id_symm (M := LGSpace n) (lgEuclideanEquiv n))
  have hd := mfderiv_comp θ (hsnd.mdifferentiable (by simp) _)
    ((contMDiff_faceTorusAmbientMap u hf).mdifferentiable (by simp) θ)
  intro a b hab
  apply hi
  let A : Model (2 * n) →L[ℝ] TorusCoordinates n :=
    mfderiv 𝓘(ℝ, Model (2 * n)) (torusModel n)
      (fun y : (lgManifold n).Point => y.2) (faceTorusAmbientMap u f θ)
  have he (v : TorusCoordinates m) : mfderiv (torusModel m) (torusModel n) f θ v =
      A (mfderiv (torusModel m) 𝓘(ℝ, Model (2 * n)) (faceTorusAmbientMap u f) θ v) :=
    congrArg (fun L : TorusCoordinates m →L[ℝ] TorusCoordinates n => L v) hd
  exact (he a).trans ((congrArg A hab).trans (he b).symm)

/-- The constructed whole-torus branch has the exact source tangent in the
actual ambient manifold. No parametrization or differential is input data. -/
theorem IsStronglyCompatibleEndPotential.eventually_exists_conormalBranch_exact_tangent
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ)
    (Φ : RealSpace n ≃ₜ RealSpace n) (hΦeq : ∀ u, Φ u = coordinateGradient φ u)
    (hΦ₀ : Φ 0 = 0)
    (hΦ : ContDiffOn ℝ ∞ Φ ({0}ᶜ : Set (RealSpace n)))
    (hΦinv : ContDiffOn ℝ ∞ Φ.symm ({0}ᶜ : Set (RealSpace n))) :
    ∀ᶠ β in atTop, ∀ s : Finset (Lattice n),
      IsPolytopeFace I.vertices s → s.Nonempty → s ≠ I.vertices →
      ∀ x : TangentCoordinates n, Φ x.1 ∈ positiveCone s →
      angleQuotient x.2 ∈ coneTorus (positiveCone s) → tailoringFamily I β 1 (lgCover x) = 1 →
      ∀ w : s → ℝ,
      (∀ᶠ y in 𝓝 (lgCover x), tailoringFamily I β 1 y =
        ∑ v ∈ s, monomial (Real.exp (-β) : ℂ) v y) →
      (∀ v : s, monomial (Real.exp (-β) : ℂ) v.val (lgCover x) = (w v : ℂ)) →
      ∀ ℓ : RealSpace n →L[ℝ] ℝ, ℓ (Φ x.1) = 1 →
      ∃ (B : Opens (conormalTransverseSpace (Submodule.span ℝ (positiveCone s)) ℓ))
        (g : conormalTransverseSpace (Submodule.span ℝ (positiveCone s)) ℓ → RealSpace n)
        (f : Torus (n - s.card) → Torus n),
        (0 : conormalTransverseSpace (Submodule.span ℝ (positiveCone s)) ℓ) ∈ B ∧
        g 0 = x.1 ∧ ContDiffAt ℝ ∞ g 0 ∧
        ContMDiff (torusModel (n - s.card)) (torusModel n) ∞ f ∧
        range f = coneTorus (positiveCone s) ∧
        Topology.IsEmbedding (Prod.map (fun q : B => g q) f) ∧
        range (fderiv ℝ g 0) = {X | X ∈ faceRealTangent w ∧
          fderiv ℝ (coordinateGradient φ) x.1 X ∈ Submodule.span ℝ (positiveCone s)} ∧
        (∀ θ, Injective (mfderiv (torusModel (n - s.card)) (torusModel n) f θ)) ∧
        (∀ q ∈ B, ∀ θ, tailoringFamily I β 1 (g q, f θ) = 1) ∧
        (∀ θ (ξ : TangentCoordinates n),
          conormalBranchAmbientMap g f (0, θ) = lgCover ξ → ∀ V,
          lgCoverTangent ξ V ∈
            (mfderiv
              ((𝓘(ℝ, conormalTransverseSpace (Submodule.span ℝ (positiveCone s)) ℓ)).prod
                (torusModel (n - s.card))) 𝓘(ℝ, Model (2 * n))
              (conormalBranchAmbientMap g f) (0, θ)).range ↔
            V ∈ faceConormalTangent s (fderiv ℝ (coordinateGradient φ) x.1) w) := by
  filter_upwards [hφ.eventually_exists_embedded_conormalBranch Φ hΦeq hΦ₀ hΦ hΦinv,
    hφ.eventually_conormal_family_germ] with β hbranch hgerm
  intro s hs hsne hsproper x hp hθ hy w hlocal hmon ℓ hℓ
  let K := conormalTransverseSpace (Submodule.span ℝ (positiveCone s)) ℓ
  obtain ⟨B, g, f, R, h₀B, hg₀, hfrange, _, hemb, hgrange, hprops, _⟩ :=
    hbranch s hs hsne hsproper (lgCover x) hp hθ hy ℓ hℓ
  change g 0 = x.1 at hg₀
  change range (fderiv ℝ g 0) = {X | fderiv ℝ Φ x.1 X ∈
    Submodule.span ℝ (positiveCone s) ∧ fderiv ℝ (tailoringRadialFunction I β) x.1 X = 0}
    at hgrange
  have hfs : ContMDiff (torusModel (n - s.card)) (torusModel n) ∞ f := by
    intro θ
    have hι : ContMDiff (torusModel (n - s.card))
        ((𝓘(ℝ, K)).prod (torusModel (n - s.card))) ∞
        (fun θ : Torus (n - s.card) => ((0 : K), θ)) := contMDiff_const.prodMk contMDiff_id
    exact ((hprops 0 h₀B θ).1.comp θ hι.contMDiffAt).snd
  let θ₀ : Torus (n - s.card) := 0
  have hgs : ContDiffAt ℝ ∞ g 0 := by
    have hι : ContMDiff 𝓘(ℝ, K) ((𝓘(ℝ, K)).prod (torusModel (n - s.card))) ∞
        (fun q : K => (q, θ₀)) := contMDiff_id.prodMk contMDiff_const
    have hprod : ContMDiffAt 𝓘(ℝ, K) (lgModel n) ∞
        (fun q : K => (g q, f θ₀)) 0 :=
      (hprops 0 h₀B θ₀).1.comp (0 : K) hι.contMDiffAt
    exact hprod.fst.contDiffAt
  have hfi (θ : Torus (n - s.card)) :
      Injective (mfderiv (torusModel (n - s.card)) (torusModel n) f θ) := by
    have hi := (hprops 0 h₀B θ).2.1
    rw [mfderiv_prodMap (hgs.contMDiffAt.mdifferentiableAt (by simp))
      ((hfs θ).mdifferentiableAt (by simp)), mfderiv_eq_fderiv] at hi
    intro a b hab
    exact congrArg Prod.snd (hi (show ((fderiv ℝ g 0).prodMap
      (mfderiv (torusModel (n - s.card)) (torusModel n) f θ)) (0, a) =
      ((fderiv ℝ g 0).prodMap
        (mfderiv (torusModel (n - s.card)) (torusModel n) f θ)) (0, b) from
      Prod.ext rfl hab))
  have hρ := hgerm (positiveCone s) (Or.inr ⟨s, hs, hsne, hsproper, rfl⟩)
    (lgCover x) (by change coordinateGradient φ x.1 ∈ positiveCone s; rw [← hΦeq]; exact hp) hθ hy
  change ∀ᶠ u in 𝓝 x.1, ∀ θ ∈ coneTorus (positiveCone s),
    tailoringFamily I β 1 (u, θ) = (tailoringRadialFunction I β u : ℝ) at hρ
  have hdρ (X : RealSpace n) : fderiv ℝ (tailoringRadialFunction I β) x.1 X =
      faceWeightFunctional w (faceLevelMap s X) :=
    tailoringRadialFunction_fderiv_eq_face_constraint I β s x w hlocal
      (hρ.mono fun u hu => hu (angleQuotient x.2) hθ) hmon X
  have hΦfun : (Φ : RealSpace n → RealSpace n) = coordinateGradient φ := funext hΦeq
  have hgrange' : range (fderiv ℝ g 0) = {X | X ∈ faceRealTangent w ∧
      fderiv ℝ (coordinateGradient φ) x.1 X ∈ Submodule.span ℝ (positiveCone s)} := by
    rw [hgrange, hΦfun]
    ext X
    rw [mem_ofPred_eq, mem_ofPred_eq, hdρ]
    exact and_comm
  refine ⟨B, g, f, h₀B, hg₀, hgs, hfs, hfrange, hemb, hgrange', hfi,
    (fun q hq θ => (hprops q hq θ).2.2.1), ?_⟩
  intro θ ξ hpoint V
  exact conormalBranchAmbientMap_tangent_iff I hs hsne hsproper hgs hfs hfrange θ ξ
    hpoint (faceTorusAmbientMap_immersion_of_immersion (g 0) hfs θ (hfi θ))
    (fderiv ℝ (coordinateGradient φ) x.1) w hgrange' V

end FsFltz
