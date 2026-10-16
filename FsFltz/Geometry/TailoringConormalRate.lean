import FsFltz.Geometry.TailoringNormalNeighborhood
import FsFltz.Geometry.TailoringConormalInvariance

/-!
# The actual intrinsic transverse rate vanishes on the smooth conormal branch

Source: `geometric-part-fsf-proof.tex`, `lem:invariance`, lines 1625–1647,
and `lem:trapping`, lines 1678–1682. This is a pointwise zero-section
producer over the entire branch, using the literal cutoff plateau and
the actual native intrinsic Liouville vector.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Geometry.SmoothManifold Set Filter Function
open scoped Topology BigOperators ContDiff Manifold

variable {n : ℕ}

section Cover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The native rate is the differential of the literal logarithmic transverse
map applied to the actual pushed intrinsic vector. -/
theorem conormalTransverseRate_eq_cover {d : ℕ}
    (N : SmoothManifold d) (j : N.SmoothEmbedding (lgManifold n)) (μ : N.Form 1)
    {Φ : RealSpace n → RealSpace n} (Q : RealSpace n →L[ℝ] E)
    (s : Finset (Lattice n)) (v₀ : Lattice n) (a : N.Point)
    (x V : TangentCoordinates n) (hpoint : j.map a = lgCover x)
    (hΦ : ContDiffAt ℝ ∞ Φ x.1)
    (hpush : mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) j.map a
      (N.liouvilleVector μ a) = lgCoverTangent x V) :
    conormalTransverseRate N j μ Φ Q s v₀ a =
      (Q (fderiv ℝ Φ x.1 V.1),
        fun v : s.erase v₀ =>
          (monomial 1 v.val (lgCover x) * exponentLinearMap v.val V).im) := by
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  let δ := conormalTransverseCoordinates Φ Q s v₀
  have hδ := (contMDiffAt_conormalTransverseCoordinates_native Q s v₀
    (lgCover x) hΦ).mdifferentiableAt (by simp)
  unfold conormalTransverseRate
  rw [mfderiv_comp_apply a (hpoint.symm ▸ hδ)
    (j.map.contMDiff.mdifferentiableAt (by simp)), hpush]
  have hcover := mfderiv_comp_apply x hδ
    ((contMDiff_lgCover n).mdifferentiableAt (by simp)) V
  change mfderiv 𝓘(ℝ, TangentCoordinates n) 𝓘(ℝ, E × (s.erase v₀ → ℝ))
    (δ ∘ lgCover) x V =
      mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, E × (s.erase v₀ → ℝ))
        δ (lgCover x) (lgCoverTangent x V) at hcover
  rw [hpoint, ← hcover, mfderiv_eq_fderiv]
  exact fderiv_conormalTransverseCoordinates_cover_apply Q s v₀ x V
    (hΦ.differentiableAt (by simp))

end Cover

/-- Vanishing holds at every actual smooth conormal-branch point. The literal
plateau and exact transverse zero set are used; the point need not be critical. -/
theorem tailoringEndpoint_exists_uniform_zero_conormalTransverseRate
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd : IsStronglyCompatibleEndPotential I φEnd)
    {R : ℝ} (hR : 0 < R)
    (heq : ∀ u, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
      range j.map = {y | tailoringFamily I β 1 y = 1} →
      ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E],
      ∀ (s : Finset (Lattice n)), IsPolytopeFace I.vertices s → s.Nonempty → s ≠ I.vertices →
      ∀ Q : RealSpace n →L[ℝ] E,
      (∀ u, Q u = 0 ↔ u ∈ Submodule.span ℝ (positiveCone s)) →
      ∀ v₀ : s, ∀ a : N.Point,
      j.map a ∈ conormalPositivePhaseNeighborhood s →
      (∀ v ∈ tailoringExponents I,
        tailoringCutoff I β v (j.map a).1 = if v = 0 ∨ v ∈ s then 1 else 0) →
      conormalTransverseCoordinates (coordinateGradient φEnd) Q s v₀.val (j.map a) = 0 →
      conormalTransverseRate N j (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ))
        (coordinateGradient φEnd) Q s v₀.val a = 0 := by
  classical
  obtain ⟨Bp, hBp, hpush⟩ := tailoringEndpoint_exists_uniform_fullFiber_projectedRadial
    I hφ hc hU hlower hupper hEnd hR heq
  obtain ⟨_, _, _, _, Bπ, _, hπ⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  obtain ⟨BR, _, hrad⟩ := tailoringFamily_exists_fiber_outside_radius I (R + 1)
  refine ⟨max Bp (max Bπ BR), hBp.trans_le (le_max_left _ _), ?_⟩
  intro β hβ N j himage E _ _ s hs hsne hsproper Q hQ v₀ a hphase hcut hzero
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hf : tailoringFamily I β 1 (j.map a) = 1 := by
    have hm : j.map a ∈ range j.map := ⟨a, rfl⟩
    rwa [himage] at hm
  have hsum := tailoringFamily_face_sum_of_point_plateau I β hs.1 (j.map a) hf hcut
  obtain ⟨hp, hθ⟩ := (conormalTransverseCoordinates_eq_zero_iff I hs hsne hsproper
    (coordinateGradient φEnd) (Submodule.span ℝ (positiveCone s)) Q hQ
    v₀.val v₀.property (j.map a) hphase (Real.exp (-β)) (Real.exp_pos _) hsum).mp hzero
  obtain ⟨x, hx⟩ := lgCover_surjective n (j.map a)
  have hpoint : j.map a = lgCover x := hx.symm
  have hxF : tailoringFamily I β 1 (lgCover x) = 1 := hpoint ▸ hf
  have hout : R < ‖(EuclideanSpace.equiv (Fin n) ℝ).symm x.1‖ := by
    have hh := hrad β ((le_max_right _ _).trans ((le_max_right _ _).trans hβ))
      1 (by simp) (lgCover x) hxF
    rw [realEuclideanRadius_eq_norm] at hh
    change R + 1 ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm x.1‖ at hh
    linarith
  have hgerm := potential_germ_eq_on_end heq hout
  have hgrad := coordinateGradient_eq_of_eventuallyEq hgerm
  have hHess := coordinateHessian_eq_of_eventuallyEq hgerm
  have hgradgerm : coordinateGradient φ =ᶠ[𝓝 x.1] coordinateGradient φEnd :=
    hgerm.eventuallyEq_nhds.mono fun _ hh => coordinateGradient_eq_of_eventuallyEq hh
  have hΦ : ContDiffAt ℝ ∞ (coordinateGradient φEnd) x.1 :=
    (contDiff_coordinateGradient hφ).contDiffAt.congr_of_eventuallyEq hgradgerm.symm
  have hoff : ∀ v ∈ I.vertices, latticeReal v ∉ positiveCone s →
      tailoringCutoff I β v x.1 = 0 := by
    intro v hv hvcone
    have hvs : v ∉ s := fun hvs => hvcone (latticeReal_mem_positiveCone hvs)
    have hv0 : v ≠ 0 := fun he => I.zero_not_mem_vertices (he ▸ hv)
    have hh := hcut v (Finset.mem_insert_of_mem hv)
    rw [hpoint] at hh
    simpa only [lgCover, hv0, hvs, or_self, ↓reduceIte] using hh
  have hnd := nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower (lgCover x)
  have hpair := ((hπ β ((le_max_left _ _).trans ((le_max_right _ _).trans hβ))
    1 (by simp) (lgCover x) hnd).2.2 (by simp [hxF])).ne'
  rw [planePairing_lambdaPotentialForm_eq_cover hφ x
    (potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)) (fun _ => rfl) hnd
      (contMDiff_tailoringFamily_lgManifold I β 1)] at hpair
  have hv := coverProjectedRadial_mem_conormal_radial_tangent I β (positiveCone s) x
    hxF (hpoint ▸ hθ) hoff hφ
    (potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)) (fun _ => rfl)
    (coordinateHessian_apply_self_on_homogeneous_end hφ hEnd.smooth hEnd.homogeneous hR heq hout)
    (by simpa only [hpoint, lgCover, hgrad] using hp) hpair
  let V := coverFiberProjection (potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1))
    (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x) (x.1, 0)
  rw [conormalTransverseRate_eq_cover N j _ Q s v₀.val a x V hpoint hΦ
    ((hpush β ((le_max_left _ _).trans hβ) N j himage a x hpoint).2)]
  apply Prod.ext
  · exact (hQ _).mpr (by rw [← hHess]; exact hv.1)
  · funext v
    change (monomial 1 v.val (lgCover x) * exponentLinearMap v.val V).im = 0
    have hchar := (I.mem_coneTorus_positiveCone_iff hs hsne hsproper (j.map a).2).mp hθ
      v.val (Finset.mem_erase.mp v.property).2
    rw [hpoint] at hchar
    have hm : monomial 1 v.val (lgCover x) =
        (Real.exp (pairing v.val x.1) : ℂ) := by
      simp only [monomial, one_mul, hchar, mul_one, ← Complex.ofReal_exp]
      rfl
    have hangle : V.2 = 0 := hv.2.2
    rw [hm, exponentLinearMap_eq_pairing, hangle]
    have hz : pairing v.val (0 : RealSpace n) = 0 := by simp [pairing]
    rw [hz]
    simp only [Complex.ofReal_zero, mul_zero, add_zero, Complex.mul_im,
      Complex.ofReal_im, zero_mul]

/-- Refine the already constructed branch neighborhood by the actual radial
plateau. The same open set contains the entire face torus and supplies the
zero-section rate identity at all nearby branch points. -/
theorem tailoringEndpoint_exists_uniform_open_zero_conormalTransverseRate
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd : IsStronglyCompatibleEndPotential I φEnd)
    {R : ℝ} (hR : 0 < R)
    (heq : ∀ u, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
      range j.map = {y | tailoringFamily I β 1 y = 1} →
      ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E],
      ∀ (s : Finset (Lattice n)), IsPolytopeFace I.vertices s → s.Nonempty → s ≠ I.vertices →
      ∀ Q : RealSpace n →L[ℝ] E,
      (∀ u, Q u = 0 ↔ u ∈ Submodule.span ℝ (positiveCone s)) →
      ∀ v₀ : s, ∀ u : RealSpace n, ∀ V : Set (RealSpace n),
      IsOpen V → u ∈ V →
      (∀ w ∈ V, ∀ v ∈ tailoringExponents I,
        tailoringCutoff I β v w = if v = 0 ∨ v ∈ s then 1 else 0) →
      ∀ O : Set (LGSpace n), IsOpen O →
      (∀ θ ∈ coneTorus (positiveCone s), (u, θ) ∈ O) →
      ∃ W : Set (LGSpace n), IsOpen W ∧ W ⊆ O ∧
        (∀ θ ∈ coneTorus (positiveCone s), (u, θ) ∈ W) ∧
        ∀ a : N.Point, j.map a ∈ W →
          conormalTransverseCoordinates (coordinateGradient φEnd) Q s v₀.val (j.map a) = 0 →
          conormalTransverseRate N j
            (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ))
            (coordinateGradient φEnd) Q s v₀.val a = 0 := by
  obtain ⟨B, hB, hrate⟩ := tailoringEndpoint_exists_uniform_zero_conormalTransverseRate
    I hφ hc hU hlower hupper hEnd hR heq
  refine ⟨B, hB, ?_⟩
  intro β hβ N j himage E _ _ s hs hsne hsproper Q hQ v₀ u V hV huV hcut O hO htorus
  let W : Set (LGSpace n) := O ∩ (Prod.fst ⁻¹' V) ∩ conormalPositivePhaseNeighborhood s
  refine ⟨W, (hO.inter (hV.preimage continuous_fst)).inter
    (isOpen_conormalPositivePhaseNeighborhood s), fun _ hw => hw.1.1, ?_, ?_⟩
  · intro θ hθ
    exact ⟨⟨htorus θ hθ, huV⟩,
      mem_conormalPositivePhaseNeighborhood_of_mem_coneTorus I hs hsne hsproper _ hθ⟩
  · intro a ha hz
    exact hrate β hβ N j himage E s hs hsne hsproper Q hQ v₀ a ha.2
      (hcut (j.map a).1 ha.1.2) hz

end FsFltz
