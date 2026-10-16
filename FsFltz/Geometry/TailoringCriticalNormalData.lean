import FsFltz.Geometry.TailoringNormalNeighborhood
import FsFltz.Geometry.TailoringNativeGradientLinearization

/-!
# One constructed critical radius for the neighborhood and normal metric

Source: `geometric-part-fsf-proof.tex`, `lem:stable`, lines 1709–1724,
and `prop:morsebott`, lines 1538–1570. One actual reduced branch supplies
the normal equation, true Hessian blocks, potential germ, plateau, and
whole-torus conormal defining neighborhood. The native chart constructor
consumes these same data, without making another choice of critical branch.
No product normal tube or uniform expansion is asserted.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set Filter Function TopologicalSpace
open scoped Topology BigOperators ContDiff Manifold

variable {n : ℕ}

/-- Concrete geometric output of the common-neighborhood construction.
This is an explicit embedded branch and zero-set contract, not a product
tubular chart. Its point, potential, face and removed vertex are fixed. -/
structure ConormalTransverseNeighborhoodAt
    (I : ToricInput n) (φEnd : RealSpace n → ℝ) (β : ℝ)
    (s : Finset (Lattice n)) (u : RealSpace n) (v₀ : s) where
  functional : RealSpace n →L[ℝ] ℝ
  functional_normalized : functional (coordinateGradient φEnd u) = 1
  projection : RealSpace n →L[ℝ] Submodule.span ℝ (positiveCone s)
  quotient : RealSpace n →L[ℝ] projection.ker
  projection_leftInverse : LeftInverse projection (Submodule.span ℝ (positiveCone s)).subtypeL
  quotient_surjective : Surjective quotient
  quotient_zero : ∀ p, quotient p = 0 ↔ p ∈ Submodule.span ℝ (positiveCone s)
  branchDomain : Opens (conormalTransverseSpace (Submodule.span ℝ (positiveCone s)) functional)
  radialBranch : conormalTransverseSpace (Submodule.span ℝ (positiveCone s)) functional → RealSpace n
  angleBranch : Torus (n - s.card) → Torus n
  zero_mem : (0 : conormalTransverseSpace (Submodule.span ℝ (positiveCone s)) functional) ∈ branchDomain
  radial_center : radialBranch 0 = u
  angle_range : range angleBranch = coneTorus (positiveCone s)
  branch_embedding : Topology.IsEmbedding (Prod.map (fun q : branchDomain => radialBranch q) angleBranch)
  branch_smooth : ∀ q ∈ branchDomain, ∀ θ : Torus (n - s.card),
    ContMDiffAt ((𝓘(ℝ, conormalTransverseSpace (Submodule.span ℝ (positiveCone s)) functional)).prod
      (torusModel (n - s.card))) (lgModel n) ∞ (Prod.map radialBranch angleBranch) (q, θ)
  branch_immersion : ∀ q ∈ branchDomain, ∀ θ : Torus (n - s.card),
    Injective (mfderiv
      ((𝓘(ℝ, conormalTransverseSpace (Submodule.span ℝ (positiveCone s)) functional)).prod
        (torusModel (n - s.card))) (lgModel n) (Prod.map radialBranch angleBranch) (q, θ))
  neighborhood : Set (LGSpace n)
  neighborhood_open : IsOpen neighborhood
  torus_mem : ∀ θ ∈ coneTorus (positiveCone s), (u, θ) ∈ neighborhood
  torus_fiber : ∀ θ ∈ coneTorus (positiveCone s), tailoringFamily I β 1 (u, θ) = 1
  torus_zero : ∀ θ ∈ coneTorus (positiveCone s),
    conormalTransverseCoordinates (coordinateGradient φEnd) quotient s v₀.val (u, θ) = 0
  transverse_smooth : ∀ w ∈ neighborhood, ContMDiffAt (lgModel n)
    𝓘(ℝ, projection.ker × (s.erase v₀.val → ℝ)) ∞
    (conormalTransverseCoordinates (coordinateGradient φEnd) quotient s v₀.val) w
  zero_iff_branch : ∀ w ∈ neighborhood, tailoringFamily I β 1 w = 1 →
    (conormalTransverseCoordinates (coordinateGradient φEnd) quotient s v₀.val w = 0 ↔
      w ∈ range (Prod.map (fun q : branchDomain => radialBranch q) angleBranch))
  zero_iff_conormal : ∀ w ∈ neighborhood, tailoringFamily I β 1 w = 1 →
    (conormalTransverseCoordinates (coordinateGradient φEnd) quotient s v₀.val w = 0 ↔
      coordinateGradient φEnd w.1 ∈ positiveCone s ∧ w.2 ∈ coneTorus (positiveCone s))

/-- Actual shared data at one specified radius. The Hessian is the literal
derivative of the end gradient, and B,R are specified producer parameters.
The existence theorem below uses the actual branch derivatives for B,R. -/
structure CriticalFaceNormalData
    (I : ToricInput n) (φEnd φ : RealSpace n → ℝ) (β : ℝ)
    (s : Finset (Lattice n)) (u : RealSpace n) (q : s → ℝ) (lam : ℝ)
    (B : (s → ℝ) →L[ℝ] RealSpace n) (R : (s → ℝ) →L[ℝ] (s → ℝ)) where
  radius_ne_zero : u ≠ 0
  weight_pos : ∀ v, 0 < q v
  multiplier_pos : 0 < lam
  weight_sum : ∑ v, q v = 1
  normal_equation : coordinateGradient φEnd u = lam • faceNormalMap s q
  right_inverse : (faceLevelMap s).comp B = ContinuousLinearMap.id ℝ (s → ℝ)
  hessian_normal : (fderiv ℝ (coordinateGradient φEnd) u).comp B = (faceNormalMap s).comp R
  hessian_symm : ∀ X Y,
    (∑ i, fderiv ℝ (coordinateGradient φEnd) u X i * Y i) =
      ∑ i, fderiv ℝ (coordinateGradient φEnd) u Y i * X i
  hessian_pos : ∀ X : RealSpace n, X ≠ 0 →
    0 < ∑ i, fderiv ℝ (coordinateGradient φEnd) u X i * X i
  reduced_negative : ∀ h : s → ℝ, h ≠ 0 →
    (∑ v, R h v * h v) - lam * faceWeightSquare q h < 0
  potential_germ : φ =ᶠ[𝓝 u] φEnd
  plateau : Set (RealSpace n)
  plateau_open : IsOpen plateau
  plateau_mem : u ∈ plateau
  plateau_cutoff : ∀ w ∈ plateau, ∀ v ∈ tailoringExponents I,
    tailoringCutoff I β v w = if v = 0 ∨ v ∈ s then 1 else 0
  monomial_eq : ∀ θ ∈ coneTorus (positiveCone s), ∀ v : s,
    monomial (Real.exp (-β) : ℂ) v.val (u, θ) = (q v : ℂ)
  fiber_eq : ∀ θ ∈ coneTorus (positiveCone s), tailoringFamily I β 1 (u, θ) = 1
  conormal_neighborhood : ∀ v₀ : s, Nonempty (ConormalTransverseNeighborhoodAt I φEnd β s u v₀)

namespace CriticalFaceNormalData

variable {I : ToricInput n} {φEnd φ : RealSpace n → ℝ} {β : ℝ}
  {s : Finset (Lattice n)} {u : RealSpace n} {q : s → ℝ} {lam : ℝ}
  {B : (s → ℝ) →L[ℝ] RealSpace n} {R : (s → ℝ) →L[ℝ] (s → ℝ)}

theorem hessian_surjective (D : CriticalFaceNormalData I φEnd φ β s u q lam B R) :
    Surjective (fderiv ℝ (coordinateGradient φEnd) u) := by
  apply LinearMap.surjective_of_injective
  intro X Y hXY
  change fderiv ℝ (coordinateGradient φEnd) u X =
    fderiv ℝ (coordinateGradient φEnd) u Y at hXY
  by_contra hne
  have hpos := D.hessian_pos (X - Y) (sub_ne_zero.mpr hne)
  have hz : fderiv ℝ (coordinateGradient φEnd) u (X - Y) = 0 := by
    rw [map_sub, hXY, sub_self]
  simp only [hz, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hpos
  exact lt_irrefl 0 hpos

theorem gradient_smooth (D : CriticalFaceNormalData I φEnd φ β s u q lam B R)
    (hStrong : IsStronglyCompatibleEndPotential I φEnd) (hEnd1 : ContDiff ℝ 1 φEnd) :
    ContDiffAt ℝ ∞ (coordinateGradient φEnd) u :=
  contDiffAt_coordinateGradient (hEnd1.differentiable one_ne_zero)
    (hStrong.smooth u D.radius_ne_zero)

theorem hessian_eq_global (D : CriticalFaceNormalData I φEnd φ β s u q lam B R) :
    fderiv ℝ (coordinateGradient φEnd) u = fderiv ℝ (coordinateGradient φ) u :=
  (coordinateHessian_eq_of_eventuallyEq D.potential_germ).symm

theorem good_germ (D : CriticalFaceNormalData I φEnd φ β s u q lam B R)
    (θ : Torus n) :
    ∀ᶠ w in 𝓝 (u, θ), ∀ v ∈ tailoringExponents I,
      tailoringCutoff I β v w.1 = 0 ∨ tailoringCutoff I β v w.1 = 1 := by
  have hnear : ∀ᶠ w : LGSpace n in 𝓝 (u, θ), w.1 ∈ D.plateau :=
    continuous_fst.continuousAt.eventually (D.plateau_open.mem_nhds D.plateau_mem)
  filter_upwards [hnear] with w hw v hv
  rw [D.plateau_cutoff w.1 hw v hv]
  split_ifs <;> simp

/-- The actual shared radius constructs every native chart used in the
normal metric theorem. It does not select a second reduced branch. -/
theorem nativeChart (D : CriticalFaceNormalData I φEnd φ β s u q lam B R)
    (hs : IsPolytopeFace I.vertices s) (hφ : ContDiff ℝ ∞ φ)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hpi : ∀ y, tailoringFamily I β 1 y = 1 →
      0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1) y
        (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    (θ : Torus n) (hθ : θ ∈ coneTorus (positiveCone s))
    (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n))
    (himage : range j.map = {y | tailoringFamily I β 1 y = 1})
    (a : N.Point) (ξ : TangentCoordinates n) (hpoint : j.map a = lgCover ξ)
    (hξ : lgCover ξ = (u, θ)) :
    Nonempty (NativeFaceHessianChart φ s (fderiv ℝ (coordinateGradient φEnd) u)
      q lam N j a ξ) := by
  have hrad : ξ.1 = u := congrArg Prod.fst hξ
  have hlocal := tailoringFamily_eventually_face_sum_of_plateau I β hs.1
    (D.fiber_eq θ hθ) D.plateau_open D.plateau_mem D.plateau_cutoff
  have hlocal' : ∀ᶠ y in 𝓝 (j.map a), tailoringFamily I β 1 y =
      ∑ v ∈ s, monomial (Real.exp (-β) : ℂ) v y := by
    rwa [hpoint, hξ]
  have hchart := tailoring_fullFiber_nonempty_nativeFaceHessianChart I β hφ hc hlower
    hpi s lam q N j himage a ξ hpoint hlocal' (hrad ▸ D.potential_germ)
    (hξ ▸ D.monomial_eq θ hθ) (hrad ▸ D.normal_equation)
    D.right_inverse (hrad ▸ D.hessian_normal) (hrad ▸ D.hessian_symm)
    (hrad ▸ D.hessian_pos) D.weight_pos D.multiplier_pos D.reduced_negative
  simpa only [hrad] using hchart

end CriticalFaceNormalData

/-- Choose the actual reduced branch once. Its literal derivatives B,R,
normal equation, plateau, native metric inputs, and conormal neighborhood
all refer to the same reconstructed radius. No independent branch
existence statement is used to provide any of these contracts. -/
theorem IsStronglyCompatibleEndPotential.exists_actual_criticalFaceNormalData
    {I : ToricInput n} {φEnd φ : RealSpace n → ℝ}
    (hStrong : IsStronglyCompatibleEndPotential I φEnd)
    (hEnd1 : ContDiff ℝ 1 φEnd) (hEnd0 : φEnd 0 = 0)
    {c : ℝ} (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun u : EuclideanSpace ℝ (Fin n) =>
      φEnd ((EuclideanSpace.equiv (Fin n) ℝ) u) - c * ‖u‖ ^ 2))
    (hlower : ∀ u : EuclideanSpace ℝ (Fin n),
      c * ‖u‖ ^ 2 ≤ φEnd ((EuclideanSpace.equiv (Fin n) ℝ) u))
    (hbound : ∀ u : EuclideanSpace ℝ (Fin n), u ≠ 0 → ∀ v,
      (2 * c) * ‖v‖ ^ 2 ≤ inner ℝ
        ((fderiv ℝ (gradient (φEnd ∘ EuclideanSpace.equiv (Fin n) ℝ)) u) v) v)
    {R₀ : ℝ} (hEnd : ∀ u,
      R₀ ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u)
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hsne : s.Nonempty) (hsproper : s ≠ I.vertices) :
    ∃ x : (s → ℝ) → RealSpace n, ∃ z : ℝ → ((s → ℝ) × ℝ),
      x 0 ∈ polarFace I s ∧ IsMinOn φEnd (polarFace I s) (x 0) ∧
      ContDiffAt ℝ ∞ x 0 ∧ ContDiffAt ℝ ∞ z 0 ∧
      ∀ᶠ β : ℝ in atTop,
        Nonempty (CriticalFaceNormalData I φEnd φ β s (faceCriticalRadius x z β)
          (z β⁻¹).1 (β * (z β⁻¹).2)
          (fderiv ℝ x (β⁻¹ • (fun v : s => Real.log ((z β⁻¹).1 v))))
          (fderiv ℝ (faceReducedCoefficient φEnd x)
            (β⁻¹ • (fun v : s => Real.log ((z β⁻¹).1 v))))) := by
  classical
  let : Nonempty s := ⟨⟨hsne.choose, hsne.choose_spec⟩⟩
  have hgrad0 : coordinateGradient φEnd 0 = 0 := by
    have hm : IsLocalMin φEnd 0 := Filter.Eventually.of_forall fun u => by
      rw [hEnd0]
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using
        (mul_nonneg hc.le (sq_nonneg _)).trans
          (hlower ((EuclideanSpace.equiv (Fin n) ℝ).symm u))
    ext i
    simp [coordinateGradient, hm.fderiv_eq_zero]
  let Φ := strongConvexCoordinateGradientHomeomorph hEnd1 hc hconv hlower
  have hΦeq : ∀ u, Φ u = coordinateGradient φEnd u :=
    fun u => strongConvexCoordinateGradientHomeomorph_apply hEnd1 hc hconv hlower u
  have hΦfun : (Φ : RealSpace n → RealSpace n) = coordinateGradient φEnd := funext hΦeq
  have hΦ₀ : Φ 0 = 0 := by simpa [Φ] using hgrad0
  have hΦ : ContDiffOn ℝ ∞ Φ ({0}ᶜ : Set (RealSpace n)) :=
    contDiffOn_strongConvexCoordinateGradientHomeomorph hEnd1 hc hconv hlower hStrong.smooth
  have hΦinv : ContDiffOn ℝ ∞ Φ.symm ({0}ᶜ : Set (RealSpace n)) :=
    contDiffOn_symm_strongConvexCoordinateGradientHomeomorph hEnd1 hc hconv hlower hgrad0
      hStrong.smooth (show 0 < 2 * c by positivity) hbound
  obtain ⟨x, z, hx₀, hm₀, hxs, has, hpos, hz₀, hzs, hsol, hzsol, _, hradial, hfiber⟩ :=
    hStrong.exists_actual_positive_faceReduced_branch hEnd1 hc hconv hs hsne hsproper
  have hμ : 0 < ∑ v, faceReducedCoefficient φEnd x 0 v :=
    Finset.sum_pos (fun v _ => hpos v) Finset.univ_nonempty
  have hq₀ : ∀ v, 0 < (z 0).1 v := by
    intro v
    rw [hz₀]
    exact div_pos (hpos v) hμ
  have hμ₀ : 0 < (z 0).2 := by simpa only [hz₀] using hμ
  have hxne : x 0 ≠ 0 := ne_zero_of_mem_polarFacet I hsne.choose
    ⟨hx₀.1, hx₀.2 hsne.choose hsne.choose_spec⟩
  have hstrict := hStrong.strict_of_polarFace_minimum hs hsne hsproper hx₀ hm₀
  have hface : ∀ v ∈ I.vertices,
      if v ∈ s then pairing v (x 0) = 1 else pairing v (x 0) < 1 := by
    intro v hv
    split_ifs with hvs
    · exact hx₀.2 v hvs
    · exact hstrict v hv hvs
  have hlevel : ∀ᶠ y in 𝓝 0, faceLevelMap s (x y) = fun v => 1 + y v := by
    filter_upwards [hsol] with y hy
    exact (mem_faceCoordinateSlice_iff s y (x y)).mp hy.1
  have hlevel' : ∀ᶠ y in 𝓝 0, ∀ v : s, pairing v.val (x y) = 1 + y v := by
    filter_upwards [hlevel] with y hy v
    simpa only [faceLevelMap_apply] using congrFun hy v
  have hparam : Tendsto (fun β : ℝ => β⁻¹ • (fun v : s => Real.log ((z β⁻¹).1 v)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_smul] using
      (differentiableAt_critical_logarithmic_parameter
        (hzs.fst.differentiableAt (by simp)) hq₀).continuousAt.tendsto.comp
          (tendsto_inv_atTop_zero (𝕜 := ℝ))
  have hblocks := hStrong.eventually_actual_face_hessian_blocks
    (hEnd1.differentiable one_ne_zero) hxs has hzs hxne hq₀ hμ₀ hlevel
    (hsol.mono fun y hy => hy.2.1)
  have hpot := faceCriticalRadius_eventually_potential_germ_eq
    hxs.continuousAt hzs.continuousAt hxne hq₀ hEnd
  have hcut := critical_reduced_branch_eventually_face_plateaus I
    (hxs.differentiableAt (by simp)) hface (hzs.fst.differentiableAt (by simp)) hq₀
  refine ⟨x, z, hx₀, hm₀, hxs, hzs, ?_⟩
  filter_upwards [hStrong.eventually_exists_conormalTransverseNeighborhood
      Φ hΦeq hΦ₀ hΦ hΦinv,
    hblocks, hpot, hcut, hradial, hfiber, hparam.eventually hlevel',
    tendsto_inv_atTop_zero.eventually hzsol, eventually_gt_atTop (0 : ℝ)]
    with β hnb hb hp hcutβ hradβ hfiberβ hlβ hzβ hβ
  let u := faceCriticalRadius x z β
  let q := (z β⁻¹).1
  let lam := β * (z β⁻¹).2
  have hlam : 0 < lam := mul_pos hβ hzβ.2.1
  have hmon : ∀ θ ∈ coneTorus (positiveCone s), ∀ v : s,
      monomial (Real.exp (-β) : ℂ) v.val (u, θ) = (q v : ℂ) := by
    intro θ hθ v
    exact monomial_eq_weight_of_shifted_face_level hβ.ne' (hzβ.1 v)
      (by simpa only [Pi.smul_apply, smul_eq_mul] using hlβ v)
      ((I.mem_coneTorus_positiveCone_iff hs hsne hsproper θ).mp hθ v.val v.property)
  have hfib : ∀ θ ∈ coneTorus (positiveCone s), tailoringFamily I β 1 (u, θ) = 1 := by
    intro θ hθ
    exact hfiberβ θ (fun v =>
      (I.mem_coneTorus_positiveCone_iff hs hsne hsproper θ).mp hθ v.val v.property)
  let a : s → ℝ := lam • q
  have ha : ∀ v, 0 < a v := fun v => mul_pos hlam (hzβ.1 v)
  have hnormal : Φ u = faceNormalMap s a := by
    rw [hΦeq, hradβ]
    exact (map_smul (faceNormalMap s) _ _).symm
  have hpne : Φ u ≠ 0 := by
    rw [hnormal]
    intro hz
    have ha0 : a = 0 := (faceNormalMap_injective_of_surjective
      (I.faceLevelMap_surjective hs hsne hsproper)) (hz.trans (map_zero _).symm)
    have := ha ⟨hsne.choose, hsne.choose_spec⟩
    rw [ha0] at this
    exact lt_irrefl 0 this
  have hune : u ≠ 0 := fun hu => hpne (by rw [hu, hΦ₀])
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hpne
  let ℓ : RealSpace n →L[ℝ] ℝ := (Φ u i)⁻¹ • ContinuousLinearMap.proj i
  have hℓ : ℓ (Φ u) = 1 := inv_mul_cancel₀ hi
  obtain ⟨U, hU, huU, hcutU⟩ := hcutβ
  have hneighborhood : ∀ v₀ : s, Nonempty (ConormalTransverseNeighborhoodAt I φEnd β s u v₀) := by
    intro v₀
    have hθ0 := zero_mem_coneTorus (positiveCone s)
    obtain ⟨P, Q, B₀, g, f, O, hP, hQsurj, hQ, h₀, hg₀, hf, hemb, hreg,
      hO, htorus, hsmooth, hzero, hcone⟩ :=
      hnb s hs hsne hsproper (u, 0) hθ0 (hfib 0 hθ0)
        a ha hnormal ℓ hℓ U hU huU hcutU v₀
    have htorus' : ∀ θ ∈ coneTorus (positiveCone s), (u, θ) ∈ O ∧
        tailoringFamily I β 1 (u, θ) = 1 ∧
        conormalTransverseCoordinates (coordinateGradient φEnd) Q s v₀.val (u, θ) = 0 := by
      simpa only [hΦfun] using htorus
    exact ⟨{
      functional := ℓ
      functional_normalized := by rwa [← hΦeq]
      projection := P
      quotient := Q
      projection_leftInverse := hP
      quotient_surjective := hQsurj
      quotient_zero := hQ
      branchDomain := B₀
      radialBranch := g
      angleBranch := f
      zero_mem := h₀
      radial_center := hg₀
      angle_range := hf
      branch_embedding := hemb
      branch_smooth := fun q hq θ => (hreg q hq θ).1
      branch_immersion := fun q hq θ => (hreg q hq θ).2
      neighborhood := O
      neighborhood_open := hO
      torus_mem := fun θ hθ => (htorus' θ hθ).1
      torus_fiber := fun θ hθ => (htorus' θ hθ).2.1
      torus_zero := fun θ hθ => (htorus' θ hθ).2.2
      transverse_smooth := by simpa only [hΦfun] using hsmooth
      zero_iff_branch := by simpa only [hΦfun] using hzero
      zero_iff_conormal := by simpa only [hΦfun] using hcone }⟩
  exact ⟨{
    radius_ne_zero := hune
    weight_pos := hzβ.1
    multiplier_pos := hlam
    weight_sum := hzβ.2.2.2
    normal_equation := hradβ
    right_inverse := hb.1
    hessian_normal := hb.2.1
    hessian_symm := hb.2.2.1
    hessian_pos := hb.2.2.2.1
    reduced_negative := hb.2.2.2.2.1
    potential_germ := hp
    plateau := U
    plateau_open := hU
    plateau_mem := huU
    plateau_cutoff := hcutU
    monomial_eq := hmon
    fiber_eq := hfib
    conormal_neighborhood := hneighborhood }⟩

end FsFltz
