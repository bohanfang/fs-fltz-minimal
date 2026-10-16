import FsFltz.Analysis.TailoringCriticalToriAffine
import FsFltz.Analysis.TailoringCriticalToriImplicit
import FsFltz.Analysis.CoordinateStrongConvexLegendre

/-!
# Actual face-affine reduced coefficients

Source: `geometric-part-fsf-proof.tex`, `prop:morsebott`, lines 1512–1527.
The constrained branch solves the literal affine levels and normal-gradient
equations. Its coefficient is identified with the derivative of the reduced
potential before applying the normalized implicit equation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Set Filter Function
open scoped Topology ContDiff BigOperators

variable {n : ℕ}

/-- All actual face-normal levels, indexed by the prescribed finite face. -/
def faceLevelMap (s : Finset (Lattice n)) : RealSpace n →L[ℝ] (s → ℝ) :=
  ContinuousLinearMap.pi fun v => pairingCLM v.val

/-- The literal sum of the prescribed face normals with real coefficients. -/
def faceNormalMap (s : Finset (Lattice n)) : (s → ℝ) →L[ℝ] RealSpace n :=
  ∑ v : s, (ContinuousLinearMap.proj v).smulRight (latticeReal v.val)

@[simp] theorem faceLevelMap_apply (s : Finset (Lattice n)) (x : RealSpace n) (v : s) :
    faceLevelMap s x v = pairing v.val x := by
  simp [faceLevelMap]

@[simp] theorem faceNormalMap_apply (s : Finset (Lattice n)) (a : s → ℝ) :
    faceNormalMap s a = ∑ v : s, a v • latticeReal v.val := by
  simp [faceNormalMap]

theorem faceNormalMap_pairing (s : Finset (Lattice n)) (a : s → ℝ) (x : RealSpace n) :
    ∑ j, faceNormalMap s a j * x j = ∑ v : s, a v * faceLevelMap s x v := by
  simp only [faceNormalMap_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, faceLevelMap_apply, pairing, latticeReal]

theorem ToricInput.faceLevelMap_surjective (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hsne : s.Nonempty) (hsproper : s ≠ I.vertices) :
    Surjective (faceLevelMap s) := by
  classical
  intro a
  let b : Lattice n → ℝ := fun v => if h : v ∈ s then a ⟨v, h⟩ else 0
  obtain ⟨x, hx⟩ := I.nonempty_faceAffineLevel hs hsne hsproper b
  refine ⟨x, funext fun v => ?_⟩
  simpa [b, v.property] using hx v.val v.property

theorem faceNormalMap_injective_of_surjective {s : Finset (Lattice n)}
    (hA : Surjective (faceLevelMap s)) : Injective (faceNormalMap s) := by
  apply (faceNormalMap s).toLinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro a ha
  change faceNormalMap s a = 0 at ha
  obtain ⟨x, hx⟩ := hA a
  have hsum : ∑ v : s, (a v) ^ 2 = 0 := by
    have h := faceNormalMap_pairing s a x
    rw [ha, hx] at h
    simpa [sq] using h.symm
  ext v
  have hv := (Finset.sum_eq_zero_iff_of_nonneg
    (fun w (_ : w ∈ Finset.univ) => sq_nonneg (a w))).mp hsum v (Finset.mem_univ v)
  exact sq_eq_zero_iff.mp hv

/-- The actual constrained derivative, with no invertibility premise. -/
def faceConstrainedLinearization (s : Finset (Lattice n))
    (H : RealSpace n →L[ℝ] RealSpace n) :
    (RealSpace n × (s → ℝ)) →L[ℝ] (RealSpace n × (s → ℝ)) :=
  (H.comp (ContinuousLinearMap.fst ℝ (RealSpace n) (s → ℝ)) -
    (faceNormalMap s).comp (ContinuousLinearMap.snd ℝ (RealSpace n) (s → ℝ))).prod
      ((faceLevelMap s).comp (ContinuousLinearMap.fst ℝ (RealSpace n) (s → ℝ)))

@[simp] theorem faceConstrainedLinearization_apply (s : Finset (Lattice n))
    (H : RealSpace n →L[ℝ] RealSpace n) (p : RealSpace n × (s → ℝ)) :
    faceConstrainedLinearization s H p = (H p.1 - faceNormalMap s p.2, faceLevelMap s p.1) := by
  simp [faceConstrainedLinearization]

theorem faceConstrainedLinearization_isInvertible {s : Finset (Lattice n)}
    (hA : Surjective (faceLevelMap s)) {H : RealSpace n →L[ℝ] RealSpace n}
    (hH : ∀ d : RealSpace n, d ≠ 0 → 0 < ∑ j, H d j * d j) :
    (faceConstrainedLinearization s H).IsInvertible := by
  let L := faceConstrainedLinearization s H
  have hinj : Injective L := by
    apply L.toLinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro p hp
    have hfirst : H p.1 = faceNormalMap s p.2 :=
      sub_eq_zero.mp (congrArg Prod.fst hp)
    have hsecond : faceLevelMap s p.1 = 0 := congrArg Prod.snd hp
    have hd : p.1 = 0 := by
      by_contra hne
      have hpos := hH p.1 hne
      rw [hfirst, faceNormalMap_pairing, hsecond] at hpos
      simp at hpos
    have hb : p.2 = 0 := faceNormalMap_injective_of_surjective hA (by
      simpa [hd] using hfirst.symm)
    exact Prod.ext hd hb
  exact ⟨(LinearEquiv.ofBijective L.toLinearMap
    ⟨hinj, L.toLinearMap.surjective_of_injective hinj⟩).toContinuousLinearEquiv, rfl⟩

/-- The native Hessian is the Euclidean Riesz Hessian under the based
change of norm. Only local second differentiability is used. -/
theorem fderiv_coordinateGradient_apply_euclidean {φ : RealSpace n → ℝ}
    (hd : Differentiable ℝ φ) {x : RealSpace n} (hs : ContDiffAt ℝ ∞ φ x)
    (d : RealSpace n) :
    fderiv ℝ (coordinateGradient φ) x d =
      (EuclideanSpace.equiv (Fin n) ℝ)
        (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
          ((EuclideanSpace.equiv (Fin n) ℝ).symm x)
          ((EuclideanSpace.equiv (Fin n) ℝ).symm d)) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hφe : ContDiffAt ℝ ∞ (φ ∘ e) (e.symm x) := by
    apply ContDiffAt.comp (e.symm x) _ e.contDiff.contDiffAt
    simpa only [e.apply_symm_apply] using hs
  have hg := (contDiffAt_gradient hφe).differentiableAt (by simp)
  have he : coordinateGradient φ = fun z => e (gradient (φ ∘ e) (e.symm z)) :=
    funext (coordinateGradient_eq_euclidean_gradient hd)
  have hderiv := e.hasFDerivAt.comp x (hg.hasFDerivAt.comp x e.symm.hasFDerivAt)
  change HasFDerivAt (fun z => e (gradient (φ ∘ e) (e.symm z))) _ x at hderiv
  rw [he, hderiv.fderiv]
  rfl

theorem IsStronglyCompatibleEndPotential.native_hessian_pos
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) (hd : Differentiable ℝ φ)
    {x : RealSpace n} (hx : x ≠ 0) {d : RealSpace n} (hdne : d ≠ 0) :
    0 < ∑ j, fderiv ℝ (coordinateGradient φ) x d j * d j := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hx' : e.symm x ≠ 0 := by simpa only [ne_eq, EmbeddingLike.map_eq_zero_iff] using hx
  have hd' : e.symm d ≠ 0 := by simpa only [ne_eq, EmbeddingLike.map_eq_zero_iff] using hdne
  rw [fderiv_coordinateGradient_apply_euclidean hd (hφ.smooth x hx) d]
  have hpos := hφ.hessian_pos (e.symm x) hx' (e.symm d) hd'
  simpa [PiLp.inner_apply, e, mul_comm] using hpos

/-- The literal constrained stationarity equation for parameter `y`. -/
def faceConstrainedEquation (s : Finset (Lattice n)) (φ : RealSpace n → ℝ)
    (p : (s → ℝ) × (RealSpace n × (s → ℝ))) : RealSpace n × (s → ℝ) :=
  (coordinateGradient φ p.2.1 - faceNormalMap s p.2.2,
    faceLevelMap s p.2.1 - (fun _ => 1) - p.1)

theorem contDiffAt_faceConstrainedEquation {φ : RealSpace n → ℝ}
    (hd : Differentiable ℝ φ) {s : Finset (Lattice n)}
    {x : RealSpace n} (hs : ContDiffAt ℝ ∞ φ x) (a : s → ℝ) :
    ContDiffAt ℝ ∞ (faceConstrainedEquation s φ) (0, (x, a)) := by
  have hgrad : ContDiffAt ℝ ∞
      (fun p : (s → ℝ) × (RealSpace n × (s → ℝ)) => coordinateGradient φ p.2.1)
      (0, (x, a)) := by
    apply ContDiffAt.comp ((0 : s → ℝ), (x, a))
      (contDiffAt_coordinateGradient hd hs)
    exact (by fun_prop : ContDiffAt ℝ ∞
      (fun p : (s → ℝ) × (RealSpace n × (s → ℝ)) => p.2.1) (0, (x, a)))
  exact (hgrad.sub (by fun_prop)).prodMk (by fun_prop)

theorem fderiv_faceConstrainedEquation_unknowns {φ : RealSpace n → ℝ}
    (hd : Differentiable ℝ φ) {s : Finset (Lattice n)}
    {x : RealSpace n} (hs : ContDiffAt ℝ ∞ φ x) (a : s → ℝ) :
    (fderiv ℝ (faceConstrainedEquation s φ) (0, (x, a))).comp
      (ContinuousLinearMap.inr ℝ (s → ℝ) (RealSpace n × (s → ℝ))) =
        faceConstrainedLinearization s (fderiv ℝ (coordinateGradient φ) x) := by
  have htotal := (contDiffAt_faceConstrainedEquation hd hs a).differentiableAt (by simp)
  have hin := (ContinuousLinearMap.inr ℝ (s → ℝ)
    (RealSpace n × (s → ℝ))).hasFDerivAt (x := (x, a))
  have hchain := htotal.hasFDerivAt.comp (x, a) hin
  have hgrad := ((contDiffAt_coordinateGradient hd hs).differentiableAt
    (by simp)).hasFDerivAt.comp (x, a) (hasFDerivAt_fst (𝕜 := ℝ) (p := (x, a)))
  have hnormal := (faceNormalMap s).hasFDerivAt.comp (x, a)
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (x, a)))
  have hlevel := ((faceLevelMap s).hasFDerivAt.comp (x, a)
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (x, a)))).sub_const (fun _ => 1)
  have hmodel := (hgrad.sub hnormal).prodMk hlevel
  change HasFDerivAt (fun p : RealSpace n × (s → ℝ) =>
    faceConstrainedEquation s φ (0, p)) _ _ at hchain
  simp only [faceConstrainedEquation, sub_zero] at hchain
  exact hchain.unique hmodel

/-- Smooth solutions of the actual constrained equations at a positive
Hessian base point. The unknowns are constructed by the implicit theorem. -/
theorem exists_smooth_faceConstrained_branch {φ : RealSpace n → ℝ}
    (hd : Differentiable ℝ φ) {s : Finset (Lattice n)}
    (hA : Surjective (faceLevelMap s)) {x₀ : RealSpace n} {a₀ : s → ℝ}
    (hs : ContDiffAt ℝ ∞ φ x₀)
    (hH : ∀ d : RealSpace n, d ≠ 0 →
      0 < ∑ j, fderiv ℝ (coordinateGradient φ) x₀ d j * d j)
    (hlevel : faceLevelMap s x₀ = fun _ => 1)
    (hnormal : coordinateGradient φ x₀ = faceNormalMap s a₀) :
    ∃ x : (s → ℝ) → RealSpace n, ∃ a : (s → ℝ) → (s → ℝ),
      x 0 = x₀ ∧ a 0 = a₀ ∧ ContDiffAt ℝ ∞ x 0 ∧ ContDiffAt ℝ ∞ a 0 ∧
      (∀ᶠ y in 𝓝 0,
        faceLevelMap s (x y) = (fun v => 1 + y v) ∧
        coordinateGradient φ (x y) = faceNormalMap s (a y)) ∧
      ∀ᶠ p in 𝓝 ((0 : s → ℝ), (x₀, a₀)),
        faceConstrainedEquation s φ p = 0 ↔ (x p.1, a p.1) = p.2 := by
  have hcs := contDiffAt_faceConstrainedEquation hd hs a₀
  have hinv : ((fderiv ℝ (faceConstrainedEquation s φ) (0, (x₀, a₀))).comp
      (ContinuousLinearMap.inr ℝ (s → ℝ) (RealSpace n × (s → ℝ)))).IsInvertible := by
    rw [fderiv_faceConstrainedEquation_unknowns hd hs a₀]
    exact faceConstrainedLinearization_isInvertible hA hH
  let z := hcs.implicitFunction (by simp) hinv
  have hz : z 0 = (x₀, a₀) := hcs.implicitFunction_apply_self (by simp) hinv
  have hzs : ContDiffAt ℝ ∞ z 0 := hcs.contDiffAt_implicitFunction (by simp) hinv
  have hbase : faceConstrainedEquation s φ (0, (x₀, a₀)) = 0 := by
    simp [faceConstrainedEquation, hnormal, hlevel]
  refine ⟨fun y => (z y).1, fun y => (z y).2,
    congrArg Prod.fst hz, congrArg Prod.snd hz, hzs.fst, hzs.snd, ?_, ?_⟩
  · have heq : ∀ᶠ y in 𝓝 0, faceConstrainedEquation s φ (y, z y) = 0 := by
      simpa only [hbase] using hcs.eventually_apply_implicitFunction (by simp) hinv
    filter_upwards [heq] with y hy
    have hfirst := sub_eq_zero.mp (congrArg Prod.fst hy)
    have hsecond := sub_eq_zero.mp (congrArg Prod.snd hy)
    refine ⟨?_, hfirst⟩
    ext v
    have h := congrFun hsecond v
    change faceLevelMap s (z y).1 v - 1 = y v at h
    linarith
  · simpa only [hbase, Prod.mk.eta] using
      hcs.eventually_apply_eq_iff_implicitFunction (by simp) hinv

/-- Zero extension from the actual finite face coordinates to lattice labels. -/
def faceCoordinateExtend (s : Finset (Lattice n)) (a : s → ℝ) (v : Lattice n) : ℝ :=
  if h : v ∈ s then a ⟨v, h⟩ else 0

@[simp] theorem faceCoordinateExtend_apply (s : Finset (Lattice n)) (a : s → ℝ)
    (v : s) : faceCoordinateExtend s a v.val = a v := by
  simp [faceCoordinateExtend, v.property]

/-- The actual affine slice with the face's finite shift coordinates. -/
def faceCoordinateSlice (s : Finset (Lattice n)) (y : s → ℝ) : Set (RealSpace n) :=
  faceAffineLevel s (fun v => 1 + faceCoordinateExtend s y v)

theorem mem_faceCoordinateSlice_iff (s : Finset (Lattice n)) (y : s → ℝ)
    (x : RealSpace n) : x ∈ faceCoordinateSlice s y ↔
      faceLevelMap s x = (fun v => 1 + y v) := by
  constructor
  · intro hx
    exact funext fun v => by simpa [faceCoordinateSlice] using hx v.val v.property
  · intro hx v hv
    simpa [faceCoordinateExtend, hv] using congrFun hx ⟨v, hv⟩

theorem faceNormalMap_eq_extended_sum (s : Finset (Lattice n)) (a : s → ℝ) :
    faceNormalMap s a = ∑ v ∈ s, faceCoordinateExtend s a v • latticeReal v := by
  rw [faceNormalMap_apply]
  simpa only [faceCoordinateExtend_apply] using
    Finset.sum_coe_sort s (fun v => faceCoordinateExtend s a v • latticeReal v)

/-- The actual strong potential furnishes the base minimum and coefficients,
and the constructed smooth branch is its unique affine minimum near zero. -/
theorem IsStronglyCompatibleEndPotential.exists_smooth_faceCoordinate_minimum
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) (hφ1 : ContDiff ℝ 1 φ)
    {c : ℝ} (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun u : EuclideanSpace ℝ (Fin n) =>
      φ ((EuclideanSpace.equiv (Fin n) ℝ) u) - c * ‖u‖ ^ 2))
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hsne : s.Nonempty) (hsproper : s ≠ I.vertices) :
    ∃ x : (s → ℝ) → RealSpace n, ∃ a : (s → ℝ) → (s → ℝ),
      x 0 ∈ polarFace I s ∧ IsMinOn φ (polarFace I s) (x 0) ∧
      ContDiffAt ℝ ∞ x 0 ∧ ContDiffAt ℝ ∞ a 0 ∧ (∀ v, 0 < a 0 v) ∧
      (∀ᶠ y in 𝓝 0,
        x y ∈ faceCoordinateSlice s y ∧
        coordinateGradient φ (x y) = faceNormalMap s (a y) ∧
        IsMinOn φ (faceCoordinateSlice s y) (x y) ∧
        ∀ z ∈ faceCoordinateSlice s y,
          IsMinOn φ (faceCoordinateSlice s y) z → z = x y) := by
  obtain ⟨x₀, hx₀, hm₀, _, _, a₀, ha₀, hn₀⟩ :=
    hφ.exists_unique_polarFace_minimum hφ1 hc hconv hs hsne hsproper
  have hA := I.faceLevelMap_surjective hs hsne hsproper
  obtain ⟨v, hv⟩ := hsne
  have hxne : x₀ ≠ 0 := ne_zero_of_mem_polarFacet I v ⟨hx₀.1, hx₀.2 v hv⟩
  have hd := hφ1.differentiable (by simp)
  have hlevel : faceLevelMap s x₀ = fun _ => 1 := funext fun v => by
    simpa only [faceLevelMap_apply] using hx₀.2 v.val v.property
  have hnormal : coordinateGradient φ x₀ = faceNormalMap s (fun v => a₀ v.val) := by
    rw [faceNormalMap_apply]
    exact hn₀.trans (Finset.sum_coe_sort s (fun v => a₀ v • latticeReal v)).symm
  obtain ⟨x, a, hx, ha, hxs, has, hsol, _⟩ := exists_smooth_faceConstrained_branch hd
    hA (hφ.smooth x₀ hxne)
    (fun d hdne => hφ.native_hessian_pos hd hxne hdne) hlevel hnormal
  refine ⟨x, a, hx ▸ hx₀, hx ▸ hm₀, hxs, has,
    (fun v => by simpa only [ha] using ha₀ v.val v.property), ?_⟩
  filter_upwards [hsol] with y hy
  have hxmem := (mem_faceCoordinateSlice_iff s y (x y)).mpr hy.1
  have hm : IsMinOn φ (faceCoordinateSlice s y) (x y) :=
    isMinOn_faceAffineLevel_of_normal_equation hd
      (convexOn_of_euclidean_convex_quadratic hc.le hconv) hxmem
      (by rw [← faceNormalMap_eq_extended_sum]; exact hy.2)
  refine ⟨hxmem, hy.2, hm, ?_⟩
  intro z hz hmz
  exact eq_of_faceAffineLevel_minima hφ1 hc hconv hz hxmem hmz hm

/-- The reduced value is evaluated on the constructed actual minimizer. -/
def faceReducedPotential (φ : RealSpace n → ℝ) {s : Finset (Lattice n)}
    (x : (s → ℝ) → RealSpace n) : (s → ℝ) → ℝ := fun y => φ (x y)

/-- The literal coordinate differential of the reduced value function. -/
def faceReducedCoefficient (φ : RealSpace n → ℝ) {s : Finset (Lattice n)}
    (x : (s → ℝ) → RealSpace n) : (s → ℝ) → (s → ℝ) :=
  coordinateGradient (faceReducedPotential φ x)

/-- Differentiating the actual affine levels and normal equation proves
the envelope identity on a neighborhood. Coefficient smoothness is not
an input of this theorem. -/
theorem faceReducedCoefficient_eventually_eq {φ : RealSpace n → ℝ}
    (hd : Differentiable ℝ φ) {s : Finset (Lattice n)}
    {x : (s → ℝ) → RealSpace n} {a : (s → ℝ) → (s → ℝ)}
    (hxs : ContDiffAt ℝ ∞ x 0)
    (hlevel : ∀ᶠ y in 𝓝 0, faceLevelMap s (x y) = (fun v => 1 + y v))
    (hnormal : ∀ᶠ y in 𝓝 0, coordinateGradient φ (x y) = faceNormalMap s (a y)) :
    faceReducedCoefficient φ x =ᶠ[𝓝 0] a := by
  classical
  have hxd : ∀ᶠ y in 𝓝 (0 : s → ℝ), DifferentiableAt ℝ x y :=
    ((hxs.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).eventually (by simp)).mono
      fun y hy => hy.differentiableAt_one
  have hleq : (fun y => faceLevelMap s (x y)) =ᶠ[𝓝 0] (fun y v => 1 + y v) := hlevel
  filter_upwards [hxd, hleq.eventuallyEq_nhds, hnormal] with y hxy hly hny
  have hleft := (faceLevelMap s).hasFDerivAt.comp y hxy.hasFDerivAt
  have hright : HasFDerivAt (fun y : s → ℝ => fun v => 1 + y v)
      (ContinuousLinearMap.id ℝ (s → ℝ)) y := by
    convert (hasFDerivAt_id y).const_add (fun _ : s => (1 : ℝ)) using 1
    ext z v
    rfl
  have hD : (faceLevelMap s).comp (fderiv ℝ x y) = ContinuousLinearMap.id ℝ (s → ℝ) :=
    hleft.unique (hright.congr_of_eventuallyEq hly)
  ext v
  change fderiv ℝ (φ ∘ x) y (Pi.single v 1) = a y v
  rw [fderiv_comp y (hd (x y)) hxy]
  rw [ContinuousLinearMap.comp_apply, fderiv_eq_coordinateGradient_pairing, hny,
    faceNormalMap_pairing]
  have hdir := congrArg (fun L : (s → ℝ) →L[ℝ] (s → ℝ) => L (Pi.single v 1)) hD
  change faceLevelMap s (fderiv ℝ x y (Pi.single v 1)) = Pi.single v 1 at hdir
  rw [hdir]
  simp [Pi.single_apply]

/-- The coefficient fed to the reduced implicit equation is the actual
derivative of the actual reduced potential, smooth and positive at zero. -/
theorem IsStronglyCompatibleEndPotential.exists_actual_faceReducedCoefficient
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) (hφ1 : ContDiff ℝ 1 φ)
    {c : ℝ} (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun u : EuclideanSpace ℝ (Fin n) =>
      φ ((EuclideanSpace.equiv (Fin n) ℝ) u) - c * ‖u‖ ^ 2))
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hsne : s.Nonempty) (hsproper : s ≠ I.vertices) :
    ∃ x : (s → ℝ) → RealSpace n,
      x 0 ∈ polarFace I s ∧ IsMinOn φ (polarFace I s) (x 0) ∧
      ContDiffAt ℝ ∞ x 0 ∧ ContDiffAt ℝ ∞ (faceReducedPotential φ x) 0 ∧
      ContDiffAt ℝ ∞ (faceReducedCoefficient φ x) 0 ∧
      (∀ v, 0 < faceReducedCoefficient φ x 0 v) ∧
      (∀ᶠ y in 𝓝 0,
        x y ∈ faceCoordinateSlice s y ∧
        coordinateGradient φ (x y) = faceNormalMap s (faceReducedCoefficient φ x y) ∧
        IsMinOn φ (faceCoordinateSlice s y) (x y) ∧
        ∀ z ∈ faceCoordinateSlice s y,
          IsMinOn φ (faceCoordinateSlice s y) z → z = x y) := by
  have hsne' := hsne
  obtain ⟨x, a, hx₀, hm₀, hxs, has, hpos, hsol⟩ :=
    hφ.exists_smooth_faceCoordinate_minimum hφ1 hc hconv hs hsne hsproper
  have hd := hφ1.differentiable (by simp)
  have heq := faceReducedCoefficient_eventually_eq hd hxs
    (hsol.mono fun y hy => (mem_faceCoordinateSlice_iff s y (x y)).mp hy.1)
    (hsol.mono fun y hy => hy.2.1)
  obtain ⟨v, hv⟩ := hsne'
  have hxne : x 0 ≠ 0 := ne_zero_of_mem_polarFacet I v ⟨hx₀.1, hx₀.2 v hv⟩
  have hψ : ContDiffAt ℝ ∞ (faceReducedPotential φ x) 0 :=
    (hφ.smooth (x 0) hxne).comp 0 hxs
  have hcoeff := has.congr_of_eventuallyEq heq
  refine ⟨x, hx₀, hm₀, hxs, hψ, hcoeff, ?_, ?_⟩
  · intro v
    simpa only [heq.eq_of_nhds] using hpos v
  · filter_upwards [hsol, heq] with y hy hay
    simpa only [hay] using hy

end FsFltz
