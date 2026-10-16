import FsFltz.Analysis.TailoringLocalCritical
import FsFltz.Geometry.PotentialHamiltonian

/-!
# Literal face Hessians at tailored critical points

Source: `geometric-part-fsf-proof.tex`, `prop:morsebott`, `eq:hessian`,
lines 1538–1570; `lem:stable`, lines 1703–1725. The face equation below is
the holomorphic equation furnished by `TailoringLocalCritical`. Its second
derivative and the Lagrangian Hessian are computed from the actual monomials.
The large-parameter negative-block estimate and the intrinsic Morse–Bott
inertia theorem remain separate obligations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set Filter
open scoped BigOperators Topology ContDiff Manifold

variable {n : ℕ}

/-- The literal holomorphic equation on a retained face, in logarithmic lifts. -/
def criticalFaceFunction (s : Finset (Lattice n)) (β : ℝ)
    (x : TangentCoordinates n) : ℂ :=
  ∑ v ∈ s, monomial (Real.exp (-β) : ℂ) v (x.1, angleQuotient x.2)

/-- The weighted face-normal square appearing in both Hessian blocks. -/
def criticalFaceGram (s : Finset (Lattice n)) (q : Lattice n → ℝ)
    (X : RealSpace n) : ℝ := ∑ v ∈ s, q v * pairing v X ^ 2

theorem contDiff_criticalFaceFunction (s : Finset (Lattice n)) (β : ℝ) :
    ContDiff ℝ ∞ (criticalFaceFunction s β) := by
  apply ContDiff.sum
  intro v _
  simp only [monomial_angleQuotient, pairing]
  have hc : ContDiff ℝ ∞ (fun r : ℝ => (r : ℂ)) := Complex.ofRealCLM.contDiff
  fun_prop

/-- Positive monomial weights make the angular square nonnegative. -/
theorem criticalFaceGram_nonneg (s : Finset (Lattice n)) {q : Lattice n → ℝ}
    (hq : ∀ v ∈ s, 0 ≤ q v) (X : RealSpace n) : 0 ≤ criticalFaceGram s q X :=
  Finset.sum_nonneg fun v hv => mul_nonneg (hq v hv) (sq_nonneg _)

/-- The exact nullspace of the weighted normal square is the face kernel. -/
theorem criticalFaceGram_eq_zero_iff (s : Finset (Lattice n)) {q : Lattice n → ℝ}
    (hq : ∀ v ∈ s, 0 < q v) (X : RealSpace n) :
    criticalFaceGram s q X = 0 ↔ ∀ v ∈ s, pairing v X = 0 := by
  rw [criticalFaceGram, Finset.sum_eq_zero_iff_of_nonneg
    (fun v hv => mul_nonneg (hq v hv).le (sq_nonneg _))]
  constructor
  · intro h v hv
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp (h v hv)).resolve_left (hq v hv).ne')
  · intro h v hv
    rw [h v hv]
    simp

/-- Every direction outside the face kernel has strictly positive angular square. -/
theorem criticalFaceGram_pos (s : Finset (Lattice n)) {q : Lattice n → ℝ}
    (hq : ∀ v ∈ s, 0 < q v) {X : RealSpace n}
    (hX : ¬ ∀ v ∈ s, pairing v X = 0) : 0 < criticalFaceGram s q X :=
  lt_of_le_of_ne (criticalFaceGram_nonneg s (fun v hv => (hq v hv).le) X)
    (Ne.symm fun h => hX ((criticalFaceGram_eq_zero_iff s hq X).mp h))

theorem hasFDerivAt_criticalFaceFunction (s : Finset (Lattice n)) (β : ℝ)
    (x : TangentCoordinates n) :
    HasFDerivAt (criticalFaceFunction s β)
      (∑ v ∈ s, monomial (Real.exp (-β) : ℂ) v (x.1, angleQuotient x.2) • exponentLinearMap v) x := by
  exact HasFDerivAt.fun_sum fun v _ => hasFDerivAt_monomial_representatives _ v x

/-- The actual complex second derivative of the face equation. -/
theorem fderiv_fderiv_criticalFaceFunction (s : Finset (Lattice n)) (β : ℝ)
    (x V W : TangentCoordinates n) :
    fderiv ℝ (fderiv ℝ (criticalFaceFunction s β)) x V W =
      ∑ v ∈ s, monomial (Real.exp (-β) : ℂ) v (x.1, angleQuotient x.2) *
        exponentLinearMap v V * exponentLinearMap v W := by
  have he : fderiv ℝ (criticalFaceFunction s β) =
      fun z => ∑ v ∈ s, monomial (Real.exp (-β) : ℂ) v (z.1, angleQuotient z.2) • exponentLinearMap v :=
    funext fun z => (hasFDerivAt_criticalFaceFunction s β z).fderiv
  rw [he]
  have hd := HasFDerivAt.fun_sum (u := s) fun v _ =>
    (hasFDerivAt_monomial_representatives (Real.exp (-β) : ℂ) v x).smul_const
      (exponentLinearMap v)
  rw [hd.fderiv]
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul]

/-- Real monomials give opposite radial and angular second-derivative signs,
with no radial–angular mixed term. -/
theorem re_fderiv_fderiv_criticalFaceFunction
    (s : Finset (Lattice n)) (β : ℝ) (x V : TangentCoordinates n)
    (hreal : ∀ v ∈ s, (monomial (Real.exp (-β) : ℂ) v (x.1, angleQuotient x.2)).im = 0) :
    (fderiv ℝ (fderiv ℝ (criticalFaceFunction s β)) x V V).re =
      criticalFaceGram s (fun v => (monomial (Real.exp (-β) : ℂ) v (x.1, angleQuotient x.2)).re) V.1 -
      criticalFaceGram s (fun v => (monomial (Real.exp (-β) : ℂ) v (x.1, angleQuotient x.2)).re) V.2 := by
  rw [fderiv_fderiv_criticalFaceFunction, Complex.re_sum]
  simp only [criticalFaceGram, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  rw [exponentLinearMap_eq_pairing]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, hreal v hv]
  ring

/-- The ambient Lagrangian whose restriction to the face fiber differs from
the potential by a constant. Its multiplier is the conormal multiplier. -/
def criticalFaceLagrangian (φ : RealSpace n → ℝ) (s : Finset (Lattice n))
    (β lam : ℝ) (x : TangentCoordinates n) : ℝ :=
  φ x.1 - lam * (criticalFaceFunction s β x).re

theorem contDiff_criticalFaceLagrangian {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (s : Finset (Lattice n)) (β lam : ℝ) :
    ContDiff ℝ ∞ (criticalFaceLagrangian φ s β lam) :=
  (hφ.comp contDiff_fst).sub
    ((Complex.reCLM.contDiff.comp (contDiff_criticalFaceFunction s β)).const_smul lam)

/-- The native normal critical equation makes the actual Lagrangian stationary. -/
theorem fderiv_criticalFaceLagrangian_eq_zero {φ : RealSpace n → ℝ}
    (s : Finset (Lattice n)) (β lam : ℝ) (x : TangentCoordinates n)
    (hφ : DifferentiableAt ℝ φ x.1)
    (hreal : ∀ v ∈ s, (monomial (Real.exp (-β) : ℂ) v (x.1, angleQuotient x.2)).im = 0)
    (hcritical : coordinateGradient φ x.1 = lam • ∑ v ∈ s,
      (monomial (Real.exp (-β) : ℂ) v (x.1, angleQuotient x.2)).re • latticeReal v) :
    fderiv ℝ (criticalFaceLagrangian φ s β lam) x = 0 := by
  have hd := (hφ.hasFDerivAt.comp x
    (ContinuousLinearMap.fst ℝ (RealSpace n) (RealSpace n)).hasFDerivAt).sub
    ((Complex.reCLM.hasFDerivAt.comp x (hasFDerivAt_criticalFaceFunction s β x)).const_smul lam)
  change HasFDerivAt (criticalFaceLagrangian φ s β lam) _ x at hd
  rw [hd.fderiv]
  apply ContinuousLinearMap.ext
  intro V
  simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply,
    sum_apply, smul_eq_mul, zero_apply]
  change fderiv ℝ φ x.1 V.1 - lam *
    (∑ v ∈ s, monomial (Real.exp (-β) : ℂ) v (x.1, angleQuotient x.2) *
      exponentLinearMap v V).re = 0
  have hface : (∑ v ∈ s, monomial (Real.exp (-β) : ℂ) v (x.1, angleQuotient x.2) *
      exponentLinearMap v V).re = ∑ v ∈ s,
        (monomial (Real.exp (-β) : ℂ) v (x.1, angleQuotient x.2)).re * pairing v V.1 := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro v hv
    simp only [exponentLinearMap_eq_pairing, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, hreal v hv,
      zero_mul, mul_zero, sub_zero, add_zero, zero_add]
  have hnormalEval : fderiv ℝ φ x.1 V.1 = lam * ∑ v ∈ s,
      (monomial (Real.exp (-β) : ℂ) v (x.1, angleQuotient x.2)).re * pairing v V.1 := by
    rw [fderiv_eq_coordinateGradient_pairing, hcritical]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
      Finset.sum_mul, mul_assoc, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [pairing, latticeReal, ← Finset.mul_sum]
  rw [hface, hnormalEval, sub_self]

section StationaryComposition

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- At a stationary point the actual second derivative of a smooth pullback
has no contribution from the acceleration of its parametrization. -/
theorem fderiv_fderiv_comp_of_stationary {f : E → ℝ} {g : F → E}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x V W : F)
    (hstationary : fderiv ℝ f (g x) = 0) :
    fderiv ℝ (fderiv ℝ (f ∘ g)) x V W =
      fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x V) (fderiv ℝ g x W) := by
  let C : (E →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] E) →L[ℝ] F →L[ℝ] ℝ :=
    ContinuousLinearMap.compL ℝ F E ℝ
  have he : fderiv ℝ (f ∘ g) = fun z => C (fderiv ℝ f (g z)) (fderiv ℝ g z) := by
    funext z
    exact ((hf.differentiable (by simp) (g z)).hasFDerivAt.comp z
      (hg.differentiable (by simp) z).hasFDerivAt).fderiv
  have hDf := (((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) (g x)).hasFDerivAt.comp x
    (hg.differentiable (by simp) x).hasFDerivAt)
  have hDg := ((hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x).hasFDerivAt
  have hd := hDf.clm_comp hDg
  rw [he]
  change HasFDerivAt (fun z => C (fderiv ℝ f (g z)) (fderiv ℝ g z)) _ x at hd
  rw [hd.fderiv]
  simp [ContinuousLinearMap.compL_apply, hstationary]

end StationaryComposition

/-- The radial-only extension has exactly the original potential Hessian. -/
theorem fderiv_fderiv_potential_radial {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x V W : TangentCoordinates n) :
    fderiv ℝ (fderiv ℝ (fun z : TangentCoordinates n => φ z.1)) x V W =
      fderiv ℝ (fderiv ℝ φ) x.1 V.1 W.1 := by
  let P := ContinuousLinearMap.fst ℝ (RealSpace n) (RealSpace n)
  let C := ContinuousLinearMap.compL ℝ (TangentCoordinates n) (RealSpace n) ℝ
  have he : fderiv ℝ (fun z : TangentCoordinates n => φ z.1) =
      fun z => C (fderiv ℝ φ z.1) P := by
    funext z
    exact ((hφ.differentiable (by simp) z.1).hasFDerivAt.comp z P.hasFDerivAt).fderiv
  rw [he]
  have hd := ((C.flip P).hasFDerivAt.comp x
    (((hφ.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x.1).hasFDerivAt.comp x
      P.hasFDerivAt)).fderiv
  exact congrArg (fun D => D V W) hd

/-- The exact diagonal Lagrangian Hessian, obtained by differentiating the
literal face equation twice. No Hessian formula is assumed. -/
theorem fderiv_fderiv_criticalFaceLagrangian {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (s : Finset (Lattice n)) (β lam : ℝ)
    (x V : TangentCoordinates n)
    (hreal : ∀ v ∈ s, (monomial (Real.exp (-β) : ℂ) v (x.1, angleQuotient x.2)).im = 0) :
    fderiv ℝ (fderiv ℝ (criticalFaceLagrangian φ s β lam)) x V V =
      fderiv ℝ (fderiv ℝ φ) x.1 V.1 V.1 -
        lam * criticalFaceGram s (fun v => (monomial (Real.exp (-β) : ℂ) v (x.1, angleQuotient x.2)).re) V.1 +
        lam * criticalFaceGram s (fun v => (monomial (Real.exp (-β) : ℂ) v (x.1, angleQuotient x.2)).re) V.2 := by
  let F := criticalFaceFunction s β
  have hF (z : TangentCoordinates n) : DifferentiableAt ℝ F z :=
    (hasFDerivAt_criticalFaceFunction s β z).differentiableAt
  have hDF (z : TangentCoordinates n) : DifferentiableAt ℝ (fderiv ℝ F) z := by
    have he : fderiv ℝ F = fun w => ∑ v ∈ s,
        monomial (Real.exp (-β) : ℂ) v (w.1, angleQuotient w.2) • exponentLinearMap v :=
      funext fun w => (hasFDerivAt_criticalFaceFunction s β w).fderiv
    rw [he]
    exact (HasFDerivAt.fun_sum fun v _ =>
      (hasFDerivAt_monomial_representatives (Real.exp (-β) : ℂ) v z).smul_const
        (exponentLinearMap v)).differentiableAt
  let C := ContinuousLinearMap.compL ℝ (TangentCoordinates n) ℂ ℝ
  have he : fderiv ℝ (criticalFaceLagrangian φ s β lam) = fun z =>
      fderiv ℝ (fun w : TangentCoordinates n => φ w.1) z -
        lam • C Complex.reCLM (fderiv ℝ F z) := by
    funext z
    exact (((hφ.comp contDiff_fst).differentiable (by simp) z).hasFDerivAt.sub
      ((Complex.reCLM.hasFDerivAt.comp z (hF z).hasFDerivAt).const_smul lam)).fderiv
  have hDφ := ((hφ.comp contDiff_fst).fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  rw [he]
  have hd := hDφ.hasFDerivAt.sub
    ((C Complex.reCLM).hasFDerivAt.comp x (hDF x).hasFDerivAt |>.const_smul lam)
  change HasFDerivAt (fun z => fderiv ℝ (fun w : TangentCoordinates n => φ w.1) z -
    lam • C Complex.reCLM (fderiv ℝ F z)) _ x at hd
  rw [hd.fderiv]
  simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  change fderiv ℝ (fderiv ℝ (fun z : TangentCoordinates n => φ z.1)) x V V -
    lam * (fderiv ℝ (fderiv ℝ F) x V V).re = _
  rw [fderiv_fderiv_potential_radial hφ]
  rw [re_fderiv_fderiv_criticalFaceFunction s β x V hreal]
  ring

/-- For every smooth local face-fiber parametrization, the actual constrained
second derivative is the computed Lagrangian Hessian. The level condition is
required only near the base point. -/
theorem criticalFace_parametrization_hessian {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (s : Finset (Lattice n)) (β lam : ℝ)
    {g : F → TangentCoordinates n} (hg : ContDiff ℝ ∞ g) (a V : F)
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
      (hg.differentiable (by simp) _), hstationary, ContinuousLinearMap.zero_comp]
  · rw [hfirst.fderiv_eq, fderiv_fderiv_comp_of_stationary hLs hg a V V hstationary]
    exact fderiv_fderiv_criticalFaceLagrangian hφ s β lam (g a) (fderiv ℝ g a V) hreal

/-- The native normal equation annihilates every actual good fiber tangent. -/
theorem tailoring_good_potential_derivative_eq_zero_of_normal
    (I : ToricInput n) (β : ℝ) (x : TangentCoordinates n)
    (hx : tailoringFamily I β 1 (lgCover x) = 1)
    (hgood : ∀ v ∈ tailoringExponents I,
      tailoringCutoff I β v x.1 = 0 ∨ tailoringCutoff I β v x.1 = 1)
    (φ : RealSpace n → ℝ) (lam : ℝ)
    (hreal : ∀ v ∈ I.vertices, (tailoringRetainedMonomial I β v (lgCover x)).im = 0)
    (hcritical : coordinateGradient φ x.1 = lam • ∑ v ∈ I.vertices,
      (tailoringRetainedMonomial I β v (lgCover x)).re • latticeReal v)
    (V : TangentCoordinates n)
    (hV : fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x V = 0) :
    fderiv ℝ φ x.1 V.1 = 0 := by
  rw [fderiv_tailoringFamily_one_eq_leading_of_good I β x hx hgood] at hV
  have hface : (tailoringLeadingDifferential I β (lgCover x) V).re =
      ∑ v ∈ I.vertices, (tailoringRetainedMonomial I β v (lgCover x)).re * pairing v V.1 := by
    simp only [tailoringLeadingDifferential, sum_apply, smul_apply, smul_eq_mul, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro v hv
    simp only [exponentLinearMap_eq_pairing, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, hreal v hv,
      zero_mul, mul_zero, sub_zero, add_zero, zero_add]
  have hnormalEval : fderiv ℝ φ x.1 V.1 = lam * ∑ v ∈ I.vertices,
      (tailoringRetainedMonomial I β v (lgCover x)).re * pairing v V.1 := by
    rw [fderiv_eq_coordinateGradient_pairing, hcritical]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
      Finset.sum_mul, mul_assoc, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [pairing, latticeReal, ← Finset.mul_sum]
  rw [hnormalEval, ← hface, hV, Complex.zero_re, mul_zero]

/-- The converse critical-point implication on the actual embedded endpoint
fiber. Its tangent equation follows by differentiating the literal constant
fiber equation, so no tangent-range or criticality premise is supplied. -/
theorem tailoring_fullFiber_critical_of_real_normal_equation
    (I : ToricInput n) (β : ℝ) {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {e : ℕ} (N : SmoothManifold e) (j : N.SmoothEmbedding (lgManifold n))
    (himage : Set.range j.map = {y | tailoringFamily I β 1 y = 1})
    (z : N.Point) (x : TangentCoordinates n) (hpoint : j.map z = lgCover x)
    (hgood : ∀ v ∈ tailoringExponents I,
      tailoringCutoff I β v x.1 = 0 ∨ tailoringCutoff I β v x.1 = 1)
    (lam : ℝ)
    (hreal : ∀ v ∈ I.vertices, (tailoringRetainedMonomial I β v (lgCover x)).im = 0)
    (hcritical : coordinateGradient φ x.1 = lam • ∑ v ∈ I.vertices,
      (tailoringRetainedMonomial I β v (lgCover x)).re • latticeReal v) :
    ∀ V : N.Tangent z, N.scalarDerivative (fun q => φ (j.map q).1) z V = 0 := by
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hconst : tailoringFamily I β 1 ∘ j.map = fun _ => (1 : ℂ) := by
    funext q
    have hmem : j.map q ∈ Set.range j.map := ⟨q, rfl⟩
    rwa [himage] at hmem
  have hx : tailoringFamily I β 1 (lgCover x) = 1 := by
    have h := congrFun hconst z
    simpa only [Function.comp_apply, hpoint] using h
  intro V
  have hkernel := mfderiv_comp_apply z
    ((contMDiff_tailoringFamily_lgManifold I β 1).mdifferentiable (by simp) (j.map z))
    (j.map.contMDiff.mdifferentiable (by simp) z) V
  rw [hconst, mfderiv_const, zero_apply] at hkernel
  have hchain := mfderiv_comp_apply z
    ((contMDiff_potentialValue hφ).mdifferentiable (by simp) (j.map z))
    (j.map.contMDiff.mdifferentiable (by simp) z) V
  change N.scalarDerivative (fun q => φ (j.map q).1) z V =
    (lgManifold n).scalarDerivative (fun y => φ y.1) (j.map z)
      (mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model (2 * n)) j.map z V) at hchain
  let w := mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model (2 * n)) j.map z V
  change 0 = complexDifferential (lgManifold n) (tailoringFamily I β 1) (j.map z) w at hkernel
  obtain ⟨Q, hQ⟩ := (lgCoverTangent_bijective x).2 w
  have hQkernel : fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x Q = 0 := by
    rw [fderiv_complex_lgCover (contMDiff_tailoringFamily_lgManifold I β 1)]
    have hkpoint := congrArg (fun y : (lgManifold n).Point =>
      complexDifferential (lgManifold n) (tailoringFamily I β 1) y w) hpoint
    have hkzero := hkpoint.symm.trans hkernel.symm
    simpa only [ContinuousLinearMap.comp_apply, hQ] using hkzero
  have hzero := tailoring_good_potential_derivative_eq_zero_of_normal
    I β x hx hgood φ lam hreal hcritical Q hQkernel
  have hnative := (scalarDerivative_potential_lgCover hφ x Q).trans hzero
  have hwzero := (congrArg ((lgManifold n).scalarDerivative
    (fun y => φ y.1) (lgCover x)) hQ).symm.trans hnative
  have hpPoint := congrArg (fun y : (lgManifold n).Point =>
    (lgManifold n).scalarDerivative (fun q => φ q.1) y w) hpoint
  exact hchain.trans (hpPoint.trans hwzero)

end FsFltz
