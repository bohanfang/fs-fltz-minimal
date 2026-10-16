import FsFltz.Analysis.TailoringCriticalToriHessian
import FsFltz.Analysis.TailoringCriticalToriBranch

/-!
# Orthogonal blocks of the actual face Hessian

Source: `geometric-part-fsf-proof.tex`, `prop:morsebott`, `eq:hessian`,
lines 1538–1571, and downstream `lem:stable`, lines 1703–1725.
The splitting is constructed using the derivative of the actual affine
constrained minimizer. Its reduced Hessian is bounded near the base point;
positive branch weights and the growing multiplier force the negative block.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Set Filter Function
open scoped Topology BigOperators ContDiff

variable {n : ℕ}

/-- The weighted face-level constraint defining both real fiber tangents. -/
def faceWeightFunctional {s : Finset (Lattice n)} (q : s → ℝ) : (s → ℝ) →L[ℝ] ℝ :=
  ∑ v : s, q v • ContinuousLinearMap.proj v

@[simp] theorem faceWeightFunctional_apply {s : Finset (Lattice n)}
    (q h : s → ℝ) : faceWeightFunctional q h = ∑ v, q v * h v := by
  simp [faceWeightFunctional]

/-- The face-level weighted square, before lifting into ambient coordinates. -/
def faceWeightSquare {s : Finset (Lattice n)} (q h : s → ℝ) : ℝ :=
  ∑ v, q v * (h v) ^ 2

/-- The radial tangent and angular tangent have this same literal constraint. -/
def faceRealTangent {s : Finset (Lattice n)} (q : s → ℝ) : Submodule ℝ (RealSpace n) :=
  ((faceWeightFunctional q).comp (faceLevelMap s)).toLinearMap.ker

@[simp] theorem mem_faceRealTangent {s : Finset (Lattice n)}
    (q : s → ℝ) (X : RealSpace n) :
    X ∈ faceRealTangent q ↔ faceWeightFunctional q (faceLevelMap s X) = 0 := Iff.rfl

/-- Coordinate version of the exact constrained quadratic Hessian. -/
def faceConstrainedHessian (s : Finset (Lattice n))
    (H : RealSpace n →L[ℝ] RealSpace n) (q : s → ℝ) (lam : ℝ)
    (V : TangentCoordinates n) : ℝ :=
  (∑ j, H V.1 j * V.1 j) - lam * faceWeightSquare q (faceLevelMap s V.1) +
    lam * faceWeightSquare q (faceLevelMap s V.2)

/-- A right inverse constructs the complete radial splitting, and the face
constraint is retained on the lifted factor. -/
theorem faceRealTangent_split {s : Finset (Lattice n)}
    {B : (s → ℝ) →L[ℝ] RealSpace n}
    (hB : (faceLevelMap s).comp B = ContinuousLinearMap.id ℝ (s → ℝ))
    (q : s → ℝ) {X : RealSpace n} (hX : X ∈ faceRealTangent q) :
    faceLevelMap s (X - B (faceLevelMap s X)) = 0 ∧
    faceWeightFunctional q (faceLevelMap s X) = 0 ∧
    X = (X - B (faceLevelMap s X)) + B (faceLevelMap s X) := by
  have hright (h : s → ℝ) : faceLevelMap s (B h) = h :=
    congrArg (fun L : (s → ℝ) →L[ℝ] (s → ℝ) => L h) hB
  exact ⟨by rw [map_sub, hright, sub_self], hX, (sub_add_cancel _ _).symm⟩

/-- The differentiated normal equation gives literal Hessian orthogonality
of the minimizer lift to the face kernel. -/
theorem face_minimum_lift_orthogonal {s : Finset (Lattice n)}
    {H : RealSpace n →L[ℝ] RealSpace n} {B : (s → ℝ) →L[ℝ] RealSpace n}
    {R : (s → ℝ) →L[ℝ] (s → ℝ)}
    (hnormal : H.comp B = (faceNormalMap s).comp R)
    {e : RealSpace n} (he : faceLevelMap s e = 0) (h : s → ℝ) :
    ∑ j, H (B h) j * e j = 0 := by
  have hb := congrArg (fun L : (s → ℝ) →L[ℝ] RealSpace n => L h) hnormal
  change H (B h) = faceNormalMap s (R h) at hb
  rw [hb, faceNormalMap_pairing, he]
  simp

/-- On the lifted factor the ambient Hessian is the actual Schur form. -/
theorem face_minimum_lift_hessian {s : Finset (Lattice n)}
    {H : RealSpace n →L[ℝ] RealSpace n} {B : (s → ℝ) →L[ℝ] RealSpace n}
    {R : (s → ℝ) →L[ℝ] (s → ℝ)}
    (hB : (faceLevelMap s).comp B = ContinuousLinearMap.id ℝ (s → ℝ))
    (hnormal : H.comp B = (faceNormalMap s).comp R) (h k : s → ℝ) :
    (∑ j, H (B h) j * B k j) = ∑ v, R h v * k v := by
  have hb := congrArg (fun L : (s → ℝ) →L[ℝ] RealSpace n => L h) hnormal
  have hk := congrArg (fun L : (s → ℝ) →L[ℝ] (s → ℝ) => L k) hB
  change H (B h) = faceNormalMap s (R h) at hb
  change faceLevelMap s (B k) = k at hk
  rw [hb, faceNormalMap_pairing, hk]

/-- The exact four-block diagonal formula, including all radial cross terms.
The angular kernel disappears literally, rather than only having zero square. -/
theorem faceConstrainedHessian_four_blocks {s : Finset (Lattice n)}
    {H : RealSpace n →L[ℝ] RealSpace n} {B : (s → ℝ) →L[ℝ] RealSpace n}
    {R : (s → ℝ) →L[ℝ] (s → ℝ)}
    (hB : (faceLevelMap s).comp B = ContinuousLinearMap.id ℝ (s → ℝ))
    (hnormal : H.comp B = (faceNormalMap s).comp R)
    (hsymm : ∀ X Y, (∑ j, H X j * Y j) = ∑ j, H Y j * X j)
    (q : s → ℝ) (lam : ℝ) {e f : RealSpace n}
    (he : faceLevelMap s e = 0) (hf : faceLevelMap s f = 0) (h k : s → ℝ) :
    faceConstrainedHessian s H q lam (e + B h, f + B k) =
      (∑ j, H e j * e j) +
      ((∑ v, R h v * h v) - lam * faceWeightSquare q h) +
      lam * faceWeightSquare q k := by
  have hright (a : s → ℝ) : faceLevelMap s (B a) = a :=
    congrArg (fun L : (s → ℝ) →L[ℝ] (s → ℝ) => L a) hB
  have hc := face_minimum_lift_orthogonal hnormal he h
  have hc' : (∑ j, H e j * B h j) = 0 := (hsymm _ _).trans hc
  have hh := face_minimum_lift_hessian hB hnormal h h
  simp only [faceConstrainedHessian, map_add, he, hf, hright, zero_add,
    Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  rw [hc, hc', hh]
  ring

/-- A positive-Hessian orthogonal complement is characterized exactly by
the minimizer lift; this identifies the source's moving space `D_F`. -/
theorem face_minimum_lift_eq_orthogonal {s : Finset (Lattice n)}
    {H : RealSpace n →L[ℝ] RealSpace n} {B : (s → ℝ) →L[ℝ] RealSpace n}
    {R : (s → ℝ) →L[ℝ] (s → ℝ)}
    (hB : (faceLevelMap s).comp B = ContinuousLinearMap.id ℝ (s → ℝ))
    (hnormal : H.comp B = (faceNormalMap s).comp R)
    (hpos : ∀ e : RealSpace n, e ≠ 0 → 0 < ∑ j, H e j * e j)
    (X : RealSpace n) :
    (∀ e : RealSpace n, faceLevelMap s e = 0 → (∑ j, H X j * e j) = 0) ↔
      X = B (faceLevelMap s X) := by
  have hright (h : s → ℝ) : faceLevelMap s (B h) = h :=
    congrArg (fun L : (s → ℝ) →L[ℝ] (s → ℝ) => L h) hB
  constructor
  · intro h
    let e := X - B (faceLevelMap s X)
    have he : faceLevelMap s e = 0 := by rw [map_sub, hright, sub_self]
    have hzero : (∑ j, H e j * e j) = 0 := by
      simp only [e, map_sub, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      change (∑ j, H X j * e j) - (∑ j, H (B (faceLevelMap s X)) j * e j) = 0
      rw [h _ he, face_minimum_lift_orthogonal hnormal he]
      ring
    have hezero : e = 0 := by
      by_contra hne
      have hp := hpos e hne
      rw [hzero] at hp
      exact (lt_irrefl 0) hp
    exact sub_eq_zero.mp hezero
  · intro h e he
    rw [h]
    exact face_minimum_lift_orthogonal hnormal he _

section FiniteQuadraticBounds

variable {ι : Type*} [Fintype ι]

/-- A finite coordinate quadratic is bounded by its operator norm and
the literal sum of coordinate squares. -/
theorem finite_coordinate_quadratic_le
    (R : (ι → ℝ) →L[ℝ] (ι → ℝ)) (h : ι → ℝ) :
    (∑ i, R h i * h i) ≤ (Fintype.card ι : ℝ) * ‖R‖ * ∑ i, (h i) ^ 2 := by
  classical
  let S := ∑ i, (h i) ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hs (i : ι) : (h i) ^ 2 ≤ S :=
    Finset.single_le_sum (fun j _ => sq_nonneg (h j)) (Finset.mem_univ i)
  have hn : ‖h‖ ^ 2 ≤ S := by
    have hb : ‖h‖ ≤ Real.sqrt S := (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg S)).mpr
      fun i => by
        have hi := hs i
        rw [Real.norm_eq_abs]
        exact Real.le_sqrt_of_sq_le (by simpa only [sq_abs] using hi)
    nlinarith [norm_nonneg h, Real.sq_sqrt hS, Real.sqrt_nonneg S]
  have hi (i : ι) : R h i * h i ≤ ‖R‖ * S := by
    have h₁ := norm_le_pi_norm (R h) i
    have h₂ := R.le_opNorm h
    have h₃ := norm_le_pi_norm h i
    have hb := mul_le_mul (h₁.trans h₂) h₃ (norm_nonneg (h i))
      (mul_nonneg (norm_nonneg R) (norm_nonneg h))
    have hab : R h i * h i ≤ ‖R h i‖ * ‖h i‖ := by
      simpa only [Real.norm_eq_abs, ← abs_mul] using le_abs_self (R h i * h i)
    calc
      R h i * h i ≤ ‖R h i‖ * ‖h i‖ := hab
      _ ≤ (‖R‖ * ‖h‖) * ‖h‖ := hb
      _ = ‖R‖ * ‖h‖ ^ 2 := by ring
      _ ≤ ‖R‖ * S := mul_le_mul_of_nonneg_left hn (norm_nonneg R)
  calc
    (∑ i, R h i * h i) ≤ ∑ i : ι, ‖R‖ * S := Finset.sum_le_sum fun i _ => hi i
    _ = (Fintype.card ι : ℝ) * ‖R‖ * S := by simp [nsmul_eq_mul]; ring

end FiniteQuadraticBounds

/-- The native coordinate pairing, as a continuous linear map into covectors. -/
def coordinatePairingCLM {ι : Type*} [Fintype ι] :
    (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (ContinuousLinearMap.proj i)

@[simp] theorem coordinatePairingCLM_apply {ι : Type*} [Fintype ι]
    (p X : ι → ℝ) : coordinatePairingCLM p X = ∑ i, p i * X i := by
  simp [coordinatePairingCLM]

/-- The literal second derivative is paired with the native coordinate
Hessian. Local smoothness at the nonzero point suffices. -/
theorem second_fderiv_eq_coordinate_hessian {φ : RealSpace n → ℝ}
    (hd : Differentiable ℝ φ) {x : RealSpace n} (hs : ContDiffAt ℝ ∞ φ x)
    (X Y : RealSpace n) :
    fderiv ℝ (fderiv ℝ φ) x X Y =
      ∑ j, fderiv ℝ (coordinateGradient φ) x X j * Y j := by
  have he : (fun u => coordinatePairingCLM (coordinateGradient φ u)) = fderiv ℝ φ := by
    funext u
    ext V
    simpa only [coordinatePairingCLM_apply] using (fderiv_eq_coordinateGradient_pairing φ u V).symm
  have hg := (contDiffAt_coordinateGradient hd hs).differentiableAt (by simp)
  have hh := coordinatePairingCLM.hasFDerivAt.comp x hg.hasFDerivAt
  change HasFDerivAt (fun u => coordinatePairingCLM (coordinateGradient φ u)) _ x at hh
  rw [he] at hh
  rw [hh.fderiv]
  simp

/-- Schwarz symmetry transfers to the based native Hessian at a smooth point. -/
theorem coordinate_hessian_symmetric_at {φ : RealSpace n → ℝ}
    (hd : Differentiable ℝ φ) {x : RealSpace n} (hs : ContDiffAt ℝ ∞ φ x)
    (X Y : RealSpace n) :
    (∑ j, fderiv ℝ (coordinateGradient φ) x X j * Y j) =
      ∑ j, fderiv ℝ (coordinateGradient φ) x Y j * X j := by
  rw [← second_fderiv_eq_coordinate_hessian hd hs,
    ← second_fderiv_eq_coordinate_hessian hd hs]
  exact hs.isSymmSndFDerivAt (by simp) X Y

/-- The actual homogeneous Hessian is degree zero; the origin is never used. -/
theorem IsStronglyCompatibleEndPotential.native_hessian_smul
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) (hd : Differentiable ℝ φ)
    {x : RealSpace n} (hx : x ≠ 0) {β : ℝ} (hβ : 0 < β) :
    fderiv ℝ (coordinateGradient φ) (β • x) = fderiv ℝ (coordinateGradient φ) x := by
  have hg : DifferentiableAt ℝ (coordinateGradient φ) x :=
    (contDiffAt_coordinateGradient hd (hφ.smooth x hx)).differentiableAt (by simp)
  have hgb : DifferentiableAt ℝ (coordinateGradient φ) (β • x) :=
    (contDiffAt_coordinateGradient hd (hφ.smooth _ (smul_ne_zero hβ.ne' hx))).differentiableAt (by simp)
  have hl := hgb.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul β)
  have hr := hg.hasFDerivAt.const_smul β
  have he : (fun u => coordinateGradient φ (β • u)) =ᶠ[𝓝 x]
      (fun u => β • coordinateGradient φ u) := by
    filter_upwards [eventually_ne_nhds hx] with u hu
    exact coordinateGradient_smul_of_homogeneous_two hφ.homogeneous
      (fun u hu => (hφ.smooth u hu).differentiableAt (by simp)) hu hβ
  have heq := hl.unique (hr.congr_of_eventuallyEq he)
  apply ContinuousLinearMap.ext
  intro V
  apply smul_right_injective (RealSpace n) hβ.ne'
  have hv := congrArg (fun L : RealSpace n →L[ℝ] RealSpace n => L V) heq
  simpa only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul] using hv

/-- Both identities behind the orthogonal splitting follow by differentiating
the actual affine levels and normal equation. -/
theorem face_minimum_derivative_equations {φ : RealSpace n → ℝ}
    (hd : Differentiable ℝ φ) {s : Finset (Lattice n)}
    {x : (s → ℝ) → RealSpace n} {a : (s → ℝ) → (s → ℝ)} {y : s → ℝ}
    (hx : DifferentiableAt ℝ x y) (ha : DifferentiableAt ℝ a y)
    (hφ : ContDiffAt ℝ ∞ φ (x y))
    (hlevel : (fun w => faceLevelMap s (x w)) =ᶠ[𝓝 y] (fun w v => 1 + w v))
    (hnormal : (fun w => coordinateGradient φ (x w)) =ᶠ[𝓝 y]
      (fun w => faceNormalMap s (a w))) :
    (faceLevelMap s).comp (fderiv ℝ x y) = ContinuousLinearMap.id ℝ (s → ℝ) ∧
    (fderiv ℝ (coordinateGradient φ) (x y)).comp (fderiv ℝ x y) =
      (faceNormalMap s).comp (fderiv ℝ a y) := by
  have hA := (face_reduced_hessian_identity hd hx ha hφ hlevel hnormal).1
  have hg := (contDiffAt_coordinateGradient hd hφ).differentiableAt (by simp)
  exact ⟨hA, (hg.hasFDerivAt.comp y hx.hasFDerivAt).unique
    (((faceNormalMap s).hasFDerivAt.comp y ha.hasFDerivAt).congr_of_eventuallyEq hnormal)⟩

/-- Branch continuity alone supplies the large-multiplier domination.
The reduced Hessian and weights are the literal derivative and branch,
not an assumed negative block or inertia certificate. -/
theorem face_branch_eventually_reduced_radial_negative
    {s : Finset (Lattice n)} [Nonempty s]
    {a : (s → ℝ) → (s → ℝ)} {z : ℝ → ((s → ℝ) × ℝ)}
    (ha : ContDiffAt ℝ ∞ a 0) (hz : ContinuousAt z 0)
    (hq : ∀ v, 0 < (z 0).1 v) (hmu : 0 < (z 0).2) :
    ∀ᶠ β : ℝ in atTop, ∀ h : s → ℝ, h ≠ 0 →
      (∑ v, fderiv ℝ a (β⁻¹ • (fun v => Real.log ((z β⁻¹).1 v))) h v * h v) -
        (β * (z β⁻¹).2) * faceWeightSquare (z β⁻¹).1 h < 0 := by
  classical
  obtain ⟨v₀, _, hv₀⟩ := Finset.exists_min_image Finset.univ
    (fun v : s => (z 0).1 v) Finset.univ_nonempty
  let δ := (z 0).1 v₀ / 2
  let μ := (z 0).2 / 2
  let C := ‖fderiv ℝ a 0‖ + 1
  have hδ : 0 < δ := half_pos (hq v₀)
  have hμ : 0 < μ := half_pos hmu
  have hC : 0 < C := by dsimp [C]; positivity
  have hqevent : ∀ᶠ ε : ℝ in 𝓝 0, ∀ v : s, δ < (z ε).1 v := by
    rw [eventually_all]
    intro v
    have hv : δ < (z 0).1 v := (half_lt_self (hq v₀)).trans_le (hv₀ v (Finset.mem_univ v))
    exact ((continuous_apply v).continuousAt.comp hz.fst).eventually (eventually_gt_nhds hv)
  have hmuevent : ∀ᶠ ε : ℝ in 𝓝 0, μ < (z ε).2 :=
    hz.snd.eventually (eventually_gt_nhds (half_lt_self hmu))
  have hparam : Tendsto (fun β : ℝ => β⁻¹ • (fun v => Real.log ((z β⁻¹).1 v)))
      atTop (𝓝 0) := by
    have hlog : ContinuousAt (fun ε : ℝ => fun v : s => Real.log ((z ε).1 v)) 0 :=
      continuousAt_pi.mpr fun v =>
        ((continuous_apply v).continuousAt.comp hz.fst).log (hq v).ne'
    have hc : ContinuousAt (fun ε : ℝ => ε • (fun v : s => Real.log ((z ε).1 v))) 0 :=
      continuousAt_id.smul hlog
    simpa only [Function.comp_def, zero_smul] using
      hc.tendsto.comp (tendsto_inv_atTop_zero (𝕜 := ℝ))
  have hbound : ∀ᶠ y : s → ℝ in 𝓝 0, ‖fderiv ℝ a y‖ < C :=
    (ha.continuousAt_fderiv (by simp)).norm.tendsto.eventually_lt_const (by dsimp [C]; linarith)
  filter_upwards [hparam.eventually hbound,
    tendsto_inv_atTop_zero.eventually hqevent, tendsto_inv_atTop_zero.eventually hmuevent,
    eventually_gt_atTop ((Fintype.card s : ℝ) * C / (μ * δ)),
    eventually_gt_atTop (0 : ℝ)] with β hR hqβ hμβ hβ hβpos h hh
  have hlarge : (Fintype.card s : ℝ) * C < (β * (z β⁻¹).2) * δ := by
    have hb : (Fintype.card s : ℝ) * C < β * (μ * δ) := (div_lt_iff₀ (mul_pos hμ hδ)).mp hβ
    have hm := mul_lt_mul_of_pos_left hμβ hβpos
    nlinarith [mul_pos hβpos hδ]
  have hS : 0 < ∑ v : s, (h v) ^ 2 := by
    have hn : ∀ v, 0 ≤ (h v) ^ 2 := fun v => sq_nonneg _
    have hne : ∃ v, h v ≠ 0 := by contrapose! hh; exact funext hh
    obtain ⟨v, hv⟩ := hne
    exact lt_of_lt_of_le (sq_pos_of_ne_zero hv)
      (Finset.single_le_sum (fun w _ => hn w) (Finset.mem_univ v))
  have hw : δ * (∑ v : s, (h v) ^ 2) ≤ faceWeightSquare (z β⁻¹).1 h := by
    rw [faceWeightSquare, Finset.mul_sum]
    exact Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_right (hqβ v).le (sq_nonneg _)
  have hr := finite_coordinate_quadratic_le
    (fderiv ℝ a (β⁻¹ • (fun v => Real.log ((z β⁻¹).1 v)))) h
  have hr' : (Fintype.card s : ℝ) * ‖fderiv ℝ a
      (β⁻¹ • (fun v => Real.log ((z β⁻¹).1 v)))‖ * (∑ v : s, (h v) ^ 2) ≤
      (Fintype.card s : ℝ) * C * (∑ v : s, (h v) ^ 2) := by
    gcongr
  have hmupos : 0 < β * (z β⁻¹).2 := mul_pos hβpos (hμ.trans hμβ)
  have hw' := mul_le_mul_of_nonneg_left hw hmupos.le
  have hs' := mul_lt_mul_of_pos_right hlarge hS
  nlinarith

/-- The source's full real tangent splitting is an actual linear equivalence. -/
def faceTangentSplitEquiv {s : Finset (Lattice n)}
    {B : (s → ℝ) →L[ℝ] RealSpace n}
    (hB : (faceLevelMap s).comp B = ContinuousLinearMap.id ℝ (s → ℝ))
    (q : s → ℝ) :
    ((faceLevelMap s).toLinearMap.ker × (faceWeightFunctional q).toLinearMap.ker) ≃ₗ[ℝ]
      faceRealTangent q where
  toFun p := ⟨p.1.val + B p.2.val, by
    change faceWeightFunctional q (faceLevelMap s (p.1.val + B p.2.val)) = 0
    have hb := congrArg (fun L : (s → ℝ) →L[ℝ] (s → ℝ) => L p.2.val) hB
    change faceLevelMap s (B p.2.val) = p.2.val at hb
    have he : faceLevelMap s p.1.val = 0 := p.1.property
    rw [map_add, he, hb, zero_add]
    exact p.2.property⟩
  invFun X := (⟨X.val - B (faceLevelMap s X.val),
    (faceRealTangent_split hB q X.property).1⟩,
    ⟨faceLevelMap s X.val, X.property⟩)
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      have he : faceLevelMap s p.1.val = 0 := p.1.property
      have hb := congrArg (fun L : (s → ℝ) →L[ℝ] (s → ℝ) => L p.2.val) hB
      change faceLevelMap s (B p.2.val) = p.2.val at hb
      simp only [map_add, he, hb, zero_add, add_sub_cancel_right]
    · apply Subtype.ext
      have he : faceLevelMap s p.1.val = 0 := p.1.property
      have hb := congrArg (fun L : (s → ℝ) →L[ℝ] (s → ℝ) => L p.2.val) hB
      change faceLevelMap s (B p.2.val) = p.2.val at hb
      simp only [map_add, he, hb, zero_add]
  right_inv X := Subtype.ext (sub_add_cancel _ _)
  map_add' p r := by
    apply Subtype.ext
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, map_add]
    abel
  map_smul' c p := by
    apply Subtype.ext
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, map_smul, smul_add]
    rfl

/-- The kernel block has the exact face codimension. -/
theorem face_kernel_finrank {s : Finset (Lattice n)}
    (hA : Surjective (faceLevelMap s)) :
    Module.finrank ℝ (faceLevelMap s).toLinearMap.ker = n - s.card := by
  have h := (faceLevelMap s).toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hA, finrank_top, Module.finrank_pi,
    Module.finrank_pi, Fintype.card_fin, Fintype.card_coe] at h
  omega

/-- A positive nonempty face has one independent tangent constraint. -/
theorem face_weight_kernel_finrank {s : Finset (Lattice n)} [Nonempty s]
    {q : s → ℝ} (hq : ∀ v, 0 < q v) :
    Module.finrank ℝ (faceWeightFunctional q).toLinearMap.ker = s.card - 1 := by
  classical
  let v : s := Classical.arbitrary s
  have hsurj : Surjective (faceWeightFunctional q) := by
    intro a
    refine ⟨Pi.single v (a / q v), ?_⟩
    simp only [faceWeightFunctional_apply, Pi.single_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    field_simp [(hq v).ne']
  have h := (faceWeightFunctional q).toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h
  simp only [Module.finrank_self, Module.finrank_pi, Fintype.card_coe] at h
  omega

/-- Dimensions of all four source blocks, before duplicating radial/angular
copies: the common kernel is `n-k`, the lift is `k-1`, their sum is `n-1`. -/
theorem face_inertia_block_dimensions {s : Finset (Lattice n)} [Nonempty s]
    (hA : Surjective (faceLevelMap s)) {q : s → ℝ} (hq : ∀ v, 0 < q v) :
    Module.finrank ℝ (faceLevelMap s).toLinearMap.ker = n - s.card ∧
    Module.finrank ℝ (faceWeightFunctional q).toLinearMap.ker = s.card - 1 ∧
    Module.finrank ℝ ((faceLevelMap s).toLinearMap.ker ×
      (faceWeightFunctional q).toLinearMap.ker) = n - 1 := by
  have h := (faceLevelMap s).toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hA, finrank_top, Module.finrank_pi,
    Module.finrank_pi, Fintype.card_fin, Fintype.card_coe] at h
  have hs : 0 < s.card := by
    simpa only [Fintype.card_coe] using Fintype.card_pos (α := s)
  refine ⟨face_kernel_finrank hA, face_weight_kernel_finrank hq, ?_⟩
  rw [Module.finrank_prod, face_kernel_finrank hA, face_weight_kernel_finrank hq]
  omega

/-- The bilinear form whose diagonal is the computed constrained Hessian. -/
def faceConstrainedPairing (s : Finset (Lattice n))
    (H : RealSpace n →L[ℝ] RealSpace n) (q : s → ℝ) (lam : ℝ)
    (V W : TangentCoordinates n) : ℝ :=
  (∑ j, H V.1 j * W.1 j) -
    lam * (∑ v, q v * faceLevelMap s V.1 v * faceLevelMap s W.1 v) +
    lam * (∑ v, q v * faceLevelMap s V.2 v * faceLevelMap s W.2 v)

theorem faceConstrainedPairing_self (s : Finset (Lattice n))
    (H : RealSpace n →L[ℝ] RealSpace n) (q : s → ℝ) (lam : ℝ)
    (V : TangentCoordinates n) :
    faceConstrainedPairing s H q lam V V = faceConstrainedHessian s H q lam V := by
  simp only [faceConstrainedPairing, faceConstrainedHessian, faceWeightSquare,
    pow_two, mul_assoc]

/-- The full bilinear radical is exactly the angular face kernel. In
particular, cancellation between positive and negative squares creates
no extra kernel directions. -/
theorem faceConstrainedPairing_radical_iff {s : Finset (Lattice n)}
    {H : RealSpace n →L[ℝ] RealSpace n} {B : (s → ℝ) →L[ℝ] RealSpace n}
    {R : (s → ℝ) →L[ℝ] (s → ℝ)}
    (hB : (faceLevelMap s).comp B = ContinuousLinearMap.id ℝ (s → ℝ))
    (hnormal : H.comp B = (faceNormalMap s).comp R)
    (hH : ∀ e : RealSpace n, e ≠ 0 → 0 < ∑ j, H e j * e j)
    {q : s → ℝ} (hq : ∀ v, 0 < q v) {lam : ℝ} (hlam : 0 < lam)
    (hnegative : ∀ h : s → ℝ, h ≠ 0 →
      (∑ v, R h v * h v) - lam * faceWeightSquare q h < 0)
    (V : TangentCoordinates n) (hV₁ : V.1 ∈ faceRealTangent q)
    (hV₂ : V.2 ∈ faceRealTangent q) :
    (∀ W : TangentCoordinates n, W.1 ∈ faceRealTangent q → W.2 ∈ faceRealTangent q →
      faceConstrainedPairing s H q lam V W = 0) ↔
      V.1 = 0 ∧ faceLevelMap s V.2 = 0 := by
  have hright (h : s → ℝ) : faceLevelMap s (B h) = h :=
    congrArg (fun L : (s → ℝ) →L[ℝ] (s → ℝ) => L h) hB
  constructor
  · intro hrad
    let h := faceLevelMap s V.1
    let e := V.1 - B h
    have he : faceLevelMap s e = 0 := by dsimp [e, h]; rw [map_sub, hright, sub_self]
    have het : e ∈ faceRealTangent q := by change faceWeightFunctional q (faceLevelMap s e) = 0; rw [he, map_zero]
    have hzero := hrad (e, 0) het (by simp)
    have hXe : (∑ j, H V.1 j * e j) = 0 := by
      simpa only [faceConstrainedPairing, he, map_zero, Pi.zero_apply,
        mul_zero, Finset.sum_const_zero, sub_zero, add_zero] using hzero
    have hezero : e = 0 := by
      by_contra hne
      have hp := hH e hne
      have hz : (∑ j, H e j * e j) = 0 := by
        simp only [e, map_sub, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
        change (∑ j, H V.1 j * e j) - (∑ j, H (B h) j * e j) = 0
        rw [hXe, face_minimum_lift_orthogonal hnormal he]
        ring
      rw [hz] at hp
      exact (lt_irrefl 0) hp
    have hX : V.1 = B h := sub_eq_zero.mp hezero
    have hBt : B h ∈ faceRealTangent q := hX ▸ hV₁
    have hzero := hrad (B h, 0) hBt (by simp)
    have hhzero : (∑ v, R h v * h v) - lam * faceWeightSquare q h = 0 := by
      simp only [faceConstrainedPairing] at hzero
      rw [hX] at hzero
      simpa only [faceConstrainedPairing, faceWeightSquare, hright, map_zero,
        Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, pow_two, mul_assoc,
        face_minimum_lift_hessian hB hnormal h h] using hzero
    have hh : h = 0 := by
      by_contra hne
      have hn := hnegative h hne
      rw [hhzero] at hn
      exact (lt_irrefl 0) hn
    have hXzero : V.1 = 0 := by rw [hX, hh, map_zero]
    have hyzero := hrad (0, V.2) (by simp) hV₂
    have hsquare : lam * faceWeightSquare q (faceLevelMap s V.2) = 0 := by
      simpa only [faceConstrainedPairing, faceWeightSquare, map_zero, Pi.zero_apply,
        zero_mul, mul_zero, Finset.sum_const_zero, mul_assoc, pow_two, sub_zero, zero_add] using hyzero
    have hs := (mul_eq_zero.mp hsquare).resolve_left hlam.ne'
    have hsum := (Finset.sum_eq_zero_iff_of_nonneg
      (fun v (_ : v ∈ Finset.univ) => mul_nonneg (hq v).le
        (sq_nonneg (faceLevelMap s V.2 v)))).mp hs
    refine ⟨hXzero, funext fun v => ?_⟩
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp (hsum v (Finset.mem_univ v))).resolve_left (hq v).ne')
  · rintro ⟨hX, hY⟩ W _ _
    simp only [faceConstrainedPairing, hX, hY, map_zero, Pi.zero_apply,
      zero_mul, mul_zero, Finset.sum_const_zero, sub_zero, add_zero]

/-- At the reconstructed branch the actual ambient Hessian and the actual
minimizer derivative give the complete positive/negative/zero/positive
orthogonal formula. Every estimate is produced from the potential and branch. -/
theorem IsStronglyCompatibleEndPotential.eventually_actual_face_hessian_blocks
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) (hd : Differentiable ℝ φ)
    {s : Finset (Lattice n)} [Nonempty s]
    {x : (s → ℝ) → RealSpace n} {z : ℝ → ((s → ℝ) × ℝ)}
    (hxs : ContDiffAt ℝ ∞ x 0)
    (has : ContDiffAt ℝ ∞ (faceReducedCoefficient φ x) 0)
    (hzs : ContDiffAt ℝ ∞ z 0) (hxne : x 0 ≠ 0)
    (hq : ∀ v, 0 < (z 0).1 v) (hmu : 0 < (z 0).2)
    (hlevel : ∀ᶠ y in 𝓝 0, faceLevelMap s (x y) = fun v => 1 + y v)
    (hnormal : ∀ᶠ y in 𝓝 0, coordinateGradient φ (x y) =
      faceNormalMap s (faceReducedCoefficient φ x y)) :
    ∀ᶠ β : ℝ in atTop,
      let y := β⁻¹ • (fun v : s => Real.log ((z β⁻¹).1 v))
      let B := fderiv ℝ x y
      let R := fderiv ℝ (faceReducedCoefficient φ x) y
      let H := fderiv ℝ (coordinateGradient φ) (faceCriticalRadius x z β)
      let q := (z β⁻¹).1
      let lam := β * (z β⁻¹).2
      (faceLevelMap s).comp B = ContinuousLinearMap.id ℝ (s → ℝ) ∧
      H.comp B = (faceNormalMap s).comp R ∧
      (∀ X Y, (∑ j, H X j * Y j) = ∑ j, H Y j * X j) ∧
      (∀ e : RealSpace n, e ≠ 0 → 0 < ∑ j, H e j * e j) ∧
      (∀ h : s → ℝ, h ≠ 0 → (∑ v, R h v * h v) - lam * faceWeightSquare q h < 0) ∧
      (∀ k : s → ℝ, k ≠ 0 → 0 < lam * faceWeightSquare q k) ∧
      (∀ e f : RealSpace n, faceLevelMap s e = 0 → faceLevelMap s f = 0 →
        ∀ h k : s → ℝ,
          faceConstrainedHessian s H q lam (e + B h, f + B k) =
            (∑ j, H e j * e j) +
            ((∑ v, R h v * h v) - lam * faceWeightSquare q h) +
            lam * faceWeightSquare q k) ∧
      (∀ V : TangentCoordinates n, V.1 ∈ faceRealTangent q → V.2 ∈ faceRealTangent q →
        ((∀ W : TangentCoordinates n, W.1 ∈ faceRealTangent q → W.2 ∈ faceRealTangent q →
          faceConstrainedPairing s H q lam V W = 0) ↔
            V.1 = 0 ∧ faceLevelMap s V.2 = 0)) ∧
      Module.finrank ℝ (faceLevelMap s).toLinearMap.ker = n - s.card ∧
      Module.finrank ℝ (faceWeightFunctional q).toLinearMap.ker = s.card - 1 ∧
      Module.finrank ℝ ((faceLevelMap s).toLinearMap.ker ×
        (faceWeightFunctional q).toLinearMap.ker) = n - 1 := by
  have hzc := hzs.continuousAt
  have hlog : ContinuousAt (fun ε : ℝ => fun v : s => Real.log ((z ε).1 v)) 0 :=
    continuousAt_pi.mpr fun v =>
      ((continuous_apply v).continuousAt.comp hzc.fst).log (hq v).ne'
  have hp : ContinuousAt (fun ε : ℝ => ε • (fun v : s => Real.log ((z ε).1 v))) 0 :=
    continuousAt_id.smul hlog
  have hparam : Tendsto (fun β : ℝ => β⁻¹ • (fun v : s => Real.log ((z β⁻¹).1 v)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_smul] using
      hp.tendsto.comp (tendsto_inv_atTop_zero (𝕜 := ℝ))
  have hxd : ∀ᶠ y in 𝓝 (0 : s → ℝ), DifferentiableAt ℝ x y :=
    ((hxs.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).eventually (by simp)).mono
      fun y hy => hy.differentiableAt_one
  have had : ∀ᶠ y in 𝓝 (0 : s → ℝ), DifferentiableAt ℝ (faceReducedCoefficient φ x) y :=
    ((has.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).eventually (by simp)).mono
      fun y hy => hy.differentiableAt_one
  have hne := hxs.continuousAt.eventually (eventually_ne_nhds hxne)
  have hleq : (fun y => faceLevelMap s (x y)) =ᶠ[𝓝 0] (fun y v => 1 + y v) := hlevel
  have hneq : (fun y => coordinateGradient φ (x y)) =ᶠ[𝓝 0]
      (fun y => faceNormalMap s (faceReducedCoefficient φ x y)) := hnormal
  have hidentities : ∀ᶠ y in 𝓝 (0 : s → ℝ),
      x y ≠ 0 ∧
      (faceLevelMap s).comp (fderiv ℝ x y) = ContinuousLinearMap.id ℝ (s → ℝ) ∧
      (fderiv ℝ (coordinateGradient φ) (x y)).comp (fderiv ℝ x y) =
        (faceNormalMap s).comp (fderiv ℝ (faceReducedCoefficient φ x) y) := by
    filter_upwards [hxd, had, hne, hleq.eventuallyEq_nhds,
      hneq.eventuallyEq_nhds] with y hx ha hny hl hn
    exact ⟨hny, face_minimum_derivative_equations hd hx ha (hφ.smooth _ hny) hl hn⟩
  have hqpos : ∀ᶠ ε : ℝ in 𝓝 0, ∀ v : s, 0 < (z ε).1 v := by
    rw [eventually_all]
    intro v
    exact ((continuous_apply v).continuousAt.comp hzc.fst).eventually (eventually_gt_nhds (hq v))
  have hmupos : ∀ᶠ ε : ℝ in 𝓝 0, 0 < (z ε).2 :=
    hzc.snd.eventually (eventually_gt_nhds hmu)
  have hneg := face_branch_eventually_reduced_radial_negative has hzc hq hmu
  filter_upwards [hparam.eventually hidentities, hneg,
    tendsto_inv_atTop_zero.eventually hqpos, tendsto_inv_atTop_zero.eventually hmupos,
    eventually_gt_atTop (0 : ℝ)] with β hi hn hqβ hμ hβ
  dsimp only
  let y := β⁻¹ • (fun v : s => Real.log ((z β⁻¹).1 v))
  have hscale : fderiv ℝ (coordinateGradient φ) (faceCriticalRadius x z β) =
      fderiv ℝ (coordinateGradient φ) (x y) :=
    hφ.native_hessian_smul hd hi.1 hβ
  have hsymm := coordinate_hessian_symmetric_at hd
    (hφ.smooth _ (smul_ne_zero hβ.ne' hi.1))
  have hH : ∀ e : RealSpace n, e ≠ 0 →
      0 < ∑ j, fderiv ℝ (coordinateGradient φ) (faceCriticalRadius x z β) e j * e j :=
    fun e he => hφ.native_hessian_pos hd (smul_ne_zero hβ.ne' hi.1) he
  have hHB : (fderiv ℝ (coordinateGradient φ) (faceCriticalRadius x z β)).comp
      (fderiv ℝ x y) = (faceNormalMap s).comp (fderiv ℝ (faceReducedCoefficient φ x) y) := by
    rw [hscale]
    exact hi.2.2
  refine ⟨hi.2.1, hHB, hsymm, hH, hn, ?_, ?_, ?_, ?_⟩
  · intro k hk
    apply mul_pos (mul_pos hβ hμ)
    have hzero : faceWeightSquare (z β⁻¹).1 k ≠ 0 := by
      intro hz
      have hsum := (Finset.sum_eq_zero_iff_of_nonneg
        (fun v (_ : v ∈ Finset.univ) => mul_nonneg (hqβ v).le (sq_nonneg (k v)))).mp hz
      apply hk
      ext v
      have hv := hsum v (Finset.mem_univ v)
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hv).resolve_left (hqβ v).ne')
    exact lt_of_le_of_ne
      (Finset.sum_nonneg fun v _ => mul_nonneg (hqβ v).le (sq_nonneg _)) (Ne.symm hzero)
  · intro e f he hf h k
    exact faceConstrainedHessian_four_blocks hi.2.1 hHB
      hsymm _ _ he hf h k
  · intro V hV₁ hV₂
    exact faceConstrainedPairing_radical_iff hi.2.1 hHB hH hqβ
      (mul_pos hβ hμ) hn V hV₁ hV₂
  · have hA : Surjective (faceLevelMap s) := by
      intro a
      refine ⟨fderiv ℝ x y a, ?_⟩
      exact congrArg (fun L : (s → ℝ) →L[ℝ] (s → ℝ) => L a) hi.2.1
    exact face_inertia_block_dimensions hA hqβ

end FsFltz
