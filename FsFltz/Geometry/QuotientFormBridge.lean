import FsFltz.Geometry.ToricForms

/-!
# Actual quotient forms in representative coordinates

The cover map and its tangent map below are the literal quotient projection
and its actual manifold derivative. The formula comparisons implement the
descent requirement of `geoemtric-part-fsf.tex`, `sec:data`, lines 68–85,
and the foundational bridge in `sec:lean`, lines 778–814.
No symplecticity, completeness, or geometric comparison existence is asserted.
-/

noncomputable section
open scoped Manifold ContDiff BigOperators ComplexConjugate

namespace FsFltz.Geometry
open SmoothManifold

local instance realContMDiffMul : ContMDiffMul 𝓘(ℝ, ℝ) ∞ ℝ where
  contMDiff_mul := by
    rw [contMDiff_iff]
    exact ⟨continuous_mul, fun _ _ => contDiff_mul.contDiffOn⟩

/-- The actual logarithmic quotient projection, with no angle choice on `Y`. -/
def lgCover {n : ℕ} (x : TangentCoordinates n) : (lgManifold n).Point :=
  (x.1, angleQuotient x.2)

theorem contMDiff_lgCover (n : ℕ) :
    ContMDiff 𝓘(ℝ, TangentCoordinates n) 𝓘(ℝ, Model (2 * n)) ∞ (lgCover (n := n)) := by
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hf : ContMDiff 𝓘(ℝ, TangentCoordinates n) 𝓘(ℝ, RealSpace n) ∞
      (Prod.fst : TangentCoordinates n → RealSpace n) :=
    (ContinuousLinearMap.fst ℝ (RealSpace n) (RealSpace n)).contDiff.contMDiff
  have hs : ContMDiff 𝓘(ℝ, TangentCoordinates n) 𝓘(ℝ, RealSpace n) ∞
      (Prod.snd : TangentCoordinates n → RealSpace n) :=
    (ContinuousLinearMap.snd ℝ (RealSpace n) (RealSpace n)).contDiff.contMDiff
  exact (contMDiff_linearRechart_id (M := LGSpace n) (lgEuclideanEquiv n)).comp
    (hf.prodMk (contMDiff_angleQuotient.comp hs))

/-- Tangent vectors transported by the derivative of the actual cover map. -/
def lgCoverTangent {n : ℕ} (x : TangentCoordinates n) :
    TangentCoordinates n →L[ℝ] (lgManifold n).Tangent (lgCover x) :=
  mfderiv 𝓘(ℝ, TangentCoordinates n) 𝓘(ℝ, Model (2 * n)) lgCover x

theorem lgCircleCoordinate_lgCover {n : ℕ} (j : Fin n) (x : TangentCoordinates n) :
    lgCircleCoordinate j (lgCover x) = Complex.exp ((x.2 j : ℂ) * Complex.I) := by
  simp [lgCircleCoordinate, lgCover, angleQuotient, AddCircle.toCircle_apply_mk,
    Circle.coe_exp, Real.pi_ne_zero]

/-- Derivative of the circle coordinate along the actual quotient projection. -/
theorem complexDifferential_lgCircleCoordinate_lgCover {n : ℕ}
    (j : Fin n) (x q : TangentCoordinates n) :
    complexDifferential (lgManifold n) (lgCircleCoordinate j) (lgCover x)
      (lgCoverTangent x q) =
        lgCircleCoordinate j (lgCover x) * ((q.2 j : ℂ) * Complex.I) := by
  let a : TangentCoordinates n →L[ℝ] ℂ :=
    Complex.I • Complex.ofRealCLM.comp ((ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.snd ℝ (RealSpace n) (RealSpace n)))
  have ha (z : TangentCoordinates n) : a z = (z.2 j : ℂ) * Complex.I := by
    simp [a, mul_comm]
  have hd := (Complex.hasStrictFDerivAt_exp_real (a x)).hasFDerivAt.comp x a.hasFDerivAt
  have hf : (fun z : TangentCoordinates n => lgCircleCoordinate j (lgCover z)) =
      Complex.exp ∘ a := by
    ext z
    simp [lgCircleCoordinate_lgCover, ha]
  have h := mfderiv_comp_apply x
    ((contMDiff_lg_circleCoordinate j).mdifferentiable (by simp) (lgCover x))
    ((contMDiff_lgCover n).mdifferentiable (by simp) x) q
  rw [mfderiv_eq_fderiv] at h
  change fderiv ℝ (fun z => lgCircleCoordinate j (lgCover z)) x q =
    complexDifferential (lgManifold n) (lgCircleCoordinate j) (lgCover x)
      (lgCoverTangent x q) at h
  rw [hf, hd.fderiv] at h
  simpa [lgCircleCoordinate_lgCover, ContinuousLinearMap.comp_apply, ha] using h.symm

/-- The actual descended angular covector pulls back to `d theta_j`. -/
theorem lgAngleCovector_lgCover {n : ℕ} (j : Fin n) (x q : TangentCoordinates n) :
    lgAngleCovector j (lgCover x) (lgCoverTangent x q) = q.2 j := by
  rw [lgAngleCovector, phaseCovector_apply,
    complexDifferential_lgCircleCoordinate_lgCover, ← mul_assoc,
    ← Complex.normSq_eq_conj_mul_self]
  have hn : Complex.normSq (lgCircleCoordinate j (lgCover x)) = 1 := by
    simp [lgCircleCoordinate, Complex.normSq_eq_norm_sq, Circle.norm_coe]
  simp [hn]

theorem contMDiff_lgLogCoordinate {n : ℕ} (j : Fin n) :
    ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞
      (fun y : (lgManifold n).Point => y.1 j) := by
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have h : ContMDiff 𝓘(ℝ, LGCoordinates n) 𝓘(ℝ, ℝ) ∞
      (fun y : LGSpace n => y.1 j) :=
    ((contDiff_apply ℝ ℝ j).contMDiff.comp
      (contMDiff_fst : ContMDiff (lgModel n) 𝓘(ℝ, RealSpace n) ∞
        (Prod.fst : LGSpace n → _)))
  exact h.comp (contMDiff_linearRechart_id_symm (M := LGSpace n) (lgEuclideanEquiv n))

/-- The actual logarithmic coordinate differential pulls back to `du_j`. -/
theorem lgLogCovector_lgCover {n : ℕ} (j : Fin n) (x q : TangentCoordinates n) :
    lgLogCovector j (lgCover x) (lgCoverTangent x q) = q.1 j := by
  let a : TangentCoordinates n →L[ℝ] ℝ := (ContinuousLinearMap.proj j).comp
    (ContinuousLinearMap.fst ℝ (RealSpace n) (RealSpace n))
  have h := mfderiv_comp_apply x
    ((contMDiff_lgLogCoordinate j).mdifferentiable (by simp) (lgCover x))
    ((contMDiff_lgCover n).mdifferentiable (by simp) x) q
  rw [mfderiv_eq_fderiv] at h
  change fderiv ℝ a x q = lgLogCovector j (lgCover x) (lgCoverTangent x q) at h
  rw [a.hasFDerivAt.fderiv] at h
  exact h.symm

/-- Logarithmic and angular covectors detect every tangent coordinate, so
the actual derivative of the cover projection is injective, including rank zero. -/
theorem lgCoverTangent_injective {n : ℕ} (x : TangentCoordinates n) :
    Function.Injective (lgCoverTangent x) := by
  intro q r h
  apply Prod.ext
  · funext j
    have hj := congrArg (lgLogCovector j (lgCover x)) h
    simpa only [lgLogCovector_lgCover] using hj
  · funext j
    have hj := congrArg (lgAngleCovector j (lgCover x)) h
    simpa only [lgAngleCovector_lgCover] using hj

/-- Equal finite dimensions turn the actual cover derivative into a tangent
isomorphism. This prevents the form formulas from only testing a proper
subspace of the geometric tangent fiber. -/
theorem lgCoverTangent_bijective {n : ℕ} (x : TangentCoordinates n) :
    Function.Bijective (lgCoverTangent x) := by
  have hd : Module.finrank ℝ (TangentCoordinates n) =
      Module.finrank ℝ ((lgManifold n).Tangent (lgCover x)) := by
    change Module.finrank ℝ (RealSpace n × RealSpace n) = Module.finrank ℝ (Model (2 * n))
    simp [RealSpace, Model, Module.finrank_prod, two_mul]
  exact ⟨lgCoverTangent_injective x,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp
      (lgCoverTangent_injective x)⟩

/-- The quadratic potential differential is the prescribed first rounding
covector, on actual cover tangent vectors. -/
theorem differentialCovector_phi0_lgCover {n : ℕ} (x q : TangentCoordinates n) :
    differentialCovector (lgManifold n) phi0 (lgCover x) (lgCoverTangent x q) =
      dPhi0 (lgCover x) q := by
  have hs : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞
      (fun y : (lgManifold n).Point => phi0 y) := by
    unfold phi0 realSquaredNorm
    exact (ContMDiff.sum (fun j _ => (contMDiff_lgLogCoordinate j).pow 2)).div_const 2
  let a (j : Fin n) : TangentCoordinates n →L[ℝ] ℝ := (ContinuousLinearMap.proj j).comp
    (ContinuousLinearMap.fst ℝ (RealSpace n) (RealSpace n))
  have hd := (HasFDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => ((a j).hasFDerivAt (x := x)).pow 2)).const_mul (1 / 2 : ℝ)
  have h := mfderiv_comp_apply x (hs.mdifferentiable (by simp) (lgCover x))
    ((contMDiff_lgCover n).mdifferentiable (by simp) x) q
  rw [mfderiv_eq_fderiv] at h
  change fderiv ℝ (fun z => (∑ j, (a j z) ^ 2) / 2) x q =
    differentialCovector (lgManifold n) phi0 (lgCover x) (lgCoverTangent x q) at h
  have heq : (fun z => (∑ j, (a j z) ^ 2) / 2) =
      (fun z => (1 / 2 : ℝ) * ∑ j, (a j z) ^ 2) := by ext z; ring
  rw [heq, hd.fderiv] at h
  rw [← h]
  simp [a, dPhi0, lgCover]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The previously proved representative differential is the pullback of the
actual quotient-manifold differential of `W`. -/
theorem complexDifferential_W_lgCover {n : ℕ} (I : ToricInput n)
    (x q : TangentCoordinates n) :
    complexDifferential (lgManifold n) (W I) (lgCover x) (lgCoverTangent x q) =
      dW I (lgCover x) q := by
  have h := mfderiv_comp_apply x
    ((contMDiff_W_lgManifold I).mdifferentiable (by simp) (lgCover x))
    ((contMDiff_lgCover n).mdifferentiable (by simp) x) q
  rw [mfderiv_eq_fderiv] at h
  exact h.symm.trans (fderiv_W_representatives_apply I x q)

theorem lambda0Form_lgCover {n : ℕ} (x q : TangentCoordinates n) :
    evalOne (lambda0Form n) (lgCover x) (lgCoverTangent x q) =
      lambda0Coordinates (lgCover x) q := by
  simp [lambda0Form, lambda0Coordinates, lgAngleCovector_lgCover]

/-- The actual quotient primitive has exactly the prescribed coordinate
expression along the derivative of the quotient projection. -/
theorem lambdaKForm_lgCover {n : ℕ} (I : ToricInput n) (K : ℝ)
    (x q : TangentCoordinates n) :
    evalOne (lambdaKForm I K) (lgCover x) (lgCoverTangent x q) =
      lambdaKCoordinates I K (lgCover x) q := by
  change evalOne (lambda0Form n) (lgCover x) (lgCoverTangent x q) +
    K * evalOne (superpotentialPlaneForm I) (lgCover x) (lgCoverTangent x q) = _
  rw [lambda0Form_lgCover, superpotentialPlaneForm_apply,
    complexDifferential_W_lgCover]
  unfold lambdaKCoordinates
  ring

/-- The other rounding covector is also the actual quotient differential. -/
theorem differentialCovector_absWSq_lgCover {n : ℕ} (I : ToricInput n)
    (x q : TangentCoordinates n) :
    differentialCovector (lgManifold n) (fun y => Complex.normSq (W I y))
      (lgCover x) (lgCoverTangent x q) = dAbsWSq I (lgCover x) q := by
  have hs : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞
      (fun y : (lgManifold n).Point => Complex.normSq (W I y)) :=
    by simpa only [Complex.normSq_eq_norm_sq, Function.comp_def] using
      (contDiff_norm_sq ℝ).contMDiff.comp (contMDiff_W_lgManifold I)
  have h := mfderiv_comp_apply x (hs.mdifferentiable (by simp) (lgCover x))
    ((contMDiff_lgCover n).mdifferentiable (by simp) x) q
  rw [mfderiv_eq_fderiv] at h
  exact h.symm.trans (fderiv_absWSq_representatives_apply I x q)

/-- Representative projection for the endpoint `T × N_R`, with the source's
order of angular and momentum coordinates (`sec:data`, lines 92–97). -/
def cotangentCover {n : ℕ} (x : TangentCoordinates n) : (cotangentManifold n).Point :=
  (angleQuotient x.1, x.2)

theorem contMDiff_cotangentCover (n : ℕ) :
    ContMDiff 𝓘(ℝ, TangentCoordinates n) 𝓘(ℝ, Model (2 * n)) ∞
      (cotangentCover (n := n)) := by
  let : ChartedSpace (Model (2 * n)) (Cotangent n) := (cotangentManifold n).charts
  have hf : ContMDiff 𝓘(ℝ, TangentCoordinates n) 𝓘(ℝ, RealSpace n) ∞
      (Prod.fst : TangentCoordinates n → RealSpace n) :=
    (ContinuousLinearMap.fst ℝ (RealSpace n) (RealSpace n)).contDiff.contMDiff
  have hs : ContMDiff 𝓘(ℝ, TangentCoordinates n) 𝓘(ℝ, RealSpace n) ∞
      (Prod.snd : TangentCoordinates n → RealSpace n) :=
    (ContinuousLinearMap.snd ℝ (RealSpace n) (RealSpace n)).contDiff.contMDiff
  exact (contMDiff_linearRechart_id (M := Cotangent n) (cotangentEuclideanEquiv n)).comp
    ((contMDiff_angleQuotient.comp hf).prodMk hs)

/-- The actual derivative of the cotangent representative projection. -/
def cotangentCoverTangent {n : ℕ} (x : TangentCoordinates n) :
    TangentCoordinates n →L[ℝ] (cotangentManifold n).Tangent (cotangentCover x) :=
  mfderiv 𝓘(ℝ, TangentCoordinates n) 𝓘(ℝ, Model (2 * n)) cotangentCover x

theorem cotangentCircleCoordinate_cotangentCover {n : ℕ} (j : Fin n)
    (x : TangentCoordinates n) :
    cotangentCircleCoordinate j (cotangentCover x) =
      Complex.exp ((x.1 j : ℂ) * Complex.I) := by
  simp [cotangentCircleCoordinate, cotangentCover, angleQuotient,
    AddCircle.toCircle_apply_mk, Circle.coe_exp, Real.pi_ne_zero]

theorem complexDifferential_cotangentCircleCoordinate_cotangentCover {n : ℕ}
    (j : Fin n) (x q : TangentCoordinates n) :
    complexDifferential (cotangentManifold n) (cotangentCircleCoordinate j)
      (cotangentCover x) (cotangentCoverTangent x q) =
        cotangentCircleCoordinate j (cotangentCover x) * ((q.1 j : ℂ) * Complex.I) := by
  let a : TangentCoordinates n →L[ℝ] ℂ :=
    Complex.I • Complex.ofRealCLM.comp ((ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.fst ℝ (RealSpace n) (RealSpace n)))
  have ha (z : TangentCoordinates n) : a z = (z.1 j : ℂ) * Complex.I := by
    simp [a, mul_comm]
  have hd := (Complex.hasStrictFDerivAt_exp_real (a x)).hasFDerivAt.comp x a.hasFDerivAt
  have hf : (fun z : TangentCoordinates n => cotangentCircleCoordinate j (cotangentCover z)) =
      Complex.exp ∘ a := by
    ext z
    simp [cotangentCircleCoordinate_cotangentCover, ha]
  have h := mfderiv_comp_apply x
    ((contMDiff_cotangent_circleCoordinate j).mdifferentiable (by simp) (cotangentCover x))
    ((contMDiff_cotangentCover n).mdifferentiable (by simp) x) q
  rw [mfderiv_eq_fderiv] at h
  change fderiv ℝ (fun z => cotangentCircleCoordinate j (cotangentCover z)) x q =
    complexDifferential (cotangentManifold n) (cotangentCircleCoordinate j)
      (cotangentCover x) (cotangentCoverTangent x q) at h
  rw [hf, hd.fderiv] at h
  simpa [cotangentCircleCoordinate_cotangentCover, ContinuousLinearMap.comp_apply, ha]
    using h.symm

/-- The angular covector at the cotangent endpoint has the same period and
positive sign as the source endpoint. -/
theorem cotangentAngleCovector_cotangentCover {n : ℕ} (j : Fin n)
    (x q : TangentCoordinates n) :
    cotangentAngleCovector j (cotangentCover x) (cotangentCoverTangent x q) = q.1 j := by
  rw [cotangentAngleCovector, phaseCovector_apply,
    complexDifferential_cotangentCircleCoordinate_cotangentCover, ← mul_assoc,
    ← Complex.normSq_eq_conj_mul_self]
  have hn : Complex.normSq (cotangentCircleCoordinate j (cotangentCover x)) = 1 := by
    simp [cotangentCircleCoordinate, Complex.normSq_eq_norm_sq, Circle.norm_coe]
  simp [hn]

theorem contMDiff_cotangentMomentumCoordinate {n : ℕ} (j : Fin n) :
    ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞
      (fun y : (cotangentManifold n).Point => y.2 j) := by
  let : ChartedSpace (Model (2 * n)) (Cotangent n) := (cotangentManifold n).charts
  have h : ContMDiff 𝓘(ℝ, CotangentCoordinates n) 𝓘(ℝ, ℝ) ∞
      (fun y : Cotangent n => y.2 j) :=
    ((contDiff_apply ℝ ℝ j).contMDiff.comp
      (contMDiff_snd : ContMDiff ((torusModel n).prod 𝓘(ℝ, RealSpace n))
        𝓘(ℝ, RealSpace n) ∞ (Prod.snd : Cotangent n → _)))
  exact h.comp
    (contMDiff_linearRechart_id_symm (M := Cotangent n) (cotangentEuclideanEquiv n))

theorem cotangentMomentumCovector_cotangentCover {n : ℕ} (j : Fin n)
    (x q : TangentCoordinates n) :
    cotangentMomentumCovector j (cotangentCover x) (cotangentCoverTangent x q) = q.2 j := by
  let a : TangentCoordinates n →L[ℝ] ℝ := (ContinuousLinearMap.proj j).comp
    (ContinuousLinearMap.snd ℝ (RealSpace n) (RealSpace n))
  have h := mfderiv_comp_apply x
    ((contMDiff_cotangentMomentumCoordinate j).mdifferentiable (by simp) (cotangentCover x))
    ((contMDiff_cotangentCover n).mdifferentiable (by simp) x) q
  rw [mfderiv_eq_fderiv] at h
  change fderiv ℝ a x q =
    cotangentMomentumCovector j (cotangentCover x) (cotangentCoverTangent x q) at h
  rw [a.hasFDerivAt.fderiv] at h
  exact h.symm

theorem cotangentCoverTangent_bijective {n : ℕ} (x : TangentCoordinates n) :
    Function.Bijective (cotangentCoverTangent x) := by
  have hi : Function.Injective (cotangentCoverTangent x) := by
    intro q r h
    apply Prod.ext
    · funext j
      have hj := congrArg (cotangentAngleCovector j (cotangentCover x)) h
      simpa only [cotangentAngleCovector_cotangentCover] using hj
    · funext j
      have hj := congrArg (cotangentMomentumCovector j (cotangentCover x)) h
      simpa only [cotangentMomentumCovector_cotangentCover] using hj
  have hd : Module.finrank ℝ (TangentCoordinates n) =
      Module.finrank ℝ ((cotangentManifold n).Tangent (cotangentCover x)) := by
    change Module.finrank ℝ (RealSpace n × RealSpace n) = Module.finrank ℝ (Model (2 * n))
    simp [RealSpace, Model, Module.finrank_prod, two_mul]
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hi⟩

/-- The endpoint primitive pulls back to the specified `sum p_j d theta_j`
formula on all cotangent-cover tangent coordinates. -/
theorem lambdaCanForm_cotangentCover {n : ℕ} (x q : TangentCoordinates n) :
    evalOne (lambdaCanForm n) (cotangentCover x) (cotangentCoverTangent x q) =
      ∑ j, x.2 j * q.1 j := by
  simp [lambdaCanForm, cotangentAngleCovector_cotangentCover]
  rfl

end FsFltz.Geometry
