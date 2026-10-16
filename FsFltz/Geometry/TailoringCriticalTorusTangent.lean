import FsFltz.Geometry.TailoringCriticalNativeHessian
import FsFltz.Geometry.TailoringCriticalTorusSmooth

/-!
# The true tangent of the constructed critical face torus

Source: `geometric-part-fsf-proof.tex`, `prop:morsebott`, lines 1500–1509,
1529–1531 and 1563–1569, and `lem:stable`, lines 1713–1724.
The actual differential of the constructed constant-radius quotient torus
has precisely the angular face-kernel image. Native restricted Hessian
kernels are identified with this true tangent, not just an ambient form.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set Filter Function
open scoped Topology BigOperators ContDiff Manifold

/-- The literal constant-radius face-torus embedding in the logarithmic
ambient, using actual quotient angles. -/
def faceTorusAmbientMap {n m : ℕ} (u : RealSpace n) (f : Torus m → Torus n)
    (α : Torus m) : (lgManifold n).Point := (u, f α)

theorem contMDiff_faceTorusAmbientMap {n m : ℕ} (u : RealSpace n)
    {f : Torus m → Torus n} (hf : ContMDiff (torusModel m) (torusModel n) ∞ f) :
    ContMDiff (torusModel m) 𝓘(ℝ, Model (2 * n)) ∞ (faceTorusAmbientMap u f) := by
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hp : ContMDiff (torusModel m) (lgModel n) ∞ (fun α => (u, f α)) :=
    contMDiff_const.prodMk hf
  exact (contMDiff_linearRechart_id (M := LGSpace n) (lgEuclideanEquiv n)).comp
    hp

/-- Differentiate the actual descended monomial after the native quotient
cover, with the same logarithmic tangent coordinates as the Hessian. -/
theorem complexDifferential_monomial_lgCover {n : ℕ} (c : ℂ) (v : Lattice n)
    (ξ V : TangentCoordinates n) :
    complexDifferential (lgManifold n) (monomial c v) (lgCover ξ) (lgCoverTangent ξ V) =
      monomial c v (lgCover ξ) * exponentLinearMap v V := by
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hs : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ) ∞ (monomial c v) :=
    (contMDiff_monomial c v).comp
      (contMDiff_linearRechart_id_symm (M := LGSpace n) (lgEuclideanEquiv n))
  have h := congrArg (fun L : TangentCoordinates n →L[ℝ] ℂ => L V)
    (fderiv_complex_lgCover hs (x := ξ))
  dsimp only [lgCover] at h
  rw [(hasFDerivAt_monomial_representatives c v ξ).fderiv] at h
  exact h.symm

/-- Constant radial coordinates and trivial face characters force the
actual immersion differential into the angular face kernel. -/
theorem faceTorusAmbientMap_tangent_subset {n m : ℕ} (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hsne : s.Nonempty) (hsproper : s ≠ I.vertices) (u : RealSpace n)
    {f : Torus m → Torus n} (hf : ContMDiff (torusModel m) (torusModel n) ∞ f)
    (hrange : range f = coneTorus (positiveCone s))
    (α : Torus m) (ξ : TangentCoordinates n)
    (hpoint : faceTorusAmbientMap u f α = lgCover ξ)
    (W : TorusCoordinates m) (V : TangentCoordinates n)
    (hV : mfderiv (torusModel m) 𝓘(ℝ, Model (2 * n)) (faceTorusAmbientMap u f) α W =
      lgCoverTangent ξ V) :
    V.1 = 0 ∧ faceLevelMap s V.2 = 0 := by
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hk := contMDiff_faceTorusAmbientMap u hf
  have hrad : V.1 = 0 := by
    funext j
    have h := mfderiv_comp_apply α
      ((contMDiff_lgLogCoordinate j).mdifferentiable (by simp) _)
      (hk.mdifferentiable (by simp) α) W
    have hc : (fun y : (lgManifold n).Point => y.1 j) ∘ faceTorusAmbientMap u f =
        fun _ => u j := rfl
    rw [hc, mfderiv_const, zero_apply] at h
    change 0 = lgLogCovector j (faceTorusAmbientMap u f α)
      (mfderiv (torusModel m) 𝓘(ℝ, Model (2 * n)) (faceTorusAmbientMap u f) α W) at h
    rw [hV, hpoint, lgLogCovector_lgCover] at h
    exact h.symm
  refine ⟨hrad, ?_⟩
  funext v
  simp only [faceLevelMap_apply, Pi.zero_apply]
  have hchars (γ : Torus m) : (character v.val (f γ) : ℂ) = 1 :=
    (I.mem_coneTorus_positiveCone_iff hs hsne hsproper (f γ)).mp
      (hrange ▸ mem_range_self γ) v.val v.property
  have hc : monomial (1 : ℂ) v.val ∘ faceTorusAmbientMap u f =
      fun _ => Complex.exp (pairing v.val u) := by
    funext γ
    simp only [Function.comp_apply, faceTorusAmbientMap, monomial, hchars,
      one_mul, mul_one]
  have hsmono : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ) ∞ (monomial (1 : ℂ) v.val) :=
    (contMDiff_monomial 1 v.val).comp
      (contMDiff_linearRechart_id_symm (M := LGSpace n) (lgEuclideanEquiv n))
  have h := mfderiv_comp_apply α (hsmono.mdifferentiable (by simp) _)
    (hk.mdifferentiable (by simp) α) W
  rw [hc, mfderiv_const, zero_apply] at h
  change 0 = complexDifferential (lgManifold n) (monomial 1 v.val)
    (faceTorusAmbientMap u f α)
    (mfderiv (torusModel m) 𝓘(ℝ, Model (2 * n)) (faceTorusAmbientMap u f) α W) at h
  rw [hV, hpoint, complexDifferential_monomial_lgCover,
    exponentLinearMap_eq_pairing, hrad] at h
  have hm : monomial (1 : ℂ) v.val (lgCover ξ) ≠ 0 := by
    rw [← hpoint]
    change (1 : ℂ) * Complex.exp (pairing v.val u) * (character v.val (f α) : ℂ) ≠ 0
    rw [hchars, mul_one, one_mul]
    exact Complex.exp_ne_zero _
  have hz : Complex.I * (pairing v.val V.2 : ℂ) = 0 := by
    have he := (mul_eq_zero.mp h.symm).resolve_left hm
    simpa [pairing] using he
  exact_mod_cast (mul_eq_zero.mp hz).resolve_left Complex.I_ne_zero

/-- The constructed smooth retraction of the angular torus remains a
smooth retraction after adjoining the constant radial coordinate. -/
theorem faceTorusAmbientMap_immersion {n m : ℕ} (u : RealSpace n)
    {f : Torus m → Torus n} {r : Torus n → Torus m}
    (hf : ContMDiff (torusModel m) (torusModel n) ∞ f)
    (hr : ContMDiff (torusModel n) (torusModel m) ∞ r) (hleft : LeftInverse r f)
    (α : Torus m) :
    Injective (mfderiv (torusModel m) 𝓘(ℝ, Model (2 * n)) (faceTorusAmbientMap u f) α) := by
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hsnd : ContMDiff 𝓘(ℝ, Model (2 * n)) (torusModel n) ∞
      (fun y : (lgManifold n).Point => y.2) :=
    (contMDiff_snd : ContMDiff (lgModel n) (torusModel n) ∞ (Prod.snd : LGSpace n → _)).comp
      (contMDiff_linearRechart_id_symm (M := LGSpace n) (lgEuclideanEquiv n))
  have hR : ContMDiff 𝓘(ℝ, Model (2 * n)) (torusModel m) ∞
      (fun y : (lgManifold n).Point => r y.2) := hr.comp hsnd
  have hk := contMDiff_faceTorusAmbientMap u hf
  have he : (fun y : (lgManifold n).Point => r y.2) ∘ faceTorusAmbientMap u f = id :=
    funext hleft
  have hd := mfderiv_comp α (hR.mdifferentiable (by simp) _) (hk.mdifferentiable (by simp) α)
  rw [he, mfderiv_id] at hd
  intro V W hVW
  have h := congrArg (fun L : TorusCoordinates m →L[ℝ] TorusCoordinates m => L V - L W) hd
  change V - W =
    mfderiv 𝓘(ℝ, Model (2 * n)) (torusModel m) (fun y : (lgManifold n).Point => r y.2)
      (faceTorusAmbientMap u f α)
      (mfderiv (torusModel m) 𝓘(ℝ, Model (2 * n)) (faceTorusAmbientMap u f) α V) -
    mfderiv 𝓘(ℝ, Model (2 * n)) (torusModel m) (fun y : (lgManifold n).Point => r y.2)
      (faceTorusAmbientMap u f α)
      (mfderiv (torusModel m) 𝓘(ℝ, Model (2 * n)) (faceTorusAmbientMap u f) α W) at h
  rw [hVW, sub_self] at h
  exact sub_eq_zero.mp h

/-- The actual differential image is exactly the angular face kernel,
using the dimension of the constructed quotient torus and actual immersion. -/
theorem faceTorusAmbientMap_tangent_iff {n : ℕ} (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hsne : s.Nonempty) (hsproper : s ≠ I.vertices) (u : RealSpace n)
    {f : Torus (n - s.card) → Torus n}
    (hf : ContMDiff (torusModel (n - s.card)) (torusModel n) ∞ f)
    (hrange : range f = coneTorus (positiveCone s))
    (α : Torus (n - s.card)) (ξ : TangentCoordinates n)
    (hpoint : faceTorusAmbientMap u f α = lgCover ξ)
    (hinj : Injective
      (mfderiv (torusModel (n - s.card)) 𝓘(ℝ, Model (2 * n)) (faceTorusAmbientMap u f) α))
    (V : TangentCoordinates n) :
    lgCoverTangent ξ V ∈
      (mfderiv (torusModel (n - s.card)) 𝓘(ℝ, Model (2 * n)) (faceTorusAmbientMap u f) α).range ↔
      V.1 = 0 ∧ faceLevelMap s V.2 = 0 := by
  let L : TangentCoordinates n ≃L[ℝ] Model (2 * n) :=
    (LinearEquiv.ofBijective (lgCoverTangent ξ).toLinearMap (lgCoverTangent_bijective ξ)).toContinuousLinearEquiv
  let D : TorusCoordinates (n - s.card) →L[ℝ] TangentCoordinates n :=
    L.symm.toContinuousLinearMap.comp
      (mfderiv (torusModel (n - s.card)) 𝓘(ℝ, Model (2 * n)) (faceTorusAmbientMap u f) α)
  have hD (W : TorusCoordinates (n - s.card)) :
      lgCoverTangent ξ (D W) =
        mfderiv (torusModel (n - s.card)) 𝓘(ℝ, Model (2 * n)) (faceTorusAmbientMap u f) α W :=
    L.apply_symm_apply _
  have hDi : Injective D := L.symm.injective.comp hinj
  have hsub (W : TorusCoordinates (n - s.card)) :
      (D W).1 = 0 ∧ faceLevelMap s (D W).2 = 0 :=
    faceTorusAmbientMap_tangent_subset I hs hsne hsproper u hf hrange α ξ hpoint W (D W) (hD W).symm
  let A : TorusCoordinates (n - s.card) →L[ℝ] (faceLevelMap s).toLinearMap.ker :=
    ((ContinuousLinearMap.snd ℝ (RealSpace n) (RealSpace n)).comp D).codRestrict
      (faceLevelMap s).toLinearMap.ker (fun W => (hsub W).2)
  have hAi : Injective A := by
    intro W Z h
    apply hDi
    apply Prod.ext
    · exact (hsub W).1.trans (hsub Z).1.symm
    · exact congrArg Subtype.val h
  have hdim : Module.finrank ℝ (TorusCoordinates (n - s.card)) =
      Module.finrank ℝ (faceLevelMap s).toLinearMap.ker := by
    rw [face_kernel_finrank (I.faceLevelMap_surjective hs hsne hsproper)]
    simp [TorusCoordinates, AngleModel, Module.finrank_pi_fintype, finrank_euclideanSpace]
  have hAs : Surjective A :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hAi
  constructor
  · rintro ⟨W, hW⟩
    exact faceTorusAmbientMap_tangent_subset I hs hsne hsproper u hf hrange α ξ hpoint W V hW
  · rintro ⟨hV₁, hV₂⟩
    obtain ⟨W, hW⟩ := hAs ⟨V.2, hV₂⟩
    have hDW : D W = V := Prod.ext ((hsub W).1.trans hV₁.symm) (congrArg Subtype.val hW)
    refine ⟨W, ?_⟩
    exact (hD W).symm.trans (congrArg (lgCoverTangent ξ) hDW)

/-- An actual smooth embedded face torus at the prescribed radius, with
its literal range and its full tangent image in every logarithmic lift. -/
theorem ToricInput.exists_faceTorusAmbientMap_exact_tangent {n : ℕ} (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hsne : s.Nonempty) (hsproper : s ≠ I.vertices) (u : RealSpace n) :
    ∃ f : Torus (n - s.card) → Torus n,
      ContMDiff (torusModel (n - s.card)) (torusModel n) ∞ f ∧
      range f = coneTorus (positiveCone s) ∧
      Topology.IsEmbedding (faceTorusAmbientMap u f) ∧
      range (faceTorusAmbientMap u f) =
        {y : (lgManifold n).Point | y.1 = u ∧ y.2 ∈ coneTorus (positiveCone s)} ∧
      (∀ α, Injective
        (mfderiv (torusModel (n - s.card)) 𝓘(ℝ, Model (2 * n)) (faceTorusAmbientMap u f) α)) ∧
      (∀ α ξ, faceTorusAmbientMap u f α = lgCover ξ → ∀ V : TangentCoordinates n,
        lgCoverTangent ξ V ∈
          (mfderiv (torusModel (n - s.card)) 𝓘(ℝ, Model (2 * n)) (faceTorusAmbientMap u f) α).range ↔
          V.1 = 0 ∧ faceLevelMap s V.2 = 0) := by
  obtain ⟨f, r, hf, hr, hleft, _, _, hrange⟩ :=
    I.exists_smooth_coneTorus_parametrization hs hsne hsproper
  have hk := contMDiff_faceTorusAmbientMap u hf
  have hi := faceTorusAmbientMap_immersion u hf hr hleft
  have he : Topology.IsEmbedding (faceTorusAmbientMap u f) :=
    Topology.IsEmbedding.of_leftInverse (fun α => hleft α)
      (hr.continuous.comp continuous_snd) hk.continuous
  refine ⟨f, hf, hrange, he, ?_, hi, ?_⟩
  · ext y
    constructor
    · rintro ⟨α, rfl⟩
      exact ⟨rfl, hrange ▸ mem_range_self α⟩
    · rintro ⟨hu, hθ⟩
      obtain ⟨α, hα⟩ := hrange.symm ▸ hθ
      exact ⟨α, Prod.ext hu.symm hα⟩
  · intro α ξ hpoint V
    exact faceTorusAmbientMap_tangent_iff I hs hsne hsproper u hf hrange α ξ hpoint (hi α) V

/-- The actual chart Hessian radical is the true tangent image of the
constructed face torus, after the actual inverse-chart and inclusion
differentials. No assigned ambient Hessian substitutes for this Hessian. -/
theorem NativeFaceHessianChart.radical_iff_faceTorus_tangent {n d : ℕ} (I : ToricInput n)
    {φ : RealSpace n → ℝ} {s : Finset (Lattice n)}
    (hs : IsPolytopeFace I.vertices s) (hsne : s.Nonempty) (hsproper : s ≠ I.vertices)
    {H : RealSpace n →L[ℝ] RealSpace n} {q : s → ℝ} {lam : ℝ}
    {N : SmoothManifold d} {j : N.SmoothEmbedding (lgManifold n)}
    {a : N.Point} {x : TangentCoordinates n}
    (C : NativeFaceHessianChart φ s H q lam N j a x)
    (u : RealSpace n) {f : Torus (n - s.card) → Torus n}
    (hf : ContMDiff (torusModel (n - s.card)) (torusModel n) ∞ f)
    (hrange : range f = coneTorus (positiveCone s))
    (α : Torus (n - s.card)) (hpoint : faceTorusAmbientMap u f α = lgCover x)
    (hinj : Injective
      (mfderiv (torusModel (n - s.card)) 𝓘(ℝ, Model (2 * n)) (faceTorusAmbientMap u f) α))
    (V : Model d) :
    (∀ W : Model d,
      fderiv ℝ (fderiv ℝ (fun y => φ (j.map ((chartAt (Model d) a).symm y)).1))
        (chartAt (Model d) a a) V W = 0) ↔
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) j.map a
        (N.inverseChartTangentMap a (chartAt (Model d) a a) V) ∈
          (mfderiv (torusModel (n - s.card)) 𝓘(ℝ, Model (2 * n)) (faceTorusAmbientMap u f) α).range := by
  have hd := congrArg (fun L : Model d →L[ℝ] Model (2 * n) => L V)
    (logarithmic_chart_lift_tangent N j a x C.smooth C.center C.cover)
  change lgCoverTangent x (fderiv ℝ C.lift (chartAt (Model d) a a) V) =
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) j.map a
      (N.inverseChartTangentMap a (chartAt (Model d) a a) V) at hd
  exact (C.radical V).trans
    ((faceTorusAmbientMap_tangent_iff I hs hsne hsproper u hf hrange α x hpoint hinj
      (fderiv ℝ C.lift (chartAt (Model d) a a) V)).symm.trans
        (Iff.of_eq (congrArg (fun z : Model (2 * n) => z ∈
          (mfderiv (torusModel (n - s.card)) 𝓘(ℝ, Model (2 * n)) (faceTorusAmbientMap u f) α).range) hd)))

end FsFltz
