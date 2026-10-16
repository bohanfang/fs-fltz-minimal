import FsFltz.Geometry.TailoringNormalGeometry
import FsFltz.Geometry.LogarithmicIntegralCurve

/-!
# Actual transverse defining coordinates over the whole critical torus

Source: `geometric-part-fsf-proof.tex`, `lem:trapping`, lines 1661–1701,
and `lem:stable`, lines 1709–1724. A quotient-defined transverse map is
constructed, with one angular component removed using the fiber equation.
The exact zero set is the actual full-span smooth conormal branch locally.
This is a producer for normal coordinates, not yet a product tubular
neighborhood or a uniform positive expansion estimate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Geometry.SmoothManifold Set Filter Function TopologicalSpace
open scoped Topology BigOperators ContDiff Manifold

variable {n : ℕ}

/-- A complement-valued radial quotient is constructed; the complement and
its projection are conclusions, rather than geometric inputs. -/
theorem exists_surjective_conormalRadialQuotient
    (V : Submodule ℝ (RealSpace n)) :
    ∃ (P : RealSpace n →L[ℝ] V) (Q : RealSpace n →L[ℝ] P.ker),
      LeftInverse P V.subtypeL ∧ Surjective Q ∧
      ∀ x, Q x = 0 ↔ x ∈ V := by
  obtain ⟨P, hP⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional
    (f := V.subtypeL) Subtype.val_injective
  let D : RealSpace n →L[ℝ] RealSpace n :=
    ContinuousLinearMap.id ℝ (RealSpace n) - V.subtypeL.comp P
  have hD (x : RealSpace n) : D x ∈ P.ker := by
    change P (x - (P x : RealSpace n)) = 0
    have hp : P (P x : RealSpace n) = P x := hP (P x)
    rw [map_sub, hp, sub_self]
  let Q : RealSpace n →L[ℝ] P.ker := D.codRestrict P.ker hD
  refine ⟨P, Q, hP, ?_, ?_⟩
  · intro x
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change (x : RealSpace n) - (P x : RealSpace n) = x
    rw [show P x = 0 from x.property]
    simp
  · intro x
    constructor
    · intro hx
      have hd : x - (P x : RealSpace n) = 0 := congrArg Subtype.val hx
      exact sub_eq_zero.mp hd ▸ (P x).property
    · intro hx
      apply Subtype.ext
      change x - (P x : RealSpace n) = 0
      have hp : P x = (⟨x, hx⟩ : V) := hP ⟨x, hx⟩
      rw [hp]
      exact sub_self x

/-- This open quotient neighborhood contains every angle of the face torus. -/
def conormalPositivePhaseNeighborhood (s : Finset (Lattice n)) : Set (LGSpace n) :=
  {y | ∀ v ∈ s, 0 < (monomial 1 v y).re}

/-- One angular coordinate is eliminated by the imaginary fiber equation. -/
def conormalTransverseCoordinates {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : RealSpace n → RealSpace n) (Q : RealSpace n →L[ℝ] E)
    (s : Finset (Lattice n)) (v₀ : Lattice n) (y : LGSpace n) :
    E × (s.erase v₀ → ℝ) :=
  (Q (Φ y.1), fun v => (monomial 1 v.val y).im)

theorem isOpen_conormalPositivePhaseNeighborhood (s : Finset (Lattice n)) :
    IsOpen (conormalPositivePhaseNeighborhood s) := by
  classical
  have he : conormalPositivePhaseNeighborhood s =
      ⋂ v ∈ s, {y : LGSpace n | 0 < (monomial 1 v y).re} := by
    ext y
    simp [conormalPositivePhaseNeighborhood]
  rw [he]
  apply isOpen_biInter_finset
  intro v hv
  exact isOpen_lt continuous_const (Complex.continuous_re.comp
    (contMDiff_monomial 1 v).continuous)

theorem mem_conormalPositivePhaseNeighborhood_of_mem_coneTorus
    (I : ToricInput n) {s : Finset (Lattice n)}
    (hs : IsPolytopeFace I.vertices s) (hsne : s.Nonempty) (hsproper : s ≠ I.vertices)
    (y : LGSpace n) (hθ : y.2 ∈ coneTorus (positiveCone s)) :
    y ∈ conormalPositivePhaseNeighborhood s := by
  intro v hv
  have hc := (I.mem_coneTorus_positiveCone_iff hs hsne hsproper y.2).mp hθ v hv
  simpa only [monomial, one_mul, hc, mul_one, ← Complex.ofReal_exp, Complex.ofReal_re]
    using Real.exp_pos (pairing v y.1)

/-- Positivity selects the unit character one, rather than the other real
unit character. No real-valued angular representative is selected. -/
theorem monomial_im_eq_zero_iff_character_eq_one {v : Lattice n} {y : LGSpace n}
    (hre : 0 < (monomial 1 v y).re) :
    (monomial 1 v y).im = 0 ↔ (character v y.2 : ℂ) = 1 := by
  let z : ℂ := character v y.2
  have hm : monomial 1 v y = (Real.exp (pairing v y.1) : ℂ) * z := by
    simp only [monomial, one_mul, ← Complex.ofReal_exp, z]
  rw [hm] at hre ⊢
  have hexp : 0 < Real.exp (pairing v y.1) := Real.exp_pos _
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero] at hre ⊢
  constructor
  · intro him
    have hi : z.im = 0 := (mul_eq_zero.mp him).resolve_left hexp.ne'
    have hz := Circle.normSq_coe (character v y.2)
    change Complex.normSq z = 1 at hz
    rw [Complex.normSq_apply, hi, mul_zero, add_zero] at hz
    have hr : 0 < z.re := (mul_pos_iff_of_pos_left hexp).mp hre
    have hr1 : z.re = 1 := by nlinarith
    exact Complex.ext hr1 hi
  · intro hz
    simp [z, hz]

theorem conormalTransverseCoordinates_eq_zero_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : ToricInput n) {s : Finset (Lattice n)}
    (hs : IsPolytopeFace I.vertices s) (hsne : s.Nonempty) (hsproper : s ≠ I.vertices)
    (Φ : RealSpace n → RealSpace n) (V : Submodule ℝ (RealSpace n))
    (Q : RealSpace n →L[ℝ] E) (hQ : ∀ x, Q x = 0 ↔ x ∈ V)
    (v₀ : Lattice n) (hv₀ : v₀ ∈ s) (y : LGSpace n)
    (hy : y ∈ conormalPositivePhaseNeighborhood s)
    (c : ℝ) (hc : 0 < c) (hlevel : ∑ v ∈ s, monomial (c : ℂ) v y = 1) :
    conormalTransverseCoordinates Φ Q s v₀ y = 0 ↔
      Φ y.1 ∈ V ∧ y.2 ∈ coneTorus (positiveCone s) := by
  classical
  have hImsum : ∑ v ∈ s, (monomial 1 v y).im = 0 := by
    have he (v : Lattice n) : monomial (c : ℂ) v y = (c : ℂ) * monomial 1 v y := by
      simp only [monomial, one_mul, mul_assoc]
    have h := congrArg Complex.im hlevel
    simp only [Complex.im_sum, he, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, Complex.one_im] at h
    rw [← Finset.mul_sum] at h
    exact (mul_eq_zero.mp h).resolve_left hc.ne'
  constructor
  · intro hzero
    have hrad : Q (Φ y.1) = 0 := congrArg Prod.fst hzero
    have hang : ∀ v ∈ s.erase v₀, (monomial 1 v y).im = 0 := by
      intro v hv
      exact congrFun (congrArg Prod.snd hzero) ⟨v, hv⟩
    have hsum : ∑ v ∈ s.erase v₀, (monomial 1 v y).im = 0 :=
      Finset.sum_eq_zero hang
    have hmissing : (monomial 1 v₀ y).im = 0 := by
      have h := Finset.sum_erase_add s (fun v => (monomial 1 v y).im) hv₀
      rw [hsum, hImsum, zero_add] at h
      exact h
    refine ⟨(hQ _).mp hrad, ?_⟩
    apply (I.mem_coneTorus_positiveCone_iff hs hsne hsproper y.2).mpr
    intro v hv
    apply (monomial_im_eq_zero_iff_character_eq_one (hy v hv)).mp
    by_cases he : v = v₀
    · simpa only [he] using hmissing
    · exact hang v (Finset.mem_erase.mpr ⟨he, hv⟩)
  · rintro ⟨hrad, hθ⟩
    apply Prod.ext
    · exact (hQ _).mpr hrad
    · funext v
      have hv := (Finset.mem_erase.mp v.property).2
      exact (monomial_im_eq_zero_iff_character_eq_one (hy v hv)).mpr
        ((I.mem_coneTorus_positiveCone_iff hs hsne hsproper y.2).mp hθ v hv)

section Differential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contMDiffAt_conormalTransverseCoordinates
    {Φ : RealSpace n → RealSpace n} (Q : RealSpace n →L[ℝ] E)
    (s : Finset (Lattice n)) (v₀ : Lattice n) (y : LGSpace n)
    (hΦ : ContDiffAt ℝ ∞ Φ y.1) :
    ContMDiffAt (lgModel n) 𝓘(ℝ, E × (s.erase v₀ → ℝ)) ∞
      (conormalTransverseCoordinates Φ Q s v₀) y := by
  have hr : ContMDiffAt (lgModel n) 𝓘(ℝ, E) ∞ (fun z : LGSpace n => Q (Φ z.1)) y :=
    Q.contMDiff.contMDiffAt.comp y (hΦ.contMDiffAt.comp y contMDiffAt_fst)
  have ha : ContMDiffAt (lgModel n) 𝓘(ℝ, s.erase v₀ → ℝ) ∞
      (fun z : LGSpace n => fun v : s.erase v₀ => (monomial 1 v.val z).im) y := by
    apply contMDiffAt_pi_space.mpr
    intro v
    exact Complex.imCLM.contMDiff.contMDiffAt.comp y
      (contMDiff_monomial 1 v.val).contMDiffAt
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact hr.prodMk ha

/-- Native smoothness uses the actual recharted quotient atlas. -/
theorem contMDiffAt_conormalTransverseCoordinates_native
    {Φ : RealSpace n → RealSpace n} (Q : RealSpace n →L[ℝ] E)
    (s : Finset (Lattice n)) (v₀ : Lattice n) (y : (lgManifold n).Point)
    (hΦ : ContDiffAt ℝ ∞ Φ y.1) :
    letI : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
    ContMDiffAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, E × (s.erase v₀ → ℝ)) ∞
      (conormalTransverseCoordinates Φ Q s v₀) y := by
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  exact (contMDiffAt_conormalTransverseCoordinates Q s v₀ y hΦ).comp y
    (contMDiff_linearRechart_id_symm (M := LGSpace n) (lgEuclideanEquiv n)).contMDiffAt

/-- The full transverse differential is derived from the literal quotient
monomials; it is not an assigned normal matrix. -/
theorem fderiv_conormalTransverseCoordinates_cover_apply
    {Φ : RealSpace n → RealSpace n} (Q : RealSpace n →L[ℝ] E)
    (s : Finset (Lattice n)) (v₀ : Lattice n) (x V : TangentCoordinates n)
    (hΦ : DifferentiableAt ℝ Φ x.1) :
    fderiv ℝ ((conormalTransverseCoordinates Φ Q s v₀) ∘ lgCover) x V =
      (Q (fderiv ℝ Φ x.1 V.1),
        fun v : s.erase v₀ => (monomial 1 v.val (lgCover x) * exponentLinearMap v.val V).im) := by
  let hr := Q.hasFDerivAt.comp x (hΦ.hasFDerivAt.comp x hasFDerivAt_fst)
  have ha (v : s.erase v₀) := Complex.imCLM.hasFDerivAt.comp x
    (hasFDerivAt_monomial_representatives 1 v.val x)
  have hapi := hasFDerivAt_pi.mpr ha
  have hd := hr.prodMk hapi
  have he := congrArg (fun L => L V) hd.fderiv
  change fderiv ℝ ((conormalTransverseCoordinates Φ Q s v₀) ∘ lgCover) x V =
    (Q (fderiv ℝ Φ x.1 V.1),
      (ContinuousLinearMap.pi fun v : s.erase v₀ =>
        Complex.imCLM.comp (monomial 1 v.val (lgCover x) • exponentLinearMap v.val)) V) at he
  exact he.trans (Prod.ext rfl (by funext v; rfl))

/-- Removing one angular component loses no tangent equation on the fiber. -/
theorem face_retained_weighted_coordinates_eq_zero_iff
    {s : Finset (Lattice n)} (v₀ : s) (q r : s → ℝ)
    (hq : ∀ v, 0 < q v) (hr : ∀ v, 0 < r v)
    (Y : RealSpace n) (hY : Y ∈ faceRealTangent q) :
    (∀ v : s.erase v₀.val, r ⟨v.val, (Finset.mem_erase.mp v.property).2⟩ *
      pairing v.val Y = 0) ↔ faceLevelMap s Y = 0 := by
  classical
  constructor
  · intro hret
    have hz : ∀ v ∈ s.erase v₀.val, pairing v Y = 0 := by
      intro v hv
      exact (mul_eq_zero.mp (hret ⟨v, hv⟩)).resolve_left (hr _).ne'
    have hzero : ∑ v : s, q v * pairing v.val Y = 0 := by
      simpa only [mem_faceRealTangent, faceWeightFunctional_apply,
        faceLevelMap_apply] using hY
    have hmissing : pairing v₀.val Y = 0 := by
      have hsplit := Finset.sum_erase_add s (fun v =>
        faceCoordinateExtend s q v * pairing v Y) v₀.property
      have hsum' : ∑ v ∈ s.erase v₀.val, faceCoordinateExtend s q v * pairing v Y = 0 :=
        Finset.sum_eq_zero (fun v hv => by rw [hz v hv, mul_zero])
      rw [hsum', zero_add, faceCoordinateExtend_apply s q v₀,
        ← Finset.sum_coe_sort s (fun v => faceCoordinateExtend s q v * pairing v Y)] at hsplit
      simp only [faceCoordinateExtend_apply] at hsplit
      rw [hzero] at hsplit
      exact (mul_eq_zero.mp hsplit).resolve_left (hq v₀).ne'
    funext v
    simp only [faceLevelMap_apply, Pi.zero_apply]
    by_cases he : v = v₀
    · simpa only [he] using hmissing
    · exact hz v.val (Finset.mem_erase.mpr ⟨fun h => he (Subtype.ext h), v.property⟩)
  · intro hzero v
    have h := congrFun hzero (⟨v.val, (Finset.mem_erase.mp v.property).2⟩ : s)
    simp only [faceLevelMap_apply, Pi.zero_apply] at h
    rw [h, mul_zero]

end Differential

section NativeDifferential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual constant whole-torus differential of the transverse map. -/
def conormalTransverseLinearMap (Q : RealSpace n →L[ℝ] E)
    (H : RealSpace n →L[ℝ] RealSpace n) (s : Finset (Lattice n))
    (v₀ : Lattice n) (r : s → ℝ) : TangentCoordinates n →L[ℝ] E × (s.erase v₀ → ℝ) :=
  ((Q.comp H).comp (ContinuousLinearMap.fst ℝ _ _)).prod
    (ContinuousLinearMap.pi fun v : s.erase v₀ =>
      (r ⟨v.val, (Finset.mem_erase.mp v.property).2⟩ • pairingCLM v.val).comp
        (ContinuousLinearMap.snd ℝ _ _))

@[simp] theorem conormalTransverseLinearMap_apply (Q : RealSpace n →L[ℝ] E)
    (H : RealSpace n →L[ℝ] RealSpace n) (s : Finset (Lattice n))
    (v₀ : Lattice n) (r : s → ℝ) (V : TangentCoordinates n) :
    conormalTransverseLinearMap Q H s v₀ r V =
      (Q (H V.1), fun v => r ⟨v.val, (Finset.mem_erase.mp v.property).2⟩ * pairing v.val V.2) := by
  apply Prod.ext
  · rfl
  · funext v
    simp [conormalTransverseLinearMap, pairingCLM_apply]

theorem fderiv_conormalTransverseCoordinates_cover_eq
    {Φ : RealSpace n → RealSpace n} (Q : RealSpace n →L[ℝ] E)
    (s : Finset (Lattice n)) (v₀ : Lattice n) (x : TangentCoordinates n)
    (hΦ : DifferentiableAt ℝ Φ x.1) (r : s → ℝ)
    (hmon : ∀ v : s, monomial 1 v.val (lgCover x) = (r v : ℂ)) :
    fderiv ℝ ((conormalTransverseCoordinates Φ Q s v₀) ∘ lgCover) x =
      conormalTransverseLinearMap Q (fderiv ℝ Φ x.1) s v₀ r := by
  apply ContinuousLinearMap.ext
  intro V
  rw [fderiv_conormalTransverseCoordinates_cover_apply Q s v₀ x V hΦ,
    conormalTransverseLinearMap_apply]
  apply Prod.ext
  · rfl
  · funext v
    change (monomial 1 v.val (lgCover x) * exponentLinearMap v.val V).im = _
    rw [hmon ⟨v.val, (Finset.mem_erase.mp v.property).2⟩, exponentLinearMap_eq_pairing]
    simp

/-- The actual native fiber differential factors through the constructed
logarithmic lift and the literal transverse map. -/
theorem NativeFaceHessianChart.transverse_fderiv_eq {d : ℕ}
    {φ : RealSpace n → ℝ} {s : Finset (Lattice n)}
    {H : RealSpace n →L[ℝ] RealSpace n} {q : s → ℝ} {lam : ℝ}
    {N : SmoothManifold d} {j : N.SmoothEmbedding (lgManifold n)}
    {a : N.Point} {x : TangentCoordinates n}
    (C : NativeFaceHessianChart φ s H q lam N j a x)
    {Φ : RealSpace n → RealSpace n} (Q : RealSpace n →L[ℝ] E)
    (v₀ : Lattice n) (hΦ : ContDiffAt ℝ ∞ Φ x.1) (r : s → ℝ)
    (hmon : ∀ v : s, monomial 1 v.val (lgCover x) = (r v : ℂ)) :
    fderiv ℝ (fun y => conormalTransverseCoordinates Φ Q s v₀
      (j.map ((chartAt (Model d) a).symm y))) (chartAt (Model d) a a) =
      (conormalTransverseLinearMap Q (fderiv ℝ Φ x.1) s v₀ r).comp
        (fderiv ℝ C.lift (chartAt (Model d) a a)) := by
  let c := chartAt (Model d) a
  let δ := conormalTransverseCoordinates Φ Q s v₀
  have he : (δ ∘ lgCover) ∘ C.lift =ᶠ[𝓝 (c a)] (fun y => δ (j.map (c.symm y))) :=
    C.cover.mono fun y hy => congrArg δ hy
  have hs : ContDiffAt ℝ ∞ (δ ∘ lgCover) x := by
    let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
    exact ((contMDiffAt_conormalTransverseCoordinates_native Q s v₀ (lgCover x) hΦ).comp x
      (contMDiff_lgCover n).contMDiffAt).contDiffAt
  rw [← he.fderiv_eq, fderiv_comp (c a)
    (C.center.symm ▸ hs.differentiableAt (by simp))
    (C.smooth.differentiableAt (by simp)), C.center,
    fderiv_conormalTransverseCoordinates_cover_eq Q s v₀ x
      (hΦ.differentiableAt (by simp)) r hmon]

/-- The differential's kernel on the true fiber tangent is exactly the
conormal branch tangent. The omitted angular equation is recovered. -/
theorem conormalTransverseLinearMap_eq_zero_iff
    (Q : RealSpace n →L[ℝ] E) (Vₛ : Submodule ℝ (RealSpace n))
    (hQ : ∀ u, Q u = 0 ↔ u ∈ Vₛ)
    (H : RealSpace n →L[ℝ] RealSpace n) (s : Finset (Lattice n))
    (hVₛ : Vₛ = Submodule.span ℝ (positiveCone s)) (v₀ : s) (q r : s → ℝ)
    (hq : ∀ v, 0 < q v) (hr : ∀ v, 0 < r v)
    (W : TangentCoordinates n)
    (hW : W.1 ∈ faceRealTangent q ∧ W.2 ∈ faceRealTangent q) :
    conormalTransverseLinearMap Q H s v₀.val r W = 0 ↔
      W ∈ faceConormalTangent s H q := by
  rw [conormalTransverseLinearMap_apply, Prod.mk_eq_zero,
    mem_faceConormalTangent]
  have hang : (fun v : s.erase v₀.val =>
      r ⟨v.val, (Finset.mem_erase.mp v.property).2⟩ * pairing v.val W.2) = 0 ↔
      faceLevelMap s W.2 = 0 := by
    rw [funext_iff]
    exact face_retained_weighted_coordinates_eq_zero_iff v₀ q r hq hr W.2 hW.2
  rw [hang, hQ, hVₛ]
  exact ⟨fun h => ⟨hW.1, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩

theorem NativeFaceHessianChart.transverse_fderiv_ker_iff {d : ℕ}
    {φ : RealSpace n → ℝ} {s : Finset (Lattice n)}
    {H : RealSpace n →L[ℝ] RealSpace n} {q : s → ℝ} {lam : ℝ}
    {N : SmoothManifold d} {j : N.SmoothEmbedding (lgManifold n)}
    {a : N.Point} {x : TangentCoordinates n}
    (C : NativeFaceHessianChart φ s H q lam N j a x)
    {Φ : RealSpace n → RealSpace n} (Q : RealSpace n →L[ℝ] E)
    (hQ : ∀ u, Q u = 0 ↔ u ∈ Submodule.span ℝ (positiveCone s))
    (v₀ : s) (hΦ : ContDiffAt ℝ ∞ Φ x.1) (hH : H = fderiv ℝ Φ x.1)
    (r : s → ℝ) (hmon : ∀ v : s, monomial 1 v.val (lgCover x) = (r v : ℂ))
    (hq : ∀ v, 0 < q v) (hr : ∀ v, 0 < r v) (w : Model d) :
    fderiv ℝ (fun y => conormalTransverseCoordinates Φ Q s v₀.val
      (j.map ((chartAt (Model d) a).symm y))) (chartAt (Model d) a a) w = 0 ↔
      fderiv ℝ C.lift (chartAt (Model d) a a) w ∈ faceConormalTangent s H q := by
  rw [C.transverse_fderiv_eq Q v₀.val hΦ r hmon, ContinuousLinearMap.comp_apply, ← hH]
  exact conormalTransverseLinearMap_eq_zero_iff Q _ hQ H s rfl v₀ q r hq hr _
    ((C.tangent_range _).mp ⟨w, rfl⟩)

end NativeDifferential

section Submersion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A positive omitted face weight makes the retained angular coordinates
surjective on the actual angular fiber hyperplane. -/
theorem exists_faceRealTangent_retained_coordinates
    {s : Finset (Lattice n)} (hA : Surjective (faceLevelMap s))
    (v₀ : s) (q r : s → ℝ) (hq : ∀ v, 0 < q v) (hr : ∀ v, 0 < r v)
    (b : s.erase v₀.val → ℝ) :
    ∃ Y : RealSpace n, Y ∈ faceRealTangent q ∧
      ∀ v : s.erase v₀.val,
        r ⟨v.val, (Finset.mem_erase.mp v.property).2⟩ * pairing v.val Y = b v := by
  classical
  let e₀ : s → ℝ := Pi.single v₀ 1
  have he₀ : faceWeightFunctional q e₀ = q v₀ := by
    simp [faceWeightFunctional_apply, e₀, Pi.single_apply, mul_ite]
  let a₀ : s → ℝ := fun v => if hv : v.val ≠ v₀.val
    then b ⟨v.val, Finset.mem_erase.mpr ⟨hv, v.property⟩⟩ / r v else 0
  let a : s → ℝ := a₀ - (faceWeightFunctional q a₀ / q v₀) • e₀
  have ha : faceWeightFunctional q a = 0 := by
    simp only [a, map_sub, map_smul, he₀, smul_eq_mul]
    rw [div_mul_cancel₀ _ (hq v₀).ne', sub_self]
  obtain ⟨Y, hY⟩ := hA a
  refine ⟨Y, ?_, ?_⟩
  · rw [mem_faceRealTangent, hY, ha]
  · intro v
    let w : s := ⟨v.val, (Finset.mem_erase.mp v.property).2⟩
    have hw : w ≠ v₀ := fun he => (Finset.mem_erase.mp v.property).1
      (congrArg Subtype.val he)
    have hval : w.val ≠ v₀.val := (Finset.mem_erase.mp v.property).1
    have he : e₀ w = 0 := by simp [e₀, hw]
    have hcoord := congrFun hY w
    simp only [faceLevelMap_apply] at hcoord
    change r w * pairing w.val Y = b v
    rw [hcoord]
    simp only [a, Pi.sub_apply, Pi.smul_apply, he, smul_eq_mul, mul_zero, sub_zero,
      a₀, dite_eq_left hval]
    exact mul_div_cancel₀ _ (hr w).ne'

/-- The actual face lift corrects the radial level equation without changing
the transverse radial target. Both normal-coordinate blocks are attained. -/
theorem conormalTransverseLinearMap_surjective_on_fiber
    (Q : RealSpace n →L[ℝ] E) (hQsurj : Surjective Q)
    (H : RealSpace n →L[ℝ] RealSpace n) (hHsurj : Surjective H)
    (s : Finset (Lattice n)) (v₀ : s) (q r : s → ℝ)
    (hq : ∀ v, 0 < q v) (hr : ∀ v, 0 < r v)
    (hQ : ∀ u, Q u = 0 ↔ u ∈ Submodule.span ℝ (positiveCone s))
    (hA : Surjective (faceLevelMap s))
    (B : (s → ℝ) →L[ℝ] RealSpace n) (R : (s → ℝ) →L[ℝ] (s → ℝ))
    (hB : (faceLevelMap s).comp B = ContinuousLinearMap.id ℝ (s → ℝ))
    (hnormal : H.comp B = (faceNormalMap s).comp R)
    (z : E × (s.erase v₀.val → ℝ)) :
    ∃ W : TangentCoordinates n,
      W.1 ∈ faceRealTangent q ∧ W.2 ∈ faceRealTangent q ∧
      conormalTransverseLinearMap Q H s v₀.val r W = z := by
  classical
  let e₀ : s → ℝ := Pi.single v₀ 1
  have he₀ : faceWeightFunctional q e₀ = q v₀ := by
    simp [faceWeightFunctional_apply, e₀, Pi.single_apply, mul_ite]
  have hright (a : s → ℝ) : faceLevelMap s (B a) = a :=
    congrArg (fun L : (s → ℝ) →L[ℝ] (s → ℝ) => L a) hB
  have hQB : Q (H (B e₀)) = 0 := by
    apply (hQ _).mpr
    rw [← faceNormalMap_range_eq_span_positiveCone]
    refine ⟨R e₀, ?_⟩
    exact (congrArg (fun L : (s → ℝ) →L[ℝ] RealSpace n => L e₀) hnormal).symm
  obtain ⟨u, hu⟩ := hQsurj z.1
  obtain ⟨X₀, hX₀⟩ := hHsurj u
  let X := X₀ - (faceWeightFunctional q (faceLevelMap s X₀) / q v₀) • B e₀
  have hX : X ∈ faceRealTangent q := by
    rw [mem_faceRealTangent]
    simp only [X, map_sub, map_smul, hright, he₀, smul_eq_mul]
    rw [div_mul_cancel₀ _ (hq v₀).ne', sub_self]
  have hQX : Q (H X) = z.1 := by
    simp only [X, map_sub, map_smul, hQB, smul_zero, sub_zero, hX₀, hu]
  obtain ⟨Y, hY, hangular⟩ := exists_faceRealTangent_retained_coordinates hA v₀ q r hq hr z.2
  refine ⟨(X, Y), hX, hY, ?_⟩
  rw [conormalTransverseLinearMap_apply]
  apply Prod.ext hQX
  exact funext hangular

theorem NativeFaceHessianChart.transverse_fderiv_surjective {d : ℕ}
    {φ : RealSpace n → ℝ} {s : Finset (Lattice n)}
    {H : RealSpace n →L[ℝ] RealSpace n} {q : s → ℝ} {lam : ℝ}
    {N : SmoothManifold d} {j : N.SmoothEmbedding (lgManifold n)}
    {a : N.Point} {x : TangentCoordinates n}
    (C : NativeFaceHessianChart φ s H q lam N j a x)
    {Φ : RealSpace n → RealSpace n} (Q : RealSpace n →L[ℝ] E)
    (hQsurj : Surjective Q) (hHsurj : Surjective H)
    (hQ : ∀ u, Q u = 0 ↔ u ∈ Submodule.span ℝ (positiveCone s))
    (v₀ : s) (hΦ : ContDiffAt ℝ ∞ Φ x.1) (hH : H = fderiv ℝ Φ x.1)
    (r : s → ℝ) (hmon : ∀ v : s, monomial 1 v.val (lgCover x) = (r v : ℂ))
    (hq : ∀ v, 0 < q v) (hr : ∀ v, 0 < r v)
    (hA : Surjective (faceLevelMap s))
    (B : (s → ℝ) →L[ℝ] RealSpace n) (R : (s → ℝ) →L[ℝ] (s → ℝ))
    (hB : (faceLevelMap s).comp B = ContinuousLinearMap.id ℝ (s → ℝ))
    (hnormal : H.comp B = (faceNormalMap s).comp R) :
    Surjective (fderiv ℝ (fun y => conormalTransverseCoordinates Φ Q s v₀.val
      (j.map ((chartAt (Model d) a).symm y))) (chartAt (Model d) a a)) := by
  rw [C.transverse_fderiv_eq Q v₀.val hΦ r hmon, ← hH]
  intro z
  obtain ⟨W, hW₁, hW₂, hW⟩ := conormalTransverseLinearMap_surjective_on_fiber
    Q hQsurj H hHsurj s v₀ q r hq hr hQ hA B R hB hnormal z
  obtain ⟨w, hw⟩ := (C.tangent_range W).mpr ⟨hW₁, hW₂⟩
  refine ⟨w, ?_⟩
  exact (congrArg (conormalTransverseLinearMap Q H s v₀.val r) hw).trans hW

end Submersion

section NativeOrbit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The transverse rate is obtained by differentiating the actual native
map against the actual Liouville vector. -/
def conormalTransverseRate {d : ℕ} (N : SmoothManifold d)
    (j : N.SmoothEmbedding (lgManifold n)) (μ : N.Form 1)
    (Φ : RealSpace n → RealSpace n) (Q : RealSpace n →L[ℝ] E)
    (s : Finset (Lattice n)) (v₀ : Lattice n) (a : N.Point) : E × (s.erase v₀ → ℝ) :=
  mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, E × (s.erase v₀ → ℝ))
    ((conormalTransverseCoordinates Φ Q s v₀) ∘ j.map) a (N.liouvilleVector μ a)

theorem hasDerivAt_conormalTransverseCoordinates_native_orbit {d : ℕ}
    (N : SmoothManifold d) (j : N.SmoothEmbedding (lgManifold n)) (μ : N.Form 1)
    {Φ : RealSpace n → RealSpace n} (Q : RealSpace n →L[ℝ] E)
    (s : Finset (Lattice n)) (v₀ : Lattice n)
    {γ : ℝ → N.Point} {t : ℝ}
    (hγ : IsMIntegralCurveAt γ (N.liouvilleVector μ) t)
    (hΦ : ContDiffAt ℝ ∞ Φ (j.map (γ t)).1) :
    HasDerivAt (fun τ => conormalTransverseCoordinates Φ Q s v₀ (j.map (γ τ)))
      (conormalTransverseRate N j μ Φ Q s v₀ (γ t)) t := by
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hδ := (contMDiffAt_conormalTransverseCoordinates_native Q s v₀
    (j.map (γ t)) hΦ).comp (γ t) j.map.contMDiff.contMDiffAt
  have hd := (hδ.mdifferentiableAt (by simp)).hasMFDerivAt.comp t hγ.self_of_nhds
  have hd' : HasFDerivAt
      (fun τ => conormalTransverseCoordinates Φ Q s v₀ (j.map (γ τ)))
      ((mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, E × (s.erase v₀ → ℝ))
        ((conormalTransverseCoordinates Φ Q s v₀) ∘ j.map) (γ t)).comp
          (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
            (N.liouvilleVector μ (γ t)))) t := hd.hasFDerivAt
  apply hd'.hasDerivAt.congr_deriv
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, E × (s.erase v₀ → ℝ))
    ((conormalTransverseCoordinates Φ Q s v₀) ∘ j.map) (γ t)
      ((1 : ℝ) • N.liouvilleVector μ (γ t)) = _
  rw [one_smul]
  rfl

end NativeOrbit

end FsFltz
