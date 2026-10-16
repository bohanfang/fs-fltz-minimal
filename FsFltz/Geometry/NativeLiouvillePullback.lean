import FsFltz.Geometry.IntrinsicPresentationCollarComparison
import FsFltz.Geometry.IntrinsicBundleFormTransport
import FsFltz.Geometry.IntrinsicExteriorNaturality
import FsFltz.Geometry.IntrinsicOutwardSign
import FsFltz.Geometry.IntrinsicExtensionOutward

/-!
# Native Liouville laws under changes of presentation

Source: `geoemtric-part-fsf.tex`, conventions 119–130, `def:chain`,
163–169, and `sec:lean`, 805–814. The original native presentation supplies
a boundaryless primitive extension. Its actual pullback along a varying
native map proves exterior naturality and transports nondegeneracy and the
Liouville field on full tangent spaces, including at boundary points.
No comparison chain or toric geometric existence assertion is made here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- The source presentation's smooth boundaryless primitive proves native
exterior naturality. A derivative-transport certificate is not an input. -/
theorem exteriorDerivative_nativePullbackForm_of_presentation
    {α : Form k M 1} (P : NativeLiouvillePresentation α) (f : M → M)
    (hf : ContMDiff (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) ∞ f) :
    exteriorDerivative (nativePullbackForm f α) =
      nativePullbackForm f (exteriorDerivative α) := by
  let N := P.domain.domain.extension
  let lam := P.domain.liouville.primitive
  have hcomp (x : M) := mfderiv_comp (f := f) (g := P.inclusion) x
    (P.smooth_inclusion.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))
  have hpull : nativePullbackForm f α =
      (fun x => (lam ((P.inclusion ∘ f) x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (P.inclusion ∘ f) x)) := by
    funext x
    unfold nativePullbackForm
    rw [← congrFun P.primitive (f x), hcomp]
    ext vs
    rfl
  rw [hpull, exteriorDerivative_pullback_from_boundaryless N (P.inclusion ∘ f)
    (P.smooth_inclusion.comp hf) lam P.domain.liouville.smooth_primitive]
  funext x
  rw [hcomp]
  have hd := congrFun P.differential (f x)
  ext vs
  exact congrArg (fun omega => omega
    (fun j => mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) f x (vs j))) hd

/-- A bijective full differential transports native symplectic
nondegeneracy from the original Liouville presentation. -/
theorem nondegenerate_nativePullbackForm_of_presentation
    {α : Form k M 1} (P : NativeLiouvillePresentation α) (f : M → M)
    (hf : ContMDiff (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) ∞ f)
    (hbij : ∀ x, Function.Bijective (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) f x))
    (x : M) : Nondegenerate (exteriorDerivative (nativePullbackForm f α)) x := by
  intro v hv
  apply (hbij x).1
  rw [map_zero]
  apply P.native_nondegenerate (f x)
  intro w
  obtain ⟨u, rfl⟩ := (hbij x).2 w
  have hd := congrArg (fun omega => omega ![v, u])
    (congrFun (exteriorDerivative_nativePullbackForm_of_presentation P f hf) x)
  convert hd.symm.trans (hv u) using 1
  apply congrArg (exteriorDerivative α (f x))
  funext j
  fin_cases j <;> rfl

/-- The actual derivative transports the canonical Liouville fields.
Both equations and the native nondegeneracy are proved from the original
presentation and its primitive, rather than a supplied field square. -/
theorem liouvilleVector_nativePullbackForm_of_presentation
    {α : Form k M 1} (P : NativeLiouvillePresentation α) (f : M → M)
    (hf : ContMDiff (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) ∞ f)
    (hbij : ∀ x, Function.Bijective (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) f x))
    (x : M) :
    mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) f x
      (liouvilleVector (nativePullbackForm f α)
        (exteriorDerivative (nativePullbackForm f α)) x) =
      liouvilleVector α (exteriorDerivative α) (f x) := by
  let δ := nativePullbackForm f α
  let A := mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) f x
  let Z := liouvilleVector δ (exteriorDerivative δ) x
  apply sub_eq_zero.mp
  apply P.native_nondegenerate (f x)
  intro v
  obtain ⟨u, rfl⟩ := (hbij x).2 v
  have hd := congrArg (fun omega => omega ![Z, u])
    (congrFun (exteriorDerivative_nativePullbackForm_of_presentation P f hf) x)
  have hZ := contraction_liouvilleVector δ (exteriorDerivative δ)
    (nondegenerate_nativePullbackForm_of_presentation P f hf hbij) x u
  have hpair : exteriorDerivative α (f x) ![A Z, A u] = α (f x) ![A u] := by
    convert hd.symm.trans hZ using 1
    · apply congrArg (exteriorDerivative α (f x))
      funext j
      fin_cases j <;> rfl
    · apply congrArg (α (f x))
      funext j
      fin_cases j
      rfl
  rw [(exteriorDerivative α (f x)).map_vecCons_sub, hpair,
    contraction_liouvilleVector α (exteriorDerivative α) P.native_nondegenerate, sub_self]

/-- Outwardness survives an actual native diffeomorphism. The original
presentation's regular ambient defining function is pulled back only for
its native derivative and sign; the resulting source defining function is
the canonical negative normal coordinate. No extension of the pulled-back
ambient defining function is assumed. -/
theorem outward_nativePullbackForm_of_presentation
    {α : Form k M 1} (P : NativeLiouvillePresentation α)
    (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
    (b : IntrinsicBoundary.Point k M) :
    0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ)
      (normalDefiningFunction (IntrinsicBoundary.chartAt b).ambient) b.val
      (liouvilleVector (nativePullbackForm e α)
        (exteriorDerivative (nativePullbackForm e α)) b.val)) := by
  let i := P.inclusion ∘ e
  let δ := nativePullbackForm e α
  let Z := liouvilleVector δ (exteriorDerivative δ)
  have heb : (𝓡∂ (k + 1)).IsBoundaryPoint (e b.val) := by
    have he := Diffeomorph.preimage_boundary (by simp : (∞ : WithTop ℕ∞) ≠ 0) e
    have hb : b.val ∈ (𝓡∂ (k + 1)).boundary M := b.property
    rw [← he] at hb
    exact hb
  have hfrontier : i b.val ∈ frontier P.domain.domain.carrier :=
    P.frontier_eq_native_boundary ▸ ⟨e b.val, heb, rfl⟩
  let R := P.domain.domain.defining (i b.val) hfrontier
  have hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i :=
    P.smooth_inclusion.comp e.contMDiff
  have hchain (x : M) := mfderiv_comp (f := e) (g := P.inclusion) x
    (P.smooth_inclusion.mdifferentiableAt (by simp)) (e.contMDiff.mdifferentiableAt (by simp))
  have hbij (x : M) : Function.Bijective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x) := by
    rw [hchain]
    exact (P.tangent_bijective (e x)).comp ((e.isInvertible_mfderiv (by simp)).bijective)
  have hfield : mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i b.val (Z b.val) =
      P.domain.liouville.field (i b.val) := by
    rw [hchain]
    change mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) P.inclusion (e b.val)
      (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) e b.val (Z b.val)) = _
    rw [liouvilleVector_nativePullbackForm_of_presentation P e e.contMDiff
      (fun x => (e.isInvertible_mfderiv (by simp)).bijective), ← P.field_inclusion]
    rfl
  have hR : ContMDiffAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) ∞ R.rho (i b.val) :=
    R.smooth_rho.contMDiffAt (R.open_neighbourhood.mem_nhds R.mem_neighbourhood)
  have hzero : (R.rho ∘ i) b.val = 0 :=
    (R.zero_level (i b.val) R.mem_neighbourhood).mp hfrontier
  have hside : ∀ᶠ y in 𝓝 b.val, (R.rho ∘ i) y ≤ 0 := by
    filter_upwards [hi.continuous.continuousAt.preimage_mem_nhds
      (R.open_neighbourhood.mem_nhds R.mem_neighbourhood)] with y hy
    exact (R.sublevel (i y) hy).mp (P.carrier_range ▸ mem_range_self (e y))
  have hρchain := mfderiv_comp (f := i) (g := R.rho) b.val
    (hR.mdifferentiableAt (by simp)) (hi.mdifferentiableAt (by simp))
  have hreg : mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) (R.rho ∘ i) b.val ≠ 0 := by
    intro hz
    apply R.regular
    ext v
    obtain ⟨u, rfl⟩ := (hbij b.val).2 v
    have h := congrArg (fun A => A u) hρchain
    rw [hz] at h
    exact h.symm
  have hpos : 0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ)
      (R.rho ∘ i) b.val (Z b.val)) := by
    rw [hρchain]
    change 0 < (show ℝ from mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) R.rho (i b.val)
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i b.val (Z b.val)))
    rw [hfield]
    exact P.domain.liouville.outward (i b.val) hfrontier
  have hbsource : b.val ∈ (IntrinsicBoundary.chartAt b).ambient.source := by
    have hb := IntrinsicBoundary.mem_chartAt_source b
    rwa [(IntrinsicBoundary.chartAt b).source_eq] at hb
  obtain ⟨c, hc, hformula⟩ := mfderiv_eq_neg_normal_of_mdifferentiable_local_sublevel
    (IntrinsicBoundary.chartAt b).mem_atlas hbsource b.property (R.rho ∘ i)
    ((hR.comp b.val hi.contMDiffAt).mdifferentiableAt (by simp)) hzero hside hreg
  rw [hformula] at hpos
  have hnegative : (show Model (k + 1) from
      chartTangentMap (IntrinsicBoundary.chartAt b).ambient b.val (Z b.val)) 0 < 0 := by
    rcases mul_pos_iff.mp hpos with h | h
    · exact (hc.not_gt h.1).elim
    · exact h.2
  rw [normalDefiningFunction_derivative (IntrinsicBoundary.chartAt b).mem_atlas hbsource]
  exact neg_pos.mpr hnegative

/-- The transported primitive satisfies the original native constructor's
complete local defining-function clause, with actual full smooth germs of
the canonical source defining function. -/
theorem localDefiningFunction_nativePullbackForm_of_presentation
    {α : Form k M 1} (P : NativeLiouvillePresentation α)
    (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
    (b : IntrinsicBoundary.Point k M) :
    ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
      rho b.val = 0 ∧ (∀ᶠ y in 𝓝 b.val, rho y ≤ 0) ∧
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho b.val ≠ 0 ∧
      ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt b).ambient.extend (𝓡∂ (k + 1)) b.val) ∧
      beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt b).ambient.extend (𝓡∂ (k + 1))).target]
        ((IntrinsicBoundary.chartAt b).ambient.extend (𝓡∂ (k + 1)) b.val)]
        (rho ∘ ((IntrinsicBoundary.chartAt b).ambient.extend (𝓡∂ (k + 1))).symm) ∧
      0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho b.val
        (liouvilleVector (nativePullbackForm e α)
          (exteriorDerivative (nativePullbackForm e α)) b.val)) := by
  let a := (IntrinsicBoundary.chartAt b).ambient
  have hbsource : b.val ∈ a.source := by
    have hb := IntrinsicBoundary.mem_chartAt_source b
    rwa [(IntrinsicBoundary.chartAt b).source_eq] at hb
  let rho := normalDefiningFunction a
  let beta : Model (k + 1) → ℝ := fun y => -y 0
  refine ⟨rho, beta,
    (normalDefiningFunction_zero_iff (IntrinsicBoundary.chartAt b).mem_atlas hbsource).mpr b.property,
    Filter.Eventually.of_forall (normalDefiningFunction_nonpos a),
    normalDefiningFunction_regular (IntrinsicBoundary.chartAt b).mem_atlas hbsource, ?_, ?_,
    outward_nativePullbackForm_of_presentation P e b⟩
  · exact ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (k + 1))).contDiff.neg).contDiffAt
  · filter_upwards [self_mem_nhdsWithin] with y hy
    change -y 0 = -(a.extend (𝓡∂ (k + 1)) ((a.extend (𝓡∂ (k + 1))).symm y)) 0
    rw [(a.extend (𝓡∂ (k + 1))).right_inv hy]

end FsFltz.Geometry.IntrinsicLiouville
