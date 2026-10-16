import FsFltz.Geometry.TailoringRoundedFamily
import FsFltz.Geometry.TailoringHorizontalGluing

/-!
# Compatible native lifts for rounded tailoring pairs

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 975–1009,
and `eq:normalizedrounding`, lines 1254–1282. The strict truncation gap
produces an actual unrounded germ along the entire ribbon. Consequently
its two fiber equations imply the literal ambient boundary equation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology Bundle
open Set Filter

namespace FsFltz
open Geometry
variable {n : ℕ}

namespace Geometry

/-- The two components of a native parameter-and-level lift. -/
theorem parameter_level_horizontal_components
    {E F Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace Q] [ChartedSpace E Q]
    {τ : Q → ℝ} {f : Q → F} {x : Q}
    (hτ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) τ x)
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) f x)
    (v : TangentSpace 𝓘(ℝ, E) x)
    (hv : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ × F) (fun q => (τ q, f q)) x v = (1, 0)) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) τ x v = (1 : ℝ) ∧
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x v = 0 := by
  have hp : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × F) (fun q => (τ q, f q)) x
      ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) τ x).prod
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x)) :=
    ⟨hτ.continuousAt.prodMk hf.continuousAt,
      hτ.hasMFDerivAt.2.prodMk hf.hasMFDerivAt.2⟩
  rw [hp.mfderiv] at hv
  exact ⟨congrArg Prod.fst hv, congrArg Prod.snd hv⟩

end Geometry

local instance roundedMarkedLGCharts : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
local instance roundedMarkedLGSmooth : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth
local instance roundedMarkedProdCharts : ChartedSpace (ℝ × Model (2 * n)) (ℝ × LGSpace n) :=
  inferInstanceAs (ChartedSpace (ModelProd ℝ (Model (2 * n))) (ℝ × LGSpace n))
local instance roundedMarkedProdSmooth : IsManifold 𝓘(ℝ, ℝ × Model (2 * n)) ∞ (ℝ × LGSpace n) := by
  rw [modelWithCornersSelf_prod]
  exact inferInstanceAs
    (IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) ∞ (ℝ × LGSpace n))

/-- A strict gap from the potential face gives an actual open germ of
the normalized base face near every point of the full truncated fiber. -/
theorem tailoringRoundedDefiningFunction_exists_unrounded_germ
    (I : ToricInput n) {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (β R A Aminus : ℝ) (m : RoundingChoice) (heps : 0 < m.eps)
    (hgap : Aminus < A - m.eps) (s : ℝ) (y : LGSpace n)
    (hf : tailoringFamily I β s y = 1) (hy : φ y.1 ≤ Aminus) :
    ∃ O : Set (ℝ × LGSpace n), IsOpen O ∧ (s, y) ∈ O ∧
      ∀ p ∈ O, tailoringRoundedDefiningFunction I φ β p.1 R A m p.2 =
        R ^ 2 * (Complex.normSq (tailoringFamily I β p.1 p.2) - 1) := by
  let x : ℝ × LGSpace n → ℝ := fun p => φ p.2.1 - A
  let z : ℝ × LGSpace n → ℝ :=
    fun p => R ^ 2 * (Complex.normSq (tailoringFamily I β p.1 p.2) - 1)
  have hx : Continuous x :=
    ((contMDiff_potentialValue hφ).continuous.comp continuous_snd).sub continuous_const
  have hz : Continuous z := by
    apply continuous_const.mul
    exact (Complex.continuous_normSq.comp
      (contMDiff_tailoringFamily_native_joint I β).continuous).sub continuous_const
  let O : Set (ℝ × LGSpace n) := {p | m.eps < z p - x p}
  have hO : IsOpen O := isOpen_lt continuous_const (hz.sub hx)
  refine ⟨O, hO, ?_, ?_⟩
  · change m.eps < R ^ 2 * (Complex.normSq (tailoringFamily I β s y) - 1) - (φ y.1 - A)
    simp only [hf, Complex.normSq_one, sub_self, mul_zero, zero_sub]
    linarith
  · intro p hp
    change m.eps < z p - x p at hp
    have hle : x p ≤ z p := by linarith
    have hexact := m.profile.exact_away (x p, z p) (by
      rw [abs_of_nonpos (sub_nonpos.mpr hle)]
      linarith)
    exact hexact.trans (max_eq_right hle)

/-- Every point of the literal full truncated fiber belongs to the
unchanged rounded zero face. This includes rank-one fibers. -/
theorem tailoringRoundedDefiningFunction_eq_zero_on_truncated_fiber
    (I : ToricInput n) {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (β R A Aminus : ℝ) (m : RoundingChoice) (heps : 0 < m.eps)
    (hgap : Aminus < A - m.eps) (s : ℝ) (y : LGSpace n)
    (hf : tailoringFamily I β s y = 1) (hy : φ y.1 ≤ Aminus) :
    tailoringRoundedDefiningFunction I φ β s R A m y = 0 := by
  obtain ⟨O, _hO, hp, hbase⟩ := tailoringRoundedDefiningFunction_exists_unrounded_germ
    I hφ β R A Aminus m heps hgap s y hf hy
  simpa only [hf, Complex.normSq_one, sub_self, mul_zero] using hbase (s, y) hp

/-- On the actual unrounded germ, a parameter-and-fiber horizontal field
automatically solves the rounded ambient boundary equation. -/
theorem tailoringRounded_derivative_zero_of_fiber_horizontal
    (I : ToricInput n) (φ : RealSpace n → ℝ) (β R A : ℝ) (m : RoundingChoice)
    (O : Set (ℝ × LGSpace n)) (hO : IsOpen O)
    (hbase : ∀ p ∈ O, tailoringRoundedDefiningFunction I φ β p.1 R A m p.2 =
      R ^ 2 * (Complex.normSq (tailoringFamily I β p.1 p.2) - 1))
    (p : ℝ × LGSpace n) (hp : p ∈ O)
    (v : TangentSpace 𝓘(ℝ, ℝ × Model (2 * n)) p)
    (hv : mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ × ℂ)
      (fun q : ℝ × LGSpace n => (q.1, tailoringFamily I β q.1 q.2)) p v = (1, 0)) :
    mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ)
      (fun q : ℝ × LGSpace n => tailoringRoundedDefiningFunction I φ β q.1 R A m q.2) p v = 0 := by
  have hτ : MDifferentiableAt 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ)
      (Prod.fst : ℝ × LGSpace n → ℝ) p := by
    rw [modelWithCornersSelf_prod]
    exact (contMDiff_fst (n := ∞)).mdifferentiableAt (by simp)
  have hf : MDifferentiableAt 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℂ)
      (fun q : ℝ × LGSpace n => tailoringFamily I β q.1 q.2) p := by
    rw [modelWithCornersSelf_prod]
    exact (contMDiff_tailoringFamily_native_joint I β).mdifferentiableAt (by simp)
  have hpair : HasMFDerivAt 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ × ℂ)
      (fun q : ℝ × LGSpace n => (q.1, tailoringFamily I β q.1 q.2)) p
      ((mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) Prod.fst p).prod
        (mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℂ)
          (fun q : ℝ × LGSpace n => tailoringFamily I β q.1 q.2) p)) := by
    exact ⟨hτ.continuousAt.prodMk hf.continuousAt,
      hτ.hasMFDerivAt.2.prodMk hf.hasMFDerivAt.2⟩
  have hdf : mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℂ)
      (fun q : ℝ × LGSpace n => tailoringFamily I β q.1 q.2) p v = 0 := by
    rw [hpair.mfderiv] at hv
    exact congrArg Prod.snd hv
  have hn : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (fun z : ℂ => ‖z‖ ^ 2)
      (tailoringFamily I β p.1 p.2) :=
    (contDiff_norm_sq ℝ (n := ∞)).contMDiff.mdifferentiableAt (by simp)
  have hnorm := hn.hasMFDerivAt.comp p hf.hasMFDerivAt
  have hscale := (hnorm.sub (hasMFDerivAt_const (c := (1 : ℝ)) p)).const_smul (R ^ 2)
  have hagree : (fun q : ℝ × LGSpace n => tailoringRoundedDefiningFunction I φ β q.1 R A m q.2)
      =ᶠ[𝓝 p] (fun q : ℝ × LGSpace n => R ^ 2 * (Complex.normSq (tailoringFamily I β q.1 q.2) - 1)) := by
    filter_upwards [hO.mem_nhds hp] with q hq
    exact hbase q hq
  rw [hagree.mfderiv_eq]
  change mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ)
    (fun q : ℝ × LGSpace n => R ^ 2 * (Complex.normSq (tailoringFamily I β q.1 q.2) - 1)) p v = 0
  rw [show (fun q : ℝ × LGSpace n => R ^ 2 * (Complex.normSq (tailoringFamily I β q.1 q.2) - 1)) =
    (fun q : ℝ × LGSpace n => R ^ 2 * (‖tailoringFamily I β q.1 q.2‖ ^ 2 - 1)) from by
      funext q; rw [Complex.normSq_eq_norm_sq]]
  change mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ)
    (fun q : ℝ × LGSpace n => R ^ 2 * (‖tailoringFamily I β q.1 q.2‖ ^ 2 - 1)) p v = 0
  erw [hscale.mfderiv]
  change R ^ 2 • ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (fun z : ℂ => ‖z‖ ^ 2)
    (tailoringFamily I β p.1 p.2))
    (mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℂ)
      (fun q : ℝ × LGSpace n => tailoringFamily I β q.1 q.2) p v) - 0) = 0
  rw [hdf, map_zero, sub_self, smul_zero]

/-- One constructed native field on the actual compact rounded pair family,
with open differential collars for all three marked boundaries. Ambient
regularity is produced by the finite-input Liouville estimate; no local
lift, compatibility certificate, or trivialization is an input. -/
theorem tailoringFamily_exists_uniform_rounded_marked_horizontalField
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    ∃ F : ℝ, 0 < F ∧ ∀ D : ℝ, F < D →
      ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      ∀ R : ℝ, 0 < R →
      ∀ Aminus : ℝ, F ^ 2 * β ^ 2 / 2 ≤ Aminus → Aminus < D ^ 2 * β ^ 2 / 2 →
      ∃ δ : ℝ, 0 < δ ∧ δ < D ^ 2 * β ^ 2 / 2 - Aminus ∧
      ∀ m : RoundingChoice, 0 < m.eps → m.eps ≤ δ →
      ∃ (O Bambient Bribbon Bfrontier : Set (ℝ × LGSpace n))
        (V : (p : ℝ × LGSpace n) → TangentSpace 𝓘(ℝ, ℝ × Model (2 * n)) p),
        IsOpen O ∧
        {p : ℝ × LGSpace n | p.1 ∈ Icc (0 : ℝ) 1 ∧
          p.2 ∈ tailoringRoundedDomain I φ β p.1 R (D ^ 2 * β ^ 2 / 2) m} ⊆ O ∧
        IsOpen Bambient ∧
        {p : ℝ × LGSpace n | p.1 ∈ Icc (0 : ℝ) 1 ∧
          tailoringRoundedDefiningFunction I φ β p.1 R (D ^ 2 * β ^ 2 / 2) m p.2 = 0} ⊆ Bambient ∧
        IsOpen Bribbon ∧
        {p : ℝ × LGSpace n | p.1 ∈ Icc (0 : ℝ) 1 ∧
          tailoringFamily I β p.1 p.2 = 1 ∧ φ p.2.1 ≤ Aminus} ⊆ Bribbon ∧
        IsOpen Bfrontier ∧
        {p : ℝ × LGSpace n | p.1 ∈ Icc (0 : ℝ) 1 ∧
          tailoringFamily I β p.1 p.2 = 1 ∧ φ p.2.1 = Aminus} ⊆ Bfrontier ∧
        ContMDiff 𝓘(ℝ, ℝ × Model (2 * n))
          (𝓘(ℝ, ℝ × Model (2 * n))).tangent ∞
          (fun p => (⟨p, V p⟩ : TangentBundle 𝓘(ℝ, ℝ × Model (2 * n)) (ℝ × LGSpace n))) ∧
        (∀ p ∈ O, mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ)
          (Prod.fst : ℝ × LGSpace n → ℝ) p (V p) = (1 : ℝ)) ∧
        (∀ p ∈ O ∩ Bambient, mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ)
          (fun q : ℝ × LGSpace n => tailoringRoundedDefiningFunction I φ β q.1 R
            (D ^ 2 * β ^ 2 / 2) m q.2) p (V p) = 0) ∧
        (∀ p ∈ O ∩ Bribbon, mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ × ℂ)
          (fun q : ℝ × LGSpace n => (q.1, tailoringFamily I β q.1 q.2)) p (V p) = (1, 0)) ∧
        ∀ p ∈ O ∩ Bfrontier, mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ)
          (fun q : ℝ × LGSpace n => φ q.2.1) p (V p) = 0 := by
  classical
  obtain ⟨F, hF, Bf, hBf, hribbon⟩ := tailoringFamily_exists_uniform_compact_horizontalField
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend
  refine ⟨F, hF, ?_⟩
  intro D hFD
  have hD : 0 < D := hF.trans hFD
  obtain ⟨Bq, hBq, hout⟩ := tailoringFamily_exists_uniform_rounded_outwardness
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend hD
  refine ⟨max Bf Bq, hBf.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  obtain ⟨Kstar, hKstar, hout⟩ := hout β ((le_max_right _ _).trans hβ)
  intro R hR Aminus hAminus hA
  obtain ⟨δ, hδ, hδgap, hout⟩ := hout R hR Aminus hA
  refine ⟨δ, hδ, hδgap, ?_⟩
  intro m hm hmd
  let A := D ^ 2 * β ^ 2 / 2
  let τ : ℝ × LGSpace n → ℝ := Prod.fst
  let f : ℝ × LGSpace n → ℂ := fun p => tailoringFamily I β p.1 p.2
  let ψ : ℝ × LGSpace n → ℝ := fun p => φ p.2.1
  let q : ℝ × LGSpace n → ℝ := fun p => tailoringRoundedDefiningFunction I φ β p.1 R A m p.2
  let C : Set (ℝ × LGSpace n) := {p | p.1 ∈ Icc (0 : ℝ) 1 ∧ q p ≤ 0}
  let Cr : Set (ℝ × LGSpace n) := {p | p.1 ∈ Icc (0 : ℝ) 1 ∧ f p = 1 ∧ ψ p ≤ Aminus}
  let Cb : Set (ℝ × LGSpace n) := C ∩ {p | q p = 0}
  let Cf : Set (ℝ × LGSpace n) := Cr ∩ {p | ψ p = Aminus}
  have hτ : ContMDiff 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) ∞ τ := by
    rw [modelWithCornersSelf_prod]; exact contMDiff_fst
  have hf : ContMDiff 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℂ) ∞ f := by
    rw [modelWithCornersSelf_prod]; exact contMDiff_tailoringFamily_native_joint I β
  have hψ : ContMDiff 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) ∞ ψ := by
    rw [modelWithCornersSelf_prod]; exact (contMDiff_potentialValue hφ).comp contMDiff_snd
  have hq : ContMDiff 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) ∞ q := by
    rw [modelWithCornersSelf_prod]; exact contMDiff_tailoringRoundedDefiningFunction_joint I hφ β R A m
  have hC : IsCompact C := isCompact_tailoringRoundedDomain_totalSpace I hφ hEnd1 hEnd
    hhom hc hlower hL hend β R A m
  have hCr : IsCompact Cr := isCompact_tailoringFamily_truncatedTotalSpace
    hφ hEnd1 hEnd hhom hc hlower hL hend I β Aminus
  have hCb : IsCompact Cb := hC.inter_right (isClosed_eq hq.continuous continuous_const)
  have hCf : IsCompact Cf := hCr.inter_right (isClosed_eq hψ.continuous continuous_const)
  obtain ⟨Or, Bf, Vr, hOr, hCrOr, hBf, hCfBf, hVr, hrf, hrψ⟩ :=
    hribbon β ((le_max_left _ _).trans hβ) Aminus hAminus
  let Ubase : Set (ℝ × LGSpace n) :=
    {p | m.eps < R ^ 2 * (Complex.normSq (f p) - 1) - (ψ p - A)}
  have hUbase : IsOpen Ubase := isOpen_lt continuous_const
    ((continuous_const.mul ((Complex.continuous_normSq.comp hf.continuous).sub continuous_const)).sub
      (hψ.continuous.sub continuous_const))
  have hCrbase : Cr ⊆ Ubase := by
    intro p hp
    change m.eps < R ^ 2 * (Complex.normSq (f p) - 1) - (ψ p - A)
    simp only [hp.2.1, Complex.normSq_one, sub_self, mul_zero, zero_sub]
    have := hp.2.2
    change δ < A - Aminus at hδgap
    linarith
  have hbase : ∀ p ∈ Ubase, q p = R ^ 2 * (Complex.normSq (f p) - 1) := by
    intro p hp
    have hle : ψ p - A ≤ R ^ 2 * (Complex.normSq (f p) - 1) := by
      change m.eps < R ^ 2 * (Complex.normSq (f p) - 1) - (ψ p - A) at hp
      linarith
    exact (m.profile.exact_away _ (by
      rw [abs_of_nonpos (sub_nonpos.mpr hle)]
      change m.eps ≤ -(ψ p - A - R ^ 2 * (Complex.normSq (f p) - 1))
      change m.eps < R ^ 2 * (Complex.normSq (f p) - 1) - (ψ p - A) at hp
      linarith)).trans (max_eq_right hle)
  obtain ⟨Br, hBr, hCrBr, hBrsub⟩ := normal_exists_closure_subset hCr.isClosed
    (hOr.inter hUbase) (fun p hp => ⟨hCrOr hp, hCrbase hp⟩)
  have hCfBrBf : Cf ⊆ Br ∩ Bf := by
    intro p hp
    exact ⟨hCrBr hp.1, hCfBf ⟨hp.1.1, hp.1.2.1, hp.2⟩⟩
  obtain ⟨Bfront, hBfront, hCfBfront, hBfrontsub⟩ := normal_exists_closure_subset
    hCf.isClosed (hBr.inter hBf) hCfBrBf
  have hboundary : ∀ a ∈ Cb, ∃ (P : Set (ℝ × LGSpace n))
      (Z : (p : ℝ × LGSpace n) → TangentSpace 𝓘(ℝ, ℝ × Model (2 * n)) p),
      IsOpen P ∧ a ∈ P ∧
      ContMDiffOn 𝓘(ℝ, ℝ × Model (2 * n)) (𝓘(ℝ, ℝ × Model (2 * n))).tangent ∞
        (fun p => (⟨p, Z p⟩ : TangentBundle 𝓘(ℝ, ℝ × Model (2 * n)) (ℝ × LGSpace n))) P ∧
      ∀ p ∈ P, mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ × ℝ)
        (fun z => (τ z, q z)) p (Z p) = (1, 0) := by
    intro a ha
    have hpot := (tailoringRoundedDomain_subset I φ β a.1 A hR m ha.1.2).1
    have hpos := hout m hm hmd Kstar le_rfl a.1 ha.1.1 a.2 hpot ha.2.ge
    have hreg : mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ)
        (tailoringRoundedDefiningFunction I φ β a.1 R A m) a.2 ≠ 0 := by
      intro hz
      have hzero : (lgManifold n).scalarDerivative
          (tailoringRoundedDefiningFunction I φ β a.1 R A m) a.2
          ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
            (lambdaPotentialForm φ) (tailoringFamily I β a.1) Kstar) a.2) = 0 := by
        change (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) _ a.2) _ = 0
        rw [hz]; rfl
      rw [hzero] at hpos
      exact (lt_irrefl 0) hpos
    have hsurj : Function.Surjective (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ)
        (tailoringRoundedDefiningFunction I φ β a.1 R A m) a.2) := by
      apply LinearMap.surjective (f := (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ)
        (tailoringRoundedDefiningFunction I φ β a.1 R A m) a.2).toLinearMap)
      intro hz
      exact hreg (ContinuousLinearMap.coe_injective hz)
    exact exists_parameter_level_horizontalField
      (contMDiff_tailoringRoundedDefiningFunction_joint I hφ β R A m) hsurj
  choose W Z hW haW hZ heq using (fun a : Cb => hboundary a a.property)
  let Uq : Set (ℝ × LGSpace n) := ⋃ a : Cb, W a
  have hUq : IsOpen Uq := isOpen_iUnion hW
  have hCbUq : Cb ⊆ Uq := fun a ha => mem_iUnion_of_mem ⟨a, ha⟩ (haW ⟨a, ha⟩)
  obtain ⟨Bambient, hBambient, hCbBambient, hBambientsub⟩ :=
    normal_exists_closure_subset hCb.isClosed hUq hCbUq
  let S : Fin 4 → Set (ℝ × LGSpace n) := ![univ, closure Bambient, closure Br, closure Bfront]
  let L : Fin 4 → (p : ℝ × LGSpace n) →
      TangentSpace 𝓘(ℝ, ℝ × Model (2 * n)) p →L[ℝ] ℝ × (ℂ × ℝ) := fun j p =>
    ![(mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) τ p).prod 0,
      (mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) τ p).prod
        ((0 : TangentSpace 𝓘(ℝ, ℝ × Model (2 * n)) p →L[ℝ] ℂ).prod
          (mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) q p)),
      (mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) τ p).prod
        ((mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℂ) f p).prod 0),
      (mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) τ p).prod
        ((mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℂ) f p).prod
          (mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) ψ p))] j
  have hlocal : ∀ a ∈ C, ∃ (P : Set (ℝ × LGSpace n))
      (V : (p : ℝ × LGSpace n) → TangentSpace 𝓘(ℝ, ℝ × Model (2 * n)) p),
      IsOpen P ∧ a ∈ P ∧
      ContMDiffOn 𝓘(ℝ, ℝ × Model (2 * n)) (𝓘(ℝ, ℝ × Model (2 * n))).tangent ∞
        (fun p => (⟨p, V p⟩ : TangentBundle 𝓘(ℝ, ℝ × Model (2 * n)) (ℝ × LGSpace n))) P ∧
      ∀ j p, p ∈ P → p ∈ S j → L j p (V p) = (1, 0) := by
    intro a _ha
    by_cases har : a ∈ closure Br
    · refine ⟨Or ∩ Ubase, Vr, hOr.inter hUbase, hBrsub har,
        hVr.contMDiffOn.mono inter_subset_left, ?_⟩
      intro j p hp hs
      have hcomp := parameter_level_horizontal_components
        (hτ.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp)) (Vr p) (hrf p hp.1)
      have hqr := tailoringRounded_derivative_zero_of_fiber_horizontal I φ β R A m
        Ubase hUbase hbase p hp.2 (Vr p) (hrf p hp.1)
      fin_cases j
      · change (_, (0, 0)) = ((1 : ℝ), (0 : ℂ), (0 : ℝ)); erw [hcomp.1]
      · change (_, (0, _)) = ((1 : ℝ), (0 : ℂ), (0 : ℝ)); erw [hcomp.1, hqr]
      · change (_, (_, 0)) = ((1 : ℝ), (0 : ℂ), (0 : ℝ)); erw [hcomp.1, hcomp.2]
      · have hpBf := (hBfrontsub hs).2
        have hpψ := hrψ p ⟨hp.1, hpBf⟩
        change (_, (_, _)) = ((1 : ℝ), (0 : ℂ), (0 : ℝ))
        erw [hcomp.1, hcomp.2, hpψ]
    · by_cases hab : a ∈ closure Bambient
      · obtain ⟨i, hai⟩ := mem_iUnion.mp (hBambientsub hab)
        refine ⟨W i ∩ (closure Br)ᶜ, Z i, (hW i).inter isClosed_closure.isOpen_compl,
          ⟨hai, har⟩, (hZ i).mono inter_subset_left, ?_⟩
        intro j p hp hs
        have hcomp := parameter_level_horizontal_components
          (hτ.mdifferentiableAt (by simp)) (hq.mdifferentiableAt (by simp)) (Z i p) (heq i p hp.1)
        fin_cases j
        · change (_, (0, 0)) = ((1 : ℝ), (0 : ℂ), (0 : ℝ)); erw [hcomp.1]
        · change (_, (0, _)) = ((1 : ℝ), (0 : ℂ), (0 : ℝ)); erw [hcomp.1, hcomp.2]
        · exact False.elim (hp.2 hs)
        · exact False.elim (hp.2 (subset_closure (hBfrontsub hs).1))
      · obtain ⟨P, V, hP, haP, hV, hv⟩ := exists_parameter_level_horizontalField
          (E := Model (2 * n)) (F := Model 0) (M := LGSpace n) (a := a)
          (f := fun _ => 0) contMDiff_const (by
            intro z
            change Model 0 at z
            refine ⟨0, ?_⟩
            change _ = (z : Model 0)
            exact Subsingleton.elim _ _)
        refine ⟨P ∩ (closure Br)ᶜ ∩ (closure Bambient)ᶜ, V,
          (hP.inter isClosed_closure.isOpen_compl).inter isClosed_closure.isOpen_compl,
          ⟨⟨haP, har⟩, hab⟩, hV.mono (fun _ hp => hp.1.1), ?_⟩
        intro j p hp hs
        have hcomp := parameter_level_horizontal_components
          (hτ.mdifferentiableAt (by simp))
          (mdifferentiableAt_const (c := (0 : Model 0))) (V p) (hv p hp.1.1)
        fin_cases j
        · change (_, (0, 0)) = ((1 : ℝ), (0 : ℂ), (0 : ℝ)); erw [hcomp.1]
        · exact False.elim (hp.2 hs)
        · exact False.elim (hp.1.2 hs)
        · exact False.elim (hp.1.2 (subset_closure (hBfrontsub hs).1))
  obtain ⟨O, V, hO, hCO, hV, hL⟩ := exists_smooth_marked_affine_lift_near_compact
    C hC S L (fun _ _ => (1, 0)) hlocal
  refine ⟨O, Bambient, Br, Bfront, V, hO, hCO, hBambient, ?_, hBr, hCrBr,
    hBfront, ?_, hV, ?_, ?_, ?_, ?_⟩
  · intro p hp; exact hCbBambient ⟨⟨hp.1, hp.2.le⟩, hp.2⟩
  · intro p hp; exact hCfBfront ⟨⟨hp.1, hp.2.1, hp.2.2.le⟩, hp.2.2⟩
  · intro p hp; exact congrArg Prod.fst (hL 0 p hp (mem_univ _))
  · intro p hp
    exact congrArg (fun z : ℝ × (ℂ × ℝ) => z.2.2) (hL 1 p hp.1 (subset_closure hp.2))
  · intro p hp
    have hcomp := congrArg (fun z : ℝ × (ℂ × ℝ) => (z.1, z.2.1))
      (hL 2 p hp.1 (subset_closure hp.2))
    have hpair : HasMFDerivAt 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ × ℂ)
        (fun z => (τ z, f z)) p
        ((mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) τ p).prod
          (mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℂ) f p)) :=
      ⟨hτ.continuous.continuousAt.prodMk hf.continuous.continuousAt,
        (hτ.mdifferentiableAt (by simp)).hasMFDerivAt.2.prodMk
          (hf.mdifferentiableAt (by simp)).hasMFDerivAt.2⟩
    change mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ × ℂ) (fun z => (τ z, f z)) p _ = _
    rw [hpair.mfderiv]
    exact hcomp
  · intro p hp
    exact congrArg (fun z : ℝ × (ℂ × ℝ) => z.2.2) (hL 3 p hp.1 (subset_closure hp.2))

end FsFltz
