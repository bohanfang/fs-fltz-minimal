import FsFltz.Geometry.LiouvilleLocalFlow
import FsFltz.Geometry.FamilyLiouvilleNeighborhood

/-!
# Parameter-preserving local flows near a compact family

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–160,
`def:chain`, lines 163–169, and `sec:lean`, lines 783–814.
Smoothness means `C∞` with extension across parameter endpoints
(lines 119–122). A compact product seam has one open neighborhood and
one positive two-sided integration time.

The original family field is assumed smooth only on its actual open
neighborhood. A compact cutoff there produces an auxiliary field with zero
parameter component. Its constructed all-real action preserves the parameter;
on the stated local tube the spatial component solves the original ODE.
All-real completeness concerns the auxiliary field only. This constructs no
completion or collar and does not establish the geometric target `thm:target`.
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology Function

namespace FsFltz.Geometry
namespace CollarFlow

section Family

variable {E H Q : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [CompleteSpace E] [FiniteDimensional ℝ E] [LocallyCompactSpace H]
  [T2Space Q] [SecondCountableTopology Q]

set_option backward.isDefEq.respectTransparency false in
/-- A family smooth only near a compact parameter-times-space seam admits
a constructed jointly smooth auxiliary action that preserves its parameter.
On a common open neighborhood and positive two-sided time interval, its
spatial trajectories remain in the given neighborhood and solve the original
family field. No global regularity or completeness of that field is assumed. -/
theorem exists_parameter_preserving_local_smoothFlow_supported
    (Z : ℝ → (x : Q) → TangentSpace I x)
    {Ω : Set (ℝ × Q)} (hΩ : IsOpen Ω)
    (hZ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) I.tangent ∞
      (fun p : ℝ × Q => (⟨p.2, Z p.1 p.2⟩ : TangentBundle I Q)) Ω)
    {J : Set ℝ} {K : Set Q} (hJ : IsCompact J) (hK : IsCompact K)
    (hseam : J ×ˢ K ⊆ Ω) :
    ∃ (U : TopologicalSpace.Opens (ℝ × Q)) (δ : ℝ),
      J ×ˢ K ⊆ (U : Set (ℝ × Q)) ∧ (U : Set (ℝ × Q)) ⊆ Ω ∧
      0 < δ ∧ ∃ F : Flow ℝ (ℝ × Q),
      ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I))
        ((𝓘(ℝ, ℝ)).prod I) ∞
        (fun p : ℝ × (ℝ × Q) => F p.1 p.2) ∧
      (∀ s p, (F s p).1 = p.1) ∧
      (∀ s p, p ∉ Ω → F s p = p) ∧
      ∀ p ∈ U, ∀ s ∈ Ioo (-δ) δ,
        F s p ∈ Ω ∧
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun u => (F u p).2) s
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Z p.1 (F s p).2)) := by
  let : LocallyCompactSpace (ModelProd ℝ H) :=
    inferInstanceAs (LocallyCompactSpace (ℝ × H))
  let v : (p : ℝ × Q) → TangentSpace ((𝓘(ℝ, ℝ)).prod I) p :=
    fun p => constantParameterLift (Z p.1) p
  have hv : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I)
      (((𝓘(ℝ, ℝ)).prod I).tangent) ∞
      (fun p => (⟨p, v p⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × Q))) Ω := by
    have ht : ContMDiff 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).tangent) ∞
        (fun t : ℝ => (⟨t, (0 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
      contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
    exact contMDiff_equivTangentBundleProd_symm.comp_contMDiffOn
      ((ht.comp contMDiff_fst).contMDiffOn.prodMk hZ)
  obtain ⟨χ, V, hχ, hKV, hone, hsupport, hsuppΩ⟩ :=
    CollarExtension.exists_smooth_compact_cutoff
      (I := (𝓘(ℝ, ℝ)).prod I) (hJ.prod hK) hΩ hseam
  let W : (p : ℝ × Q) → TangentSpace ((𝓘(ℝ, ℝ)).prod I) p :=
    fun p => χ p • v p
  have hW : ContMDiff ((𝓘(ℝ, ℝ)).prod I)
      (((𝓘(ℝ, ℝ)).prod I).tangent) ∞
      (fun p => (⟨p, W p⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × Q))) :=
    hχ.contMDiffOn.smul_section_of_tsupport hΩ hsuppΩ hv
  obtain ⟨F, hF, hode⟩ := exists_supported_smoothFlow W hW hsupport
    (fun p hp => by simp only [W, image_eq_zero_of_notMem_tsupport hp, zero_smul])
  have hfst : ∀ s p, (F s p).1 = p.1 := by
    intro s p
    have hd : ∀ u : ℝ, HasDerivAt (fun a => (F a p).1) (0 : ℝ) u := by
      intro u
      have hm := (hasMFDerivAt_fst (I := 𝓘(ℝ, ℝ)) (I' := I) (F u p)).comp u (hode p u)
      have hh := (hasMFDerivAt_iff_hasFDerivAt.mp hm).hasDerivAt
      apply hh.congr_deriv
      change (1 : ℝ) • (χ (F u p) • (0 : ℝ)) = 0
      simp only [smul_zero]
    have he : (fun a => (F a p).1) = fun _ => p.1 := by
      apply ODE_solution_unique_univ (t₀ := 0) (v := fun (_ : ℝ) (_ : ℝ) => (0 : ℝ))
        (s := fun _ => univ) (K := 0) (fun _ => (LipschitzWith.const 0).lipschitzOnWith)
      · exact fun u => ⟨hd u, mem_univ _⟩
      · exact fun u => ⟨hasDerivAt_const u _, mem_univ _⟩
      · exact congrArg Prod.fst (F.map_zero_apply p)
    exact congrFun he s
  have hfixed : ∀ s p, p ∉ Ω → F s p = p := by
    intro s p hp
    have hWp : W p = 0 := by
      have hn : p ∉ tsupport χ := fun hm => hp (hsuppΩ hm)
      simp only [W, image_eq_zero_of_notMem_tsupport hn, zero_smul]
    have hc : IsMIntegralCurve (fun _ : ℝ => p) W := by
      intro u
      rw [hWp, ContinuousLinearMap.smulRight_zero]
      exact hasMFDerivAt_const _ _
    exact congrFun (isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
      (t₀ := 0) (hW.of_le (by simp)) (hode p) hc (F.map_zero_apply p)) s
  let S : Set (ℝ × (ℝ × Q)) :=
    (fun p : ℝ × (ℝ × Q) => F p.1 p.2) ⁻¹' ((V : Set (ℝ × Q)) ∩ Ω)
  have hS : IsOpen S := (V.isOpen.inter hΩ).preimage hF.continuous
  have hzeroSeam : ({0} : Set ℝ) ×ˢ (J ×ˢ K) ⊆ S := by
    rintro ⟨s, p⟩ ⟨hs, hp⟩
    have hs₀ : s = 0 := hs
    subst s
    simpa only [S, mem_preimage, Flow.map_zero_apply] using
      (show p ∈ (V : Set (ℝ × Q)) ∩ Ω from ⟨hKV hp, hseam hp⟩)
  obtain ⟨T, A, hT, hA, hzeroT, hKA, hTA⟩ :=
    generalized_tube_lemma isCompact_singleton (hJ.prod hK) hS hzeroSeam
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (hT.mem_nhds (hzeroT (mem_singleton 0)))
  have hAΩ : A ⊆ Ω := by
    intro p hp
    have h : (0, p) ∈ S := hTA ⟨hzeroT (mem_singleton 0), hp⟩
    simpa only [S, mem_preimage, Flow.map_zero_apply] using h.2
  refine ⟨⟨A, hA⟩, δ, hKA, hAΩ, hδ, F, hF, hfst, hfixed, ?_⟩
  intro p hp s hs
  have hsT : s ∈ T := hball (by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using hs)
  have hFV : F s p ∈ (V : Set (ℝ × Q)) ∩ Ω :=
    show (s, p) ∈ S from hTA ⟨hsT, hp⟩
  refine ⟨hFV.2, ?_⟩
  have hd := (hasMFDerivAt_snd (I := 𝓘(ℝ, ℝ)) (I' := I) (F s p)).comp s (hode p s)
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change ℝ at r
  change r • (W (F s p)).2 = r • Z p.1 (F s p).2
  simp only [W, v, constantParameterLift, hone _ hFV.1, one_smul, hfst]

/-- The local-flow interface without its additional support conclusion. -/
theorem exists_parameter_preserving_local_smoothFlow
    (Z : ℝ → (x : Q) → TangentSpace I x)
    {Ω : Set (ℝ × Q)} (hΩ : IsOpen Ω)
    (hZ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) I.tangent ∞
      (fun p : ℝ × Q => (⟨p.2, Z p.1 p.2⟩ : TangentBundle I Q)) Ω)
    {J : Set ℝ} {K : Set Q} (hJ : IsCompact J) (hK : IsCompact K)
    (hseam : J ×ˢ K ⊆ Ω) :
    ∃ (U : TopologicalSpace.Opens (ℝ × Q)) (δ : ℝ),
      J ×ˢ K ⊆ (U : Set (ℝ × Q)) ∧ (U : Set (ℝ × Q)) ⊆ Ω ∧
      0 < δ ∧ ∃ F : Flow ℝ (ℝ × Q),
      ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I))
        ((𝓘(ℝ, ℝ)).prod I) ∞
        (fun p : ℝ × (ℝ × Q) => F p.1 p.2) ∧
      (∀ s p, (F s p).1 = p.1) ∧
      ∀ p ∈ U, ∀ s ∈ Ioo (-δ) δ,
        F s p ∈ Ω ∧
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun u => (F u p).2) s
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Z p.1 (F s p).2)) := by
  obtain ⟨U, δ, hU, hsub, hδ, F, hF, hfst, _, hlocal⟩ :=
    exists_parameter_preserving_local_smoothFlow_supported Z hΩ hZ hJ hK hseam
  exact ⟨U, δ, hU, hsub, hδ, F, hF, hfst, hlocal⟩

end Family

end CollarFlow

namespace CompactDomain

set_option backward.isDefEq.respectTransparency false in
/-- Smooth interval primitives on a fixed compact domain produce an actual
parameter-preserving local Liouville flow, jointly smooth in flow time,
family parameter and initial point. One positive two-sided time interval
works near the entire compact family. Along these trajectories the original
interval primitive has a nondegenerate differential and its canonical field
satisfies the contraction equation. The all-real action is auxiliary; its
original Liouville ODE is asserted precisely on this local interval. -/
theorem exists_liouvilleFamily_localFlow_invariant {d : ℕ} (D : CompactDomain d)
    (L : Parameter → LiouvilleStructure D)
    (halpha : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive)) :
    ∃ (U : TopologicalSpace.Opens (ℝ × D.extension.Point)) (δ : ℝ),
      parameterInterval ×ˢ D.carrier ⊆ (U : Set (ℝ × D.extension.Point)) ∧
      0 < δ ∧ ∃ F : Flow ℝ (ℝ × D.extension.Point),
      ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)))
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
        (fun p : ℝ × (ℝ × D.extension.Point) => F p.1 p.2) ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)))
        𝓘(ℝ, Model d) ∞
        (fun p : ℝ × (ℝ × D.extension.Point) => (F p.1 p.2).2) ∧
      (∀ s p, (F s p).1 = p.1) ∧
      (∀ (t : Parameter) s x,
        x ∈ (⟨D, L t⟩ : LiouvilleDomain d).symplecticNeighborhood ↔
          (F s (t.val, x)).2 ∈ (⟨D, L t⟩ : LiouvilleDomain d).symplecticNeighborhood) ∧
      ∀ (t : Parameter) (x : D.extension.Point), (t.val, x) ∈ U →
        ∀ s ∈ Ioo (-δ) δ,
          D.extension.Nondegenerate
            (D.extension.exteriorDerivative ((L t).primitive)) (F s (t.val, x)).2 ∧
          D.extension.LiouvilleEquation ((L t).primitive) (F s (t.val, x)).2
            (D.extension.liouvilleVector ((L t).primitive) (F s (t.val, x)).2) ∧
          HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
            (fun u => (F u (t.val, x)).2) s
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (D.extension.liouvilleVector ((L t).primitive) (F s (t.val, x)).2)) := by
  obtain ⟨alpha, _, he, V, hseam, hnd, hcontract, hZ, _⟩ :=
    D.exists_liouvilleFamily_nondegenerateNeighborhood L halpha
  obtain ⟨U, δ, hU, _, hδ, F, hF, hfst, hfixed, hlocal⟩ :=
    CollarFlow.exists_parameter_preserving_local_smoothFlow_supported
      (fun t => D.extension.liouvilleVector (alpha t)) V.isOpen hZ
      (show IsCompact parameterInterval from isCompact_Icc) D.compact hseam
  have hfix (t : Parameter) (s : ℝ) (x : D.extension.Point)
      (hx : x ∉ (⟨D, L t⟩ : LiouvilleDomain d).symplecticNeighborhood) :
      F s (t.val, x) = (t.val, x) := by
    apply hfixed
    intro hv
    apply hx
    have hn := hnd (t.val, x) hv
    rw [he t] at hn
    exact hn
  have hinv (t : Parameter) (s : ℝ) (x : D.extension.Point) :
      x ∈ (⟨D, L t⟩ : LiouvilleDomain d).symplecticNeighborhood ↔
        (F s (t.val, x)).2 ∈ (⟨D, L t⟩ : LiouvilleDomain d).symplecticNeighborhood := by
    constructor
    · intro hx
      by_contra hn
      have heq := hfix t (-s) (F s (t.val, x)).2 hn
      have hp : (t.val, (F s (t.val, x)).2) = F s (t.val, x) :=
        Prod.ext (hfst s (t.val, x)).symm rfl
      rw [hp, ← F.map_add, neg_add_cancel, F.map_zero_apply] at heq
      exact hn (congrArg Prod.snd heq ▸ hx)
    · intro hx
      by_contra hn
      rw [hfix t s x hn] at hx
      exact hn hx
  refine ⟨U, δ, hU, hδ, F, hF, contMDiff_snd.comp hF, hfst, hinv, ?_⟩
  intro t x hx s hs
  obtain ⟨hmem, hode⟩ := hlocal (t.val, x) hx s hs
  have hn := hnd (F s (t.val, x)) hmem
  have hc := hcontract (F s (t.val, x)) hmem
  rw [hfst, he t] at hn hc
  rw [he t] at hode
  exact ⟨hn, hc, hode⟩

/-- The original local-flow interface, obtained from the invariant auxiliary flow. -/
theorem exists_liouvilleFamily_localFlow {d : ℕ} (D : CompactDomain d)
    (L : Parameter → LiouvilleStructure D)
    (halpha : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive)) :
    ∃ (U : TopologicalSpace.Opens (ℝ × D.extension.Point)) (δ : ℝ),
      parameterInterval ×ˢ D.carrier ⊆ (U : Set (ℝ × D.extension.Point)) ∧
      0 < δ ∧ ∃ F : Flow ℝ (ℝ × D.extension.Point),
      ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)))
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
        (fun p : ℝ × (ℝ × D.extension.Point) => F p.1 p.2) ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)))
        𝓘(ℝ, Model d) ∞
        (fun p : ℝ × (ℝ × D.extension.Point) => (F p.1 p.2).2) ∧
      (∀ s p, (F s p).1 = p.1) ∧
      ∀ (t : Parameter) (x : D.extension.Point), (t.val, x) ∈ U →
        ∀ s ∈ Ioo (-δ) δ,
          D.extension.Nondegenerate
            (D.extension.exteriorDerivative ((L t).primitive)) (F s (t.val, x)).2 ∧
          D.extension.LiouvilleEquation ((L t).primitive) (F s (t.val, x)).2
            (D.extension.liouvilleVector ((L t).primitive) (F s (t.val, x)).2) ∧
          HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
            (fun u => (F u (t.val, x)).2) s
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (D.extension.liouvilleVector ((L t).primitive) (F s (t.val, x)).2)) := by
  obtain ⟨U, δ, hU, hδ, F, hF, hs, hfst, _, hlocal⟩ :=
    D.exists_liouvilleFamily_localFlow_invariant L halpha
  exact ⟨U, δ, hU, hδ, F, hF, hs, hfst, hlocal⟩

end CompactDomain
end FsFltz.Geometry
