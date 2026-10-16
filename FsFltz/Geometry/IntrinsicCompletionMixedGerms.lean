import FsFltz.Geometry.IntrinsicNativeJointCollar
import FsFltz.Geometry.IntrinsicCompletionFamilyCharts

/-!
# Joint germs of the original interior-cylinder transitions

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 142–158;
`def:chain`, lines 163–169; and `sec:lean`, lines 788–814.
The overlap of the original interior and the cylinder is the positive
inward collar. The same source-derived real collar extension constructs
mutually inverse smooth germs there, including at parameter endpoints.
Their restrictions are the literal transitions of the original quotient
patches. This does not construct a global atlas on the completed family.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCompletionGluing

private def productWithReal {d : ℕ} {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (Model d) X] [ChartedSpace (Model d) Y]
    (q : PartialDiffeomorph 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) X Y ∞) :
    PartialDiffeomorph ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (ℝ × X) (ℝ × Y) ∞ where
  toPartialEquiv := (PartialEquiv.refl ℝ).prod q.toPartialEquiv
  open_source := isOpen_univ.prod q.open_source
  open_target := isOpen_univ.prod q.open_target
  contMDiffOn_toFun := contMDiff_fst.contMDiffOn.prodMk
    (q.contMDiffOn_toFun.comp contMDiff_snd.contMDiffOn (fun _ hp => hp.2))
  contMDiffOn_invFun := contMDiff_fst.contMDiffOn.prodMk
    (q.contMDiffOn_invFun.comp contMDiff_snd.contMDiffOn (fun _ hp => hp.2))

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] [T2Space M] [SecondCountableTopology M]

private def restrictPositive {δ : ℝ}
    (A : PartialDiffeomorph ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1)))
      (ℝ × (ℝ × IntrinsicBoundary.Point k M))
      (ℝ × IntrinsicInterior.Point k M) ∞) :
    PartialDiffeomorph ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1)))
      (ℝ × (ℝ × IntrinsicBoundary.Point k M))
      (ℝ × IntrinsicInterior.Point k M) ∞ where
  __ := A.toOpenPartialHomeomorph.restr (univ ×ˢ (Ioo 0 δ ×ˢ univ))
  contMDiffOn_toFun := A.contMDiffOn_toFun.mono inter_subset_left
  contMDiffOn_invFun := A.contMDiffOn_invFun.mono inter_subset_left

/-- The retained real extension of the same native collar gives an actual
joint partial diffeomorphism on every positive overlap. Both directions
preserve parameter, and their interval restrictions are the natural maps
between the original quotient interior and cylinder patches. -/
theorem exists_joint_mixed_transition_germ {δ : ℝ}
    (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
    (hboundary : ∀ t b s, s ∈ Ico 0 δ →
      ((𝓡∂ (k + 1)).IsBoundaryPoint (C t (s, b)) ↔ s = 0))
    (D : CompactDomain (k + 1)) (i : M → D.extension.Point)
    (hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i)
    (hinj : Function.Injective i)
    (hbij : ∀ x, Function.Bijective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x))
    (eB : (IntrinsicBoundary.smoothManifold k M).SmoothEquiv D.boundary)
    (c : ℝ × (D.boundary.Point × ℝ) → D.extension.Point)
    (J : TopologicalSpace.Opens ℝ) (hJ : parameterInterval ⊆ (J : Set ℝ))
    (hdiff : IsLocalDiffeomorphOn ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1))) ∞
      (fun p : ℝ × (D.boundary.Point × ℝ) => (p.1, c p))
      ((J : Set ℝ) ×ˢ (univ ×ˢ Ioo (-δ) δ)))
    (hsquare : ∀ t p, p ∈ Ico 0 δ ×ˢ univ →
      i (C t p) = c (t.val, (eB p.2, -p.1))) :
    let c₀ := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
    ∀ (t : Parameter) (p : ℝ × IntrinsicBoundary.Point k M), p.1 ∈ Ioo 0 δ →
      ∃ A : PartialDiffeomorph
          ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)))
          ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1)))
          (ℝ × (ℝ × IntrinsicBoundary.Point k M))
          (ℝ × IntrinsicInterior.Point k M) ∞,
        (t.val, p) ∈ A.source ∧
        (∀ q ∈ A.source, q.2.1 ∈ Ioo 0 δ) ∧
        (∀ q ∈ A.source, (A q).1 = q.1) ∧
        (∀ q ∈ A.target, (A.symm q).1 = q.1) ∧
        (∀ (a : Parameter) q, (a.val, q) ∈ A.source →
          (A (a.val, q)).2.val = C a q) ∧
        (∀ (a : Parameter) (q : Band δ (IntrinsicBoundary.Point k M)),
          (a.val, q.val) ∈ A.source →
          totalInterior c₀ (a, (A (a.val, q.val)).2) = totalCylinder c₀ (a, q)) ∧
        (∀ (a : Parameter) (x : IntrinsicInterior.Point k M), (a.val, x) ∈ A.target →
          ∃ q : Band δ (IntrinsicBoundary.Point k M),
            A.symm (a.val, x) = (a.val, q.val) ∧
            totalCylinder c₀ (a, q) = totalInterior c₀ (a, x)) := by
  dsimp only
  intro t p hp
  have hpHalf : p ∈ Ico 0 δ ×ˢ univ := ⟨⟨hp.1.le, hp.2⟩, mem_univ _⟩
  have hx : (𝓡∂ (k + 1)).IsInteriorPoint (C t p) :=
    ((𝓡∂ (k + 1)).isInteriorPoint_iff_not_isBoundaryPoint _).mpr (by
      intro hb
      exact (ne_of_gt hp.1) ((hboundary t p.2 p.1 hpHalf.1).mp hb))
  let x : IntrinsicInterior.Point k M := ⟨C t p, hx⟩
  let j : IntrinsicInterior.Point k M → D.extension.Point := fun y => i y.val
  have hj : ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ j :=
    hi.comp IntrinsicInterior.contMDiff_val
  have hjbij : Function.Bijective (mfderiv 𝓘(ℝ, Model (k + 1))
      𝓘(ℝ, Model (k + 1)) j x) := by
    change Function.Bijective (mfderiv 𝓘(ℝ, Model (k + 1))
      𝓘(ℝ, Model (k + 1)) (i ∘ Subtype.val) x)
    rw [mfderiv_comp x (hi.mdifferentiableAt (by simp))
      (IntrinsicInterior.contMDiff_val.mdifferentiableAt (by simp))]
    exact (hbij x.val).comp (IntrinsicInterior.bijective_mfderiv_val x)
  obtain ⟨q, hxq, hq⟩ := isLocalDiffeomorphAt_of_bijective_mfderiv_manifold
    isOpen_univ hj.contMDiffOn (mem_univ x) hjbij
  let Q := productWithReal q
  let z : ℝ × (D.boundary.Point × ℝ) := (t.val, (eB p.2, -p.1))
  have hz : z ∈ (J : Set ℝ) ×ˢ (univ ×ˢ Ioo (-δ) δ) :=
    ⟨hJ t.property, mem_univ _, neg_lt_neg hp.2, by linarith [hp.1, hp.2]⟩
  obtain ⟨d, hzd, hd⟩ := hdiff ⟨z, hz⟩
  let E : Diffeomorph
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)))
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)))
      (ℝ × (ℝ × IntrinsicBoundary.Point k M))
      (ℝ × (D.boundary.Point × ℝ)) ∞ :=
    { toFun := fun u => (u.1, (eB u.2.2, -u.2.1))
      invFun := fun u => (u.1, (-u.2.2, eB.symm u.2.1))
      left_inv := by intro u; ext <;> simp
      right_inv := by intro u; ext <;> simp
      contMDiff_toFun := contMDiff_fst.prodMk
        ((eB.contMDiff.comp (contMDiff_snd.comp contMDiff_snd)).prodMk
          (contMDiff_fst.comp contMDiff_snd).neg)
      contMDiff_invFun := contMDiff_fst.prodMk
        ((contMDiff_snd.comp contMDiff_snd).neg.prodMk
          (eB.symm.contMDiff.comp (contMDiff_fst.comp contMDiff_snd))) }
  let A₀ := E.toPartialDiffeomorph.trans (d.trans Q.symm)
  let A := restrictPositive (δ := δ) A₀
  have hcq : c z ∈ q.target := by
    rw [← hsquare t p hpHalf]
    change j x ∈ q.target
    rw [hq hxq]
    exact q.map_source hxq
  have hpA₀ : (t.val, p) ∈ A₀.source := by
    change (t.val, p) ∈ univ ∧ E (t.val, p) ∈ d.source ∧ d (E (t.val, p)) ∈ Q.symm.source
    refine ⟨mem_univ _, hzd, ?_⟩
    change d z ∈ Q.symm.source
    rw [← hd hzd]
    exact ⟨mem_univ _, hcq⟩
  have hW : IsOpen ((univ : Set ℝ) ×ˢ (Ioo (0 : ℝ) δ ×ˢ
      (univ : Set (IntrinsicBoundary.Point k M)))) :=
    isOpen_univ.prod (isOpen_Ioo.prod isOpen_univ)
  have hpA : (t.val, p) ∈ A.source :=
    ⟨hpA₀, hW.interior_eq.symm ▸
      ⟨mem_univ _, hp, mem_univ _⟩⟩
  have hpositive : ∀ u ∈ A.source, u.2.1 ∈ Ioo 0 δ := by
    intro u hu
    exact (interior_subset hu.2).2.1
  have hparam : ∀ u ∈ A.source, (A u).1 = u.1 := by
    intro u hu
    change (d (E u)).1 = u.1
    have hdu : E u ∈ d.source := hu.1.2.1
    exact (congrArg Prod.fst (hd hdu)).symm
  have hparamInv : ∀ u ∈ A.target, (A.symm u).1 = u.1 := by
    intro u hu
    have h := hparam (A.symm u) (A.map_target hu)
    exact h.symm.trans (congrArg Prod.fst (A.toPartialEquiv.right_inv hu))
  have hnative : ∀ (a : Parameter) u, (a.val, u) ∈ A.source →
      (A (a.val, u)).2.val = C a u := by
    intro a u hu
    have hdsrc : E (a.val, u) ∈ d.source := hu.1.2.1
    have hqtar : (d (E (a.val, u))).2 ∈ q.target := hu.1.2.2.2
    have hqs := q.map_target hqtar
    have hjq : j (q.symm (d (E (a.val, u))).2) = (d (E (a.val, u))).2 :=
      (hq hqs).trans (q.right_inv hqtar)
    apply hinj
    change j (q.symm (d (E (a.val, u))).2) = i (C a u)
    exact hjq.trans ((congrArg Prod.snd (hd hdsrc)).symm.trans
      (hsquare a u ⟨⟨(hpositive _ hu).1.le, (hpositive _ hu).2⟩, mem_univ _⟩).symm)
  refine ⟨A, hpA, hpositive, hparam, hparamInv, hnative, ?_, ?_⟩
  · intro a u hu
    apply (totalInterior_eq_totalCylinder_iff
      (fun a (v : Half δ (IntrinsicBoundary.Point k M)) => C a v.val)
      (fun a v => hboundary a v.val.2 v.val.1 v.property.1) _ _).mpr
    exact ⟨rfl, (hpositive _ hu).1, (hnative a u.val hu).symm⟩
  · intro a y hy
    let u := A.symm (a.val, y)
    have hus : u ∈ A.source := A.map_target hy
    let p : Band δ (IntrinsicBoundary.Point k M) :=
      ⟨u.2, (hpositive u hus).2, mem_univ _⟩
    have hu : u = (a.val, p.val) := Prod.ext (hparamInv _ hy) rfl
    refine ⟨p, hu, ?_⟩
    have hpSource : (a.val, p.val) ∈ A.source := hu ▸ hus
    have hA : A (a.val, p.val) = (a.val, y) := hu ▸ A.toPartialEquiv.right_inv hy
    apply (totalInterior_eq_totalCylinder_iff
      (fun a (v : Half δ (IntrinsicBoundary.Point k M)) => C a v.val)
      (fun a v => hboundary a v.val.2 v.val.1 v.property.1) _ _).mpr _ |>.symm
    refine ⟨rfl, (hpositive _ hpSource).1, ?_⟩
    exact (hnative a p.val hpSource).symm.trans (congrArg (fun z => z.2.val) hA)

end FsFltz.Geometry.IntrinsicCompletionGluing
