import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import PrimalitySheafVerification.ManuscriptAudit.FiniteSupportEtaleRetraction
import PrimalitySheafVerification.ManuscriptAudit.SheafCoverLifts
import PrimalitySheafVerification.ManuscriptAudit.SheafHOnePushout
import PrimalitySheafVerification.ManuscriptAudit.SheafSectionDifference

/-!
# Degree-one descent for a finite-support affine étale sheaf

A degree-one class is represented by a cokernel section. Choose a finite
cover on which it lifts. The differences on the finitely many overlaps
are supported on one finite subset of the summands. Pushing out along
the complementary projection makes those lifts compatible.
-/

namespace ManuscriptAudit.FiniteSupportPresheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (S : Scheme.{0})

private abbrev J := Scheme.AffineEtale.topology S
private abbrev C := Sheaf (J S) AddCommGrpCat.{0}

variable [HasExt.{0} (C S)]
variable [(J S).HasSheafCompose (forget AddCommGrpCat.{0})]
variable [(J S).WEqualsLocallyBijective AddCommGrpCat.{0}]

private theorem restrict_restrict (F : S.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{0})
    {X Y Z : S.AffineEtale} (f : X ⟶ Y) (g : Y ⟶ Z) (x : F.obj (op Z)) :
    F.map f.op (F.map g.op x) = F.map (f ≫ g).op x := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

set_option maxHeartbeats 5000000 in
/-- Vanishing H¹ on all finite sums implies vanishing on the actual
finite-support sum on the affine étale site. -/
theorem affineEtaleDirectSum_HOne_subsingleton {I : Type} (P : I → C S)
    {T : S.AffineEtale} (hT : IsTerminal T)
    (hVanishing : ∀ t : Finset I,
      Subsingleton (Sheaf.H (affineEtaleDirectSum S (fun a : t ↦ P a.val)) 1)) :
    Subsingleton (Sheaf.H (affineEtaleDirectSum S P) 1) := by
  classical
  letI : IsGrothendieckAbelian.{0} (C S) :=
    Scheme.isGrothendieckAbelian_sheaf_affineEtaleTopology S AddCommGrpCat.{0}
  letI : EnoughInjectives (C S) := IsGrothendieckAbelian.enoughInjectives.{0} (C := C S)
  let D := affineEtaleDirectSum S P
  let M := Injective.under D
  let i : D ⟶ M := Injective.ι D
  letI : Mono i := inferInstanceAs (Mono (Injective.ι D))
  let Q := cokernel i
  let π : M ⟶ Q := cokernel.π i
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨y, rfl⟩ := SheafH1Descent.connectingSection_surjective i hT x
  have hLocal : Presheaf.imageSieve π.hom y ∈ J S T :=
    SheafH1Descent.cokernel_section_lift_sieve_mem i y
  have hFin : HasFiniteCoverFamilies (J S) :=
    fun U f h ↦ AffineEtaleFiniteCover.finiteSubcover_ofArrows U f h
  obtain ⟨L, hL, U, f, hf, z, hz⟩ := SheafCoverLifts.exists_finite_cover_lifts π hFin y hLocal
  letI : Finite L := hL
  letI := Fintype.ofFinite L
  let W (a b : L) := pullback (f a) (f b)
  let l (a b : L) : W a b ⟶ U a := pullback.fst (f a) (f b)
  let r (a b : L) : W a b ⟶ U b := pullback.snd (f a) (f b)
  have hSame (a b : L) :
      π.hom.app (op (W a b)) (M.obj.map (l a b).op (z a)) =
        π.hom.app (op (W a b)) (M.obj.map (r a b).op (z b)) := by
    rw [NatTrans.naturality_apply π.hom (l a b).op (z a),
      NatTrans.naturality_apply π.hom (r a b).op (z b), hz a, hz b]
    rw [restrict_restrict, restrict_restrict, show l a b ≫ f a = r a b ≫ f b from pullback.condition]
  let d (a b : L) : D.obj.obj (op (W a b)) :=
    SheafSectionDifference.difference i (W a b)
      (M.obj.map (l a b).op (z a)) (M.obj.map (r a b).op (z b)) (hSame a b)
  have hd (a b : L) :
      i.hom.app (op (W a b)) (d a b) =
        M.obj.map (l a b).op (z a) - M.obj.map (r a b).op (z b) :=
    SheafSectionDifference.difference_spec i _ _ _ _
  let t : Finset I := Finset.univ.biUnion (fun p : L × L ↦ (d p.1 p.2).support)
  have ht (a b : L) (j : I) (hj : j ∉ t) : DFinsupp.toFun (d a b) j = 0 := by
    by_contra hn
    exact hj (Finset.mem_biUnion.mpr ⟨(a, b), Finset.mem_univ _,
      (DFinsupp.mem_support_toFun (d a b) j).mpr hn⟩)
  let p := finiteProjection S P t
  let k := finiteInclusion S P t
  let ρ : D ⟶ D := 𝟙 D - (p ≫ k)
  have hρ (a b : L) : ρ.hom.app (op (W a b)) (d a b) = 0 := by
    change d a b - k.hom.app (op (W a b)) (p.hom.app (op (W a b)) (d a b)) = 0
    rw [projection_inclusion_of_support S P t (op (W a b)) (d a b) (ht a b), sub_self]
  let M' := pushout i ρ
  let m : M ⟶ M' := pushout.inl i ρ
  let q : M' ⟶ Q := (CokernelPushout.sequence i ρ).g
  let z' (a : L) : M'.obj.obj (op (U a)) := m.hom.app (op (U a)) (z a)
  have hz' (a : L) : q.hom.app (op (U a)) (z' a) = Q.obj.map (f a).op y := by
    have eq := congrArg (fun e : M ⟶ Q ↦ e.hom.app (op (U a))) (CokernelPushout.inl_sequence_g i ρ)
    exact (ConcreteCategory.congr_hom eq (z a)).trans (hz a)
  have hPair (a b : L) :
      M'.obj.map (l a b).op (z' a) = M'.obj.map (r a b).op (z' b) := by
    apply sub_eq_zero.mp
    change M'.obj.map (l a b).op (m.hom.app _ (z a)) -
      M'.obj.map (r a b).op (m.hom.app _ (z b)) = 0
    rw [← NatTrans.naturality_apply m.hom (l a b).op (z a),
      ← NatTrans.naturality_apply m.hom (r a b).op (z b)]
    change (m.hom.app (op (W a b))).hom _ - (m.hom.app (op (W a b))).hom _ = 0
    rw [← map_sub]
    change m.hom.app (op (W a b))
      (M.obj.map (l a b).op (z a) - M.obj.map (r a b).op (z b)) = 0
    rw [← hd a b]
    have hc := congrArg (fun e : D ⟶ M' ↦ e.hom.app (op (W a b)))
      (pushout.condition (f := i) (g := ρ))
    rw [show m.hom.app (op (W a b)) (i.hom.app (op (W a b)) (d a b)) =
        (pushout.inr i ρ).hom.app (op (W a b)) (ρ.hom.app (op (W a b)) (d a b)) from
      ConcreteCategory.congr_hom hc (d a b), hρ a b]
    exact ((pushout.inr i ρ).hom.app (op (W a b))).hom.map_zero
  obtain ⟨v, hv⟩ := SheafCoverLifts.exists_lift_of_pullback_compatible q U f hf y z' hz' hPair
  have hZero := SheafHOnePushout.map_connecting_eq_zero_of_lift i ρ hT y v hv
  let α := SheafH1Descent.connectingSection i hT y
  let H := Sheaf.functorH (J S) 1
  have hP : Sheaf.H.map p 1 α = 0 := (hVanishing t).allEq _ _
  have hMap : H.map ρ = 𝟙 (H.obj D) - (H.map p ≫ H.map k) := by
    change H.map (𝟙 D - (p ≫ k)) = _
    rw [H.map_sub, H.map_id D, H.map_comp p k]
  have hApply := ConcreteCategory.congr_hom hMap α
  change Sheaf.H.map ρ 1 α = α - Sheaf.H.map k 1 (Sheaf.H.map p 1 α) at hApply
  rw [hP, map_zero, sub_zero] at hApply
  exact hApply.symm.trans hZero

end

end ManuscriptAudit.FiniteSupportPresheaf

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.FiniteSupportPresheaf.affineEtaleDirectSum_HOne_subsingleton
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
