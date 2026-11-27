import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.Adjunctions
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineCover
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineCoproduct

/-! Local lifts over an affine object in the native pro-étale site
lift over one affine weakly étale fpqc cover. -/

namespace ManuscriptAudit.ProetaleAffineSingletonLift

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleAffineCoproduct

universe u v
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{u}} {T : S.ProEt}

private abbrev J := Scheme.ProEt.topology S
private abbrev C := Sheaf (J (S := S)) AddCommGrpCat.{v}

private theorem underlying_types_isSheaf (I : C.{u, v} (S := S)) :
    Presieve.IsSheaf (J (S := S)) (I.obj ⋙ forget AddCommGrpCat.{v}) := by
  letI : PreservesLimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{v}) :=
    AddCommGrpCat.adj.rightAdjoint_preservesLimits
  exact (isSheaf_iff_isSheaf_of_type (J (S := S)) _).mp
    (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget AddCommGrpCat.{v}) I.property)

private theorem sections_subsingleton_of_empty (I : C.{u, v} (S := S))
    (W : S.ProEt) [IsEmpty W.left] : Subsingleton (I.obj.obj (op W)) := by
  let V : PEmpty.{u + 1} → S.ProEt := PEmpty.elim
  let f : ∀ i, V i ⟶ W := fun i ↦ PEmpty.elim i
  have hCov : Sieve.ofArrows V f ∈ J (S := S) W := by
    have h : Sieve.ofArrows V f = ⊥ := by
      ext X g
      constructor
      · rintro ⟨_, _, _, ⟨i⟩, _⟩
        exact PEmpty.elim i
      · exact False.elim
    rw [h]
    exact Scheme.ProEt.bot_mem_topology W
  let P := I.obj ⋙ forget AddCommGrpCat.{v}
  have hI : Presieve.IsSheaf (J (S := S)) P := underlying_types_isSheaf I
  obtain ⟨t, _, ht⟩ :=
    (Presieve.isSheafFor_arrows_iff (P := P) f).mp (hI.isSheafFor _ hCov)
      (fun i ↦ PEmpty.elim i) (fun i ↦ PEmpty.elim i)
  exact ⟨fun a b ↦ (ht a (fun i ↦ PEmpty.elim i)).trans (ht b (fun i ↦ PEmpty.elim i)).symm⟩

private theorem component_cover {n : ℕ} (V : Fin n → S.ProEt) :
    Sieve.ofArrows V (injection V) ∈ J (S := S) (coproduct V) := by
  apply Precoverage.generate_mem_toGrothendieck
  change (Presieve.ofArrows V (injection V)).map (Scheme.ProEt.forget S ⋙ Over.forget S) ∈
    Scheme.proetalePrecoverage (coproduct V).left
  rw [Presieve.map_ofArrows]
  apply Scheme.etalePrecoverage_le_proetalePrecoverage _
  apply (Scheme.ofArrows_mem_precoverage_iff @Etale).mpr
  constructor
  · let g : Fin n → Scheme.{u} := fun i ↦ (V i).left
    let D := sigmaOpenCover g
    intro x
    exact ⟨D.idx x, D.covers x⟩
  · intro i
    change Etale (Sigma.ι (fun j ↦ (V j).left) i)
    infer_instance

/-- Sections on disjoint coproduct components glue in the actual pro-étale sheaf. -/
theorem glue_sections {n : ℕ} (V : Fin n → S.ProEt) (I : C.{u, v} (S := S))
    (s : ∀ i, I.obj.obj (op (V i))) :
    ∃! z : I.obj.obj (op (coproduct V)), ∀ i, I.obj.map (injection V i).op z = s i := by
  let U := Scheme.ProEt.forget S ⋙ Over.forget S
  let P := I.obj ⋙ forget AddCommGrpCat.{v}
  have hI : Presieve.IsSheaf (J (S := S)) P := underlying_types_isSheaf I
  have hs : Presieve.Arrows.Compatible P (injection V) s := by
    intro i j W p q hpq
    change I.obj.map p.op (s i) = I.obj.map q.op (s j)
    have hw : p.left ≫ Sigma.ι (fun k ↦ (V k).left) i =
        q.left ≫ Sigma.ι (fun k ↦ (V k).left) j := U.congr_map hpq
    by_cases hij : i = j
    · subst j
      have h : p = q := by
        apply MorphismProperty.Over.Hom.ext
        exact (cancel_mono (Sigma.ι (fun k ↦ (V k).left) i)).mp hw
      rw [h]
    · letI : IsEmpty W.left := isEmpty_of_commSq_sigmaι_of_ne ⟨hw⟩ hij
      exact (sections_subsingleton_of_empty I W).elim _ _
  exact (Presieve.isSheafFor_arrows_iff (P := P) (injection V)).mp
    (hI.isSheafFor _ (component_cover V)) s hs

/-- An epimorphism's local lift over an affine object is realized by one
affine weakly étale covering morphism. -/
theorem exists_singleton_cover_lift [IsAffine T.left]
    {I Q : C.{u, v} (S := S)} (q : I ⟶ Q) [Sheaf.IsLocallySurjective q]
    (x : Q.obj.obj (op T)) :
    ∃ (W : S.ProEt) (f : W ⟶ T), IsAffine W.left ∧ WeaklyEtale f.left ∧
      Surjective f.left ∧
      Sieve.generate (Presieve.singleton f) ∈ J (S := S) T ∧
      ∃ y : I.obj.obj (op W), q.hom.app (op W) y = Q.obj.map f.op x := by
  classical
  let R : Sieve T := Presheaf.imageSieve q.hom x
  have hR : R ∈ J (S := S) T := Presheaf.imageSieve_mem (J (S := S)) q.hom x
  obtain ⟨n, V, a, ha, hw, hr, hs⟩ := ProetaleAffineCover.exists_finite_refinement R hR
  letI := ha
  let W := coproduct V
  let f := descent V a
  have hLift (i : Fin n) : ∃ y : I.obj.obj (op (V i)),
      q.hom.app (op (V i)) y = Q.obj.map (a i).op x := hr i
  choose s hs' using hLift
  obtain ⟨y, hy, _⟩ := glue_sections V I s
  let t := Q.obj.map f.op x
  obtain ⟨z, _, hz⟩ := glue_sections V Q (fun i ↦ Q.obj.map (injection V i).op t)
  refine ⟨W, f, inferInstance, descent_weaklyEtale V a hw,
    descent_surjective V a hs, descent_covers V a hw hs, y, ?_⟩
  have hy' (i : Fin n) : Q.obj.map (injection V i).op (q.hom.app (op W) y) =
      Q.obj.map (injection V i).op t := by
    rw [← NatTrans.naturality_apply, hy, hs']
    change Q.obj.map (a i).op x = Q.obj.map (injection V i).op (Q.obj.map f.op x)
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      injection_descent]
  exact (hz _ hy').trans (hz t (fun _ ↦ rfl)).symm

end
end ManuscriptAudit.ProetaleAffineSingletonLift

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAffineSingletonLift.glue_sections,
      ``ManuscriptAudit.ProetaleAffineSingletonLift.exists_singleton_cover_lift] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
