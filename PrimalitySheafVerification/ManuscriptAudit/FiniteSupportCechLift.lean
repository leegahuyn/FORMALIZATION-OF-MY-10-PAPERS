import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CokernelPushout
import PrimalitySheafVerification.ManuscriptAudit.FiniteSupportComplement
import PrimalitySheafVerification.ManuscriptAudit.InjectiveCechPullback
import PrimalitySheafVerification.ManuscriptAudit.SheafSectionDifference
import PrimalitySheafVerification.ManuscriptAudit.SingletonCoverRefinement

/-!
# Lifting a cocycle after discarding finitely many support coordinates

A local lift on a double overlap has two defects: failure to descend
along its own covering arrow, and failure of the cocycle relation on
a common refinement of the triple overlap. Both defects are sections
of the finite-support kernel, so a single finite complement kills them
in the pushout of the short exact sequence.
-/

namespace ManuscriptAudit.FiniteSupportPresheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open InjectiveCechPullback SingletonCoverRefinement

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (S : Scheme.{0}) {I : Type}

private abbrev J := Scheme.AffineEtale.topology S
private abbrev C := Sheaf (J S) AddCommGrpCat.{0}
private abbrev D (P : I → C S) := affineEtaleDirectSum S P

variable [(J S).HasSheafCompose (forget AddCommGrpCat.{0})]
variable (P : I → C S)

private theorem restrict_restrict (A : C S) {X Y Z : S.AffineEtale}
    (a : X ⟶ Y) (b : Y ⟶ Z) (x : A.obj.obj (op Z)) :
    A.obj.map a.op (A.obj.map b.op x) = A.obj.map (a ≫ b).op x := by
  rw [op_comp, CategoryTheory.Functor.map_comp, ConcreteCategory.comp_apply]

set_option maxHeartbeats 6000000 in
/-- After pushing out along a finite complementary projection, an
actual local cocycle lift descends to the double overlap and satisfies
the triple cocycle relation there. -/
theorem exists_cocycle_lift_after_finiteComplement
    {M : C S} (i : D S P ⟶ M) [Mono i] {U T : S.AffineEtale} (f : U ⟶ T)
    (b : (cokernel i).obj.obj (op (Double f)))
    (hb : (cokernel i).obj.map (edge23 f).op b - (cokernel i).obj.map (edge13 f).op b +
      (cokernel i).obj.map (edge12 f).op b = 0)
    {V : S.AffineEtale} (g : V ⟶ Double f) (hg : Covers (J S) g)
    (y : M.obj.obj (op V))
    (hy : (cokernel.π i).hom.app (op V) y = (cokernel i).obj.map g.op b) :
    ∃ (t : Finset I) (z : (pushout i (finiteComplement S P t)).obj.obj (op (Double f))),
      (CokernelPushout.sequence i (finiteComplement S P t)).g.hom.app (op (Double f)) z = b ∧
        (pushout i (finiteComplement S P t)).obj.map (edge23 f).op z -
          (pushout i (finiteComplement S P t)).obj.map (edge13 f).op z +
          (pushout i (finiteComplement S P t)).obj.map (edge12 f).op z = 0 := by
  classical
  let Q := cokernel i
  let π : M ⟶ Q := cokernel.π i
  let W := pullback g g
  let l : W ⟶ V := pullback.fst g g
  let r : W ⟶ V := pullback.snd g g
  have hPair : π.hom.app (op W) (M.obj.map l.op y) =
      π.hom.app (op W) (M.obj.map r.op y) := by
    rw [NatTrans.naturality_apply π.hom l.op y, NatTrans.naturality_apply π.hom r.op y, hy]
    rw [restrict_restrict S, restrict_restrict S, show l ≫ g = r ≫ g from pullback.condition]
  let d₀ := SheafSectionDifference.difference i W
    (M.obj.map l.op y) (M.obj.map r.op y) hPair
  have hd₀ : i.hom.app (op W) d₀ = M.obj.map l.op y - M.obj.map r.op y :=
    SheafSectionDifference.difference_spec i W _ _ hPair
  obtain ⟨E, e, he, a₁₂, a₁₃, a₂₃, h₁₂, h₁₃, h₂₃⟩ :=
    exists_common_refinement (J S) g hg (edge12 f) (edge13 f) (edge23 f)
  let yDefect : M.obj.obj (op E) :=
    M.obj.map a₂₃.op y - M.obj.map a₁₃.op y + M.obj.map a₁₂.op y
  have hπDefect : π.hom.app (op E) yDefect = 0 := by
    have hm (a : E ⟶ V) (p : Triple f ⟶ Double f) (h : a ≫ g = e ≫ p) :
        π.hom.app (op E) (M.obj.map a.op y) = Q.obj.map e.op (Q.obj.map p.op b) := by
      rw [NatTrans.naturality_apply π.hom a.op y, hy, restrict_restrict S, h, ← restrict_restrict S]
    change (π.hom.app (op E)).hom
      (M.obj.map a₂₃.op y - M.obj.map a₁₃.op y + M.obj.map a₁₂.op y) = 0
    rw [map_add, map_sub]
    change π.hom.app (op E) (M.obj.map a₂₃.op y) - π.hom.app (op E) (M.obj.map a₁₃.op y) +
      π.hom.app (op E) (M.obj.map a₁₂.op y) = 0
    rw [hm _ _ h₂₃, hm _ _ h₁₃, hm _ _ h₁₂]
    change (Q.obj.map e.op).hom _ - (Q.obj.map e.op).hom _ + (Q.obj.map e.op).hom _ = 0
    rw [← map_sub, ← map_add, hb, map_zero]
  obtain ⟨d₁, hd₁⟩ :=
    (SheafSectionDifference.cokernel_sections_exact i E yDefect).mp hπDefect
  let t : Finset I := d₀.support ∪ d₁.support
  let ρ := finiteComplement S P t
  let N := pushout i ρ
  let m : M ⟶ N := pushout.inl i ρ
  let p : N ⟶ Q := (CokernelPushout.sequence i ρ).g
  have hOutside (Z : S.AffineEtaleᵒᵖ) (d : (D S P).obj.obj Z) (ht : d.support ⊆ t)
      (a : I) (ha : a ∉ t) : DFinsupp.toFun d a = 0 := by
    by_contra hn
    exact ha (ht ((DFinsupp.mem_support_toFun d a).mpr hn))
  have hk₀ : m.hom.app (op W) (i.hom.app (op W) d₀) = 0 :=
    pushout_inl_app_eq_zero_of_support S P t i (op W) d₀
      (hOutside (op W) d₀ Finset.subset_union_left)
  have hk₁ : m.hom.app (op E) (i.hom.app (op E) d₁) = 0 :=
    pushout_inl_app_eq_zero_of_support S P t i (op E) d₁
      (hOutside (op E) d₁ Finset.subset_union_right)
  let y' := m.hom.app (op V) y
  have hyPair : N.obj.map l.op y' = N.obj.map r.op y' := by
    apply sub_eq_zero.mp
    change N.obj.map l.op (m.hom.app (op V) y) - N.obj.map r.op (m.hom.app (op V) y) = 0
    rw [← NatTrans.naturality_apply m.hom l.op y, ← NatTrans.naturality_apply m.hom r.op y]
    change (m.hom.app (op W)).hom _ - (m.hom.app (op W)).hom _ = 0
    rw [← map_sub]
    change m.hom.app (op W) (M.obj.map l.op y - M.obj.map r.op y) = 0
    rw [← hd₀]
    exact hk₀
  obtain ⟨z, hz⟩ := exists_amalgamation (J S) N g hg y' hyPair
  refine ⟨t, z, ?_, ?_⟩
  · change p.hom.app (op (Double f)) z = b
    apply restriction_injective (J S) Q g hg
    rw [← NatTrans.naturality_apply p.hom g.op z, hz]
    have h := congrArg (fun q : M ⟶ Q ↦ q.hom.app (op V))
      (CokernelPushout.inl_sequence_g i ρ)
    exact (ConcreteCategory.congr_hom h y).trans hy
  · change N.obj.map (edge23 f).op z - N.obj.map (edge13 f).op z +
      N.obj.map (edge12 f).op z = 0
    apply restriction_injective (J S) N e he
    have hRestrict (a : E ⟶ V) (p' : Triple f ⟶ Double f) (h : a ≫ g = e ≫ p') :
        N.obj.map e.op (N.obj.map p'.op z) = m.hom.app (op E) (M.obj.map a.op y) := by
      rw [restrict_restrict S, ← h, ← restrict_restrict S, hz]
      exact (NatTrans.naturality_apply m.hom a.op y).symm
    change (N.obj.map e.op).hom
      (N.obj.map (edge23 f).op z - N.obj.map (edge13 f).op z +
        N.obj.map (edge12 f).op z) = (N.obj.map e.op).hom 0
    rw [map_add, map_sub, map_zero]
    change N.obj.map e.op (N.obj.map (edge23 f).op z) -
      N.obj.map e.op (N.obj.map (edge13 f).op z) +
      N.obj.map e.op (N.obj.map (edge12 f).op z) = 0
    rw [hRestrict _ _ h₂₃, hRestrict _ _ h₁₃, hRestrict _ _ h₁₂]
    change (m.hom.app (op E)).hom _ - (m.hom.app (op E)).hom _ +
      (m.hom.app (op E)).hom _ = 0
    rw [← map_sub, ← map_add]
    change m.hom.app (op E) yDefect = 0
    rw [← hd₁]
    exact hk₁

end

end ManuscriptAudit.FiniteSupportPresheaf

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.FiniteSupportPresheaf.exists_cocycle_lift_after_finiteComplement
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
