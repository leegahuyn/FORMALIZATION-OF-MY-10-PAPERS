import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicClosedPairSupport
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousDirectImageGlobal
import PrimalitySheafVerification.ManuscriptAudit.ProetaleClosedSupportLocalConstants
import PrimalitySheafVerification.ManuscriptAudit.SheafImageGlobalLift
import PrimalitySheafVerification.ManuscriptAudit.SheafProductSectionExt
import PrimalitySheafVerification.ManuscriptAudit.TwoOpenCokernelLift

/-! Both actual rational boundary values are global sections of the
categorical image of the native continuous pair restriction. -/

namespace ManuscriptAudit.ProetaleAdicBoundaryPairImageHZero

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open ProetaleContinuousDirectImageMaps (functions functionsOver diagonal)
open ProetaleContinuousDirectImageGlobal (finalObject terminalEquiv)
open ProetaleClosedSupportLocalConstants (openObject openArrow)
open ProetaleAdicClosedPairSupport (boundary pairRestriction)
open TwoOpenCokernelLift (coverObjects coverArrows)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{0}} (L : Type) [Field L]
variable (i₀ i₁ : Spec (CommRingCat.of L) ⟶ X) [IsClosedImmersion i₀] [IsClosedImmersion i₁]
variable (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev A := AddCommGrpCat.{1}
private abbrev M := ℤ_[ℓ]
private abbrev T := finalObject X
private abbrev J := Scheme.ProEt.topology X
private abbrev integers :=
  (constantSheaf (J (X := X)) A).obj (AddCommGrpCat.of (ULift.{1} ℤ))

private def pointValue (i : Spec (CommRingCat.of L) ⟶ X)
    (s : (functionsOver (M ℓ) i).obj.obj (op (T (X := X)))) : M ℓ :=
  terminalEquiv (M ℓ) i s (IsLocalRing.closedPoint L)

private theorem constant_lift_on_chart {V : X.ProEt} (a : V ⟶ T (X := X))
    (i : Spec (CommRingCat.of L) ⟶ X)
    (s : (functionsOver (M ℓ) i).obj.obj (op (T (X := X)))) :
    (diagonal (M ℓ) i).hom.app (op V) ⟨ContinuousMap.const V.left (pointValue L ℓ i s)⟩ =
      (functionsOver (M ℓ) i).obj.map a.op s := by
  let c := pointValue L ℓ i s
  have hs : s = (terminalEquiv (M ℓ) i).symm (ContinuousMap.const _ c) := by
    apply (terminalEquiv (M ℓ) i).injective
    rw [AddEquiv.apply_symm_apply]
    apply ContinuousMap.ext
    intro x
    exact congrArg (terminalEquiv (M ℓ) i s) (Subsingleton.elim x (IsLocalRing.closedPoint L))
  change (diagonal (M ℓ) i).hom.app (op V) ⟨ContinuousMap.const V.left c⟩ = _
  rw [hs]
  rfl

private theorem section_eq_off_chart {V : X.ProEt} (i : Spec (CommRingCat.of L) ⟶ X)
    (h : Disjoint (Set.range V.hom) (Set.range i))
    (s t : (functionsOver (M ℓ) i).obj.obj (op V)) : s = t := by
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  change ↥(pullback V.hom i : Scheme.{0}) at x
  have hx : V.hom (pullback.fst V.hom i x) = i (pullback.snd V.hom i x) :=
    congrArg (fun f : pullback V.hom i ⟶ X ↦ f x) (pullback.condition (f := V.hom) (g := i))
  exact (Set.disjoint_left.mp h ⟨_, rfl⟩ ⟨_, hx.symm⟩).elim

private abbrev G := boundary i₀ i₁ ℓ
private abbrev d := pairRestriction i₀ i₁ ℓ
private abbrev π₀ : G i₀ i₁ ℓ ⟶ functionsOver (M ℓ) i₀ := prod.fst
private abbrev π₁ : G i₀ i₁ ℓ ⟶ functionsOver (M ℓ) i₁ := prod.snd

private theorem local_lift_first {V : X.ProEt} (a : V ⟶ T (X := X))
    (h : Disjoint (Set.range V.hom) (Set.range i₁))
    (s : (G i₀ i₁ ℓ).obj.obj (op (T (X := X)))) :
    ∃ b : (functions (M ℓ) X).obj.obj (op V), (d i₀ i₁ ℓ).hom.app (op V) b =
      (G i₀ i₁ ℓ).obj.map a.op s := by
  let p := π₀ i₀ i₁ ℓ
  let t := p.hom.app (op (T (X := X))) s
  refine ⟨⟨ContinuousMap.const V.left (pointValue L ℓ i₀ t)⟩, ?_⟩
  apply SheafProductSectionExt.section_ext
  · change ((d i₀ i₁ ℓ ≫ p).hom.app (op V)) _ = p.hom.app (op V) ((G i₀ i₁ ℓ).obj.map a.op s)
    rw [show d i₀ i₁ ℓ ≫ p = diagonal (M ℓ) i₀ from prod.lift_fst _ _,
      NatTrans.naturality_apply p.hom a.op s]
    exact constant_lift_on_chart L ℓ a i₀ t
  · exact section_eq_off_chart L ℓ i₁ h _ _

private theorem local_lift_second {V : X.ProEt} (a : V ⟶ T (X := X))
    (h : Disjoint (Set.range V.hom) (Set.range i₀))
    (s : (G i₀ i₁ ℓ).obj.obj (op (T (X := X)))) :
    ∃ b : (functions (M ℓ) X).obj.obj (op V), (d i₀ i₁ ℓ).hom.app (op V) b =
      (G i₀ i₁ ℓ).obj.map a.op s := by
  let p := π₁ i₀ i₁ ℓ
  let t := p.hom.app (op (T (X := X))) s
  refine ⟨⟨ContinuousMap.const V.left (pointValue L ℓ i₁ t)⟩, ?_⟩
  apply SheafProductSectionExt.section_ext
  · exact section_eq_off_chart L ℓ i₀ h _ _
  · change ((d i₀ i₁ ℓ ≫ p).hom.app (op V)) _ = p.hom.app (op V) ((G i₀ i₁ ℓ).obj.map a.op s)
    rw [show d i₀ i₁ ℓ ≫ p = diagonal (M ℓ) i₁ from prod.lift_snd _ _,
      NatTrans.naturality_apply p.hom a.op s]
    exact constant_lift_on_chart L ℓ a i₁ t

set_option maxHeartbeats 2200000 in
private theorem exists_image_terminal_section
    (hDisjoint : Disjoint (Set.range i₀) (Set.range i₁))
    (s : (G i₀ i₁ ℓ).obj.obj (op (T (X := X)))) :
    ∃ b : (Abelian.image (d i₀ i₁ ℓ)).obj.obj (op (T (X := X))),
      (Abelian.image.ι (d i₀ i₁ ℓ)).hom.app (op (T (X := X))) b = s := by
  let t := T (X := X)
  let O₀ : X.Opens := ⟨(Set.range i₁)ᶜ, i₁.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let O₁ : X.Opens := ⟨(Set.range i₀)ᶜ, i₀.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let V := coverObjects (openObject t O₀) (openObject t O₁)
  let a := coverArrows (openArrow t O₀) (openArrow t O₁)
  have hCover : Sieve.ofArrows V a ∈ J (X := X) t := by
    apply Precoverage.generate_mem_toGrothendieck
    change (Presieve.ofArrows V a).map (Scheme.ProEt.forget X ⋙ Over.forget X) ∈
      Scheme.proetalePrecoverage X
    rw [Presieve.map_ofArrows]
    apply Scheme.etalePrecoverage_le_proetalePrecoverage _
    apply (Scheme.ofArrows_mem_precoverage_iff @Etale).mpr
    constructor
    · intro x
      by_cases hx : x ∈ Set.range i₁
      · refine ⟨true, ⟨x, ?_⟩, rfl⟩
        intro h₀
        exact Set.disjoint_left.mp hDisjoint h₀ hx
      · exact ⟨false, ⟨x, hx⟩, rfl⟩
    · intro b
      cases b
      · exact inferInstanceAs (Etale O₀.ι)
      · exact inferInstanceAs (Etale O₁.ι)
  apply SheafImageGlobalLift.exists_image_section V a hCover (d i₀ i₁ ℓ) s
  intro b
  cases b
  · apply local_lift_first L i₀ i₁ ℓ
    exact Set.disjoint_left.mpr (by rintro _ ⟨x, rfl⟩ h; exact x.property h)
  · apply local_lift_second L i₀ i₁ ℓ
    exact Set.disjoint_left.mpr (by rintro _ ⟨x, rfl⟩ h; exact x.property h)

/-- Native global sections of the categorical image are all pairs of closed point values. -/
def imageHZeroEquiv (hDisjoint : Disjoint (Set.range i₀) (Set.range i₁)) :
    Sheaf.H (Abelian.image (d i₀ i₁ ℓ)) 0 ≃+ Sheaf.H (G i₀ i₁ ℓ) 0 := by
  let m := Abelian.image.ι (d i₀ i₁ ℓ)
  let hT := MorphismProperty.Over.mkIdTerminal @WeaklyEtale X
  refine AddEquiv.ofBijective (Sheaf.H.map m 0)
    ⟨Ext.postcomp_mk₀_injective_of_mono integers m, ?_⟩
  intro a
  obtain ⟨b, hb⟩ := exists_image_terminal_section L i₀ i₁ ℓ hDisjoint
    (Sheaf.H.equiv₀ (G i₀ i₁ ℓ) hT a)
  refine ⟨(Sheaf.H.equiv₀ (Abelian.image (d i₀ i₁ ℓ)) hT).symm b,
    (Sheaf.H.equiv₀ (G i₀ i₁ ℓ) hT).injective ?_⟩
  rw [← Sheaf.H.equiv₀_naturality, AddEquiv.apply_symm_apply]
  exact hb

end

end ManuscriptAudit.ProetaleAdicBoundaryPairImageHZero

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleAdicBoundaryPairImageHZero.imageHZeroEquiv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
