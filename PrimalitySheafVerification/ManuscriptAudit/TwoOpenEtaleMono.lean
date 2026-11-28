import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import PrimalitySheafVerification.ManuscriptAudit.EtaleTwoOpenHOne
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionExact

/-! Monomorphisms of actual small étale sheaves can be checked on a
cover by two open subschemes. -/

namespace ManuscriptAudit.TwoOpenEtaleMono

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open EtaleTwoOpenHOne OpenEtaleExtension

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {U V X : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ X)
variable [IsOpenImmersion j] [IsOpenImmersion k]
variable {P Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (m : P ⟶ Q)

private theorem injective_at_factor {Z : X.Etale} (g : Z ⟶ Scheme.Etale.mk j)
    (hm : Mono ((restriction j AddCommGrpCat.{u}).map m)) :
    Function.Injective (m.hom.app (op Z)).hom := by
  have hg : g.left ≫ j = Z.hom := MorphismProperty.Over.w g
  letI : Etale (g.left ≫ j) := hg.symm ▸ Z.prop
  let D : U.Etale := MorphismProperty.Over.mk ⊤ g.left (Etale.of_comp _ j)
  let e : (etalePostcompose j).obj D ≅ Z :=
    MorphismProperty.Over.isoMk (Iso.refl Z.left) (by
      change 𝟙 _ ≫ Z.hom = g.left ≫ j
      rw [Category.id_comp, hg])
  letI := hm
  letI : Mono ((restriction j AddCommGrpCat.{u}).map m).hom :=
    (sheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{u}).map_mono _
  have h : Mono (m.hom.app (op ((etalePostcompose j).obj D))) := by
    exact (NatTrans.mono_iff_mono_app ((restriction j AddCommGrpCat.{u}).map m).hom).mp
      inferInstance (op D)
  intro x y hxy
  apply (P.obj.mapIso e.op).addCommGroupIsoToAddEquiv.injective
  apply (AddCommGrpCat.mono_iff_injective _).mp h
  exact (NatTrans.naturality_apply m.hom e.hom.op x).symm.trans
    ((congrArg (fun w => Q.obj.map e.hom.op w) hxy).trans
      (NatTrans.naturality_apply m.hom e.hom.op y))

private theorem twoOpens_cover (h : Set.range j ∪ Set.range k = Set.univ) :
    Sieve.ofTwoArrows (openArrow j) (openArrow k) ∈ X.smallEtaleTopology (identityObject X) := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ Set.range j ∪ Set.range k := h.symm ▸ Set.mem_univ x
  rcases hx with hj | hk
  · exact Set.mem_iUnion.2 ⟨WalkingPair.left, hj⟩
  · exact Set.mem_iUnion.2 ⟨WalkingPair.right, hk⟩

/-- A sheaf map monic on the actual two open charts is monic globally. -/
theorem mono_of_restrictions (h : Set.range j ∪ Set.range k = Set.univ)
    (hj : Mono ((restriction j AddCommGrpCat.{u}).map m))
    (hk : Mono ((restriction k AddCommGrpCat.{u}).map m)) : Mono m := by
  have hMono : Mono m.hom := (NatTrans.mono_iff_mono_app _).2 (by
    intro W
    apply (AddCommGrpCat.mono_iff_injective _).mpr
    intro x y hxy
    let T := identityObject X
    let t : unop W ⟶ T := (MorphismProperty.Over.mkIdTerminal @Etale X).from (unop W)
    let S := Sieve.ofTwoArrows (openArrow j) (openArrow k)
    have hS : S.pullback t ∈ X.smallEtaleTopology (unop W) :=
      X.smallEtaleTopology.pullback_stable t (twoOpens_cover j k h)
    let P' := P.obj ⋙ forget AddCommGrpCat.{u}
    have hP : Presieve.IsSheaf X.smallEtaleTopology P' :=
      (isSheaf_iff_isSheaf_of_type X.smallEtaleTopology _).mp
        ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj P).property
    apply (hP.isSheafFor _ hS).isSeparatedFor.ext
    intro Z a ha
    have ha' : S (a ≫ t) := ha
    obtain ⟨d, g, _⟩ := Sieve.ofArrows.exists ha'
    have hInject : Function.Injective (m.hom.app (op Z)).hom := by
      cases d
      · exact injective_at_factor j m g hj
      · exact injective_at_factor k m g hk
    change P.obj.map a.op x = P.obj.map a.op y
    apply hInject
    exact (NatTrans.naturality_apply m.hom a.op x).symm.trans
      ((congrArg (fun w => Q.obj.map a.op w) hxy).trans
        (NatTrans.naturality_apply m.hom a.op y)))
  letI : Mono m.hom := hMono
  exact Sheaf.Hom.mono_of_presheaf_mono X.smallEtaleTopology AddCommGrpCat.{u} m

end

end ManuscriptAudit.TwoOpenEtaleMono

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.TwoOpenEtaleMono.mono_of_restrictions
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
