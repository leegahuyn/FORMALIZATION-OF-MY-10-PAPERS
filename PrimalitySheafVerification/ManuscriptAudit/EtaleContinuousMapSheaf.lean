import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# The small étale constant sheaf as continuous maps to a discrete group

The ambient continuous-map sheaf descends for fpqc covers. Its restriction
to the small étale site is the sheafification of the constant presheaf:
each continuous map to the discrete coefficient group is constant on the
open cover by its fibers.
-/

namespace ManuscriptAudit.EtaleContinuousMapSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{u}) (M : AddCommGrpCat.{u}) [TopologicalSpace M]
variable [DiscreteTopology M] [IsTopologicalAddGroup M]

private theorem etale_le_fpqc : Scheme.etaleTopology.{u} ≤ Scheme.fpqcTopology := by
  apply le_trans _ Scheme.fppfTopology_le_fpqcTopology
  apply Precoverage.toGrothendieck_mono
  apply Scheme.precoverage_mono
  intro V W f hf
  letI : Etale f := hf
  exact ⟨inferInstance, inferInstance⟩

private theorem etaleForget_continuous :
    (Scheme.Etale.forget X).IsContinuous X.smallEtaleTopology (Scheme.etaleTopology.over X) := by
  let G := Scheme.Etale.forget X
  let K := Scheme.etaleTopology.over X
  letI : PreservesFiniteLimits G := inferInstanceAs
    (PreservesFiniteLimits (MorphismProperty.Over.forget @Etale ⊤ X))
  letI : RepresentablyFlat G := flat_of_preservesFiniteLimits G
  change G.IsContinuous (G.restrictedTopology K) K
  exact Functor.isContinuous_iff_coverPreserving.mpr
    (G.coverPreserving_restrictedTopology K)

/-- Continuous maps into the discrete coefficient group are a sheaf on the small étale site. -/
def continuousMapSheaf : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} := by
  let B : Sheaf Scheme.etaleTopology AddCommGrpCat.{u} :=
    ⟨continuousMapPresheafAb M, (isSheaf_fpqcTopology_continuousMapPresheafAb M).of_le etale_le_fpqc⟩
  let K := Scheme.etaleTopology.over X
  let H : Sheaf K AddCommGrpCat.{u} :=
    ⟨(Over.forget X).op ⋙ B.obj, (Over.forget X).op_comp_isSheaf K Scheme.etaleTopology B⟩
  letI := etaleForget_continuous X
  exact ⟨(Scheme.Etale.forget X).op ⋙ H.obj,
    (Scheme.Etale.forget X).op_comp_isSheaf X.smallEtaleTopology K H⟩

private def constantToContinuous :
    (Functor.const (X.Etaleᵒᵖ)).obj M ⟶ (continuousMapSheaf X M).obj where
  app W := AddCommGrpCat.ofHom
    { toFun := ContinuousMap.const W.unop.left
      map_zero' := by ext w; rfl
      map_add' := by intros; ext w; rfl }
  naturality := by
    intro W W' f
    ext a w <;> rfl

private theorem constantToContinuous_locallyInjective :
    Presheaf.IsLocallyInjective X.smallEtaleTopology (constantToContinuous X M) where
  equalizerSieve_mem {W} a b h := by
    by_cases hn : Nonempty W.unop.left
    · obtain ⟨w⟩ := hn
      have hab : a = b := congrArg (fun g : C(W.unop.left, M) => g w) h
      subst b
      rw [Presheaf.equalizerSieve_self_eq_top]
      exact X.smallEtaleTopology.top_mem _
    · let T : Empty → X.Etale := Empty.elim
      let f (i : Empty) : T i ⟶ W.unop := i.elim
      have hcover : Sieve.ofArrows T f ∈ X.smallEtaleTopology W.unop := by
        rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
        exact Set.eq_univ_of_forall fun w => (hn ⟨w⟩).elim
      refine X.smallEtaleTopology.superset_covering ?_ hcover
      apply (Sieve.generate_le_iff _ _).2
      rintro _ _ ⟨i⟩
      exact i.elim

private theorem constantToContinuous_locallySurjective :
    Presheaf.IsLocallySurjective X.smallEtaleTopology (constantToContinuous X M) where
  imageSieve_mem {W} s := by
    let s' : C(W.left, M) := s
    let V (a : M) : W.left.Opens := ⟨s' ⁻¹' {a}, (isOpen_discrete _).preimage s'.continuous⟩
    letI : Etale W.hom := W.prop
    let T (a : M) : X.Etale := Scheme.Etale.mk ((V a).ι ≫ W.hom)
    let f (a : M) : T a ⟶ W := MorphismProperty.Over.homMk (V a).ι rfl
    have hcover : Sieve.ofArrows T f ∈ X.smallEtaleTopology W := by
      rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
      apply Set.eq_univ_of_forall
      intro w
      exact Set.mem_iUnion.2 ⟨s' w, ⟨⟨w, rfl⟩, rfl⟩⟩
    refine X.smallEtaleTopology.superset_covering ?_ hcover
    apply (Sieve.generate_le_iff _ _).2
    rintro _ _ ⟨a⟩
    refine ⟨a, ?_⟩
    apply ContinuousMap.ext
    intro w
    exact w.property.symm

/-- The native constant abelian sheaf is the sheaf of continuous maps to the discrete group. -/
def constantSheafContinuousMapIso :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj M ≅ continuousMapSheaf X M := by
  let P := presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}
  letI := constantToContinuous_locallyInjective X M
  letI := constantToContinuous_locallySurjective X M
  letI : IsIso (P.map (constantToContinuous X M)) :=
    (X.smallEtaleTopology.W_iff _).1
      (X.smallEtaleTopology.W_of_isLocallyBijective (constantToContinuous X M))
  exact asIso (P.map (constantToContinuous X M)) ≪≫
    (sheafificationIso (continuousMapSheaf X M)).symm

end

end ManuscriptAudit.EtaleContinuousMapSheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleContinuousMapSheaf.continuousMapSheaf,
      ``ManuscriptAudit.EtaleContinuousMapSheaf.constantSheafContinuousMapIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
