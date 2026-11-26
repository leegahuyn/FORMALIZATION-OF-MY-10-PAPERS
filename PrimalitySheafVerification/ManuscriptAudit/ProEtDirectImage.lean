import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.Over

/-!
# Direct image on the actual small pro-étale sites

Fiber product of weakly étale schemes is continuous on the small
pro-étale sites. The resulting sheaf direct image is evaluated on each
open by that fiber product. In particular, the terminal evaluation
is the original sheaf's terminal evaluation, naturally in the sheaf.
-/

namespace ManuscriptAudit.ProEtDirectImage

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

abbrev baseChange {X Y : Scheme.{u}} (f : X ⟶ Y) : Y.ProEt ⥤ X.ProEt :=
  MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ f

private def baseChangeCompForget {X Y : Scheme.{u}} (f : X ⟶ Y) :
    baseChange f ⋙ Scheme.ProEt.forget X ≅
      Scheme.ProEt.forget Y ⋙ CategoryTheory.Over.pullback f :=
  MorphismProperty.Over.pullbackCompForgetIso (P := @AlgebraicGeometry.WeaklyEtale)
    (Q := ⊤) f

private theorem topology_eq_restrictedTopology (X : Scheme.{u}) :
    Scheme.ProEt.topology X =
      (Scheme.ProEt.forget X).restrictedTopology (Scheme.proetaleTopology.over X) :=
  MorphismProperty.toGrothendieck_comap_forget_eq_restrictedTopology
    Scheme.proetalePrecoverage Scheme.proetalePrecoverage_le_precoverage_weaklyEtale

/-- A covering in the small source site stays covering after pullback.
The full weakly étale subcategory has the restricted slice topology. -/
theorem coverPreserving {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CoverPreserving (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) (baseChange f) := by
  letI : (baseChange f ⋙ Scheme.ProEt.forget X).IsContinuous
      (Scheme.ProEt.topology Y) (Scheme.proetaleTopology.over X) :=
    Functor.isContinuous_comp' (baseChangeCompForget f).symm (Scheme.ProEt.topology Y)
      (Scheme.proetaleTopology.over Y) (Scheme.proetaleTopology.over X)
  have h := CoverPreserving.of_isContinuous (baseChange f ⋙ Scheme.ProEt.forget X)
    (Scheme.ProEt.topology Y) (Scheme.proetaleTopology.over X)
  constructor
  intro U S hS
  rw [topology_eq_restrictedTopology X]
  apply Functor.mem_restrictedTopology_of_functorPushforward_mem
  rw [← Sieve.functorPushforward_comp]
  exact h.cover_preserve hS

theorem preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (baseChange f) := by
  let ex := Scheme.ProEt.forget X
  let ey := Scheme.ProEt.forget Y
  letI : PreservesFiniteLimits (ey ⋙ CategoryTheory.Over.pullback f) :=
    comp_preservesFiniteLimits _ _
  letI := preservesFiniteLimits_of_natIso (baseChangeCompForget f).symm
  exact preservesFiniteLimits_of_reflects_of_preserves (baseChange f) ex

theorem isContinuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (baseChange f).IsContinuous (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) := by
  letI := preservesFiniteLimits f
  letI := flat_of_preservesFiniteLimits (baseChange f)
  exact (Functor.isContinuous_iff_coverPreserving).2 (coverPreserving f)

/-- Actual pro-étale direct image along any scheme map, including a
closed immersion or the inclusion of a residue point. -/
def directImage {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type v) [Category.{w} A] :
    Sheaf (Scheme.ProEt.topology X) A ⥤ Sheaf (Scheme.ProEt.topology Y) A :=
  letI := isContinuous f
  (baseChange f).sheafPushforwardContinuous A (Scheme.ProEt.topology Y)
    (Scheme.ProEt.topology X)

@[simp] theorem directImage_eval {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A : Type v} [Category.{w} A] (F : Sheaf (Scheme.ProEt.topology X) A) (U : Y.ProEt) :
    ((directImage f A).obj F).obj.obj (op U) =
      F.obj.obj (op ((baseChange f).obj U)) := rfl

def terminalObject (X : Scheme.{u}) : X.ProEt := Scheme.ProEt.mk (𝟙 X)

def terminalObjectIsTerminal (X : Scheme.{u}) : IsTerminal (terminalObject X) :=
  MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.WeaklyEtale X

def terminalBaseChangeIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    terminalObject X ≅ (baseChange f).obj (terminalObject Y) :=
  letI := preservesFiniteLimits f
  (terminalObjectIsTerminal X).uniqueUpToIso
    (IsTerminal.isTerminalObj (baseChange f) (terminalObject Y) (terminalObjectIsTerminal Y))

def terminalSections (X : Scheme.{u}) (A : Type v) [Category.{w} A] :
    Sheaf (Scheme.ProEt.topology X) A ⥤ A :=
  sheafToPresheaf _ A ⋙ (evaluation _ A).obj (op (terminalObject X))

/-- The direct image has precisely the original terminal sections. -/
def directImageTerminalSectionsIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type v) [Category.{w} A] :
    directImage f A ⋙ terminalSections Y A ≅ terminalSections X A := by
  refine NatIso.ofComponents (fun F => ?_) ?_
  · exact F.obj.mapIso (terminalBaseChangeIso f).op
  · intro F G α
    exact (α.hom.naturality (terminalBaseChangeIso f).op.hom).symm

/-- An abelian direct image is zero on every object whose pullback is empty. -/
theorem directImage_eval_isZero_of_isEmpty {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf (Scheme.ProEt.topology X) Ab.{v}) (U : Y.ProEt)
    [IsEmpty ((baseChange f).obj U).left] :
    IsZero (((directImage f Ab.{v}).obj F).obj.obj (op U)) := by
  rw [directImage_eval]
  exact (F.isTerminalOfBotCover _ (Scheme.ProEt.bot_mem_topology _)).isZero

end

end ManuscriptAudit.ProEtDirectImage

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProEtDirectImage.coverPreserving,
      ``ManuscriptAudit.ProEtDirectImage.isContinuous,
      ``ManuscriptAudit.ProEtDirectImage.directImage,
      ``ManuscriptAudit.ProEtDirectImage.directImageTerminalSectionsIso,
      ``ManuscriptAudit.ProEtDirectImage.directImage_eval_isZero_of_isEmpty] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
