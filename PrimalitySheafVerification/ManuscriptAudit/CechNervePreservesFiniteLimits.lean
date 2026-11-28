import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CechNervePreservedWideCone

/-! A finite-limit-preserving site functor identifies the actual Čech
nerves naturally, with their precise simplicial faces. -/

namespace ManuscriptAudit.CechNervePreservesFiniteLimits

open CategoryTheory CategoryTheory.Limits Opposite
open CechNerveLowDegrees (N vertex)
open scoped Simplicial

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C D : Type*} [Category* C] [Category* D] [HasFiniteLimits C] [HasFiniteLimits D]
  (F : C ⥤ D) [PreservesFiniteLimits F] {U T : C} (f : U ⟶ T)

private abbrev cone (n : ℕ) := CechNervePreservedWideCone.cone F f n

private def atDegree (n : ℕ) : F.obj (N f n) ≅ N (F.map f) n :=
  (CechNervePreservedWideCone.isLimit_cone F f n).conePointUniqueUpToIso
    (limit.isLimit (WidePullbackShape.wideCospan (F.obj T) (fun _ : Fin (n + 1) ↦ F.obj U)
      (fun _ ↦ F.map f)))

private theorem atDegree_vertex (n : ℕ) (i : Fin (n + 1)) :
    (atDegree F f n).hom ≫ vertex (F.map f) n i = F.map (vertex f n i) := by
  have h := (CechNervePreservedWideCone.isLimit_cone F f n).conePointUniqueUpToIso_hom_comp
    (limit.isLimit (WidePullbackShape.wideCospan (F.obj T) (fun _ : Fin (n + 1) ↦ F.obj U)
      (fun _ ↦ F.map f))) (some i)
  change (atDegree F f n).hom ≫ vertex (F.map f) n i = (cone F f n).π i at h
  exact h.trans (CechNervePreservedWideCone.cone_π F f n i)

private theorem map_vertex {E : Type*} [Category* E] [HasFiniteLimits E] {V W : E}
    (g : V ⟶ W) {m n : ℕ} (s : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    (Arrow.mk g).cechNerve.map s.op ≫ vertex g m i = vertex g n (s.toOrderHom i) := by
  rw [Arrow.cechNerve_map]
  exact WidePullback.lift_π _ _ _ _ _

set_option maxHeartbeats 4300000 in
private theorem natural {m n : ℕ} (s : ⦋m⦌ ⟶ ⦋n⦌) :
    F.map ((Arrow.mk f).cechNerve.map s.op) ≫ (atDegree F f m).hom =
      (atDegree F f n).hom ≫ (Arrow.mk (F.map f)).cechNerve.map s.op := by
  have h (i : Fin (m + 1)) :
      (F.map ((Arrow.mk f).cechNerve.map s.op) ≫ (atDegree F f m).hom) ≫ vertex (F.map f) m i =
        ((atDegree F f n).hom ≫ (Arrow.mk (F.map f)).cechNerve.map s.op) ≫ vertex (F.map f) m i := by
    rw [Category.assoc, Category.assoc, atDegree_vertex, map_vertex, atDegree_vertex, ← Functor.map_comp,
      map_vertex]
  apply WidePullback.hom_ext
  · exact h
  · rw [← WidePullback.π_arrow (fun _ : Fin (m + 1) ↦ F.map f) (0 : Fin (m + 1)),
      ← Category.assoc, ← Category.assoc, h]

/-- The comparison preserves all the actual simplicial restriction maps. -/
def comparison : (Arrow.mk f).cechNerve ⋙ F ≅ (Arrow.mk (F.map f)).cechNerve :=
  NatIso.ofComponents (fun s ↦ atDegree F f s.unop.len) (by
    intro a b g
    rcases a with ⟨⟨n⟩⟩
    rcases b with ⟨⟨m⟩⟩
    exact natural F f g.unop)

end
end ManuscriptAudit.CechNervePreservesFiniteLimits

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CechNervePreservesFiniteLimits.comparison
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
